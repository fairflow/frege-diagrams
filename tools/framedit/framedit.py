#!/usr/bin/env python3
"""framedit: the figure editor of FregeDiagrams/ (see docs/design/EDITOR.md).

    python3 -I tools/framedit/framedit.py FILE [--def NAME] [--port 8765] [--lake-dir DIR] [--no-browser]

FILE is a file of figures in the syntax of FregeDiagrams/Syntax.lean (as for
`framediag --fig FILE`), or a Lean file holding the figures in a raw string
`def NAME : String := r#"…"#` (such as `exampleSource` in
FregeDiagrams/Examples.lean).  For a Lean file only the string's contents are
edited and written back.  A Lean file may hold several such strings: the page
lists them and switches between them; `--def NAME` picks the one to start
with (default: the first).  Opens http://127.0.0.1:PORT/ (this machine only).

This bridge holds no figure logic.  It runs two copies of the Lean drawing
server (`framediag --serve`, FregeDiagrams/Serve.lean): one for parsing, edits and
view A, one for view B and the link router, which takes seconds, so that it
never holds up a drag.  It passes the page's requests to them, serves the
page, and reads and writes FILE.  A save is refused when the text does not
parse, and when FILE changed on disk since the page read it.

Python standard library only.  DIR is the Lake package that builds
`framediag` (default: the repository containing this script).
"""
import hashlib
import http.server
import json
import os
import re
import subprocess
import sys
import threading
import webbrowser

HERE = os.path.dirname(os.path.abspath(__file__))
OPEN_BROWSER = True
DEF = None

# A raw string definition in a Lean file: `def NAME : String := r#"`, closed by `"#`.
RAW = re.compile(r'def\s+([^\s:]+)\s*:\s*String\s*:=\s*r(#+)"')


def raw_strings(full):
    """The raw string definitions of a Lean file, in order: (name, match,
    closing delimiter, end of the contents or -1 if not closed).  A string's
    contents end at the first `"` followed by its own number of `#`, so a
    `"#` inside an `r##"…"##` string does not end it; a definition inside an
    earlier string's contents is not one."""
    out, pos = [], 0
    while True:
        m = RAW.search(full, pos)
        if not m:
            return out
        close = '"' + m.group(2)
        end = full.find(close, m.end())
        out.append((m.group(1), m, close, end))
        if end < 0:
            return out
        pos = end + len(close)


class Source:
    """Where the figure text lives: a whole file, or the contents of one raw
    string in a Lean file.  `split` returns (before, text, after, kind, line
    offset of the text in the file); the file is always re-read, so a change
    on disk is seen.  A Lean file may hold several strings: `name` is the one
    being edited (the first, unless `--def NAME` or the page chooses another),
    and `strings` lists them all."""

    def __init__(self, path, name):
        self.path, self.name = path, name
        self.lean = path.endswith('.lean')

    def strings(self, full):
        return [{'name': n, 'line': full[:m.start()].count('\n') + 1}
                for n, m, _, _ in raw_strings(full)] if self.lean else []

    def split(self, full):
        if not self.lean:
            return '', full, '', 'figure file', 0
        all_ = raw_strings(full)
        if not all_:
            raise ValueError(f'no raw string definition in {self.path} '
                             '(expected def NAME : String := r#"…"#)')
        ms = [x for x in all_ if self.name in (None, x[0])]
        if not ms:
            raise ValueError(f'no raw string definition {self.name} in {self.path} '
                             f'(it has {", ".join(x[0] for x in all_)})')
        names = [x[0] for x in all_]
        if self.name is not None and names.count(self.name) > 1:
            raise ValueError(f'{self.path} defines the string {self.name} more than once')
        _, m, close, end = ms[0]
        if end < 0:
            raise ValueError(f'the string {m.group(1)} is not closed by {close}')
        self.name = m.group(1)
        self.close = close
        return (full[:m.end()], full[m.end():end], full[end:], f'Lean string {m.group(1)}',
                full[:m.end()].count('\n'))

    def read(self):
        with open(self.path, encoding='utf-8') as f:
            full = f.read()
        return (full,) + self.split(full)


SKIP = {'.git', '.lake', '_build', 'node_modules', '.claude', 'archive'}


def uses(root, src_path, names):
    """Where each figure is used: Lean terms (`fig_of% SRC "N"`)
    and TeX (`\\diag{N}`, `\\diag[…]{N_B}`, `\\formula{N}`), as `path:line`."""
    pats = {n: re.compile(r'(_fig%|fig_of%)[^\n]*"' + re.escape(n) + r'"|\\(diag|formula)(\[[^\]]*\])?\{'
                          + re.escape(n) + r'(_B)?\}') for n in names}
    out = {n: [] for n in names}
    for d, subdirs, files in os.walk(root):
        subdirs[:] = [x for x in subdirs if x not in SKIP]
        for fn in files:
            if not fn.endswith(('.lean', '.tex')):
                continue
            p = os.path.join(d, fn)
            if os.path.abspath(p) == src_path:
                continue
            try:
                lines = open(p, encoding='utf-8').read().split('\n')
            except (UnicodeDecodeError, OSError):
                continue
            for i, line in enumerate(lines):
                for n, pat in pats.items():
                    if pat.search(line):
                        out[n].append(f'{os.path.relpath(p, root)}:{i + 1}')
    return out


def args():
    a = sys.argv[1:]
    if not a or a[0].startswith('-'):
        sys.exit(__doc__)
    path, port, lake = os.path.abspath(a[0]), 8765, os.path.dirname(os.path.dirname(HERE))
    global OPEN_BROWSER, DEF
    i = 1
    while i < len(a):
        if a[i] == '--no-browser':
            OPEN_BROWSER = False; i += 1
        elif a[i] == '--def':
            DEF = a[i + 1]; i += 2
        elif a[i] == '--port':
            port = int(a[i + 1]); i += 2
        elif a[i] == '--lake-dir':
            lake = os.path.abspath(a[i + 1]); i += 2
        else:
            sys.exit(f'framedit: unknown argument {a[i]}\n{__doc__}')
    return path, port, lake


class Lean:
    """One `framediag --serve` process; requests are serialised."""

    def __init__(self, exe):
        self.p = subprocess.Popen([exe, '--serve'], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, encoding='utf-8', bufsize=1)
        self.lock = threading.Lock()

    def ask(self, req):
        with self.lock:
            self.p.stdin.write(json.dumps(req, ensure_ascii=False) + '\n')
            self.p.stdin.flush()
            line = self.p.stdout.readline()
        if not line:
            return {'ok': False, 'error': 'the Lean server stopped'}
        return json.loads(line)


def digest(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def tool_info(exe, repo):
    """The version of the tools in use: `framediag --version`, and the commit
    of the package (short hash, tag if any, commit date and time, whether the
    working tree has changes), shown at the top of the page."""
    def run(*cmd):
        try:
            r = subprocess.run(cmd, cwd=repo, capture_output=True, text=True, timeout=10)
            return r.stdout.strip() if r.returncode == 0 else ''
        except OSError:
            return ''
    version = run(exe, '--version').replace('frege-diagrams ', '')
    commit = run('git', 'rev-parse', '--short', 'HEAD')
    tag = run('git', 'describe', '--tags', '--exact-match')
    date = run('git', 'log', '-1', '--format=%cd', '--date=format:%Y-%m-%d %H:%M')
    dirty = bool(run('git', 'status', '--porcelain', '--untracked-files=no'))
    parts = [f'frege-diagrams v{version}' if version else 'frege-diagrams']
    parts += [p for p in (commit + (' (modified)' if dirty else '') if commit else '', tag, date) if p]
    return {'version': version, 'commit': commit, 'tag': tag, 'date': date, 'dirty': dirty,
            'line': ' · '.join(parts)}


def main():
    path, port, lake = args()
    if not os.path.exists(path):
        sys.exit(f'framedit: no such file {path}')
    src = Source(path, DEF)
    try:
        src.read()
    except ValueError as e:
        sys.exit(f'framedit: {e}')
    g = subprocess.run(['git', '-C', os.path.dirname(path), 'rev-parse', '--show-toplevel'],
                       capture_output=True, text=True)
    root = g.stdout.strip() if g.returncode == 0 else os.path.dirname(path)
    print('framedit: building framediag ...', flush=True)
    b = subprocess.run(['lake', 'build', 'framediag'], cwd=lake)
    if b.returncode != 0:
        sys.exit('framedit: lake build framediag failed')
    exe = os.path.join(lake, '.lake', 'build', 'bin', 'framediag')
    tool = tool_info(exe, lake)
    print(f'framedit: {tool["line"]}', flush=True)
    fast, slow = Lean(exe), Lean(exe)

    class H(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def send(self, code, body, ctype='application/json; charset=utf-8'):
            data = body.encode('utf-8') if isinstance(body, str) else body
            self.send_response(code)
            self.send_header('Content-Type', ctype)
            self.send_header('Content-Length', str(len(data)))
            self.send_header('Cache-Control', 'no-store')
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            if self.path in ('/', '/index.html') or self.path.startswith('/#'):
                with open(os.path.join(HERE, 'index.html'), encoding='utf-8') as f:
                    self.send(200, f.read(), 'text/html; charset=utf-8')
            elif self.path == '/api/file':
                full, _, t, _, kind, off = src.read()
                self.send(200, json.dumps({'path': path, 'kind': kind, 'lineOffset': off, 'root': root,
                                           'text': t, 'hash': digest(full), 'tool': tool,
                                           'strings': src.strings(full), 'def': src.name},
                                          ensure_ascii=False))
            else:
                self.send(404, json.dumps({'error': 'not found'}))

        def do_POST(self):
            n = int(self.headers.get('Content-Length', 0))
            req = json.loads(self.rfile.read(n).decode('utf-8'))
            if self.path == '/api/lean':
                slow_op = req.get('op') == 'check' or (req.get('op') == 'render' and req.get('only') == 'b')
                self.send(200, json.dumps((slow if slow_op else fast).ask(req), ensure_ascii=False))
            elif self.path == '/api/select':
                # edit another raw string of the same Lean file
                old = src.name
                src.name = req.get('name')
                try:
                    src.read()
                    self.send(200, json.dumps({'ok': True}))
                except ValueError as e:
                    src.name = old
                    self.send(400, json.dumps({'ok': False, 'error': str(e)}, ensure_ascii=False))
            elif self.path == '/api/uses':
                self.send(200, json.dumps(uses(root, path, req.get('names', [])), ensure_ascii=False))
            elif self.path == '/api/save':
                text = req['text']
                full, before, disk, after, _, _ = src.read()
                if digest(full) != req.get('base'):
                    self.send(409, json.dumps({'ok': False, 'error': 'The file changed on disk since it was read; nothing was written.',
                                               'text': disk, 'hash': digest(full)}, ensure_ascii=False))
                    return
                if src.lean and src.close in text:
                    self.send(400, json.dumps({'ok': False, 'error': f'Not saved: the text contains {src.close}, which would end the Lean string early.'}))
                    return
                r = fast.ask({'op': 'parse', 'text': text})
                if not r.get('ok'):
                    self.send(400, json.dumps({'ok': False, 'error': 'Not saved: the text does not parse: ' + r.get('error', '')}, ensure_ascii=False))
                    return
                new = before + text + after
                tmp = path + '.framedit-tmp'
                with open(tmp, 'w', encoding='utf-8') as f:
                    f.write(new)
                os.replace(tmp, path)
                self.send(200, json.dumps({'ok': True, 'hash': digest(new)}))
            else:
                self.send(404, json.dumps({'error': 'not found'}))

    srv = http.server.ThreadingHTTPServer(('127.0.0.1', port), H)
    url = f'http://127.0.0.1:{port}/'
    print(f'framedit: editing {path} ({src.split(src.read()[0])[3]})\nframedit: open {url}  (Ctrl-C to stop)', flush=True)
    if OPEN_BROWSER:
        webbrowser.open(url)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == '__main__':
    main()
