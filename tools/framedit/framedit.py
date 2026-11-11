#!/usr/bin/env python3
"""framedit: the figure editor of FregeDiagrams/ (see docs/design/EDITOR.md).

    python3 -I tools/framedit/framedit.py FILE [--def NAME] [--port 8765] [--lake-dir DIR] [--no-browser]

FILE is a file of figures in the syntax of FregeDiagrams/Syntax.lean (as for
`framediag --fig FILE`), or a Lean file holding the figures in a raw string
`def NAME : String := r#"…"#` (such as `exampleSource` in
FregeDiagrams/Examples.lean).  For a Lean file only the string's contents are
edited and written back; `--def NAME` picks the string when the file has more
than one.  Opens http://127.0.0.1:PORT/ (this machine only).

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


class Source:
    """Where the figure text lives: a whole file, or the contents of one raw
    string in a Lean file.  `split` returns (before, text, after, kind, line
    offset of the text in the file); the file is always re-read, so a change
    on disk is seen."""

    def __init__(self, path, name):
        self.path, self.name = path, name
        self.lean = path.endswith('.lean')

    def split(self, full):
        if not self.lean:
            return '', full, '', 'figure file', 0
        ms = [m for m in RAW.finditer(full) if self.name in (None, m.group(1))]
        if not ms:
            raise ValueError(f'no raw string definition {self.name or ""} in {self.path} '
                             '(expected def NAME : String := r#"…"#)')
        if len(ms) > 1:
            raise ValueError(f'{self.path} has several raw string definitions '
                             f'({", ".join(m.group(1) for m in ms)}); choose one with --def NAME')
        m = ms[0]
        close = '"' + m.group(2)
        end = full.find(close, m.end())
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
                                           'text': t, 'hash': digest(full)}, ensure_ascii=False))
            else:
                self.send(404, json.dumps({'error': 'not found'}))

        def do_POST(self):
            n = int(self.headers.get('Content-Length', 0))
            req = json.loads(self.rfile.read(n).decode('utf-8'))
            if self.path == '/api/lean':
                slow_op = req.get('op') == 'check' or (req.get('op') == 'render' and req.get('only') == 'b')
                self.send(200, json.dumps((slow if slow_op else fast).ask(req), ensure_ascii=False))
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
