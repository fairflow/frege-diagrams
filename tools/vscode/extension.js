// @ts-check
/*
 * Frege Diagrams for VS Code (docs/design/VSCODE.md).
 *
 * A custom editor for figure files (*.fgd): the page of the browser editor
 * (tools/framedit/index.html) in a webview, talking to the same Lean drawing
 * server (`framediag --serve`).  The page sends the requests it would send to
 * framedit.py as messages; `handle` answers them in the same form.  The file
 * is a VS Code document: saving goes through VS Code, and a change made
 * elsewhere (a text editor, the disk) is passed on to the page.
 *
 * Plain JavaScript, type-checked by `// @ts-check` against the VS Code API
 * declarations, so there is no build step.
 */
const vscode = require('vscode');
const cp = require('child_process');
const fs = require('fs');
const os = require('os');
const path = require('path');
const crypto = require('crypto');

/** One `framediag --serve` process; requests are answered in order. */
class Server {
  /** @param {string} exe */
  constructor(exe) {
    this.p = cp.spawn(exe, ['--serve'], { stdio: ['pipe', 'pipe', 'pipe'] });
    this.buf = '';
    /** @type {((line: string | null) => void)[]} */
    this.waiting = [];
    this.dead = false;
    this.p.stdout.setEncoding('utf8');
    this.p.stdout.on('data', (d) => {
      this.buf += d;
      let i;
      while ((i = this.buf.indexOf('\n')) >= 0) {
        const line = this.buf.slice(0, i);
        this.buf = this.buf.slice(i + 1);
        const k = this.waiting.shift();
        if (k) k(line);
      }
    });
    this.p.on('exit', () => {
      this.dead = true;
      for (const k of this.waiting.splice(0)) k(null);
    });
    this.p.on('error', () => {
      this.dead = true;
      for (const k of this.waiting.splice(0)) k(null);
    });
  }

  /** @param {any} req @returns {Promise<any>} */
  ask(req) {
    return new Promise((resolve) => {
      if (this.dead) return resolve({ ok: false, error: 'the Lean server stopped' });
      this.waiting.push((line) => resolve(line ? JSON.parse(line) : { ok: false, error: 'the Lean server stopped' }));
      this.p.stdin.write(JSON.stringify(req) + '\n');
    });
  }

  dispose() { this.p.kill(); }
}

/** @param {string} text */
const digest = (text) => crypto.createHash('sha256').update(text, 'utf8').digest('hex');

/** @param {string} cmd @param {string[]} args @param {string} cwd */
function run(cmd, args, cwd) {
  try {
    return cp.execFileSync(cmd, args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'], timeout: 10000 }).trim();
  } catch {
    return '';
  }
}

/**
 * Where the tools are for a document: the workspace folder, the package
 * directory of frege-diagrams (a dependency in .lake/packages, or the
 * workspace itself), and the framediag program.
 * @param {vscode.Uri} uri
 */
function locate(uri) {
  const folder = vscode.workspace.getWorkspaceFolder(uri);
  const root = folder ? folder.uri.fsPath : path.dirname(uri.fsPath);
  const cfg = vscode.workspace.getConfiguration('fregeDiagrams');
  let pkg = path.join(root, '.lake', 'packages', 'frege-diagrams');
  if (!fs.existsSync(pkg)) {
    const lf = path.join(root, 'lakefile.toml');
    if (fs.existsSync(lf) && /name\s*=\s*"frege-diagrams"/.test(fs.readFileSync(lf, 'utf8'))) pkg = root;
  }
  const exe = cfg.get('framediagPath') || path.join(pkg, '.lake', 'build', 'bin', 'framediag');
  const elanLake = path.join(os.homedir(), '.elan', 'bin', 'lake');
  const lake = cfg.get('lakePath') || (fs.existsSync(elanLake) ? elanLake : 'lake');
  return { root, pkg, exe: String(exe), lake: String(lake) };
}

/** Build framediag with Lake in the workspace when it is missing. */
async function ensureBuilt(/** @type {ReturnType<typeof locate>} */ loc) {
  if (fs.existsSync(loc.exe)) return true;
  return vscode.window.withProgress(
    { location: vscode.ProgressLocation.Notification, title: 'Frege Diagrams: building framediag (lake build framediag)…' },
    () => new Promise((resolve) => {
      cp.execFile(loc.lake, ['build', 'framediag'], { cwd: loc.root, maxBuffer: 64 * 1024 * 1024 }, (err) => {
        if (err || !fs.existsSync(loc.exe)) {
          vscode.window.showErrorMessage(`Frege Diagrams: could not build framediag in ${loc.root} (${err ? err.message : 'no program at ' + loc.exe}). ` +
            'The workspace must require frege-diagrams in its lakefile, or set fregeDiagrams.framediagPath.');
          resolve(false);
        } else resolve(true);
      });
    }));
}

/** The version line of the page header: version, commit, tag, date. */
function toolInfo(/** @type {ReturnType<typeof locate>} */ loc) {
  const version = run(loc.exe, ['--version'], loc.root).replace('frege-diagrams ', '');
  const commit = run('git', ['rev-parse', '--short', 'HEAD'], loc.pkg);
  const tag = run('git', ['describe', '--tags', '--exact-match'], loc.pkg);
  const date = run('git', ['log', '-1', '--format=%cd', '--date=format:%Y-%m-%d %H:%M'], loc.pkg);
  const dirty = !!run('git', ['status', '--porcelain', '--untracked-files=no'], loc.pkg);
  const parts = [version ? `frege-diagrams v${version}` : 'frege-diagrams'];
  if (commit) parts.push(commit + (dirty ? ' (modified)' : ''));
  if (tag) parts.push(tag);
  if (date) parts.push(date);
  return { version, commit, tag, date, dirty, line: parts.join(' · ') + ' · VS Code' };
}

/** The page: from the package the program comes from, so that the two
match; else (no page there, or one older than 0.7.0 that cannot talk to VS
Code) the copy in the extension. */
function pageHtml(/** @type {ReturnType<typeof locate>} */ loc, /** @type {string} */ extDir) {
  const fromPkg = path.join(loc.pkg, 'tools', 'framedit', 'index.html');
  if (fs.existsSync(fromPkg)) {
    const html = fs.readFileSync(fromPkg, 'utf8');
    if (html.includes('acquireVsCodeApi')) return html;
  }
  return fs.readFileSync(path.join(extDir, 'media', 'index.html'), 'utf8');
}

const SKIP = new Set(['.git', '.lake', '_build', 'node_modules', '.claude', 'archive']);

/** Where each figure is used: `fig_of% SRC "N"` in Lean, `\diag{N}`, `\formula{N}` in TeX. */
function uses(/** @type {string} */ root, /** @type {string} */ self, /** @type {string[]} */ names) {
  const esc = (/** @type {string} */ s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const pats = Object.fromEntries(names.map((n) => [n, new RegExp('(_fig%|fig_of%)[^\\n]*"' + esc(n) + '"|\\\\(diag|formula)(\\[[^\\]]*\\])?\\{' + esc(n) + '(_B)?\\}')]));
  /** @type {Record<string, string[]>} */
  const out = Object.fromEntries(names.map((n) => [n, []]));
  const walk = (/** @type {string} */ d) => {
    let ents = [];
    try { ents = fs.readdirSync(d, { withFileTypes: true }); } catch { return; }
    for (const e of ents) {
      const p = path.join(d, e.name);
      if (e.isDirectory()) { if (!SKIP.has(e.name)) walk(p); continue; }
      if (!/\.(lean|tex)$/.test(e.name) || p === self) continue;
      let lines;
      try { lines = fs.readFileSync(p, 'utf8').split('\n'); } catch { continue; }
      lines.forEach((line, i) => {
        for (const n of names) if (pats[n].test(line)) out[n].push(`${path.relative(root, p)}:${i + 1}`);
      });
    }
  };
  walk(root);
  return out;
}

/**
 * A request of the page, answered as framedit.py would.
 * @param {{doc: vscode.TextDocument, loc: ReturnType<typeof locate>, fast: Server, slow: Server, tool: any, saving: {on: boolean}}} ed
 * @param {string} p @param {any} body
 * @returns {Promise<{status: number, body: any}>}
 */
async function handle(ed, p, body) {
  const text = ed.doc.getText();
  switch (p) {
    case '/api/lean': {
      const slow = body.op === 'check' || (body.op === 'render' && body.only === 'b');
      return { status: 200, body: await (slow ? ed.slow : ed.fast).ask(body) };
    }
    case '/api/file':
      return { status: 200, body: { path: ed.doc.uri.fsPath, kind: 'figure file', lineOffset: 0, root: ed.loc.root,
        text, hash: digest(text), tool: ed.tool, strings: [], def: null } };
    case '/api/save': {
      if (digest(text) !== body.base)
        return { status: 409, body: { ok: false, error: 'The file changed since the editor read it; nothing was written.', text, hash: digest(text) } };
      const r = await ed.fast.ask({ op: 'parse', text: body.text });
      if (!r.ok) return { status: 400, body: { ok: false, error: 'Not saved: the text does not parse: ' + (r.error || '') } };
      const edit = new vscode.WorkspaceEdit();
      edit.replace(ed.doc.uri, new vscode.Range(ed.doc.positionAt(0), ed.doc.positionAt(text.length)), body.text);
      ed.saving.on = true;
      try {
        await vscode.workspace.applyEdit(edit);
        await ed.doc.save();
      } finally { ed.saving.on = false; }
      return { status: 200, body: { ok: true, hash: digest(ed.doc.getText()) } };
    }
    case '/api/uses':
      return { status: 200, body: uses(ed.loc.root, ed.doc.uri.fsPath, body.names || []) };
    case '/api/select':
      return { status: 400, body: { ok: false, error: 'A figure file holds one text; strings are chosen in Lean files.' } };
    default:
      return { status: 404, body: { error: 'not found' } };
  }
}

/** @implements {vscode.CustomTextEditorProvider} */
class FigureEditor {
  /** @param {vscode.ExtensionContext} ctx */
  constructor(ctx) { this.ctx = ctx; }

  /** @param {vscode.TextDocument} doc @param {vscode.WebviewPanel} panel */
  async resolveCustomTextEditor(doc, panel) {
    const loc = locate(doc.uri);
    panel.webview.options = { enableScripts: true };
    if (!(await ensureBuilt(loc))) {
      panel.webview.html = `<p>framediag is not available: see the error message.</p>`;
      return;
    }
    const ed = { doc, loc, fast: new Server(loc.exe), slow: new Server(loc.exe), tool: toolInfo(loc), saving: { on: false } };
    panel.webview.html = pageHtml(loc, this.ctx.extensionPath);
    const subs = [
      panel.webview.onDidReceiveMessage(async (m) => {
        if (!m || m.type !== 'api') return;
        let reply;
        try { reply = await handle(ed, m.path, m.body); } catch (e) { reply = { status: 500, body: { ok: false, error: String(e) } }; }
        panel.webview.postMessage({ type: 'reply', id: m.id, status: reply.status, body: reply.body });
      }),
      vscode.workspace.onDidChangeTextDocument((e) => {
        if (e.document === doc && !ed.saving.on && e.contentChanges.length) panel.webview.postMessage({ type: 'reload' });
      }),
    ];
    panel.onDidDispose(() => { subs.forEach((s) => s.dispose()); ed.fast.dispose(); ed.slow.dispose(); });
  }
}

/** @param {vscode.ExtensionContext} ctx */
function activate(ctx) {
  ctx.subscriptions.push(vscode.window.registerCustomEditorProvider('fregeDiagrams.figureEditor', new FigureEditor(ctx), {
    webviewOptions: { retainContextWhenHidden: true },
  }));
}

function deactivate() {}

module.exports = { activate, deactivate, Server, handle, uses, locate, digest };
