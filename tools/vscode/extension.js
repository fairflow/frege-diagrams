// @ts-check
/*
 * Frege Diagrams for VS Code (docs/design/VSCODE.md).
 *
 * A custom editor for figure files (*.fgd), and an "Edit figures" code lens
 * above each figure string `def NAME : String := r#"…"#` of a Lean file, which
 * opens the same editor on that string beside the Lean file.  The editor is
 * the page of the browser editor
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
  // the Lake project the file belongs to: the nearest folder above it with a
  // lakefile, whatever folder the window has open (a file may be opened from
  // another project); else the workspace folder; else the file's own folder
  const folder = vscode.workspace.getWorkspaceFolder(uri);
  const root = lakeRoot(path.dirname(uri.fsPath)) || (folder ? folder.uri.fsPath : path.dirname(uri.fsPath));
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

/** The nearest folder at or above `dir` holding a lakefile, or null. */
function lakeRoot(/** @type {string} */ dir) {
  for (let d = dir; ; d = path.dirname(d)) {
    if (fs.existsSync(path.join(d, 'lakefile.toml')) || fs.existsSync(path.join(d, 'lakefile.lean'))) return d;
    if (path.dirname(d) === d) return null;
  }
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

/* The raw string definitions of a Lean file, as framedit.py and
   FregeDiagrams.leanRawStrings find them: each string ends at the first `"`
   followed by its own number of `#`, and a `def` inside a string's contents
   is not a definition. */
const RAW = /def\s+([^\s:]+)\s*:\s*String\s*:=\s*r(#+)"/g;
/** @param {string} full @returns {{name: string, defAt: number, start: number, end: number, close: string}[]} */
function rawStrings(full) {
  const out = [];
  let pos = 0;
  for (;;) {
    RAW.lastIndex = pos;
    const m = RAW.exec(full);
    if (!m) return out;
    const close = '"' + m[2], start = m.index + m[0].length, end = full.indexOf(close, start);
    out.push({ name: m[1], defAt: m.index, start, end, close });
    if (end < 0) return out;
    pos = end + close.length;
  }
}

/**
 * Where the figure text lives in a document: the whole of a figure file, or
 * the contents of one raw string of a Lean file (`name`; the first if null).
 * `read` looks it up afresh each time, so it follows edits of the document.
 * @param {vscode.TextDocument} doc @param {boolean} lean @param {string | null} name
 */
function makeSource(doc, lean, name) {
  return {
    doc, lean, name,
    read() {
      const full = doc.getText();
      if (!lean) return { full, text: full, start: 0, end: full.length, kind: 'figure file', off: 0, close: '', strings: [] };
      const all = rawStrings(full);
      if (!all.length) throw new Error('this Lean file has no figure string (def NAME : String := r#"…"#)');
      const s = all.find((x) => this.name === null || x.name === this.name);
      if (!s) throw new Error(`no figure string ${this.name} in this file`);
      if (s.end < 0) throw new Error(`the string ${s.name} is not closed by ${s.close}`);
      this.name = s.name;
      return { full, text: full.slice(s.start, s.end), start: s.start, end: s.end, kind: `Lean string ${s.name}`,
        off: full.slice(0, s.start).split('\n').length - 1, close: s.close,
        strings: all.map((x) => ({ name: x.name, line: full.slice(0, x.defAt).split('\n').length })) };
    },
  };
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
 * @param {{src: ReturnType<typeof makeSource>, loc: ReturnType<typeof locate>, fast: Server, slow: Server, tool: any, saving: {on: boolean}}} ed
 * @param {string} p @param {any} body
 * @returns {Promise<{status: number, body: any}>}
 */
async function handle(ed, p, body) {
  const doc = ed.src.doc;
  /** @type {ReturnType<ReturnType<typeof makeSource>['read']>} */
  let r;
  try { r = ed.src.read(); } catch (e) { return { status: 400, body: { ok: false, error: String(e instanceof Error ? e.message : e) } }; }
  switch (p) {
    case '/api/lean': {
      const slow = body.op === 'check' || (body.op === 'render' && body.only === 'b');
      return { status: 200, body: await (slow ? ed.slow : ed.fast).ask(body) };
    }
    case '/api/file':
      return { status: 200, body: { path: doc.uri.fsPath, kind: r.kind, lineOffset: r.off, root: ed.loc.root,
        text: r.text, hash: digest(r.full), tool: ed.tool, strings: r.strings, def: ed.src.lean ? ed.src.name : null } };
    case '/api/save': {
      if (digest(r.full) !== body.base)
        return { status: 409, body: { ok: false, error: 'The file changed since the editor read it; nothing was written.', text: r.text, hash: digest(r.full) } };
      if (r.close && body.text.includes(r.close))
        return { status: 400, body: { ok: false, error: `Not saved: the text contains ${r.close}, which would end the Lean string early.` } };
      const parsed = await ed.fast.ask({ op: 'parse', text: body.text });
      if (!parsed.ok) return { status: 400, body: { ok: false, error: 'Not saved: the text does not parse: ' + (parsed.error || '') } };
      const edit = new vscode.WorkspaceEdit();
      edit.replace(doc.uri, new vscode.Range(doc.positionAt(r.start), doc.positionAt(r.end)), body.text);
      ed.saving.on = true;
      try {
        await vscode.workspace.applyEdit(edit);
        await doc.save();
      } finally { ed.saving.on = false; }
      return { status: 200, body: { ok: true, hash: digest(doc.getText()) } };
    }
    case '/api/uses':
      return { status: 200, body: uses(ed.loc.root, doc.uri.fsPath, body.names || []) };
    case '/api/select': {
      if (!ed.src.lean) return { status: 400, body: { ok: false, error: 'A figure file holds one text; strings are chosen in Lean files.' } };
      const old = ed.src.name;
      ed.src.name = body.name;
      try { ed.src.read(); } catch (e) { ed.src.name = old; return { status: 400, body: { ok: false, error: String(e instanceof Error ? e.message : e) } }; }
      return { status: 200, body: { ok: true } };
    }
    default:
      return { status: 404, body: { error: 'not found' } };
  }
}

/**
 * Put the figure editor into a webview panel, for a source of figure text.
 * @param {vscode.WebviewPanel} panel @param {ReturnType<typeof makeSource>} src @param {string} extDir
 */
async function attach(panel, src, extDir) {
  const doc = src.doc, loc = locate(doc.uri);
  panel.webview.options = { enableScripts: true };
  if (!(await ensureBuilt(loc))) {
    panel.webview.html = `<p>framediag is not available: see the error message.</p>`;
    return;
  }
  const ed = { src, loc, fast: new Server(loc.exe), slow: new Server(loc.exe), tool: toolInfo(loc), saving: { on: false } };
  panel.webview.html = pageHtml(loc, extDir);
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

/** @implements {vscode.CustomTextEditorProvider} */
class FigureEditor {
  /** @param {vscode.ExtensionContext} ctx */
  constructor(ctx) { this.ctx = ctx; }

  /** @param {vscode.TextDocument} doc @param {vscode.WebviewPanel} panel */
  async resolveCustomTextEditor(doc, panel) {
    await attach(panel, makeSource(doc, false, null), this.ctx.extensionPath);
  }
}

/** "Edit figures" above each figure string of a Lean file. @implements {vscode.CodeLensProvider} */
class FigureLenses {
  /** @param {vscode.TextDocument} doc */
  provideCodeLenses(doc) {
    return rawStrings(doc.getText()).filter((s) => s.end >= 0).map((s) => {
      const line = doc.positionAt(s.defAt).line;
      return new vscode.CodeLens(new vscode.Range(line, 0, line, 0),
        { title: 'Edit figures', command: 'fregeDiagrams.editFigures', arguments: [doc.uri.toString(), s.name],
          tooltip: `Open the figure editor on the string ${s.name}, beside this file` });
    });
  }
}

/** Open the figure editor on string `name` of a Lean file (the active one if no uri). */
async function editFigures(/** @type {vscode.ExtensionContext} */ ctx, /** @type {string | undefined} */ uriStr, /** @type {string | undefined} */ name) {
  const doc = uriStr ? await vscode.workspace.openTextDocument(vscode.Uri.parse(uriStr)) : vscode.window.activeTextEditor && vscode.window.activeTextEditor.document;
  if (!doc) { vscode.window.showInformationMessage('Frege Diagrams: open a Lean file with a figure string first.'); return; }
  const src = makeSource(doc, true, name || null);
  try { src.read(); } catch (e) { vscode.window.showErrorMessage(`Frege Diagrams: ${e instanceof Error ? e.message : e}`); return; }
  const panel = vscode.window.createWebviewPanel('fregeDiagrams.leanFigures', `Figures: ${src.name}`, vscode.ViewColumn.Beside,
    { enableScripts: true, retainContextWhenHidden: true });
  await attach(panel, src, ctx.extensionPath);
}

/* ---------- squiggles: parse errors and the checks of every figure ---------- */

/** One drawing server per framediag program, for diagnostics (started when needed). */
const diagServers = new Map();
/** @param {ReturnType<typeof locate>} loc @returns {Server | null} */
function diagServer(loc) {
  if (!fs.existsSync(loc.exe)) return null;
  let srv = diagServers.get(loc.exe);
  if (!srv || srv.dead) { srv = new Server(loc.exe); diagServers.set(loc.exe, srv); }
  return srv;
}

/** The figure texts of a document: a figure file whole, or each string of a Lean file. */
function figureTexts(/** @type {vscode.TextDocument} */ doc) {
  const full = doc.getText();
  if (doc.uri.fsPath.endsWith('.fgd')) return [{ text: full, start: 0 }];
  if (doc.uri.fsPath.endsWith('.lean')) return rawStrings(full).filter((x) => x.end >= 0).map((x) => ({ text: full.slice(x.start, x.end), start: x.start }));
  return [];
}

/**
 * The problems of one figure text, with positions in the text (0-based line
 * and column): a parse error where the parser stopped; otherwise the checks
 * of each figure (`lint`), at the figure's name, with their fixes.
 * @param {Server} srv @param {string} text
 * @returns {Promise<{line: number, col: number, len: number, msg: string, sev: string, fix: null | {fig: string, edit: any, label: string}}[]>}
 */
async function diagnoseText(srv, text) {
  const p = await srv.ask({ op: 'parse', text });
  if (!p.ok) {
    const m = /^line (\d+), column (\d+): ([\s\S]*)$/.exec(p.error || '');
    return [{ line: m ? +m[1] - 1 : 0, col: m ? +m[2] - 1 : 0, len: 1, msg: m ? m[3] : String(p.error), sev: 'error', fix: null }];
  }
  const out = [];
  for (const f of p.figs) {
    const l = await srv.ask({ op: 'lint', text, fig: f.name });
    if (!l.ok || !l.items.length) continue;
    const esc = f.name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const m = new RegExp('(^|\\n)([ \\t]*fig[ \\t]+)' + esc + '(?![\\w\'′₀-₉])').exec(text);
    const at = m ? m.index + m[1].length + m[2].length : 0;
    const before = text.slice(0, at), line = before.split('\n').length - 1, col = at - (before.lastIndexOf('\n') + 1);
    for (const it of l.items)
      out.push({ line, col, len: f.name.length, msg: `${f.name}: ${it.msg}`, sev: it.sev, fix: it.fix ? { fig: f.name, edit: it.fix, label: it.fixLabel } : null });
  }
  return out;
}

/** Quick fixes, by document and diagnostic: the edit to apply to that figure text. */
const fixes = new Map();
const fixKey = (/** @type {vscode.Uri} */ u, /** @type {vscode.Diagnostic} */ d) => `${u.toString()}|${d.range.start.line}:${d.range.start.character}|${d.message}`;

/** @param {vscode.DiagnosticCollection} coll @param {vscode.TextDocument} doc */
async function refreshDiagnostics(coll, doc) {
  const texts = figureTexts(doc);
  if (!texts.length) { coll.delete(doc.uri); return; }
  const srv = diagServer(locate(doc.uri));
  if (!srv) return;
  const version = doc.version, diags = [];
  for (const { text, start } of texts) {
    const lineStart = text.split('\n').reduce((acc, l) => { acc.push(acc[acc.length - 1] + l.length + 1); return acc; }, [0]);
    for (const p of await diagnoseText(srv, text)) {
      const a = start + (lineStart[p.line] ?? 0) + p.col;
      const d = new vscode.Diagnostic(new vscode.Range(doc.positionAt(a), doc.positionAt(a + Math.max(1, p.len))), p.msg,
        p.sev === 'error' ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Warning);
      d.source = 'Frege Diagrams';
      if (p.fix) fixes.set(fixKey(doc.uri, d), { start, len: text.length, ...p.fix });
      diags.push(d);
    }
  }
  if (doc.version === version) coll.set(doc.uri, diags);
}

/** @implements {vscode.CodeActionProvider} */
class FigureFixes {
  /** @param {vscode.TextDocument} doc @param {vscode.Range} _r @param {vscode.CodeActionContext} ctx */
  provideCodeActions(doc, _r, ctx) {
    const out = [];
    for (const d of ctx.diagnostics) {
      const f = fixes.get(fixKey(doc.uri, d));
      if (!f) continue;
      const a = new vscode.CodeAction(f.label || 'Fix', vscode.CodeActionKind.QuickFix);
      a.diagnostics = [d];
      a.command = { title: f.label, command: 'fregeDiagrams.applyFix', arguments: [doc.uri.toString(), f] };
      out.push(a);
    }
    return out;
  }
}

/** Apply a check's fix: the server edits the figure text, which replaces it in the document. */
async function applyFix(/** @type {string} */ uriStr, /** @type {any} */ f) {
  const doc = await vscode.workspace.openTextDocument(vscode.Uri.parse(uriStr));
  const srv = diagServer(locate(doc.uri));
  if (!srv) return;
  const text = doc.getText().slice(f.start, f.start + f.len);
  const r = await srv.ask({ op: 'edit', text, fig: f.fig, edit: f.edit });
  if (!r.ok) { vscode.window.showErrorMessage(`Frege Diagrams: ${r.error}`); return; }
  const e = new vscode.WorkspaceEdit();
  e.replace(doc.uri, new vscode.Range(doc.positionAt(f.start), doc.positionAt(f.start + f.len)), r.text);
  await vscode.workspace.applyEdit(e);
}

/** @param {vscode.ExtensionContext} ctx */
function activate(ctx) {
  const coll = vscode.languages.createDiagnosticCollection('fregeDiagrams');
  /** @type {Map<string, NodeJS.Timeout>} */
  const timers = new Map();
  const schedule = (/** @type {vscode.TextDocument} */ doc, ms = 400) => {
    if (!figureTexts(doc).length && !coll.has(doc.uri)) return;
    const k = doc.uri.toString();
    clearTimeout(timers.get(k));
    timers.set(k, setTimeout(() => { timers.delete(k); refreshDiagnostics(coll, doc).catch(() => {}); }, ms));
  };
  ctx.subscriptions.push(
    coll,
    vscode.workspace.onDidOpenTextDocument((d) => schedule(d, 0)),
    vscode.workspace.onDidChangeTextDocument((e) => schedule(e.document)),
    vscode.workspace.onDidCloseTextDocument((d) => coll.delete(d.uri)),
    vscode.languages.registerCodeActionsProvider([{ pattern: '**/*.fgd' }, { pattern: '**/*.lean' }], new FigureFixes(),
      { providedCodeActionKinds: [vscode.CodeActionKind.QuickFix] }),
    vscode.commands.registerCommand('fregeDiagrams.applyFix', applyFix),
    { dispose: () => { for (const s of diagServers.values()) s.dispose(); } },
  );
  for (const d of vscode.workspace.textDocuments) schedule(d, 0);
  ctx.subscriptions.push(
    vscode.window.registerCustomEditorProvider('fregeDiagrams.figureEditor', new FigureEditor(ctx), {
      webviewOptions: { retainContextWhenHidden: true },
    }),
    vscode.languages.registerCodeLensProvider([{ language: 'lean4' }, { pattern: '**/*.lean' }], new FigureLenses()),
    vscode.commands.registerCommand('fregeDiagrams.editFigures', (u, n) => editFigures(ctx, u, n)),
  );
}

function deactivate() {}

module.exports = { activate, deactivate, Server, handle, uses, locate, lakeRoot, digest, rawStrings, makeSource, diagnoseText };
