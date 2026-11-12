// Smoke test of the extension's request handling, outside VS Code: the
// `vscode` module is replaced by a small stand-in, and a real framediag
// (built at the repository root) draws.  Run: npm test
const Module = require('module');
const path = require('path');
const fs = require('fs');
const os = require('os');
const assert = require('assert');

const repo = path.join(__dirname, '..', '..', '..');
const file = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'fgd-')), 'smoke.fgd');
fs.writeFileSync(file, 'fig one = all t. s <= t\n');

let docText = fs.readFileSync(file, 'utf8');
const doc = {
  uri: { fsPath: file },
  getText: () => docText,
  positionAt: (n) => n,
  save: async () => { fs.writeFileSync(file, docText); return true; },
};
const vscodeStub = {
  workspace: {
    getWorkspaceFolder: () => ({ uri: { fsPath: repo } }),
    getConfiguration: () => ({ get: () => '' }),
    applyEdit: async (e) => { for (const [, r, t] of e.ops) docText = docText.slice(0, r.a) + t + docText.slice(r.b); return true; },
    onDidChangeTextDocument: () => ({ dispose() {} }),
  },
  WorkspaceEdit: class { constructor() { this.ops = []; } replace(u, r, t) { this.ops.push([u, r, t]); } },
  Range: class { constructor(a, b) { this.a = a; this.b = b; } },
  window: {}, ProgressLocation: {},
};
const load = Module._load;
Module._load = function (req, ...rest) { return req === 'vscode' ? vscodeStub : load.call(this, req, ...rest); };
const ext = require('../extension.js');

(async () => {
  const loc = ext.locate(doc.uri);
  assert.strictEqual(loc.pkg, repo, 'frege-diagrams itself is its own package');
  assert.ok(fs.existsSync(loc.exe), 'framediag is built (lake build framediag at the repository root)');
  const ed = { doc, loc, fast: new ext.Server(loc.exe), slow: new ext.Server(loc.exe), tool: { line: 'test' }, saving: { on: false } };

  const f = await ext.handle(ed, '/api/file');
  assert.strictEqual(f.body.text, 'fig one = all t. s <= t\n');
  const p = await ext.handle(ed, '/api/lean', { op: 'parse', text: f.body.text });
  assert.deepStrictEqual(p.body.figs.map((x) => x.name), ['one']);
  const r = await ext.handle(ed, '/api/lean', { op: 'render', text: f.body.text, fig: 'one', opts: {}, only: 'b' });
  assert.ok(r.body.ok && r.body.b.startsWith('<svg'), 'view B is drawn (slow server)');
  const e = await ext.handle(ed, '/api/lean', { op: 'edit', text: f.body.text, fig: 'one', edit: { kind: 'judgement', v: 'content' } });
  assert.strictEqual(e.body.text, 'fig one [judgement content] = all t. s <= t\n');

  // saving: refused against a stale base, refused for text that does not parse, else written
  assert.strictEqual((await ext.handle(ed, '/api/save', { text: e.body.text, base: 'stale' })).status, 409);
  assert.strictEqual((await ext.handle(ed, '/api/save', { text: 'fig =', base: f.body.hash })).status, 400);
  const s = await ext.handle(ed, '/api/save', { text: e.body.text, base: f.body.hash });
  assert.strictEqual(s.status, 200);
  assert.strictEqual(fs.readFileSync(file, 'utf8'), e.body.text);
  assert.strictEqual(s.body.hash, ext.digest(e.body.text));

  const u = await ext.handle(ed, '/api/uses', { names: ['ex_trans'] });
  assert.ok(Array.isArray(u.body.ex_trans));
  assert.strictEqual((await ext.handle(ed, '/api/select', { name: 'x' })).status, 400);

  ed.fast.dispose(); ed.slow.dispose();
  console.log('smoke test: ok');
})().catch((err) => { console.error(err); process.exit(1); });
