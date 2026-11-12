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
  const ed = { src: ext.makeSource(doc, false, null), loc, fast: new ext.Server(loc.exe), slow: new ext.Server(loc.exe), tool: { line: 'test' }, saving: { on: false } };

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

  // a Lean file with two figure strings: the first by default, the other by /api/select;
  // a save replaces only that string's contents
  docText = 'import X\n\ndef figsA : String := r#"\nfig a = s <= t\n"#\n\ntheorem t : True := trivial\n\ndef figsB : String := r##"\n-- "# inside\nfig b = s R t\n"##\n';
  ed.src = ext.makeSource(doc, true, null);
  let lf = await ext.handle(ed, '/api/file');
  assert.strictEqual(lf.body.kind, 'Lean string figsA');
  assert.deepStrictEqual(lf.body.strings, [{ name: 'figsA', line: 3 }, { name: 'figsB', line: 9 }]);
  assert.strictEqual(lf.body.text, '\nfig a = s <= t\n');
  assert.strictEqual((await ext.handle(ed, '/api/select', { name: 'nope' })).status, 400);
  assert.strictEqual((await ext.handle(ed, '/api/select', { name: 'figsB' })).status, 200);
  lf = await ext.handle(ed, '/api/file');
  assert.strictEqual(lf.body.text, '\n-- "# inside\nfig b = s R t\n');
  assert.strictEqual(lf.body.lineOffset, 8);
  // a text that would end the string early is refused
  assert.strictEqual((await ext.handle(ed, '/api/save', { text: 'fig b = s R t "##', base: lf.body.hash })).status, 400);
  const before = docText;
  const sv = await ext.handle(ed, '/api/save', { text: '\nfig b [judgement content] = s R t\n', base: lf.body.hash });
  assert.strictEqual(sv.status, 200);
  assert.strictEqual(docText, before.replace('\n-- "# inside\nfig b = s R t\n', '\nfig b [judgement content] = s R t\n'));
  assert.ok(docText.includes('fig a = s <= t') && docText.includes('theorem t : True'));
  // rawStrings: unclosed, and a def inside a string is not one
  assert.deepStrictEqual(ext.rawStrings('def f : String := r#"\n-- def g : String := r#"\n"#').map((x) => x.name), ['f']);
  assert.strictEqual(ext.rawStrings('def f : String := r#"x').at(0).end, -1);

  // squiggles: a parse error at its line and column; a check at the figure's name, with its fix
  const d1 = await ext.diagnoseText(ed.fast, '\nfig a = s <= t\nfig b = s $ t\n');
  assert.deepStrictEqual(d1.map((x) => [x.line, x.col, x.sev]), [[2, 10, 'error']]);
  const d2 = await ext.diagnoseText(ed.fast, '\nfig ok = s <= t\n  fig far [size (100,50), s@(10,30), t@(130,70)] = s <= t\n');
  assert.strictEqual(d2.length, 1);
  assert.deepStrictEqual([d2[0].line, d2[0].col, d2[0].len], [2, 6, 3]);
  assert.ok(d2[0].msg.startsWith('far: The state t') && d2[0].fix && d2[0].fix.label === 'Enlarge the canvas');
  assert.deepStrictEqual(await ext.diagnoseText(ed.fast, 'fig a = s <= t\n'), []);

  ed.fast.dispose(); ed.slow.dispose();
  console.log('smoke test: ok');
})().catch((err) => { console.error(err); process.exit(1); });
