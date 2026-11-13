// Runs inside VS Code (see run.js).  Plain assertions, no test framework.
const vscode = require('vscode');
const path = require('path');
const assert = require('assert');

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

/** Wait until `pred()` holds, or fail with `what` after `ms`. */
async function until(pred, what, ms = 90000) {
  for (const t0 = Date.now(); Date.now() - t0 < ms; await sleep(250)) if (await pred()) return;
  throw new Error(`timed out: ${what}`);
}

exports.run = async () => {
  const proj = /** @type {string} */ (process.env.FD_PROJECT);
  const me = vscode.extensions.getExtension('fairflow.frege-diagrams');
  assert.ok(me, 'the extension is loaded');
  // no Lean extension here, so onLanguage:lean4 never fires; activate directly
  const { status } = await me.activate();
  const log = (s) => console.log(`[vscode test] ${s}`);
  const report = () => JSON.stringify(status, null, 1);

  // 1. A Lean file of another Lake project: the lens, then the figure editor
  const lean = await vscode.workspace.openTextDocument(path.join(proj, 'Diagrams', 'Figs.lean'));
  await vscode.window.showTextDocument(lean);
  assert.ok(!vscode.workspace.getWorkspaceFolder(lean.uri), 'the Lean file is outside the open folder');
  /** @type {vscode.CodeLens[]} */
  let lenses = [];
  await until(async () => {
    lenses = (await vscode.commands.executeCommand('vscode.executeCodeLensProvider', lean.uri)) || [];
    return lenses.some((l) => l.command && l.command.title === 'Edit figures');
  }, 'an Edit figures lens on the Lean file');
  const lens = lenses.find((l) => l.command && l.command.title === 'Edit figures');
  assert.strictEqual(lens.range.start.line, 1, 'the lens sits on the def line');
  log('lens found');
  await vscode.commands.executeCommand(lens.command.command, ...(lens.command.arguments || []));
  await until(() => status.panels.some((p) => p.file === lean.uri.fsPath && (p.drawn > 0 || p.failed)),
    'the figure editor on the Lean file draws (or fails)');
  const p1 = status.panels.find((p) => p.file === lean.uri.fsPath);
  assert.strictEqual(p1.failed, null, `the panel failed: ${report()}`);
  assert.strictEqual(p1.exe, path.join(proj, '.lake', 'packages', 'frege-diagrams', '.lake', 'build', 'bin', 'framediag'),
    "framediag comes from the file's Lake project");
  assert.ok(vscode.window.tabGroups.all.some((g) => g.tabs.some((t) => t.label === 'Figures: figs')), 'a tab "Figures: figs" is open');
  log(`Lean file: ${p1.drawn} drawing(s)`);

  // 2. A figure file opened in the figure editor
  const fgd = vscode.Uri.file(path.join(proj, 'Diagrams', 'figs.fgd'));
  await vscode.commands.executeCommand('vscode.openWith', fgd, 'fregeDiagrams.figureEditor');
  await until(() => status.panels.some((p) => p.file === fgd.fsPath && (p.drawn > 0 || p.failed)),
    'the figure editor on the .fgd file draws (or fails)');
  const p2 = status.panels.find((p) => p.file === fgd.fsPath);
  assert.strictEqual(p2.failed, null, `the panel failed: ${report()}`);
  log(`figure file: ${p2.drawn} drawing(s)`);

  assert.deepStrictEqual(status.errors, [], `errors were shown: ${report()}`);
  log('ok');
};
