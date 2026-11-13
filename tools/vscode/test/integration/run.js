// Integration test in a real VS Code (contract H1 and H5 of
// docs/design/NEXT-STAGE.md): downloads a VS Code, starts it with this
// extension and no other, and runs suite.js inside it.  The window's folder is
// a plain folder; the Lean file and the figure file live in ANOTHER Lake
// project, whose frege-diagrams package is this repository (a symbolic link),
// so framediag must be found from the file, not from the window's folder.
//   Needs: lake build framediag at the repository root; npm install in
//   tools/vscode; on Linux without a display, run under xvfb-run.
//   Run: npm run test:vscode   (in tools/vscode)
const path = require('path');
const fs = require('fs');
const os = require('os');
const { runTests } = require('@vscode/test-electron');

const ext = path.join(__dirname, '..', '..');
const repo = path.join(ext, '..', '..');

function fixture() {
  const top = fs.mkdtempSync(path.join(os.tmpdir(), 'fd-vscode-'));
  const folder = path.join(top, 'open-folder');          // what the window opens
  const proj = path.join(top, 'figures-project');        // where the files are
  fs.mkdirSync(folder);
  fs.writeFileSync(path.join(folder, 'README.md'), 'A folder that is not a Lake project.\n');
  fs.mkdirSync(path.join(proj, 'Diagrams'), { recursive: true });
  fs.mkdirSync(path.join(proj, '.lake', 'packages'), { recursive: true });
  fs.symlinkSync(repo, path.join(proj, '.lake', 'packages', 'frege-diagrams'), 'dir');
  fs.writeFileSync(path.join(proj, 'lakefile.toml'), 'name = "figures-project"\n');
  fs.writeFileSync(path.join(proj, 'Diagrams', 'Figs.lean'),
    '/-- Figures. -/\ndef figs : String := r#"\nfig one = all t. s <= t\n"#\n');
  fs.writeFileSync(path.join(proj, 'Diagrams', 'figs.fgd'), 'fig two = all t. if s <= t then t R t\n');
  return { folder, proj };
}

(async () => {
  require(path.join(ext, 'scripts', 'prepare.js'));
  const exe = path.join(repo, '.lake', 'build', 'bin', 'framediag');
  if (!fs.existsSync(exe)) { console.error(`no ${exe}: run lake build framediag at the repository root`); process.exit(1); }
  const { folder, proj } = fixture();
  try {
    await runTests({
      version: process.env.FD_VSCODE_VERSION || '1.85.2',   // the oldest version package.json allows
      extensionDevelopmentPath: ext,
      extensionTestsPath: path.join(__dirname, 'suite.js'),
      extensionTestsEnv: { FD_PROJECT: proj },
      launchArgs: [folder, '--disable-extensions', '--disable-workspace-trust', '--skip-welcome', '--skip-release-notes'],
    });
  } catch (e) {
    console.error('integration test failed:', e);
    process.exit(1);
  }
})();
