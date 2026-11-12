# Frege Diagrams for VS Code

Edit the figures of [frege-diagrams](https://github.com/fairflow/frege-diagrams)
inside VS Code: Frege-style formula trees and Kripke frame pictures, drawn by
Lean from the figure language.

Opening a figure file (`*.fgd`) shows the figure editor: the sketch, the
Frege view, the inspector and the text, as in the browser editor
(`tools/framedit/`). Saving goes through VS Code; *Reopen Editor With… → Text
Editor* shows the plain text.

The drawing is done by `framediag`, built by Lake in your workspace: the
workspace's `lakefile` requires frege-diagrams, and the extension runs
`lake build framediag` the first time if needed. The settings
`fregeDiagrams.framediagPath` and `fregeDiagrams.lakePath` override where the
programs are.

Planned (docs/design/VSCODE.md): editing the figure strings of Lean files
(*Edit figures*), colouring and diagnostics for the figure language, pictures
on hover.

## Building and installing

```bash
cd tools/vscode
npm run package          # writes frege-diagrams.vsix
code --install-extension frege-diagrams.vsix
```

`npm test` runs a smoke test of the message handling against a real
`framediag` (built with `lake build framediag` at the repository root).
