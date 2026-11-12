# A VS Code extension: design note

Status 2026-11-12: approved by Matthew (every detail, including the three
decisions below: here, a local `.vsix`, the workspace's `framediag`). Steps 1
and 2 are built (0.7.0), step 3 too (0.8.0). One change from the plan: the extension is plain
JavaScript type-checked with `// @ts-check` against the VS Code API
declarations, not TypeScript, so that it has no build step. The browser
editor (`tools/framedit/`) stays: it needs nothing but Python and a browser,
and works one file at a time. The extension is for working inside VS Code
beside the Lean extension, with VS Code's own file management, undo and
saving.

## What the user gets

1. **A figure editor for `.fgd` files.** Opening a `.fgd` file offers the
   figure editor (the page of `framedit`) as an editor of its own, with the
   text editor one click away ("Reopen with…"). Saving, undo and redo,
   "modified" marks, file history, search and source control are VS Code's.
2. **Figures in Lean files.** Above each `def NAME : String := r#"` a code
   lens *Edit figures* opens the figure editor on that string, beside the
   Lean file. Every change is an edit of the Lean document, so the Lean
   extension re-elaborates as you go and the theorems that use the figures
   (`fig_of%`) report at once whether they still hold.
3. **Language support for the figure language.** In `.fgd` files and inside
   the raw strings of Lean files: syntax colouring, and parse errors and the
   checks of `framediag --check` (hints that name nothing, a notch in the
   wrong place, a state outside the canvas, …) as squiggles in the Problems
   panel, with their one-click fixes as quick fixes.
4. **Pictures on hover** (later): hovering over `fig_of% SRC "NAME"` in Lean
   shows the figure.

## How it is built

Most of it exists:

| piece | now | in the extension |
|---|---|---|
| drawing, edits, checks | `framediag --serve`, JSON lines, stateless | the same process, started by the extension (the Lake package of the workspace builds it) |
| the page | `tools/framedit/index.html` | the same page in a webview; its five requests (`/api/lean`, `/api/file`, `/api/save`, `/api/uses`, `/api/select`) go through one function, which in the webview posts a message instead of fetching |
| the file | read and written by `framedit.py` | a `TextDocument`: the page's edits become `WorkspaceEdit`s of the string's range; VS Code saves |
| uses of a figure | a walk over the repository | `workspace.findFiles`, then a search of each Lean and TeX file |
| grammar | `docs/tools/grammar.py`, the single source | also writes a TextMate grammar for colouring |

New code, in TypeScript:

* a `CustomTextEditorProvider` for `.fgd` (the editor of item 1);
* a `CodeLensProvider` for Lean files that finds the raw strings, with the
  same rules as `framedit.py` and `FregeDiagrams.leanRawStrings` (each string
  ends at its own closing delimiter), and a command that opens the editor on
  one string, kept in step as the document changes;
* a diagnostics provider calling the server's `parse` and `lint` when a
  document changes (debounced), mapping lines and columns, and offset by the
  string's position in a Lean file;
* the message bridge between webview and server.

Estimate: 800 to 1200 lines of TypeScript, the page changed only at its five
requests, and the grammar generator extended. No language server is needed
for this: diagnostics and quick fixes come straight from the drawing server.
A language server (completion of names and hint words, go to the uses of a
figure) can come later if wanted.

## Decisions for Matthew

1. **Where it lives**: in this repository (`tools/vscode/`), versioned with
   the tools, or in a repository of its own. Proposed: here, so that the
   page and the server it talks to never drift apart.
2. **Distribution**: a `.vsix` file built locally and installed with
   *Install from VSIX*; publishing on the Marketplace (a publisher account)
   is a later, separate decision.
3. **Which `framediag`**: the one the workspace's Lake build makes (a client
   repository requires frege-diagrams, as now), else a path in the settings.

## Order of work

1. The page's requests through one function (a small change to the browser
   editor, testable alone).
2. The extension skeleton: the `.fgd` custom editor with the page in a
   webview, saving through VS Code.
3. *Edit figures* in Lean files.
4. Colouring and diagnostics.
5. Hover pictures.

Each step is a pull request with a version, as for the other tools.
