# Changelog

One section per version, newest first: the version, the commit of main it
was merged as, the date and time (UTC) of that commit, and the tag if one
is applied. `framediag --version` prints the version; the editor shows it
with the commit it runs from.

## 0.15.0 (unreleased)

* The reference for view B (`FregeDiagrams/SpecB.lean`, docs/design/NEXT-STAGE.md §3.3.1): a reader that rebuilds the formula from the picture's geometry alone, and `Fig.checkB`, which checks that it gets the figure's formula (B5) and, with links, the figure's binding with names shown and hidden (B3, B3′). `lake exe speccheck` runs both views' references on the examples and on 2000 generated figures, in CI. The renderer of view B returns its scene, the shapes the SVG is written from; the SVG is unchanged.
* Fixed, found by the reader: in view B a loop with a composite relation (`s R;<= s`) was drawn solid, as `R`; it now draws every stretch. A state with a loop took its fill from its first occurrence only (`s R s°` lost the `°`); it is hollow if any occurrence is `°`. In both views an arrow ending in `⊑` or `R°` now ends in a hollow state, so that `s ⊑ t` no longer draws like `s ≤ t`. No picture of the documentation changes.
* Known, not yet changed: two loops on one state are drawn on top of each other; a large negative `namedy` moves a bound name out of its notch; a directed labelled stretch inside a composite draws like an undirected one.

## 0.14.0 (unreleased)

* View A shows every quantifier: one whose state no arrow enters (`all t. t R s`) is drawn on the state itself, a notch on a short stroke under it, instead of not at all. A shadowed or vacuous quantifier binds nothing and gets no mark. The reference's property A3 says so, and holds on the 2000 generated figures.
* The language is named FGD (LANGUAGE.md, README); files use `.fgd` in lower case. NOTATION.md and the design say that view B is the canonical picture and view A deliberately incomplete.

## 0.13.0 · 3ef98d5 · 2026-11-13 10:50 UTC

* The reference for view A (`FregeDiagrams/Spec.lean`, docs/design/NEXT-STAGE.md §3.3): what view A must show (arrows and loops with their composites, states per panel, one notch per quantifier, colours) stated by a plain recursion over the formula, independently of the drawing code, and `Fig.checkA` / `Fig.checkCanvasA`, which compare a drawing with it. Tested on the examples and on 2000 generated figures.
* Fixed, found by the checker: a self-loop with a composite relation (`s R;<= s`) drew only its first stretch; it now draws every stretch, with beads and labels, as an arrow does. A state bound by `ex` is red (or crossed) in every panel of the binder's scope, not only its own. A state with two position hints was drawn twice; the last hint counts, and the lint warns.
* Known, not yet changed: a quantifier whose state no arrow enters (`all t. t R s`) has no notch in view A (property A3, a decision pending).

## 0.12.0 · 04f199b · 2026-11-13 08:59 UTC

* The drawing server's protocol has a JSON schema, `docs/protocol/serve.schema.json`: every op's request and reply, every edit kind, and errors. CI starts `framediag --serve`, sends a corpus covering all of them, and checks each request and reply against the schema (`tools/protocol/test_protocol.py`). The server's summary in `Serve.lean` gains the `undash` edit and the unit of an edge's `at` (hundredths).
* VS Code: an integration test in a real VS Code, run in CI (`npm run test:vscode`): a Lean file and a figure file of another Lake project than the open folder are opened in the figure editor, and the test waits until each page has received a drawing from `framediag` with no error shown. For it, the extension records every error it shows and, per panel, its file, its `framediag` and the drawings that reached the page (`activate` returns them).

## 0.11.1 · 15a5007 · 2026-11-13 08:34 UTC

* VS Code: a Lean file opened in a window whose folder is another project now finds its own project's `framediag`, the nearest folder above the file with a lakefile, instead of failing to build in the file's own folder ("could not build framediag in …/Diagrams").
* Docs: after installing the VS Code extension, reload every open window (VS Code does not start a new extension in windows already open).

## 0.11.0 · 0d82ee4 · 2026-11-12 22:53 UTC · tag `v0.11.0`

* Dash patterns in the figure language. `dash x "PATTERN"` or `dash x morse "WORD"` dashes the links of binder `x` (view B); `dash REL …` the lines of a relation in both views; and a file statement `default dash REL "PATTERN"` sets a relation's style for every figure of the file (a figure's own hint wins). A pattern reads like typed text, one 4-unit cell per character: `-` ink (neighbours join), `.` a dot, space blank; it repeats, and with no blank it is solid. The strokes of view B's tree are never affected. A `dash x` naming no binder is reported, with *Remove the hint* as its fix. LANGUAGE, NOTATION, the syntax diagrams and the VS Code colouring follow.

## 0.10.0 · 1ff2650 · 2026-11-12 22:53 UTC · tag `v0.10.0`

* A softer default style: thinner lines (the assertion stroke 1.6 instead of 2.0, strokes and links 1.0 to 1.15 instead of 1.3 to 1.9), round joins, and every bend of a stroke or link rounded (radius 3.5, at most half of either segment). Layout is unchanged. `--style classic` (and `style: "classic"` for `--serve`) draws as before, byte for byte. The editor keeps square bends. The pictures of the documentation are redrawn.

## 0.9.0 · d97ce0a · 2026-11-12 22:16 UTC · tag `v0.9.0`

* VS Code: the figure language is coloured, in `.fgd` files and inside the figure strings of Lean files (TextMate grammars generated from the grammar source, `docs/tools/grammar.py --textmate`, checked in CI); parse errors and the checks of every figure are squiggles, at the parser's position or the figure's name, with each check's fix as a quick fix.

## 0.8.0 · 6715cac · 2026-11-12 21:52 UTC · tag `v0.8.0`

* VS Code: *Edit figures* above each figure string of a Lean file opens the figure editor on that string beside the Lean file (and from the command palette); saving writes the string back into the Lean document and saves it; edits elsewhere in the Lean file do not disturb the editor; the String menu switches between the strings of the file. A text that would end the string early is refused.
* framedit: the String menu is hidden for a figure file (the toolbar style overrode `hidden`); the help strip names a menu or field by its label, not by its options.

## 0.7.0 · 8acb4e1 · 2026-11-12 21:49 UTC · tag `v0.7.0`

* A VS Code extension, first version (`tools/vscode/`, docs/design/VSCODE.md steps 1 and 2): figure files (`*.fgd`) open in the figure editor inside VS Code, the browser editor's page in a webview talking to the same `framediag --serve`; saving goes through VS Code; a change made in a text editor or on disk reaches the page. framediag is the workspace's (built with Lake when missing), and the page comes from the same package. Plain JavaScript type-checked with `// @ts-check`; a smoke test against a real framediag; `npm run package` writes the `.vsix`.
* framedit: the page sends every request through one function, `api`, which in VS Code posts a message instead of fetching.

## 0.6.0 · 8e26eba · 2026-11-12 10:02 UTC · tag `v0.6.0`

* The canvas grows instead of reporting an error: a state dragged or nudged past the right or bottom edge enlarges the `size` hint (with a margin); it cannot leave by the left or top. A corner handle resizes the canvas, and with Shift stretches the figure (the new edit `resize {w, h, from}`: hinted states and captions move in proportion). A state outside the canvas in typed text is still reported, now with the fix *Enlarge the canvas*.

## 0.5.0 · b8f7de4 · 2026-11-12 10:02 UTC · tag `v0.5.0`

* framedit: a Lean file may hold several figure strings; the toolbar's *String* menu switches between them (refused while there are unsaved changes), `--def NAME` picks the first one shown. *New figure* in the figure inspector appends a figure. Tests of the file handling (zero, one or several strings, nested delimiters, unclosed strings, repeated names, the round trip), run in CI.
* MANUAL: the figure module, a Lean file holding only the figure strings, imported where theorems use them.

## 0.4.0 · 695efc6 · 2026-11-12 09:42 UTC · tag `v0.4.0`

* Notches can be grabbed in both views. Sketch: drag a notch along its arrow (`at`) or across it (`side`). Frege view: drag a notch sideways, or ←/→, to move it along its stroke (the `stroke` hint of its block). In both, drag the name in a notch to move it: the new hint `namedy x N`, one binder's name offset, both views (`namedy N` remains the figure's). The direction of a drag that starts on the name decides: along the stroke moves the notch, across it the name.
* framedit: the strapline under the title is gone (the version line stays); no browser focus ring on the selected element (the selection marker shows it); a drag in the sketch keeps the coordinates it started in, so the redraws during a drag cannot make it run away.

## 0.3.0 · a39f575 · 2026-11-12 08:24 UTC · tag `v0.3.0`

* Versions: `framediag --version`; the editor's header shows the version, the commit (short hash, "modified" if the working tree has changes), the tag if any, and the commit's date and time. This changelog has one section per version.
* View B layout hints: `stroke PATH DX` lengthens or shortens the stroke into a block (moving the block, and a quantifier's notch, along the stroke) and `gap PATH DY` gives a hypothesis or fork part more or less room above. Block paths are written `b/1/0`. Lint reports hints naming no block. framedit: with a block selected, a square handle and ←/→ set its stroke, a diamond and ↑/↓ its gap; links are hidden during a drag and routed again after it, with no mode.
* Blocks: every subtree of the formula has a path (`b`, `b/0`, `b/1/2`, …, `blockPath`, `Form.blockAt`). With `annotate`, view B carries each block's extent and hit targets at its start, a fork's dot and a condition stroke's junctions, and view A's arrows and states carry their blocks. framedit selects a block by a click there, shades it in the Frege view, marks its arrows and states in the sketch and shows its formula (`--serve` op `block`); Alt+↑ and Alt+↓ widen and narrow; a selected notch shows its scope.
* Claims and their theorems: `@[figure_claim "NAME"]` tags the theorem that states a figure; `#figure_claims SRC` fails when a claimed figure of SRC has no tagged theorem (definitions, contents and schematic figures, those with a text leaf without a meaning, are not checked) and otherwise lists each figure with its theorems (`FregeDiagrams.Claims`). `evalString` (of `FregeDiagrams.Elab`) is now public.
* docs/MANUAL.md, section 2: claims, definitions and contents, with the syntax.

## 0.2.0 · d491de4 · 2026-11-12 00:20 UTC · tag `v0.2.0`

* docs/design/PROPOSAL.md: judgement strokes, blocks, editing view B, sound transformations, sheets.
* Route pins and view options: a pin is made for, and used in, the layout with names shown, the figure's own notch-name offset and spacing 1. With `--hide-bound`, another `--notch-name-offset` or `--spacing` (or the editor's toolbar options) it is set aside and the links are routed automatically, with a note instead of an error; framedit asks for those options before it pins links. A pin that no longer fits its own layout is still an error.
* Judgement strokes: the hint `judgement claim|definition|content` gives view B one judgement stroke (a claim, the default), Frege's double stroke (a definition `"D" {f}`: both views draw `f`, view B writes `D :≡`, LaTeX `\text{D}\ :\equiv\ f`) or none (a content, nothing claimed). Lint reports a definition of another shape; framedit sets it in the figure inspector. Existing figures draw byte-identically.

## 0.1.0 · f6eb77a · 2026-11-11 23:05 UTC · tag `v0.1.0`

* docs/LANGUAGE.md: the figure language, with its grammar in EBNF and syntax diagrams generated from one source (docs/tools/grammar.py); CI checks the EBNF and that the examples parse.
* docs/MANUAL.md: the tools (installing, `framediag`, `framedit`, LaTeX, figures with a meaning in Lean); replaces docs/GUIDE.md, whose language part is in docs/LANGUAGE.md.
* `framediag --fig FILE.lean [--def NAME]` reads the figures from a raw string in a Lean file, so one string serves theorems (`fig_of%`), drawings and the editor; parse errors give the line of the file.
* View B with links: the hint `route x …` pins a binder's links to given polylines; the router routes the others around them; a pin that no longer fits its layout is reported (`--check`, framedit) and replaced by automatic routing. framedit edits links directly: segment handles, bend and branch-point handles, orthogonality kept, ends fixed with automatic jogs.
* View B: the hint `notch x up|down` fixes the side a binder's notch opens to; the link router routes around it instead of turning it over. In framedit, notches in the Frege view can be selected and set to automatic, up or down.
* docs/NOTATION.md: how to read view A and view B, and where the notation departs from Frege's; its pictures are drawn from docs/notation.fgd and the examples by docs/tools/images.sh, checked in CI.
* The key to view A (`legend.svg`): wider, so the captions no longer run into the right-hand column; a row for labelled relations.
* Names may contain Greek letters (`Α`–`Ω`, `α`–`ω`), also as first letter; set in LaTeX as their macros, linked in Greek Morse code.
* CONTRIBUTING.md: documentation is updated in the same pull request as any visible or design change.

What exists in 0.1.0-dev:

* the figure language: syntax, lexer, parser and printer, with line and column in errors;
* view A (frame pictures) and view B (Frege-style formula trees), drawn as SVG;
* the formula in LaTeX (`NAME.tex`);
* the link router (exact Steiner trees, Morse-code dash patterns) and the layout checks (`framediag --check`);
* `fig_of%`, figures as Lean terms, for giving them a meaning in a client library;
* the editor `framedit` (`framediag --serve` and a browser page), which edits hints in place and writes the text back;
* lint of hints and of the reading of view A;
* build-time tests (`FregeDiagrams.Test`) and example figures (`examples/basic.fgd`).

### Provenance

Developed 2025–2026 inside Matthew Fairtlough's Lean projects and extracted into this repository with a fresh history on 2026-11-11. The library was first generalised in 2026-11-09 (neutral example figures in place of a project's own, `framediag --fig FILE` as the normal input, labelled relations, the notch-name offset) and gained the editor's foundations (line and column in parse errors, source spans, hint edits, lint) on 2026-11-11.
