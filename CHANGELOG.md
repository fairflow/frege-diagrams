# Changelog

## Unreleased

* Claims and their theorems: `@[figure_claim "NAME"]` tags the theorem that states a figure; `#figure_claims SRC` fails when a claimed figure of SRC has no tagged theorem (definitions, contents and schematic figures, those with a text leaf without a meaning, are not checked) and otherwise lists each figure with its theorems (`FregeDiagrams.Claims`). `evalString` (of `FregeDiagrams.Elab`) is now public.

* Route pins and view options: a pin is made for, and used in, the layout with names shown, the figure's own notch-name offset and spacing 1. With `--hide-bound`, another `--notch-name-offset` or `--spacing` (or the editor's toolbar options) it is set aside and the links are routed automatically, with a note instead of an error; framedit asks for those options before it pins links. A pin that no longer fits its own layout is still an error.
* Judgement strokes: the hint `judgement claim|definition|content` gives view B one judgement stroke (a claim, the default), Frege's double stroke (a definition `"D" {f}`: both views draw `f`, view B writes `D :≡`, LaTeX `\text{D}\ :\equiv\ f`) or none (a content, nothing claimed). Lint reports a definition of another shape; framedit sets it in the figure inspector. Existing figures draw byte-identically.
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
