# Changelog

## Unreleased

* docs/LANGUAGE.md: the figure language, with its grammar in EBNF and syntax diagrams generated from one source (docs/tools/grammar.py); CI checks the EBNF and that the examples parse.
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
