# frege-diagrams: plan for the documentation and for integration

Status 2026-11-11: PLAN. The library, the two views, the router, the editor and
`docs/GUIDE.md` exist. This note plans the documents still to be written and
the exchange with other notations. Names: the package is `frege-diagrams`, the
Lean library and namespace `FregeDiagrams`, the extension of figure files
`.fgd` (`.fig` clashes with xfig and MATLAB; `framediag --fig` accepts any
file name). Credits and references are in `ACKNOWLEDGEMENTS.md`.

## Contents

```
README.md                 what it is, one picture of both views, quick start, status, credits
LICENSE
ACKNOWLEDGEMENTS.md       people, tools, and references
CITATION.cff              how to cite the software
CHANGELOG.md
docs/LANGUAGE.md          the figure language: lexical rules, EBNF, syntax (railroad) diagrams, examples
docs/NOTATION.md          reading the pictures: view A (frame pictures) and view B (Frege notation),
                          and where this notation departs from Frege's
docs/MANUAL.md            the tools: framediag (options, outputs, checks), framedit (the editor),
                          LaTeX (\diag, \formula), Lean (fig_of%, giving figures a meaning)
docs/diagrams/            railroad diagrams (SVG), generated from the EBNF
FregeDiagrams/            the Lean library (today FregeDiagrams/), Lean core only
FregeDiagrams/Main.lean   the framediag executable
tools/framedit/           the editor (bridge and page)
examples/*.fgd            example figures (as `exampleSource`), drawn by CI
lakefile.toml, lean-toolchain
.github/workflows/ci.yml  lake build; the #guard tests; framediag --check on the examples
```

Design notes (`DESIGN.md`, `EDITOR.md`) are in `docs/design/`.

### The documents

* **docs/LANGUAGE.md.** The grammar in W3C-style EBNF (the notation of the
  XML specification: `::=`, `|`, `?`, `*`, `+`, quoted terminals), one
  production per construct with an example of each, and a railroad diagram per
  production. The diagrams are generated once from the EBNF by a small
  script (the `railroad-diagrams` Python package) and committed as SVG, so
  reading them needs no tools. The EBNF is checked against the parser by a
  test that parses one example per production.
* **docs/NOTATION.md.** For readers of the pictures rather than writers of
  figures: the legend of view A (hollow and filled states, colour as
  polarity, one line style per relation, beads, notches, labelled relations,
  panels for disjunction) and of view B (content and judgement strokes,
  condition strokes, the notch as Frege's concavity, the negation tick, forks
  for ∧ and ∨, which Frege did not have, binding links and their Morse
  patterns). Each with a figure drawn by the tool from `examples/`.
* **docs/MANUAL.md.** Sections 2 to 4 of `GUIDE.md`, rewritten for
  someone new to the project: installing, `framediag`, `framedit`, the
  checks, LaTeX macros, and how to state and prove what a figure means in
  one's own Lean development (a `denote` function into one's own frames, and
  a theorem per figure, as a template).
* **README.md.** Ten lines of description, one picture, quick start
  (`lake build`, `lake exe framediag OUT --fig examples/…`,
  `python3 tools/framedit/framedit.py examples/…`), links to the three
  documents, status, licence, citation, credits.

## Other notations: exchange and integration

The figure language is not a drawing format. It is a formula with layout
hints: its unit is a quantifier, a relation, an implication, not a line or a
point. That is what lets one text give a frame picture, a Frege tree, a LaTeX
formula and a Lean meaning, and lets the editor refuse changes of meaning.
Formats for drawings are built the other way round, so the comparison is
mostly about where each is the better tool:

| tool or format | what it is | relation to frege-diagrams |
|---|---|---|
| xfig `.fig` (with `fig2dev`) | a low-level drawing format: polylines, splines, text, in fixed units | no semantics; a possible export target only. Its extension is why `.fgd` was chosen |
| TikZ / PGF, tikz-cd | the LaTeX drawing language; tikz-cd for commutative diagrams | **the most useful integration**: exporting views A and B as TikZ would set names in the document's own fonts and drop the `rsvg-convert` step |
| quiver | a web editor for commutative diagrams that writes tikz-cd | the closest analogue to framedit: a graphical editor whose saved form is text. For plain diagrams without meaning it is simpler than ours |
| Graphviz DOT | graphs with attributes, laid out automatically | a source of automatic positions for view A (Sugiyama-style layout), imported as hints |
| Ipe | an editor with LaTeX labels, XML files | a place for final hand touch-up of an exported picture, one way |
| `begriff`, `grundgesetze` (LaTeX) | macros that typeset Frege's notation | prior art for view B; an export to their macros is possible but low value, since we already draw view B |
| GraphML, JSON graph formats | graph exchange | export of the flattened frame (states, edges, sets) for other graph tools, if ever wanted |

Recommended: keep the language small and semantic; add a **TikZ export**
for both views (most value for LaTeX documents); possibly **DOT import of
positions** for view A. As a general drawing exchange format it would be
clumsier than TikZ or SVG and should not try to be one. For figures that are
formulas it carries more than any of these, since meaning and picture are one
text.
