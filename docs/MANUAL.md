# Manual

The tools of frege-diagrams: `framediag`, which draws and checks figures;
`framedit`, the interactive editor; and the ways to use figures in LaTeX and
in Lean. The language itself is defined in [LANGUAGE.md](LANGUAGE.md), and
how to read the pictures is in [NOTATION.md](NOTATION.md).

## 1. Installing

You need Lean 4 through elan (the version is fixed by `lean-toolchain`);
`rsvg-convert` (librsvg) if you want PDF copies of the pictures; and Python 3
for the editor. The library is Lean core only: no Mathlib.

```bash
git clone https://github.com/fairflow/frege-diagrams
cd frege-diagrams
lake build
```

`lake build` builds the library, runs its tests (`FregeDiagrams/Test.lean`,
`#guard` checks) and builds `framediag`. As a dependency of another Lake
package:

```toml
[[require]]
name = "frege-diagrams"
git = "https://github.com/fairflow/frege-diagrams"
rev = "main"
```

## 2. Where figures live

Figures are text in the figure language, in one of two places:

* a **figure file**, with the extension `.fgd`;
* a **Lean file**, in a raw string: `def NAME : String := r#"…"#` (any number
  of `#`).

The second makes one text the source of everything: Lean theorems take
figures from it with `fig_of%` (section 6), `framediag --fig FILE.lean`
draws them, and the editor edits them in place. Prefer it whenever a figure
has a meaning you prove something about.

Lean's `include_str "figures.fgd"` also works with `fig_of%`, but Lake does
not rebuild a module when the included file changes, so a theorem can go on
using an old figure. Keep the text in the Lean file instead.

## 3. framediag: drawing and checking

```bash
lake exe framediag OUTDIR [--fig FILE [--def NAME]] [--no-pdf] [--links] [--hide-bound]
                          [--spacing X] [--notch-name-offset DY] [--check] [--stats]
```

OUTDIR is required, even with `--check`, which writes nothing.

| option | effect |
|---|---|
| `--fig FILE` | the figures to draw: a `.fgd` file, or a Lean file holding them in a raw string. Without it, the built-in examples (`exampleSource`). |
| `--def NAME` | with a Lean file that has several raw strings, the one to use |
| `--no-pdf` | no PDF copies. Otherwise `rsvg-convert` must be on the PATH (macOS: `brew install librsvg`). |
| `--links` | binding links in view B (section 3.2) |
| `--hide-bound` | bound names left out, in both views (the notches get smaller) |
| `--spacing X` | every clearance of the links scaled by X (default 1): row gaps, tracks, channels, room around states and names |
| `--notch-name-offset DY` | each bound name moved DY units into its notch (positive) or towards the stroke (negative), in both views. Up to 1 unit inwards the notch keeps its size; beyond that it deepens by the excess. A figure's `namedy` hint overrides it. Values between −2 and 3 are usually enough. |
| `--check` | the checks of section 3.3, instead of drawing |
| `--stats` | as `--check`, and also the numbers of crossings and nesting violations per figure |

Two further options serve the editor: `--annotate` adds element ids to the
SVG (the default output is unchanged without it), and `--serve` runs the
drawing server (section 4).

### 3.1 Output

For each figure NAME, in OUTDIR:

| file | content |
|---|---|
| `NAME.svg` | view A; or view B, for a figure with `views B` |
| `NAME_B.svg` | view B, when the figure has both views |
| `NAME.pdf`, `NAME_B.pdf` | PDF copies |
| `NAME.tex` | the formula in LaTeX (section 5) |
| `legend.svg`, `.pdf` | the key to view A (written only for the built-in examples; do not name a figure `legend`) |

Texts and captions are escaped for SVG, so they may contain `<`, `>`, `&`
and `"`.

### 3.2 Links

With `--links`, each binder (notch) is joined to every state it binds by one
tree of links, with a dot where it branches. Each binder has its own colour,
and its links are dashed in the Morse code of its name, so that binders stay
distinct in black and white.

The router computes, for each binder, an **exact minimum Steiner tree**
(Dreyfus–Wagner) in a grid built around the tree, against the strokes and the
other binders. Crossings come first in its costs; bends, length, room for
names and the nesting of scopes only break ties. Binders are routed in turn,
then ripped up and routed again. For up to four binders every choice of
turned-over notches is tried, and for each of the three cheapest every
routing order. The result is optimal for each binder given the grid, the costs
and the other binders; it is not globally optimal. The phases are described
in the header of `FregeDiagrams/Route/Router.lean`.

Two hints override the router (both written by the editor, section 4):

* `notch x up`, `notch x down` fixes the side a binder's notch opens to;
* `route x …` pins a binder's links to given polylines. A pin is made for,
  and used in, the layout with names shown, the figure's own notch-name offset
  (its `namedy`, or none) and spacing 1. With `--hide-bound`, another
  `--notch-name-offset` or another `--spacing` the layout differs, so the pin
  is set aside and the links are routed automatically; `--check` prints a
  note, not an error. When the notch or a bound state has moved since the pin
  was made, it is not used either, and `--check` reports it as an error.

### 3.3 Checks

`--check` exits with status 1, printing each problem, for:

* **hints that do nothing**: a position, arrow, loop, notch or route hint that
  names nothing in the figure;
* **a notch in the wrong place**: a notch past the first bead of a composite
  arrow when its quantifier and the arrow's intermediate state are of
  different kinds, so that the picture would read the quantifiers in the
  wrong order ([NOTATION.md](NOTATION.md));
* **a state outside the canvas**;
* **a route pin that no longer fits** its layout (names shown, the figure's
  own offset, spacing 1);
* in view B with links, routed with names shown and with names hidden: an
  **empty bigon** (a link and another curve crossing twice around a region
  holding nothing) or a **monogon** (a link crossing itself), which mean the
  route is not as short as it could be; and a **misplaced name**, more than
  `10 × spacing` from its state or cut off from it by a link.

Reported without failing: warnings (overlapping states, a name partly outside
the canvas, `side` or `at` on an arrow without a notch) and **nesting
violations** (an inner binder's links running outside an outer binder's on
some side of the tree).

### 3.4 Timings

Drawing without links takes milliseconds per figure; most of the time of a
`lake exe framediag` run is start-up (about 1.5 s). Routing grows quickly
with the number of binders: a figure with four binders takes a few seconds,
and `--check` routes each figure twice.

## 4. framedit: the editor

```bash
python3 tools/framedit/framedit.py FILE [--def NAME] [--port 8765] [--no-browser]
```

This builds `framediag`, starts two drawing servers (one for edits and the
sketch, one for the slower routing of links, so that routing never holds up
a drag), and opens `http://127.0.0.1:8765/` in a browser. It serves this
machine only. FILE is a `.fgd` file or a Lean file with a raw string
(`--def NAME` if it has several); in a Lean file only the string's contents
are edited and written back.

**Lean draws everything you see, and every change is a change to the text.**
The text is shown under the pictures, and each change appears as a diff in
the strip at the top. Hovering over or focusing a control says what it will do.

**The sketch (view A).** Click a state, a name or an arrow to select it, or
reach it with Tab. Drag it, or nudge it with the arrow keys (Shift: by 10).
On an arrow, ↑ and ↓ bend it and ← → slide its notch; a selected arrow also
has a square handle for bending. The inspector edits the same hints by
number. These edits change hints only, never the formula.

**The Frege view (view B).**

* Click a notch to select it. The inspector sets its side to *automatic*,
  *up* or *down* (the hint `notch x …`); ↑, ↓ and Delete do the same.
* With *Links* on, click a binder's links to select them. A square handle
  moves a segment sideways (its neighbours stretch); a round handle moves a
  bend or a branch point (the segments through it move with it, keeping their
  direction). The ends at the notch and the states stay; where one would have
  to move, a short jog is added. On release the links are pinned (`route x
  …`) and every notch is fixed as drawn, since the pin depends on the layout.
  *Route automatically again*, or Delete, removes the pin. Pins are made and
  used with names shown and the toolbar's notch-name offset at 0 (a figure's
  own `namedy` counts as 0 here); with other toolbar options the pinned links
  are drawn routed automatically, with a note in Problems, and moving links
  asks you to change the options first.

**The text.** The source can be edited directly. It is parsed after a pause;
an error shows its line and column with a caret (and, for a Lean file, the
line of the file), and the pictures stay as they were, marked out of date.

**Undo** (⌘Z or Ctrl+Z) and **redo** (⇧⌘Z, Ctrl+Shift+Z or Ctrl+Y) restore
whole texts, so they are exact. Consecutive nudges of one object make one
step; so does a drag. The history list jumps to any earlier state.

**Problems** lists the checks of section 3.3 that need no routing after
every change, each with *Show* and, where possible, a one-click fix; *Run
checks* adds the routed checks of the Frege view.

**Saving.** *Save* writes the file, and is refused when the text does not
parse, when the file has changed on disk since it was read, or, for a Lean
file, when the text would end the string early. When a formula has changed
(not only hints), it asks first and lists where each changed figure is used:
`fig_of%` in Lean files and `\diag`, `\formula` in TeX files of the
repository. The inspector shows the same list for the current figure.

The toolbar options (links, hidden names, notch-name offset) are the options
of `framediag`; they are not stored in the file.

## 5. LaTeX

Two macros include the output in a document (here drawn into `figures/`):

```latex
\usepackage{graphicx}
\graphicspath{{figures/}}
\pdfsuppresswarningpagegroup=1        % rsvg's PDFs carry page groups; harmless
% \diag[scale]{NAME}: a picture; a placeholder box if it has not been drawn
\newcommand{\diag}[2][1.0]{\begin{center}\IfFileExists{figures/#2.pdf}%
  {\includegraphics[scale=#1]{#2}}%
  {\fbox{\small diagram \texttt{\detokenize{#2}} not drawn}}\end{center}}
% \formula{NAME}: the figure's formula (use in math mode)
\newcommand{\formula}[1]{\IfFileExists{figures/#1.tex}%
  {\input{figures/#1.tex}}{\text{\fbox{formula \texttt{\detokenize{#1}}}}}}
```

```latex
\[ \formula{ex_trans} \]
\diag{ex_trans}          % view A
\diag[1.05]{ex_trans_B}  % view B
```

The formulas use these macros (`\leadsto` needs `amssymb`):

```latex
\newcommand{\imp}{\rightarrow}
\newcommand{\sq}{\sqsubseteq}
\newcommand{\SqR}{\mathrel{{\sqsubseteq};R}}
\newcommand{\Y}{\mathrel{{\sqsubseteq};R;{\sqsubseteq}}}
\newcommand{\reach}{\leadsto}
\newcommand{\nF}{\notin F}
```

Greek names come out as their macros (`σ₁` as `{\sigma}_1`). A figure's
printed size is its canvas size times the scale of `\diag`: one unit of the
canvas is 0.75 pt. A build script runs `framediag` before LaTeX, passing the
options through (for instance `--links --spacing 1.4`).

## 6. Lean: figures with a meaning

`fig_of% SRC "NAME"` is the figure NAME of the source `SRC : String` as a Lean
term of type `Fig`, parsed when the file is elaborated; a parse error or a
missing figure is an elaboration error, so a theorem always refers to the
very text that is drawn.

```lean
import FregeDiagrams.Elab
open FregeDiagrams

def myFigs : String := r#"
fig serial = all t. if s <= t then ex u. t R u°
"#

def serial : Fig := fig_of% myFigs "serial"
```

The library gives figures no meaning, since that depends on the frames of
your logic. A client defines a function `Form.denote` from formulas
(`FregeDiagrams/Fig.lean`: chains of relations, `all`, `ex`, `not`, `if`,
`&`, `|`, text leaves with their meaning) into propositions about its own
frames, reading each relation symbol as its relation and each name through an
assignment of states, and then proves for each figure that it means exactly
the condition it illustrates:

```lean
-- outline; Fr, Form.denote and condSerial are the client's
theorem fig_serial :
    (∀ s, ¬ Fr.F s → serial.body.denote Fr (fun _ => s)) ↔ Fr.condSerial := by
  simp [serial, Form.denote, …]
```

The free state (here `s`) is the implicit outer "for every infallible s",
hence the `∀ s, ¬ Fr.F s →`. Hints never enter `denote`, so layout edits
cannot break such a theorem; formula edits can, and the editor says which
uses to check. Legend and bracketing figures (`legend_*` in the examples)
have no meaning.

## 7. Status

* **Tested, not proved:** the round trip `parse (print d) = d` for every
  well-formed figure, checked on the examples and on 2000 pseudo-random
  figures (`lake build FregeDiagrams.Test`).
* **Tested, not proved:** no empty bigons or monogons and no misplaced names
  in the routed links of the examples (`--check`).
* **Tested:** every hint edit of the editor re-parses to exactly the edited
  figure (the editor refuses any edit for which it does not).
* **Not built** (proposals in [design/DESIGN.md](design/DESIGN.md) and
  [design/EDITOR.md](design/EDITOR.md)): automatic layout of view A, reflow
  of view B, a relation signature declared in Lean, figures made from Lean
  definitions, a proof of the round trip.

## 8. The library

| module | what it is |
|---|---|
| `Syntax` | lexer, parser (with source spans), printer, Lean raw strings |
| `Fig` | the syntax tree: `Form`, hints, `Fig` |
| `View`, `Frame` | view A: flattening a formula into a frame picture, and its shapes |
| `Tree` | view B: the formula tree, `DrawOpts`, Morse patterns |
| `Route/` | the link router: geometry, Steiner trees, routing, pins and checks |
| `Latex` | the LaTeX output |
| `Lint` | the checks of hints and of view A |
| `Edit` | hint edits written back into the text |
| `Serve` | the drawing server of the editor |
| `Elab` | `fig_of%` |
| `Examples`, `Legend` | the built-in example figures and the key to view A |
| `Main` | `framediag` |
| `Test` | the `#guard` tests |
