# Frame-condition diagrams: a guide

A small language for drawing frame conditions of intuitionistic modal logics:
Kripke frames with a preorder ≤, an accessibility relation R and a set F of
fallible states (a state not in F is *infallible*). One text describes a
**figure**, which is a formula. From that text, `lake exe framediag` makes:

* **view A**, a frame picture: states and arrows;
* **view B**, a formula tree in the style of Frege's *Begriffsschrift*;
* the formula typeset in LaTeX (`NAME.tex`).

The library itself gives figures no meaning. A client library can define a
`denote` into its own frames and prove, per figure, that the figure means
exactly the Lean condition it illustrates; with `fig_of%` (section 4) the
picture, the displayed formula and the theorem all come from the same text.
Lean core only, no Mathlib.

| file | what it is |
|---|---|
| `FregeDiagrams/Syntax.lean` | the grammar (in its header), lexer, parser, printer |
| `FregeDiagrams/Fig.lean` | the AST: `Form`, hints, `Fig` |
| `FregeDiagrams/Examples.lean` | `exampleSource`: example figures as text (legends of view B, bracketing, a few frame conditions) |
| `FregeDiagrams/Legend.lean` | `legend`, the key to view A, drawn directly |
| `FregeDiagrams/View.lean`, `Frame.lean` | view A (flattening a formula into a frame picture) and its shapes |
| `FregeDiagrams/Tree.lean` | view B (the formula tree), `DrawOpts`, Morse dash patterns |
| `FregeDiagrams/Route/` | the link router: `Geom.lean` (geometry), `Steiner.lean` (Steiner trees), `Router.lean` (phases, checks, SVG of view B) |
| `FregeDiagrams/Latex.lean` | the LaTeX output |
| `FregeDiagrams/Elab.lean` | `fig_of% SRC "NAME"`: a figure of the source `SRC : String` as a Lean term |
| `FregeDiagrams/Main.lean` | the `framediag` executable |
| `FregeDiagrams/Test.lean` | `#guard` tests: round trip, LaTeX, Steiner, layout checks |
| `docs/design/DESIGN.md` | design notes; what is built and what is only proposed |

## 1. Writing a figure

The full definition of the language, with its grammar, is
[LANGUAGE.md](LANGUAGE.md); this section is a summary.

```
fig NAME [hints] = formula
```

### Formulas

| you write | it means | view B draws |
|---|---|---|
| `s <= t` | s ≤ t | a dashed arrow |
| `s <=° t` | s ⊑ t (≤ into an infallible state) | a dashed arrow; inside a composite, a hollow bead after the stretch |
| `s R t`, `s R° t` | s R t, and R into an infallible state | a solid arrow (bead inside a composite for `R°`) |
| `s ~> t` | s ⇝ t, i.e. (≤ ∪ R)* | a wavy arrow |
| `s = t`, `s != t` | equality, inequality | a double line, struck through for ≠ |
| `s -[L]- t`, `s -[L]-> t` | a labelled relation L between s and t, undirected or directed (agreement `u -[≡ᵣ₊₁]- u′`, a bisimulation link `k -[Z₂ₙ₊₁]-> m`, …); the label is free text | a dotted line with the label at its middle, an arrowhead only for `->`; usable in chains and composites like `<=` |
| `s <=°;R;<= y` | a composite relation, here s (⊑;R;≤) y | one arrow whose stretches change style |
| `t°` | t is infallible (a state on its own, or written on any occurrence) | a hollow dot |
| `s <= u° R t` | a chain: s ≤ u ∧ u R t | a chain of arrows |
| `all x. φ` | ∀x φ | a ⊓ notch in the stroke |
| `ex x. φ` | ∃x φ | a ∨ notch in the stroke |
| `not φ` | ¬φ | a tick below the stroke |
| `if φ₁, φ₂ then ψ` | φ₁ → (φ₂ → ψ) | ψ along the stroke; each φᵢ on its own condition stroke, staggered (φ₁ leftmost, lowest) |
| `if (φ₁ & φ₂) then ψ` | (φ₁ ∧ φ₂) → ψ | one hypothesis, a ∧-fork |
| `if (if φ then χ) then ψ` | (φ → χ) → ψ | the hypothesis is a whole tree |
| `(φ & ψ & …)` | conjunction | a fork with a filled dot |
| `(φ \| ψ \| …)` | disjunction (primitive, not encoded through ¬ and →) | a fork with a hollow dot and an arc |
| `"text" {φ}` | a leaf drawn as the text, meaning φ (without `{φ}`: meaning True) | the text |

Rules:

* `--` starts a comment (a labelled relation `-[` is not one). Names may use primes, subscript digits and Greek letters: `s′`, `t₁`, `σ` (the exact rule is in [LANGUAGE.md](LANGUAGE.md)).
* Binders carry no `°` (`all y.`); `°` belongs to occurrences.
* **Labelled relations** are for relations a frame does not have. Unicode
  subscripts in a label (`ᵣ₊₁`, `₂ₙ₊₁`) are set as real SVG subscripts, so
  they do not depend on the font. The library gives a labelled relation no
  meaning: a client that interprets figures reads it by its own definitions.
* **Membership of a set** is not a node marker: nodes keep their hollow or
  filled meaning. Where membership follows from a relation the frame has, the
  arrow into the state already shows it. (Coloured fills with a per-figure key
  are a possible later addition for other sets; not implemented.)
* **Colour is polarity**, in both views: red positive, black negative. A
  conclusion keeps the polarity of its condition; a hypothesis, and the body
  of a `not`, reverse it. The figure itself is positive.
* **The free state.** A name that no `all`/`ex` binds is the implicit outer
  "for every infallible s". It has no notch, is drawn hollow in both views,
  and gets no links.
* **View A** flattens the formula: every chain step is an arrow (a step back
  to the same state is a self-loop), equal names are one state, each
  quantifier is a notch on the first arrow into the state it binds (`all`: a
  square ⊓; `ex`: a pointed ∨ and a red state; an `ex` under an odd number of
  `not`s: a crossed, unlabelled state with a square notch). Each disjunct is a
  panel of its own. Text leaves and `!=` steps are not drawn in view A.
* **Notches.** ⊓ is ∀ and ∨ is ∃, each with the bound name inside. With
  `--hide-bound` the name is dropped and the notch is smaller. With `--links`
  the router may flip a notch in view B (⊔ for ∀, ∧ for ∃).

Examples (from `exampleSource`): transitivity along two given steps, and a
composite relation with a self-loop:

```
fig ex_trans [size (300,150),
    s@(30,115), u@(150,40), t@(270,115) label (12,4),
    edge s>u side -, edge u>t side -, edge s>t bend 10] =
  all u. all t. if s <= u, u <= t then s <= t

fig ex_composite [size (300,140),
    s@(30,100), y@(250,100) label (12,4),
    edge s>y bend -40 at 0.17, edge s>y#2 bend 12, loop y -90] =
  all y. if s <=°;R;<= y° then (y R y & s ~> y)
```

Without hints a figure is one line: `fig serial = all t. if s <= t then ex u. t R u°`.

The grammar, with syntax diagrams, is in [LANGUAGE.md](LANGUAGE.md).

### Hints (view A layout, and `namedy`; optional)

View A is laid out by hand: a state without a position goes on a plain grid,
which is enough for a first look. View B needs no hints.

| hint | effect |
|---|---|
| `size (W,H)` | the canvas size |
| `views A`, `views B` | draw only that view (default: both) |
| `s@(X,Y)` | the position of state s; `s/2@(X,Y)` for state s of the second panel of a disjunction |
| `s@(X,Y) label (DX,DY)` | the same, with the label offset (default (0,-10)) |
| `edge a>b` | hints for the arrow from a to b; `#2` picks the second such arrow, `/2` the second panel |
| `edge a>b bend N` | bend the arrow by N pixels (signed) |
| `edge a>b side +` / `side -` | the side the arrow's notch opens to |
| `edge a>b at 0.3` | the notch at that fraction of the arrow (at most two decimals; default 0.35) |
| `loop s ANGLE` | the direction, in degrees, of a self-loop |
| `namedy N` | this figure's bound-name offset in its notches (signed integer, both views); overrides `--notch-name-offset` |
| `notch x up`, `notch x down` | view B: binder `x`'s notch always opens up (down); the link router routes around it and does not turn it over |
| `text (X,Y) red 11 middle italic "…"` | a caption: colour `black`/`red`/`grey` (default grey), size, `middle`, `italic` |

## 2. Drawing

```bash
lake build framediag
lake exe framediag OUTDIR [--fig FILE] [--no-pdf] [--links] [--hide-bound] [--spacing X] [--notch-name-offset DY] [--check] [--stats]
```

OUTDIR is required, even though `--check` and `--stats` write nothing.

| option | effect |
|---|---|
| `--fig FILE` | draw the figures in FILE (a text file in the syntax above; the normal input). Without it, `framediag` draws `exampleSource`. |
| `--no-pdf` | skip the PDF copies. Otherwise `rsvg-convert` must be on the PATH (macOS: `brew install librsvg`). |
| `--links` | binding links in view B (below). View A is unaffected. |
| `--hide-bound` | leave bound names out, in both views (and make the notches smaller) |
| `--spacing X` | scale every clearance of the links by X (decimal, default 1): row gaps, tracks, channels, and the room kept around states and for their names |
| `--notch-name-offset DY` | move each bound name DY units (signed decimal, default 0) into its notch (positive) or towards the stroke (negative), in both views. By default a name's x-height is centred at half the depth of a `∀` box and at 0.30 of the depth of an `∃` point, whichever way the notch opens. Up to 1 unit inwards the notch is unchanged; beyond that it deepens by the excess (a pointed notch also widens in proportion), so the name never touches the floor. A negative DY leaves the notch as it is. Small values (−2 to 3) are enough. A figure's `namedy` hint overrides it. Works with `--links`, `--hide-bound` (no name, no effect) and `--check`. |
| `--check` | route every view-B figure with links, names shown and hidden, and run the checks below |
| `--stats` | the same as `--check`, and also print, per figure and variant, the link-link crossings (different binders), link-stroke crossings and nesting violations |

Text is escaped for SVG: a text leaf or caption may contain `<`, `>`, `&` and `"`.

Output, for each figure NAME:

| file | content |
|---|---|
| `NAME.svg` | view A; or view B if the figure has `views B` |
| `NAME_B.svg` | view B (when both views exist) |
| `NAME.pdf`, `NAME_B.pdf` | PDF copies of the SVGs |
| `NAME.tex` | the formula in chained-relation notation (section 3) |
| `legend.svg`, `.pdf` | the key to view A (always written; so do not name a figure `legend`) |

### Links (`--links`)

* Each binder (notch) is joined to every state it binds by **one tree of
  links**, with a dot where it branches.
* Each binder has its own **pastel colour**, and its link is dashed in the
  **Morse code of its name** (dot 1.6, dash 5.5, short gaps; a short mark in
  the longer gaps between letters and repeats), so binders stay distinct in
  black and white.
* Phases (the header of `FregeDiagrams/Route/Router.lean` has the detail):
  1. view B is laid out as typed marks (with the flips as a parameter);
  2. the obstacles are read from the shapes (`Scene`);
  3. a routing grid is built: lines through terminals, tracks beside the
     rows, channels and columns around the tree;
  4. each binder gets an **exact minimum Steiner tree** in the grid
     (Dreyfus–Wagner), against the tree strokes and the other binders. Costs,
     in effect lexicographic: crossings and obstacles first; bends, length,
     name room, nesting and flips only break ties. A crossing with another
     binder's links costs less than one with the tree; running along a
     stroke costs most. A state is met from any side free of arrows and loops.
     Binders are routed in turn, then ripped up and rerouted;
  5. names are placed **after routing**, at the first free place among a few
     around the state; the room for them is reserved before routing;
  6. checks (below).
* **Scope nesting.** A binder whose scope contains another's routes outside
  it; inner binders prefer the tracks nearest the tree.
* **Flips.** For up to four binders every choice of flipped notches is tried;
  the three cheapest are routed again, in every routing order (up to four
  binders; otherwise the default order and its reverse). The best score wins.
* The result is optimal per binder given the grid, the cost model and the
  other binders. It is not globally optimal.

### Checks (`--check`, `--stats`)

Exit status 1, with a message, for:

* an **empty bigon**: a link and another curve crossing twice around a region
  holding no state, name or link end; or a **monogon**: a link crossing
  itself. Either can be removed, so the route is not in minimal position
  (the bigon criterion for curves on a punctured plane);
* a **misplaced name**: more than `10 × spacing` from its state, or with a
  link crossing the segment between them.

Only reported, exit status unaffected: **nesting violations** (outer binder,
inner binder, side): an inner binder's links running outside an outer
binder's on some side of the tree. The last line gives the three totals.

### Timings

Measured 2026-11-09 on this machine, `exampleSource` (11 small figures), after
`lake build framediag`. Wall time of `lake exe`, most of it start-up:

| command | time |
|---|---|
| `framediag OUT --no-pdf` | 2.5 s |
| `framediag OUT --no-pdf --links` | 2.4 s |
| `framediag x --check` | 2.8 s |

Routing time grows quickly with the number of binders in a figure: on a set
of 13 larger figures (up to four binders each) `--links` took about 24 s and
`--check`, which routes each figure twice (names shown and hidden), about
46 s. Without `--links` drawing is fast.

## 2a. Editing interactively (framedit, v0.1)

```bash
python3 -I tools/framedit/framedit.py FILE.fgd
python3 -I tools/framedit/framedit.py FregeDiagrams/Examples.lean
```

opens http://127.0.0.1:8765/ (this machine only; `--port N` to change it,
`--no-browser` not to open a browser). It builds `framediag` first. FILE is a
file of figures, as for `--fig`, or a Lean file that keeps its figures in a
raw string `def NAME : String := r#"…"#` (`--def NAME` if it has several):
then only the string's contents are edited and written back, error lines are
also given as lines of the file, and a save that would put `"#` into the
string is refused.

* Everything on the page is drawn by Lean (`framediag --serve`); every change
  is a change to the text, shown under the pictures and as a diff in the strip
  at the top.
* Sketch: click a state, a name or an arrow to select it; drag it; arrow keys
  nudge by 1, with Shift by 10; on an arrow ↑/↓ bend it and ←/→ move its
  notch; a selected arrow has a square handle to bend it. The inspector edits
  the same hints by number. These edits change hints only, never the formula.
* The text can be edited directly; it is parsed after a pause, and an error
  shows its line and column with a caret. The pictures keep the last good
  version, marked out of date.
* Undo and redo (⌘Z, ⇧⌘Z) restore whole texts; consecutive nudges of one
  object make one step.
* Save writes the file. It is refused when the text does not parse or when
  the file changed on disk since it was read, and it asks first when a
  formula changed, listing where each changed figure is used (`fig_of%`,
  `\diag`, `\formula` in the repository's `.lean` and `.tex`
  files). The inspector shows the same list for the current figure.
* Frege view: click a notch (or Tab to it) to select it; the inspector sets
  its side to *automatic*, *up* or *down* (the hint `notch x up|down`); ↑,
  ↓ and Delete do the same. With links on, the links are routed again.
* Problems lists the checks of `Diagrams/Lint` after every redraw (hints that
  match nothing, notches in the wrong place, overlaps, states off the
  canvas), each with Show and, where possible, a fix; Run checks adds the
  layout checks of the Frege view.
* The toolbar options (links, hidden names, notch-name offset) are the
  command-line flags; they are not stored in the file.

Not yet: editing the routes of the links. The plan is `docs/design/EDITOR.md`.

## 3. Using the output in LaTeX

Two macros include the output in a document (here the figures were drawn
into `figures/`):

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

The generated formulas use these macros (`\leadsto` needs `amssymb`):

```latex
\newcommand{\imp}{\rightarrow}
\newcommand{\sq}{\sqsubseteq}
\newcommand{\SqR}{\mathrel{{\sqsubseteq};R}}
\newcommand{\Y}{\mathrel{{\sqsubseteq};R;{\sqsubseteq}}}
\newcommand{\reach}{\leadsto}
\newcommand{\nF}{\notin F}
```

A build script can run `framediag` and then latexmk; pass the flags through
(for instance `--links --spacing 1.4`, or `--links --hide-bound`).

## 4. Adding a figure, and proving what it means

1. Write a `fig …` entry in a text file of your own, say `figures.fgd`.
2. Draw it and look at it:

   ```bash
   lake exe framediag _build/try --fig figures.fgd --no-pdf --links
   ```

3. Check the layout: `lake exe framediag x --fig figures.fgd --check`.
4. To tie it to a Lean condition, keep the source in a `def` and take the
   figure from it with `fig_of%`, which parses at elaboration time:

   ```lean
   import FregeDiagrams.Elab
   open FregeDiagrams

   def myFigs : String := r#"
   fig serial = all t. if s <= t then ex u. t R u°
   "#

   def serial : Fig := fig_of% myFigs "serial"

   -- in a library that defines `Form.denote` for its frames:
   theorem fig_serial :
       (∀ s, ¬ Fr.F s → serial.body.denote Fr (fun _ => s)) ↔ Fr.condSerial := by
     simp [serial, …]
   ```

   `fig_of% SRC "NAME"` takes any term `SRC : String` (a constant, or a
   string literal) and evaluates it at elaboration time; a parse error or a
   missing figure is an elaboration error. Since `SRC` is a Lean term,
   editing it rebuilds every use. `framediag` reads only files, so the text
   of `myFigs` must also be in the file given to `--fig`; nothing checks that
   the two copies stay equal.
5. Use `\formula{serial}` and `\diag{serial}` in the TeX.

Legend and bracketing figures (`legend_*`) have no meaning.

## 5. Status

* Tested, not proved: the round trip `parse (print d) = .ok d`
  (`ParsePrint`), checked by `#guard` on every figure of `exampleSource` and
  on 2000 pseudo-random ones (`lake build FregeDiagrams.Test`).
* Tested, not proved: no empty bigons or monogons, no misplaced names, in the
  routed links (`--check`; 0 of each, and 0 nesting violations, on
  `exampleSource`, 2026-11-09).
* Not built (proposals in `design/DESIGN.md`): automatic layout for view A, reflow
  for view B, HTML/Verso output, a proof of `ParsePrint`.
