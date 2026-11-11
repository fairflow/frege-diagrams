# FregeDiagrams: design

**Status, 2026-11-09.** §1 (one language, two views), §2 (figures as Lean
terms) and the LaTeX output are IMPLEMENTED; the Lean executable replaced an
earlier Python generator, whose output it reproduces byte for byte. §3
(automatic layout), §5 (Verso) and the round-trip proof are PROPOSALS. Deviations from the original proposal are
marked *Changed*.

| piece | where | status |
|---|---|---|
| AST `Form`, `Fig`, hints | `FregeDiagrams/Fig.lean` | done |
| syntax: `Fig.print`, `Fig.parse`, `parseFile` | `FregeDiagrams/Syntax.lean` | done |
| round trip `ParsePrint` | `FregeDiagrams/Syntax.lean`, `FregeDiagrams/Test.lean` | stated, tested, OPEN |
| views A and B | `FregeDiagrams/View.lean` (+ `Frame`, `Tree`) | done, hand-placed hints |
| LaTeX | `FregeDiagrams/Latex.lean` | done |
| example figures | `FregeDiagrams/Examples.lean` (`exampleSource`) | done |
| key to view A | `FregeDiagrams/Legend.lean` (`legend`) | done |
| figures as terms, `fig_of%` | `FregeDiagrams/Elab.lean` | done |
| executable | `FregeDiagrams/Main.lean` (`framediag`) | done |
| meaning (`denote`) | in client libraries, not here | (none in this library) |

## 1. One language, two views

The **figure is a formula** with layout hints; variant A (frame picture)
and variant B (formula tree) are two *views* of it. View B draws the tree.
View A flattens it: chain steps become arrows of one graph, equal names one
state, colour by polarity (red positive, black negative), each quantifier a
notch on the first arrow into the state it binds, `ex x` a red state, an
`ex x` under an odd number of `not` a crossed state with a square notch.
A disjunction is one panel per disjunct (keys `name/k`).

### Grammar (as implemented; the authoritative copy is the header of `FregeDiagrams/Syntax.lean`)

```
figure ::= "fig" NAME hints? "=" form
form   ::= "all" NAME "." form | "ex" NAME "." form | "not" form
         | "if" form ("," form)* "then" form
         | "(" form ("&" form)+ ")" | "(" form ("|" form)+ ")" | "(" form ")"
         | STRING ("{" form "}")? | chain
chain  ::= state (rel state)*
state  ::= NAME "°"?
rel    ::= base (";" base)*
base   ::= "<=" | "<=°" | "R" | "R°" | "~>" | "=" | "!="
hint   ::= "size" (W,H) | "views" (A|B) | key "@" (X,Y) ("label" (DX,DY))?
         | "edge" NAME ">" NAME ("#" OCC)? ("/" PANEL)? ("bend" INT)? ("side" ±)? ("at" DEC)?
         | "loop" key ANGLE | "text" (X,Y) colour? SIZE? "middle"? "italic"? STRING
```

Example (verbatim from `exampleSource`):

```
fig ex_composite [size (300,140),
    s@(30,100), y@(250,100) label (12,4),
    edge s>y bend -40 at 0.17, edge s>y#2 bend 12, loop y -90] =
  all y. if s <=°;R;<= y° then (y R y & s ~> y)
```

*Changed* from the proposal:

* Text leaves are `"TEXT" {form}`: the braces hold a **formula of the same
  language** (its meaning), not a Lean term, since `denote` is a function on
  syntax and cannot elaborate a string. The text is what both views draw;
  the formula is what `denote` and the LaTeX use.
* Binders carry no `°` (`all y.`, not `all y°.`); `°` belongs to occurrences.
* New bases `R°` (`R` into an infallible state) and `!=`; a chain may have
  no steps (`t°` says `t ∉ F`).
* Hints grew to reproduce the hand-placed pictures: label offsets, edge keys
  with occurrence and panel, notch position `at`, loop angles, captions,
  canvas size, `views`.
* **Conjunction in view B is a fork**, not a double bar (2026-11-07): with the bar the first conjunct continued the main stroke
  and the others hung below it, which read as the hypotheses of a
  condition. Now the stroke ends in a junction dot and straight rays run to
  the parts, stacked symmetrically above and below.
* **Disjunction is primitive** (2026-11-07): `|` is a `Form.or`
  node and view B draws it as `Tree.or`, a fork with a hollow junction dot
  (r 2.6) and an arc (radius 9) across the rays from the first ray's angle
  to the last's, closing the fan like the opening of `∨`. Neither
  connective is encoded through the other (`¬A → B` for `∨`, `¬(A → ¬B)`
  for `∧`: both wrong intuitionistically). In AND–OR graphs an arc usually
  means *and*; here arc + hollow dot means *or*, and a document using the
  figures should say so.
  View A draws one panel per disjunct with the word "or" between them (a
  caption hint).
* `!=` steps and text leaves are not drawn in view A; captions (hints) say
  them.

### Read back

`Fig.print`, `Fig.parse` (tokens, then recursive descent; `partial def`).
`ParsePrint : Prop := ∀ d, d.WellFormed → Fig.parse d.print = .ok d`, where
`WellFormed` is syntactic (identifiers, no `"` in texts, `&`/`|` with ≥ 2
parts, `if` with ≥ 1 hypothesis, nonempty composites). **Not proved**:
tested by `#guard` on every figure and on 2000 pseudo-random well-formed
figures (`FregeDiagrams/Test.lean`, fixed seed). A proof needs structurally
recursive (or fuelled) versions of lexer and parser over `List Char`; that
is step 5 below.

Result of the switch from the Python generator, on its 17 pictures: 14
SVGs were byte-identical before the fork change; two differed only in
drawing order, and one view-B tree became the same formula as its view A
instead of a tree with text leaves. After the fork change all view-B trees
with a conjunction differ by design.

## 2. Link to logic: figures as Lean terms (implemented)

The library has no semantics: the AST stays free of any frame structure and
of Mathlib. A client gives figures a meaning by a function
`Form.denote f Fr e : Prop`, with `e : String → Fr.S`, into its own frames.
The intended reading:

| syntax | meaning |
|---|---|
| `x <= y`, `x R y`, `x ~> y`, `x = y`, `x != y` | `≤`, `R`, `(≤ ∪ R)*`, `=`, `≠` |
| `x <=° y` (bead) | `x ⊑ y`, i.e. `x ≤ y ∧ y ∉ F` |
| `x R° y` | `x R y ∧ y ∉ F` |
| `y°` | adds `y ∉ F` |
| `r₁;r₂` | `∃ m, r₁ x m ∧ r₂ m y` |
| `if H₁,…,Hₙ then C` | `H₁ → … → Hₙ → C` |
| `"t" {f}` / `"t"` | meaning of `f` / `True` |

`fig_of% SRC "NAME"` (`FregeDiagrams/Elab.lean`) evaluates `SRC : String` and
parses it at elaboration time, so a theorem `fig_NAME : (∀ s, s ∉ F →
denote …) ↔ cond` is about the very text that is drawn; a figure that
drifts from its condition breaks the build. `SRC` is a Lean term rather than
a file path so that Lake tracks the dependency.

## 3. Layout instead of coordinates (PROPOSAL)

**View B.** `measure`/`draw` is already a box layout (width, extent above
and below the stroke). Give each `&`, `|`, `if` node two arrangements,
*stacked* (as now) or *inline* (side by side), and for a target width `W`
choose inline where it fits, outermost first: the `group` rule of Wadler's
*A prettier printer* (1998), in two dimensions. Notches and negation ticks
never reflow.

**View A.** A simplified layered (Sugiyama) layout:

1. rank = longest path from `s` along hypothesis edges;
2. order within a rank by barycentre of neighbours, two sweeps;
3. conclusion edges that run backwards or overlap a straight edge are bent
   by `±k` per rank distance, alternating sides; loops point away from most
   edges; `∀` notches above, `∃` below, flipped on collision;
4. hints override.

Today a state without a hint goes on a plain grid.

## 4. LaTeX (implemented)

`Fig.toLatex` writes chained-relation notation (`\sq`, `\SqR`, `\Y`,
`\reach`, `\nF`, `^{\circ}`, bounded `\forall u\sqsupseteq s.`); the rules
are in the header of `FregeDiagrams/Latex.lean`, the macro definitions in
`../MANUAL.md` §5. `framediag` writes `NAME.tex`, and a document's
`\formula{NAME}` inputs it.

## 5. Verso (PROPOSAL, not implemented)

Verso documents (a blueprint, say) could show figures inline
from the same `Fig`, with no PDF step:

* a Verso code-block extension, say `` ```figure ex_trans``` ``, or a
  role `{figure}`ex_trans``, whose expander runs `fig_of%`'s lookup at
  elaboration time (so a missing or malformed figure is a document build
  error) and emits an HTML block;
* the block holds view A as an inline `<svg>` (the same `Diagram.svg`
  string) and view B as nested HTML: each leaf an inline SVG, each
  combinator a CSS flex container (`flex-wrap: wrap`), the condition stroke
  a `border-left`, the fork a small inline SVG joining the rows; this
  reflows with the page width without recomputing layout;
* the formula as KaTeX/MathJax from `Fig.toLatex` (the Blueprint already
  renders TeX math), and a hover link to the `fig_…` theorem, whose
  statement Verso can print from the compiled library.

## 6. What Lean buys, and what it costs

Buys: one source for picture, formula and meaning; with a client's
`denote`, a kernel-checked `↔` per figure (a figure that drifts from its
condition breaks the build);
typed relations and trees; speed (irrelevant: `rsvg-convert` dominates).
Costs: numeric fidelity work (`FregeDiagrams/Num.lean`), Lean float-literal
quirks, compile time, and `partial def`s that block proofs.

## 7. Order of remaining work

1. Tree reflow (view B), then layered layout (view A).
2. HTML/CSS and Verso output (§5).
3. The `ParsePrint` proof.

## Link routing (view B, `--links`)

`FregeDiagrams/Route/`. Drawing produces typed shapes (`Shape`, `FregeDiagrams/Frame.lean`)
and marks (`Mark`, `FregeDiagrams/Tree.lean`); SVG text is written only at the end.
The router works in phases, each a function: scene from the marks; routing
grid (lines through terminals and approach points, tracks beside rows,
channels and columns around the tree; H and V node per point, bend edges);
one exact minimum Steiner tree per binder (Dreyfus–Wagner, `Route/Steiner.lean`)
against the tree and the other binders, in turn and then rip-up and
reroute (every routing order for up to four binders, else the default and
its reverse), inner scopes first and preferring the nearest tracks; flips
chosen by trying all; names placed last, with room reserved; spacing as
`--spacing`; checks (empty bigons and monogons, misplaced names fail;
nesting violations are reported). `../MANUAL.md` has the user-facing account. Optimal per binder given the grid, the cost
model and the other binders; not globally optimal. (An earlier router, a
fixed route family searched exhaustively, is not included.)
