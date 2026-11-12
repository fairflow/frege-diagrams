# Proposal: judgement strokes, blocks, editing view B, sound transformations

Status 2026-11-12: a proposal; steps 1 and 2 of section 7 are implemented. It extends
[EDITOR.md](EDITOR.md) (sections 6 and 8 there) and keeps its rules: Lean is
the only renderer and the only writer of figure text; the default output of
every existing figure stays byte-identical; every new construct is a hint or a
new keyword with a default, so old files parse and print unchanged.

## 1. Judgement strokes: 0, 1 or 2

Frege distinguishes a judgement from a content (Begriffsschrift §2) and marks
a definition with a double judgement stroke (§24). Three kinds of figure:

| strokes | kind | drawn | means |
|---|---|---|---|
| 1 | **claim** (default, as now) | `⊢` | a result: some Lean theorem must state it |
| 2 | **definition** | `⊩` (double stroke) | an abbreviation `"D" {f}`: D is defined as f |
| 0 | **content** | content stroke only | a formula displayed, nothing claimed |

**Language.** One new hint, printed only when it is not the default:

    judgement-hint ::= "judgement" ( "claim" | "definition" | "content" )

    fig trans [judgement content] = if s <= u, u <= t then s <= t
    fig inf_def [judgement definition] = "inf(u)" {all t. if u R t then t°}

A definition must be a text with a meaning, `"D" {f}`, the form the language
already has for named abbreviations; `Lint` reports any other shape. View A
draws all three kinds alike (it shows no judgement); view B differs only in the
leftmost stroke; the LaTeX formula of a definition is `D :≡ f`.

**Lean.** `Fig` gets a field `judgement : Judgement := .claim`, so `fig_of%`
and existing clients are unaffected. A claim can be checked: an attribute
`@[figure_claim SRC "NAME"]` on the theorem that states figure NAME, and a
command `#figure_claims SRC` that fails when a claim of SRC has no tagged
theorem (in the manner of the axiom pins). A client that gives figures a
meaning (`denote`) can then require the tagged theorem to mention the figure.

**Cost.** One hint, one stroke variant in `Tree.lean`, one field; no effect on
speed.

## 2. Blocks: the place graph, and selecting a region

A **block** is a subtree of the formula tree (EDITOR.md vocabulary). View B
with its links is a bigraph in Milner's sense: the tree is the **place graph**
(a block's region contains the regions of its sub-blocks), the bindings are
the **link graph** (one hyperedge per binder, one port per occurrence). More
exactly it is a *binding* bigraph: a binder's links must stay inside the
region of the block it heads. This is the scope condition, and it gives the
precise meaning of a "point of no return": **a move is refused when it would
take an occurrence out of its binder's region, or put a foreign occurrence
into it.**

The regions are not drawn; they are selected:

* a click on a **branch point** (a fork's dot, the junction of a condition
  stroke, a notch) selects the block that starts there;
* `Alt+↑` widens the selection to the enclosing block, `Alt+↓` narrows it;
  `Esc` clears it;
* the selected block is highlighted in view B, and its states and arrows in
  view A (view A is not a tree: shared states and loops make it a graph, so it
  has no regions of its own, only the images of view B's blocks).

Loops and shared states belong to view A and the link graph, never to the
place graph, so the tree structure of blocks is exact.

**Implementation.** Each block gets an id from its path in the formula (`b.1.0`:
the conclusion's first hypothesis), as planned in EDITOR.md step 3, written on
its SVG group by `DrawOpts.annotate`. Paths are stable under hint edits.

## 3. Editing view B

The same gestures as view A (select, drag, arrow keys nudge), on the elements
of the tree:

| handle | moves | stored as |
|---|---|---|
| a condition stroke's junction | the hypothesis up or down (vertical gap) | `gap PATH DY` |
| the end of a content stroke | the leaf left or right (stroke length) | `stroke PATH DX` |
| a fork's ray | the spread of the fork | `spread PATH DY` |
| a notch | the notch along its stroke | `notch x at T` (0–1 along its segment) |

**Notches.** A notch can slide freely along its own stroke segment, between
the neighbouring junctions: that is layout only, the formula is unchanged.
Crossing a junction is a change of the formula (quantifier shifting). It is
offered only as a rule of section 4: the drag stops at the junction, and the
side panel offers the shift with its status (`⇔`, `⇒`, `⇐`, or refused). For
example, moving `∀x` right past a hypothesis H:

    ∀x (H → C)  ⇔  H → ∀x C        when x is not free in H
    ∃x (H → C)  ⇒  H → ∃x C        when x is not free in H (the converse is not valid)

and refused whenever x is free in H, the bigraph condition of section 2.

**Links while editing.** Decided (Matthew, 2026-11-12): no mode. The
handles are always there; a drag hides the links of the figure, and they are
routed again on release, in the background, as now. (Considered and not
taken: the handles of view B act only with `Links` off.)

**Pins and view options** (a fix, independent of the rest). A pinned route is
laid out with names shown and no nudge. With "hide bound names" or a nudge
the tree's geometry changes and the pin is reported as no longer fitting,
which reads as an error in the file. Two remedies: (a) the editor says that
the pin holds for names shown and draws the other settings routed
automatically, without an error; (b) pins are stored relative to the strokes
(a track number) instead of in absolute coordinates. (a) is small; (b) is the
choice (B) that was not taken on 2026-11-11.

## 4. Changing the formula: structure edits and sound rules

Two kinds of edit, never confused in the interface:

1. **Structure edits** change what the figure says, on purpose: wrap a block
   as the conclusion or a hypothesis of a new `if`; add a block as a part of an
   `&` or `|`; negate it; quantify it; delete it; drag it onto another block
   (drop targets: a stroke's end, a fork, a junction). The editor shows the new
   formula and says that the meaning changed; the theorems of a claim will need
   attention (EDITOR.md 1a).
2. **Rules** replace a block by one that is equivalent (`⇔`) or that follows
   from it (`⇒`): interchange of conditions (Begriffsschrift formula 8),
   currying `if A, B then C ⇔ if (A & B) then C`, permuting the parts of `&` and
   `|`, α-renaming, quantifier shifting as in section 3,
   `∀x (A & B) ⇔ ∀x A & ∀x B`, `∃x (A | B) ⇔ ∃x A | ∃x B`,
   `∃x A → C ⇔ ∀x (A → C)` (x not free in C), contraposition in its valid
   direction.

Rules that are **not** intuitionistically valid are not offered, for example
`∀x (A | B) ⇒ A | ∀x B` (x not free in A), which is the constant-domain
principle, and `(H → ∃x C) ⇒ ∃x (H → C)`.

**Soundness in Lean.** The package gives figures no meaning, but every
client's meaning has the same shape: chains and texts are interpreted by the
client, and the connectives and quantifiers are those of Lean. So the package
defines a generic interpretation

    Form.interp (D : Type) (atom : Leaf → (String → D) → Prop) : Form → (String → D) → Prop

and proves each rule once: `interp (rule f) ↔ interp f` (or `→`), with
**axioms pinned** to exclude `Classical.choice`, so that each rule is
intuitionistically valid and not just classically. A client whose `denote` is
an instance of `interp` (as `denote` in the present client is) gets every
rule for free, and a theorem about a figure carries over to its rewritten form
by the rule's lemma. A rule is a Lean function `Form → Option Form` (it
returns `none` where its side condition fails), run by the server; the side
conditions are syntactic (free names), so checking one is immediate.

## 5. Several diagrams in one: sheets and derivations

A **sheet** is a sequence of figures drawn together, each with its own
judgement stroke:

    sheet NAME [hints] = fig₁, fig₂, …

and a **derivation** is a sheet whose steps are justified, in the manner of
Frege's proofs (judgements in a column, the rule and its premises in the
margin):

    derivation NAME = A by premise; B by interchange A; C by mp A B

Each step is checked by the server (the rule of section 4 applied to the cited
steps must give the step), and the whole derivation is a Lean term, so it can
be a theorem. Drag and drop between the figures of a sheet is a structure
edit (section 4) that copies a block. This comes last: it needs sections 1, 2
and 4.

## 6. No modes

Rules for keeping the editor non-modal as it grows:

* **select, then act.** A click selects the smallest element under the
  pointer (state, arrow, notch, stroke, branch point); actions apply to the
  selection and are listed in the side panel with their keys. There is no
  tool to pick first.
* **Layout and meaning are separate.** A drag changes only the layout. A
  change of the formula always comes from an explicit action or an explicit
  drop, and is previewed (the new formula and its status `⇔`, `⇒`, changed)
  before it happens.
* **Every action is undoable** (the history of whole texts) and every state is
  visible: no hidden tool, no sticky mode, the same keys in both views.
* **View options are not modes.** `Links`, `hide bound names` and the nudge
  change what is drawn, never what a gesture does.

## 7. Order of work

| step | content | size |
|---|---|---|
| 1 | judgement strokes (section 1): hint, drawing, field, docs, tests | small; done 2026-11-12 (PR #10) |
| 2 | pins and view options, remedy (a) (section 3) | small; done 2026-11-12 (PR #11) |
| 3 | block ids in view B, block selection, highlight in view A (section 2) | medium |
| 4 | view B layout hints and handles; notches along their segment (section 3) | medium |
| 5 | `Form.interp`, the rules with pinned soundness theorems, structure edits and rules in the editor (section 4) | large |
| 6 | `@[figure_claim]` and `#figure_claims` (section 1) | small |
| 7 | sheets and derivations (section 5) | large |

Steps 1, 2 and 6 are independent of the rest; 4 needs 3; 5 needs 3; 7 needs
1, 3 and 5. Each step is one pull request, and its documentation changes with
it (CONTRIBUTING.md).
