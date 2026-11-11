# The figure editor: design and plan

Status 2026-11-11. Architecture: Lean is the only renderer and the only
writer of figure text. This file answers the design questions of 2026-11-11
(numbered as they were asked) and fixes the order of work. In this repository
the figures come from `--fig FILE` or from `exampleSource`, and
`fig_of% SRC "NAME"` already plays the part that section 9 plans for
`figure%`. From now on each editor version is a commit.

Vocabulary used below:

* **figure language**: the text language of `FregeDiagrams/Syntax.lean`
  (`fig NAME [hints] = formula`), files `*.fgd` or a Lean raw string such as `exampleSource`;
* **edge**: a drawn relation instance (an arrow of view A, a step of a leaf);
* **link**: a binding connector, from a quantifier notch to the states it binds
  (view B, `--links`);
* **stroke**: a line of the Frege tree (content, condition, judgement);
* **block**: a subtree of the Frege tree (a conjunct, a hypothesis, a
  quantifier's scope).

The three are kept distinct in the AST, in the SVG ids and in the editor
(question 2).

## 1. The figure language between Lean and the user

There are three layers, and the editor must keep their roles fixed:

| layer | role | who writes it |
|---|---|---|
| Lean definitions of the conditions a figure illustrates, and theorems `fig_X` | the meaning; authoritative | the user, in Lean |
| figure text | what is drawn, and the formula that `denote` reads | the editor, or the user as text |
| SVG, LaTeX | output | `framediag` only |

The link between the first two is the theorem `fig_X : (… denote …) ↔ cond`.

### 1a. A change that breaks the build: block, or go ahead?

Two kinds of error, treated differently:

* **The text does not parse.** Never written. Save is disabled, with the
  error at its line and column. Reason: `fig_of%` parses the whole source
  at elaboration time, so one unparsable figure would break every theorem that
  uses that source, not just one.
* **The text parses but the formula changed.** Written only after a choice in
  the save dialog, which names the theorems that use the figure:
  1. *Save as a new figure* (`ex_trans_2`): the old figure and its
     theorem stay as they are. The default.
  2. *Save and fix the theorem*: the text is written; the editor then runs
     `lake build` of the modules that use the figure, in the background, and
     shows the failing theorems with links that open them in VS Code.
  3. *Cancel.*

  Layout-only changes (hints) never ask: `denote` reads only the formula, so
  the theorems cannot be affected. The editor compares formulas, not texts, so
  it knows which case applies.

### 1b. Unicode, ASCII, Greek, roman and numeric names

* *Corrected 2026-11-11:* this said that any Unicode letter, Greek
  included, may begin a name; the parser accepts only ASCII letters and `_`
  (then also digits, `'`, `′`, `₀`–`₉`). `s`, `t₁`, `x12`, `u′` work; `σ`
  did not. Unicode of any kind is fine in labels, strings and comments
  (`-[≡ᵣ]-`, `"σ ⊨ φ"`). Greek letters (`Α`–`Ω`, `α`–`ω`) are accepted in
  names since 2026-11-11 (docs/LANGUAGE.md has the rule in force). The display name is the
  name, except that ASCII `'` displays as `′`.
* Relation symbols get an ASCII spelling and a display form (`<=` is `≤`,
  `~>` is `⇝`). In the editor's text pane, typing Lean's abbreviations
  (`\le`, `\sqsubseteq`, `\a`) inserts the Unicode, as in VS Code.
* Nothing depends on the Lean source using the same characters: the figure
  language does not parse Lean notation (1c).

### 1c. Elaboration and notation

The figure language never elaborates Lean notation. Its relation symbols are
those of a **signature**: a finite list of symbols, each with an arity, a
display form, a line style, a LaTeX form and the Lean constant it denotes
(question 7). `denote` builds the meaning from those constants, not from
notation strings, so there is nothing to reverse-parse and no Lean notation
can be refused for not elaborating. An unknown symbol is a parse error that
lists the symbols in scope. Lean's own notation and pretty printing stay in
Lean; the figure's display comes from the signature.

### 1d. One more language to learn

Mitigations, in order of effect:

1. Most edits need no text at all (positions, colours, relations, blocks).
2. **Figures from Lean** (phase 4): `fig NAME from CFrame.condX [hints]`. An
   elaborator reads the Lean definition and builds the formula, and the
   theorem `fig_X` is then by `Iff.rfl` (or one `simp`). The formula of such a
   figure is not editable in the editor at all (only hints are), so the user
   writes Lean only. The formula then comes from Lean.
3. Error messages: line and column, a caret, what was expected in words, and
   the symbols in scope. The grammar is small (one page), so messages stay
   short.

## 2. Notches on composite arrows

### What moving a notch does today

`edge a>b at 0.3` is a hint: `denote` ignores it, so moving a notch never
changes the meaning. But it can change the *reading*. A composite arrow
`s (ρ₁;ρ₂) y` hides an intermediate state z:
`s (ρ₁;ρ₂) y ⇔ ∃z. s ρ₁ z ∧ z ρ₂ y`. Read with the convention that a notch
binds at its position along the path (states before it are outside its scope,
states after it inside), the notch before the bead reads ∀y ∃z, after it
∃z ∀y.

### When it matters

The intermediate's quantifier is fixed by polarity: in a hypothesis it is ∀
(`(∃z. …) → C` is `∀z. (… → C)`), in a conclusion it is ∃. Two quantifiers
of the same kind commute, so:

* notch kind = intermediate kind (a ∀ notch on a hypothesis arrow, an ∃ notch
  on a conclusion arrow, the usual case): **the position is free**,
  every reading is equivalent;
* the kinds differ (`all y. s ≡;R y`, an ∀ on a conclusion arrow): **the notch
  must sit before the first bead**; anywhere later the picture reads ∃z ∀y,
  which is a different (stronger) statement.

Planned: the editor clamps the drag to the allowed interval and says why, and
`--check` reports a notch past a bead of the other kind (new check, phase 2).

### 2a. What a notch means in view A

View A is a picture of the formula, not a notation that determines it. A notch
says: this state is bound by this quantifier, and the arrow carrying the notch
is its guard (the first relation into the state inside the quantifier's
scope). What view A does not draw: the relative scope of quantifiers and
implications, beyond colour (polarity). So two different formulas can have the
same sketch, and view B (Frege) is the one that determines the meaning. The
editor will make this visible rather than hide it: selecting a notch
highlights its scope in the formula text and in the Frege view.

## 3. Fragile text, buggy annotations

* Text that does not parse is never saved (1a); the picture keeps the last
  good version, marked out of date.
* Every edit is checked before it is shown: Lean applies it, prints, parses the
  printed text again and compares with the edited figure. A mismatch refuses
  the edit and reports an editor bug, so a bug cannot reach the file.
* The element ids are written only in editor mode; the default output is
  byte-identical to today's (a test pins it), so an annotation bug cannot
  change a document that uses the figures.
* No "beginner mode": the safety above applies to everyone.

## 4. A menu of symbols in scope

Feasible and cheap once the signature exists: the server sends it at start-up
(one message), the page shows a palette (display form, ASCII spelling, Lean
constant, arity), and the text pane completes symbols. With figures from Lean
(1d.2) the signature is read from Lean declarations carrying an attribute, so
"in scope" means exactly what Lean has in scope.

## 5. Speed

The renderer is already compiled native code. The costs measured: 1.5 s
start-up of `lake exe`, a few ms to draw a figure without links, about 2 s to
route links. The persistent server removes the start-up, and the router runs
only when the editor is idle. Certified computation (an untrusted producer, a checker proved sound) fits a different need: making a
check kernel-certified (for instance that a route has no empty bigon) rather
than making it faster. It can be added for the checks later.

## 6. Ids, blocks and bigraphs

The Frege tree and its links are a bigraph in Milner's sense: the tree is the
**place graph** (blocks nest), the bindings are the **link graph** (links run
across block boundaries). This gives the rule for moving blocks:

* a block move is allowed exactly when it is a structural congruence of the
  formula that preserves the meaning: permuting the parts of `&` or `|`,
  exchanging two hypotheses of one `if` (Frege's own law of interchange of
  conditions, Begriffsschrift formula 8), α-renaming a bound name;
* moving a notch along the content stroke in view B is quantifier shifting, and
  is allowed only where it is valid (`∀x (A → B) ⇔ A → ∀x B` when x is not
  free in A; the ∃ forms only in the valid direction). Each allowed move is
  backed by a named Lean lemma about `denote` (`Form.denote_congr`), proved
  once, so the theorems `fig_X` survive a block move.

Ids: every edge, link, stroke, notch, state and block gets an id derived from
its position in the formula (a path in the AST), stable under hint edits.

## 7. Syntax

* Brackets for blocks are already in the grammar: `( … & … )`, `( … | … )`,
  `if … then …`, and `"text" {formula}`.
* **Signature** (phase 3): relations declared with arity, display, style,
  LaTeX and Lean constant; the present relations (`<=`, `<=°`, `R`, `R°`,
  `~>`, `=`, `!=`) become the first signature, so existing figures do not
  change. In Lean: an attribute on the definition of a relation, e.g.
  `@[figure_rel "≡ᵣ" (style := dotted) (latex := "\\equiv_r")]`.
* **n-ary relations** as hyperedges: `T(x, y, z)` for a ternary relation,
  drawn in view A as a small hyperedge dot with one tentacle per argument
  (labelled by argument position), in view B as a leaf. This is the hypergraph
  vocabulary of bigraphs' link graph, and it covers ternary relations.
* The planned hints (`set`, `fill`, `key`, `line`, per-notch
  `namedy`), each round-tripped in `FregeDiagrams/Test.lean`.

## 8. From the Begriffsschrift

Worth taking over, in order of use here:

1. **The ancestral** (§§26–31: "y follows x in the f-sequence"). `⇝ = (≤ ∪ R)*`
   is an ancestral; Frege's notation for it could replace the wavy line in
   view B.
2. **Laws of interchange and contraposition** of conditions (formulas 8, 28):
   these are the allowed block moves of 6.
3. **The definition stroke** (the double judgement stroke, §24): a figure made
   from a Lean `def` (1d.2) drawn with it, an asserted theorem with the plain
   judgement stroke, a mere content (a hypothesis displayed on its own) with
   none.
4. **Latin letters for generality, German letters in the concavity**: Frege
   writes free variables (implicit ∀ over the whole judgement, our "free
   state" s) in Latin italic and bound ones in Fraktur. An option to do the
   same would make free and bound names distinct at a glance.
5. **Second-order generality** (concavity over function letters): quantifying
   over a set or a relation (`all S.` for a set S of states).
6. **Derivations**: Frege's proofs are sequences of judgements with the rule
   and the premises written in the margin, and substitution tables. A
   derivation view could draw sequent derivations.

## 9. Generic

* `FregeDiagrams` stays Lean core only (no Mathlib).
* The built-in relations move into a signature (7); the core knows only symbols
  with arities.
* The editor takes a Lake package directory and a figure file (or a Lean file
  with a figure string) as arguments; nothing names a particular client.
* `fig_of%` is generalised to `figure% "FILE" "NAME"` reading any figure
  file at elaboration time (with the file declared to Lake as an input, so a
  change rebuilds the dependent theorems).

## 10. Figures inside documents, text flow, LaTeX rebuilds, the Lean code base

(Design note of 2026-11-11.)

* **Embedded figures.** Documents refer to figures by name (`\diag{NAME}`,
  `\formula{NAME}`, `fig_of% SRC "NAME"`, Verso later). The editor never edits
  a PDF; it edits the figure text, and lists for each figure every place it is
  used: TeX files, Lean theorems, slides. From a draft PDF the way back is a
  link: with `\diagdraft` on, `\diag{NAME}` puts an invisible link over the
  picture that opens the editor at that figure (`http://localhost:PORT/#NAME`),
  which a PDF viewer follows.
* **Text flow.** A figure's printed size is its canvas size times the scale in
  `\diag[scale]{…}`. The editor shows that size against a page frame of the
  target document (the text width of the document, or a landscape slide with one
  sketch and one Frege view) and warns when it does not fit. A slide preview
  shows both views at their printed size.
* **LaTeX rebuilds.** Save writes only the files whose bytes changed (`NAME.svg`,
  `NAME_B.svg`, the PDFs, `NAME.tex`), so `latexmk` reruns only when a figure
  actually changed. A "rebuild document" button runs the document's build command
  in the background and reports the result; the PDF viewer reloads the PDF itself.
* **The Lean code base.** Both directions:
  * figure → Lean: the theorems that use a figure are found by name; their
    state is shown after a background `lake build` of those modules; links open
    the theorem and the condition in VS Code (`vscode://file/…:LINE`);
  * Lean → figure: the signature from Lean declarations (7) and figures made
    from Lean definitions (1d.2).

## Order of work

Each step is one commit (or a few), reviewable on its own, with tests; the
default output stays byte-identical throughout.

| step | content | state |
|---|---|---|
| 1 | parse errors with line and column; token positions | done |
| 2 | source spans of figures, hints and formulas | done (`parseFileSpans`) |
| 3 | `DrawOpts.annotate`: ids on SVG elements (edges, links, strokes, notches, states, blocks) | view A done (states, labels, arrows, with their current hints); view B later |
| 4 | edit operations on hints, span-preserving text output, property tests | done (`FregeDiagrams/Edit.lean`); a comment next to a deleted hint goes with it |
| 5 | `framediag --serve` (JSON lines) and `tools/framedit/` (bridge + page): select, drag, nudge, undo, save with the rules of 1a and 3 — **first live version** | done: v0.1 (`tools/framedit/`); v0.2 also edits figures inside a Lean raw string (such as `exampleSource`) and lists the uses of a figure |
| 6 | new checks (unmatched hints, overlaps, off-canvas, notch reading of 2) in `--check` and the editor | done (`FregeDiagrams/Lint.lean`); the editor shows each problem with a fix instead of clamping drags |
| 7 | `set`/`fill`/`key`, `line`, per-notch `namedy` | |
| 8 | relation edits; block moves with `Form.denote_congr` (6) | |
| 9 | uses of a figure, draft links from the PDF, page frame, rebuild button (10) | |
| 10 | signature and n-ary relations (7); `figure% FILE NAME` (9) | |
| 11 | figures from Lean definitions (1d.2) | |


## Link editing (2026-11-11)

Decision (Matthew, 2026-11-11): **(A) pinned routes.** An edited binder's links
are stored as polylines in the tree's own coordinates (`route x …`, whole
units). Considered and not taken: (B) relative moves ("one track further
out"), which tie the text to the router's grid; (C) router preferences,
which are robust but not direct manipulation.

* A pin holds for one layout. It is checked against the binder's terminals
  (the notch point, and `NODE_R + 1` from each bound state on one of its four
  sides), ends within 1.5 units are snapped onto them with a short jog, and a
  pin that misses a terminal or has a slanted segment is not used: reported
  (`--check`, the editor's Problems, with a one-click "route automatically
  again"), never adapted silently.
* Since the layout of view B depends on which way every notch opens, pinning
  a binder also fixes every notch of the figure as drawn.
* Editing (the page, not Lean): the binder's links as a graph of points and
  horizontal or vertical segments; moving a coordinate of a point moves it
  along every segment sharing that coordinate; terminals do not move, and a
  segment reaching one gets a jog. The page draws only a preview during a
  drag; on release Lean checks and draws the pin.
