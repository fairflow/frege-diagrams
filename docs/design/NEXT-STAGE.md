# Frege Diagrams, the next stage: a formal reference and an architecture

**Status 2026-11-13: agreed by Matthew, with one change (section 12). Nothing
in it is built unless it says so.** Every statement about the present code is labelled:

- **PROVED**: a Lean theorem, kernel-checked, axioms pinned;
- **TESTED**: checked by `#guard` or a test program on examples and on
  generated cases, not proved;
- **OPEN**: stated, neither proved nor tested;
- **PROPOSED**: not built.

This document extends [DESIGN.md](DESIGN.md) (one language, two views),
[PROPOSAL.md](PROPOSAL.md) (blocks, sound rules, sheets),
[EDITOR.md](EDITOR.md) and [VSCODE.md](VSCODE.md). It does not repeat them.

## 0. Why now

The toolkit has grown past a toy:
- a figure language with a grammar, a manual and a notation guide;
- two views, binding links, and an editor in the browser and in VS Code;
- figures that are Lean terms, with claimed figures checked against their
  theorems.

Bugs have grown with it. The latest shows the kind:
- the VS Code extension looked for its drawing program in the folder of the
  window instead of in the Lake project of the file;
- a Lean file opened from another project therefore showed an *Edit figures*
  link that opened an error;
- every test passed, because no test said where the program must come from.

What is missing is a **reference**: a statement, for each layer, of what it
must do, precise enough to test and, where it pays, to prove. Sections 1 to 4
give that reference. Sections 5 to 9 give the architecture it supports:
- `.fgd` files as the source of truth;
- a language independent of Lean;
- styles and export;
- proof states in the Infoview, read and eventually driven through the
  diagrams.

Section 10 places the work among its sources, section 11 orders the work,
and section 12 lists the decisions for Matthew.

## 1. Principles

1. **One source of truth.** A figure exists as text in the figure language,
   in a `.fgd` file. Pictures, LaTeX, Lean terms and editor state are
   computed from it. Direct manipulation in an editor is an edit of that
   text.
2. **The language is not Lean's.** Lean is the implementation language and
   the first client. The language, its files and its tools stand without a
   Lean installation: a compiled kernel (`framediag`), a file format, a
   protocol.
3. **Layers with contracts.** Each layer of section 2 has a stated contract
   (section 3), and tests are derived from the contract, not from the code.
4. **Checked claims.** Anything said about the meaning of a figure is a Lean
   theorem; anything said about the tools is TESTED or PROVED, or labelled
   OPEN.
5. **Few file kinds.** Figures, style sheets and export settings are all
   `.fgd` files.
6. **Docs move with code.** Unchanged from CONTRIBUTING.md.

## 2. Layers

```
L5  meaning      a client's denote : Fig → Prop; theorems about figures
L4  hosts        framediag CLI · server (JSON lines) · language server ·
                 browser editor · VS Code · Lean elaborators · Infoview widget
L3  rendering    scene + style → SVG, PDF, TikZ, LaTeX style file
L2  scenes       geometry: points, edges, hyperedges, junctions, names,
                 notches, bars, regions — positions and shapes, no colours
L1  figures      abstract syntax: Form, Hints, File (figures + statements)
L0  text         the figure language: lexing, parsing, printing, spans
```

Today L2 and L3 are one step: `Diagram.svg` and the tree renderer produce
SVG strings directly, and `softSvg` rewrites them afterwards. Separating
a **scene** (L2) from its **rendering** (L3) is the main structural change
proposed here, because both styles (section 7) and checkable view properties
(section 3.3) need a scene that can be inspected.

## 3. The reference

### 3.1 Text and figures (L0, L1)

The abstract syntax is as implemented (DESIGN.md §1, LANGUAGE.md). A file is
now a sequence of figures and file statements:

```
File      ::= (Statement | Figure)*
Statement ::= default dash REL DASHING          (implemented, 0.11.0)
            | default PROPERTY CLASS VALUE      (PROPOSED, section 7)
            | include "PATH"                    (PROPOSED, section 6)
```

Laws:

```
(R1) round trip    ∀ d : Fig, d.WellFormed → Fig.parse (Fig.print d) = .ok d
(R2) file defaults ∀ s, parseFile s = .ok fs → ∀ f ∈ fs, f.defaults = (defaults of s, latest first)
(R3) spans         ∀ s f, parseFileSpans s = .ok fs → the span of each hint of f, cut from s
                   and parsed as a hint, gives that hint
```

| law | status |
|---|---|
| R1 | TESTED: every example, and 2000 pseudo-random figures with every kind of hint (`Test.lean`); OPEN as a theorem (DESIGN.md: needs a structurally recursive parser) |
| R2 | TESTED on examples |
| R3 | TESTED indirectly: every editor edit is checked at run time to reparse to the intended figure (`applyEdit1`) |

### 3.2 Edits (L1 on text)

An edit `e` acts on a figure's hints, `Edit.apply : Hints → Hints × Act`, and
on the text through the hint's span. The laws:

```
(E1) correctness   applyEdit s n e = .ok s'  →  parseFile s' = (parseFile s) with figure n's hints := (e.apply h).1
(E2) locality      s and s' agree outside the span of the one hint changed (and its comma)
(E3) inverses      adding then removing a hint gives back the text
```

E1 is checked at run time on every edit (`applyEdit1` refuses an edit whose
result does not parse to the intended figure): TESTED on every use. That makes
it a run-time assertion, not a guarantee. E2 and E3 are OPEN. All three are
decidable for given `s` and `e`, so they can become `#guard`s over generated
texts at once, and theorems later.

### 3.3 Views (L2): what a picture must show

A view is a function from a figure, options and a style to a scene. Its
contract is a list of properties of the scene in terms of the figure. Write
`steps f` for the chain steps of `f` (source state, composite relation,
target state, polarity), `binders f` for its quantified names, and `occ f x`
for the occurrences of `x` bound by its binder.

View A (the frame picture):

```
(A1) arrows    the arrows of the scene are in bijection with steps f (per panel);
               each arrow carries the step's composite relation, stretch by stretch
(A2) states    the states of the scene are the names of f (per panel), each once
(A3) notches   each binder x of f has exactly one notch, on the first arrow into x,
               of its quantifier's shape, opening to the side its hint says
(A4) polarity  colour of an arrow or state = polarity of its step or binder
(A5) canvas    every state, arrow and name lies inside the canvas
```

View B (the Frege tree):

```
(B1) tree      the blocks of the scene form a tree isomorphic to the formula tree
               (the place graph), each block at its path b/…
(B2) strokes   one judgement stroke for a claim, two for a definition, none for a content
(B3) links     with links on, for each binder x the link tree of x connects its notch to
               every occurrence in occ f x and to nothing else (the link graph)
(B4) scope     every link of x lies inside the region of the block x heads
(B5) adequacy  the formula can be read back from the scene: readB (viewB f) = f.shown
```

Both views:

```
(S1) determinism   a view is a function of (figure, options, style)
(S2) style         two styles give scenes with the same geometry: a style changes
                   attributes, never positions, sizes or topology
(S3) annotation    the annotated scene minus its annotations is the plain scene
```

| property | status |
|---|---|
| A1–A5, B1–B4 | OPEN as stated. Parts are TESTED today by `framediag --check` (states outside the canvas, notch placement, misplaced names, nesting) and by the router's own checks |
| B5 | OPEN. View A is not adequate: two formulas can share a view A (NOTATION.md), and that is a documented fact, not a bug |
| S1 | holds by construction: the code is pure Lean |
| S2 | TESTED for the soft and classic styles in the narrow sense that layout code does not read the style |
| S3 | TESTED for SVG output byte by byte (annotations off reproduces the earlier output) |

**How these become checks.** Each property is a decidable function of the
figure and the scene. With a scene as data (section 2), each property becomes
a checker `Scene.checkA1 : Fig → Scene → Bool`, and so on. Each checker is:
- run in `--check`;
- run on every generated figure in the tests;
- where it is worth the cost, proved: `∀ f, (viewA f).checkA1 f = true`.

This is the certificate pattern: an untrusted layout, a trusted checker. The
checkers are small, and their correctness is a statement about the
specification, which a reader can audit. The layout algorithms are large and
need not be proved.

### 3.4 Hosts (L4)

The hosts have contracts too. The failure in section 0 was a host failure.

```
(H1) program     for a file F, the framediag used is the one built by the Lake project
                 that contains F (nearest lakefile above F), else a configured path
(H2) page        the editor page comes from the same package as the program
(H3) protocol    each server op (parse, render, edit, body, lint, check, block) has a
                 JSON schema for its request and reply; a reply either matches its
                 schema or is an error object
(H4) save        a save is refused against a stale base and for text that does not parse
(H5) visibility  every failure the user can cause shows a message naming the cause and
                 the fix; nothing fails silently
```

H1 was violated until 0.11.1. H2 and H4 are TESTED by the smoke test. H3 is
OPEN: there are no schemas yet. H5 is a review rule, and since 0.12.0 every
error the extension shows is also recorded where tests can see it.

The missing test level was **VS Code itself**: the smoke test replaces the
`vscode` module with a stand-in, so it cannot see what the user sees. Since
0.12.0 a test runs a real VS Code (`@vscode/test-electron`, headless in CI,
`tools/vscode/test/integration/`). It:
- opens a plain folder, and a Lean file and a figure file from another Lake
  project;
- presses the lens, and opens the figure file in the figure editor;
- waits until each page has received a drawing from `framediag`, and checks
  that no error was shown.

So H1 is TESTED end to end; this test would have caught the bug of 0.11.0.

### 3.5 Meaning (L5)

The package gives figures no meaning; a client does, `denote : Fig → Prop`,
and states theorems about `fig_of% SRC "NAME"`. `@[figure_claim]` and
`#figure_claims` check that each claimed figure has a theorem (implemented).
Two additions, both PROPOSED:

```
(M1) generic interpretation   Form.interp D atom : Form → (String → D) → Prop
                              (PROPOSAL.md §4); a client's denote is an instance
(M2) rule soundness           ∀ r ∈ rules, ∀ f f', r f = some f' → (interp f' ↔ interp f)
                              (or →), proved once with axioms pinned, so valid
                              intuitionistically
```

M2 is what makes diagram moves (section 8) sound for every client at once.

## 4. Figures as a graph: points, edges, hyperedges

The vocabulary of graphical elements, and so of styles (section 7), is fixed
here once:

| element | in view A | in view B |
|---|---|---|
| **point** (vertex) | a state: hollow, filled, red, crossed | a state on a leaf's chain |
| **edge** | an arrow of a relation, or a stretch of a composite | a relation stretch in a leaf |
| **hyperedge** | — | a binder's link tree (one notch, many occurrences) |
| **junction** | — | a branch point of a link tree; a fork's dot |
| **name** | a state's label | a state's label; a name in a notch |
| **notch** | a quantifier on an arrow (⊓ for ∀, ∧ for ∃) | a quantifier on the content stroke |
| **bar** | — | judgement, content, condition and negation strokes |
| **region** | a panel of a disjunction | a block (not drawn; selected) |

The formal model is Milner's **bigraph**, as PROPOSAL.md §2 already says for
view B:
- the **place graph** is the nesting of regions: blocks in view B, panels
  (and later free regions) in view A;
- the **link graph** has one hyperedge per binder, with ports at its notch
  and at each occurrence;
- the scope condition B4 makes it a *binding* bigraph.

View A has the same link graph: a binder is a state, and its occurrences
are the arrows into it. Its place graph is flat, panels apart.

This model is what the requested *regions* (an open item) need: a region is a
place, the user draws its boundary, and moves that change nesting are the
reactions of section 8.

## 5. The figure language as a language of its own

- **Specification.** LANGUAGE.md and the grammar source (`docs/tools/grammar.py`)
  are the contract. A **conformance corpus**, `tests/conformance/*.fgd`, holds
  each case with its expected outcome:
  - parse, print, lint and check results;
  - the view properties of section 3.3, as JSON.
  
  Any implementation, including a future non-Lean one, is checked against it.
- **The kernel.** `framediag` is compiled Lean, a single binary with no Lean
  installation needed to run it. Distribution: release binaries for macOS,
  Linux and Windows built by CI (PROPOSED); a WebAssembly build of the
  kernel for a browser-only editor is OPEN as to feasibility (Lean compiles
  to C; an Emscripten build of the Lean runtime is the unknown).
- **The language server.** `framediag --lsp` (PROPOSED) speaks the Language
  Server Protocol: diagnostics (today's squiggles), completion of names and
  hint words, hover pictures, go to the uses of a figure, rename a state
  everywhere. Any editor with LSP support (VS Code, Emacs, Vim, Zed) then
  edits `.fgd` files properly; the VS Code extension shrinks to the preview
  and the bridge.

## 6. Files: `.fgd` as the source of truth

Today figures can live in a raw string inside a Lean file. That was a good
first step: one file, and `fig_of%` sees exactly what is drawn. It has
costs:
- the editor's text panel is small and not coloured;
- VS Code's file handling does not apply to a string;
- the figures cannot be used without Lean.

**Proposal.** Figures live in `.fgd` files. A Lean file that states theorems
about them reads the file:

```
def figs : String := include_str "figs.fgd"        -- Lean core
```

with the file declared to Lake as an input of the library, so that changing
the figures rebuilds the theorems:

```toml
[[input_file]]
name = "figs"
path = "Diagrams/figs.fgd"

[[lean_lib]]
name = "Diagrams"
needs = ["figs"]
```

Both halves are TESTED on Lean 4.31 (2026-11-13, a scratch project):
- **without** the `input_file` declaration, Lake did not rebuild after the
  `.fgd` changed, and the theorems would have been checked against the old
  figures;
- **with** it, the module was rebuilt and read the new text.

A convenience elaborator `fig_file% "figs.fgd" "NAME"` (PROPOSED) can do both
steps and report an error if the file is not declared.

Raw strings stay supported. The editor offers *Move figures to a `.fgd`
file*, which writes the file, replaces the string with `include_str` and
prints the lakefile lines to add.

**`include` and file statements.** `include "house-style.fgd"` (PROPOSED)
reads the statements of another file: style sheets (section 7) and shared
defaults. Included files may hold statements only, not figures, so that a
figure has exactly one home.

**In VS Code**, following principle 1:
- a `.fgd` file opens in the **text editor**, with colouring, squiggles and
  quick fixes (all implemented), and completion (with the language server);
- **Open Preview to the Side**, as for Markdown, shows the figure under the
  cursor in both views and follows the cursor from figure to figure;
- dragging in the preview edits the text, which the text editor shows at
  once;
- the **figure editor** stays (decision 3): the page that is the browser
  editor, and in VS Code the custom editor that *Reopen With…* offers, for
  quick changes and for use outside VS Code;
- its text panel sits in an **opener**, a section closed by default, so the
  drawing has the room; open, it shows the text coloured with the same
  grammar.

The preview and the figure editor are one page in two modes, so one code
path serves every host, as now.

### 6.1 Screen space and phones (PROPOSED; important, not urgent)

The page should work on a phone and keep clutter down everywhere. The
rules:

- **The drawing first.** Everything else is in openers, closed by default:
  the text, the inspector of the selection, styling (section 7), the
  figure list.
- **One column on a narrow screen.** The two views stack. An open panel
  becomes a sheet from the bottom of the screen, not a side column.
- **The selection's panel under the drawing**, showing only what concerns
  the selected element.
- **A full-screen button** for either view, with the export buttons (SVG,
  PNG, PDF) beside it.
- **Touch.** Every drag is a pointer event and works with a finger. Where a
  hit area is smaller than a finger, a long press opens a chooser of the
  candidates under it.

These follow the Astrodynamics app ([fairflow/astro](https://github.com/fairflow/astro),
GUIDE.md): a panel under the wheel for the selection, a chooser where lines
overlap, full screen with export beside it, and one *Display* menu for theme,
contrast and text size.

## 7. Styles, skins and export

A **style** fixes how the elements of section 4 look; it never changes
geometry (S2). Styles are written as file statements, extending `default
dash` (0.11.0):

```
default style soft                       -- a built-in skin: soft | classic
default width bar 1.6                    -- PROPERTY CLASS VALUE
default width edge R 1.0                 -- a class may be narrowed to a relation
default dash edge <= ". "
default colour claim "#c0392b"           -- polarity colours
default font name "Latin Modern Math" 12
default radius point 3.2
default corner 3.5                       -- rounded bends
default palette hyperedge "#4c9be8" "#e8894c" "#5bb37a"
```

The general form is `default PROPERTY CLASS [REL] VALUE`. The classes are
point, edge, hyperedge, junction, name, notch, bar and region, and the
properties are those of the table below. A **skin** is a `.fgd` file of such
statements, used with `include`. A figure's own hints override the file's
defaults, as `dash` does now.

| property | classes |
|---|---|
| width | edge, hyperedge, bar, notch |
| dash | edge, hyperedge |
| colour | claim, hypothesis, grey, palette entries |
| radius | point, junction |
| corner | edge, hyperedge, bar, notch (rounded bends) |
| font | name, text |

**The styling panel** (PROPOSED). Styles are edited in a panel of their
own, an opener of the page (6.1), not in the figure inspector.
- Every colour, width, radius and font of the drawing is a CSS custom
  property set from the style. The panel changes the properties, and the
  drawing changes at once without being drawn again.
- *Save* writes the changes as `default` statements to the skin file.
- Dark and light, and low and high contrast, are skins.
- A test forbids colours written directly in the page or the SVG output,
  as Astrodynamics does after three cases of dark text on a dark ground.

**Export.**
- `framediag --export latex-style OUT.sty` (PROPOSED) writes the style as
  LaTeX: `xcolor` colours, TikZ styles named after the classes
  (`fd point`, `fd edge R`, …), and `\fregefigure{NAME}`, which includes a
  figure's PDF.
- `--export tikz` (PROPOSED) writes a figure as TikZ code that uses those
  styles, so a paper's figures follow the paper's style sheet.
- SVG and PDF remain the default outputs.

## 8. Proof states: reading them, and driving them

This is the longest-range part, and the reason for the formal care above.

### 8.1 Displaying a goal (PROPOSED)

A client that has a `denote` can also supply a **reification**:

```
reify : Lean.Expr → Option Fig
adequate : ∀ e f, reify e = some f → (denote f ↔ ⟦e⟧)
```

The adequacy statement is per instance, as `figure_claims` is: when the
Infoview shows a goal, the widget reifies it, and the equivalence is
checked by elaboration: by `Iff.rfl` where `denote f` unfolds to the goal;
where it does not, the figure is not shown and the widget says why. The figure is then drawn in the
Infoview with Lean's user widgets, beside the text goal, and redrawn as the
proof state changes. A goal the client cannot reify is shown as text only.

### 8.2 Moves on diagrams (PROPOSED)

A **move** is an edit of the formula, made in view B, with a soundness
lemma:

```
structure Move where
  name  : String
  apply : Form → Option Form           -- none where a side condition fails
  sound : ∀ f f', apply f = some f' → (interp f' → interp f)   -- backward: f' suffices for f
```

Performing a move on the goal's figure runs a tactic: it applies `sound` and
leaves `denote f'` as the new goal. The diagram drives the proof, and every
step is checked by the kernel like any tactic. First moves, mirroring natural
deduction on the Frege tree:

| move | on the tree | logic |
|---|---|---|
| assume | a hypothesis block moves into the context | →-introduction |
| generalise | a ∀ notch is removed, its state fresh | ∀-introduction |
| split | a fork's parts become separate goals | ∧-introduction |
| witness | a ∃ notch is filled by a chosen state | ∃-introduction |
| interchange | two hypotheses swap | Begriffsschrift formula 8 |

The rules of PROPOSAL.md §4 (equivalences) are moves in both directions.

Moves are rewrite rules on the bigraph of section 4: in Milner's terms,
reaction rules, so the figure language with moves is a bigraphical reactive
system.

The heterogeneous rules of Hyperproof and the transformation rules of
Peirce's existential graphs are the precedents. Erasure, insertion,
iteration and deiteration have direct counterparts on Frege's trees, which
is Shin's line of work. They are candidates for later moves once each is
given its lemma.

### 8.3 Why

Matthew's motivation, recorded here as his:
- a visual-spatial representation may suit some people better than a linear
  one, as his work on how signers process technical information suggests;
- formal visual languages for mathematics and logic are a neglected
  resource.

The design's answer is to make the diagram a first-class, checked interface
to proof, not an illustration of it.

## 9. Reaching beyond Lean

Section 5's kernel, file format, protocol and language server make the tool
usable by people who never open Lean:
- they draw and check figures, export them to LaTeX, and edit them in their
  own editor;
- Lean is needed only for meaning: claims, theorems and proof states.

## 10. Sources

Bibliographic details are from memory and are to be checked before
publication.

- G. Frege, *Begriffsschrift* (1879): the notation of view B; judgement,
  content and condition strokes; generality by the concavity (notch).
- C. S. Peirce, existential graphs; S.-J. Shin, *The Logical Status of
  Diagrams* (1994) and *The Iconic Logic of Peirce's Graphs* (2002): diagrams
  as a formal system in their own right, with syntax, semantics and rules,
  and soundness and completeness proved for them.
- J. Barwise and J. Etchemendy, *Hyperproof* (1994) and *Turing's World*;
  G. Allwein and J. Barwise (eds.), *Logical Reasoning with Diagrams* (1996):
  heterogeneous reasoning, with rules that move information between diagram
  and sentence.
- D. Harel, statecharts (1987) and "On visual formalisms" (1988): higraphs,
  blobs and orthogonal components, a precise reading of nesting and
  regions.
- R. Milner, *A Calculus of Communicating Systems* (1980) and *Communication
  and Concurrency* (1989): flow graphs as an exact display of a system's
  static structure beside its dynamics. R. Milner, *The Space and Motion of
  Communicating Agents* (2009), with O. H. Jensen: bigraphs (place graph,
  link graph, binding) and bigraphical reactive systems.
- M. Fairtlough and M. Mendler, Propositional Lax Logic (1997): the logic
  whose frames view A draws.

## 11. Order of work

Each step is a pull request with a version, as now.

1. **Hosts (now).** 0.11.1 fixes H1. Next: a real-VS Code test in CI
   (section 3.4); JSON schemas for the server (H3).
2. **The reference.**
   - scenes as data (L2 separate from L3);
   - checkers for A1–A5, B1–B4, S2 and S3, run in `--check` and on
     generated figures;
   - a ledger of PROVED, TESTED and OPEN in this document;
   - the conformance corpus.
3. **`.fgd` as the source.** `include_str` with `input_file`, `fig_file%`,
   *Move figures to a `.fgd` file*, the VS Code preview, and the language
   server.
4. **Styles.** The general `default` statements, `include`, skins, the
   styling panel, and LaTeX style and TikZ export.
4a. **Screen space.** Openers closed by default, one column on narrow
   screens, touch (6.1).
5. **Meaning.** `Form.interp` and the rules with their proofs (M1, M2).
6. **Infoview.** Display of goals (8.1), then moves (8.2).
7. **Regions and sheets.** Places in view A, sheets and derivations
   (PROPOSAL.md §5).

Steps 2 and 3 are independent and can run side by side; 5 must precede 6.

## 12. Decisions (Matthew, 2026-11-13)

All the recommendations are agreed, with one change to the third.

1. **The layer split (section 2):** agreed. Scenes are separated from
   rendering.
2. **`.fgd` by default (section 6):** agreed. Figures move out of raw strings
   into `.fgd` files, read with `include_str` and an `input_file`
   declaration. Raw strings remain supported.
3. **VS Code:** a `.fgd` opens as text with a preview to the side, as
   proposed. **Changed:** the figure editor is kept, as an option for quick
   changes and for use outside VS Code, with its text panel in an opener
   closed by default (section 6). A layout that works on phones and keeps
   the screen clear, with a separate styling panel, is important but not
   urgent (6.1, section 7).
4. **Style syntax:** `default PROPERTY CLASS [REL] VALUE`, as proposed.
5. **What to prove:** the checkers' soundness and M2, as proposed. The round
   trip stays TESTED until the parser is structurally recursive.
