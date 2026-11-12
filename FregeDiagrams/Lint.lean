/-
FregeDiagrams.Lint: checks of a figure's hints and of the reading of view A.

Run by `framediag --check` (errors fail it) and shown live by the editor.

* **Unmatched hints** (error): a position, arrow or loop hint that names
  nothing in the picture has no effect.  This happens after a formula edit
  (reversing `s <= t` to `t <= s` leaves `edge s>t …` behind), and the
  renderer ignores such hints silently.
* **Notch reading** (error, `docs/design/EDITOR.md` §2): a composite arrow
  `s (ρ₁;…;ρₙ) y` hides intermediate states, quantified by polarity (∀ in a
  negative place, ∃ in a positive one).  A notch is read as binding at its
  place along the arrow.  When the notch's quantifier (in prenex form) and
  the intermediates' differ, a notch past the first bead reads the two
  quantifiers in the wrong order, a different statement; it must sit in the
  first stretch.  When they agree the place is free (same quantifiers
  commute).
* **Notch hints on an arrow without a notch** (warning): no effect.
* **`stroke` and `gap` hints that name no block** (error), or a `gap` on a
  block without room above it.
* **A definition that is not `"D" {f}`** (error): `judgement definition` needs
  the name it defines and its definiens.
* **Overlapping states** (warning) and **states or names outside the canvas**
  (error for a state, warning for a name), from the positions as drawn.

Each item carries the editor's key of the object (`state:NAME/P`,
`label:NAME/P`, `edge:A>B#OCC/P`) and, where there is one, an `Edit` that fixes
it.
-/
import FregeDiagrams.View
import FregeDiagrams.Edit

namespace FregeDiagrams

inductive Severity where
  | error | warning
deriving BEq, Repr, Inhabited

structure Lint where
  sev : Severity
  msg : String
  /-- the editor's key of the object concerned, or empty -/
  sel : String := ""
  /-- an edit that removes the problem, and what it does -/
  fix : Option Edit := none
  fixLabel : String := ""
deriving Inhabited

def Quant.word : Quant → String
  | .all => "every" | .ex => "some"

def Quant.sym : Quant → String
  | .all => "∀" | .ex => "∃"

/-- A state's id (`NAME/PANEL`) as shown: the panel only when it is not the first. -/
def idShow (id : String) : String :=
  match id.splitOn "/" with
  | [n, "1"] => dispName n
  | [n, p] => s!"{dispName n} (panel {p})"
  | _ => id

def edgeSel (src tgt : String) (occ panel : Nat) : String := s!"edge:{src}>{tgt}#{occ}/{panel}"

/-- The checks of the pictures of one figure (for a figure without view A,
only its notch hints). -/
def Fig.lintPictures (d : Fig) : Array Lint := Id.run do
  if d.hints.views == .b then
    -- only the view-B hint can be checked
    return (d.hints.notches.filter fun (x, _) => !d.shown.bound.contains x).toArray.map fun (x, up) =>
      { sev := .error, msg := s!"The hint notch {x} {if up then "up" else "down"} names no quantified state, so it has no effect.",
        fix := some (.notch x none), fixLabel := "Remove the hint" }
  let ((), fl) := (flatten d.shown 1 true false).run {}
  let h := d.hints
  let edges := fl.items.filterMap fun | .edge e => some e | _ => none
  let loops := fl.items.filterMap fun | .loop p a _ _ => some (p, a) | _ => none
  let mut out : Array Lint := #[]
  -- unmatched hints
  for nh in h.nodes do
    unless fl.nodes.any (fun n => n.panel == nh.key.panel && n.name == nh.key.name) do
      out := out.push { sev := .error,
                        msg := s!"The hint {nh.print} names no state of the picture, so it has no effect.",
                        fix := some (.unnode nh.key), fixLabel := "Remove the hint" }
  for eh in h.edges do
    unless edges.any (fun e => e.src == eh.src && e.tgt == eh.tgt && e.occ == eh.occ && e.panel == eh.panel) do
      out := out.push { sev := .error,
                        msg := s!"The hint {eh.print} matches no arrow, so it has no effect. (An arrow is named by the direction of its step in the formula, and #N counts arrows between the same states.)",
                        fix := some (.edge { eh with bend := none, side := none, at_ := none }), fixLabel := "Remove the hint" }
  for l in h.loops do
    unless loops.any (· == (l.key.panel, l.key.name)) do
      out := out.push { sev := .error,
                        msg := s!"The hint {l.print} names no loop of the picture, so it has no effect.",
                        fix := some (.loop l.key none), fixLabel := "Remove the hint" }
  -- view-B notch hints naming no binder
  let bound := d.shown.bound
  for (x, up) in h.notches do
    unless bound.contains x do
      out := out.push { sev := .error,
                        msg := s!"The hint notch {x} {if up then "up" else "down"} names no quantified state, so it has no effect.",
                        fix := some (.notch x none), fixLabel := "Remove the hint" }
  -- route pins naming no binder, or not drawn with horizontal and vertical segments
  for (x, ps) in h.routes do
    if !bound.contains x then
      out := out.push { sev := .error,
                        msg := s!"The hint route {x} … names no quantified state, so it has no effect.",
                        fix := some (.route x none), fixLabel := "Remove the hint" }
    else if ps.any (fun p => (p.zip p.tail).any fun ((a, b), (c, e)) => a != c && b != e) then
      out := out.push { sev := .error,
                        msg := s!"The route of {x} has a segment that is neither horizontal nor vertical, so it cannot be used; the links are routed automatically.",
                        fix := some (.route x none), fixLabel := "Route automatically again" }
  -- notches
  for e in edges do
    let eh := h.edges.find? fun eh =>
      eh.src == e.src && eh.tgt == e.tgt && eh.occ == e.occ && eh.panel == e.panel
    let sel := edgeSel e.src e.tgt e.occ e.panel
    match e.q, e.prenex with
    | none, _ =>
      if let some eh := eh then
        if eh.side.isSome || eh.at_.isSome then
          out := out.push { sev := .warning, sel,
                            msg := s!"The arrow {e.src}→{e.tgt} has no notch, so `side` and `at` in {eh.print} have no effect.",
                            fix := some (.edge { eh with side := none, at_ := none }), fixLabel := "Remove side and at" }
    | some _, some p =>
      let n := e.rel.length
      let inter : Quant := if e.concl then .ex else .all
      if n ≥ 2 && p != inter then
        let pos : Nat := ((eh.bind (·.at_)).getD 35)
        if pos * n ≥ 100 then
          let base : EdgeHint := eh.getD { src := e.src, tgt := e.tgt, occ := e.occ, panel := e.panel }
          let x := dispName e.tgt
          out := out.push { sev := .error, sel,
                            msg := s!"The {p.sym} notch for {x} on {e.src}→{e.tgt} sits past the first bead. The formula says: for {p.word} {x}, {inter.word} intermediate state; with the notch here the picture reads: {inter.word} intermediate state, then {p.word} {x}, which is a different statement. Put the notch in the first stretch (at below {printDec (100 / n)}).",
                            fix := some (.edge { base with at_ := some (50 / n) }),
                            fixLabel := s!"Move the notch to {printDec (50 / n)}" }
    | _, _ => pure ()
  -- positions as drawn
  let g := d.toDiagram
  let ns := g.nodes
  for i in [0:ns.size] do
    for j in [i+1:ns.size] do
      let a := ns[i]!; let b := ns[j]!
      let dx := a.x - b.x; let dy := a.y - b.y
      if dx * dx + dy * dy < 144 then
        out := out.push { sev := .warning, sel := s!"state:{b.id}",
                          msg := s!"The states {idShow a.id} and {idShow b.id} are less than 12 units apart; arrows between them cannot be told apart." }
  for s in ns do
    if s.x < 0 || s.y < 0 || s.x > g.w || s.y > g.h then
      out := out.push { sev := .error, sel := s!"state:{s.id}",
                        msg := s!"The state {idShow s.id} at ({s.x},{s.y}) is outside the canvas ({g.w}×{g.h}), so it is cut off." }
    else if s.label != "" then
      let lx := s.x + s.lx; let ly := s.y + s.ly
      if lx < 0 || lx > g.w || ly - 11 < 0 || ly + 3 > g.h then
        out := out.push { sev := .warning, sel := s!"label:{s.id}",
                          msg := s!"The name of {idShow s.id} is partly outside the canvas ({g.w}×{g.h})." }
  return out

/-- A definition must have the form `"D" {f}`: the name it defines, and its
definiens. -/
def Fig.lintJudgement (d : Fig) : Array Lint :=
  if d.hints.judgement == .definition && d.defines.isNone then
    #[{ sev := .error,
        msg := "A definition must be a text with its meaning, \"D\" {formula}: the name it defines and what it stands for.",
        fix := some (.judgement .claim), fixLabel := "Make it a claim" }]
  else #[]

/-- `stroke` and `gap` hints must name a block of the formula, and a `gap`
one that can take it (a hypothesis, or a fork part other than the first). -/
def Fig.lintBlocks (d : Fig) : Array Lint := Id.run do
  let mut out := #[]
  for (p, v) in d.hints.strokes do
    if (d.shown.blockAt p).isNone then
      out := out.push { sev := .error, msg := s!"The hint stroke {p} {v} names no block of the formula, so it has no effect.",
                        fix := some (.stroke p none), fixLabel := "Remove the hint" }
  for (x, v) in d.hints.nameDys do
    unless d.shown.bound.contains x do
      out := out.push { sev := .error, msg := s!"The hint namedy {x} {v} names no quantified state, so it has no effect.",
                        fix := some (.nameDyOf x none), fixLabel := "Remove the hint" }
  for (p, v) in d.hints.gaps do
    if (d.shown.blockAt p).isNone then
      out := out.push { sev := .error, msg := s!"The hint gap {p} {v} names no block of the formula, so it has no effect.",
                        fix := some (.gap p none), fixLabel := "Remove the hint" }
    else if !d.shown.gapable p then
      out := out.push { sev := .error, msg := s!"The hint gap {p} {v} has no effect: only a hypothesis, or a part of a fork other than the first, has room above it.",
                        fix := some (.gap p none), fixLabel := "Remove the hint" }
  return out

/-- The checks of one figure. -/
def Fig.lint (d : Fig) : Array Lint := d.lintJudgement ++ d.lintBlocks ++ d.lintPictures

end FregeDiagrams
