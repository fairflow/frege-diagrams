/-
FregeDiagrams.Spec: the reference for view A (docs/design/NEXT-STAGE.md §3.3).

What view A must show is stated here **independently of the code that draws
it** (`flatten` and `Fig.toDiagram` in `FregeDiagrams.View`): `Spec.contentA`
is a plain recursion over the formula giving, per panel, its states, its chain
steps with their relation and polarity, and its quantifiers with the steps in
their scope.  `Fig.checkA` compares a drawn `Diagram` with it, property by
property, and returns the violations as messages:

* A1 arrows   — the arrows are the steps between distinct states, each with
                its composite relation; the loops are the steps from a state
                to itself, each with its composite relation (steps with `!=`
                are not drawn)
* A2 states   — the states are the names of the chains, per panel, each once
* A3 quantifiers — each quantifier binding something is shown exactly once:
                by a notch on an arrow into a state it binds if there is one,
                else by a mark on the state
* A4 polarity — an arrow is red exactly when its step is claimed; a state
                bound by `ex` is red (new) in a claimed place, crossed under
                an odd number of `not`
* A5 canvas   — states, their names and arrows lie inside the canvas

A checker is only as good as its statement; these are written to be read and
audited, and are tested on the examples and on generated figures
(`FregeDiagrams/Test.lean`).
-/
import FregeDiagrams.View
import FregeDiagrams.Syntax

namespace FregeDiagrams.Spec

/-- A chain step, as the formula states it, with the quantifier (if any) that
binds its target. -/
structure Step where
  panel : Nat
  src : String
  tgt : String
  rel : Composite
  /-- in a claimed (positive) place: drawn red -/
  claim : Bool
  /-- the quantifier binding the target here (an index into `quantifiers`) -/
  tgtBinder : Option Nat := none
deriving BEq, Repr, Inhabited

/-- A quantifier occurrence. -/
structure Quantifier where
  panel : Nat
  name : String
  ex : Bool
  /-- under an odd number of `not` -/
  neg : Bool
  claim : Bool
deriving Repr, Inhabited

/-- What view A must show.  `occs` are the occurrences of states in chains:
panel, name, and the quantifier binding it there. -/
structure ContentA where
  states : List (Nat × String) := []
  occs : List (Nat × String × Option Nat) := []
  steps : List Step := []
  quantifiers : Array Quantifier := #[]
  nextPanel : Nat := 2
deriving Inhabited

/-- The content of a formula in view A.  `env` maps a name to the innermost
quantifier binding it.  The first part of a disjunction keeps the panel; each
further part gets the next new panel, in the order the formula is read. -/
partial def walk (f : Form) (panel : Nat) (claim neg : Bool) (env : List (String × Nat)) :
    StateM ContentA Unit := do
  match f with
  | .chain st steps =>
    let note (x : String) : StateM ContentA Unit := modify fun c =>
      let c := { c with occs := c.occs ++ [(panel, x, env.lookup x)] }
      if c.states.contains (panel, x) then c else { c with states := c.states ++ [(panel, x)] }
    note st.name
    let mut prev := st.name
    for (r, t) in steps do
      note t.name
      modify fun c => { c with steps := c.steps ++
        [{ panel, src := prev, tgt := t.name, rel := r, claim, tgtBinder := env.lookup t.name }] }
      prev := t.name
  | .text _ _ => pure ()
  | .all x b => quant x false b
  | .ex x b => quant x true b
  | .not b => walk b panel (!claim) (!neg) env
  | .imp hs c =>
    for h in hs do walk h panel (!claim) neg env
    walk c panel claim neg env
  | .and ps => for p in ps do walk p panel claim neg env
  | .or ps =>
    let mut first := true
    for p in ps do
      if first then
        walk p panel claim neg env
        first := false
      else
        let k := (← get).nextPanel
        modify fun c => { c with nextPanel := k + 1 }
        walk p k claim neg env
where
  quant (x : String) (ex : Bool) (b : Form) : StateM ContentA Unit := do
    let i := (← get).quantifiers.size
    modify fun c => { c with quantifiers := c.quantifiers.push { panel, name := x, ex, neg, claim } }
    walk b panel claim neg ((x, i) :: env)

def contentA (f : Form) : ContentA := ((walk f 1 true false []).run {}).2

/-- Is a step drawn at all (steps with `!=` are not drawn in view A)? -/
def Step.drawn (s : Step) : Bool := !s.rel.contains .ne

/-- The number of times `a` occurs in `xs`. -/
def count (xs : List String) (a : String) : Nat := (xs.filter (· == a)).length

/-- The differences between two multisets of keys, as messages. -/
def multisetDiff (what : String) (want have_ : List String) : List String :=
  let keys := (want ++ have_).foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  keys.filterMap fun k =>
    let w := count want k
    let h := count have_ k
    if w == h then none else some s!"{what} {k}: the formula has {w}, the picture {h}"

end Spec

open Spec in
/-- The violations of A1–A4 in view A of a figure (A5 separately, as random
hints may place states anywhere). -/
def Fig.checkA (d : Fig) (o : DrawOpts := {}) : List String := Id.run do
  if d.hints.views == .b then return []
  let c := contentA d.shown
  let g := d.toDiagram (d.drawOpts o)
  let id (p : Nat) (x : String) := nodeId p x
  let mut out : List String := []
  -- A2 states
  let want := c.states.map fun (p, x) => id p x
  let have_ := g.nodes.toList.map (·.id)
  out := out ++ multisetDiff "A2 state" want have_
  -- A1 arrows and loops (with their composite), A4 colour of arrows
  let arrows := c.steps.filter fun s => s.drawn && s.src != s.tgt
  let loops := c.steps.filter fun s => s.drawn && s.src == s.tgt
  let drawnEdges := g.items.toList.filterMap fun | .edge e => some e | _ => none
  let drawnLoops := g.items.toList.filterMap fun | .loop a r cl _ => some (a, r, cl) | _ => none
  out := out ++ multisetDiff "A1 arrow"
    (arrows.map fun s => s!"{id s.panel s.src} → {id s.panel s.tgt} by {compPrint s.rel}")
    (drawnEdges.map fun e => s!"{e.a} → {e.b} by {compPrint e.rel}")
  out := out ++ multisetDiff "A1 loop"
    (loops.map fun s => s!"on {id s.panel s.src} by {compPrint s.rel}")
    (drawnLoops.map fun (a, r, _) => s!"on {a} by {compPrint r}")
  out := out ++ multisetDiff "A4 arrow"
    (arrows.map fun s => s!"{id s.panel s.src} → {id s.panel s.tgt} {if s.claim then "red" else "black"}")
    (drawnEdges.map fun e => s!"{e.a} → {e.b} {if e.concl then "red" else "black"}")
  -- A3 quantifiers: each quantifier with a bound occurrence is shown exactly
  -- once: by a notch on an arrow into a state it binds if there is one, else by
  -- a mark on the state
  let entering (i : Nat) := arrows.filter (·.tgtBinder == some i)
  let qs := (c.quantifiers.toList.zip (List.range c.quantifiers.size)).filter fun (_, i) =>
    c.occs.any (·.2.2 == some i)
  let notched := drawnEdges.filter (·.q.isSome)
  let marks := g.items.toList.filterMap fun | .qmark a _ _ _ => some ((a.splitOn "/").headD a) | _ => none
  out := out ++ multisetDiff "A3 notch into"
    ((qs.filter fun (_, i) => !(entering i).isEmpty).map (·.1.name))
    (notched.map fun e => ((e.b.splitOn "/").headD e.b))
  out := out ++ multisetDiff "A3 mark on"
    ((qs.filter fun (_, i) => (entering i).isEmpty).map (·.1.name))
    marks
  -- A4 marks: every state bound by `ex` is red in a claimed place, crossed under `not`
  for (p, x, b) in c.occs do
    if let some i := b then
      let q := c.quantifiers[i]!
      if q.ex then
        let n := g.find (id p x)
        if q.neg && !n.cross then out := out ++ [s!"A4 state {id p x}: bound by ex under not, but not crossed"]
        if !q.neg && q.claim && !n.new then out := out ++ [s!"A4 state {id p x}: bound by ex in a claimed place, but not red"]
  return out

/-- The violations of A5 in view A: states, names and arrows outside the canvas. -/
def Fig.checkCanvasA (d : Fig) (o : DrawOpts := {}) : List String := Id.run do
  if d.hints.views == .b then return []
  let g := d.toDiagram (d.drawOpts o)
  let inside (p : P) : Bool := p.x ≥ 0.0 && p.y ≥ 0.0 && p.x ≤ g.w.toFloat && p.y ≤ g.h.toFloat
  let mut out : List String := []
  for n in g.nodes do
    let c := P.ofInt n.x n.y
    for q in [c + ⟨NODE_R, 0.0⟩, c - ⟨NODE_R, 0.0⟩, c + ⟨0.0, NODE_R⟩, c - ⟨0.0, NODE_R⟩] do
      unless inside q do out := out ++ [s!"A5 state {n.id} at ({n.x},{n.y}) is outside the canvas {g.w}×{g.h}"]; break
    if !n.label.isEmpty && !inside (P.ofInt (n.x + n.lx) (n.y + n.ly)) then
      out := out ++ [s!"A5 the name of {n.id} is outside the canvas"]
  for it in g.items do
    if let .edge e := it then
      let A := g.find e.a; let B := g.find e.b
      let A := P.ofInt A.x A.y; let B := P.ofInt B.x B.y
      let ctrl := (A + B) * 0.5 + (B - A).unit.perp * e.bend
      if !(bezier A ctrl B).all inside then
        out := out ++ [s!"A5 the arrow {e.a} → {e.b} leaves the canvas"]
  return out

end FregeDiagrams
