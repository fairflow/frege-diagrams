/-
FregeDiagrams.Test: build-time tests of the syntax.

* every figure of `exampleSource` parses, is well formed, and round-trips;
* `fig_of%` gives the same figure as parsing at run time;
* `parse (print d) = .ok d` on 2000 pseudo-random well-formed figures
  (a fixed linear congruential generator, so the test is reproducible).

`ParsePrint` itself is not proved.
-/
import FregeDiagrams.View
import FregeDiagrams.Syntax
import FregeDiagrams.Examples
import FregeDiagrams.Elab
import FregeDiagrams.Latex
import FregeDiagrams.Edit
import FregeDiagrams.Lint

namespace FregeDiagrams.Test

def exampleFigs : List Fig := (parseFile exampleSource).toOption.getD []

#guard (parseFile exampleSource).toOption.isSome
#guard exampleFigs.length == 11
#guard exampleFigs.all Fig.WellFormed
#guard exampleFigs.all Fig.roundTrips
-- the printed text is a fixed point of print ∘ parse
#guard exampleFigs.all fun d => (Fig.parse d.print).toOption.map Fig.print == some d.print

/-! ## Pseudo-random figures -/

abbrev G := StateM Nat

def rand (n : Nat) : G Nat := do
  let s := (1103515245 * (← get) + 12345) % 2147483648
  set s
  return (s / 65536) % (max n 1)

def pick {α} [Inhabited α] (xs : List α) : G α := do return xs[← rand xs.length]!

def names : List String := ["s", "t", "u", "x′", "t₁", "y", "s'", "ab_2", "σ", "Ωτ₂′"]
def texts : List String := ["inf(u)", "R°(u) = ∅", "", "a, b & c | d {x}", "then"]
def rels : List Rel := [.le, .sqle, .R, .Rinf, .reach, .eq, .ne]

def genSt : G St := do return { name := ← pick names, inf := (← rand 2) == 0 }

def genComp : G Composite := do
  let n := 1 + (← rand 3)
  (List.range n).mapM fun _ => pick rels

def genList {α} (lo hi : Nat) (g : G α) : G (List α) := do
  let n := lo + (← rand (hi - lo + 1))
  (List.range n).mapM fun _ => g

def genForm : Nat → G Form
  | 0 => do
    let st ← genSt
    let steps ← genList 0 3 (do return (← genComp, ← genSt))
    return .chain st steps
  | d + 1 => do
    match ← rand 9 with
    | 0 => return .text (← pick texts) none
    | 1 => return .text (← pick texts) (some (← genForm d))
    | 2 => return .all (← pick names) (← genForm d)
    | 3 => return .ex (← pick names) (← genForm d)
    | 4 => return .not (← genForm d)
    | 5 => return .imp (← genList 1 3 (genForm d)) (← genForm d)
    | 6 => return .and (← genList 2 3 (genForm d))
    | 7 => return .or (← genList 2 3 (genForm d))
    | _ => genForm 0

def genInt : G Int := do return (← rand 400 : Nat) - (200 : Int)

def genKey : G Key := do return { name := ← pick names, panel := 1 + (← rand 3) }

def genHints : G Hints := do
  let size ← if (← rand 2) == 0 then pure none else pure (some (← rand 500, ← rand 500))
  let views ← pick [Views.both, .a, .b]
  let nodes ← genList 0 3 do
    let label ← if (← rand 2) == 0 then pure none else pure (some (← genInt, ← genInt))
    return { key := ← genKey, x := ← genInt, y := ← genInt, label : NodeHint }
  let edges ← genList 0 3 do
    let opt {α} (g : G α) : G (Option α) := do if (← rand 2) == 0 then pure none else some <$> g
    return { src := ← pick names, tgt := ← pick names, occ := 1 + (← rand 3),
             panel := 1 + (← rand 3), bend := ← opt genInt, side := ← opt (do return (← rand 2) == 0),
             at_ := ← opt (rand 250) : EdgeHint }
  let loops ← genList 0 2 do return { key := ← genKey, angle := ← genInt : LoopHint }
  let notches ← genList 0 2 do return (← pick names, (← rand 2) == 0)
  let routes ← genList 0 2 do
    let ps ← genList 1 3 (genList 2 4 (do return (← genInt, ← genInt)))
    return (← pick names, ps)
  let texts ← genList 0 2 do
    return { x := ← genInt, y := ← genInt, s := ← pick texts, color := ← pick [Color.black, .red, .grey],
             size := ← rand 30, middle := (← rand 2) == 0, italic := (← rand 2) == 0 : TextHint }
  let nameDy ← (do if (← rand 2) == 0 then pure none else some <$> genInt : G (Option Int))
  return { size, views, nodes, edges, loops, texts, nameDy, notches, routes }

def genFig : G Fig := do
  return { name := ← pick ["f", "ex_trans", "x1"], hints := ← genHints, body := ← genForm (← rand 5) }

def randomFigs (n seed : Nat) : List Fig := ((List.range n).mapM fun _ => genFig).run' seed

#guard (randomFigs 2000 2026).all Fig.WellFormed
#guard (randomFigs 2000 2026).all Fig.roundTrips

/-! ## The LaTeX formulas (golden) -/

def latexOf (n : String) : String := ((exampleFigs.find? (·.name == n)).map Fig.toLatex).getD ""

#guard latexOf "ex_trans" == "\\forall u.\\ \\forall t.\\ s\\le u\\ \\imp\\ (u\\le t\\ \\imp\\ s\\le t)"
#guard latexOf "ex_serial" == "\\forall t.\\ s\\le t\\ \\imp\\ \\exists u.\\ t\\mathrel{R^{\\circ}} u"
#guard latexOf "ex_composite" == "\\forall y.\\ s\\Y y\\ \\imp\\ y\\mathrel{R} y \\wedge s\\reach y"
#guard latexOf "ex_or" == "(\\exists t.\\ s\\mathrel{R^{\\circ}} t) \\vee (\\neg \\exists u.\\ s\\sq u\\neq s)"
#guard latexOf "ex_text" == "\\forall u\\sqsupseteq s.\\ (\\neg \\exists x.\\ u\\mathrel{R} x)\\ \\imp\\ \\exists t.\\ u\\le t \\wedge s\\le t"
#guard latexOf "legend_conj" == "\\text{A} \\wedge \\text{B}\\ \\imp\\ \\text{C}"

/-! ## The elaborator -/

#guard (fig_of% exampleSource "ex_trans").print == ((exampleFigs.find? (·.name == "ex_trans")).map Fig.print).getD ""
#guard (fig_of% "fig a = s <= t°" "a").print == "fig a =\n  s <= t°\n"

end FregeDiagrams.Test

/-! ## The Steiner solver

A star: centre 0 joined to 1, 2, 3 at cost 2 each, and a path 1–2–3 at
cost 3.5 per edge.  The minimum tree joining 1, 2, 3 is the star (cost 6,
three edges, through the non-terminal 0), not the path (cost 7). -/

open FregeDiagrams.Route in
def starGraph : Graph :=
  let e : List (Nat × Nat × Float) := [(0,1,2.0), (0,2,2.0), (0,3,2.0), (1,2,3.5), (2,3,3.5)]
  { adj := (List.range 4).toArray.map fun v =>
      (e.filterMap fun (a, b, w) => if a == v then some (b, w) else if b == v then some (a, w) else none).toArray }

open FregeDiagrams.Route in
#guard (steiner starGraph #[2, 3] 1).map (·.1) == some 6.0
open FregeDiagrams.Route in
#guard ((steiner starGraph #[2, 3] 1).map (·.2.size)) == some 3

/-! ## The layout checks, on constructed cases -/

open FregeDiagrams FregeDiagrams.Route in
/-- A state at the origin with its name `t` just above it: fine alone; cut
off by a link running between them; far if put 30 away. -/
def nameCases : List Nat :=
  let sc : Scene := { labels := #[{ pos := ⟨0.0, 0.0⟩, text := "t", color := RED, looped := false }] }
  let near : Shape := .text ⟨0.0, -9.0⟩ "t" RED 12 "middle"
  let far : Shape := .text ⟨0.0, -40.0⟩ "t" RED 12 "middle"
  let link : Polyline := #[⟨-20.0, -6.0⟩, ⟨20.0, -6.0⟩]
  [(nameViolations sc #[near] #[]).size, (nameViolations sc #[near] #[link]).size,
   (nameViolations sc #[far] #[]).size]
#guard nameCases == [0, 1, 1]

open FregeDiagrams FregeDiagrams.Route in
/-- Two binders, the second inside the first's scope, each with a vertical
link to the right of a tree occupying `[0, 20] × [0, 50]`: fine when the
outer one is further out, a violation when the inner one is. -/
def nestCases : List Nat :=
  let outer : Binder := { name := "x", notch := ⟨0.0, 0.0⟩, dir := -1.0, hw := 5.0, tgts := #[] }
  let inner : Binder := { name := "y", notch := ⟨5.0, 0.0⟩, dir := -1.0, hw := 5.0, tgts := #[],
                          depth := 1, encl := [⟨0.0, 0.0⟩] }
  let col (x : Float) : Routed := { polys := #[#[⟨x, 0.0⟩, ⟨x, 50.0⟩]] }
  let sc : Scene := { cboxes := #[(0.0, 0.0, 20.0, 50.0)] }
  [(nestingViolations sc #[outer, inner] #[col 40.0, col 30.0]).size,
   (nestingViolations sc #[outer, inner] #[col 30.0, col 40.0]).size]
#guard nestCases == [0, 1]
/-! ## Error positions (line, column; columns count characters, from 1) -/

def errOf (s : String) : String := match FregeDiagrams.parseFile s with | .error e => e | .ok _ => "ok"

#guard errOf "fig a =\n  all y. if s <= y ex t. t" ==
  "line 2, column 20: expected 'then', at: ex t . t"
#guard errOf "fig a [edge s>y at 0.175] = s" ==
  "line 1, column 20: a decimal has at most two fractional digits"
#guard errOf "fig a = s′ <= t\n  fig" == "line 2, column 6: expected a name, at: end of input"
#guard errOf "fig a = s $ t" == "line 1, column 11: unexpected character '$'"
#guard errOf "fig a = (s & t" == "line 1, column 15: expected ')', at: end of input"

/-! ## Edits keep the rest of the text (`FregeDiagrams/Edit.lean`) -/

def editSrc := "-- c\nfig a [s@(1,2),  -- keep\n  edge s>t bend 3] =\n  s <= t\nfig b = t R s\n"
def editRun (e : Except String String) : String := match e with | .ok s => s | .error e => "ERROR " ++ e

-- replace one hint: the comment and the line break stay
#guard editRun (FregeDiagrams.applyEdit editSrc "a" (.node { key := { name := "s" }, x := 5, y := 6, label := some (3, -4) })) ==
  "-- c\nfig a [s@(5,6) label (3,-4),  -- keep\n  edge s>t bend 3] =\n  s <= t\nfig b = t R s\n"
-- add a hint to a figure with none: brackets appear
#guard editRun (FregeDiagrams.applyEdit editSrc "b" (.edge { src := "t", tgt := "s", bend := some 4 })) ==
  "-- c\nfig a [s@(1,2),  -- keep\n  edge s>t bend 3] =\n  s <= t\nfig b [edge t>s bend 4] = t R s\n"
-- an arrow hint with nothing in it is removed, with its comma
#guard editRun (FregeDiagrams.applyEdit editSrc "a" (.edge { src := "s", tgt := "t" })) ==
  "-- c\nfig a [s@(1,2)] =\n  s <= t\nfig b = t R s\n"
-- adding and removing the only hint gives the text back
#guard editRun (do
    let s ← FregeDiagrams.applyEdit editSrc "b" (.edge { src := "t", tgt := "s", bend := some 4 })
    FregeDiagrams.applyEdit s "b" (.edge { src := "t", tgt := "s" })) == editSrc
-- appended after the last hint
#guard editRun (FregeDiagrams.applyEdit editSrc "a" (.nameDy (some 3))) ==
  "-- c\nfig a [s@(1,2),  -- keep\n  edge s>t bend 3, namedy 3] =\n  s <= t\nfig b = t R s\n"
#guard editRun (FregeDiagrams.applyEdit editSrc "c" (.nameDy (some 3))) == "ERROR no figure c"
-- every example figure: moving each hinted state by (1,1) re-parses to the edited figure
#guard FregeDiagrams.Test.exampleFigs.all fun f => f.hints.nodes.all fun n =>
  (FregeDiagrams.applyEdit FregeDiagrams.exampleSource f.name (.node { n with x := n.x + 1, y := n.y + 1 })).toOption.isSome

/-! ## Checks of hints and of view A (`FregeDiagrams/Lint.lean`) -/

def lintSrc : String := "
fig rev [s@(30,40), t@(150,40), edge t>s#2 bend 10, loop t 90, z@(1,1)] = all t. if s <= t then t <= s
fig mixed [size (300,100), s@(30,60), y@(250,60), edge s>y at 0.50] = all y. s <=;R y
fig same [s@(30,60), y@(250,60), edge s>y at 0.80] = all y. if s <=;R y then y R° y
fig near [size (300,100), s@(30,60), t@(36,64), u@(200,60) label (0,-58)] = all t. all u. if s <= t then t R u
fig out [size (100,60), s@(30,40), y@(130,40)] = all y. if s <= y then y R y
fig nonotch [s@(30,60), t@(250,60), edge s>t side +] = s <= t
"

def lintOf (n : String) : List (String × String) :=
  match (FregeDiagrams.parseFile lintSrc).toOption.bind (·.find? (·.name == n)) with
  | some f => f.lint.toList.map fun l =>
      ((match l.sev with | .error => "E" | .warning => "W"), (l.msg.splitOn " ").take 3 |> " ".intercalate)
  | none => [("missing", n)]

-- unmatched hints: a state, an arrow (#2 of t>s), a loop
#guard lintOf "rev" == [("E", "The hint z@(1,1)"), ("E", "The hint edge"), ("E", "The hint loop")]
-- ∀y on a conclusion arrow: intermediate ∃, notch at 0.50 is past the first bead of two
#guard lintOf "mixed" == [("E", "The ∀ notch")]
-- ∀y on a hypothesis arrow: intermediate ∀ too, the place is free
#guard lintOf "same" == []
#guard lintOf "near" == [("W", "The states s"), ("W", "The name of")]
#guard lintOf "out" == [("E", "The state y")]
#guard lintOf "nonotch" == [("W", "The arrow s→t")]

/-- Apply every offered fix of a figure, one at a time, then check again. -/
partial def fixAll (src : String) (n : String) (fuel : Nat := 10) : String :=
  match fuel, (FregeDiagrams.parseFile src).toOption.bind (·.find? (·.name == n)) with
  | fuel + 1, some f =>
    match f.lint.toList.findSome? (·.fix) with
    | some e => match FregeDiagrams.applyEdit src n e with
      | .ok s => fixAll s n fuel
      | .error _ => src
    | none => src
  | _, _ => src

-- every fix removes its problem: after the fixes only unfixable items are left
#guard ["rev", "mixed", "nonotch"].all fun n =>
  let s := fixAll lintSrc n
  ((FregeDiagrams.parseFile s).toOption.bind (·.find? (·.name == n))).map (·.lint.size) == some 0
-- the notch fix puts it in the middle of the first stretch
#guard ((fixAll lintSrc "mixed").splitOn "edge s>y at 0.25").length == 2

/-! ## Greek letters in names -/

#guard FregeDiagrams.isIdent "σ" && FregeDiagrams.isIdent "τ₁′" && FregeDiagrams.isIdent "xα"
#guard !FregeDiagrams.isIdent "°" && !FregeDiagrams.isIdent "ϕ"   -- ϕ (U+03D5) is outside the ranges
#guard (FregeDiagrams.Fig.parse "fig g = all σ. if s <= σ then σ R τ₁").toOption.map (·.roundTrips) == some true
#guard FregeDiagrams.latexName "σ₁" == "{\\sigma}_1"
#guard FregeDiagrams.latexName "Ω′" == "{\\Omega}'"
#guard FregeDiagrams.latexName "Ακ" == "A{\\kappa}"
#guard FregeDiagrams.morseOf 'σ' == "..." && FregeDiagrams.morseOf 'Ω' == ".--"
-- distinct names keep distinct link patterns
#guard FregeDiagrams.morseDash "α" != FregeDiagrams.morseDash "β"

/-! ## Fixed notch orientation in view B (`notch NAME up|down`) -/

#guard FregeDiagrams.notchUp { fixedNotches := [("t", false)] } .all "t" == false
-- a fixed notch is not turned over by the router's choice
#guard FregeDiagrams.notchUp { fixedNotches := [("u", true)], flips := ["u"] } .ex "u" == true
#guard FregeDiagrams.notchUp { flips := ["u"] } .ex "u" == true
#guard (FregeDiagrams.Fig.parse "fig n [notch t down] = all t. s <= t").toOption.map (·.hints.notches) == some [("t", false)]
-- editing: fix, change, release
#guard editRun (FregeDiagrams.applyEdit "fig n = all t. s <= t\n" "n" (.notch "t" (some false))) == "fig n [notch t down] = all t. s <= t\n"
#guard editRun (FregeDiagrams.applyEdit "fig n [notch t down] = all t. s <= t\n" "n" (.notch "t" (some true))) == "fig n [notch t up] = all t. s <= t\n"
#guard editRun (FregeDiagrams.applyEdit "fig n [notch t down] = all t. s <= t\n" "n" (.notch "t" none)) == "fig n = all t. s <= t\n"
-- a notch hint for a name no quantifier binds is reported, with a fix
#guard ((FregeDiagrams.Fig.parse "fig n [notch zz up] = all t. s <= t").toOption.map (·.lint.size)) == some 1
-- the fixed side reaches the drawing: view B of t fixed down differs from the default
#guard (({ name := "n", tree := (FregeDiagrams.Fig.parse "fig n = all t. s <= t").toOption.get!.body.toTree : FregeDiagrams.TreeDiagram }).svg {} !=
        ({ name := "n", tree := (FregeDiagrams.Fig.parse "fig n = all t. s <= t").toOption.get!.body.toTree : FregeDiagrams.TreeDiagram }).svg { fixedNotches := [("t", false)] })

/-! ## Pinned routes (`route NAME …`) -/

open FregeDiagrams FregeDiagrams.Route in
/-- A binder with its notch at the origin and one bound state at (100, 50):
a pin ending at the notch and at the top of the state (rounded) fits and is
snapped onto the terminals; moved by 40 it does not fit. -/
def pinCases : List Bool :=
  let b : Binder := { name := "x", notch := ⟨0.0, 0.0⟩, dir := -1.0, hw := 5.0, tgts := #[⟨100.0, 50.0⟩] }
  let pin : Array Polyline := #[#[⟨0.0, 0.0⟩, ⟨0.0, -20.0⟩, ⟨100.0, -20.0⟩, ⟨100.0, 45.0⟩]]
  let moved : Array Polyline := pin.map (·.map fun p => ⟨p.x + 40.0, p.y⟩)
  let diagonal : Array Polyline := #[#[⟨0.0, 0.0⟩, ⟨100.0, 45.0⟩]]
  [(fitPin b pin).isSome,
   ((fitPin b pin).map fun r => decide ((r.polys[0]!.back! - ⟨100.0, 50.0 - (NODE_R + 1.0)⟩).len < 0.01)) == some true,
   (fitPin b moved).isNone,
   (fitPin b diagonal).isNone]
#guard pinCases == [true, true, true, true]
#guard (FregeDiagrams.Fig.parse "fig r [route x (0,0) (0,-20) (100,-20); (100,-20) (100,45)] = all x. s <= x").toOption.map (·.hints.routes) ==
  some [("x", [[(0, 0), (0, -20), (100, -20)], [(100, -20), (100, 45)]])]
#guard editRun (FregeDiagrams.applyEdit "fig r = all x. s <= x\n" "r" (.route "x" (some [[(0, 0), (0, 9)]]))) ==
  "fig r [route x (0,0) (0,9)] = all x. s <= x\n"
#guard editRun (FregeDiagrams.applyEdit "fig r [route x (0,0) (0,9)] = all x. s <= x\n" "r" (.route "x" none)) == "fig r = all x. s <= x\n"
-- a route for an unbound name, and a diagonal segment, are reported with a fix
#guard ((FregeDiagrams.Fig.parse "fig r [route zz (0,0) (0,9)] = all x. s <= x").toOption.map (·.lint.size)) == some 1
#guard ((FregeDiagrams.Fig.parse "fig r [route x (0,0) (5,9)] = all x. s <= x").toOption.map (·.lint.size)) == some 1
