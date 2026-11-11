/-
FregeDiagrams.Legend: the key to view A.

`legend` is a key to the drawing conventions of view A (the frame picture):
the arrow styles of the relations, hollow (infallible), red (conclusion) and
crossed states, and the two quantifier notches.  It is not a formula, so it
is drawn directly as a `Diagram` rather than written in the figure language.
`lake exe framediag` writes it as `legend.svg`.
-/
import FregeDiagrams.Frame

namespace FregeDiagrams

open Rel Quant in
/-- The legend of view A: a key to the drawing conventions, not a formula. -/
def legend : Diagram := Id.run do
  let mut g : Diagram := { name := "legend", w := 720, h := 252 }
  let rows : List (Composite × String) :=
    [([le], "a ≤ b"), ([R], "a R b"), ([reach], "a ⇝ b"), ([sqle, R], "a (⊑;R) b: bead = infallible middle"), ([eq], "a = b"),
     ([named "L" true], "a L b: a labelled relation")]
  for (i, (rel, lab)) in (List.range rows.length).zip rows do
    let y : Int := 22 + 38 * i
    g := g.node s!"a{i}" 20 y (label := "") |>.node s!"b{i}" 110 y (label := "")
    g := g.edge { a := s!"a{i}", b := s!"b{i}", rel, head := rel != [eq] && rel != [named "L" false] }
    g := g.text 122 (y + 4) lab
  -- (label, edge template, state flags inf/new/cross)
  let rows2 : List (String × Edge × Bool × Bool × Bool) :=
    [("hollow: infallible (dashed into hollow is ⊑)", { a := "", b := "", rel := [le] }, true, false, false),
     ("red: conclusion", { a := "", b := "", rel := [R], concl := true }, false, false, false),
     ("⊓ notch: for all successors (here u)",
        { a := "", b := "", rel := [R], q := some all, qvar := some "u" }, true, false, false),
     ("∨ notch: there is a successor (here t)",
        { a := "", b := "", rel := [R], concl := true, q := some ex, qvar := some "t" }, false, true, false),
     ("crossed state: no such state", { a := "", b := "", rel := [R], concl := true }, true, false, true)]
  for (i, (lab, e, inf, new, cross)) in (List.range rows2.length).zip rows2 do
    let y : Int := 22 + 38 * i
    g := g.node s!"c{i}" 360 y (label := "") |>.node s!"d{i}" 460 y (label := "") (inf := inf) (new := new) (cross := cross)
    g := g.edge { e with a := s!"c{i}", b := s!"d{i}" }
    g := g.text 472 (y + 4) lab
  return g

end FregeDiagrams
