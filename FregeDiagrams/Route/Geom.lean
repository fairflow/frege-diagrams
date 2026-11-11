/-
FregeDiagrams.Route.Geom: segment geometry for the link router.

Float literals in compiled code are rebuilt (`Float.ofScientific`) at every
use, so the constants of the inner loops are top-level definitions.
-/
import FregeDiagrams.Geometry

namespace FregeDiagrams.Route

def fZero : Float := 0.0
def fOne : Float := 1.0
def fEps : Float := 1.0e-6
def fBig : Float := 1.0e30
def fHalf : Float := 0.5

/-- An axis-aligned box `(x0, y0, x1, y1)`. -/
abbrev Box := Float × Float × Float × Float

def orient (a b c : P) : Float := (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

/-- Where two segments cross properly (not at an end): the parameters along
each. -/
def crossAt (p1 p2 q1 q2 : P) : Option (Float × Float) :=
  let d1 := orient q1 q2 p1; let d2 := orient q1 q2 p2
  let d3 := orient p1 p2 q1; let d4 := orient p1 p2 q2
  if ((d1 > fEps && d2 < -fEps) || (d1 < -fEps && d2 > fEps)) &&
     ((d3 > fEps && d4 < -fEps) || (d3 < -fEps && d4 > fEps))
  then some (d1 / (d1 - d2), d3 / (d3 - d4)) else none

def bbox (a : Polyline) : Box :=
  a.foldl (fun (x0, y0, x1, y1) p => (min x0 p.x, min y0 p.y, max x1 p.x, max y1 p.y))
    (fBig, fBig, -fBig, -fBig)

def boxesMeet (a b : Box) : Bool :=
  let (ax0, ay0, ax1, ay1) := a
  let (bx0, by0, bx1, by1) := b
  !(ax1 < bx0 || bx1 < ax0 || ay1 < by0 || by1 < ay0)

/-- The proper crossings of two polylines, as `(parameter along a, parameter
along b)`; a parameter is a segment index plus a fraction. -/
def crossings (a b : Polyline) : Array (Float × Float) := Id.run do
  let mut out := #[]
  if !boxesMeet (bbox a) (bbox b) then return out
  for i in [0:a.size - 1] do
    for j in [0:b.size - 1] do
      if let some (s, t) := crossAt a[i]! a[i+1]! b[j]! b[j+1]! then
        out := out.push (i.toFloat + s, j.toFloat + t)
  return out

/-- The number of proper crossings of a segment with a polyline whose box is
given. -/
def segCrossCount (a b : P) (c : Polyline) (cb : Box) : Nat := Id.run do
  if !boxesMeet (min a.x b.x, min a.y b.y, max a.x b.x, max a.y b.y) cb then return 0
  let mut n := 0
  for j in [0:c.size - 1] do
    if (crossAt a b c[j]! c[j+1]!).isSome then n := n + 1
  return n

/-- Distance from a point to a segment. -/
def segDist (p a b : P) : Float :=
  let d := b - a
  let l2 := d.x * d.x + d.y * d.y
  let t := if l2 == fZero then fZero
    else max fZero (min fOne (((p.x - a.x) * d.x + (p.y - a.y) * d.y) / l2))
  (p - (a + d * t)).len

/-- Distance between two segments. -/
def segSegDist (a b c d : P) : Float :=
  if (crossAt a b c d).isSome then fZero
  else min (min (segDist a c d) (segDist b c d)) (min (segDist c a b) (segDist d a b))

/-- Does an axis-parallel segment meet the inside of a box? -/
def segMeetsBox (a b : P) (bx : Box) : Bool :=
  let (x0, y0, x1, y1) := bx
  if a.y == b.y then y0 < a.y && a.y < y1 && min a.x b.x < x1 && x0 < max a.x b.x
  else if a.x == b.x then x0 < a.x && a.x < x1 && min a.y b.y < y1 && y0 < max a.y b.y
  else
    -- not axis-parallel: sample
    (List.range 13).any fun k =>
      let p := a + (b - a) * (k.toFloat / 12.0)
      x0 < p.x && p.x < x1 && y0 < p.y && p.y < y1

/-- Do two segments run on top of each other: parallel and axis-aligned,
closer than `tol`, sharing more than `tol` of their length? -/
def segsOverlap (p q r s : P) (tol : Float) : Bool :=
  let shared (u0 u1 v0 v1 : Float) := min (max u0 u1) (max v0 v1) - max (min u0 u1) (min v0 v1)
  (p.y == q.y && r.y == s.y && (p.y - r.y).abs < tol && shared p.x q.x r.x s.x > tol) ||
  (p.x == q.x && r.x == s.x && (p.x - r.x).abs < tol && shared p.y q.y r.y s.y > tol)

/-- Point at parameter `s` (segment index plus fraction) of a polyline. -/
def atParam (pts : Polyline) (s : Float) : P :=
  let i := min (s.floor.toUInt64.toNat) (pts.size - 2)
  pts[i]! + (pts[i+1]! - pts[i]!) * (s - i.toFloat)

/-- The piece of a polyline between two parameters, in the order given. -/
def subPath (pts : Polyline) (s0 s1 : Float) : Polyline := Id.run do
  let lo := min s0 s1; let hi := max s0 s1
  let mut out := #[atParam pts lo]
  for k in [0:pts.size] do
    if lo < k.toFloat && k.toFloat < hi then out := out.push pts[k]!
  out := out.push (atParam pts hi)
  return if s0 ≤ s1 then out else out.reverse

/-- Is a point inside a polygon (even-odd rule)? -/
def inPoly (poly : Polyline) (p : P) : Bool := Id.run do
  let mut inside := false
  let n := poly.size
  for i in [0:n] do
    let a := poly[i]!; let b := poly[(i + n - 1) % n]!
    if (a.y > p.y) != (b.y > p.y) && p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x then
      inside := !inside
  return inside

/-- Drop the interior points of straight runs. -/
def simplify (pts : Polyline) : Polyline := Id.run do
  if pts.size ≤ 2 then return pts
  let mut out := #[pts[0]!]
  for i in [1:pts.size - 1] do
    let a := out.back!; let b := pts[i]!; let c := pts[i+1]!
    if (orient a b c).abs > fEps then out := out.push b
  return out.push pts.back!

end FregeDiagrams.Route
