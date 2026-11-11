/-
FregeDiagrams.Geometry: points, polylines and the operations the renderer applies
to them (Bézier sampling, trimming, splitting, offsetting, waving).

Every curve is a polyline (`Array P`); a quadratic Bézier is sampled to one.
The operations follow the Python generator this library was ported from,
step for step and in the same floating-point evaluation order, so that the
output matches exactly.
-/
import FregeDiagrams.Num

namespace FregeDiagrams

/-- A point (or vector) in SVG user coordinates: `y` grows downwards. -/
structure P where
  x : Float
  y : Float
deriving Inhabited

namespace P
instance : Add P := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩
instance : Sub P := ⟨fun p q => ⟨p.x - q.x, p.y - q.y⟩⟩
/-- Scalar multiple `p * k`. -/
instance : HMul P Float P := ⟨fun p k => ⟨p.x * k, p.y * k⟩⟩
/-- Euclidean length (Python's `math.hypot`). -/
def len (p : P) : Float := hypot p.x p.y
/-- The unit vector along `p`; the zero vector is divided by 1. -/
def unit (p : P) : P :=
  let n := p.len
  let n := if n == c0 then c1 else n
  ⟨p.x / n, p.y / n⟩
/-- `p` turned a quarter turn (clockwise on screen). -/
def perp (p : P) : P := ⟨-p.y, p.x⟩
/-- A point at integer grid coordinates. -/
def ofInt (x y : Int) : P := ⟨x.toF, y.toF⟩
end P

/-- A polyline: the common representation of every drawn curve. -/
abbrev Polyline := Array P

/-- The quadratic Bézier curve from `a` to `b` with control point `c`, sampled
at `n + 1` equally spaced parameter values. -/
def bezier (a c b : P) (n : Nat := 40) : Polyline := Id.run do
  let mut pts := #[]
  for i in [0:n+1] do
    let t := i.toF / n.toF
    let s := c1 - t
    let x := Float.pow s c2 * a.x + c2 * s * t * c.x + t * t * b.x
    let y := Float.pow s c2 * a.y + c2 * s * t * c.y + t * t * b.y
    pts := pts.push ⟨x, y⟩
  return pts

/-- The lengths of the segments of a polyline. -/
def segLens (pts : Polyline) : List Float :=
  (List.range (pts.size - 1)).map fun i => (pts[i+1]! - pts[i]!).len

/-- Arc length of a polyline (summed as Python's `sum` does). -/
def arclen (pts : Polyline) : Float := pySum (segLens pts)

/-- Cut arc length `d` from the start of a polyline. -/
def cutStart (p : Polyline) (d : Float) : Polyline := Id.run do
  let mut acc := c0
  for i in [0:p.size - 1] do
    let seg := (p[i+1]! - p[i]!).len
    if acc + seg ≥ d then
      let t := if seg != c0 then (d - acc) / seg else c0
      let q := p[i]! + (p[i+1]! - p[i]!) * t
      return #[q] ++ p.extract (i + 1) p.size
    acc := acc + seg
  return p.extract (p.size - 1) p.size

/-- Cut length `d0` from the start and `d1` from the end of a polyline (used to
stop an arrow short of the dots it joins). -/
def trim (pts : Polyline) (d0 d1 : Float) : Polyline :=
  (cutStart (cutStart pts d0).reverse d1).reverse

/-- Split a polyline at the given increasing fractions of its length; a
composite relation such as `≤;R;≤` is drawn as one stretch per piece. -/
def split (pts : Polyline) (fracs : List Float) : Array Polyline := Id.run do
  let total := arclen pts
  let cuts := (fracs.map (· * total)).toArray
  let mut pieces : Array Polyline := #[]
  let mut cur : Polyline := #[pts[0]!]
  let mut acc := c0
  let mut ci := 0
  for i in [0:pts.size - 1] do
    let a := pts[i]!
    let b := pts[i+1]!
    let seg := (b - a).len
    while ci < cuts.size && acc + seg ≥ cuts[ci]! do
      let t := if seg != c0 then (cuts[ci]! - acc) / seg else c0
      let q := a + (b - a) * t
      cur := cur.push q
      pieces := pieces.push cur
      cur := #[q]
      ci := ci + 1
    cur := cur.push b
    acc := acc + seg
  return pieces.push cur

/-- The unit normal at vertex `i` (from the chord of its neighbours). -/
def normalAt (pts : Polyline) (i : Nat) : P :=
  let a := pts[if i == 0 then 0 else i - 1]!
  let b := pts[min (i + 1) (pts.size - 1)]!
  (b - a).perp.unit

/-- The parallel polyline at signed distance `d` (for `=` and the dotted twin). -/
def offset (pts : Polyline) (d : Float) : Polyline :=
  pts.mapIdx fun i p => p + normalAt pts i * d

/-- A sine wave along the polyline, tapered to zero at both ends: the line
style of `⇝`. -/
def wavy (pts : Polyline) (amp : Float := 2.6) (wavelength : Float := 9.0) : Polyline := Id.run do
  let total := arclen pts
  if total == c0 then return pts
  let mut out := #[]
  let mut acc := c0
  for i in [0:pts.size] do
    if i != 0 then acc := acc + (pts[i]! - pts[i-1]!).len
    let n := normalAt pts i
    let env := min (min c1 (acc / c6)) ((total - acc) / c10)
    out := out.push (pts[i]! + n * (amp * env * Float.sin (c2 * pi * acc / wavelength)))
  return out

/-- The point and unit direction at arc length `s` along a polyline. -/
def pointAt (pts : Polyline) (s : Float) : P × P := Id.run do
  let mut acc := c0
  for i in [0:pts.size - 1] do
    let seg := (pts[i+1]! - pts[i]!).len
    if acc + seg ≥ s || i == pts.size - 2 then
      let t := if seg != c0 then (s - acc) / seg else c0
      return (pts[i]! + (pts[i+1]! - pts[i]!) * t, (pts[i+1]! - pts[i]!).unit)
    acc := acc + seg
  return (default, default)

/-- SVG `points` attribute: coordinates to one decimal. -/
def polyStr (pts : Polyline) : String :=
  " ".intercalate (pts.toList.map fun p => fmt1 p.x ++ "," ++ fmt1 p.y)

end FregeDiagrams
