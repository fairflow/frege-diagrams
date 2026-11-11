/-
FregeDiagrams.Num: the floating-point primitives on which the SVG output depends.

The Python generator from which this library was ported (not included) is
the reference.  To make the Lean output byte-identical, three Python
behaviours are reproduced exactly rather than approximated:

* `f"{x:.1f}"`: correctly rounded fixed-point output (round half to even on
  the exact binary value), computed here with integer arithmetic;
* `repr(x)` for a float: the shortest decimal that reads back as `x`;
* `math.hypot` and `sum` of floats: CPython 3.12 computes `hypot` by a
  compensated algorithm (correctly rounded in practice) and `sum` by
  Neumaier summation.  Plain `sqrt (x*x + y*y)` differs from `math.hypot` in
  the last bit in about 15% of random calls; for the 17 pictures of the
  original figure set it happens not to change any printed digit (checked
  2026-11-07), so the exact
  port is insurance for other diagrams rather than a necessity for these.
-/

/-- A small natural number as a float.  (Core's `Nat.toFloat` goes through
`OfScientific` and big-number arithmetic: it was the largest single cost of
rendering before this replacement.)  Exact below `2^53`. -/
def Nat.toF (n : Nat) : Float := n.toUInt64.toFloat

/-- A small integer as a float, as `Nat.toF`. -/
def Int.toF (i : Int) : Float := if i ≥ 0 then i.toNat.toF else -(i.natAbs.toF)

namespace FregeDiagrams

/-! Float literals used in inner loops.  The Lean 4.31 compiler does not hoist
a literal such as `2.0` out of a function body: each evaluation calls
`Float.ofScientific` (big-number arithmetic).  Top-level constants are
computed once.  Profiling showed this was about two thirds of render time. -/
def c0 : Float := 0.0
def c1 : Float := 1.0
def c2 : Float := 2.0
def c6 : Float := 6.0
def c10 : Float := 10.0
def cHalf : Float := 0.5
def cMillion : Float := 1.0e6
def cMicro : Float := 1.0e-6
/-- Veltkamp's splitting constant `2^27 + 1`. -/
def cSplit : Float := 134217729.0

/-- `10^k` for `k ≤ 20`, computed once. -/
def pow10 : Array Nat := (List.range 21).toArray.map (10 ^ ·)

/-- The exact value of a finite float: `(negative?, m, e)` with `|x| = m * 2^e`. -/
def Float.decompose (x : Float) : Bool × Nat × Int :=
  let b := x.toBits
  let neg := (b >>> 63) == 1
  let ex := ((b >>> 52) &&& 0x7FF).toNat
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0 then (neg, frac, -1074) else (neg, frac + 4503599627370496, (ex : Int) - 1075)

/-- `round(m * 2^e * 10^k)`, rounding half to even, in exact arithmetic. -/
def roundScaled (m : Nat) (e : Int) (k : Nat) : Nat :=
  let num := m * pow10[k]!
  if e ≥ 0 then num <<< e.toNat
  else
    let den := 1 <<< (-e).toNat
    let q := num / den
    let r := num % den
    if 2 * r > den then q + 1
    else if 2 * r < den then q
    else if q % 2 == 0 then q else q + 1

/-- Render the natural number `n / 10^k` with exactly `k` decimals. -/
def showScaled (neg : Bool) (n k : Nat) : String :=
  let ip := n / pow10[k]!
  let fp := toString (n % pow10[k]!)
  let fp := String.ofList (List.replicate (k - fp.length) '0') ++ fp
  (if neg then "-" else "") ++ toString ip ++ (if k == 0 then "" else "." ++ fp)

/-- Python's `f"{x:.{k}f}"` for finite `x` (including the sign of `-0.0`). -/
def fixed (x : Float) (k : Nat) : String :=
  let (neg, m, e) := Float.decompose x
  showScaled neg (roundScaled m e k) k

/-- Python's `f"{x:.1f}"`: one decimal, correctly rounded.

Fast path: for `|10x| < 10^6` the float product `10x` is within `1.2e-10` of
the exact value, so unless it lies within `1e-6` of a rounding boundary
(a half-integer) its nearest integer is the exact answer.  Otherwise the
exact integer computation of `fixed` decides. -/
def fmt1 (x : Float) : String :=
  let y := x.abs * c10
  let fl := y.floor
  let fr := y - fl
  if y < cMillion && (fr - cHalf).abs > cMicro then
    let n := fl.toUInt64.toNat + (if fr > cHalf then 1 else 0)
    (if (x.toBits >>> 63) == 1 then "-" else "") ++ toString (n / 10) ++ "." ++ toString (n % 10)
  else fixed x 1

/-- Python's `repr(x)` for a float of moderate size (`1e-4 ≤ |x| < 1e16`, or
zero): the shortest fixed-point decimal that reads back as `x`, with at least
one decimal (`2.0`, `1.2000000000000002`).  Outside that range Python switches
to scientific notation; this function does not (no diagram uses such values). -/
def pyRepr (x : Float) : String := Id.run do
  let (neg, m, e) := Float.decompose x
  if e ≥ 0 then return showScaled neg ((m <<< e.toNat) * 10) 1
  let pe := 1 <<< (-e).toNat
  -- lower neighbour is closer when m is a power of two (not subnormal)
  let narrowBelow := m == 4503599627370496 && e > -1074
  for k in [1:18] do
    let n := roundScaled m e k
    let d := pow10[k]!
    -- x = m/pe, candidate = n/d; compare |n*pe - m*d| against half the gap
    let lhs : Int := (n * pe : Nat)
    let rhs : Int := (m * d : Nat)
    let diff := (lhs - rhs).natAbs
    let ok :=
      if lhs ≥ rhs || !narrowBelow then 2 * diff < d || (2 * diff == d && m % 2 == 0)
      else 4 * diff ≤ d
    if ok then return showScaled neg n k
  return showScaled neg (roundScaled m e 17) 17

/-- Veltkamp's split of `v` into a high half and a low half (26 + 27 bits). -/
@[inline] def veltkamp (v : Float) : Float × Float :=
  let c := cSplit * v
  let hi := c - (c - v)
  (hi, v - hi)

/-- Error-free product (Dekker): `hi + lo = a * b` exactly. -/
@[inline] def twoProd (a b : Float) : Float × Float :=
  let p := a * b
  let (ah, al) := veltkamp a
  let (bh, bl) := veltkamp b
  (p, ((ah * bh - p) + ah * bl + al * bh) + al * bl)

/-- Error-free sum for `|a| ≥ |b|`: `hi + lo = a + b` exactly. -/
@[inline] def fastSum (a b : Float) : Float × Float :=
  let hi := a + b
  (hi, (a - hi) + b)

/-- `math.hypot(x, y)` as computed by CPython 3.12 (`vector_norm` with
`n = 2`): lossless scaling and squaring, a square root, and one step of
differential correction. -/
def hypot (x y : Float) : Float :=
  let mx := max x.abs y.abs
  if mx == c0 then mx else
  let scale := Float.scaleB c1 (-mx.frExp.2)
  let x := x * scale
  let y := y * scale
  let (px, plx) := twoProd x x
  let (s1, sl1) := fastSum c1 px
  let (py, ply) := twoProd y y
  let (s2, sl2) := fastSum s1 py
  let f1 := c0 + plx + ply
  let f2 := c0 + sl1 + sl2
  let h := Float.sqrt (s2 - c1 + (f1 + f2))
  let (ph, pl) := twoProd (-h) h
  let (s3, sl3) := fastSum s2 ph
  let r := s3 - c1 + ((f1 + pl) + (f2 + sl3))
  (h + r / (c2 * h)) / scale

/-- Python 3.12's `sum` of floats: Neumaier compensated summation. -/
def pySum (xs : List Float) : Float := Id.run do
  let mut f := c0
  let mut c := c0
  for x in xs do
    let t := f + x
    if f.abs ≥ x.abs then c := c + ((f - t) + x) else c := c + ((x - t) + f)
    f := t
  if c != c0 && c.isFinite then f + c else f

/-- Python's `math.pi`, given by its bits (Lean's decimal literal reader is not
guaranteed to round correctly). -/
def pi : Float := Float.ofBits 0x400921FB54442D18

/-- Python's `math.radians`: `x * (math.pi / 180)`. -/
def radians (deg : Float) : Float := deg * (pi / 180.0)

-- Reference values from Python 3.12 (`format(v, '.1f')`, `repr(v)`).
#guard [0.25, 0.75, 1.25, -0.04, -0.0, 12.35].map fmt1 == ["0.2", "0.8", "1.2", "-0.0", "-0.0", "12.3"]
#guard [1.5 * 0.8, 1.3 * 0.8, 4.2, 2.0, 0.25].map pyRepr == ["1.2000000000000002", "1.04", "4.2", "2.0", "0.25"]
#guard pySum [0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1] == 1.0

end FregeDiagrams
