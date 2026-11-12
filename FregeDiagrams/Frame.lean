/-
FregeDiagrams.Frame: variant A, a frame picture.

A frame picture is a set of states (dots) and arrows between them, drawn at
hand-placed integer coordinates.  The vocabulary
(`docs/LANGUAGE.md` and `docs/NOTATION.md` have the full tables):

* a **hollow** dot is an infallible state; a **red** dot is a new state (one
  asserted to exist by the conclusion); a **crossed** dot says "no such state";
* a **dashed** arrow is `≤`, a **solid** arrow is `R`, a **wavy** arrow is
  `⇝ = (≤ ∪ R)*`, a **double line** is equality;
* a **composite** relation such as `≤;R;≤` is one arrow whose stretches change
  style in order;
* **black** is hypothesis, **red** conclusion;
* a **quantifier notch** in the line binds the target: a square `⊓` for "for
  all", a pointed `∨` for "there exists", with the bound name inside.
-/
import FregeDiagrams.Geometry

namespace FregeDiagrams

def BLACK := "#1b1b1b"
def RED := "#c0392b"
def GREY := "#6b6b6b"
/-- Radius of a state dot. -/
def NODE_R : Float := 4.2
/-- Default stroke width. -/
def STROKE : Float := 1.5
def FONT := "Latin Modern Math, STIX Two Math, Cambria Math, Times New Roman, serif"

/-- A basic relation; each has its own line style. -/
inductive Rel where
  /-- `≤`, the intuitionistic order: dashed. -/
  | le
  /-- `⊑ = ≤°`: dashed like `≤`; inside a composite, a hollow bead at the end
  of the stretch marks the intermediate state as infallible. -/
  | sqle
  /-- `R`, the modal accessibility relation: solid. -/
  | R
  /-- `R° = R` into an infallible state: solid like `R`; inside a composite,
  a hollow bead at the end of the stretch. -/
  | Rinf
  /-- `⇝ = (≤ ∪ R)*`, reachability: wavy. -/
  | reach
  /-- equality: a double line, no arrowhead. -/
  | eq
  /-- inequality: a double line struck through, no arrowhead.  Not drawn in a
  frame picture (variant A), where a caption says it. -/
  | ne
  /-- a labelled relation `-[LABEL]-` (undirected) or `-[LABEL]->` (directed),
  for relations a frame does not have (agreement, bisimulation links, …):
  dotted, the label at the middle of its stretch.  The library gives it no
  meaning; a client interprets it by its own definitions. -/
  | named (label : String) (directed : Bool)
deriving BEq, DecidableEq, Inhabited, Repr

/-- Does an arrow ending in this relation get an arrowhead? -/
def Rel.headed : Rel → Bool
  | .eq | .ne => false
  | .named _ d => d
  | _ => true

/-- A composite relation `r₁;r₂;…;rₙ` (relational composition), drawn as one
arrow in `n` equal stretches.  A singleton list is a basic relation. -/
abbrev Composite := List Rel

/-- The two quantifiers a notch can carry. -/
inductive Quant where
  /-- for all: the square notch `⊓`, drawn above a left-to-right line. -/
  | all
  /-- there exists: the pointed notch `∨`, drawn below. -/
  | ex
deriving BEq, Inhabited, Repr

/-- A state: a dot at integer grid coordinates, with an optional label placed
at offset `(lx, ly)`. -/
structure State where
  id : String
  x : Int
  y : Int
  label : String
  /-- infallible: drawn hollow. -/
  inf : Bool := false
  /-- new (asserted by the conclusion): drawn red. -/
  new : Bool := false
  lx : Int := 0
  ly : Int := -10
  /-- "no such state": a red cross over the dot. -/
  cross : Bool := false
  /-- extra SVG attributes for the editor (`DrawOpts.annotate`), else empty -/
  attrs : String := ""
deriving Inhabited

/-- An arrow from state `a` to state `b`. -/
structure Edge where
  a : String
  b : String
  rel : Composite := [.R]
  /-- part of the conclusion: red. -/
  concl : Bool := false
  /-- a dotted twin alongside the arrow ("there exists", older notation). -/
  twin : Bool := false
  /-- an open wedge at the source ("for all", older notation). -/
  wedge : Bool := false
  /-- signed sagitta of the quadratic Bézier, in pixels. -/
  bend : Float := 0.0
  head : Bool := true
  wedgeAngle : Float := 30.0
  /-- a quantifier notch in the line. -/
  q : Option Quant := none
  /-- the bound name in the notch (default: the target's label). -/
  qvar : Option String := none
  /-- `+1` or `-1`: which side the notch opens to (default: `∀` above, `∃`
  below, for a left-to-right arrow). -/
  qside : Option Float := none
  /-- where the notch sits, as a fraction of the arrow's length. -/
  qpos : Float := 0.35
  /-- extra SVG attributes for the editor (`DrawOpts.annotate`), else empty -/
  attrs : String := ""

/-- One drawn item of a frame picture, in drawing order. -/
inductive Item where
  | edge (e : Edge)
  /-- a self-loop on a state, leaving in direction `angle` (degrees). -/
  | loop (a : String) (rel : Rel) (concl : Bool) (angle : Float)
  /-- free text at integer coordinates. -/
  | text (x y : Int) (s color : String) (size : Nat) (anchor : String) (italic : Bool)

/-- The drawing style.  **soft** (the default since 0.10.0): thinner
strokes, round joins, and rounded corners on every bend of a line (notches,
forks, condition strokes, link turns).  **classic**: the drawing of earlier
versions, byte for byte (`--style classic`). -/
inductive Style where
  | soft | classic
deriving BEq, DecidableEq, Repr, Inhabited

/-- A variant-A diagram: states (drawn last, on top) and items. -/
structure Diagram where
  name : String
  w : Nat
  h : Nat
  nodes : Array State := #[]
  items : Array Item := #[]
  /-- the offset of the bound names in their notches (`--notch-name-offset`) -/
  nameDy : Float := 0.0
  /-- per binder (by state name), overriding `nameDy` -/
  nameDys : List (String × Float) := []
  /-- for the editor: wrap each state, label and arrow in a `<g>` carrying its
  `attrs` attributes.  Off by default, so the output is unchanged. -/
  annotate : Bool := false
  style : Style := .soft
deriving Inhabited

namespace Diagram

/-- Add a state (Python `Diagram.node`); the label defaults to the id. -/
def node (d : Diagram) (id : String) (x y : Int) (label : Option String := none)
    (inf new : Bool := false) (lx : Int := 0) (ly : Int := -10) (cross : Bool := false)
    (attrs : String := "") : Diagram :=
  { d with nodes := d.nodes.push (
      { id, x, y, label := label.getD id, inf, new, lx, ly, cross, attrs : State }) }

/-- Add an arrow. -/
def edge (d : Diagram) (e : Edge) : Diagram := { d with items := d.items.push (.edge e) }

/-- Add a self-loop. -/
def loop (d : Diagram) (a : String) (rel : Rel := .R) (concl : Bool := false)
    (angle : Float := -90.0) : Diagram :=
  { d with items := d.items.push (.loop a rel concl angle) }

/-- Add free text. -/
def text (d : Diagram) (x y : Int) (s : String) (color : String := GREY) (size : Nat := 11)
    (anchor : String := "start") (italic : Bool := false) : Diagram :=
  { d with items := d.items.push (.text x y s color size anchor italic) }

def find (d : Diagram) (id : String) : State :=
  (d.nodes.find? (·.id == id)).getD default

end Diagram

/-! ## Shapes

The drawing is built as typed shapes; SVG text is written only at the end
(`Shape.svg`).  The link router (`FregeDiagrams.Route`) reads the shapes, not the
SVG. -/

/-- One drawn element. -/
inductive Shape where
  /-- an open polyline; `width` as printed, `attrs` extra SVG attributes
  (dashes, caps, joins) -/
  | poly (pts : Polyline) (color : String) (width : String) (attrs : String := "")
  /-- a filled polygon (an arrowhead) -/
  | polygon (pts : Polyline) (fill : String)
  /-- a circle; no outline when `stroke` is empty -/
  | circle (c : P) (r : Float) (fill : String) (stroke : String := "") (width : String := "1.3")
  /-- italic text at `p`; `anchor` is `start` or `middle`; `rich` sets Unicode
  subscripts as SVG subscripts (the labels of labelled relations) -/
  | text (p : P) (s : String) (color : String) (size : Nat := 12) (anchor : String := "start")
    (rich : Bool := false)
  /-- anything else, as SVG text (not seen by the router) -/
  | raw (s : String)
deriving Inhabited

/-- Text content and attribute values for SVG: `&`, `<`, `>`, `"` escaped. -/
def xmlEsc (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | c => c.toString) ""

/-- The plain character a Unicode subscript stands for, if it is one. -/
def unsub (c : Char) : Option Char :=
  let subs := "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼᵣᵤᵥ".toList
  let plain := "0123456789+-=()aeoxhklmnpstijruv".toList
  (subs.zip plain).lookup c

/-- Escaped text with each run of Unicode subscripts set as an SVG subscript
(`tspan`), so that it does not depend on the font having those characters. -/
def subText (s : String) : String := Id.run do
  let mut out := ""
  let mut inSub := false
  for c in s.toList do
    match unsub c with
    | some p =>
      if !inSub then out := out ++ "<tspan baseline-shift=\"sub\" font-size=\"75%\">"; inSub := true
      out := out ++ xmlEsc p.toString
    | none =>
      if inSub then out := out ++ "</tspan>"; inSub := false
      out := out ++ xmlEsc c.toString
  if inSub then out := out ++ "</tspan>"
  return out

def Shape.svg : Shape → String
  | .poly pts c w a => s!"<polyline points=\"{polyStr pts}\" fill=\"none\" stroke=\"{c}\" stroke-width=\"{w}\"{a}/>"
  | .polygon pts f => s!"<polygon points=\"{polyStr pts}\" fill=\"{f}\"/>"
  | .circle c r f s w =>
    let st := if s.isEmpty then "" else s!" stroke=\"{s}\" stroke-width=\"{w}\""
    s!"<circle cx=\"{fmt1 c.x}\" cy=\"{fmt1 c.y}\" r=\"{pyRepr r}\" fill=\"{f}\"{st}/>"
  | .text p s c sz a rich =>
    s!"<text x=\"{fmt1 p.x}\" y=\"{fmt1 p.y}\" font-family=\"{FONT}\" font-size=\"{sz}\" font-style=\"italic\" text-anchor=\"{a}\" fill=\"{c}\">{if rich then subText s else xmlEsc s}</text>"
  | .raw s => s

/-- The box a text occupies (an estimate from its length): `(x0, y0, x1, y1)`. -/
def textBox (p : P) (s : String) (anchor : String) (size : Nat := 12) : Float × Float × Float × Float :=
  let w := 0.55 * size.toFloat * s.length.toFloat
  let x0 := if anchor == "middle" then p.x - w / 2.0 else if anchor == "end" then p.x - w else p.x
  (x0 - 1.0, p.y - 0.83 * size.toFloat, x0 + w + 1.0, p.y + 0.17 * size.toFloat)

/-! ## Rendering primitives -/

/-- Draw a polyline in the style of a basic relation. -/
def stroke (pts : Polyline) (rel : Rel) (color : String) (width : Float := STROKE) :
    Array Shape :=
  let eqLines := #[-1.7, 1.7].map fun d => Shape.poly (offset pts d) color (pyRepr (width * 0.8))
  match rel with
  | .eq => eqLines
  | .named .. => #[.poly pts color (pyRepr (width * 0.85)) " stroke-linecap=\"round\" stroke-dasharray=\"0.1,4.2\""]
  | .ne =>
    let (m, d) := pointAt pts (arclen pts / 2.0)
    let n := d.perp
    let a := m + d * 2.5 + n * 5.0
    let b := m - d * 2.5 - n * 5.0
    eqLines.push (.poly #[a, b] color (pyRepr width))
  | _ =>
    let pts := if rel == .reach then wavy pts else pts
    let da := if rel == .le || rel == .sqle then " stroke-dasharray=\"5,3.2\"" else ""
    #[.poly pts color (pyRepr width) (" stroke-linecap=\"round\"" ++ da)]

/-- Hollow beads at the joints of a composite that follow a `⊑` or `R°`
stretch: the intermediate state there is infallible. -/
def beads (pts : Polyline) (rels : Composite) (color : String) : Array Shape := Id.run do
  let n := rels.length
  if n ≤ 1 then return #[]
  let pieces := split pts ((List.range (n - 1)).map fun i => (i + 1).toF / n.toF)
  let mut out := #[]
  for i in List.range (n - 1) do
    if rels[i]! == .sqle || rels[i]! == .Rinf then
      let p := pieces[i]!.back!
      out := out.push (.circle p 3.2 "white" color)
  return out

/-- An arrowhead at the end of a polyline, aimed along its last few points. -/
def arrowHead (pts : Polyline) (color : String) : Array Shape :=
  let tip := pts.back!
  let back := pts[pts.size - 4]!   -- `max 0 (n - 4)` by truncated subtraction
  let d := (tip - back).unit
  let n := d.perp
  let base := tip - d * 8.0
  let p1 := base + n * 3.6
  let p2 := base - n * 3.6
  #[.polygon #[tip, p1, p2] color]

/-- How far a bound name may move into its notch (`dy`) before the notch
deepens to keep room for it. -/
def NOTCH_SLACK : Float := 1.0

/-- Half the x-height of a 12-unit italic name: its baseline goes this far
below the point where the name's visual centre should be. -/
def NAME_HALF_X : Float := 2.7

/-- A quantifier notch: the width of the gap it takes in its line, and its
height.  An unnamed notch (bound names hidden) is smaller.  A name moved
further in than `NOTCH_SLACK` deepens the notch by the excess. -/
def notchDims (kind : Quant) (var : String) (dy : Float := 0.0) : Float × Float :=
  let tw := 7.2 * var.length.toF
  let deeper := if var.isEmpty then 0.0 else max 0.0 (dy - NOTCH_SLACK)
  if var.isEmpty then (if kind == .all then (10.0, 9.0) else (14.0, 11.0))
  else if kind == .all then (max 13.0 (tw + 6.0), 14.0 + deeper)
  -- the pointed notch widens with its depth, so the name, moved down by
  -- `deeper`, keeps the same clearance from the sloping sides
  else (max 20.0 (tw + 12.0) * ((17.0 + deeper) / 17.0), 17.0 + deeper)


/-- A quantifier notch centred at arc length `s`: `⊓` (square) for `∀`, `∨`
(pointed) for `∃`, opening away from the line, with the variable inside.
The name's visual centre (the middle of its x-height) sits at half the depth
of a square notch and at 0.30 of the depth of a pointed one (where it is
wide enough), whichever way the notch opens.  `dy` moves the name `dy` units
further in (positive) or towards the line (negative); beyond `NOTCH_SLACK`
the notch deepens by the excess, widening a pointed one in proportion.
Returns the SVG and the gap `(lo, hi)` (arc lengths) it bridges. -/
def notch (pts : Polyline) (s : Float) (kind : Quant) (var color : String) (rels : Composite)
    (side : Option Float) (dy : Float := 0.0) : Array Shape × Float × Float :=
  let (p, d) := pointAt pts s
  let side := side.getD (if kind == .all then -1.0 else 1.0)
  let n := d.perp * side
  let (g, h) := notchDims kind var dy
  let h0 := (notchDims kind var).2
  let a := p - d * (g / 2.0)
  let b := p + d * (g / 2.0)
  let L := arclen pts
  let rel := if L != 0.0 then rels[min (s / L * rels.length.toF).toUInt64.toNat (rels.length - 1)]!
             else rels[0]!
  let rel := if rel == .reach then .R else rel
  let (shape, tc) := match kind with
    | .all => (#[a, a + n * h, b + n * h, b], p + n * (h0 * 0.5 + dy))
    | .ex => (#[a, p + n * h, b], p + n * (h0 * 0.30 + dy))
  let out := stroke shape rel color |>.push (.text ⟨tc.x, tc.y + NAME_HALF_X⟩ var color 12 "middle")
  (out, s - g / 2.0, s + g / 2.0)

/-- Sorted, without duplicates (Python `sorted(set(xs))`). -/
def sortDedup (xs : List Float) : List Float :=
  let ys := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  ys.mergeSort (· ≤ ·)

/-- The cut points `1/n, …, (n-1)/n` of an `n`-stretch composite. -/
def stretchCuts (n : Nat) : List Float :=
  (List.range (n - 1)).map fun i => (i + 1).toF / n.toF

/-- The labels of the labelled stretches of a composite arrow, each at the
middle of its stretch, set off to the left of the direction of drawing. -/
def relLabels (pts : Polyline) (rels : Composite) (color : String) : Array Shape := Id.run do
  let L := arclen pts
  let n := rels.length
  let mut out := #[]
  for (r, i) in rels.zip (List.range n) do
    if let .named l _ := r then
      let (m, d) := pointAt pts (L * ((i.toF + 0.5) / n.toF))
      let p := m + d.perp * (-8.0)
      out := out.push (.text ⟨p.x, p.y + 1.0⟩ l color 11 "middle" true)
  return out

/-- Draw the stretches of a composite arrow. -/
def stretches (pts : Polyline) (rels : Composite) (color : String) : Array Shape :=
  let pieces := if rels.length > 1 then split pts (stretchCuts rels.length) else #[pts]
  (rels.zip pieces.toList).foldl (fun out (r, piece) => out ++ stroke piece r color) #[]

namespace Diagram

/-- An arrow whose line has a gap bridged by a quantifier notch. -/
def notched (d : Diagram) (pts : Polyline) (rels : Composite) (color : String) (e : Edge)
    (q : Quant) : Array Shape := Id.run do
  let L := arclen pts
  let var := e.qvar.getD (d.find e.b).label
  -- the binder is the target state, `NAME/PANEL`
  let x := (e.b.splitOn "/").headD e.b
  let dy := (d.nameDys.lookup x).getD d.nameDy
  let (out, lo, hi) := notch pts (L * e.qpos) q var color rels e.qside dy
  -- for the editor: the notch, and the name in it, as elements of their own
  let out := if !d.annotate then out else
    #[Shape.raw s!"<g data-part=\"notch\" data-var=\"{xmlEsc x}\" data-dy=\"{((d.nameDys.lookup x).map (toString ·.toInt64)).getD ""}\">"] ++
      out.pop ++ #[Shape.raw "<g data-part=\"nname\">", out.back!, Shape.raw "</g></g>"]
  let bounds := sortDedup (stretchCuts rels.length ++ [lo / L, hi / L])
  let pieces := split pts bounds
  let edges := (0.0 :: bounds ++ [1.0]).toArray
  let mut out := out
  for k in [0:pieces.size] do
    let mid := (edges[k]! + edges[k+1]!) / 2.0
    if lo / L < mid && mid < hi / L then continue
    let rel := rels[min (mid * rels.length.toF).toUInt64.toNat (rels.length - 1)]!
    out := out ++ stroke pieces[k]! rel color
  return out

def renderEdge (d : Diagram) (e : Edge) : Array Shape := Id.run do
  let A := (d.find e.a); let B := (d.find e.b)
  let A := P.ofInt A.x A.y; let B := P.ofInt B.x B.y
  let color := if e.concl then RED else BLACK
  let mid := (A + B) * 0.5
  let ctrl := mid + (B - A).unit.perp * e.bend
  let pts := trim (bezier A ctrl B) (NODE_R + 3.0) (NODE_R + 3.0)
  let rels := e.rel
  let mut out := match e.q with
    | some q => d.notched pts rels color e q
    | none => stretches pts rels color
  out := out ++ beads pts rels color ++ relLabels pts rels color
  if e.head && rels.getLast!.headed then out := out ++ arrowHead pts color
  if e.twin then
    let tw := trim (offset pts 4.6) 2.0 9.0
    out := out.push (.poly tw color "1.3" " stroke-dasharray=\"0.1,3.2\" stroke-linecap=\"round\"")
  if e.wedge then
    let src := pts[0]!
    let dir := (pts[min 6 (pts.size - 1)]! - src).unit
    let ang := radians e.wedgeAngle
    let Lw := min 38.0 (0.5 * arclen pts)
    for sgn in [1.0, -1.0] do
      let ca := Float.cos (sgn * ang); let sa := Float.sin (sgn * ang)
      let r : P := ⟨dir.x * ca - dir.y * sa, dir.x * sa + dir.y * ca⟩
      let r0 := rels.head!
      out := out ++ stroke #[src, src + r * Lw] (if r0 == .reach then .R else r0) color 1.1
  return out

def renderLoop (d : Diagram) (a : String) (rel : Rel) (concl : Bool) (angle : Float) :
    Array Shape :=
  let n := d.find a
  let c := P.ofInt n.x n.y
  let color := if concl then RED else BLACK
  let ang := radians angle
  let dir : P := ⟨Float.cos ang, Float.sin ang⟩
  let p := dir.perp
  let r := 11.0
  let start := c + (dir * (NODE_R + 2.0) + p * 4.0)
  let stop := c + (dir * (NODE_R + 2.0) + p * (-4.0))
  let top := c + dir * (NODE_R + 2.0 * r + 4.0)
  let ctl1 := top + p * (2.0 * r)
  let ctl2 := top + p * (-2.0 * r)
  let pts := bezier start ctl1 top 20 ++ (bezier top ctl2 stop 20).extract 1
  stroke pts rel color ++ arrowHead pts color

/-- The dot of a state (and its cross). -/
def renderDot (n : State) : Array String := Id.run do
  let color := if n.new then RED else BLACK
  let fill := if n.inf then "white" else color
  let mut out := #[s!"<circle cx=\"{n.x}\" cy=\"{n.y}\" r=\"{pyRepr NODE_R}\" fill=\"{fill}\" stroke=\"{color}\" stroke-width=\"1.4\"/>"]
  if n.cross then
    for s in [(1 : Int), -1] do
      out := out.push s!"<line x1=\"{n.x - 7}\" y1=\"{n.y - 7 * s}\" x2=\"{n.x + 7}\" y2=\"{n.y + 7 * s}\" stroke=\"{RED}\" stroke-width=\"1.8\"/>"
  return out

/-- The label of a state, if it has one. -/
def renderLabel (n : State) : Array String :=
  let color := if n.new then RED else BLACK
  if n.label != "" then
    #[s!"<text x=\"{n.x + n.lx}\" y=\"{n.y + n.ly}\" font-family=\"{FONT}\" font-size=\"14\" font-style=\"italic\" text-anchor=\"middle\" fill=\"{color}\">{xmlEsc n.label}</text>"]
  else #[]

def renderNode (n : State) : Array String := renderDot n ++ renderLabel n

end Diagram

/-- The stroke widths of the soft style, from those of the classic one. -/
def softWidth : String → String
  | "2.0" => "1.6" | "1.9" => "1.15" | "1.5" => "1.1" | "1.4" => "1.1" | "1.3" => "1.0" | w => w

/-- The radius of the rounded corners of the soft style. -/
def SOFT_R : Float := 3.5

/-- A polyline as an SVG path whose corners are rounded with radius `r`
(less where a segment is short: at most half of either segment). -/
def roundedPath (pts : Array P) (r : Float) : String := Id.run do
  let f (p : P) := fmt1 p.x ++ "," ++ fmt1 p.y
  let mut d := "M" ++ f pts[0]!
  for i in [1:pts.size - 1] do
    let p0 := pts[i-1]!; let p1 := pts[i]!; let p2 := pts[i+1]!
    let l1 := (p1 - p0).len; let l2 := (p2 - p1).len
    let rr := min r (min (l1 / 2.0) (l2 / 2.0))
    if rr < 0.3 then
      d := d ++ " L" ++ f p1
    else
      let a := p1 - (p1 - p0) * (rr / l1)
      let b := p1 + (p2 - p1) * (rr / l2)
      d := d ++ " L" ++ f a ++ " Q" ++ f p1 ++ " " ++ f b
  return d ++ " L" ++ f pts.back!

/-- A decimal number as `fmt1` prints it (`-12.5`, `3.0`). -/
def parseFloat? (s : String) : Option Float := do
  let (neg, t) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let (ip, fp) := match t.splitOn "." with
    | [a] => (a, "")
    | [a, b] => (a, b)
    | _ => ("", "x")
  if ip.isEmpty || !ip.all Char.isDigit || !fp.all Char.isDigit then none
  let v := ip.toNat!.toFloat + (if fp.isEmpty then 0.0 else fp.toNat!.toFloat / (10.0 ^ fp.length.toFloat))
  return if neg then -v else v

/-- Parse the `points` of a polyline as printed by `polyStr`. -/
def parsePoints (s : String) : Array P :=
  (s.splitOn " ").toArray.filterMap fun xy =>
    match xy.splitOn "," with
    | [x, y] => do
      let px ← parseFloat? x; let py ← parseFloat? y
      pure (⟨px, py⟩ : P)
    | _ => none

/-- The soft style, applied to a drawn SVG: widths, round joins, and (unless
`keepLines`, which the editor needs for its handles) every polyline with a
bend drawn as a path with rounded corners. -/
def softSvg (svg : String) (keepLines : Bool := false) : String := Id.run do
  -- stroke widths
  let parts := svg.splitOn "stroke-width=\""
  let mut out := parts.headD ""
  for p in parts.drop 1 do
    match p.splitOn "\"" with
    | w :: rest => out := out ++ "stroke-width=\"" ++ softWidth w ++ "\"" ++ "\"".intercalate rest
    | [] => out := out ++ "stroke-width=\"" ++ p
  -- round joins everywhere
  out := out.replace "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>"
    "<style>polyline,path,polygon{stroke-linejoin:round}</style>\n<rect width=\"100%\" height=\"100%\" fill=\"white\"/>"
  if keepLines then return out
  -- rounded corners
  let parts := out.splitOn "<polyline points=\""
  let mut res := parts.headD ""
  for p in parts.drop 1 do
    match p.splitOn "\"" with
    | ptsStr :: rest =>
      let pts := parsePoints ptsStr
      if pts.size ≥ 3 then res := res ++ "<path d=\"" ++ roundedPath pts SOFT_R ++ "\"" ++ "\"".intercalate rest
      else res := res ++ "<polyline points=\"" ++ p
    | [] => res := res ++ "<polyline points=\"" ++ p
  return res

/-- The SVG document around a body. -/
def svgDoc (w h : Nat) (body : Array String) : String :=
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" viewBox=\"0 0 {w} {h}\">\n" ++
  "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>\n" ++
  "\n".intercalate body.toList ++ "\n</svg>\n"

/-- Render a frame picture: items in order, then the states on top.  With
`annotate`, each arrow, dot and label is a `<g>` with its `attrs` attributes. -/
def Diagram.svg (d : Diagram) : String := Id.run do
  let wrap (attrs : String) (xs : Array String) : Array String :=
    if d.annotate && !xs.isEmpty then #[s!"<g{attrs}>"] ++ xs ++ #["</g>"] else xs
  let mut body := #[]
  for it in d.items do
    match it with
    | .edge e => body := body ++ wrap e.attrs ((d.renderEdge e).map Shape.svg)
    | .loop a rel concl angle => body := body ++ (d.renderLoop a rel concl angle).map Shape.svg
    | .text x y s color size anchor italic =>
      let st := if italic then " font-style=\"italic\"" else ""
      body := body.push s!"<text x=\"{x}\" y=\"{y}\" font-family=\"{FONT}\" font-size=\"{size}\" fill=\"{color}\" text-anchor=\"{anchor}\"{st}>{xmlEsc s}</text>"
  for n in d.nodes do
    body := body ++ wrap (n.attrs ++ " data-part=\"dot\"") (Diagram.renderDot n)
      ++ wrap (n.attrs ++ " data-part=\"label\"") (Diagram.renderLabel n)
  let svg := svgDoc d.w d.h body
  return if d.style == .soft then softSvg svg d.annotate else svg

end FregeDiagrams
