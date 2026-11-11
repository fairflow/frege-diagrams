/-
FregeDiagrams.Tree: variant B, a Frege-style formula tree whose leaves are small
frame pictures.

The tree is asserted by a vertical judgement stroke on the left.  Each
construct draws a horizontal content stroke from its left end; its layout is
computed bottom-up by `measure` (width, extent above, extent below the
stroke) and drawn top-down by `draw`.  Colour is polarity: red positive,
black negative.  A conclusion keeps the polarity of its condition; a
hypothesis, and the body of a negation, reverse it.  The asserted tree is
positive.
-/
import FregeDiagrams.Frame

namespace FregeDiagrams

/-- A formula tree (variant B). -/
inductive Tree where
  /-- A chain of states `s r₁ t r₂ u …`: a small frame picture on the stroke.
  A name ending in `°` is an infallible (hollow) state; a step back to the same
  name (ignoring `°`) draws a self-loop. -/
  | leaf (start : String) (steps : List (Composite × String))
  /-- A leaf in words. -/
  | text (s : String)
  /-- A quantifier notch on the stroke; its scope is everything to the right. -/
  | q (kind : Quant) (var : String) (body : Tree)
  /-- Frege's negation: a short tick below the stroke. -/
  | neg (body : Tree)
  /-- A condition: the conclusion continues the stroke, the hypotheses hang
  below on a vertical condition stroke. -/
  | cond (concl : Tree) (hyps : List Tree)
  /-- A conjunction: a fork.  The stroke ends in a junction dot; straight rays
  run from it to the parts, stacked symmetrically above and below, so that
  no part continues the stroke (which would read as a condition). -/
  | and (parts : List Tree)
  /-- A disjunction (primitive, never encoded as `¬A → B`): a fork like a
  conjunction, with a hollow junction dot and an arc across the rays near the
  junction, closing the fan like the opening of `∨`. -/
  | or (parts : List Tree)
deriving Inhabited

/-- Typesetting options for a set of diagrams.
* `links`: draw links, routed around the outside of the tree, from each
  quantifier notch to every occurrence of the state it binds, each binder in
  its own colour and dashed in the Morse code of its name;
  free states (the implicit outer quantifier) get none (view B);
* `hideBound`: leave bound names out (in the notches and at the states they
  bind), to show that the links, or the arrows, carry the binding. -/
structure DrawOpts where
  links : Bool := false
  hideBound : Bool := false
  /-- internal: where the implicit outer quantifier sits (the judgement
  stroke), the anchor of links to free states -/
  root : P := ⟨0.0, 0.0⟩
  /-- internal: the free state names of the tree, in order (for lanes) -/
  free : List String := []
  /-- internal: the binders whose notch is drawn flipped (`⊔` for `∀`, `∧`
  for `∃`), chosen by the link router where that saves crossings -/
  flips : List String := []
  /-- binders whose notch is fixed (the `notch NAME up|down` hint): `true`
  opens upwards; these are never turned over by the router -/
  fixedNotches : List (String × Bool) := []
  /-- a factor on every clearance of the links: row gaps, tracks, channels,
  the room kept around states and names (`--spacing`) -/
  spacing : Float := 1.0
  /-- the offset of a bound name in its notch, in SVG units, towards the
  notch's open end (positive: away from the stroke, the notch deepened by the
  same amount; negative: towards the stroke); `--notch-name-offset` -/
  nameDy : Float := 0.0
  /-- for the editor: ids and current hint values on the SVG elements of
  view A (`Diagram.annotate`).  Off by default; the output is then unchanged. -/
  annotate : Bool := false
deriving Inhabited

/-- Extra room between rows, for the link lanes. -/
def DrawOpts.gap (o : DrawOpts) : Float := if o.links then 16.0 * o.spacing else 0.0


/-- A binder in scope, for links: the state name, the path of the stroke
from its notch (or, for a free state, from the judgement stroke) to the
current point, its rail number, and whether it is free. -/
structure Bind where
  name : String
  path : Polyline
  lane : Nat
  free : Bool
  /-- where the notch's own line is, relative to the stroke: the top of a
  `⊓` (negative, above) or the point of a `∨` (positive, below) -/
  notchDy : Float := 0.0
  /-- half the notch's width -/
  notchHw : Float := 0.0
  /-- the binders whose scope contains this one, by their notch points -/
  encl : List P := []
deriving Inhabited

/-- Extend the stroke path of every binder in scope by a point. -/
def extendAll (env : List Bind) (p : P) : List Bind :=
  env.map fun b =>
    if b.path.size > 0 && b.path.back!.x == p.x && b.path.back!.y == p.y then b
    else { b with path := b.path.push p }

/-- Pastel but not pale link colours, one per binder (dark enough to print). -/
def linkPalette : Array String :=
  #["#4f8fc0", "#d4813a", "#5ea35a", "#b0619f", "#c2a02e", "#45a8a0", "#c4605c", "#7f78c4"]

/-- Greek Morse code (the Greek national variant of Morse), for Greek letters
in names; capital and small letters alike.  Without it every all-Greek name
would get the same fallback pattern. -/
def greekMorse (c : Char) : String :=
  let small := "αβγδεζηθικλμνξοπρσςτυφχψω".toList
  let capital := "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΣΤΥΦΧΨΩ".toList
  let codes := [".-", "-...", "--.", "-..", ".", "--..", "....", "-.-.", "..", "-.-", ".-..", "--",
    "-.", "-..-", "---", ".--.", ".-.", "...", "...", "-", "-.--", "..-.", "----", "--.-", ".--"]
  ((small.zip codes ++ capital.zip codes).lookup c).getD ""

/-- International Morse for the characters of state names; a prime is the
apostrophe, a subscript digit the digit; Greek letters by `greekMorse`. -/
def morseOf : Char → String
  | 'a' => ".-" | 'b' => "-..." | 'c' => "-.-." | 'd' => "-.." | 'e' => "." | 'f' => "..-."
  | 'g' => "--." | 'h' => "...." | 'i' => ".." | 'j' => ".---" | 'k' => "-.-" | 'l' => ".-.."
  | 'm' => "--" | 'n' => "-." | 'o' => "---" | 'p' => ".--." | 'q' => "--.-" | 'r' => ".-."
  | 's' => "..." | 't' => "-" | 'u' => "..-" | 'v' => "...-" | 'w' => ".--" | 'x' => "-..-"
  | 'y' => "-.--" | 'z' => "--.."
  | '′' | '\'' => ".----." | '0' | '₀' => "-----" | '1' | '₁' => ".----" | '2' | '₂' => "..---"
  | '3' | '₃' => "...--" | '4' | '₄' => "....-" | '5' | '₅' => "....." | '6' | '₆' => "-...."
  | '7' | '₇' => "--..." | '8' | '₈' => "---.." | '9' | '₉' => "----."
  | c => greekMorse c

/-- The dash pattern spelling a name in Morse, repeated along the link: dot
1.6, dash 5.5, gap 2.2 within a letter; between letters and between repeats
the gap carries a short mark (0.8) in its middle (not strict Morse). -/
def morseDash (name : String) : String := Id.run do
  let mut parts : Array String := #[]
  let letters := name.toList.map morseOf |>.filter (· != "")
  for (li, code) in (List.range letters.length).zip letters do
    let syms := code.toList
    for (i, c) in (List.range syms.length).zip syms do
      parts := parts.push (if c == '.' then "1.6" else "5.5")
      let last := i + 1 == syms.length
      -- within a letter a plain gap; between letters, and between repeats, a
      -- short mark (shorter than a dot) in the middle of the gap, so that the
      -- line is broken less and corners more often fall on ink
      parts := parts.push (if !last then "2.2"
        else if li + 1 == letters.length then "2.6,0.8,2.6,0.8,2.6"   -- between repeats
        else "2.2,0.8,2.2")                                           -- between letters
  return if parts.isEmpty then "4,2.5" else ",".intercalate parts.toList

/-- A bound occurrence of a state, for the link router: its binder (named,
and identified by the midpoint of its notch's own line, where every link
from it starts), the direction away from the stroke (`-1` up, `+1` down), and
the state. -/
structure Occ where
  name : String
  notch : P
  dir : Float
  /-- half the notch's width -/
  hw : Float
  tgt : P
  /-- the number of binders whose scope contains this binder's -/
  depth : Nat := 0
  /-- those binders, by their notch points (`notch`) -/
  encl : List P := []
deriving Inhabited

/-- A state's name, placed after the links are routed. -/
structure Label where
  pos : P
  text : String
  color : String
  /-- the state carries a loop (above it) -/
  looped : Bool
deriving Inhabited

/-- What drawing a tree produces: shapes, and for the link router the bound
occurrences, the names still to place, and the box of each leaf. -/
inductive Mark where
  | shape (s : Shape)
  | occ (o : Occ)
  | label (l : Label)
  | box (x0 y0 x1 y1 : Float)
  /-- an undrawn piece of stroke, for routing: the small gaps a row leaves
  around its states, which a link must not slip through -/
  | bar (pts : Polyline)
deriving Inhabited

def sh (xs : Array Shape) : Array Mark := xs.map .shape

/-- The colour of the opposite polarity. -/
def flipCol (c : String) : String := if c == RED then BLACK else RED

/-- Length of the stub of stroke before each construct. -/
def STUB : Float := 10.0

/-- Horizontal length of the rays of a conjunction fork. -/
def FORK : Float := 16.0

/-- Horizontal room for one stretch of a relation in a leaf. -/
def segLen : Rel → Float
  | .le => 44.0 | .sqle => 44.0 | .R => 44.0 | .Rinf => 44.0 | .reach => 50.0 | .eq => 30.0
  | .ne => 30.0
  | .named l _ => max 44.0 (6.6 * l.length.toF + 16.0)

/-- Room for a (possibly composite) relation: stretches of a composite are
shortened to 70%. -/
def relLen (r : Composite) : Float :=
  pySum (r.map fun x => segLen x * (if r.length > 1 then 0.7 else 1.0))

/-- A state name without its trailing `°` marks. -/
def bare (s : String) : String := String.ofList (s.toList.reverse.dropWhile (· == '°')).reverse

/-- Does this notch open upwards (`⊓`, or a flipped `∨`)? -/
def notchUp (o : DrawOpts) (kind : Quant) (var : String) : Bool :=
  match o.fixedNotches.lookup var with
  | some up => up
  | none => (kind == .all) != o.flips.contains var

/-- `(width, above, below)`: the extent of a tree around its stroke. -/
partial def measure (o : DrawOpts := {}) : Tree → Float × Float × Float
  | .leaf s steps => Id.run do
    let states := s :: steps.map (·.2)
    let mut w := 8.0
    let mut isLoop := false
    for (i, (r, _)) in (List.range steps.length).zip steps do
      if bare states[i]! == bare states[i+1]! then
        isLoop := true
        continue
      w := w + relLen r
    return (STUB + w + 10.0, if isLoop then 36.0 else 22.0, 8.0)
  | .text s => (STUB + 6.6 * s.length.toF + 8.0, 12.0, 6.0)
  | .q kind var body =>
    let (w, up, dn) := measure o body
    let (g, h) := notchDims kind (if o.hideBound then "" else var) o.nameDy
    let (up, dn) := if notchUp o kind var then (max up (h + 3.0), dn) else (up, max dn (h + 3.0))
    (STUB + g + w, up, dn)
  | .neg body =>
    let (w, up, dn) := measure o body
    (STUB + 8.0 + w, up, max dn 10.0)
  | .cond concl hyps => Id.run do
    -- Frege's staggering: hypothesis i hangs from its own junction, the i-th
    -- along the stroke; the outermost (first) attaches leftmost and lowest
    let n := hyps.length
    let (wc, up, dn) := measure o concl
    let mut w := STUB * n.toF + wc
    let mut cur := dn
    for (i, h) in ((List.range n).zip hyps).reverse do
      let (wh, uh, dh) := measure o h
      cur := cur + (12.0 + o.gap + uh + dh)
      w := max w (STUB * (i + 1).toF + wh)
    return (w, up, cur)
  | .and parts | .or parts =>
    -- a fork: the parts stacked symmetrically about the stroke
    let ms := parts.map (measure o)
    let w := (ms.map (·.1)).foldl max 0.0 + FORK
    let tot := pySum (ms.map fun (_, u, d) => u + d) + (10.0 + o.gap) * (parts.length - 1).toF
    (STUB + w, tot / 2.0, tot / 2.0)

/-- Draw a leaf chain with its stroke starting at `(x, y)`. -/
def drawLeaf (s : String) (steps : List (Composite × String)) (x y : Float) (col : String)
    (env : List Bind := []) (o : DrawOpts := {}) : Array Mark := Id.run do
  let states := (s :: steps.map (·.2)).toArray
  let mut out := sh (stroke #[⟨x, y⟩, ⟨x + STUB, y⟩] .R col 1.3)
  let mut cx := x + STUB + 8.0
  out := out.push (.bar #[⟨x + STUB, y⟩, ⟨cx - NODE_R, y⟩])
  let mut pos : Array Float := #[]
  for i in [0:states.size] do
    let st := states[i]!
    if i != 0 then
      let r := steps[i-1]!.1
      if bare st == bare states[i-1]! then
        -- a loop on the previous state
        let p := pos.back!
        let pts := bezier ⟨p - 4.0, y - NODE_R - 2.0⟩ ⟨p - 18.0, y - 32.0⟩ ⟨p, y - 30.0⟩ 15 ++
          (bezier ⟨p, y - 30.0⟩ ⟨p + 18.0, y - 32.0⟩ ⟨p + 4.0, y - NODE_R - 2.0⟩ 15).extract 1
        -- Python passes a composite name here, which draws solid
        out := out ++ sh (stroke pts (if r.length == 1 then r.head! else .R) col)
        out := out ++ sh (arrowHead pts col)
        continue
      let nx := cx + relLen r
      -- sampled densely, so that a wavy (⇝) stretch really waves
      let pts := trim (bezier ⟨cx, y⟩ ⟨(cx + nx) / 2.0, y⟩ ⟨nx, y⟩) (NODE_R + 2.0) (NODE_R + 2.0)
      out := out.push (.bar #[⟨cx + NODE_R, y⟩, pts[0]!]) |>.push (.bar #[pts.back!, ⟨nx - NODE_R, y⟩])
      out := out ++ sh (stretches pts r col)
      out := out ++ sh (beads pts r col) ++ sh (relLabels pts r col)
      if r.getLast!.headed then out := out ++ sh (arrowHead pts col)
      cx := nx
    pos := pos.push cx
    -- a free state is the implicit outer one, an arbitrary infallible state
    let hollow := st.endsWith "°" || !(env.any (·.name == bare st))
    out := out.push (.shape (.circle ⟨cx, y⟩ NODE_R (if hollow then "white" else col) col "1.4"))
    let lab0 := bare st
    let binder := env.find? (fun b => b.name == lab0 && !b.free)
    if o.links then
      if let some b := env.find? (fun b => b.name == lab0 && !b.free) then
        let a := b.path[0]!
        let oc : Occ := { name := b.name, notch := ⟨a.x, a.y + b.notchDy⟩,
                          dir := if b.notchDy < 0.0 then -1.0 else 1.0, hw := b.notchHw, tgt := ⟨cx, y⟩, depth := b.lane, encl := b.encl }
        out := out.push (.occ oc)
    let lab := if o.hideBound && binder.isSome then "" else lab0
    let repeated := i != 0 && (List.range states.size).any fun j => bare states[j]! == lab0 && j != i
    -- a looped state (its loop is above) is labelled beside the dot, so that
    -- a link arriving from below meets the dot, not the name
    let (lx, ly, anchor) := if repeated then (cx + 9.0, y + 4.0, "start") else (cx, y - 9.0, "middle")
    -- the name of a linked state is placed after routing, clear of the links
    if o.links && lab != "" && binder.isSome then
      out := out.push (.label { pos := ⟨cx, y⟩, text := lab, color := col, looped := repeated })
      continue
    out := out.push (.shape (.text ⟨lx, ly⟩ lab col 12 anchor))
  return out

/-- Draw a leaf, plus its box for the link router. -/
def drawLeafBoxed (s : String) (steps : List (Composite × String)) (x y : Float) (col : String)
    (env : List Bind) (o : DrawOpts) : Array Mark :=
  let (w, up, dn) := measure o (.leaf s steps)
  (drawLeaf s steps x y col env o).push (.box x (y - up) (x + w) (y + dn))

/-- Draw a tree with its stroke starting at `(x, y)`, in colour `col`. -/
partial def draw (t : Tree) (x y : Float) (col : String)
    (env : List Bind := []) (o : DrawOpts := {}) : Array Mark :=
  let line (x0 x1 : Float) := sh (stroke #[⟨x0, y⟩, ⟨x1, y⟩] .R col 1.3)
  match t with
  | .leaf s steps => drawLeafBoxed s steps x y col (extendAll env ⟨x, y⟩) o
  | .text s =>
    let (w, up, dn) := measure o (.text s)
    line x (x + STUB) |>.push (.shape (.text ⟨x + STUB + 4.0, y + 4.2⟩ s col))
      |>.push (.box x (y - up) (x + w) (y + dn))
  | .q kind var body =>
    let shown := if o.hideBound then "" else var
    let (g, h) := notchDims kind shown o.nameDy
    let upw := notchUp o kind var
    let x1 := x + STUB + g + 4.0
    let (svg, lo, hi) := notch #[⟨x, y⟩, ⟨x1, y⟩] (STUB + g / 2.0) kind shown col [.R]
      (some (if upw then -1.0 else 1.0)) o.nameDy
    -- for the editor: the notch as one element carrying its binder
    let svg := if !o.annotate then svg else
      #[Shape.raw s!"<g data-k=\"notch\" data-name=\"{xmlEsc var}\" data-kind=\"{if kind == .all then "all" else "ex"}\" data-up=\"{if upw then 1 else 0}\" data-fixed=\"{match o.fixedNotches.lookup var with | some true => "up" | some false => "down" | none => ""}\">"] ++
        svg ++ #[Shape.raw "</g>"]
    -- the new binder's rail starts under the notch
    let nb : Bind := { name := var, path := #[⟨x + STUB + g / 2.0, y⟩], lane := env.length, free := false,
                       notchDy := if upw then -h else h, notchHw := g / 2.0,
                       encl := (env.filter (!·.free)).map fun b =>
                         (⟨b.path[0]!.x, b.path[0]!.y + b.notchDy⟩ : P) }
    let env := extendAll env ⟨x1, y⟩
    sh svg ++ line x (x + lo) ++ line (x + hi) x1 ++
      draw body x1 y col (nb :: env.filter (·.name != var)) o
  | .neg body =>
    line x (x + STUB + 8.0) ++ sh (stroke #[⟨x + STUB, y⟩, ⟨x + STUB, y + 9.0⟩] .R col 1.3) ++
      draw body (x + STUB + 8.0) y (flipCol col) (extendAll env ⟨x + STUB + 8.0, y⟩) o
  | .cond concl hyps => Id.run do
    -- `if H₀, …, Hₙ₋₁ then C` is H₀ → (… → (Hₙ₋₁ → C)): one condition stroke
    -- per hypothesis, staggered along the main stroke (Frege).  The outermost
    -- hypothesis H₀ attaches leftmost and hangs lowest.  Conjunction is only
    -- ever drawn as a fork, never as hypotheses sharing a stroke.
    let n := hyps.length
    let xc := x + STUB * n.toF
    let mut out := line x xc
    let (_, _, dn) := measure o concl
    out := out ++ draw concl xc y col (extendAll env ⟨xc, y⟩) o
    let mut cur := dn
    for (i, h) in ((List.range n).zip hyps).reverse do
      let xj := x + STUB * (i + 1).toF
      let (_, uh, dh) := measure o h
      let yh := y + cur + 12.0 + o.gap + uh
      out := out ++ draw h xj yh (flipCol col) (extendAll (extendAll env ⟨xj, y⟩) ⟨xj, yh⟩) o
      out := out ++ sh (stroke #[⟨xj, y⟩, ⟨xj, yh⟩] .R (flipCol col) 1.3)
      cur := (yh - y) + dh
    return out
  | .and parts => fork false parts
  | .or parts => fork true parts
where
  /-- A fork: the stroke ends in a junction dot, and a straight ray runs from
  it to the start of each part; no part continues the main stroke.  For a
  disjunction the dot is hollow and an arc closes the fan near the junction. -/
  fork (isOr : Bool) (parts : List Tree) : Array Mark := Id.run do
    let xj := x + STUB
    let mut out := sh (stroke #[⟨x, y⟩, ⟨xj, y⟩] .R col 1.3)
    let ms := parts.map (measure o)
    let tot := pySum (ms.map fun (_, u, d) => u + d) + (10.0 + o.gap) * (parts.length - 1).toF
    let mut yy := y - tot / 2.0
    let mut ends : Array Float := #[]
    for (p, (_, up, dn)) in parts.zip ms do
      let yp := yy + up
      out := out ++ sh (stroke #[⟨xj, y⟩, ⟨xj + FORK, yp⟩] .R col 1.3)
      out := out ++ draw p (xj + FORK) yp col (extendAll (extendAll env ⟨xj, y⟩) ⟨xj + FORK, yp⟩) o
      ends := ends.push yp
      yy := yp + dn + 10.0 + o.gap
    if isOr then
      let r := 9.0
      let a0 := Float.atan2 (ends[0]! - y) FORK
      let a1 := Float.atan2 (ends.back! - y) FORK
      let pts := ((List.range 21).map fun i =>
        let a := a0 + (a1 - a0) * i.toFloat / 20.0
        (⟨xj + r * Float.cos a, y + r * Float.sin a⟩ : P)).toArray
      out := out ++ sh (stroke pts .R col 1.3)
      return out.push (.shape (.circle ⟨xj, y⟩ 2.6 "white" col))
    return out.push (.shape (.circle ⟨xj, y⟩ 2.2 col))

/-- A variant-B diagram: one formula tree, asserted with a judgement stroke. -/
structure TreeDiagram where
  name : String
  tree : Tree

/-- The state names of a tree not bound by any of its notches, in order. -/
partial def Tree.free (bound : List String := []) : Tree → List String
  | .leaf s steps => ((s :: steps.map (·.2)).map bare).filter (!bound.contains ·)
  | .text _ => []
  | .q _ v b => b.free (v :: bound)
  | .neg b => b.free bound
  | .cond c hs => (c :: hs).foldl (fun acc t => acc ++ t.free bound) []
  | .and ps | .or ps => ps.foldl (fun acc t => acc ++ t.free bound) []


/-- All orderings of a list. -/
partial def perms : List Nat → List (List Nat)
  | [] => [[]]
  | xs => xs.flatMap fun x => (perms (xs.erase x)).map (x :: ·)

/-- The binder names of a tree, in order, without repeats. -/
partial def Tree.binders : Tree → List String
  | .leaf .. | .text _ => []
  | .q _ v b => v :: (b.binders.filter (· != v))
  | .neg b => b.binders
  | .cond c hs => (c :: hs).foldl (fun acc t => acc ++ (t.binders.filter (!acc.contains ·))) []
  | .and ps | .or ps => ps.foldl (fun acc t => acc ++ (t.binders.filter (!acc.contains ·))) []

/-- Lay out a tree: the marks it draws, and the geometry `(x0, y, w, up, dn)`
(stroke start, stroke height, width, extent above and below). -/
def TreeDiagram.layout (d : TreeDiagram) (o : DrawOpts) :
    Array Mark × Float × Float × Float × Float × Float :=
  let (w, up, dn) := measure o d.tree
  let y := up + 12.0 + (if o.links then 10.0 else 0.0)
  let x0 := if o.links then 26.0 else 14.0
  let free := (d.tree.free).foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []
  let o := { o with root := ⟨x0, y⟩, free }
  (sh (stroke #[⟨x0, y - 9.0⟩, ⟨x0, y + 9.0⟩] .R BLACK 2.0) ++ draw d.tree x0 y RED [] o, x0, y, w, up, dn)

end FregeDiagrams
