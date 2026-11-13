/-
FregeDiagrams.SpecB: the reference for view B (docs/design/NEXT-STAGE.md §3.3.1).

View B is the canonical picture, so its reference is a **reader**: `readB`
reconstructs the formula from the scene alone, the shapes as drawn
(`Rendered.scene`, of which the SVG is a transcript), read the way Frege's
strokes are read.  It uses geometry and the visible style of the ink (stroke
width, colour, dash, fill), never the renderer's ids, block paths or drawing
order.  The relation drawn by a stretch is recognised by the figure's legend:
the style `stroke` gives each relation under the figure's `dash` hints.

The properties tested (`Fig.checkB`):

* B5 adequacy — names shown, no links: `readB (sceneB f) = nf f.shown`, with
  the judgement and the defined name, where `nf` makes the three
  identifications of the notation (currying, free states infallible, meanings
  of texts dropped);
* B3 links — names shown, links: the binding read from the link trees equals
  the binding of the formula (compared after renaming every bound name to its
  binder, `canon`);
* B3′ hidden — links, names hidden: the same, so the formula is recovered up
  to renaming of bound names.
-/
import FregeDiagrams.View
import FregeDiagrams.Syntax

namespace FregeDiagrams.SpecB

/-! ## The scene, sorted by kind of ink -/

/-- The scene of view B, its shapes sorted by what kind of ink they are. -/
structure SceneB where
  /-- the strokes of the tree: content and condition strokes, negation
  ticks, fork rays and arcs (width 1.3, red or black) -/
  strokes : Array Polyline := #[]
  /-- the judgement bars (width 2.0) -/
  bars : Array Polyline := #[]
  /-- every other line: relation stretches, loops, notches, strikes:
  points, width, attributes -/
  ink : Array (Polyline × String × String) := #[]
  /-- the links (width 1.9): points, colour, attributes -/
  links : Array (Polyline × String × String) := #[]
  /-- arrowheads -/
  heads : Array Polyline := #[]
  /-- centre, radius, fill, outline -/
  circles : Array (P × Float × String × String) := #[]
  /-- position, text, size, anchor -/
  texts : Array (P × String × Nat × String) := #[]
deriving Inhabited

def SceneB.ofShapes (shapes : Array Shape) : SceneB := Id.run do
  let mut sc : SceneB := {}
  for s in shapes do
    match s with
    | .poly pts c w a =>
      if w == pyRepr 1.3 && (c == RED || c == BLACK) then sc := { sc with strokes := sc.strokes.push pts }
      else if w == pyRepr 2.0 then sc := { sc with bars := sc.bars.push pts }
      else if w == "1.9" then sc := { sc with links := sc.links.push (pts, c, a) }
      else sc := { sc with ink := sc.ink.push (pts, w, a) }
    | .polygon pts _ => sc := { sc with heads := sc.heads.push pts }
    | .circle c r f st _ => sc := { sc with circles := sc.circles.push (c, r, f, st) }
    | .text p t _ sz a _ => sc := { sc with texts := sc.texts.push (p, t, sz, a) }
    | .raw _ => pure ()
  return sc

/-! ## Geometry -/

def EPS : Float := 0.05
def close (a b : Float) (e : Float := EPS) : Bool := (a - b).abs < e
def near (p q : P) (e : Float := EPS) : Bool := close p.x q.x e && close p.y q.y e
def xs (pts : Polyline) : Array Float := pts.map (·.x)
def ys (pts : Polyline) : Array Float := pts.map (·.y)
def amin (a : Array Float) : Float := a.foldl min (a[0]!)
def amax (a : Array Float) : Float := a.foldl max (a[0]!)

/-- A two-point stroke, as `(left or top end, other end)`. -/
def ends (pts : Polyline) : P × P := (pts[0]!, pts.back!)

def isHoriz (pts : Polyline) : Bool := pts.size == 2 && close pts[0]!.y pts[1]!.y && !close pts[0]!.x pts[1]!.x
def isVert (pts : Polyline) : Bool := pts.size == 2 && close pts[0]!.x pts[1]!.x && !close pts[0]!.y pts[1]!.y

/-- The horizontal strokes at height `y`, as `(x0, x1)` with `x0 < x1`. -/
def SceneB.horizAt (sc : SceneB) (y : Float) : Array (Float × Float) :=
  sc.strokes.filterMap fun pts =>
    if isHoriz pts && close pts[0]!.y y then
      some (min pts[0]!.x pts[1]!.x, max pts[0]!.x pts[1]!.x) else none

/-- Is `p` an end of a horizontal stroke? -/
def SceneB.strokeEndAt (sc : SceneB) (p : P) : Bool :=
  sc.strokes.any fun pts => isHoriz pts && (near pts[0]! p || near pts[1]! p)

/-- A quantifier notch: its ends on the stroke, its kind, the point where its
links start (the middle of its own line), and its name. -/
structure Notch where
  a : P
  b : P
  kind : Quant
  root : P
  name : String
deriving Inhabited

/-- The notches: lines of three or four points whose ends are ends of
horizontal strokes at one height; the name is the text inside. -/
def SceneB.notches (sc : SceneB) : Array Notch :=
  sc.ink.filterMap fun (pts, _, _) =>
    if (pts.size == 3 || pts.size == 4) && close pts[0]!.y pts.back!.y &&
        sc.strokeEndAt pts[0]! && sc.strokeEndAt pts.back! then
      let (a, b) := if pts[0]!.x ≤ pts.back!.x then (pts[0]!, pts.back!) else (pts.back!, pts[0]!)
      let kind := if pts.size == 4 then Quant.all else .ex
      let root : P := if pts.size == 4 then (pts[1]! + pts[2]!) * 0.5 else pts[1]!
      let y0 := min a.y root.y; let y1 := max a.y root.y
      let name := (sc.texts.find? fun (p, _, sz, anc) =>
        sz == 12 && anc == "middle" && p.x > a.x && p.x < b.x && p.y > y0 && p.y < y1 + 6.0).map (·.2.1)
      some { a, b, kind, root, name := name.getD "" }
    else none

def isNotchInk (ns : Array Notch) (pts : Polyline) : Bool :=
  (pts.size == 3 || pts.size == 4) && ns.any fun n => near n.a pts[0]! || near n.a pts.back!

/-! ## Reading -/

/-- What the reader is told besides the scene: the figure's legend (its
`dash` table), and whether links are drawn and names hidden. -/
structure ReadOpts where
  relDash : List (Rel × String) := []
  links : Bool := false
  hideBound : Bool := false
deriving Inhabited

/-- What `readB` reads: the judgement, the name a definition defines, the
formula, and the places where the picture admits more than one reading. -/
structure Reading where
  judgement : Judgement
  defines : Option String
  form : Form
deriving Inhabited

abbrev R := ExceptT String (StateM (Array String))

def ambiguous (msg : String) : R Unit := modify (·.push msg)

/-- The style signature of the lines a relation draws: (width, attributes),
sorted, and whether it waves. -/
def signature (lines : Array (Polyline × String × String)) : List (String × String) :=
  (lines.toList.map fun (_, w, a) => (w, a)).mergeSort fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)

def styleOf (tbl : List (Rel × String)) (r : Rel) : List (String × String) :=
  let line : Polyline := (List.range 41).toArray.map fun i => ⟨i.toFloat, 0.0⟩
  let ls := (stroke line r "c" (dash := relDashFor tbl r)).filterMap fun
    | .poly pts _ w a => some (pts, w, a) | _ => none
  signature ls

/-- Does a line wave (the style of `⇝`)?  It turns left and right in
alternation: its turns change sign several times (a curved loop, or a
straight line with a kink, does not). -/
def waves (pts : Polyline) : Bool := Id.run do
  let mut prev := 0.0
  let mut changes := 0
  for i in [1:pts.size - 1] do
    let u := pts[i]! - pts[i-1]!; let v := pts[i+1]! - pts[i]!
    let t := u.x * v.y - u.y * v.x
    if t.abs < 1.0e-3 then continue
    if prev != 0.0 && (t > 0.0) != (prev > 0.0) then changes := changes + 1
    prev := t
  return changes ≥ 4

def beaded (r : Rel) : Bool := r == .sqle || r == .Rinf

/-- Of the relations drawn in one style, the one a stretch is read as:
inside an arrow the bead decides between `≤` and `⊑` (`R` and `R°`); at
its end, where no bead is drawn, the plain one (the state shows the `°`). -/
def pickRel (cands : List Rel) (bead : Option Bool) : Option Rel :=
  let pref := match bead with
    | some b => cands.filter (beaded · == b)
    | none => cands.filter (!beaded ·)
  (if pref.isEmpty then cands else pref).head?

/-- The basic relation drawn by the lines of one stretch, `bead` whether a
hollow bead ends it, `label` the label drawn at its middle. -/
def readStretch (o : ReadOpts) (lines : Array (Polyline × String × String)) (bead : Bool)
    (label : Option String) (directed final : Bool) : R Rel := do
  let sig := signature lines
  let wavy := lines.any fun (pts, _, _) => waves pts
  let named : List Rel := match label with | some l => [.named l directed] | none => []
  let cands := ([Rel.le, .sqle, .R, .Rinf, .reach, .eq, .ne] ++ named).filter fun r =>
    styleOf o.relDash r == sig && (r == .reach) == wavy
  let some r := pickRel cands (if final then none else some bead)
    | throw s!"a stretch in no relation's style: {sig}"
  if (cands.filter fun q => beaded q == beaded r).length > 1 then
    ambiguous s!"the legend draws {cands.map Rel.syntax} alike"
  return r

/-- The name of a state drawn at `c`, where the leaf puts it: above, beside a
looped state, or below a state with two loops. -/
def SceneB.nameAt (sc : SceneB) (c : P) : Option String :=
  (sc.texts.find? fun (p, _, sz, anc) => sz == 12 &&
    ((anc == "middle" && (near p ⟨c.x, c.y - 9.0⟩ || near p ⟨c.x, c.y + 18.0⟩)) ||
     (anc == "start" && near p ⟨c.x + 9.0, c.y + 4.0⟩))).map (·.2.1)

/-- The state circles (radius `NODE_R`) at height `y`, left to right: centre
and hollowness. -/
def SceneB.statesAt (sc : SceneB) (y : Float) : Array (P × Bool) :=
  let cs := sc.circles.filterMap fun (c, r, f, _) =>
    if close r NODE_R && close c.y y then some (c, f == "white") else none
  cs.qsort (·.1.x < ·.1.x)

/-- For links: which notch (an index) the link tree touching a state at `c`
starts at, if any. -/
def bindingAt (ports : Array (P × Nat)) (c : P) : Option Nat :=
  (ports.find? fun (p, _) => (p - c).len < NODE_R + 2.5).map (·.2)

/-- The state at `c`: its name and `°`.  With links, a state a link tree
reaches is named by that tree's notch (`#k`); the others are free and named
by their text. -/
def readState (sc : SceneB) (o : ReadOpts) (ports : Array (P × Nat)) (c : P) (hollow : Bool) : R St := do
  if o.links then
    if let some k := bindingAt ports c then return { name := s!"#{k}", inf := hollow }
  match sc.nameAt c with
  | some n => return { name := n, inf := hollow }
  | none => throw s!"a state at ({fmt1 c.x}, {fmt1 c.y}) without a name"

/-- Read a composite relation from its lines: `param` places a point along
the arrow (or loop), `headed` says whether the arrow ends in a head.  Lines
covering the same stretch (the two lines of `=`, the strike of `≠`) are one
stretch; stretches follow each other along the arrow, a hollow bead at the
end of one marking `⊑` or `R°`. -/
def readComposite (sc : SceneB) (o : ReadOpts) (lines : Array (Polyline × String × String))
    (param : P → Float) (headed : Bool) : R Composite := do
  let span (pts : Polyline) : Float × Float :=
    let ps := pts.map param
    (amin ps, amax ps)
  let sorted := lines.qsort fun p q => (span p.1).1 < (span q.1).1
  -- (lines, start, end) of each stretch
  let mut groups : Array (Array (Polyline × String × String) × Float × Float) := #[]
  for l in sorted do
    let (a, b) := span l.1
    match groups.back? with
    | some (g, ga, gb) =>
      let ov := min b gb - max a ga
      if ov > 0.5 * min (b - a) (gb - ga) then
        groups := groups.pop.push (g.push l, min a ga, max b gb)
      else groups := groups.push (#[l], a, b)
    | none => groups := groups.push (#[l], a, b)
  let mut comp : Composite := []
  for ((g, _, _), i) in groups.zip (List.range groups.size).toArray do
    let last := i + 1 == groups.size
    -- the points of the stretch at its far end
    let endPts := g.map fun (pts, _, _) => if param pts[0]! > param pts.back! then pts[0]! else pts.back!
    let bead := !last && sc.circles.any fun (q, r, f, _) =>
      close r 3.2 && f == "white" && endPts.any fun p => (p - q).len < 2.0
    let mid := (g[0]!.1)[g[0]!.1.size / 2]!
    let label := (sc.texts.find? fun (p, _, sz, _) => sz == 11 && (p - mid).len < 10.0).map (·.2.1)
    comp := comp ++ [← readStretch o g bead label (last && headed) last]
  return comp

/-- Read the relation of a loop on the state at `c`, ending in the head at
`tip`, from its lines: its stretches follow each other end to end from its
first foot (the end of its lines nearest the state, away from the head);
the lines of one stretch (the two of `=`) start together, a strike crosses
the stretch nearest it, and a hollow bead at the end of a stretch marks `⊑`
or `R°`. -/
def readLoop (sc : SceneB) (o : ReadOpts) (c tip : P) (ls : Array (Polyline × String × String)) :
    R Composite := do
  let lines := ls.filter (·.1.size > 2)
  let strikes := ls.filter (·.1.size == 2)
  let endsOf (pts : Polyline) : List P := [pts[0]!, pts.back!]
  let feet := (lines.toList.flatMap fun l => endsOf l.1).filter fun e => (e - tip).len > 2.05
  let some foot := feet.foldl (fun (m : Option P) e => match m with
      | some q => if (e - c).len < (q - c).len then some e else m
      | none => some e) none
    | throw s!"a loop at ({fmt1 c.x}, {fmt1 c.y}) with no lines"
  let dist (cur : List P) (e : P) : Float := cur.foldl (fun m q => min m (e - q).len) 1.0e9
  let mut rest := List.range lines.size
  -- the two lines of a `=` start apart: every end close to the first foot
  let mut cur : List P := feet.filter fun e => (e - foot).len < 4.0
  let mut groups : Array (List Nat × List P) := #[]
  for _ in [0:lines.size] do
    -- the lines ending at the head are the last stretch's
    let atHead (i : Nat) := (endsOf lines[i]!.1).any fun e => (e - tip).len < 2.05
    let g := rest.filter fun i => (endsOf lines[i]!.1).any (dist cur · < 3.6) &&
      (!atHead i || rest.all atHead)
    if g.isEmpty then break
    rest := rest.filter (!g.contains ·)
    let farEnds := g.map fun i =>
      let a := lines[i]!.1[0]!; let b := lines[i]!.1.back!
      if dist cur a ≤ dist cur b then b else a
    groups := groups.push (g, farEnds)
    cur := farEnds
  if !rest.isEmpty then
    let showL (i : Nat) := let l := lines[i]!.1; s!"({fmt1 l[0]!.x},{fmt1 l[0]!.y})–({fmt1 l.back!.x},{fmt1 l.back!.y})"
    throw s!"a loop at ({fmt1 c.x}, {fmt1 c.y}) whose lines do not join end to end: from ({fmt1 foot.x},{fmt1 foot.y}), left {rest.map showL}"
  let near (g : List Nat) (q : P) : Float :=
    g.foldl (fun m i => min m (dist lines[i]!.1.toList q)) 1.0e9
  let mut comp : Composite := []
  for ((g, farEnds), k) in groups.zip (List.range groups.size).toArray do
    let last := k + 1 == groups.size
    let mine := strikes.filter fun l =>
      let m := (l.1[0]! + l.1[1]!) * 0.5
      groups.all fun (h, _) => near g m ≤ near h m
    let bead := !last && sc.circles.any fun (q, r, f, _) =>
      close r 3.2 && f == "white" && farEnds.any fun e => (e - q).len < 2.0
    let first := lines[g.head!]!.1
    let mid := first[first.size / 2]!
    let label := (sc.texts.find? fun (p, _, sz, _) => sz == 11 && (p - mid).len < 10.0).map (·.2.1)
    comp := comp ++ [← readStretch o (g.toArray.map (lines[·]!) ++ mine) bead label last last]
  return comp

/-- Read a leaf chain starting with the state at `c0`. -/
def readLeaf (sc : SceneB) (o : ReadOpts) (ns : Array Notch) (ports : Array (P × Nat))
    (c0 : P × Bool) : R Form := do
  let y := c0.1.y
  let row := sc.statesAt y
  let ink := sc.ink.filter fun (pts, _, _) => !isNotchInk ns pts
  let st0 ← readState sc o ports c0.1 c0.2
  let mut steps : Array (Composite × St) := #[]
  let mut cur := c0
  let mut curSt := st0
  for _ in [0:row.size + 1] do
    let c := cur.1
    -- loops on this state: each ends in an arrowhead at the state; a line of
    -- a loop is the one whose middle is nearest this state, off the line of
    -- the arrows; it belongs to the loop whose head is next clockwise from
    -- its farthest point
    let ang (p : P) : Float := Float.atan2 (p.x - c.x) (c.y - p.y) * 180.0 / 3.141592653589793
    let cw (a b : Float) : Float := let d := b - a; if d < 0.0 then d + 360.0 else d
    let tips := (sc.heads.map (·[0]!)).filter fun t =>
      (t - c).len > 5.5 && (t - c).len < 8.5 && (t.y - c.y).abs > 2.0
    let mean (pts : Polyline) : P := (pts.foldl (· + ·) (⟨0.0, 0.0⟩ : P)) * (1.0 / pts.size.toFloat)
    let nearestIsC (q : P) : Bool := row.all fun (d, _) => (q - c).len ≤ (q - d).len + EPS
    -- the lines of its loops: from its feet, joined end to end away from it
    let offLine := (List.range ink.size).filter fun i =>
      let pts := ink[i]!.1
      pts.size > 2 && (mean pts - c).len < 36.0 && nearestIsC (mean pts) && pts.any fun q => (q.y - c.y).abs > 7.5
    let ends (i : Nat) : List P := [ink[i]!.1[0]!, ink[i]!.1.back!]
    let mut taken := offLine.filter fun i => (ends i).any fun e => (e - c).len < 9.5
    let mut frontier : List P := taken.flatMap ends |>.filter fun e => (e - c).len ≥ 10.0
    for _ in [0:ink.size] do
      let more := offLine.filter fun i => !taken.contains i &&
        (ends i).any fun e => frontier.any fun f => (e - f).len < 2.5
      if more.isEmpty then break
      taken := taken ++ more
      frontier := more.flatMap ends |>.filter fun e => (e - c).len ≥ 10.0
    let lines := taken.toArray.map (ink[·]!)
    let strikes := ink.filter fun (pts, _, _) => pts.size == 2 &&
      lines.any fun (q, _, _) => q.any fun v => (v - (pts[0]! + pts[1]!) * 0.5).len < 3.0
    if !tips.isEmpty then
      for t in tips do
        if (tips.filter fun u => (u - t).len < 1.0).size > 1 then
          throw s!"loops on the state at ({fmt1 c.x}, {fmt1 c.y}) drawn on top of each other"
      let owner (q : P) : Nat := Id.run do
        let mut best := 0
        for k in [0:tips.size] do
          if cw (ang q - 8.0) (ang tips[k]!) < cw (ang q - 8.0) (ang tips[best]!) then best := k
        return best
      let far (pts : Polyline) : P := pts.foldl (fun m q => if (q - c).len > (m - c).len then q else m) pts[0]!
      let mut loops : Array (P × Array (Polyline × String × String)) := tips.map fun t => (t, #[])
      for l in lines do loops := loops.modify (owner (far l.1)) fun (t, ls) => (t, ls.push l)
      for l in strikes do loops := loops.modify (owner ((l.1[0]! + l.1[1]!) * 0.5)) fun (t, ls) => (t, ls.push l)
      -- read above the line first, then below, each left to right
      let axis (ls : Array (Polyline × String × String)) : P :=
        (ls.foldl (fun (acc : P) l => acc + mean l.1) (⟨0.0, 0.0⟩ : P)) * (1.0 / (max 1 ls.size).toFloat) - c
      let order := loops.filter (!·.2.isEmpty) |>.qsort fun a b =>
        let p := axis a.2; let q := axis b.2
        if (p.y < 0.0) != (q.y < 0.0) then p.y < 0.0 else p.x < q.x
      if order.size != tips.size then throw s!"a loop head at ({fmt1 c.x}, {fmt1 c.y}) with no loop"
      for (t, ls) in order do
        steps := steps.push (← readLoop sc o c t ls, curSt)
    -- the next state: the stretches from this one to it
    let starts := ink.any fun (pts, _, _) =>
      close (amin (xs pts)) (c.x + NODE_R + 2.0) 1.0 && (pts[0]!.y - c.y).abs < 3.0
    let some nxt := row.find? (·.1.x > c.x + EPS) | break
    if !starts then break
    let x0 := c.x + NODE_R + 1.0
    let x1 := nxt.1.x - NODE_R - 1.0
    let between := ink.filter fun (pts, _, _) =>
      amin (xs pts) ≥ x0 && amax (xs pts) ≤ x1 && (amin (ys pts) - c.y).abs < 7.5 && (amax (ys pts) - c.y).abs < 7.5
    if between.isEmpty then throw s!"a state at ({fmt1 nxt.1.x}, {fmt1 y}) with no arrow into it"
    let headed := sc.heads.any fun h => (h[0]! - ⟨nxt.1.x - NODE_R - 2.0, y⟩).len < 1.5
    let comp ← readComposite sc o between (·.x) headed
    let st ← readState sc o ports nxt.1 nxt.2
    steps := steps.push (comp, st)
    cur := nxt
    curSt := st
  return .chain st0 steps.toList

/-- `imp [h] rest`, curried: a condition on a condition is one `if` with
more hypotheses. -/
def mkImp (h : Form) : Form → Form
  | .imp hs c => .imp (h :: hs) c
  | c => .imp [h] c

/-- Read what the stroke from `p` rightwards says. -/
partial def walk (sc : SceneB) (o : ReadOpts) (ns : Array Notch) (ports : Array (P × Nat))
    (p : P) (fuel : Nat) : R Form := do
  if fuel == 0 then throw "the tree is too deep"
  let y := p.y
  let hs := sc.horizAt y
  let dotAt (q : P) := sc.circles.find? fun (c, r, _, _) => (close r 2.2 || close r 2.6) && near c q
  -- the stroke from p: the horizontal strokes at this height chained from p,
  -- stopping at a fork's junction
  let mut reach := p.x
  for _ in [0:hs.size + 1] do
    if (dotAt ⟨reach, y⟩).isSome && reach > p.x + EPS then break
    let ext := hs.filter fun (a, b) => a ≤ reach + EPS && b > reach + EPS
    if ext.isEmpty then break
    reach := ext.foldl (fun m (_, b) => max m b) reach
  if reach ≤ p.x + EPS then throw s!"no stroke at ({fmt1 p.x}, {fmt1 y})"
  -- the first thing hanging from it: a condition stroke or a negation tick
  let downs := sc.strokes.filter fun pts => isVert pts &&
    (let top := if pts[0]!.y < pts[1]!.y then pts[0]! else pts[1]!
     close top.y y && top.x > p.x + EPS && top.x ≤ reach + EPS)
  let downs := downs.qsort fun a b => a[0]!.x < b[0]!.x
  if h : downs.size > 0 then
    let v := downs[0]
    let (top, bot) := if v[0]!.y < v[1]!.y then (v[0]!, v[1]!) else (v[1]!, v[0]!)
    let rest ← walk sc o ns ports top (fuel - 1)
    if sc.strokeEndAt bot then
      let hyp ← walk sc o ns ports bot (fuel - 1)
      return mkImp hyp rest
    else
      return .not rest
  let e : P := ⟨reach, y⟩
  -- a notch
  if let some n := ns.find? fun n => near n.a e then
    let body ← walk sc o ns ports n.b (fuel - 1)
    let k := (ns.findIdx? fun m => near m.a n.a).getD 0
    let x := if o.links then s!"#{k}" else n.name
    return if n.kind == .all then .all x body else .ex x body
  -- a fork
  if let some (c, r, _, _) := dotAt e then
    let rays := sc.strokes.filter fun pts => pts.size == 2 &&
      ((near pts[0]! c && pts[1]!.x > c.x + EPS) || (near pts[1]! c && pts[0]!.x > c.x + EPS))
    let tips := (rays.map fun pts => if near pts[0]! c then pts[1]! else pts[0]!).qsort (·.y < ·.y)
    let parts ← tips.toList.mapM fun t => walk sc o ns ports t (fuel - 1)
    if parts.length < 2 then throw s!"a fork at ({fmt1 c.x}, {fmt1 c.y}) with {parts.length} part(s)"
    return if close r 2.6 then .or parts else .and parts
  -- a leaf: a chain
  if let some c := (sc.statesAt y).find? fun (c, _) => c.x > reach && c.x ≤ reach + 12.0 then
    return ← readLeaf sc o ns ports c
  -- a leaf: a text
  if let some (_, t, _, _) := sc.texts.find? fun (q, _, sz, anc) =>
      sz == 12 && anc == "start" && near q ⟨reach + 4.0, y + 4.2⟩ then
    return .text t none
  throw s!"the stroke ends at ({fmt1 reach}, {fmt1 y}) in nothing readable"

/-- The link trees: link lines of one style joined at their ends.  For each
tree, the notch it starts at (an index into `ns`) and the other points it
reaches.  A tree touching no notch, or more than one, is an error. -/
def linkPorts (sc : SceneB) (ns : Array Notch) : R (Array (P × Nat)) := do
  let ls := sc.links
  -- union-find by shared ends, within one style
  let mut comp : Array Nat := (List.range ls.size).toArray
  let find (comp : Array Nat) (i : Nat) : Nat := Id.run do
    let mut j := i
    for _ in [0:comp.size] do
      if comp[j]! == j then break
      j := comp[j]!
    return j
  for i in [0:ls.size] do
    for j in [i+1:ls.size] do
      let (a, ca, aa) := ls[i]!; let (b, cb, ab) := ls[j]!
      if ca == cb && aa == ab &&
          [a[0]!, a.back!].any (fun p => [b[0]!, b.back!].any fun q => near p q 0.5) then
        let ri := find comp i; let rj := find comp j
        if ri != rj then comp := comp.set! ri rj
  let roots := (List.range ls.size).map (find comp ·) |>.eraseDups
  let mut out : Array (P × Nat) := #[]
  for r in roots do
    let mine := (List.range ls.size).filter (find comp · == r)
    let pts := mine.foldl (fun acc i => acc ++ [ls[i]!.1[0]!, ls[i]!.1.back!]) []
    let hits := (List.range ns.size).filter fun k => pts.any fun p => near p ns[k]!.root 0.5
    match hits with
    | [k] => out := out ++ (pts.toArray.map (·, k))
    | [] => throw "a link tree that starts at no notch"
    | _ => throw "a link tree that touches several notches"
  return out

/-- Read a scene of view B. -/
def readB (shapes : Array Shape) (o : ReadOpts := {}) : Except String Reading × Array String :=
  let sc := SceneB.ofShapes shapes
  let run : R Reading := do
    let ns := sc.notches
    let ports ← if o.links then linkPorts sc ns else pure #[]
    let bars := (sc.bars.filter isVert).qsort (·[0]!.x < ·[0]!.x)
    let judgement := match bars.size with | 0 => Judgement.content | 1 => .claim | _ => .definition
    let root : P ← match bars.back? with
      | some b => pure ⟨b[0]!.x, (b[0]!.y + b[1]!.y) / 2.0⟩
      | none =>
        let hs := sc.strokes.filter isHoriz
        if hs.isEmpty then throw "no stroke"
        let l := hs.foldl (fun (m : P) pts =>
          let q := if pts[0]!.x ≤ pts[1]!.x then pts[0]! else pts[1]!
          if q.x < m.x then q else m) ⟨1.0e9, 0.0⟩
        pure l
    let defines := (sc.texts.find? fun (_, t, _, anc) => anc == "end" && t.endsWith " :≡").map fun (_, t, _, _) =>
      String.ofList (t.toList.take (t.length - 3))
    let form ← walk sc o ns ports root 400
    return { judgement, defines, form }
  let (r, amb) := (run.run).run #[]
  (r, amb)

/-! ## What the picture must say -/

/-- The relation `r` is read as, by the figure's legend (`pickRel` among
the relations drawn in its style); `final` at the end of an arrow.  With the
default legend this is `r`, except that a final `⊑` or `R°` is `≤` or `R`
(into a hollow state). -/
def legendRel (tbl : List (Rel × String)) (final : Bool) (r : Rel) : Rel :=
  match r with
  | .named .. => r
  | _ =>
    let cands := [Rel.le, .sqle, .R, .Rinf, .reach, .eq, .ne].filter fun q =>
      styleOf tbl q == styleOf tbl r && (q == .reach) == (r == .reach)
    (pickRel cands (if final then none else some (beaded r))).getD r

/-- The formula up to the identifications of view B: nested conditions
curried into one, free states infallible (`°`), meanings of texts dropped;
names as displayed (`'` as `′`).  Two consequences of drawing are also
normalised: the occurrences of a state on one circle (a loop) share its `°`,
and relations the figure's legend draws alike are one (`legendRel`). -/
partial def nf (bound : List String := []) (tbl : List (Rel × String) := []) : Form → Form
  | .chain st steps =>
    let fix (s : St) : St := let n := dispName s.name; { name := n, inf := s.inf || !bound.contains n }
    -- an arrow ending in `⊑` (`R°`) ends in an infallible state
    let sts := (st :: steps.map fun (r, t) => if beaded r.getLast! then { t with inf := true } else t).toArray.map fix
    let rels (r : Composite) : Composite :=
      (r.zip (List.range r.length)).map fun (q, i) => legendRel tbl (i + 1 == r.length) q
    -- runs of the same state (loops) share their `°`
    let sts := sts.mapIdx fun i s => Id.run do
      let mut j := i
      while j > 0 && sts[j-1]!.name == s.name do j := j - 1
      let mut k := i
      while k + 1 < sts.size && sts[k+1]!.name == s.name do k := k + 1
      return { s with inf := (List.range (k + 1 - j)).any fun d => sts[j + d]!.inf }
    .chain sts[0]! ((steps.zip (List.range steps.length)).map fun ((r, _), i) =>
      (rels r, sts[i + 1]!))
  | .text s _ => .text s none
  | .all x b => .all (dispName x) (nf (dispName x :: bound) tbl b)
  | .ex x b => .ex (dispName x) (nf (dispName x :: bound) tbl b)
  | .not b => .not (nf bound tbl b)
  | .imp hs c =>
    let hs := hs.map (nf bound tbl)
    match nf bound tbl c with
    | .imp hs' c' => .imp (hs ++ hs') c'
    | c' => if hs.isEmpty then c' else .imp hs c'
  | .and ps => .and (ps.map (nf bound tbl))
  | .or ps => .or (ps.map (nf bound tbl))

/-- Every bound name renamed to its binder, numbered in the order the
formula is written (`#0`, `#1`, …); free names kept. -/
partial def canon (f : Form) : Form := (go [] f).run' 0
where
  go (env : List (String × String)) : Form → StateM Nat Form
    | .chain st steps => do
      let r (s : St) : St := { s with name := (env.lookup s.name).getD s.name }
      return .chain (r st) (steps.map fun (c, t) => (c, r t))
    | .text s m => return .text s m
    | .all x b => do let k ← getModify (· + 1); return .all s!"#{k}" (← go ((x, s!"#{k}") :: env) b)
    | .ex x b => do let k ← getModify (· + 1); return .ex s!"#{k}" (← go ((x, s!"#{k}") :: env) b)
    | .not b => return .not (← go env b)
    | .imp hs c => return .imp (← hs.mapM (go env)) (← go env c)
    | .and ps => return .and (← ps.mapM (go env))
    | .or ps => return .or (← ps.mapM (go env))

/-- The first place where two formulas differ, as a short description. -/
partial def firstDiff : Form → Form → Option String
  | .chain s ss, .chain t ts =>
    if s != t then some s!"state {s.print} read as {t.print}" else
    if ss.length != ts.length then some s!"a chain of {ss.length} steps read as {ts.length}" else
    (ss.zip ts).findSome? fun ((r, a), (q, b)) =>
      if r != q then some s!"relation {compPrint r} read as {compPrint q}"
      else if a != b then some s!"state {a.print} read as {b.print}" else none
  | .text a _, .text b _ => if a != b then some s!"text {a} read as {b}" else none
  | .all x a, .all y b | .ex x a, .ex y b => if x != y then some s!"binder {x} read as {y}" else firstDiff a b
  | .not a, .not b => firstDiff a b
  | .imp hs c, .imp ks d =>
    if hs.length != ks.length then some s!"an if with {hs.length} hypotheses read with {ks.length}" else
    ((hs.zip ks).findSome? fun (h, k) => firstDiff h k).orElse fun _ => firstDiff c d
  | .and ps, .and qs | .or ps, .or qs =>
    if ps.length != qs.length then some s!"a fork of {ps.length} read as {qs.length}" else
    (ps.zip qs).findSome? fun (p, q) => firstDiff p q
  | a, b => if a == b then none else
    let k : Form → String
      | .chain .. => "chain" | .text .. => "text" | .all .. => "all" | .ex .. => "ex"
      | .not .. => "not" | .imp .. => "if" | .and .. => "&" | .or .. => "|"
    some s!"{k a} read as {k b}"

end SpecB

open SpecB in
/-- The violations of B5, B3 and B3′ in view B of a figure, and the
ambiguities of its legend, as messages. -/
def Fig.checkB (d : Fig) (o : DrawOpts := {}) : List String := Id.run do
  if d.hints.views == .a then return []
  let mut out : List String := []
  for (links, hide, tag) in [(false, false, "B5"), (true, false, "B3"), (true, true, "B3′")] do
    let o' := d.drawOpts { o with links, hideBound := hide }
    let want := nf [] o'.relDash d.shown
    let r := d.toTreeDiagram.render o'
    let (res, amb) := readB r.scene { relDash := o'.relDash, links, hideBound := hide }
    -- the legend drawing two relations alike is the figure's choice, not a
    -- violation; several loops on one state are
    out := out ++ (amb.toList.eraseDups.filter (!·.startsWith "the legend") |>.map fun m => s!"{tag} ambiguous: {m}")
    match res with
    | .error e => out := out ++ [s!"{tag} unreadable: {e}"]
    | .ok rd =>
      if rd.judgement != d.hints.judgement then
        out := out ++ [s!"{tag} judgement: the figure has {repr d.hints.judgement}, the picture {repr rd.judgement}"]
      if rd.defines != d.defines then
        out := out ++ [s!"{tag} defines: the figure has {d.defines}, the picture {rd.defines}"]
      let (w, g) := if links then (canon want, canon rd.form) else (want, rd.form)
      if w != g then
        out := out ++ [s!"{tag} formula, {(firstDiff w g).getD "?"}: the figure has {w.print}, the picture says {g.print}"]
  return out

end FregeDiagrams
