/-
FregeDiagrams.Route.Router: the binding links of view B, as one Steiner tree per
binder, and the rendering of a view-B diagram.

The phases, each a function of its own:

1. **Layout** (`TreeDiagram.layout`, in `FregeDiagrams.Tree`) draws the tree as
   typed marks: shapes, bound occurrences, names still to place, leaf boxes.
   Which notches are flipped (`⊔` for `⊓`, `∧` for `∨`) is a layout parameter.
2. **Scene** (`Scene.ofMarks`): the obstacles, read from the shapes.
3. **Grid** (`Grid.build`): the routing graph.  Its lines are the lines
   through every terminal and its approach points, tracks just outside every
   leaf row, channels around the whole tree, and columns to its right; each
   grid point has a horizontal and a vertical node, joined by a bend edge.
   An edge costs its length, plus a penalty for each tree stroke it crosses
   or touches, each state or junction it passes, each name it runs through,
   and each stroke it runs along.
4. **Routing** (`routeAll`): each binder is joined to all its occurrences by
   an exact minimum Steiner tree in the grid (`Route.steiner`,
   Dreyfus–Wagner), against the trees of the other binders (a crossing with
   another binder's tree costs less than one with the tree, running along it
   much more).  A state is met from any free side: one not taken by a
   relation arrow or a loop.  Binders are routed in turn, then each is ripped
   up and routed again against the others, for a few rounds.  The flips are
   chosen by trying every choice (up to four binders).
5. **Names** (`placeNames`): each bound state's name goes to the first free
   place among a few around it.
6. **Output and checks** (`TreeDiagram.render`): the SVG, and the empty
   bigons and monogons left (`problems`), which `framediag --check` reports.
-/
import FregeDiagrams.Tree
import FregeDiagrams.Route.Steiner

namespace FregeDiagrams
open Route

/-! ## Costs

In effect lexicographic: crossings and obstacles (tens to hundreds) first;
bends, length, the room kept for names, scope nesting and flips (a few
units) only break ties.  Names can go anywhere around their states, so
their room only tips the balance. -/

def cLen : Float := 0.01
def cTree : Float := 100.0
def cLink : Float := 60.0
def cState : Float := 300.0
def cText : Float := 120.0
/-- running through the room kept for a state's name -/
def cName : Float := 3.0
/-- per unit length, for each step a link's outside track is off the rank
its scope asks for (innermost binder nearest the tree) -/
def cNest : Float := 0.03
def cAlong : Float := 400.0
def cAlongLink : Float := 250.0
def cBend : Float := 1.0
def cConn : Float := 1000.0
def cFlip : Float := 3.0
/-- How far from a state's centre a link's grid route ends; a short
connector reaches the circle. -/
def APP : Float := 7.2
def PROBE : Float := 14.0
def fTol : Float := 3.0
def fTouch : Float := 0.6
def fClear : Float := 2.5
def fNear : Float := 1.0

/-! ## Scene -/

structure Scene where
  /-- the spacing factor (`DrawOpts.spacing`) -/
  sp : Float := 1.0
  /-- room kept for the names placed after routing (their default places) -/
  soft : Array Box := #[]
  curves : Array Polyline := #[]
  cboxes : Array Box := #[]
  circles : Array (P × Float) := #[]
  texts : Array Box := #[]
  boxes : Array Box := #[]
  occs : Array Occ := #[]
  labels : Array Label := #[]
  shapes : Array Shape := #[]
deriving Inhabited

def Scene.ofMarks (ms : Array Mark) (sp : Float := 1.0) : Scene := Id.run do
  let mut sc : Scene := { sp }
  for m in ms do
    match m with
    | .shape s =>
      sc := { sc with shapes := sc.shapes.push s }
      match s with
      | .poly pts .. => sc := { sc with curves := sc.curves.push pts, cboxes := sc.cboxes.push (bbox pts) }
      | .polygon pts _ =>
        let c := pts.push pts[0]!
        sc := { sc with curves := sc.curves.push c, cboxes := sc.cboxes.push (bbox c) }
      | .circle c r .. => sc := { sc with circles := sc.circles.push (c, r) }
      | .text p s _ sz a _ => sc := { sc with texts := sc.texts.push (textBox p s a sz) }
      | .raw _ => pure ()
    | .occ o => sc := { sc with occs := sc.occs.push o }
    | .label l =>
      let (x0, y0, x1, y1) := if l.looped then textBox ⟨l.pos.x + 9.0, l.pos.y + 4.0⟩ l.text "start"
        else textBox ⟨l.pos.x, l.pos.y - 9.0⟩ l.text "middle"
      sc := { sc with labels := sc.labels.push l,
                      soft := sc.soft.push (x0 - 2.0 * sp, y0 - 2.0 * sp, x1 + 2.0 * sp, y1 + 2.0 * sp) }
    | .box x0 y0 x1 y1 => sc := { sc with boxes := sc.boxes.push (x0, y0, x1, y1) }
    | .bar pts => sc := { sc with curves := sc.curves.push pts, cboxes := sc.cboxes.push (bbox pts) }
  return sc

/-- The extent of everything drawn so far. -/
def Scene.extent (sc : Scene) : Box := Id.run do
  let mut b : Box := (fBig, fBig, -fBig, -fBig)
  let grow (b : Box) (c : Box) : Box :=
    (min b.1 c.1, min b.2.1 c.2.1, max b.2.2.1 c.2.2.1, max b.2.2.2 c.2.2.2)
  for c in sc.cboxes do b := grow b c
  for (p, r) in sc.circles do b := grow b (p.x - r, p.y - r, p.x + r, p.y + r)
  for t in sc.texts ++ sc.soft do b := grow b t
  return b

/-- How far from a state's centre a link's grid route ends (a short
connector reaches the circle), and the room kept clear around every other
state. -/
def Scene.app (sc : Scene) : Float := NODE_R + 3.0 + 3.0 * sc.sp
def Scene.halo (sc : Scene) : Float := 1.0 + 2.5 * sc.sp

/-- A binder: its name, the midpoint of its notch's own line, the outward
direction (`-1` up, `+1` down), its half width, and its occurrences. -/
structure Binder where
  name : String
  notch : P
  dir : Float
  hw : Float
  tgts : Array P
  /-- the number of binders whose scope contains this one's -/
  depth : Nat := 0
  /-- those binders, by their notch points -/
  encl : List P := []
deriving Inhabited

def Scene.binders (sc : Scene) : Array Binder := Id.run do
  let mut bs : Array Binder := #[]
  for o in sc.occs do
    match bs.findIdx? (fun b => (b.notch - o.notch).len < fHalf) with
    | some i =>
      if !bs[i]!.tgts.any (fun t => (t - o.tgt).len < fHalf) then
        bs := bs.modify i fun b => { b with tgts := b.tgts.push o.tgt }
    | none => bs := bs.push { name := o.name, notch := o.notch, dir := o.dir, hw := o.hw, tgts := #[o.tgt], depth := o.depth, encl := o.encl }
  return bs

/-- Is the side `d` (a unit vector) of the state at `c` free of strokes? -/
def Scene.sideFree (sc : Scene) (c d : P) : Bool := Id.run do
  let a := c + d * (NODE_R + fHalf)
  let b := c + d * PROBE
  for i in [0:sc.curves.size] do
    let cv := sc.curves[i]!
    if !boxesMeet (min a.x b.x - fClear, min a.y b.y - fClear, max a.x b.x + fClear, max a.y b.y + fClear) sc.cboxes[i]! then continue
    for j in [0:cv.size - 1] do
      if segSegDist a b cv[j]! cv[j+1]! < fClear then return false
  return true

/-! ## Grid -/

def sortUniq (xs : Array Float) : Array Float := Id.run do
  let ys := xs.qsort (· < ·)
  let mut out : Array Float := #[]
  for y in ys do
    if out.isEmpty || y - out.back! > fHalf then out := out.push y
  return out

def nearestIdx (xs : Array Float) (v : Float) : Nat := Id.run do
  let mut best := 0
  for i in [0:xs.size] do
    if (xs[i]! - v).abs < (xs[best]! - v).abs then best := i
  return best

structure Grid where
  xs : Array Float
  ys : Array Float
  /-- `(u, v, base cost, a, b)` -/
  edges : Array (Nat × Nat × Float × P × P)
  /-- the outside tracks: `(horizontal?, coordinate, rank)`, rank 0 nearest
  the tree -/
  tracks : Array (Bool × Float × Nat) := #[]
deriving Inhabited

def Grid.nx (g : Grid) : Nat := g.xs.size
def Grid.node (g : Grid) (ix iy : Nat) (vert : Bool) : Nat := (iy * g.nx + ix) * 2 + (if vert then 1 else 0)
def Grid.nodes (g : Grid) : Nat := g.xs.size * g.ys.size * 2
def Grid.pt (g : Grid) (v : Nat) : P := let q := v / 2; ⟨g.xs[q % g.nx]!, g.ys[q / g.nx]!⟩
def Grid.at (g : Grid) (p : P) (vert : Bool) : Nat := g.node (nearestIdx g.xs p.x) (nearestIdx g.ys p.y) vert

/-- The cost of a grid segment against the tree. -/
def Scene.segCost (sc : Scene) (a b : P) : Float := Id.run do
  let mut c := cLen * (b - a).len
  let sb : Box := (min a.x b.x - fTol, min a.y b.y - fTol, max a.x b.x + fTol, max a.y b.y + fTol)
  for i in [0:sc.curves.size] do
    if !boxesMeet sb sc.cboxes[i]! then continue
    let cv := sc.curves[i]!
    let mut along := false
    for j in [0:cv.size - 1] do
      let p := cv[j]!; let q := cv[j+1]!
      if (crossAt a b p q).isSome then c := c + cTree
      if !along && segsOverlap a b p q fTol then along := true
    -- touching a vertex of the stroke (a corner, a joint, an end) counts as a
    -- crossing: general position is not assumed
    for p in cv do
      if segDist p a b < fTouch && (p - a).len > fTouch && (p - b).len > fTouch then c := c + cTree
    -- an end of the segment on the stroke: half a crossing at each end, so a
    -- path through that point pays one crossing
    let mut endA := false
    let mut endB := false
    for j in [0:cv.size - 1] do
      if segDist a cv[j]! cv[j+1]! < fTouch then endA := true
      if segDist b cv[j]! cv[j+1]! < fTouch then endB := true
    if endA then c := c + cTree * fHalf
    if endB then c := c + cTree * fHalf
    if along then c := c + cAlong
  for (o, r) in sc.circles do
    if segDist o a b < r + sc.halo then c := c + cState
  for t in sc.texts do
    if segMeetsBox a b t then c := c + cText
  for t in sc.soft do
    if segMeetsBox a b t then c := c + cName
  return c

def Grid.build (sc : Scene) (bs : Array Binder) : Grid := Id.run do
  let (ex0, ey0, ex1, ey1) := sc.extent
  let B := bs.size
  let mut tracks : Array (Bool × Float × Nat) := #[]
  let mut xs : Array Float := #[]
  let mut ys : Array Float := #[]
  for b in bs do
    xs := xs.push b.notch.x |>.push (b.notch.x - b.hw - 6.0) |>.push (b.notch.x + b.hw + 6.0)
    ys := ys.push (b.notch.y + b.dir * 4.0) |>.push (b.notch.y - b.dir * 4.0)
    for t in b.tgts do
      xs := xs.push t.x |>.push (t.x - sc.app) |>.push (t.x + sc.app)
      ys := ys.push t.y |>.push (t.y - sc.app) |>.push (t.y + sc.app)
  for (x0, y0, x1, y1) in sc.boxes do
    xs := xs.push (x0 - 5.0) |>.push (x1 + 5.0)
    for k in [0:B] do
      ys := ys.push (y0 - (5.0 + 4.0 * k.toFloat) * sc.sp) |>.push (y1 + (5.0 + 4.0 * k.toFloat) * sc.sp)
  for r in [0:B + 1] do
    -- (the first track clear of the approach lines, which lie APP from a state)
    let off := (14.0 + 7.0 * r.toFloat) * sc.sp
    xs := xs.push (ex1 + off) |>.push (ex0 - off)
    ys := ys.push (ey0 - off) |>.push (ey1 + off)
    tracks := tracks.push (false, ex1 + off, r) |>.push (false, ex0 - off, r)
      |>.push (true, ey0 - off, r) |>.push (true, ey1 + off, r)
  let g0 : Grid := { xs := sortUniq xs, ys := sortUniq ys, edges := #[], tracks }
  let mut edges := #[]
  for iy in [0:g0.ys.size] do
    for ix in [0:g0.xs.size] do
      let p : P := ⟨g0.xs[ix]!, g0.ys[iy]!⟩
      edges := edges.push (g0.node ix iy false, g0.node ix iy true, cBend, p, p)
      if ix + 1 < g0.xs.size then
        let q : P := ⟨g0.xs[ix+1]!, g0.ys[iy]!⟩
        edges := edges.push (g0.node ix iy false, g0.node (ix+1) iy false, sc.segCost p q, p, q)
      if iy + 1 < g0.ys.size then
        let q : P := ⟨g0.xs[ix]!, g0.ys[iy+1]!⟩
        edges := edges.push (g0.node ix iy true, g0.node ix (iy+1) true, sc.segCost p q, p, q)
  return { g0 with edges }

/-! ## Routing -/

/-- One binder's links: polylines (from junction to junction or end), the
junction points, and the cost. -/
structure Routed where
  polys : Array Polyline := #[]
  junctions : Array P := #[]
  cost : Float := 0.0
deriving Inhabited

/-- Turn a set of segments into polylines between ends and junctions: the
segments are first made a tree (a minimum spanning forest by length, then
leaves that are not `keep` points pruned). -/
def toPolylines (segs : Array (P × P)) (keep : Array P) : Array Polyline × Array P := Id.run do
  -- points
  let mut pts : Array P := #[]
  let idx (pts : Array P) (p : P) : Option Nat := pts.findIdx? fun q => (q - p).len < fHalf
  let mut es : Array (Float × Nat × Nat) := #[]
  for (a, b) in segs do
    if (a - b).len < fHalf then continue
    let ia ← match idx pts a with
      | some i => pure i
      | none => do pts := pts.push a; pure (pts.size - 1)
    let ib ← match idx pts b with
      | some i => pure i
      | none => do pts := pts.push b; pure (pts.size - 1)
    es := es.push ((a - b).len, ia, ib)
  -- Kruskal
  let sorted := es.qsort (fun x y => x.1 < y.1)
  let mut parent := (List.range pts.size).toArray
  let mut adj : Array (List Nat) := Array.replicate pts.size []
  for (_, a, b) in sorted do
    let mut ra := a
    let mut fuel := pts.size + 1
    while parent[ra]! != ra && fuel > 0 do ra := parent[ra]!; fuel := fuel - 1
    let mut rb := b
    fuel := pts.size + 1
    while parent[rb]! != rb && fuel > 0 do rb := parent[rb]!; fuel := fuel - 1
    if ra == rb then continue
    parent := parent.set! ra rb
    adj := adj.modify a (b :: ·) |>.modify b (a :: ·)
  -- prune leaves that are not kept
  let isKeep (i : Nat) := keep.any fun k => (k - pts[i]!).len < fHalf
  let mut changed := true
  while changed do
    changed := false
    for i in [0:pts.size] do
      if adj[i]!.length == 1 && !isKeep i then
        let j := adj[i]!.head!
        adj := adj.set! i [] |>.modify j (·.filter (· != i))
        changed := true
  -- walk from every node of degree ≠ 2
  let mut polys : Array Polyline := #[]
  let mut used : Array (Nat × Nat) := #[]
  let mut junctions : Array P := #[]
  for i in [0:pts.size] do
    let d := adj[i]!.length
    if d ≥ 3 then junctions := junctions.push pts[i]!
    if d == 0 || d == 2 then continue
    for j0 in adj[i]! do
      if used.contains (i, j0) then continue
      let mut line : Polyline := #[pts[i]!]
      let mut prev := i
      let mut cur := j0
      used := used.push (i, j0) |>.push (j0, i)
      let mut fuel := pts.size + 1
      while fuel > 0 do
        fuel := fuel - 1
        line := line.push pts[cur]!
        if adj[cur]!.length != 2 then break
        let nxt := (adj[cur]!.filter (· != prev)).head!
        used := used.push (cur, nxt) |>.push (nxt, cur)
        prev := cur
        cur := nxt
      polys := polys.push (simplify line)
  return (polys, junctions)

/-- Route one binder against the tree and the other binders' links. -/
def routeBinder (sc : Scene) (g : Grid) (b : Binder) (others : Array Polyline) (want : Nat := 0) :
    Routed := Id.run do
  let n := g.nodes
  let oboxes := others.map bbox
  let mut adj : Array (Array (Nat × Float)) := Array.replicate n #[]
  for (u, v, w, a, c) in g.edges do
    let mut w := w
    if (a - c).len > fHalf then
      let sb : Box := (min a.x c.x - fTol, min a.y c.y - fTol, max a.x c.x + fTol, max a.y c.y + fTol)
      for i in [0:others.size] do
        if !boxesMeet sb oboxes[i]! then continue
        let o := others[i]!
        for j in [0:o.size - 1] do
          if (crossAt a c o[j]! o[j+1]!).isSome then w := w + cLink
          if segsOverlap a c o[j]! o[j+1]! fTol then w := w + cAlongLink
      -- scope nesting: an outer binder's links on outer tracks
      let horiz := a.y == c.y
      let v := if horiz then a.y else a.x
      for (h, tv, r) in g.tracks do
        if h == horiz && (tv - v).abs < fHalf then
          let d := if r ≥ want then r - want else want - r
          w := w + cNest * d.toFloat * (a - c).len
    adj := adj.modify u (·.push (v, w)) |>.modify v (·.push (u, w))
  -- the root: two connectors from the notch's line, outwards and inwards
  let root := n
  let outP : P := ⟨b.notch.x, b.notch.y + b.dir * 4.0⟩
  let inP : P := ⟨b.notch.x, b.notch.y - b.dir * 4.0⟩
  let mut extra : Array (Array (Nat × Float)) := #[#[]]
  for p in [outP, inP] do
    let v := g.at p true
    extra := extra.modify 0 (·.push (v, cConn))
    adj := adj.modify v (·.push (root, cConn))
  -- the terminals: one connector per free side of each state
  let sides : List (P × Bool × Float) :=
    [(⟨0.0, 1.0⟩, true, 0.0), (⟨1.0, 0.0⟩, false, 0.5), (⟨0.0, -1.0⟩, true, 1.0), (⟨-1.0, 0.0⟩, false, 1.5)]
  let mut terms : Array Nat := #[]
  for t in b.tgts do
    let tn := n + extra.size
    terms := terms.push tn
    let mut conn : Array (Nat × Float) := #[]
    for (d, vert, pref) in sides do
      if !sc.sideFree t d then continue
      let v := g.at (t + d * sc.app) vert
      conn := conn.push (v, cConn + pref)
      adj := adj.modify v (·.push (tn, cConn + pref))
    -- a state whose four sides are all taken (arrows both ways, loops above
    -- and below) is met diagonally, between them
    if conn.isEmpty then
      for (sx, sy, pref) in [(1.0, 1.0, 2.0), (-1.0, 1.0, 2.25), (1.0, -1.0, 2.5), (-1.0, -1.0, 2.75)] do
        if !sc.sideFree t ⟨sx * 0.7071067811865476, sy * 0.7071067811865476⟩ then continue
        let v := g.at ⟨if sx > 0.0 then t.x + sc.app else t.x - sc.app, if sy > 0.0 then t.y + sc.app else t.y - sc.app⟩ false
        conn := conn.push (v, cConn + pref)
        adj := adj.modify v (·.push (tn, cConn + pref))
    extra := extra.push conn
  let gr : Graph := { adj := adj ++ extra }
  let some (cost, edges) := steiner gr terms root
    | return { cost := fBig }
  -- segments: grid edges as they are, connectors to the notch and the circles
  let mut segs : Array (P × P) := #[]
  let mut keep : Array P := #[b.notch]
  for (u, v) in edges do
    let (u, v) := if u ≥ n then (v, u) else (u, v)   -- a virtual node second
    if v < n then segs := segs.push (g.pt u, g.pt v)
    else if v == root then
      segs := segs.push (g.pt u, ⟨b.notch.x, g.pt u |>.y⟩) |>.push (⟨b.notch.x, (g.pt u).y⟩, b.notch)
    else
      let t := b.tgts[v - n - 1]!
      let p := g.pt u
      let e := t + (p - t).unit * (NODE_R + fOne)
      segs := segs.push (p, e)
      keep := keep.push e
  let (polys, junctions) := toPolylines segs keep
  return { polys, junctions, cost := cost - cConn * (b.tgts.size.toFloat + fOne) }

/-- A pinned route (the `route` hint) made to meet binder `b`'s terminals
exactly: an end within reach of the notch point, or of the place where a link
meets a bound state (`NODE_R + 1` from its centre, on one of four sides), is
moved onto it with a small jog, so that segments stay horizontal or vertical
and points shared with other polylines do not move.  `none` when a segment is
neither horizontal nor vertical or some terminal is met by no end: the pin
was made for another layout. -/
def fitPin (b : Binder) (ps : Array Polyline) : Option Routed := Id.run do
  let tol : Float := 1.5
  let reach : Float := NODE_R + fOne
  for p in ps do
    if p.size < 2 then return none
    for i in [0:p.size - 1] do
      let a := p[i]!; let c := p[i+1]!
      if (a.x - c.x).abs > 0.01 && (a.y - c.y).abs > 0.01 then return none
  -- the exact terminal an end stands for, if any
  let termFor (e : P) : Option P :=
    if (e - b.notch).len ≤ tol then some b.notch
    else b.tgts.findSome? fun t =>
      let d := e - t
      if (d.len - reach).abs ≤ tol then
        let u : P := if d.x.abs ≥ d.y.abs then ⟨if d.x ≥ 0.0 then 1.0 else -1.0, 0.0⟩
                     else ⟨0.0, if d.y ≥ 0.0 then 1.0 else -1.0⟩
        some (t + u * reach)
      else none
  -- replace an end by its terminal, joined to the next point by a jog
  let snapStart (q : Polyline) : Polyline :=
    match termFor q[0]! with
    | none => q
    | some t =>
      let e := q[0]!; let nx := q[1]!
      let m : P := if (e.x - nx.x).abs ≤ 0.01 then ⟨nx.x, t.y⟩ else ⟨t.x, nx.y⟩
      let rest := q.extract 1 q.size
      if (m - t).len < 0.01 || (m - nx).len < 0.01 then #[t] ++ rest else #[t, m] ++ rest
  let out := ps.map fun p => (snapStart (snapStart p).reverse).reverse
  -- every terminal met
  let ends := out.foldl (fun acc p => acc.push p[0]! |>.push p.back!) #[]
  if !(ends.any fun e => (e - b.notch).len < 0.01) then return none
  for t in b.tgts do
    if !(ends.any fun e => ((e - t).len - reach).abs < 0.01) then return none
  -- junctions: ends shared by two or more polylines
  let mut junctions : Array P := #[]
  for e in ends do
    let n := (ends.filter fun f => (f - e).len < 0.01).size
    if n ≥ 2 && !(junctions.any fun j => (j - e).len < 0.01) then junctions := junctions.push e
  return some { polys := out, junctions, cost := 0.0 }

/-- Route every binder: in turn, then `rounds` rounds of rip-up and reroute.
Pinned binders (`pinned`) keep their routes; the others route around them. -/
def routeAll (sc : Scene) (g : Grid) (bs : Array Binder) (rounds : Nat) (reverse : Bool := false)
    (given : Option (Array Nat) := none) (pinned : Array (Option Routed) := #[]) : Array Routed := Id.run do
  -- innermost scopes first, so that they take the tracks nearest the tree
  -- and the outer binders route round them
  let order := ((List.range bs.size).toArray.qsort fun i j =>
    bs[i]!.depth > bs[j]!.depth || (bs[i]!.depth == bs[j]!.depth && bs[i]!.tgts.size > bs[j]!.tgts.size))
  let maxD := bs.foldl (fun m b => max m b.depth) 0
  let order := if reverse then order.reverse else order
  let order := given.getD order
  let mut rs : Array Routed := (List.range bs.size).toArray.map fun i => (pinned[i]?.bind id).getD {}
  for r in [0:rounds + 1] do
    for i in order do
      if (pinned[i]?.bind id).isSome then continue
      let others := (List.range bs.size).foldl (fun acc j => if j == i then acc else acc ++ rs[j]!.polys) #[]
      let _ := r
      rs := rs.set! i (routeBinder sc g bs[i]! others (maxD - bs[i]!.depth))
  return rs

/-- The score of a finished configuration, measured on it (each binder's own
cost is recorded when it was last routed, so its crossings with binders
routed after it may be out of date): crossings with the tree, then crossings
between different binders, then the recorded costs as a tie-break. -/
def score (sc : Scene) (rs : Array Routed) : Float := Id.run do
  let mut nLink := 0
  for i in [0:rs.size] do
    for j in [i+1:rs.size] do
      for a in rs[i]!.polys do
        for b in rs[j]!.polys do nLink := nLink + (crossings a b).size
  let mut nTree := 0
  for r in rs do
    for a in r.polys do
      for k in [0:sc.curves.size] do
        if boxesMeet (bbox a) sc.cboxes[k]! then nTree := nTree + (crossings a sc.curves[k]!).size
  let own := rs.foldl (fun c r => c + r.cost) 0.0
  return 1.0e6 * nTree.toFloat + 1.0e4 * nLink.toFloat + own

/-! ## Names -/

/-- Place each bound state's name at the first free place among a few
around it (clear of links, strokes, states and other names). -/
def placeNames (sc : Scene) (links : Array Polyline) : Array Shape := Id.run do
  let mut placed : Array Box := #[]
  let mut out : Array Shape := #[]
  for l in sc.labels do
    let c := l.pos
    let cands : List (Float × Float × String) :=
      if l.looped then [(9.0, 4.0, "start"), (9.0, -6.0, "start"), (-9.0, 4.0, "end"), (0.0, 18.0, "middle")]
      else [(0.0, -9.0, "middle"), (7.0, -7.0, "start"), (9.0, 4.0, "start"), (-7.0, -7.0, "end"),
            (0.0, 18.0, "middle"), (-9.0, 4.0, "end")]
    let score (dx dy : Float) (anc : String) : Nat := Id.run do
      let bx := textBox ⟨c.x + dx, c.y + dy⟩ l.text anc
      let mut n := 0
      for pl in links do
        for j in [0:pl.size - 1] do
          if segMeetsBox pl[j]! pl[j+1]! bx then n := n + 1
      for i in [0:sc.curves.size] do
        if boxesMeet bx sc.cboxes[i]! then
          let cv := sc.curves[i]!
          for j in [0:cv.size - 1] do
            if segMeetsBox cv[j]! cv[j+1]! bx then n := n + 1
      for (o, _) in sc.circles do
        if bx.1 < o.x && o.x < bx.2.2.1 && bx.2.1 < o.y && o.y < bx.2.2.2 then n := n + 1
      for t in placed ++ sc.texts do
        if boxesMeet bx t then n := n + 1
      return n
    let mut best := cands.head!
    let mut bestN := score best.1 best.2.1 best.2.2
    for (dx, dy, anc) in cands.tail do
      if bestN == 0 then break
      let s := score dx dy anc
      if s < bestN then best := (dx, dy, anc); bestN := s
    let (dx, dy, anc) := best
    placed := placed.push (textBox ⟨c.x + dx, c.y + dy⟩ l.text anc)
    out := out.push (.text ⟨c.x + dx, c.y + dy⟩ l.text l.color 12 anc)
  return out

/-! ## Checks -/

/-- Empty bigons and monogons.  A link and another curve crossing at two
points consecutive along both bound a bigon; if no state, name or link end
lies inside, the link can be pushed across it, removing both crossings (the
bigon criterion for curves in minimal position, on the plane punctured at
the states, names and link ends).  A link crossing itself bounds a monogon,
always removable. -/
def problems (links others : Array Polyline) (punct : Array P) : Array Polyline := Id.run do
  let mut n := #[]
  for li in [0:links.size] do
    let l := links[li]!
    for o in others ++ links.extract (li + 1) links.size do
      let xs := (crossings l o).qsort (fun p q => p.1 < q.1)
      for k in [0:xs.size - 1] do
        let (s0, t0) := xs[k]!; let (s1, t1) := xs[k+1]!
        if xs.any fun (_, t) => min t0 t1 < t && t < max t0 t1 then continue
        let poly := subPath l s0 s1 ++ subPath o t1 t0
        if !(punct.any (inPoly poly)) then n := n.push poly
    for (s0, s1) in crossings l l do
      if s0 + 1.5 < s1 then n := n.push (subPath l s0 s1)
  return n

/-- **Nesting check.**  For each pair of binders where one's scope contains
the other's, and each side (above, below, right, left): compare the two
binders' segments that run along the outside of the tree on that side
(nothing of the tree lies beyond them across their span).  If an inner
binder's segment lies further out than every outer binder's segment
alongside it, the inner links pass outside the outer ones there: a
violation.
Returns `(outer, inner, side)`. -/
def nestingViolations (sc : Scene) (bs : Array Binder) (rs : Array Routed) :
    Array (String × String × String) := Id.run do
  -- the tree's boxes (strokes, states, names)
  let tree : Array Box := sc.cboxes ++ sc.circles.map (fun (p, r) => (p.x - r, p.y - r, p.x + r, p.y + r)) ++ sc.texts
  -- side k: the outside segments as (outward coordinate, lo, hi), larger = further out
  let outside (r : Routed) (k : Nat) : Array (Float × Float × Float) := Id.run do
    let mut out := #[]
    for pl in r.polys do
      for q in [0:pl.size - 1] do
        let a := pl[q]!; let b := pl[q+1]!
        let horiz := a.y == b.y && a.x != b.x
        let vert := a.x == b.x && a.y != b.y
        let lo := if horiz then min a.x b.x else min a.y b.y
        let hi := if horiz then max a.x b.x else max a.y b.y
        let beyond (bx : Box) : Bool :=
          let (x0, y0, x1, y1) := bx
          if k == 0 then horiz && x0 < hi && lo < x1 && y0 < a.y
          else if k == 1 then horiz && x0 < hi && lo < x1 && y1 > a.y
          else if k == 2 then vert && y0 < hi && lo < y1 && x1 > a.x
          else vert && y0 < hi && lo < y1 && x0 < a.x
        let onSide := (k ≤ 1 && horiz) || (k ≥ 2 && vert)
        if onSide && !(tree.any beyond) then
          let c := if k == 0 then -a.y else if k == 1 then a.y else if k == 2 then a.x else -a.x
          out := out.push (c, lo, hi)
    return out
  let sides := #["above", "below", "right", "left"]
  let mut v := #[]
  for i in [0:bs.size] do
    for j in [0:bs.size] do
      if !(bs[j]!.encl.any fun q => (q - bs[i]!.notch).len < fHalf) then continue
      for k in [0:4] do
        let so := outside rs[i]! k; let si := outside rs[j]! k
        -- against the outermost of the outer binder's segments alongside it
        if si.any (fun (ci, li, hi) =>
            let along := so.filter fun (_, lo, ho) => min hi ho - max li lo > fHalf
            !along.isEmpty && ci > along.foldl (fun m (co, _, _) => max m co) (-fBig) + fHalf) then
          v := v.push (bs[i]!.name, bs[j]!.name, sides[k]!)
  return v

/-- **Name check.**  Each bound name must lie within `10 × spacing` of its
state, and no link may pass between them (cross the segment from the
state's centre to the middle of its name).  Returns the names that fail. -/
def nameViolations (sc : Scene) (names : Array Shape) (links : Array Polyline) : Array String := Id.run do
  let mut v := #[]
  for (l, s) in sc.labels.zip names do
    let .text p str _ sz a _ := s | continue
    let (x0, y0, x1, y1) := textBox p str a sz
    let c := l.pos
    let nx := max x0 (min c.x x1); let ny := max y0 (min c.y y1)
    let far := (c - ⟨nx, ny⟩).len > 10.0 * sc.sp
    let mid : P := ⟨(x0 + x1) / 2.0, (y0 + y1) / 2.0⟩
    let cut := links.any fun pl => !(crossings #[c, mid] pl).isEmpty
    if far || cut then v := v.push s!"{l.text}{if far then " (far)" else ""}{if cut then " (cut off by a link)" else ""}"
  return v

/-- What rendering a view-B tree gives: the SVG and the checks. -/
structure Rendered where
  svg : String
  /-- the scene of view B (L2): every shape drawn, in drawing order, in the
  tree's coordinates (before the canvas translation); the SVG is these shapes
  written out (`Shape.svg`), with the style applied.  `FregeDiagrams.SpecB`
  reads the formula back from it. -/
  scene : Array Shape := #[]
  /-- empty bigons and monogons -/
  problems : Array Polyline := #[]
  /-- crossings between different binders' links, and of links with strokes -/
  nLink : Nat := 0
  nTree : Nat := 0
  nesting : Array (String × String × String) := #[]
  names : Array String := #[]
  /-- binders with a `route` pin that does not fit the layout (routed
  automatically instead) -/
  stalePins : Array String := #[]
  /-- binders with a `route` pin that was set aside because the pins do not
  apply to this layout (`DrawOpts.pinsApply`); routed automatically -/
  setAside : Array String := #[]

/-! ## Rendering -/

/-- Render a formula tree, with its links if asked; also the empty bigons
and monogons the links leave (none when the routing is locally minimal). -/
def TreeDiagram.render (d : TreeDiagram) (o : DrawOpts := {}) : Rendered := Id.run do
  -- with links, every choice of flipped notches (up to four binders) is
  -- routed once; the three cheapest are routed again with more rounds
  let bs := d.tree.binders.filter fun b => (o.fixedNotches.lookup b).isNone
  let pinsFor (binders : Array Binder) : Array (Option Routed) :=
    binders.map fun b => if !o.pinsApply then none else (o.pinned.lookup b.name).bind (fitPin b)
  let flipSets : List (List String) :=
    if !o.links || bs.length > 4 then [[]]
    else (List.range (2 ^ bs.length)).map fun m =>
      (List.range bs.length).filterMap fun i => if (m >>> i) % 2 == 1 then bs[i]? else none
  let attempt (fs : List String) (rounds : Nat) (_reverse : Bool := false) :
      Float × Scene × Array Binder × Array Routed :=
    let (ms, _) := d.layout { o with flips := fs }
    let sc := Scene.ofMarks ms o.spacing
    let binders := sc.binders
    if binders.isEmpty then (cFlip * fs.length.toFloat, sc, binders, #[]) else
    let g := Grid.build sc binders
    let rs := routeAll sc g binders rounds (pinned := pinsFor binders)
    (score sc rs + cFlip * fs.length.toFloat, sc, binders, rs)
  let mut ranked : Array (Float × List String) := #[]
  for fs in flipSets do
    ranked := ranked.push ((attempt fs 0).1, fs)
  ranked := ranked.qsort (fun a b => a.1 < b.1)
  let mut best : Option (Float × Scene × Array Binder × Array Routed) := none
  -- routing in turn can lock binders into an arrangement that none can leave
  -- alone; for up to four binders every routing order is tried, otherwise
  -- the default order and its reverse
  for (_, fs) in ranked.extract 0 (if o.links then 3 else 1) do
    let (ms, _) := d.layout { o with flips := fs }
    let sc := Scene.ofMarks ms o.spacing
    let binders := sc.binders
    if binders.isEmpty then
      if best.isNone then best := some (cFlip * fs.length.toFloat, sc, binders, #[])
      continue
    let g := Grid.build sc binders
    let orders : List (Option (Array Nat)) :=
      if binders.size ≤ 4 then (perms (List.range binders.size)).map (some ·.toArray)
      else [none, some ((List.range binders.size).toArray.reverse)]
    for ord in orders do
      let rs := routeAll sc g binders 2 false ord (pinsFor binders)
      let c := score sc rs + cFlip * fs.length.toFloat
      if best.all (c < ·.1) then best := some (c, sc, binders, rs)
  let some (_, sc, binders, rs) := best | return { svg := "" }
  let sc : Scene := sc
  let binders : Array Binder := binders
  let rs : Array Routed := rs
  -- links: each binder its own pastel colour, its name in Morse as the dashes
  let mut linkSh : Array Shape := #[]
  let mut links : Array Polyline := #[]
  let pins := pinsFor binders
  for i in [0:binders.size] do
    let colr := linkPalette[i % linkPalette.size]!
    -- for the editor: one group per binder's links
    if o.annotate then
      linkSh := linkSh.push <| .raw s!"<g data-k=\"link\" data-name=\"{xmlEsc binders[i]!.name}\" data-pinned=\"{if (pins[i]?.bind id).isSome then 1 else 0}\">"
    for pl in rs[i]!.polys do
      links := links.push pl
      let da := (o.linkDash.lookup binders[i]!.name).getD (morseDash binders[i]!.name)
      let da := if da == "" then "" else s!" stroke-dasharray=\"{da}\""
      linkSh := linkSh.push (Shape.poly pl colr "1.9" s!" stroke-linejoin=\"round\"{da}")
    for j in rs[i]!.junctions do
      linkSh := linkSh.push (Shape.circle j 2.4 colr)
    if o.annotate then linkSh := linkSh.push (.raw "</g>")
  let names := placeNames sc links
  -- the canvas: everything drawn, with a margin
  let sc' := { sc with curves := sc.curves ++ links, cboxes := sc.cboxes ++ links.map bbox,
                       texts := sc.texts ++ names.filterMap fun (s : Shape) => match s with
                         | .text p s _ sz a _ => some (textBox p s a sz) | _ => none }
  let (x0, y0, x1, y1) := sc'.extent
  let m := 12.0
  let scene := sc.shapes ++ linkSh ++ names
  let body := #[s!"<g transform=\"translate({fmt1 (m - x0)},{fmt1 (m - y0)})\">"] ++
    scene.map Shape.svg ++ #["</g>"]
  let punct := sc.circles.map (·.1) ++
    sc.texts.map (fun (a, b, c, e) => (⟨(a + c) / 2.0, (b + e) / 2.0⟩ : P)) ++
    binders.map (·.notch) ++ binders.foldl (fun acc b => acc ++ b.tgts) #[]
  let probs := if o.links then problems links sc.curves punct else #[]
  -- crossings: between different binders' links, and of links with strokes
  let mut nLink := 0
  for i in [0:rs.size] do
    for j in [i+1:rs.size] do
      for a in rs[i]!.polys do
        for b in rs[j]!.polys do nLink := nLink + (crossings a b).size
  let mut nTree := 0
  for a in links do
    for c in sc.curves do nTree := nTree + (crossings a c).size
  let doc := svgDoc (x1 - x0 + 2.0 * m).toUInt64.toNat (y1 - y0 + 2.0 * m).toUInt64.toNat body
  return { svg := if o.style == .soft then softSvg doc o.annotate else doc, scene,
           problems := probs, nLink, nTree,
           nesting := if o.links then nestingViolations sc binders rs else #[],
           names := if o.links then nameViolations sc names links else #[],
           setAside := if o.links && !o.pinsApply then (o.pinned.map (·.1)).toArray else #[],
           stalePins := if !o.links || !o.pinsApply then #[] else
             (o.pinned.filter fun (x, _) => (binders.zip pins).any fun (b, p) => b.name == x && p.isNone).toArray.map (·.1) }

def TreeDiagram.svg (d : TreeDiagram) (o : DrawOpts := {}) : String := (d.render o).svg

end FregeDiagrams
