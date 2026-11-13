/-
FregeDiagrams.View: the two pictures of a figure.

* **View B** (`Form.toTree`) draws the formula as a Frege-style tree.  A
  conjunction is a fork with a filled junction dot; a disjunction is primitive
  (never encoded as `¬A → B`): a fork with a hollow junction dot and an arc
  across the rays.
* **View A** (`Fig.toDiagram`) flattens the formula into one frame picture:
  every step of a chain is an arrow (a step back to the same state is a
  self-loop), equal names are one state, a state written `x°` anywhere is
  hollow; colour is polarity, red positive and black negative (a hypothesis
  of an `if`, or the body of a `not`, reverses it), as in view B.  Each
  quantifier is a notch on the first arrow, after it, into the state it
  binds: `all x` a square notch; `ex x` a pointed notch and a red state; an
  `ex x` under an odd number of `not`s says "no such state", drawn as a
  crossed state (unlabelled) with a square notch.  Text leaves and `!=`
  steps are not drawn in view A (captions, given as hints, say them).
  Each disjunct of a disjunction is a panel of its own; its states are keyed
  `name/k` in the hints.

The positions come from the hints (`Hints`); a state without a hint is put on
a plain grid (automatic layout is a later step, see `docs/design/DESIGN.md`).
-/
import FregeDiagrams.Fig
import FregeDiagrams.Route.Router

namespace FregeDiagrams

/-! ## View B -/

def St.label (st : St) : String := dispName st.name ++ (if st.inf then "°" else "")

partial def Form.toTree : Form → Tree
  | .chain st steps => .leaf st.label (steps.map fun (r, t) => (r, t.label))
  | .text s _ => .text s
  | .all x b => .q .all (dispName x) b.toTree
  | .ex x b => .q .ex (dispName x) b.toTree
  | .not b => .neg b.toTree
  | .imp hs c => .cond c.toTree (hs.map toTree)
  | .and ps => .and (ps.map toTree)
  | .or ps => .or (ps.map toTree)

/-! ## View A: flattening -/

structure NodeInfo where
  panel : Nat
  name : String
  inf : Bool := false
  new : Bool := false
  cross : Bool := false
  /-- the blocks (`blockPath`) of the chains this state occurs in -/
  paths : Array String := #[]

structure FlatEdge where
  panel : Nat
  src : String
  tgt : String
  occ : Nat
  rel : Composite
  concl : Bool
  q : Option Quant
  /-- the binder's quantifier in prenex form: as written if the binder sits
  in a positive place, its dual if in a negative one (for `FregeDiagrams.Lint`) -/
  prenex : Option Quant := none
  /-- the block (`blockPath`) of the chain this arrow comes from -/
  path : String := ""

inductive FlatItem where
  | edge (e : FlatEdge)
  | loop (panel : Nat) (name : String) (rel : Composite) (concl : Bool)
  /-- a quantifier no arrow could carry: shown on its state (`Item.qmark`) -/
  | mark (panel : Nat) (name : String) (q : Quant) (concl : Bool)

structure Flat where
  nodes : Array NodeInfo := #[]
  items : Array FlatItem := #[]
  /-- quantifiers waiting for their notch, innermost first: (id, name, kind
  drawn, kind in prenex form) -/
  pending : List (Nat × String × Quant × Quant) := []
  marks : Array (Nat × String × Bool) := #[]  -- (panel, name, crossed?) of `ex` binders
  fresh : Nat := 0
  /-- the quantifiers in scope, innermost first: (id, name) -/
  scopes : List (Nat × String) := []
  /-- for each quantifier with a bound occurrence, the first panel it occurs in -/
  seen : List (Nat × Nat) := []
  nextPanel : Nat := 2

namespace Flat

def note (f : Flat) (panel : Nat) (st : St) (path : String := "") : Flat :=
  -- the occurrence is bound by the innermost quantifier of its name in scope
  let f := match f.scopes.find? (·.2 == st.name) with
    | some (id, _) => if f.seen.any (·.1 == id) then f else { f with seen := f.seen ++ [(id, panel)] }
    | none => f
  match f.nodes.findIdx? (fun n => n.panel == panel && n.name == st.name) with
  | some i => { f with nodes := f.nodes.modify i fun n =>
      { n with inf := n.inf || st.inf, paths := if n.paths.contains path then n.paths else n.paths.push path } }
  | none => { f with nodes := f.nodes.push { panel, name := st.name, inf := st.inf, paths := #[path] } }

/-- Take the innermost pending quantifier binding `t`, if any. -/
def consume (f : Flat) (t : String) : Flat × Option (Quant × Quant) :=
  match f.pending.find? (fun (_, x, _, _) => x == t) with
  | some (id, _, q, p) => ({ f with pending := f.pending.filter (·.1 != id) }, some (q, p))
  | none => (f, none)

def addEdge (f : Flat) (panel : Nat) (src tgt : String) (rel : Composite) (concl : Bool)
    (path : String := "") : Flat :=
  let (f, qp) := f.consume tgt
  let q := qp.map (·.1)
  let prenex := qp.map (·.2)
  let occ := 1 + (f.items.filter fun
    | .edge e => e.panel == panel && e.src == src && e.tgt == tgt
    | _ => false).size
  { f with items := f.items.push (.edge { panel, src, tgt, occ, rel, concl, q, prenex, path }) }

end Flat

partial def flatten (fm : Form) (panel : Nat) (concl neg : Bool) (path : String := "b") :
    StateM Flat Unit := do
  match fm with
  | .chain st steps =>
    modify (·.note panel st path)
    let mut prev := st
    for (r, t) in steps do
      if r.contains .ne then pure ()
      else if prev.name == t.name then
        modify fun f => { f with items := f.items.push (.loop panel t.name r concl) }
      else modify (·.addEdge panel prev.name t.name r concl path)
      modify (·.note panel t path)
      prev := t
  | .text _ _ => pure ()
  | .all x b => binder x .all (if concl then .all else .ex) false b
  | .ex x b => binder x (if neg then .all else .ex) (if concl then .ex else .all) true b
  | .not b => flatten b panel (!concl) (!neg) (blockPath path 0)
  | .imp hs c =>
    for (i, h) in (List.range hs.length).zip hs do flatten h panel (!concl) neg (blockPath path (i + 1))
    flatten c panel concl neg (blockPath path 0)
  | .and ps => for (i, p) in (List.range ps.length).zip ps do flatten p panel concl neg (blockPath path i)
  | .or ps =>
    let mut first := true
    for (i, p) in (List.range ps.length).zip ps do
      if first then
        flatten p panel concl neg (blockPath path i)
        first := false
      else
        let k := (← get).nextPanel
        modify fun f => { f with nextPanel := k + 1 }
        flatten p k concl neg (blockPath path i)
where
  binder (x : String) (q prenex : Quant) (isEx : Bool) (b : Form) : StateM Flat Unit := do
    let id := (← get).fresh
    let k0 := (← get).nextPanel
    modify fun f => { f with fresh := id + 1, pending := (id, x, q, prenex) :: f.pending,
                             scopes := (id, x) :: f.scopes }
    flatten b panel concl neg (blockPath path 0)
    modify fun f => { f with scopes := f.scopes.drop 1 }
    -- an `ex` binder marks its state in its own panel and in every panel opened
    -- inside its scope (the further parts of a disjunction in its body)
    let k1 := (← get).nextPanel
    let panels := panel :: (List.range (k1 - k0)).map (k0 + ·)
    -- no arrow into x took the notch: show the quantifier on the state itself,
    -- in the first panel of its scope where x occurs
    let st ← get
    if st.pending.any (·.1 == id) then
      if let some (_, p) := st.seen.find? (·.1 == id) then
        modify fun f => { f with items := f.items.push (.mark p x q concl) }
    modify fun f => { f with pending := f.pending.filter (·.1 != id),
                             marks := if isEx then f.marks ++ (panels.map (·, x, neg)).toArray
                                      else f.marks }

/-- The block of a formula at a path (`blockPath`): `b` is the formula itself. -/
def Form.blockAt (f : Form) (path : String) : Option Form :=
  match path.splitOn "/" with
  | "b" :: rest => go f (rest.map String.toNat?)
  | _ => none
where
  go (f : Form) : List (Option Nat) → Option Form
    | [] => some f
    | none :: _ => none
    | some i :: rest =>
      let child : Option Form := match f with
        | .all _ b | .ex _ b | .not b => if i == 0 then some b else none
        | .imp hs c => if i == 0 then some c else hs[i - 1]?
        | .and ps | .or ps => ps[i]?
        | .chain .. | .text .. => none
      child.bind (go · rest)

/-- Whether the block at `path` can take a `gap` hint: a hypothesis of an
`if`, or a part of `&` or `|` other than the first. -/
def Form.gapable (f : Form) (path : String) : Bool :=
  match path.splitOn "/" |>.reverse with
  | last :: parentRev@(_ :: _) =>
    let parent := "/".intercalate parentRev.reverse
    match f.blockAt parent, last.toNat? with
    | some (.imp ..), some i => i ≥ 1
    | some (.and ..), some i | some (.or ..), some i => i ≥ 1
    | _, _ => false
  | _ => false

/-! ## View A: placing -/

def Color.svg : Color → String
  | .black => BLACK | .red => RED | .grey => GREY

def nodeId (panel : Nat) (name : String) : String := s!"{name}/{panel}"

/-- The names bound by a quantifier somewhere in a formula. -/
partial def Form.bound : Form → List String
  | .chain .. | .text .. => []
  | .all x b | .ex x b => x :: b.bound
  | .not b => b.bound
  | .imp hs c => (hs.map Form.bound).foldl (· ++ ·) [] ++ c.bound
  | .and ps | .or ps => (ps.map Form.bound).foldl (· ++ ·) []

def Fig.toDiagram (d : Fig) (o : DrawOpts := {}) : Diagram := Id.run do
  let bound := d.shown.bound
  let ((), fl) := (flatten d.shown 1 true false).run {}
  let h := d.hints
  -- crossed / new marks
  let mut nodes := fl.nodes
  for (p, x, crossed) in fl.marks do
    nodes := nodes.map fun n =>
      if n.panel == p && n.name == x then
        if crossed then { n with cross := true } else { n with new := true }
      else n
  -- order: hinted states in hint order, then the rest in order of occurrence
  -- a state hinted twice: the last hint counts (as for size and namedy)
  let lastHints := h.nodes.reverse.foldl (fun acc nh =>
    if acc.any (·.key == nh.key) then acc else nh :: acc) []
  let hinted := lastHints.filterMap fun nh =>
    nodes.find? (fun n => n.panel == nh.key.panel && n.name == nh.key.name) |>.map (·, some nh)
  let rest := nodes.toList.filter fun n =>
    !h.nodes.any fun nh => n.panel == nh.key.panel && n.name == nh.key.name
  let placed := hinted ++ rest.map (·, none)
  let mut g : Diagram := { name := d.name, w := 0, h := 0 }
  let mut i := 0
  let mut maxX : Int := 0
  let mut maxY : Int := 0
  for (n, nh) in placed do
    let (x, y) := match nh with
      | some nh => (nh.x, nh.y)
      | none => ((40 + 100 * (i % 5) : Nat), (40 + 80 * (i / 5) : Nat))
    let (lx, ly) := (nh.bind (·.label)).getD (0, -10)
    let attrs := if !o.annotate then "" else
      s!" data-k=\"state\" data-name=\"{xmlEsc n.name}\" data-panel=\"{n.panel}\" data-x=\"{x}\" data-y=\"{y}\"" ++
      s!" data-lx=\"{lx}\" data-ly=\"{ly}\" data-labelled=\"{if (nh.bind (·.label)).isSome then 1 else 0}\" data-hinted=\"{if nh.isSome then 1 else 0}\"" ++
      s!" data-paths=\"{" ".intercalate n.paths.toList}\""
    g := g.node (nodeId n.panel n.name) x y (label := if n.cross || (o.hideBound && bound.contains n.name) then "" else dispName n.name)
      -- a free state is the implicit outer one, an arbitrary infallible state
      (inf := n.inf || (!bound.contains n.name && !n.cross)) (new := n.new) (lx := lx) (ly := ly) (cross := n.cross)
      (attrs := attrs)
    maxX := max maxX x; maxY := max maxY y
    i := i + 1
  for it in fl.items do
    match it with
    | .edge e =>
      let eh := h.edges.find? fun eh =>
        eh.src == e.src && eh.tgt == e.tgt && eh.occ == e.occ && eh.panel == e.panel
      let bend := ((eh.bind (·.bend)).map Float.ofInt).getD 0.0
      let qside := (eh.bind (·.side)).map fun b => if b then 1.0 else -1.0
      let qpos := match eh.bind (·.at_) with
        | some a => a.toFloat / 100.0
        | none => 0.35
      let attrs := if !o.annotate then "" else
        s!" data-k=\"edge\" data-src=\"{xmlEsc e.src}\" data-tgt=\"{xmlEsc e.tgt}\" data-occ=\"{e.occ}\" data-panel=\"{e.panel}\"" ++
        s!" data-bend=\"{((eh.bind (·.bend)).map toString).getD ""}\"" ++
        s!" data-side=\"{match eh.bind (·.side) with | some true => "+" | some false => "-" | none => ""}\"" ++
        s!" data-at=\"{((eh.bind (·.at_)).map toString).getD ""}\"" ++
        s!" data-q=\"{match e.q with | some .all => "all" | some .ex => "ex" | none => ""}\"" ++
        s!" data-path=\"{e.path}\""
      g := g.edge { a := nodeId e.panel e.src, b := nodeId e.panel e.tgt, rel := e.rel,
                    concl := e.concl, q := e.q, qside, qpos, bend,
                    qvar := if o.hideBound then some "" else none, attrs }
    | .mark p x q concl =>
      g := g.qmark (nodeId p x) q (if o.hideBound then "" else dispName x) concl
    | .loop p a rel concl =>
      let angle := ((h.loops.find? fun l => l.key.panel == p && l.key.name == a).map
        (Float.ofInt ·.angle)).getD (-90.0)
      g := g.loop (nodeId p a) rel concl angle
  for t in h.texts do
    g := g.text t.x t.y t.s (color := t.color.svg) (size := t.size)
      (anchor := if t.middle then "middle" else "start") (italic := t.italic)
  let (w, ht) := h.size.getD ((maxX + 40).toNat, (maxY + 40).toNat)
  return { g with w := w, h := ht, nameDy := o.nameDy, nameDys := o.nameDys, annotate := o.annotate,
                  style := o.style, relDash := o.relDash }

/-- The drawing options of a figure: its `namedy` and `notch` hints over the
options of the run. -/
def Fig.drawOpts (d : Fig) (o : DrawOpts) : DrawOpts :=
  -- the pins are laid out with the figure's own offset (its namedy, or none)
  -- and spacing 1
  let layoutOk := (d.hints.nameDy.isSome || o.nameDy == 0.0) && o.spacing == 1.0
  let o := match d.hints.nameDy with | some v => { o with nameDy := Float.ofInt v } | none => o
  { o with fixedNotches := d.hints.notches, pinsLayoutOk := layoutOk,
           strokes := d.hints.strokes.map fun (p, v) => (p, Float.ofInt v),
           gaps := d.hints.gaps.map fun (p, v) => (p, Float.ofInt v),
           nameDys := d.hints.nameDys.map fun (x, v) => (x, Float.ofInt v),
           -- the figure's own `dash` hints first, then the file's defaults
           relDash := (d.hints.dashes.filterMap fun
                         | (.rel r, a) => some (r, a.array)
                         | _ => none) ++ d.defaults.map fun (r, a) => (r, a.array),
           linkDash := d.hints.dashes.filterMap fun
                         | (.binder x, a) => some (x, a.array)
                         | _ => none,
           pinned := d.hints.routes.map fun (x, ps) =>
             (x, ps.toArray.map fun p => p.toArray.map fun (a, b) => (⟨Float.ofInt a, Float.ofInt b⟩ : P)) }

/-- View B of a figure: its formula tree, with its judgement stroke. -/
def Fig.toTreeDiagram (d : Fig) : TreeDiagram :=
  { name := d.name, tree := d.shown.toTree, judgement := d.hints.judgement, defines := d.defines }

/-- The pictures of a figure: `(file stem, SVG)`.  With both views, view A is
`NAME` and view B `NAME_B`. -/
def Fig.pictures (d : Fig) (o : DrawOpts := {}) : List (String × String) :=
  let o := d.drawOpts o
  let a := (d.name, (d.toDiagram o).svg)
  let b := d.toTreeDiagram.svg o
  match d.hints.views with
  | .both => [a, (d.name ++ "_B", b)]
  | .a => [a]
  | .b => [(d.name, b)]

end FregeDiagrams
