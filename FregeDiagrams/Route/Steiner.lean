/-
FregeDiagrams.Route.Steiner: minimum Steiner trees in a weighted graph.

`steiner g terms root` is the Dreyfus–Wagner algorithm (Networks 1, 1971):
for every subset `S` of the terminals and every node `v`, `dp S v` is the
cost of a cheapest tree joining `S ∪ {v}`; a subset's table is built from
its splits at `v` and then relaxed by Dijkstra.  Time
`O(3^k n + 2^k (m + n) log n)` for `k` terminals; exact.  The link router has
at most a handful of terminals per binder.
-/
import FregeDiagrams.Route.Geom

namespace FregeDiagrams.Route

/-- An undirected weighted graph: `adj v` lists `(neighbour, weight)`. -/
structure Graph where
  adj : Array (Array (Nat × Float))
deriving Inhabited

def Graph.size (g : Graph) : Nat := g.adj.size

/-- A binary min-heap of `(key, node)`, kept in an array.  The functions take
and return the array itself (not a structure holding it), so that it stays
unshared and is updated in place: reading it through a field of a live
structure would share it and copy it at every push and pop. -/
abbrev Heap := Array (Float × Nat)

def heapPush (a : Heap) (x : Float × Nat) : Heap := Id.run do
  let mut a := a.push x
  let mut i := a.size - 1
  while i > 0 do
    let p := (i - 1) / 2
    if a[i]!.1 < a[p]!.1 then
      a := a.swapIfInBounds i p
      i := p
    else break
  return a

/-- The least element (the array must be nonempty), and the rest. -/
def heapPop (a : Heap) : (Float × Nat) × Heap := Id.run do
  let top := a[0]!
  let mut a := a.swapIfInBounds 0 (a.size - 1)
  a := a.pop
  let mut i := 0
  let n := a.size
  while true do
    let l := 2 * i + 1
    let r := l + 1
    let mut m := i
    if l < n && a[l]!.1 < a[m]!.1 then m := l
    if r < n && a[r]!.1 < a[m]!.1 then m := r
    if m == i then break
    a := a.swapIfInBounds i m
    i := m
  return (top, a)

/-- Dijkstra from initial costs `init` (several sources at once): final
costs, and for each node its predecessor (`g.size` if its cost is its
initial one). -/
def dijkstra (g : Graph) (init : Array Float) : Array Float × Array Nat := Id.run do
  let n := g.size
  let mut dist := init
  let mut pred := Array.replicate n n
  let mut done := Array.replicate n false
  let mut h : Heap := #[]
  for v in [0:n] do
    if dist[v]! < fBig then h := heapPush h (dist[v]!, v)
  let mut fuel := (n + 1) * 64
  while fuel > 0 && !h.isEmpty do
    fuel := fuel - 1
    let ((d, v), h') := heapPop h
    h := h'
    if done[v]! || d > dist[v]! then continue
    done := done.set! v true
    for (u, w) in g.adj[v]! do
      let nd := d + w
      if nd < dist[u]! then
        dist := dist.set! u nd
        pred := pred.set! u v
        h := heapPush h (nd, u)
  return (dist, pred)

/-- A minimum Steiner tree joining `root` and `terms`: its cost and its
edges, or `none` if they are not connected. -/
def steiner (g : Graph) (terms : Array Nat) (root : Nat) : Option (Float × Array (Nat × Nat)) := Id.run do
  let n := g.size
  let k := terms.size
  if k == 0 then return some (fZero, #[])
  let full := (1 <<< k) - 1
  let mut dp : Array (Array Float) := Array.replicate (full + 1) #[]
  let mut pr : Array (Array Nat) := Array.replicate (full + 1) #[]
  -- split[S][v]: the sub-subset merged at v (0: none)
  let mut sp : Array (Array Nat) := Array.replicate (full + 1) #[]
  for i in [0:k] do
    let init := (Array.replicate n fBig).set! terms[i]! fZero
    let (d, p) := dijkstra g init
    dp := dp.set! (1 <<< i) d
    pr := pr.set! (1 <<< i) p
    sp := sp.set! (1 <<< i) (Array.replicate n 0)
  for S in [1:full + 1] do
    if S &&& (S - 1) == 0 then continue     -- a single terminal: done above
    let low := S &&& (S ^^^ (S - 1)) -- lowest bit of S
    let mut base := Array.replicate n fBig
    let mut split := Array.replicate n 0
    -- proper subsets containing the lowest bit (each split counted once)
    let mut T := (S - 1) &&& S
    while T > 0 do
      if T &&& low != 0 then
        let a := dp[T]!; let b := dp[S ^^^ T]!
        for v in [0:n] do
          let c := a[v]! + b[v]!
          if c < base[v]! then
            base := base.set! v c
            split := split.set! v T
      T := (T - 1) &&& S
    let (d, p) := dijkstra g base
    dp := dp.set! S d
    pr := pr.set! S p
    sp := sp.set! S split
  let cost := dp[full]![root]!
  if cost ≥ fBig then return none
  -- reconstruct
  let mut edges : Array (Nat × Nat) := #[]
  let mut stack : List (Nat × Nat) := [(full, root)]
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => break
    | (S, v) :: rest =>
      stack := rest
      let u := pr[S]![v]!
      if u < n then
        edges := edges.push (u, v)
        stack := (S, u) :: stack
      else
        let T := sp[S]![v]!
        if T != 0 then stack := (T, v) :: (S ^^^ T, v) :: stack
  return some (cost, edges)

end FregeDiagrams.Route
