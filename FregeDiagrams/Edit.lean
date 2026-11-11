/-
FregeDiagrams.Edit: edits of a figure's hints, written back into its source text.

An `Edit` changes one hint of one figure (a state's position, an arrow's
bend, the canvas size, …).  `applyEdit` applies it to the parsed figure and
to the text, replacing only the characters of that hint (`FigSpans`), so
comments, line breaks and the order of the other hints stay as they were.
Before the new text is returned it is parsed again and compared with the
edited figure; any difference is reported as an editor bug and nothing
changes.  Edits never touch the formula, so they cannot change a figure's
meaning (`denote` reads only the formula).
-/
import FregeDiagrams.Syntax

namespace FregeDiagrams

/-- An edit of one hint of a figure. -/
inductive Edit where
  /-- set the position hint of a state (with its label offset), adding it if absent -/
  | node (h : NodeHint)
  /-- remove the position hint of a state (it goes back to the grid) -/
  | unnode (k : Key)
  /-- set the hint of an arrow; a hint with no bend, side or `at` is removed -/
  | edge (h : EdgeHint)
  | size (w h : Nat)
  /-- set or remove the figure's `namedy` -/
  | nameDy (v : Option Int)
  /-- set or remove a loop's angle -/
  | loop (k : Key) (angle : Option Int)
  /-- fix a binder's notch in view B to open up (`true`) or down (`false`), or
  leave it to the router (`none`) -/
  | notch (x : String) (up : Option Bool)
deriving Repr, Inhabited

/-- What an edit does to the text of the hints. -/
inductive Act where
  | replace (r : HintRef) (txt : String)
  | delete (r : HintRef)
  | add (txt : String)
  | nothing
deriving Repr, Inhabited

/-- Apply an edit to the hints: the new hints, and what to do to the text. -/
def Edit.apply (h : Hints) : Edit → Hints × Act
  | .node nh =>
    match h.nodes.findIdx? (·.key == nh.key) with
    | some i => ({ h with nodes := h.nodes.set i nh }, .replace (.node i) nh.print)
    | none => ({ h with nodes := h.nodes ++ [nh] }, .add nh.print)
  | .unnode k =>
    match h.nodes.findIdx? (·.key == k) with
    | some i => ({ h with nodes := h.nodes.eraseIdx i }, .delete (.node i))
    | none => (h, .nothing)
  | .edge eh =>
    let empty := eh.bend.isNone && eh.side.isNone && eh.at_.isNone
    let same (e : EdgeHint) := e.src == eh.src && e.tgt == eh.tgt && e.occ == eh.occ && e.panel == eh.panel
    match h.edges.findIdx? same, empty with
    | some i, true => ({ h with edges := h.edges.eraseIdx i }, .delete (.edge i))
    | some i, false => ({ h with edges := h.edges.set i eh }, .replace (.edge i) eh.print)
    | none, true => (h, .nothing)
    | none, false => ({ h with edges := h.edges ++ [eh] }, .add eh.print)
  | .size w ht =>
    let t := s!"size {printPair w ht}"
    ({ h with size := some (w, ht) }, if h.size.isSome then .replace .size t else .add t)
  | .nameDy v =>
    match h.nameDy, v with
    | some _, some v => ({ h with nameDy := some v }, .replace .namedy s!"namedy {v}")
    | some _, none => ({ h with nameDy := none }, .delete .namedy)
    | none, some v => ({ h with nameDy := some v }, .add s!"namedy {v}")
    | none, none => (h, .nothing)
  | .loop k a =>
    match h.loops.findIdx? (·.key == k), a with
    | some i, some a =>
      let l : LoopHint := { key := k, angle := a }
      ({ h with loops := h.loops.set i l }, .replace (.loop i) l.print)
    | some i, none => ({ h with loops := h.loops.eraseIdx i }, .delete (.loop i))
    | none, some a =>
      let l : LoopHint := { key := k, angle := a }
      ({ h with loops := h.loops ++ [l] }, .add l.print)
    | none, none => (h, .nothing)
  | .notch x up =>
    match h.notches.findIdx? (·.1 == x), up with
    | some i, some u => ({ h with notches := h.notches.set i (x, u) }, .replace (.notch i) (notchPrint (x, u)))
    | some i, none => ({ h with notches := h.notches.eraseIdx i }, .delete (.notch i))
    | none, some u => ({ h with notches := h.notches ++ [(x, u)] }, .add (notchPrint (x, u)))
    | none, none => (h, .nothing)

def splice (cs : List Char) (a b : Nat) (ins : String) : List Char :=
  cs.take a ++ ins.toList ++ cs.drop b

/-- Apply the text side of an edit to the source (as characters).  A replaced
or deleted hint is the last one with that reference (for `size` and `namedy`
the last one written is the one in force). -/
def Act.text (src : List Char) (fs : FigSpans) : Act → Except String (List Char)
  | .nothing => .ok src
  | .replace r t =>
    match fs.hints.reverse.find? (·.1 == r) with
    | some (_, sp) => .ok (splice src sp.start.off sp.stop.off t)
    | none => .error "editor bug: no source span for the hint"
  | .delete r =>
    let hs := fs.hints
    match (hs.zipIdx.reverse.find? (·.1.1 == r)) with
    | none => .error "editor bug: no source span for the hint"
    | some ((_, sp), j) =>
      if j > 0 then
        -- with the comma before it
        .ok (splice src hs[j-1]!.2.stop.off sp.stop.off "")
      else if h : 1 < hs.length then
        -- the first of several: with the comma after it
        .ok (splice src sp.start.off hs[1].2.start.off "")
      else
        -- the only hint: the brackets go too, with one space before them
        match fs.open_, fs.close with
        | some o, some c =>
          let a := if o.start.off > 0 && src[o.start.off - 1]? == some ' ' then o.start.off - 1 else o.start.off
          .ok (splice src a c.stop.off "")
        | _, _ => .error "editor bug: hints without brackets"
  | .add t =>
    match fs.close with
    | some c => .ok (splice src c.start.off c.start.off (if fs.hints.isEmpty then t else ", " ++ t))
    | none => .ok (splice src fs.eq.start.off fs.eq.start.off ("[" ++ t ++ "] "))

/-- Apply an edit to figure `fig` of the source text `src`.  The result is
the new text; it is checked to parse to the edited figure, with every other
figure unchanged. -/
def applyEdit (src : String) (fig : String) (e : Edit) : Except String String := do
  let figs ← parseFileSpans src
  let some i := figs.findIdx? (·.1.name == fig) | throw s!"no figure {fig}"
  let (f, fs) := figs[i]!
  let (h', act) := e.apply f.hints
  let out := String.ofList (← act.text src.toList fs)
  let figs' ← (parseFile out).mapError (s!"editor bug: the edited text does not parse ({·}); nothing changed")
  let expected := (figs.map (·.1)).set i { f with hints := h' }
  if figs' != expected then
    throw "editor bug: the edited text does not parse to the edited figure; nothing changed"
  return out

end FregeDiagrams
