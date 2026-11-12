/-
FregeDiagrams.Serve: `framediag --serve`, the drawing server of the editor.

One JSON object per line on standard input, one reply per line on standard
output.  The server keeps no state: every request carries the whole source
text, so the editor's undo history is a list of texts and is exact.

Requests (`op`):

* `parse` `{text}` → `{ok, figs: [{name, views, hasSize, w, h, namedy, judgement}]}` or `{ok: false, error}`
* `render` `{text, fig, opts}` → `{ok, a, b}`: view A (annotated, see
  `DrawOpts.annotate`) and view B as SVG text, `null` for a view the figure
  does not have (or did not ask for: `only` is `"a"` or `"b"`).  `opts`: `links`, `hideBound` (booleans), `nameDy`,
  `spacing` (numbers).
* `edit` `{text, fig, edit}` → `{ok, text}`: the source after the edit
  (`FregeDiagrams.Edit`), checked to re-parse to the edited figure.
* `body` `{text, fig}` → `{ok, body, tex}`: the formula as printed, and as
  LaTeX (the editor compares formulas to tell a layout change from a change
  of meaning).
* `lint` `{text, fig}` → `{ok, items: [{sev, msg, sel, fix, fixLabel}]}`: the
  checks of `FregeDiagrams.Lint`; `fix` is an `edit` object, or `null`.
* `check` `{text, fig, opts}` → `{ok, problems: [string], notes: [string]}`:
  the layout checks of `--check` for view B (links, names shown and hidden).

`edit` objects (`kind`): `node {name, panel, x, y, label: [dx,dy] | null}`,
`unnode {name, panel}`, `edge {src, tgt, occ, panel, bend, side: "+"|"-"|null, at}`,
`size {w, h}`, `namedy {v}`, `judgement {v: "claim"|"definition"|"content"}`, `loop {name, panel, angle}`, `notch {name, dir: "up"|"down"}`,
`route {name, polys: [[[x,y],…],…]}` (`null` removes).  `render` also returns `stale`: the
binders whose `route` pin no longer fits (drawn routed automatically), `setAside`: the
binders whose pin was set aside because the view options change the layout (names
hidden, another notch-name offset; not an error), and `pinsApply`: whether pins are
used with these options (`DrawOpts.pinsApply`).
-/
import Lean.Data.Json
import FregeDiagrams.View
import FregeDiagrams.Syntax
import FregeDiagrams.Latex
import FregeDiagrams.Edit
import FregeDiagrams.Lint

namespace FregeDiagrams.Serve

open Lean

def err (msg : String) : Json := Json.mkObj [("ok", false), ("error", msg)]

def okWith (fields : List (String × Json)) : Json := Json.mkObj (("ok", (true : Json)) :: fields)

def getStr (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def getInt (j : Json) (k : String) : Except String Int := j.getObjValAs? Int k
def getNat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k

/-- An optional field: absent or `null` is `none`. -/
def getOpt {α} [FromJson α] (j : Json) (k : String) : Except String (Option α) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => (fromJson? v).map some

def getBool (j : Json) (k : String) : Bool := (j.getObjValAs? Bool k).toOption.getD false

def getFloat (j : Json) (k : String) : Option Float :=
  match j.getObjVal? k with
  | .ok (.num n) => some n.toFloat
  | _ => none

def keyOf (j : Json) : Except String Key := do
  return { name := ← getStr j "name", panel := (← getOpt (α := Nat) j "panel").getD 1 }

def decodeEdit (j : Json) : Except String Edit := do
  match ← getStr j "kind" with
  | "node" =>
    let label ← match j.getObjVal? "label" with
      | .ok (.arr #[a, b]) => do
        let a : Int ← fromJson? a
        let b : Int ← fromJson? b
        pure (some (a, b))
      | _ => pure none
    return .node { key := ← keyOf j, x := ← getInt j "x", y := ← getInt j "y", label }
  | "unnode" => return .unnode (← keyOf j)
  | "edge" =>
    let side ← match ← getOpt (α := String) j "side" with
      | some "+" => pure (some true)
      | some "-" => pure (some false)
      | none => pure none
      | some s => throw s!"side must be + or -, not {s}"
    return .edge { src := ← getStr j "src", tgt := ← getStr j "tgt",
                   occ := (← getOpt j "occ").getD 1, panel := (← getOpt j "panel").getD 1,
                   bend := ← getOpt j "bend", side, at_ := ← getOpt j "at" }
  | "size" => return .size (← getNat j "w") (← getNat j "h")
  | "namedy" => return .nameDy (← getOpt j "v")
  | "judgement" =>
    match ← getStr j "v" with
    | "claim" => return .judgement .claim
    | "definition" => return .judgement .definition
    | "content" => return .judgement .content
    | s => throw s!"judgement must be claim, definition or content, not {s}"
  | "loop" => return .loop (← keyOf j) (← getOpt j "angle")
  | "route" =>
    let ps : Option (List (List (Int × Int))) ← match j.getObjVal? "polys" with
      | .ok .null | .error _ => pure none
      | .ok v => do
        let raw : List (List (List Int)) ← fromJson? v
        pure (some (raw.map fun p => p.map fun xy => (xy.getD 0 0, xy.getD 1 0)))
    return .route (← getStr j "name") ps
  | "notch" =>
    let up ← match ← getOpt (α := String) j "dir" with
      | some "up" => pure (some true)
      | some "down" => pure (some false)
      | none => pure none
      | some s => throw s!"dir must be up or down, not {s}"
    return .notch (← getStr j "name") up
  | k => throw s!"unknown edit kind {k}"

def judgementStr : Judgement → String
  | .claim => "claim" | .definition => "definition" | .content => "content"

def optJson {α} [ToJson α] : Option α → Json
  | some a => toJson a
  | none => .null

def keyFields (k : Key) : List (String × Json) := [("name", k.name), ("panel", k.panel)]

/-- The inverse of `decodeEdit`. -/
def encodeEdit : Edit → Json
  | .node h => Json.mkObj ([("kind", ("node" : Json))] ++ keyFields h.key ++ [("x", toJson h.x), ("y", toJson h.y),
      ("label", match h.label with | some (a, b) => Json.arr #[toJson a, toJson b] | none => .null)])
  | .unnode k => Json.mkObj ([("kind", ("unnode" : Json))] ++ keyFields k)
  | .edge e => Json.mkObj [("kind", "edge"), ("src", e.src), ("tgt", e.tgt), ("occ", e.occ),
      ("panel", e.panel), ("bend", optJson e.bend),
      ("side", match e.side with | some true => "+" | some false => "-" | none => Json.null),
      ("at", optJson e.at_)]
  | .size w h => Json.mkObj [("kind", "size"), ("w", w), ("h", h)]
  | .nameDy v => Json.mkObj [("kind", "namedy"), ("v", optJson v)]
  | .judgement j => Json.mkObj [("kind", "judgement"), ("v", judgementStr j)]
  | .loop k a => Json.mkObj ([("kind", ("loop" : Json))] ++ keyFields k ++ [("angle", optJson a)])
  | .route x ps => Json.mkObj [("kind", "route"), ("name", x),
      ("polys", match ps with
        | some ps => Json.arr (ps.toArray.map fun p => Json.arr (p.toArray.map fun (a, b) => Json.arr #[toJson a, toJson b]))
        | none => Json.null)]
  | .notch x up => Json.mkObj [("kind", "notch"), ("name", x),
      ("dir", match up with | some true => "up" | some false => "down" | none => Json.null)]

def optsOf (j : Json) : DrawOpts :=
  let o := (j.getObjVal? "opts").toOption.getD (Json.mkObj [])
  let d : DrawOpts := { links := getBool o "links", hideBound := getBool o "hideBound" }
  let d := match getFloat o "nameDy" with | some v => { d with nameDy := v } | none => d
  match getFloat o "spacing" with | some v => { d with spacing := v } | none => d

def findFig (text name : String) : Except String Fig := do
  let figs ← parseFile text
  match figs.find? (·.name == name) with
  | some f => return f
  | none => throw s!"no figure {name}"

def viewsStr : Views → String
  | .both => "both" | .a => "A" | .b => "B"

def handle (j : Json) : Except String Json := do
  let text ← getStr j "text"
  match ← getStr j "op" with
  | "parse" =>
    let figs ← parseFile text
    return okWith [("figs", Json.arr (figs.toArray.map fun f =>
      let (w, h) := f.hints.size.getD (0, 0)
      Json.mkObj [("name", f.name), ("views", viewsStr f.hints.views),
                  ("hasSize", f.hints.size.isSome), ("w", w), ("h", h),
                  ("namedy", match f.hints.nameDy with | some v => toJson v | none => Json.null),
                  ("judgement", judgementStr f.hints.judgement)]))]
  | "render" =>
    let f ← findFig text (← getStr j "fig")
    let o := optsOf j
    let o := f.drawOpts o
    let only := (getStr j "only").toOption.getD ""
    let a : Json := if f.hints.views == .b || only == "b" then .null
      else (f.toDiagram { o with annotate := true }).svg
    let rb := if f.hints.views == .a || only == "a" then none
      else some (f.toTreeDiagram.render { o with annotate := true })
    let b : Json := match rb with | some r => r.svg | none => .null
    let stale : Json := Json.arr ((rb.map (·.stalePins)).getD #[] |>.map toJson)
    let setAside : Json := Json.arr ((rb.map (·.setAside)).getD #[] |>.map toJson)
    return okWith [("a", a), ("b", b), ("stale", stale), ("setAside", setAside),
                   ("pinsApply", o.pinsApply)]
  | "edit" =>
    let e ← decodeEdit (← j.getObjVal? "edit")
    return okWith [("text", ← applyEdit text (← getStr j "fig") e)]
  | "body" =>
    let f ← findFig text (← getStr j "fig")
    return okWith [("body", f.body.print), ("tex", f.toLatex)]
  | "lint" =>
    let f ← findFig text (← getStr j "fig")
    return okWith [("items", Json.arr (f.lint.map fun l => Json.mkObj [
      ("sev", match l.sev with | .error => "error" | .warning => "warning"),
      ("msg", l.msg), ("sel", l.sel),
      ("fix", match l.fix with | some e => encodeEdit e | none => .null),
      ("fixLabel", l.fixLabel)]))]
  | "check" =>
    let f ← findFig text (← getStr j "fig")
    if f.hints.views == .a then return okWith [("problems", Json.arr #[]), ("notes", Json.arr #[])]
    let o := optsOf j
    let o := f.drawOpts o
    let mut probs : Array Json := #[]
    let mut notes : Array Json := #[]
    for hb in [false, true] do
      let t : TreeDiagram := f.toTreeDiagram
      let r := t.render { o with links := true, hideBound := hb }
      let tag := if hb then " (names hidden)" else ""
      if !r.problems.isEmpty then
        probs := probs.push s!"view B{tag}: {r.problems.size} empty bigon(s) or monogon(s)"
      for x in r.stalePins do
        probs := probs.push s!"view B: the route of {x} no longer fits the layout (its notch or its states moved); it is routed automatically"
      if !r.names.isEmpty then
        probs := probs.push s!"view B{tag}: misplaced names {r.names}"
      for (outer, inner, side) in r.nesting do
        notes := notes.push s!"view B{tag}: nesting violation: {inner}'s links run outside {outer}'s on the {side} (reported, not an error)"
      notes := notes.push s!"view B{tag}: {r.nLink} link-link and {r.nTree} link-stroke crossings"
    return okWith [("problems", Json.arr probs), ("notes", Json.arr notes)]
  | op => throw s!"unknown op {op}"

/-- Serve until standard input ends. -/
partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let reply := match Json.parse line with
    | .error e => err s!"bad JSON: {e}"
    | .ok j => match handle j with
      | .ok r => r
      | .error e => err e
  -- echo the request id, if any, so the client can drop stale replies
  let reply := match (Json.parse line).toOption.bind (·.getObjVal? "id" |>.toOption) with
    | some id => reply.setObjVal! "id" id
    | none => reply
  stdout.putStrLn reply.compress
  stdout.flush
  loop stdin stdout

def serve : IO UInt32 := do
  loop (← IO.getStdin) (← IO.getStdout)
  return 0

end FregeDiagrams.Serve
