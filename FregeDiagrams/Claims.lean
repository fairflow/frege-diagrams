/-
FregeDiagrams.Claims: every claimed figure has its theorem.

A figure with one judgement stroke (`judgement claim`, the default) claims
its formula.  Tag the theorem that states it:

    @[figure_claim "serial"] theorem fig_serial : … := …

and check a whole figure source:

    #figure_claims myFigs

`#figure_claims SRC` parses `SRC : String` and fails, naming each figure,
when a claimed figure has no theorem tagged with its name.  It does not
check claims that cannot be stated: a **schematic** figure, one with a text
leaf without a meaning (`"A"`, `"hypothesis 1"`), such as the legends and
bracketing examples.  Definitions and contents claim nothing and are not
checked.  On success it lists each claim with its theorems.

The tag says which theorem states the figure; that the theorem's statement
is about that figure (for example, that it mentions `fig_of% SRC "NAME"`)
is the client's to ensure, since the library gives figures no meaning.  A
tag must name a theorem; tags are matched by figure name, so two sources
checked in one project should not use the same figure names.
-/
import Lean
import FregeDiagrams.Elab

namespace FregeDiagrams

open Lean Elab Command

/-- A formula is schematic when it has a text leaf without a meaning: it
stands for a form of statement, not a statement. -/
partial def Form.schematic : Form → Bool
  | .chain .. => false
  | .text _ none => true
  | .text _ (some f) => f.schematic
  | .all _ b | .ex _ b | .not b => b.schematic
  | .imp hs c => hs.any (·.schematic) || c.schematic
  | .and ps | .or ps => ps.any (·.schematic)

syntax (name := figureClaim) "figure_claim " str : attr

/-- `@[figure_claim "NAME"]`: this theorem states the claimed figure NAME. -/
initialize figureClaimAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `figureClaim
    descr := "this theorem states the claimed figure of this name (see #figure_claims)"
    getParam := fun decl stx => do
      let some s := stx[1].isStrLit? | throwError "figure_claim: expected a figure name in quotes"
      let info ← getConstInfo decl
      unless info matches .thmInfo _ do
        throwError "figure_claim: {decl} is not a theorem; tag the theorem that states figure {s}"
      return s }

/-- Every tagged theorem with its figure name, imported or local. -/
def figureClaims (env : Environment) : Array (Name × String) := Id.run do
  let mut out := #[]
  for i in [0:env.allImportedModuleNames.size] do
    out := out ++ figureClaimAttr.ext.getModuleEntries env i
  for (n, s) in (figureClaimAttr.ext.getState env).2 do
    out := out.push (n, s)
  return out

/-- `#figure_claims SRC`: every claimed, non-schematic figure of the figure
source `SRC : String` has a theorem tagged `@[figure_claim "NAME"]`. -/
elab "#figure_claims " src:term : command => do
  let text ← liftTermElabM (evalString src)
  let figs ← match parseFile text with
    | .ok fs => pure fs
    | .error e => throwErrorAt src "#figure_claims: {src} does not parse: {e}"
  let tags := figureClaims (← getEnv)
  let mut lines : Array String := #[]
  let mut missing : Array String := #[]
  for f in figs do
    let thms := (tags.filter (·.2 == f.name)).map (·.1)
    let thmStr := ", ".intercalate (thms.toList.map toString)
    match f.hints.judgement with
    | .definition => lines := lines.push s!"{f.name}: definition"
    | .content =>
      lines := lines.push s!"{f.name}: content{if thms.isEmpty then "" else s!" (tagged {thmStr}, but a content claims nothing)"}"
    | .claim =>
      if !thms.isEmpty then lines := lines.push s!"{f.name}: claim, {thmStr}"
      else if f.body.schematic then lines := lines.push s!"{f.name}: claim, schematic (not checked)"
      else
        lines := lines.push s!"{f.name}: claim, NO THEOREM"
        missing := missing.push f.name
  let report := "\n".intercalate lines.toList
  if missing.isEmpty then
    logInfoAt src m!"#figure_claims {src}: {figs.length} figures\n{report}"
  else
    throwErrorAt src m!"#figure_claims {src}: no theorem tagged @[figure_claim \"NAME\"] for {", ".intercalate missing.toList}\n{report}"

end FregeDiagrams
