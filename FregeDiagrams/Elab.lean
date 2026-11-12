/-
FregeDiagrams.Elab: figures as Lean terms.

`fig_of% SRC "NAME"` evaluates `SRC`, a term of type `String` (typically
the name of a `def` holding a figure source, such as `exampleSource`), at
elaboration time, parses it with `parseFile`, and is the figure `NAME` as a
closed term of type `Fig`.  A parse error or a missing figure is an
elaboration error.

    def myFigs : String := r#"fig trans = all t. if s <= u, u <= t then s <= t"#
    def trans : Fig := fig_of% myFigs "trans"

So a theorem about `trans` is about the very text that `lake exe framediag
--fig` draws, provided the figure file and the `def` hold the same text (keep
the figures in the `def` and write the file from it, or the other way round).
Because `SRC` is an ordinary term, editing the `def` re-elaborates every use:
Lake tracks the dependency, which it would not for a file read from disk.
`SRC` must be computable (it is run by the interpreter).
-/
import Lean.ToExpr
import Lean.Elab.Eval
import FregeDiagrams.Syntax

namespace FregeDiagrams

open Lean Elab Term

deriving instance ToExpr for Rel
deriving instance ToExpr for St
deriving instance ToExpr for Form
deriving instance ToExpr for Key
deriving instance ToExpr for NodeHint
deriving instance ToExpr for EdgeHint
deriving instance ToExpr for LoopHint
deriving instance ToExpr for Color
deriving instance ToExpr for TextHint
deriving instance ToExpr for Views
deriving instance ToExpr for Judgement
deriving instance ToExpr for Hints
deriving instance ToExpr for Fig

private unsafe def evalStringUnsafe (stx : Syntax) : TermElabM String :=
  evalTerm String (mkConst ``String) stx

/-- Evaluate a term of type `String` at elaboration time (used by `fig_of%`
and `#figure_claims`). -/
@[implemented_by evalStringUnsafe]
opaque evalString (stx : Syntax) : TermElabM String

/-- `fig_of% SRC "NAME"`: the figure `NAME` of the figure source `SRC : String`,
parsed at elaboration time. -/
elab "fig_of% " src:term:max n:str : term => do
  let text ← evalString src
  match parseFile text with
  | .error e => throwErrorAt src "fig_of%: {src} does not parse: {e}"
  | .ok figs =>
    match figs.find? (·.name == n.getString) with
    | some f => return toExpr f
    | none => throwErrorAt n "fig_of%: no figure {n.getString} in {src}"

end FregeDiagrams
