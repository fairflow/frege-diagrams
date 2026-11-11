/-
FregeDiagrams.Fig: one language for the figures.

A figure is a formula (`Form`) together with layout hints (`Hints`).  The two
pictures of a figure are two *views* of it (`FregeDiagrams.View`): variant A, a
frame picture, and variant B, a Frege-style formula tree.  This library gives
figures no meaning; a client that does (a `denote` into its own frames) can
state theorems about figures obtained with `fig_of%` (`FregeDiagrams.Elab`).  Its
LaTeX formula is `Fig.toLatex` (`FregeDiagrams.Latex`); its textual syntax is
`Fig.print` / `Fig.parse` (`FregeDiagrams.Syntax`).  Lean core only.
-/
import FregeDiagrams.Tree

namespace FregeDiagrams

/-- A state occurrence in a chain: a name, and `°` (infallible). -/
structure St where
  name : String
  inf : Bool := false
deriving BEq, DecidableEq, Repr, Inhabited

/-- A figure's formula.  Colour is not written: in the pictures it follows
from position (hypotheses of an `if` black, everything else red). -/
inductive Form where
  /-- A chain `x₀ ρ₁ x₁ ρ₂ x₂ …` means `x₀ ρ₁ x₁ ∧ x₁ ρ₂ x₂ ∧ …`; each `ρᵢ` is
  a composite relation; a state written `x°` is infallible.  With no steps it
  says only what its `°` says. -/
  | chain (start : St) (steps : List (Composite × St))
  /-- A leaf in words, drawn as the text; `meaning`, a formula, is what it
  denotes and what the LaTeX shows. -/
  | text (s : String) (meaning : Option Form)
  | all (x : String) (body : Form)
  | ex (x : String) (body : Form)
  | not (body : Form)
  /-- `if H₁, …, Hₙ then C`. -/
  | imp (hyps : List Form) (concl : Form)
  | and (parts : List Form)
  | or (parts : List Form)
deriving BEq, Repr, Inhabited

/-! ## Layout hints (variant A)

A *key* names a state of the frame picture.  A disjunction draws one panel
per disjunct, each with its own states, so a key carries the panel number
(`s/2` is the state `s` of the second panel). -/

structure Key where
  name : String
  panel : Nat := 1
deriving BEq, DecidableEq, Repr, Inhabited

/-- Where a state is drawn, and where its label sits relative to it
(default `(0, -10)`). -/
structure NodeHint where
  key : Key
  x : Int
  y : Int
  label : Option (Int × Int) := none
deriving BEq, DecidableEq, Repr, Inhabited

/-- Hints for the `occ`-th arrow from `src` to `tgt` (in drawing order). -/
structure EdgeHint where
  src : String
  tgt : String
  occ : Nat := 1
  panel : Nat := 1
  /-- signed sagitta in pixels. -/
  bend : Option Int := none
  /-- `true`: the notch opens to the `+` side. -/
  side : Option Bool := none
  /-- where the notch sits, in hundredths of the arrow's length. -/
  at_ : Option Nat := none
deriving BEq, DecidableEq, Repr, Inhabited

/-- The direction (degrees) in which a self-loop leaves its state. -/
structure LoopHint where
  key : Key
  angle : Int
deriving BEq, DecidableEq, Repr, Inhabited

inductive Color where
  | black | red | grey
deriving BEq, DecidableEq, Repr, Inhabited

/-- A caption: decoration only, no meaning. -/
structure TextHint where
  x : Int
  y : Int
  s : String
  color : Color := .grey
  size : Nat := 11
  middle : Bool := false
  italic : Bool := false
deriving BEq, DecidableEq, Repr, Inhabited

/-- Which pictures a figure has. -/
inductive Views where
  | both | a | b
deriving BEq, DecidableEq, Repr, Inhabited

structure Hints where
  size : Option (Nat × Nat) := none
  views : Views := .both
  nodes : List NodeHint := []
  edges : List EdgeHint := []
  loops : List LoopHint := []
  texts : List TextHint := []
  /-- this figure's notch-name offset, overriding `--notch-name-offset` -/
  nameDy : Option Int := none
  /-- view B: binders whose notch is fixed to open upwards (`true`) or
  downwards (`false`); the router does not turn these over -/
  notches : List (String × Bool) := []
deriving BEq, DecidableEq, Repr, Inhabited

/-- A figure: `fig NAME [hints] = form`. -/
structure Fig where
  name : String
  hints : Hints := {}
  body : Form
deriving BEq, Repr, Inhabited

/-! ## Names and well-formedness -/

def isSubscriptDigit (c : Char) : Bool := '₀' ≤ c && c ≤ '₉'

/-- A Greek letter: `Α`–`Ω` (without the unassigned U+03A2) and `α`–`ω`
(with the final sigma `ς`). -/
def isGreekLetter (c : Char) : Bool :=
  ('Α' ≤ c && c ≤ 'Ω' && c.toNat != 0x3A2) || ('α' ≤ c && c ≤ 'ω')

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || isGreekLetter c

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '′' || isSubscriptDigit c || isGreekLetter c

/-- Words with a fixed meaning in a formula; no name may be one of them. -/
def reserved : List String := ["fig", "all", "ex", "not", "if", "then", "R"]

/-- Words with a fixed meaning at the start of a hint. -/
def hintWords : List String := ["size", "views", "edge", "loop", "text", "namedy", "notch"]

def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentChar && !reserved.contains s

/-- What can be written between the quotes of a text. -/
def isTextOK (s : String) : Bool := !s.toList.contains '"'

namespace Form

/-- The syntactic side condition of the round trip `parse (print d) = .ok d`:
names are identifiers, texts have no `"`, every `&`/`|` has at least two
parts, every `if` at least one hypothesis, every relation at least one
stretch. -/
partial def WellFormed : Form → Bool
  | .chain st steps => isIdent st.name &&
      steps.all fun (r, t) => !r.isEmpty && isIdent t.name
  | .text s m => isTextOK s && (match m with | none => true | some f => f.WellFormed)
  | .all x b | .ex x b => isIdent x && b.WellFormed
  | .not b => b.WellFormed
  | .imp hs c => !hs.isEmpty && hs.all WellFormed && c.WellFormed
  | .and ps | .or ps => ps.length ≥ 2 && ps.all WellFormed

end Form

def Key.WellFormed (k : Key) : Bool := isIdent k.name

def Hints.WellFormed (h : Hints) : Bool :=
  h.nodes.all (fun n => n.key.WellFormed && !hintWords.contains n.key.name) &&
  h.edges.all (fun e => isIdent e.src && isIdent e.tgt) &&
  h.loops.all (·.key.WellFormed) &&
  h.texts.all (isTextOK ·.s) &&
  h.notches.all (isIdent ·.1)

def Fig.WellFormed (d : Fig) : Bool := isIdent d.name && d.hints.WellFormed && d.body.WellFormed

/-! ## Display names

Names are written as they are displayed (`s′`, `t₁`); an ASCII `'` displays
as `′`. -/

def dispName (s : String) : String := s.map fun c => if c == '\'' then '′' else c
end FregeDiagrams
