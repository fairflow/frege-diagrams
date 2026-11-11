/-
FregeDiagrams.Latex: a figure's formula in chained-relation notation.

The output uses these macros (definitions in `docs/GUIDE.md`, section 3): `\sq` (`⊑`), `\SqR` (`⊑;R`), `\Y`
(`⊑;R;⊑`), `\reach` (`⇝`), `\nF` (`∉ F`), `\imp`; `^{\circ}` restricts a
relation to infallible targets, and a composite is written `({\sq};R;{\le})`.

* A `°` on a state is absorbed into the relation that reaches it (`≤` into
  `x°` is `⊑`, `R` into `x°` is `R^{\circ}`, `⊑;R;≤` into `y°` is `\Y`).
  Where it cannot be (after `⇝`, `=`, `≠`, or on the first state of a
  chain) it is dropped if the state is already known to be infallible (the
  free state `s`, or a state shown infallible earlier: in a hypothesis, in an
  earlier conjunct, or in a bounding quantifier), and written `x\nF`
  otherwise.
* `all u. if s <= u°, … then C` is the bounded `\forall u\sqsupseteq s.\ …`,
  and `ex u. (s <= u° & …)` the bounded `\exists u\sqsupseteq s.\ …`.
* Adjacent conjuncts that are chains, the second starting where the first
  ends, are written as one chain (`a ρ b ∧ b σ c` is `a ρ b σ c`).
* A text leaf is typeset by its meaning; a text without one as `\text{…}`.
* Quantifiers and implications extend as far right as possible; parentheses
  are added where that would capture too much.
-/
import FregeDiagrams.Fig

namespace FregeDiagrams

/-- The LaTeX of a Greek letter, braced so that a following letter cannot run
into the macro name; capitals that look like Latin letters are those letters. -/
def greekTex (c : Char) : String :=
  let lower := "αβγδεζηθικλμνξοπρςστυφχψω".toList.zip
    ["\\alpha", "\\beta", "\\gamma", "\\delta", "\\varepsilon", "\\zeta", "\\eta", "\\theta",
     "\\iota", "\\kappa", "\\lambda", "\\mu", "\\nu", "\\xi", "o", "\\pi", "\\rho", "\\varsigma",
     "\\sigma", "\\tau", "\\upsilon", "\\varphi", "\\chi", "\\psi", "\\omega"]
  let upper := "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ".toList.zip
    ["A", "B", "\\Gamma", "\\Delta", "E", "Z", "H", "\\Theta", "I", "K", "\\Lambda", "M", "N", "\\Xi",
     "O", "\\Pi", "P", "\\Sigma", "T", "\\Upsilon", "\\Phi", "X", "\\Psi", "\\Omega"]
  match (lower ++ upper).lookup c with
  | some t => if t.startsWith "\\" then "{" ++ t ++ "}" else t
  | none => c.toString

def latexName (s : String) : String :=
  let cs := s.toList
  let base := (cs.filter (!isSubscriptDigit ·)).map fun c => if c == '′' then '\'' else c
  let subs := (cs.filter isSubscriptDigit).map fun c => Char.ofNat (c.toNat - '₀'.toNat + '0'.toNat)
  String.join (base.map greekTex) ++ match subs with
    | [] => ""
    | [d] => "_" ++ String.singleton d
    | ds => "_{" ++ String.ofList ds ++ "}"

def baseTex : Rel → String
  | .le => "{\\le}" | .sqle => "{\\sq}" | .R => "R" | .Rinf => "R^{\\circ}"
  | .reach => "{\\reach}" | .eq => "{=}" | .ne => "{\\neq}"
  | .named l _ => "{" ++ l ++ "}"

def relTex : Composite → String
  | [.le] => "\\le" | [.sqle] => "\\sq" | [.R] => "\\mathrel{R}" | [.Rinf] => "\\mathrel{R^{\\circ}}"
  | [.reach] => "\\reach" | [.eq] => "=" | [.ne] => "\\neq"
  | [.named l _] => "\\mathrel{" ++ l ++ "}"
  | [.sqle, .R] => "\\SqR" | [.sqle, .R, .sqle] => "\\Y"
  | rs => "\\mathrel{(" ++ ";".intercalate (rs.map baseTex) ++ ")}"

/-- The relation with an infallible target folded in, if it can be. -/
def absorb (r : Composite) : Option Composite :=
  match r.getLast? with
  | some .le => some (r.dropLast ++ [.sqle])
  | some .sqle | some .Rinf => some r
  | some .R => some (r.dropLast ++ [.Rinf])
  | _ => none

def texEscape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '\\' => "\\textbackslash{}" | '{' => "\\{" | '}' => "\\}" | '_' => "\\_" | '&' => "\\&"
    | '%' => "\\%" | '#' => "\\#" | '$' => "\\$" | '^' => "\\^{}" | '~' => "\\~{}"
    | c => String.singleton c) ""

/-- A chain, with the states known to be infallible: `(text, level, known)`. -/
def chainTex (K : List String) (st : St) (steps : List (Composite × St)) :
    String × Nat × List String := Id.run do
  if steps.isEmpty then
    return (latexName st.name ++ (if st.inf then "\\nF" else ""), 3,
      if st.inf then st.name :: K else K)
  let mut K := K
  let mut out := latexName st.name
  let mut extra : Array String := #[]
  if st.inf && !K.contains st.name then extra := extra.push st.name
  if st.inf then K := st.name :: K
  let n := steps.length
  let mut i := 0
  for (r, t) in steps do
    i := i + 1
    let (r', absorbed) := if t.inf then
        match absorb r with | some r' => (r', true) | none => (r, false)
      else (r, false)
    out := out ++ relTex r' ++ " " ++ latexName t.name
    if t.inf && !absorbed && !K.contains t.name then
      if i == n then out := out ++ "\\nF" else extra := extra.push t.name
    if t.inf then K := t.name :: K
  let res := extra.foldl (fun o x => o ++ " \\wedge " ++ latexName x ++ "\\nF") out
  return (res, if extra.isEmpty then 3 else 2, K)

def paren (s : String) : String := "(" ++ s ++ ")"

/-- `a <= x°` or `a <=° x`, with `a` not `x` and not among `avoid`: the
bound of a bounded quantifier over `x`. -/
def boundOf (K : List String) (x : String) (avoid : List String) : Form → Option String
  | .chain a [(r, t)] =>
    if t.name == x && a.name != x && !avoid.contains a.name && (!a.inf || K.contains a.name) &&
       (r == [.sqle] || (r == [.le] && t.inf)) then some a.name else none
  | _ => none

/-- Merge adjacent chains `a … b` and `b … c` of a conjunction. -/
partial def mergeChains : List Form → List Form
  | .chain a s₁ :: .chain b s₂ :: rest =>
    let lastName := match s₁.getLast? with | some (_, t) => t.name | none => a.name
    if !s₁.isEmpty && !s₂.isEmpty && lastName == b.name then
      let s₁' := match s₁.reverse with
        | (r, t) :: init => (init.reverse ++ [(r, { t with inf := t.inf || b.inf })])
        | [] => []
      mergeChains (.chain a (s₁' ++ s₂) :: rest)
    else .chain a s₁ :: mergeChains (.chain b s₂ :: rest)
  | f :: rest => f :: mergeChains rest
  | [] => []

/-- `(text, level, known)`; levels: 0 open to the right (quantifier,
implication), 1 disjunction, 2 conjunction, 3 atomic. -/
partial def Form.tex (K : List String) : Form → String × Nat × List String
  | .chain st steps => chainTex K st steps
  | .text _ (some m) => m.tex K
  | .text s none => ("\\text{" ++ texEscape s ++ "}", 3, K)
  | .not b =>
    let (t, l, _) := b.tex K
    ("\\neg " ++ (if l == 1 || l == 2 then paren t else t), if l == 0 then 0 else 3, K)
  | .all x b =>
    let K := K.erase x
    match b with
    | .imp (h :: hs) c =>
      match boundOf K x [] h with
      | some a =>
        let body := if hs.isEmpty then c else .imp hs c
        let (t, _, _) := body.tex (x :: K)
        (s!"\\forall {latexName x}\\sqsupseteq {latexName a}.\\ " ++ t, 0, K)
      | none => (s!"\\forall {latexName x}.\\ " ++ (b.tex K).1, 0, K)
    | _ => (s!"\\forall {latexName x}.\\ " ++ (b.tex K).1, 0, K)
  | .ex x b =>
    -- consecutive `ex` binders, then the body
    let rec binders : Form → List String × Form
      | .ex y c => let (ys, d) := binders c; (y :: ys, d)
      | d => ([], d)
    let (ys, body) := binders b
    let K' := (x :: ys).foldl List.erase K
    let others := String.join (ys.map fun y => s!"\\exists {latexName y}.\\ ")
    match body with
    | .and (c₁ :: rest) =>
      match boundOf K' x ys c₁ with
      | some a =>
        let inner := match rest with | [f] => f | fs => .and fs
        let (t, _, _) := inner.tex (x :: K')
        (s!"\\exists {latexName x}\\sqsupseteq {latexName a}.\\ " ++ others ++ t, 0, K)
      | none => (s!"\\exists {latexName x}.\\ " ++ others ++ (body.tex K').1, 0, K)
    | _ => (s!"\\exists {latexName x}.\\ " ++ others ++ (body.tex K').1, 0, K)
  | .imp hs c => Id.run do
    let mut K' := K
    let mut parts : Array String := #[]
    for h in hs do
      let (t, l, K'') := h.tex K'
      parts := parts.push (if l < 2 then paren t else t)
      K' := K''
    let (tc, _, _) := c.tex K'
    -- the comma is currying: H₀ → (H₁ → … → C), as the tree draws it
    let rec cur : List String → String
      | [] => tc
      | [p] => p ++ "\\ \\imp\\ " ++ tc
      | p :: ps => p ++ "\\ \\imp\\ (" ++ cur ps ++ ")"
    return (cur parts.toList, 0, K)
  | .and ps => Id.run do
    let ps := mergeChains ps
    let mut K' := K
    let mut parts : Array String := #[]
    let mut lastLevel := 3
    let n := ps.length
    let mut i := 0
    for p in ps do
      i := i + 1
      let (t, l, K'') := p.tex K'
      let isLast := i == n
      parts := parts.push (if l == 1 || (l == 0 && !isLast) then paren t else t)
      K' := K''
      lastLevel := l
    return (" \\wedge ".intercalate parts.toList, if lastLevel == 0 then 0 else 2, K')
  | .or ps =>
    let parts := ps.map fun p => let (t, l, _) := p.tex K; if l < 2 then paren t else t
    (" \\vee ".intercalate parts, 1, K)

/-- The formula of a figure, for an arbitrary infallible `s` (left implicit). -/
def Fig.toLatex (d : Fig) : String := (d.body.tex ["s"]).1

end FregeDiagrams
