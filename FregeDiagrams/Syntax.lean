/-
FregeDiagrams.Syntax: the textual syntax of figures, a printer and a parser.

The definition for users, with the tokens, the EBNF and syntax diagrams, is
`docs/LANGUAGE.md` (generated from `docs/tools/grammar.py`); keep the three in
step (CONTRIBUTING.md).  A summary:

```
file   ::= figure*
figure ::= "fig" NAME hints? "=" form
form   ::= "all" NAME "." form | "ex" NAME "." form | "not" form
         | "if" form ("," form)* "then" form
         | "(" form ("&" form)+ ")" | "(" form ("|" form)+ ")" | "(" form ")"
         | STRING ("{" form "}")?                 text leaf, with its meaning
         | chain
chain  ::= state (rel state)*
state  ::= NAME "°"?                              ° = infallible
rel    ::= base (";" base)*                       composite: one arrow
base   ::= "<=" | "<=°" | "R" | "R°" | "~>" | "=" | "!="
         | "-[" LABEL "]-" | "-[" LABEL "]->"        labelled relation
hints  ::= "[" (hint ("," hint)*)? "]"
hint   ::= "size" "(" NAT "," NAT ")" | "views" ("A" | "B")
         | key "@" "(" INT "," INT ")" ("label" "(" INT "," INT ")")?
         | "edge" NAME ">" NAME ("#" NAT)? ("/" NAT)?
             ("bend" INT | "side" ("+" | "-") | "at" DEC)*        any order
         | "loop" key INT | "namedy" INT | "notch" NAME ("up" | "down")
         | "route" NAME pair pair+ (";" pair pair+)*
         | "text" "(" INT "," INT ")"
             ("black" | "red" | "grey" | NAT | "middle" | "italic")* STRING
key    ::= NAME ("/" NAT)?                        state NAME of panel NAT
```

`<=°` is `⊑` (`≤` into an infallible state) and `R°` is `R` into an
infallible state; inside a composite they make the intermediate state
infallible (the hollow bead).  `~>` is `⇝ = (≤ ∪ R)*`.  A form ends at the
first `&`, `|`, `,`, `then`, `)`, `}` or `fig` it cannot consume, so the
printer needs parentheses only for `&` and `|`.  `--` starts a comment.

The round trip `parse (print d) = .ok d` for well-formed `d` is stated as
`ParsePrint` and tested (`FregeDiagrams/Test.lean`), not proved.
-/
import FregeDiagrams.Fig

namespace FregeDiagrams

/-! ## Tokens -/

inductive Tok where
  | ident (s : String)
  | num (n : Int)
  /-- a decimal with at most two fractional digits, in hundredths -/
  | dec (h : Nat)
  | str (s : String)
  | sym (s : String)
  /-- a labelled relation `-[LABEL]-` or `-[LABEL]->` -/
  | lrel (label : String) (directed : Bool)
deriving BEq, Repr, Inhabited

def Tok.show : Tok → String
  | .ident s => s
  | .num n => toString n
  | .dec h => s!"{h / 100}.{h % 100}"
  | .str s => s!"\"{s}\""
  | .sym s => s
  | .lrel l d => s!"-[{l}]-{if d then ">" else ""}"

def digitsVal (ds : List Char) : Nat := ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0

def singleSyms : List Char := ['(', ')', '[', ']', '{', '}', ',', '.', ';', '&', '|', '=', '°',
  '@', '>', '#', '/', '+', '-']

/-- A place in the source: offset (in characters), line and column (from 1). -/
structure Pos where
  off : Nat := 0
  line : Nat := 1
  col : Nat := 1
deriving BEq, Repr, Inhabited

def Pos.advance (p : Pos) (cs : List Char) : Pos :=
  cs.foldl (fun p c => if c == '\n' then { off := p.off + 1, line := p.line + 1, col := 1 }
    else { p with off := p.off + 1, col := p.col + 1 }) p

def Pos.show (p : Pos) : String := s!"line {p.line}, column {p.col}"

/-- Where a token starts and where it ends (exclusive). -/
structure Span where
  start : Pos
  stop : Pos
deriving BEq, Repr, Inhabited

/-- One step of the lexer at `cs`: a token (none for whitespace and comments)
and the rest of the input. -/
def lexOne (cs : List Char) : Except String (Option Tok × List Char) :=
  match cs with
  | [] => .ok (none, [])
  | c :: rest =>
    if c.isWhitespace then .ok (none, rest)
    else if c == '-' && rest.head? == some '[' then
      let body := rest.tail.takeWhile (· != ']')
      match rest.tail.dropWhile (· != ']') with
      | ']' :: '-' :: '>' :: rest' => .ok (some (.lrel (String.ofList body) true), rest')
      | ']' :: '-' :: rest' => .ok (some (.lrel (String.ofList body) false), rest')
      | _ => .error "a labelled relation is written -[LABEL]- or -[LABEL]->"
    else if c == '-' && rest.head? == some '-' then .ok (none, rest.dropWhile (· != '\n'))
    else if c == '<' && rest.head? == some '=' then .ok (some (.sym "<="), rest.tail)
    else if c == '~' && rest.head? == some '>' then .ok (some (.sym "~>"), rest.tail)
    else if c == '!' && rest.head? == some '=' then .ok (some (.sym "!="), rest.tail)
    else if c.isDigit || (c == '-' && (rest.head?.map Char.isDigit).getD false) then
      let neg := c == '-'
      let s := if neg then rest else cs
      let ds := s.takeWhile Char.isDigit
      let s := s.dropWhile Char.isDigit
      let int : Int := digitsVal ds
      let int := if neg then -int else int
      match s with
      | '.' :: d :: s' =>
        if d.isDigit then
          let fs := (d :: s').takeWhile Char.isDigit
          let s'' := (d :: s').dropWhile Char.isDigit
          if neg then .error "a decimal must not be negative"
          else if fs.length > 2 then .error "a decimal has at most two fractional digits"
          else
            let frac := digitsVal fs * (if fs.length == 1 then 10 else 1)
            .ok (some (.dec (100 * digitsVal ds + frac)), s'')
        else .ok (some (.num int), s)
      | _ => .ok (some (.num int), s)
    else if isIdentStart c then
      .ok (some (.ident (String.ofList (cs.takeWhile isIdentChar))), cs.dropWhile isIdentChar)
    else if c == '"' then
      let body := rest.takeWhile (· != '"')
      match rest.dropWhile (· != '"') with
      | _ :: rest' => .ok (some (.str (String.ofList body)), rest')
      | [] => .error "unterminated string"
    else if singleSyms.contains c then .ok (some (.sym (String.singleton c)), rest)
    else .error s!"unexpected character '{c}'"

/-- The tokens with their spans, and the place where the input ends.  An
error names its line and column. -/
partial def lexAux (cs : List Char) (p : Pos) (acc : Array (Tok × Span)) :
    Except String (Array (Tok × Span) × Pos) :=
  if cs.isEmpty then .ok (acc, p) else
  match lexOne cs with
  | .error e => .error s!"{p.show}: {e}"
  | .ok (t, rest) =>
    let q := p.advance (cs.take (cs.length - rest.length))
    lexAux rest q (match t with | some t => acc.push (t, ⟨p, q⟩) | none => acc)

def lexSpans (s : String) : Except String (Array (Tok × Span) × Pos) := lexAux s.toList {} #[]

def lex (s : String) : Except String (List Tok) := (lexSpans s).map (·.1.toList.map (·.1))

/-! ## Printer -/

def Rel.syntax : Rel → String
  | .le => "<=" | .sqle => "<=°" | .R => "R" | .Rinf => "R°" | .reach => "~>" | .eq => "="
  | .ne => "!="
  | .named l d => s!"-[{l}]-{if d then ">" else ""}"

def St.print (st : St) : String := st.name ++ (if st.inf then "°" else "")

def compPrint (r : Composite) : String := ";".intercalate (r.map Rel.syntax)

namespace Form

partial def print : Form → String
  | .chain st steps =>
    steps.foldl (fun acc (r, t) => acc ++ " " ++ compPrint r ++ " " ++ t.print) st.print
  | .text s none => s!"\"{s}\""
  | .text s (some m) => s!"\"{s}\" \{{m.print}}"
  | .all x b => s!"all {x}. {b.print}"
  | .ex x b => s!"ex {x}. {b.print}"
  | .not b => s!"not {b.print}"
  | .imp hs c => s!"if {", ".intercalate (hs.map print)} then {c.print}"
  | .and ps => "(" ++ " & ".intercalate (ps.map print) ++ ")"
  | .or ps => "(" ++ " | ".intercalate (ps.map print) ++ ")"

end Form

def printDec (h : Nat) : String :=
  let f := h % 100
  s!"{h / 100}.{if f < 10 then "0" else ""}{f}"

def printPair (a b : Int) : String := s!"({a},{b})"

def Key.print (k : Key) : String := k.name ++ (if k.panel != 1 then s!"/{k.panel}" else "")

def Color.print : Color → String
  | .black => "black" | .red => "red" | .grey => "grey"

def NodeHint.print (n : NodeHint) : String :=
  s!"{n.key.print}@{printPair n.x n.y}" ++
    (match n.label with | some (a, b) => s!" label {printPair a b}" | none => "")

def EdgeHint.print (e : EdgeHint) : String :=
  s!"edge {e.src}>{e.tgt}" ++ (if e.occ != 1 then s!"#{e.occ}" else "") ++
    (if e.panel != 1 then s!"/{e.panel}" else "") ++
    (match e.bend with | some b => s!" bend {b}" | none => "") ++
    (match e.side with | some true => " side +" | some false => " side -" | none => "") ++
    (match e.at_ with | some a => s!" at {printDec a}" | none => "")

def LoopHint.print (l : LoopHint) : String := s!"loop {l.key.print} {l.angle}"

def TextHint.print (t : TextHint) : String :=
  s!"text {printPair t.x t.y} {t.color.print} {t.size}" ++
    (if t.middle then " middle" else "") ++ (if t.italic then " italic" else "") ++
    s!" \"{t.s}\""

def notchPrint (n : String × Bool) : String := s!"notch {n.1} {if n.2 then "up" else "down"}"

def routePrint (r : String × List (List (Int × Int))) : String :=
  s!"route {r.1} " ++ "; ".intercalate (r.2.map fun ps => " ".intercalate (ps.map fun (a, b) => printPair a b))

def Hints.print (h : Hints) : List String :=
  (match h.size with | some (w, ht) => [s!"size {printPair w ht}"] | none => []) ++
  (match h.views with | .both => [] | .a => ["views A"] | .b => ["views B"]) ++
  h.nodes.map NodeHint.print ++
  h.edges.map EdgeHint.print ++
  h.loops.map LoopHint.print ++
  (match h.nameDy with | some v => [s!"namedy {v}"] | none => []) ++
  h.notches.map notchPrint ++
  h.routes.map routePrint ++
  h.texts.map TextHint.print

/-- The canonical text of a figure. -/
def Fig.print (d : Fig) : String :=
  let hs := d.hints.print
  let hs := if hs.isEmpty then "" else " [" ++ ",\n    ".intercalate hs ++ "]"
  s!"fig {d.name}{hs} =\n  {d.body.print}\n"

/-! ## Parser -/

/-- The parser's state: the tokens still to read, with their spans; where
the input ends; where the last token read ends. -/
structure PState where
  toks : List (Tok × Span)
  eof : Pos := {}
  prevEnd : Pos := {}

abbrev Parser := StateT PState (Except String)

def peek : Parser (Option Tok) := return (← get).toks.head?.map (·.1)

/-- Where the next token starts (the end of input if there is none). -/
def here : Parser Pos := do
  let st ← get
  return (st.toks.head?.map (·.2.start)).getD st.eof

def fail {α} (msg : String) : Parser α := do
  let st ← get
  let near := " ".intercalate ((st.toks.take 6).map (·.1.show))
  throw s!"{(← here).show}: {msg}, at: {if st.toks.isEmpty then "end of input" else near}"

def next : Parser Tok := do
  match (← get).toks with
  | (t, sp) :: ts => modify fun st => { st with toks := ts, prevEnd := sp.stop }; return t
  | [] => fail "unexpected end of input"

def isSym (s : String) : Parser Bool := return (← peek) == some (.sym s)
def isWord (s : String) : Parser Bool := return (← peek) == some (.ident s)

def expectSym (s : String) : Parser Unit := do
  if ← isSym s then discard next else fail s!"expected '{s}'"

def expectWord (s : String) : Parser Unit := do
  if ← isWord s then discard next else fail s!"expected '{s}'"

def optSym (s : String) : Parser Bool := do
  if ← isSym s then discard next; return true else return false

def name : Parser String := do
  match ← peek with
  | some (.ident s) =>
    if reserved.contains s then fail s!"'{s}' is reserved" else discard next; return s
  | _ => fail "expected a name"

def int : Parser Int := do
  match ← peek with
  | some (.num n) => discard next; return n
  | _ => fail "expected an integer"

def nat : Parser Nat := do
  let n ← int
  if n < 0 then fail "expected a natural number" else return n.toNat

def pair : Parser (Int × Int) := do
  expectSym "("; let a ← int; expectSym ","; let b ← int; expectSym ")"; return (a, b)

def decimal : Parser Nat := do
  match ← peek with
  | some (.dec h) => discard next; return h
  | some (.num n) => if n ≥ 0 then discard next; return 100 * n.toNat else fail "expected a decimal"
  | _ => fail "expected a decimal"

/-- A base relation, if one starts here. -/
def base? : Parser (Option Rel) := do
  match ← peek with
  | some (.sym "<=") => discard next; return some (if ← optSym "°" then .sqle else .le)
  | some (.ident "R") => discard next; return some (if ← optSym "°" then .Rinf else .R)
  | some (.sym "~>") => discard next; return some .reach
  | some (.sym "=") => discard next; return some .eq
  | some (.sym "!=") => discard next; return some .ne
  | some (.lrel l d) => discard next; return some (.named l d)
  | _ => return none

partial def compRest (acc : Array Rel) : Parser Composite := do
  if ← optSym ";" then
    match ← base? with
    | some b => compRest (acc.push b)
    | none => fail "expected a relation after ';'"
  else return acc.toList

def state : Parser St := do
  let n ← name
  return { name := n, inf := ← optSym "°" }

partial def chainRest (acc : Array (Composite × St)) : Parser (List (Composite × St)) := do
  match ← base? with
  | some b =>
    let r ← compRest #[b]
    let t ← state
    chainRest (acc.push (r, t))
  | none => return acc.toList

mutual
partial def form : Parser Form := do
  match ← peek with
  | some (.ident "all") => discard next; let x ← name; expectSym "."; return .all x (← form)
  | some (.ident "ex") => discard next; let x ← name; expectSym "."; return .ex x (← form)
  | some (.ident "not") => discard next; return .not (← form)
  | some (.ident "if") =>
    discard next
    let hs ← sepBy1 ","
    expectWord "then"
    return .imp hs (← form)
  | some (.sym "(") =>
    discard next
    let f ← form
    if ← isSym "&" then
      let ps ← partsRest "&" #[f]
      expectSym ")"; return .and ps
    else if ← isSym "|" then
      let ps ← partsRest "|" #[f]
      expectSym ")"; return .or ps
    else expectSym ")"; return f
  | some (.str s) =>
    discard next
    if ← optSym "{" then
      let m ← form
      expectSym "}"
      return .text s (some m)
    else return .text s none
  | some (.ident _) =>
    let st ← state
    return .chain st (← chainRest #[])
  | _ => fail "expected a formula"

partial def sepBy1 (sep : String) : Parser (List Form) := do
  let f ← form
  if ← optSym sep then return f :: (← sepBy1 sep) else return [f]

partial def partsRest (sep : String) (acc : Array Form) : Parser (List Form) := do
  if ← optSym sep then partsRest sep (acc.push (← form)) else return acc.toList
end

def key : Parser Key := do
  let n ← name
  if ← optSym "/" then return { name := n, panel := ← nat } else return { name := n }

partial def edgeOpts (e : EdgeHint) : Parser EdgeHint := do
  if ← isWord "bend" then discard next; edgeOpts { e with bend := some (← int) }
  else if ← isWord "side" then
    discard next
    if ← optSym "+" then edgeOpts { e with side := some true }
    else if ← optSym "-" then edgeOpts { e with side := some false }
    else fail "expected '+' or '-'"
  else if ← isWord "at" then discard next; edgeOpts { e with at_ := some (← decimal) }
  else return e

partial def textOpts (t : TextHint) : Parser TextHint := do
  match ← peek with
  | some (.ident "black") => discard next; textOpts { t with color := .black }
  | some (.ident "red") => discard next; textOpts { t with color := .red }
  | some (.ident "grey") => discard next; textOpts { t with color := .grey }
  | some (.ident "middle") => discard next; textOpts { t with middle := true }
  | some (.ident "italic") => discard next; textOpts { t with italic := true }
  | some (.num _) => textOpts { t with size := ← nat }
  | some (.str s) => discard next; return { t with s }
  | _ => fail "expected a text option or a string"

def hint (h : Hints) : Parser Hints := do
  match ← peek with
  | some (.ident "size") =>
    discard next
    let (w, ht) ← pair
    if w < 0 || ht < 0 then fail "negative size" else
    return { h with size := some (w.toNat, ht.toNat) }
  | some (.ident "views") =>
    discard next
    if ← isWord "A" then discard next; return { h with views := .a }
    else if ← isWord "B" then discard next; return { h with views := .b }
    else fail "expected 'A' or 'B'"
  | some (.ident "edge") =>
    discard next
    let src ← name; expectSym ">"; let tgt ← name
    let occ ← if ← optSym "#" then nat else pure 1
    let panel ← if ← optSym "/" then nat else pure 1
    let e ← edgeOpts { src, tgt, occ, panel }
    return { h with edges := h.edges ++ [e] }
  | some (.ident "namedy") =>
    discard next
    return { h with nameDy := some (← int) }
  | some (.ident "notch") =>
    discard next
    let x ← name
    let up ← if ← isWord "up" then do discard next; pure true
      else if ← isWord "down" then do discard next; pure false
      else fail "expected 'up' or 'down'"
    return { h with notches := h.notches ++ [(x, up)] }
  | some (.ident "route") =>
    discard next
    let x ← name
    let rec polyline (acc : Array (Int × Int)) (fuel : Nat) : Parser (List (Int × Int)) := do
      match fuel with
      | 0 => return acc.toList
      | fuel + 1 => if ← isSym "(" then polyline (acc.push (← pair)) fuel else return acc.toList
    let rec polylines (acc : Array (List (Int × Int))) (fuel : Nat) : Parser (List (List (Int × Int))) := do
      let p ← polyline #[] 10000
      if p.length < 2 then fail "a route's polyline needs at least two points"
      match fuel with
      | 0 => return (acc.push p).toList
      | fuel + 1 => if ← optSym ";" then polylines (acc.push p) fuel else return (acc.push p).toList
    return { h with routes := h.routes ++ [(x, ← polylines #[] 10000)] }
  | some (.ident "loop") =>
    discard next
    let k ← key
    return { h with loops := h.loops ++ [{ key := k, angle := ← int }] }
  | some (.ident "text") =>
    discard next
    let (x, y) ← pair
    let t ← textOpts { x, y, s := "" }
    return { h with texts := h.texts ++ [t] }
  | _ =>
    let k ← key
    expectSym "@"
    let (x, y) ← pair
    let label ← if ← isWord "label" then do discard next; pure (some (← pair)) else pure none
    return { h with nodes := h.nodes ++ [{ key := k, x, y, label }] }

partial def hintsRest (h : Hints) : Parser Hints := do
  if ← optSym "," then hintsRest (← hint h) else return h

def hints : Parser Hints := do
  if ← optSym "[" then
    if ← optSym "]" then return {}
    let h ← hintsRest (← hint {})
    expectSym "]"
    return h
  else return {}

/-! ## Source spans (for the editor)

A figure parsed with the spans of its parts, so that an edit can replace
exactly the text of one hint and leave everything else (comments, line
breaks, the order of hints) as it was. -/

/-- Which hint a span holds: an index into the list of its kind. -/
inductive HintRef where
  | size | views | namedy
  | node (i : Nat) | edge (i : Nat) | loop (i : Nat) | text (i : Nat) | notch (i : Nat) | route (i : Nat)
deriving BEq, Repr, Inhabited

structure FigSpans where
  whole : Span
  /-- the brackets around the hints, if written -/
  open_ : Option Span := none
  close : Option Span := none
  /-- the hints in source order -/
  hints : List (HintRef × Span) := []
  /-- the `=` before the formula -/
  eq : Span
  body : Span
deriving Repr, Inhabited

/-- The span of the next token (empty, at the end of input, if none). -/
def tokSpan : Parser Span := do
  let st ← get
  return (st.toks.head?.map (·.2)).getD ⟨st.eof, st.eof⟩

def hintS (h : Hints) : Parser (Hints × HintRef × Span) := do
  let a ← here
  let r : HintRef := match ← peek with
    | some (.ident "size") => .size
    | some (.ident "views") => .views
    | some (.ident "namedy") => .namedy
    | some (.ident "edge") => .edge h.edges.length
    | some (.ident "loop") => .loop h.loops.length
    | some (.ident "text") => .text h.texts.length
    | some (.ident "notch") => .notch h.notches.length
    | some (.ident "route") => .route h.routes.length
    | _ => .node h.nodes.length
  let h' ← hint h
  return (h', r, ⟨a, (← get).prevEnd⟩)

partial def hintsRestS (h : Hints) (acc : Array (HintRef × Span)) :
    Parser (Hints × Array (HintRef × Span)) := do
  if ← optSym "," then
    let (h, r, sp) ← hintS h
    hintsRestS h (acc.push (r, sp))
  else return (h, acc)

def hintsS : Parser (Hints × Option Span × Option Span × List (HintRef × Span)) := do
  if ← isSym "[" then
    let o ← tokSpan
    discard next
    if ← isSym "]" then
      let c ← tokSpan
      discard next
      return ({}, some o, some c, [])
    let (h, r, sp) ← hintS {}
    let (h, acc) ← hintsRestS h #[(r, sp)]
    let c ← tokSpan
    expectSym "]"
    return (h, some o, some c, acc.toList)
  else return ({}, none, none, [])

def figureS : Parser (Fig × FigSpans) := do
  let a ← here
  expectWord "fig"
  let n ← name
  let (h, o, c, hs) ← hintsS
  let e ← tokSpan
  expectSym "="
  let b0 ← here
  let body ← form
  let b1 := (← get).prevEnd
  return ({ name := n, hints := h, body },
          { whole := ⟨a, b1⟩, open_ := o, close := c, hints := hs, eq := e, body := ⟨b0, b1⟩ })

def figure : Parser Fig := (·.1) <$> figureS

partial def figuresS (acc : Array (Fig × FigSpans)) : Parser (List (Fig × FigSpans)) := do
  if (← get).toks.isEmpty then return acc.toList else figuresS (acc.push (← figureS))

partial def figures (acc : Array Fig) : Parser (List Fig) := do
  if (← get).toks.isEmpty then return acc.toList else figures (acc.push (← figure))

def runP {α} (p : Parser α) (s : String) : Except String α := do
  let (ts, eof) ← lexSpans s
  match p.run { toks := ts.toList, eof } with
  | .ok (a, { toks := [], .. }) => .ok a
  | .ok (_, { toks := rest@((_, sp) :: _), .. }) =>
    .error s!"{sp.start.show}: unexpected input after the end: {" ".intercalate ((rest.take 6).map (·.1.show))}"
  | .error e => .error e

def Fig.parse (s : String) : Except String Fig := runP figure s

/-- Parse a file of figures. -/
def parseFile (s : String) : Except String (List Fig) := runP (figures #[]) s

/-- Parse a file of figures, with the source spans of each. -/
def parseFileSpans (s : String) : Except String (List (Fig × FigSpans)) := runP (figuresS #[]) s

/-- The round trip, for one figure, as a test. -/
def Fig.roundTrips (d : Fig) : Bool :=
  match Fig.parse d.print with
  | .ok d' => d' == d
  | .error _ => false

/-- **The round trip** (stated, not proved; tested in `FregeDiagrams/Test.lean`):
printing a well-formed figure and parsing the text gives the figure back.
The converse holds only up to whitespace, comments and the order of hints of
different kinds. -/
def ParsePrint : Prop := ∀ d : Fig, d.WellFormed = true → Fig.parse d.print = .ok d

end FregeDiagrams
