/-
`lake exe framediag OUTDIR [--fig FILE] [--no-pdf] [--links] [--hide-bound] [--spacing X] [--notch-name-offset DY] [--check] [--stats]`

`--links` joins each quantifier notch to the states it binds by one tree of
links (view B); `--hide-bound` leaves the bound names out (both views);
`--spacing X` scales the clearances of the links; `--notch-name-offset DY`
moves each bound name DY units towards its notch's open end (a figure's
`namedy` hint overrides it); `--check` and `--stats` run
the layout checks instead of drawing.  `docs/GUIDE.md` has the detail.

Parses the figures of FILE (`--fig FILE`, the normal input), or without
`--fig` the example figures (`exampleSource` in `FregeDiagrams/Examples.lean`), and
writes into OUTDIR, for each figure `NAME`:

* `NAME.svg` (view A) and `NAME_B.svg` (view B), or one of them;
* `NAME.pdf`, `NAME_B.pdf`: PDF copies for `\includegraphics`, made with
  `rsvg-convert` (an error if it is missing, unless `--no-pdf`);
* `NAME.tex`: the figure's formula in chained-relation notation
  (`Fig.toLatex`), for `\formula{NAME}`;

and `legend.svg`/`.pdf`, the key to view A (`FregeDiagrams/Legend.lean`).
-/
import FregeDiagrams.View
import FregeDiagrams.Syntax
import FregeDiagrams.Latex
import FregeDiagrams.Legend
import FregeDiagrams.Examples
import FregeDiagrams.Serve
import FregeDiagrams.Lint

open FregeDiagrams

/-- A decimal such as `1.4`, `2` or `-1.5`. -/
def parseDecimal (s : String) : Option Float :=
  if s.startsWith "-" then (parseDecimal' (s.drop 1).toString).map (-·) else parseDecimal' s
where parseDecimal' (s : String) : Option Float :=
  match s.splitOn "." with
  | [a] => a.toNat?.map Nat.toFloat
  | [a, b] => do
    let ai ← (if a.isEmpty then some 0 else a.toNat?)
    let bi ← b.toNat?
    return ai.toFloat + bi.toFloat / (10 ^ b.length).toFloat
  | _ => none

def usage : String :=
  "usage: lake exe framediag OUTDIR [--fig FILE] [--no-pdf] [--links] [--hide-bound] [--spacing X] [--notch-name-offset DY] [--check]"

/-- Is `rsvg-convert` on the PATH? -/
def haveRsvg : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "rsvg-convert", args := #["--version"] }
    return out.exitCode == 0
  catch _ => return false

def rsvgConvert (svg pdf : System.FilePath) : IO Unit := do
  let out ← IO.Process.output
    { cmd := "rsvg-convert", args := #["-f", "pdf", "-o", pdf.toString, svg.toString] }
  if out.exitCode != 0 then
    throw (IO.userError s!"framediag: rsvg-convert failed on {svg}:\n{out.stderr}")

def main (args : List String) : IO UInt32 := do
  -- `framediag --serve`: the drawing server of the editor (`FregeDiagrams/Serve.lean`)
  if args == ["--serve"] then return ← FregeDiagrams.Serve.serve
  -- typesetting options for the whole set of diagrams
  let opts : DrawOpts := { links := args.contains "--links", hideBound := args.contains "--hide-bound",
                           annotate := args.contains "--annotate" }
  let args0 := args
  let check := args.contains "--check" || args.contains "--stats"
  -- `--spacing X`: a factor on the clearances of the links
  let rec spacingOf : List String → Option Float
    | "--spacing" :: v :: _ => parseDecimal v
    | _ :: rest => spacingOf rest
    | [] => none
  let opts := match spacingOf args with | some s => { opts with spacing := s } | none => opts
  -- `--notch-name-offset DY`: bound names moved towards their notch's open end
  let rec nameDyOf : List String → Option Float
    | "--notch-name-offset" :: v :: _ => parseDecimal v
    | _ :: rest => nameDyOf rest
    | [] => none
  let opts := match nameDyOf args with | some v => { opts with nameDy := v } | none => opts
  let rec dropSpacing : List String → List String
    | "--spacing" :: _ :: rest => dropSpacing rest
    | "--notch-name-offset" :: _ :: rest => dropSpacing rest
    | a :: rest => a :: dropSpacing rest
    | [] => []
  let args := (dropSpacing args).filter fun a => a != "--links" && a != "--hide-bound" && a != "--annotate" && a != "--check" && a != "--stats"
  let rec parseArgs : List String → Option String × Option String × Bool → Option (Option String × Option String × Bool)
    | [], acc => some acc
    | "--fig" :: f :: rest, (d, _, p) => parseArgs rest (d, some f, p)
    | "--no-pdf" :: rest, (d, f, _) => parseArgs rest (d, f, false)
    | a :: rest, (none, f, p) => if a.startsWith "-" then none else parseArgs rest (some a, f, p)
    | _, _ => none
  let some (some outdir, file, pdf) := parseArgs args (none, none, true)
    | IO.eprintln usage; return 2
  let (src, srcName) ← match file with
    | some f => pure (← IO.FS.readFile f, f)
    | none => pure (exampleSource, "FregeDiagrams/Examples.lean")
  let figs ← match parseFile src with
    | .ok fs => pure fs
    | .error e => IO.eprintln s!"framediag: {srcName}: {e}"; return 1
  if pdf && !check && !(← haveRsvg) then
    IO.eprintln "framediag: rsvg-convert not found on PATH; it makes the PDF copies of the SVGs.\n  Install librsvg (macOS: `brew install librsvg` or `port install librsvg`), or pass --no-pdf."
    return 1
  if check then
    -- route every view-B tree with links, names shown and hidden; fail on an
    -- empty bigon or monogon (a non-minimal route) or a name cut off from or
    -- far from its state; report scope-nesting violations
    let mut bad := 0
    let mut badNames := 0
    let mut nests := 0
    let mut lintErrs := 0
    for f in figs do
      -- the checks of hints and of view A (FregeDiagrams/Lint.lean)
      for l in f.lint do
        let tag := match l.sev with | .error => "error" | .warning => "warning"
        IO.println s!"framediag --check: {f.name}: {tag}: {l.msg}"
        if l.sev == .error then lintErrs := lintErrs + 1
    for f in figs do
      if f.hints.views == .a then continue
      for hb in [false, true] do
        let t : TreeDiagram := { name := f.name, tree := f.body.toTree }
        let o := match f.hints.nameDy with | some v => { opts with nameDy := Float.ofInt v } | none => opts
        let r := t.render { o with links := true, hideBound := hb }
        let tag := s!"{f.name}{if hb then " (names hidden)" else ""}"
        if args0.contains "--stats" then
          IO.println s!"{tag}: {r.nLink} link-link, {r.nTree} link-stroke crossings, {r.nesting.size} nesting violations"
        if !r.problems.isEmpty then
          bad := bad + r.problems.size
          IO.println s!"framediag --check: {tag}: {r.problems.size} empty bigon(s) or monogon(s): {r.problems.map polyStr}"
        if !r.names.isEmpty then
          badNames := badNames + r.names.size
          IO.println s!"framediag --check: {tag}: names {r.names}"
        if !r.nesting.isEmpty then
          nests := nests + r.nesting.size
          IO.println s!"framediag --check: {tag}: nesting (outer, inner, side) {r.nesting}"
    IO.println s!"framediag --check: {figs.length} figures: {lintErrs} hint and view-A errors, {bad} empty bigons/monogons, {badNames} names misplaced, {nests} nesting violations (reported, not failed)"
    return (if bad == 0 && badNames == 0 && lintErrs == 0 then 0 else 1)
  let dir := System.FilePath.mk outdir
  IO.FS.createDirAll dir
  let mut svgs : Array System.FilePath := #[]
  let legendFile := dir / "legend.svg"
  IO.FS.writeFile legendFile legend.svg
  svgs := svgs.push legendFile
  for f in figs do
    for (n, svg) in f.pictures opts do
      let p := dir / (n ++ ".svg")
      IO.FS.writeFile p svg
      svgs := svgs.push p
    IO.FS.writeFile (dir / (f.name ++ ".tex"))
      s!"% {f.name}: generated by `lake exe framediag` from {srcName}; do not edit\n{f.toLatex}\n"
  if pdf then
    for p in svgs do rsvgConvert p (p.withExtension "pdf")
  IO.println s!"framediag: {figs.length} figures from {srcName} -> {outdir}: {svgs.size} svg{if pdf then " + pdf" else ""}, {figs.length} tex"
  return 0
