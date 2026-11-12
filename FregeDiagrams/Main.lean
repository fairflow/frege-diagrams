/-
`lake exe framediag OUTDIR [--fig FILE] [--no-pdf] [--links] [--hide-bound] [--spacing X] [--notch-name-offset DY] [--check] [--stats]`

`--links` joins each quantifier notch to the states it binds by one tree of
links (view B); `--hide-bound` leaves the bound names out (both views);
`--spacing X` scales the clearances of the links; `--notch-name-offset DY`
moves each bound name DY units towards its notch's open end (a figure's
`namedy` hint overrides it); `--check` and `--stats` run
the layout checks instead of drawing.  `docs/MANUAL.md` has the detail.

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
import FregeDiagrams.Version

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
  "usage: lake exe framediag OUTDIR [--fig FILE [--def NAME]] [--no-pdf] [--links] [--hide-bound] [--spacing X] [--notch-name-offset DY] [--style classic] [--check] [--stats]"

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
  if args == ["--version"] then
    IO.println s!"frege-diagrams {FregeDiagrams.version}"
    return 0
  -- typesetting options for the whole set of diagrams
  let opts : DrawOpts := { links := args.contains "--links", hideBound := args.contains "--hide-bound",
                           annotate := args.contains "--annotate",
                           style := if ((args.dropWhile (· != "--style")).drop 1).head? == some "classic" then .classic else .soft }
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
    | "--def" :: _ :: rest => dropSpacing rest
    | "--style" :: _ :: rest => dropSpacing rest
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
  -- `--def NAME`: which raw string of a Lean file holds the figures
  let rec defOf : List String → Option String
    | "--def" :: v :: _ => some v
    | _ :: rest => defOf rest
    | [] => none
  let (src, srcName, lineNote) ← match file with
    | some f =>
      let text ← IO.FS.readFile f
      if f.endsWith ".lean" then
        let defs : List (String × String × Nat) := leanRawStrings text
        let chosen := match defOf args0 with
          | some n => defs.filter (fun d => d.1 == n)
          | none => defs
        match chosen with
        | [(n, body, line)] =>
          pure (body, s!"{f} (the string {n})", s!" (line 1 of the string is line {line} of the file)")
        | [] =>
          IO.eprintln s!"framediag: {f}: no raw string definition{match defOf args0 with | some n => s!" named {n}" | none => ""} (expected def NAME : String := r#\"…\"#)"
          return 1
        | ds =>
          IO.eprintln s!"framediag: {f}: several raw string definitions ({", ".intercalate (ds.map (fun d : String × String × Nat => d.1))}); choose one with --def NAME"
          return 1
      else pure (text, f, "")
    | none => pure (exampleSource, "FregeDiagrams/Examples.lean", "")
  let figs ← match parseFile src with
    | .ok fs => pure fs
    | .error e => IO.eprintln s!"framediag: {srcName}: {e}{lineNote}"; return 1
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
        let t : TreeDiagram := f.toTreeDiagram
        let o := f.drawOpts opts
        let r := t.render { o with links := true, hideBound := hb }
        let tag := s!"{f.name}{if hb then " (names hidden)" else ""}"
        -- a pin holds for one layout (names shown, the figure's own offset,
        -- spacing 1: `DrawOpts.pinsApply`); in others it is set aside
        for x in r.stalePins do
          IO.println s!"framediag --check: {f.name}: error: the route of {x} no longer fits the layout (its notch or its states moved); it is routed automatically"
          lintErrs := lintErrs + 1
        if hb == opts.hideBound then
          for x in r.setAside do
            IO.println s!"framediag --check: {tag}: note: the route of {x} is pinned for names shown, the figure's own notch-name offset and spacing 1; with these options it is routed automatically"
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
  IO.FS.writeFile legendFile { legend with style := opts.style }.svg
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
