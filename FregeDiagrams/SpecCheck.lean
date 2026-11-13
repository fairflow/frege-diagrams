/-
FregeDiagrams.SpecCheck: the references of both views on generated figures,
compiled (the reader of view B routes links three times per figure, too slow
for `#guard`).

    lake exe speccheck [N] [SEED]

checks view A (`Fig.checkA`) and view B (`Fig.checkB`) on the examples and on
N generated figures (default 2000, seed 2026), both views forced, prints the
violations by kind with one example each, and fails if there are any.
-/
import FregeDiagrams.Spec
import FregeDiagrams.SpecB
import FregeDiagrams.Test

open FregeDiagrams FregeDiagrams.Test

/-- The violations of a list of figures, by kind (the text before the first
`:`), with a count and the first example of each. -/
def tally (figs : List Fig) (check : Fig → List String) : IO Nat := do
  let mut kinds : Array (String × Nat × String) := #[]
  let mut bad := 0
  for f in figs do
    let vs := check f
    if !vs.isEmpty then bad := bad + 1
    for v in vs do
      let k := (v.splitOn ":").head!
      match kinds.findIdx? (·.1 == k) with
      | some i => kinds := kinds.modify i fun (a, n, ex) => (a, n + 1, ex)
      | none => kinds := kinds.push (k, 1, s!"{v}\n      in {f.print}")
  IO.println s!"  {bad} of {figs.length} figures with violations"
  for (k, n, ex) in kinds do IO.println s!"  {k}: {n}\n    e.g. {ex}"
  return bad

def main (args : List String) : IO UInt32 := do
  let n := (args[0]? >>= String.toNat?).getD 2000
  let seed := (args[1]? >>= String.toNat?).getD 2026
  let figs : List Fig := (randomFigs n seed).map fun (f : Fig) =>
    ({ f with hints := { f.hints with views := Views.both } } : Fig)
  let mut bad := 0
  IO.println "view A, the examples:"
  bad := bad + (← tally exampleFigs Fig.checkA)
  IO.println s!"view A, {n} generated figures (seed {seed}):"
  bad := bad + (← tally figs Fig.checkA)
  IO.println "view B, the examples:"
  bad := bad + (← tally exampleFigs Fig.checkB)
  IO.println s!"view B, {n} generated figures (seed {seed}):"
  bad := bad + (← tally figs Fig.checkB)
  return if bad == 0 then 0 else 1
