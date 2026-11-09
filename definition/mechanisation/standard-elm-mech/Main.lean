/-
  Runs every example through the evaluator, with both choices of a member of
  APPLY, and compares the definition's value with the implementation's
  (the CHECK value). Prints a Markdown table and a summary.
-/
import StandardElmMech

open StandardElm

def fuel : Nat := 100000

def showResult : Option Val → String
  | some v => showElm v
  | none => "(no value)"

/-- Labels whose disagreement is expected and recorded in the report. -/
def knownDivergent : List (String × String) := []

def runGroup (title : String) (ps : List Program) : IO (Nat × Nat × Nat) := do
  IO.println s!"\n## {title}\n"
  IO.println "| Program | Label | Implementation (CHECK) | Definition | Status |"
  IO.println "|---|---|---|---|---|"
  let mut total := 0
  let mut agree := 0
  let mut diverge := 0
  for p in ps do
    for ck in p.checks do
      let e := p.phrase ck
      let r0 := showResult (evExp false fuel p.env e)
      let r1 := showResult (evExp true fuel p.env e)
      let book := if r0 == r1 then r0 else s!"{r0} or {r1}"
      let ok := ck.expected == r0 || ck.expected == r1
      total := total + 1
      if ok then agree := agree + 1 else diverge := diverge + 1
      let status := if ok then (if r0 == r1 then "agree" else "agree (member of the set)")
                    else if knownDivergent.contains (p.name, ck.label) then "DIVERGENCE (known)"
                    else "DIVERGENCE"
      IO.println s!"| {p.name} | {ck.label} | {ck.expected} | {book} | {status} |"
  IO.println s!"\n{title}: {total} checks, {agree} agree, {diverge} diverge."
  return (total, agree, diverge)

def main : IO UInt32 := do
  IO.println "# Standard Elm mechanisation: example run"
  IO.println s!"\nCorpus programs: {corpus.length}; ruling programs: {rulings.length}."
  let (t1, a1, d1) ← runGroup "Corpus (the test programs that accompany the book)" corpus
  let (t2, a2, d2) ← runGroup "Rulings (A40, A42, A43, A46 to A51)" rulings
  let (t3, a3, d3) ← runGroup "Rule coverage and book Comments" coverage
  IO.println s!"\nTotal: {t1 + t2 + t3} checks, {a1 + a2 + a3} agree, {d1 + d2 + d3} diverge."
  return 0
