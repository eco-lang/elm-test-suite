/-
  Prints the phrase of every check of every example, one per line, so that a
  change to how phrases are built (such as generating the derived forms of
  Derived.lean from a table) can be shown to change nothing.
-/
import StandardElmMech.AllPrograms
import StandardElmMech.Theorems

open StandardElm

def main : IO UInt32 := do
  for p in allPrograms do
    for ck in p.checks do
      IO.println s!"{p.name} | {ck.label} | {reprStr (p.phrase ck)}"
  return 0
