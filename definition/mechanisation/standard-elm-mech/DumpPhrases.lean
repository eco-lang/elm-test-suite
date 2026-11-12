/-
  Prints the modules of every example program, one program per line, so that a change to how
  programs are built (such as generating the derived forms of Derived.lean from a table) can be
  shown to change nothing.
-/
import StandardElmMech.AllPrograms
import StandardElmMech.Theorems

open StandardElm

def main : IO UInt32 := do
  for p in allPrograms do
    IO.println s!"{p.name} | {(repr p.modules).pretty 1000000}"
  return 0
