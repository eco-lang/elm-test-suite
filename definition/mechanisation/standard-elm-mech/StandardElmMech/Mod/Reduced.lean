/-
  A Standard Definition of Elm? Mechanisation: the reduced part of a program, plan step 10.

  What the dynamic semantics reads of a program: its modules in the reduced syntax of Chapter 7
  (sec:dynamic-modules-reduced), its port environment, the flags type of `main` and its kind (a
  view or a worker). Step 10 compares the program that Lean's specialisation and erasure compute
  from the source syntax with the translator's on this object only, so that the fields a test
  carries for its harness (name, checks, `native`) and the way a definition was written do not
  enter the comparison.

  The translator writes a view test as a `Program` and a worker test as a `Prog.WorkerTest` over
  one; their reduced parts are `Program.reduced` and `Prog.WorkerTest.reduced`. The flags type of
  a view is not read by the semantics (step 5); it is `.unit` (step 10, Translator changes, item 3).
-/
import StandardElmMech.SyntaxDecEq
import StandardElmMech.Prog.Worker

namespace StandardElm.Mod
open StandardElm

/-- The kind of a program: `main` is a view (r:p-stat-main-view) or a worker
    (r:p-stat-main-program). -/
inductive ProgKind where
  | view | worker
  deriving DecidableEq, Repr, Inhabited

/-- The part of a program that the dynamic semantics reads. -/
structure Reduced where
  modules : List Module
  ports : Prog.PortEnv
  flagsType : Eff.PTy
  kind : ProgKind
  deriving DecidableEq, Repr

/-- A reduced program from its modules: the port environment is the one its modules declare
    (`Prog.portEnv`, the semantics' reading of the `port` declarations). -/
def Reduced.ofModules (ms : List Module) (flags : Eff.PTy) (k : ProgKind) : Reduced :=
  ⟨ms, Prog.portEnv ms, flags, k⟩

end StandardElm.Mod

namespace StandardElm

/-- The reduced part of a view test as the translator writes it. -/
def Program.reduced (p : Program) : Mod.Reduced := .ofModules p.modules .unit .view

/-- The reduced part of a worker test as the translator writes it. -/
def Prog.WorkerTest.reduced (w : Prog.WorkerTest) : Mod.Reduced :=
  .ofModules w.prog.modules w.flagsType .worker

end StandardElm
