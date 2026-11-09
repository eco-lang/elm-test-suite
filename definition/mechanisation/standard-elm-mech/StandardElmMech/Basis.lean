/-
  A Standard Definition of Elm? Mechanisation, part 8.
  The environment E0 in which an example program's expressions are
  evaluated: E0 = (∅, VE0) of Appendix D with what the default imports
  `import Basics exposing (..)`, `import Debug`, `import Maybe exposing
  (Maybe(..))` add (Chapter 7 is out of this pass's scope, so the imports are
  applied by hand). The qualifier Basics gives the interface of Basics, which
  holds no hidden variable: operators are reached through OT_dyn only.
-/
import StandardElmMech.InitialBasis

namespace StandardElm
open StandardElm.D

/-- The value environment of the interface ME0(Basics) in the fragment:
    the exposed identifiers, without the hidden variables of the operators
    and of composeL, composeR, apR, apL. -/
def VE_Basics : ValEnv :=
  fmPlus VE_BasicsKernel (VE_elm.filter fun (x, _) =>
    !(["composeL", "composeR", "apR", "apL"].contains x))

/-- Debug: Debug.log and Debug.todo. -/
def VE_Debug : ValEnv := [("log", bas .debugLog), ("todo", bas .debugTodo)]

/-- Maybe: Just and Nothing. -/
def VE_Maybe : ValEnv := [("Just", conv conJust), ("Nothing", conv conNothing)]

/-- E0: the environment of the examples, before the program's own
    constructors are added. -/
def E0 : Env :=
  E0base.plus [("Basics", .mk [] VE_Basics), ("Debug", .mk [] VE_Debug), ("Maybe", .mk [] VE_Maybe)]
    (fmPlus VE_Basics VE_Maybe)

/-- E0 extended with the constructors of a program's custom types, given as
    (name, arity). Their binding is the business of Chapter 7. -/
def E0with (cons : List (String × Nat)) : Env :=
  E0.plusVE (cons.map fun (k, n) => (k, conv ⟨k, n⟩))

end StandardElm
