/-
  A Standard Definition of Elm? Mechanisation, part 8.
  The environment E0 in which an example program's expressions are evaluated in the let form of the
  translated tests: E0 = (∅, VE0) of Appendix D modified by the environment that the default imports
  give in ME0 (Mod/ME0.lean), as rule r:dm-module evaluates a module's top-level declarations
  (plan step 2: one ME0 for the let form and the module form). The qualifier Basics gives the
  interface of Basics, which holds no hidden variable: operators are reached through OT_dyn only.
  The value environments below are kept for the hand-written examples that name them.
-/
import StandardElmMech.InitialBasis
import StandardElmMech.Mod.ME0

namespace StandardElm
open StandardElm.D

/-- The value environment of the interface ME0(Basics) in the fragment:
    the exposed identifiers, without the hidden variables of the operators
    and of composeL, composeR, apR, apL. -/
def VE_Basics : ValEnv :=
  fmPlus VE_BasicsKernel (VE_elm.filter fun (x, _) =>
    !(["composeL", "composeR", "apR", "apL"].contains x))

/-- Debug: Debug.log, Debug.todo and Debug.toString. -/
def VE_Debug : ValEnv :=
  [("log", bas .debugLog), ("todo", bas .debugTodo), ("toString", bas .debugToString)]

/-- Char, as far as the book's basis has it: toCode and fromCode, reached by
    their qualified names only (the default imports expose none of Char). -/
def VE_Char : ValEnv := [("toCode", bas .charToCode), ("fromCode", bas .charFromCode)]

/-- Maybe: Just and Nothing. -/
def VE_Maybe : ValEnv := [("Just", conv conJust), ("Nothing", conv conNothing)]

/-- Result: Ok and Err (the default import `import Result exposing (Result(..))`). -/
def VE_Result : ValEnv := [("Ok", conv conOk), ("Err", conv conErr)]

/-- E0: the environment of the examples, before the program's own constructors are added: E0 of
    Appendix D (which binds [] and ::) modified by the environment the default imports give in ME0
    (Mod/ME0.lean, `E_default`, derived by the rules: `E_default_eval`), as rule r:dm-module
    evaluates a module's declarations. -/
def E0 : Env := E0base.plusEnv Mod.E_default

/-- E0 extended with the constructors of a program's custom types, given as
    (name, arity). Their binding is the business of Chapter 7. -/
def E0with (cons : List (String × Nat)) : Env :=
  E0.plusVE (cons.map fun (k, n) => (k, conv ⟨k, n⟩))

end StandardElm
