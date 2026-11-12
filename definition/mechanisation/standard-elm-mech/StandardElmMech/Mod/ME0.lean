/-
  A Standard Definition of Elm? Mechanisation: the dynamic ME0 for the modules every program imports
  (plan decision D3), the harness Html and the test basis Btest (decision D2), plan step 2.

  From appendix-dynamic-basis.tex, sec:appendix-dynamic-basis-env (Figures
  fig:dynamic-basis-basics, fig:dynamic-basis-others and the constructor environments): every RA is
  empty (the basis has no record alias). ME0 is a literal value; the values of the texts written in
  Elm are those InitialBasis.lean builds, each with its derivation theorem (Theorems.lean,
  `elmTexts_eval`, `never_eval`; `none_eval` below). Task and Process are added in step 4; the frame
  lemma makes a partial ME0 sound for programs that do not import them.
-/
import StandardElmMech.Mod.Sound
import StandardElmMech.InitialBasis
import StandardElmMech.Eff.TaskTexts

namespace StandardElm.Mod
open StandardElm StandardElm.D

/-- The hidden texts of the operators, which Basics does not expose. -/
def hiddenTexts : List String := ["composeL", "composeR", "apR", "apL"]

/-- The value environment of the interface of Basics: its exposed basic values, constructors and
    floats, and the values of its exposed texts (abs and its copy abs$Int, logBase, degrees,
    radians, turns, fromPolar, toPolar, identity, always, never). -/
def VE_BasicsI : ValEnv :=
  VE_BasicsKernel ++ VE_elm.filter (fun (x, _) => !(hiddenTexts.contains x))

def I_Basics : Interface :=
  ⟨[], [("Bool", [("True", conv conTrue), ("False", conv conFalse)]),
        ("Order", [("LT", conv conLT), ("EQ", conv conEQ), ("GT", conv conGT)]),
        ("Never", [])],
   VE_BasicsI⟩

def VE_MaybeI : ValEnv := [("Just", conv conJust), ("Nothing", conv conNothing)]
def VE_ResultI : ValEnv := [("Ok", conv conOk), ("Err", conv conErr)]

def I_Maybe : Interface := ⟨[], [("Maybe", VE_MaybeI)], VE_MaybeI⟩
def I_Result : Interface := ⟨[], [("Result", VE_ResultI)], VE_ResultI⟩
def I_Char : Interface := .ofVE [("toCode", bas .charToCode), ("fromCode", bas .charFromCode)]
def I_Debug : Interface :=
  .ofVE [("log", bas .debugLog), ("todo", bas .debugTodo), ("toString", bas .debugToString)]
def I_Platform : Interface := .ofVE [("worker", bas .platformWorker)]

/-- The environments of the texts of Platform.Cmd and Platform.Sub (sec:appendix-dynamic-basis-elm):
    E0 with the module's own basic values unqualified. -/
def E_Cmd : Env := E0base.plus [] [("batch", bas .cmdBatch), ("map", bas .cmdMap)]
def E_Sub : Env := E0base.plus [] [("batch", bas .subBatch), ("map", bas .subMap)]

/-- `none = batch []`, the text of Platform/Cmd.elm and of Platform/Sub.elm. -/
def noneBody : Exp := ap (v "batch") [listE []]

def I_Cmd : Interface := .ofVE [("none", .batch []), ("batch", bas .cmdBatch), ("map", bas .cmdMap)]
def I_Sub : Interface := .ofVE [("none", .batch []), ("batch", bas .subBatch), ("map", bas .subMap)]

/-- ME0(Task) and ME0(Process) (fig:dynamic-basis-others): Task's basic values and the values of
    its texts (Eff/TaskTexts.lean), Process's basic values (plan step 4). -/
def I_Task : Interface := .ofVE Eff.VE_TaskIface
def I_Process : Interface := .ofVE Eff.VE_Process

/-- ME0 for the modules of the default imports, Task and Process, and the modules the book binds
    for their types only (appendix-dynamic-basis.tex: their interfaces are (∅, {}, {})). -/
def ME0 : ModEnv :=
  [ ("Basics", I_Basics), ("List", .empty), ("Maybe", I_Maybe), ("Result", I_Result),
    ("String", .empty), ("Char", I_Char), ("Tuple", .empty), ("Debug", I_Debug),
    ("Platform", I_Platform), ("Platform.Cmd", I_Cmd), ("Platform.Sub", I_Sub),
    ("Array", .empty), ("Bytes", .empty), ("Json.Encode", .empty), ("Json.Decode", .empty),
    ("VirtualDom", .empty), ("Html", .empty), ("Task", I_Task), ("Process", I_Process) ]

/-- D2 (a): the harness Html. `text` is the constructor value node# of arity 1. -/
def I_HtmlHarness : Interface := .ofVE [("text", conv conNode)]

/-- D2: the test basis. `lib` holds the core library's additions (core-library.md), empty until that
    plan's steps; they extend the interfaces ME0 already has, component by component, and add the
    modules it does not have. -/
def btestStep (B : Basis) (p : ModId × Interface) : Basis :=
  match fmLookup B p.1 with
  | some I0 => fmPlus B [(p.1, I0.plus p.2)]
  | none => fmPlus B [(p.1, p.2)]

def Btest (lib : ModEnv := []) : Basis :=
  lib.foldl btestStep (fmPlus ME0 [("Html", I_HtmlHarness)])

/-- The evaluator gives the declaration `none = batch []` the value environment {none ↦ batch()}. -/
def noneIsBatchB (E : Env) : Bool :=
  match evDec (.const false) 100 E (.val (.var "none" noneBody none)) 0 with
  | ⟨.value [(x, .batch [])], _, _⟩ => x == "none"
  | _ => false

theorem noneIsBatch_sound {E : Env} (h : noneIsBatchB E = true) :
    EvalDec E (.val (.var "none" noneBody none)) [("none", .batch [])] := by
  unfold noneIsBatchB at h
  split at h
  · rename_i x l k hr
    simp only [beq_iff_eq] at h; subst h
    exact evDec_sound (by rw [hr])
  · cases h

/-- The text of Platform.Cmd's `none` evaluates, in its environment, to batch() (D3). -/
theorem me0_PlatformCmd_none_eval :
    EvalDec E_Cmd (.val (.var "none" noneBody none)) [("none", .batch [])] :=
  noneIsBatch_sound (by decide +kernel)

/-- The text of Platform.Sub's `none` evaluates, in its environment, to batch() (D3). -/
theorem me0_PlatformSub_none_eval :
    EvalDec E_Sub (.val (.var "none" noneBody none)) [("none", .batch [])] :=
  noneIsBatch_sound (by decide +kernel)

/-- The environment the default imports give, in ME0. -/
def E_default : Env :=
  match evImports ME0 defaultImports with
  | some E => E
  | none => .mk [] []

theorem E_default_eval : EvalImports ME0 defaultImports E_default :=
  evImports_sound (by rfl)

end StandardElm.Mod
