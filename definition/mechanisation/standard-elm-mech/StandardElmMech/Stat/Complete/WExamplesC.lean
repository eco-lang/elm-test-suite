/-
  A Standard Definition of Elm? Mechanisation: the unit examples of milestone (c) of plan step 11
  ("Unit examples"), by `decide +kernel`: the meet table against `Adm` on sample types, the
  propagation table, and unification with classes and rigid variables (MguC.lean). (The record
  examples belong to milestone (d).)
-/
import StandardElmMech.Stat.Complete.MguCLoop
import StandardElmMech.Stat.Complete.W

namespace StandardElm.Stat.Complete
open StandardElm.Stat

namespace WExamplesC

def classes : List Cls := [.any, .num, .comp, .app, .capp]

/-- Sample types: the base types, lists, tuples, an arrow, a record, a custom type, and a variable
    of each class. -/
def samples : List Ty :=
  [tIntTy, tFloatTy, tCharTy, tStringTy, tUnitTy, listTy tIntTy, listTy (.fn tIntTy tIntTy),
   listTy (listTy tCharTy), tupleTy tIntTy tStringTy none, tupleTy tIntTy (.fn tIntTy tIntTy) none,
   tupleTy tCharTy tFloatTy (some tIntTy), .fn tIntTy tIntTy, .record [] none, .con [] tBool,
   .con [tIntTy] tMaybe] ++ classes.map (fun k => .var (.fresh 0 k))

/-- `meet_table`: the 25 meets of section 3, each against `Adm` (decided by step 9's `adm`,
    `adm_iff`) on the samples: a type is in both classes iff the meet exists and the type is in it. -/
theorem meet_table : (classes.all fun k => classes.all fun k' => samples.all fun τ =>
    (adm k τ && adm k' τ) == (match Cls.meet k k' with | some m => adm m τ | none => false)) = true := by
  decide +kernel

/-- The 25 entries themselves. -/
theorem meet_entries :
    classes.map (fun k => classes.map (Cls.meet k)) =
      [[some .any, some .num, some .comp, some .app, some .capp],
       [some .num, some .num, some .num, none, none],
       [some .comp, some .num, some .comp, some .capp, some .capp],
       [some .app, none, some .capp, some .app, some .capp],
       [some .capp, none, some .capp, some .capp, some .capp]] := by decide +kernel

/-- `prop_table`: D(κ, t) for the classes other than any (D(any, t) is all any, not tabulated)
    and the built-in type names, with Bool, Maybe, Result, Array. -/
theorem prop_table :
    [tInt, tFloat, tChar, tString, tUnit, tList, tTuple2, tTuple3, tBool, tMaybe, tResult, tArray].map
      (fun t => [Cls.num, .comp, .app, .capp].map (fun k => clsD k t)) =
    [[some [], some [], none, none],
     [some [], some [], none, none],
     [none, some [], none, none],
     [none, some [], some [], some []],
     [none, none, none, none],
     [none, some [.comp], some [.any], some [.comp]],
     [none, some [.comp, .comp], none, none],
     [none, some [.comp, .comp, .comp], none, none],
     [none, none, none, none],
     [none, none, none, none],
     [none, none, none, none],
     [none, none, none, none]] := by decide +kernel

def v (n : Nat) (k : Cls) : Ty := .var (.fresh n k)
def flex : Rigid := fun _ => false
/-- Only the named variables are rigid. -/
def rigidNamed : Rigid := fun a => match a with | .named _ => true | _ => false

def outLk (o : COut) (a : TyVar) : Option Ty :=
  match o with
  | .ok θ _ => some (lk θ a)
  | _ => none

/-- `α_comp ≐ β_app` gives a fresh `γ_capp` for both. -/
theorem comp_app :
    let o := mguC 10 flex 2 [(v 0 .comp, v 1 .app)]
    outLk o (.fresh 0 .comp) = some (v 2 .capp) ∧ outLk o (.fresh 1 .app) = some (v 2 .capp) := by
  decide +kernel

/-- `α_num ≐ String` fails. -/
theorem num_string : mguC 10 flex 1 [(v 0 .num, tStringTy)] = .fail := by decide +kernel

/-- `α_comp ≐ (Int, β) Tuple2` refines `β` to comp. -/
theorem comp_tuple :
    outLk (mguC 10 flex 2 [(v 0 .comp, tupleTy tIntTy (v 1 .any) none)]) (.fresh 0 .comp) =
      some (tupleTy tIntTy (v 2 .comp) none) := by decide +kernel

/-- `α_capp ≐ β List` refines `β` to comp. -/
theorem capp_list :
    outLk (mguC 10 flex 2 [(v 0 .capp, listTy (v 1 .any))]) (.fresh 0 .capp) = some (listTy (v 2 .comp)) := by
  decide +kernel

/-- `α_app ≐ β List` leaves `β` of class any. -/
theorem app_list :
    let o := mguC 10 flex 2 [(v 0 .app, listTy (v 1 .any))]
    outLk o (.fresh 0 .app) = some (listTy (v 1 .any)) ∧ outLk o (.fresh 1 .any) = some (v 1 .any) := by
  decide +kernel

/-- A rigid `comparable ≐ β_num` fails; a rigid `number ≐ β_comp` binds `β` to it. -/
theorem rigid_comp_num : mguC 10 rigidNamed 1 [(.var (.named "comparable"), v 0 .num)] = .fail := by
  decide +kernel

theorem rigid_num_comp :
    outLk (mguC 10 rigidNamed 1 [(.var (.named "number"), v 0 .comp)]) (.fresh 0 .comp) =
      some (.var (.named "number")) := by decide +kernel

/-- Two rigid variables never unify; a rigid variable is never bound to a type. -/
theorem rigid_rigid : mguC 10 rigidNamed 0 [(.var (.named "a"), .var (.named "b"))] = .fail := by decide +kernel
theorem rigid_type : mguC 10 rigidNamed 0 [(.var (.named "a"), tCharTy)] = .fail := by decide +kernel

/-- `α ≐ α → Int` fails (occurs). -/
theorem occurs : mguC 10 flex 1 [(v 0 .any, .fn (v 0 .any) tIntTy)] = .fail := by decide +kernel

/-- Propagation through a list into a tuple: `α_comp ≐ (β, γ → Int) Tuple2 List` fails (an arrow is
    never comparable); `α_comp ≐ (β, Char) Tuple2 List` refines `β` to comp. -/
theorem comp_list_fn :
    mguC 10 flex 2 [(v 0 .comp, listTy (tupleTy (v 1 .any) (.fn (v 1 .any) tIntTy) none))] = .fail := by
  decide +kernel

theorem comp_list_tuple :
    outLk (mguC 10 flex 2 [(v 0 .comp, listTy (tupleTy (v 1 .any) tCharTy none))]) (.fresh 0 .comp) =
      some (listTy (tupleTy (v 2 .comp) tCharTy none)) := by decide +kernel

/-- num and app have no meet: `α_num ≐ β_app` fails; `α_num ≐ β_comp` binds `β ↦ α`. -/
theorem num_app : mguC 10 flex 2 [(v 0 .num, v 1 .app)] = .fail := by decide +kernel

theorem num_comp :
    outLk (mguC 10 flex 2 [(v 0 .num, v 1 .comp)]) (.fresh 1 .comp) = some (v 0 .num) := by decide +kernel

end WExamplesC

end StandardElm.Stat.Complete
