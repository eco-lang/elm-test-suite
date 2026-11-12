/-
  A Standard Definition of Elm? Mechanisation: unit examples of step 11, milestone (a) ("Tests
  gained", "Unit examples"): the meet and propagation tables, and unification over classes, rows
  and rigid variables, each by `decide +kernel`.

  Metavariables are `mv [i]`; a rigid variable is a named type variable `var (named s)` (its class
  by its name, A19). The specification's examples with flexible row variables are stated with field
  constraints (`has`), the form milestone (a) uses (Unify.lean); its lacks example (A23) becomes a
  field constraint against a closed record, and its occurs check through rows is not detected by
  milestone (a) (stuck field constraints carry no occurs check), stated as such below.
-/
import StandardElmMech.Stat.Complete.Unify

namespace StandardElm.Stat.Complete.Examples
open StandardElm.Stat StandardElm.Stat.Complete

private def a : T := .mv [0]
private def b : T := .mv [1]
private def c : T := .mv [2]
private def int : T := .con [] tInt
private def str : T := .con [] tString
private def bool : T := .con [] tBool
private def lst (t : T) : T := .con [t] tList
private def rigid (s : String) : T := .var (.named s)

def fails (cs : List Con) : Bool := (unifyCs cs).isFail
def succeeds (cs : List Con) : Bool :=
  match unifyCs cs with
  | .ok _ => true
  | _ => false

/-! ## Meets and propagation (section 3) -/

theorem meet_table :
    Cls.meet .comp .app = some .capp ∧ Cls.meet .num .comp = some .num ∧ Cls.meet .num .app = none ∧
    Cls.meet .capp .num = none ∧ Cls.meet .any .app = some .app ∧ Cls.meet .capp .comp = some .capp := by
  decide +kernel

theorem prop_table :
    Cls.prop .num tInt = some [] ∧ Cls.prop .num tString = none ∧ Cls.prop .comp tList = some [.comp] ∧
    Cls.prop .comp tTuple3 = some [.comp, .comp, .comp] ∧ Cls.prop .app tList = some [.any] ∧
    Cls.prop .capp tList = some [.comp] ∧ Cls.prop .comp tBool = none ∧ Cls.prop .app tChar = none ∧
    Cls.prop .capp tFloat = none := by
  decide +kernel

/-! ## Unification -/

/-- α_comp ≐ β_app: the meet capp exists. -/
theorem comp_app : succeeds [.cls a .comp, .cls b .app, .eq a b] = true := by decide +kernel

/-- α_num ≐ String fails. -/
theorem num_string : fails [.cls a .num, .eq a str] = true := by decide +kernel

/-- α_comp ≐ (Int, β) refines β to comp: β ≐ Bool then fails, β ≐ String does not. -/
theorem comp_tuple :
    fails [.cls a .comp, .eq a (.con [int, b] tTuple2), .eq b bool] = true ∧
    succeeds [.cls a .comp, .eq a (.con [int, b] tTuple2), .eq b str] = true := by decide +kernel

/-- α_capp ≐ List β refines β to comp; α_app ≐ List β leaves β any. -/
theorem capp_app_list :
    fails [.cls a .capp, .eq a (lst b), .eq b (.fn int int)] = true ∧
    succeeds [.cls a .app, .eq a (lst b), .eq b (.fn int int)] = true := by decide +kernel

/-- A rigid comparable against a number fails; a rigid number against a comparable binds it. -/
theorem rigid_classes :
    fails [.cls b .num, .eq (rigid "comparable") b] = true ∧
    succeeds [.cls b .comp, .eq (rigid "number") b] = true := by decide +kernel

/-- Two different rigid variables never unify. -/
theorem rigid_rigid : fails [.eq (rigid "a") (rigid "b")] = true := by decide +kernel

/-- α ≐ α → Int fails (occurs check, K3). -/
theorem occurs : fails [.eq a (.fn a int)] = true := by decide +kernel

/-- {x : Int | ε} ≐ {y : Bool | ε'}: two open records unify. -/
theorem open_open : succeeds [.has a "x" int, .has b "y" bool, .eq a b] = true := by decide +kernel

/-- An open record with x : Int against the closed { x : String } fails; a missing field fails. -/
theorem open_closed :
    fails [.has a "x" int, .eq a (.record [("x", str)] none)] = true ∧
    fails [.has a "y" int, .eq a (.record [("x", int)] none)] = true := by decide +kernel

/-- Two field constraints with the same label give an equation. -/
theorem same_field : fails [.has a "x" int, .has a "x" str] = true := by decide +kernel

/-- A record is in no class but any. -/
theorem record_class : fails [.cls a .comp, .has a "x" int] = true := by decide +kernel

/-- A closed record against a record with a rigid tail fails (A21's rigid extension). -/
theorem rigid_tail : fails [.eq (.record [("name", int)] (some (.named "r"))) (.record [("name", int)] none)] = true := by
  decide +kernel

/-- Not detected at milestone (a): a record that is its own field's type (the occurs check
    through rows of the specification); its field constraint stays stuck. -/
theorem occurs_through_rows_not_detected : succeeds [.has a "a" a] = true := by decide +kernel

end StandardElm.Stat.Complete.Examples
