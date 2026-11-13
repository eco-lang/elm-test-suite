/-
  A Standard Definition of Elm? Mechanisation: the unit examples of milestone (d) of plan step 11
  ("Unit examples", the row cases), by `decide +kernel`, on unification with rows (MguR.lean):

  * `⟨x : Int | ε⟩ ≐ ⟨y : Bool | ε'⟩` gives one fresh tail `ε''`: `ε ↦ ⟨y : Bool | ε''⟩`,
    `ε' ↦ ⟨x : Int | ε''⟩`, and both sides become `⟨x : Int, y : Bool | ε''⟩`;
  * A23: `⟨∅ | ε⟩ ≐ ⟨x : String⟩` with `⟨x : Int | ε⟩` in the frame fails (and succeeds without
    it);
  * `⟨a : ⟨∅ | ε⟩ | ε'⟩ ≐ ⟨∅ | ε⟩` fails (the occurs check through rows);
  * and: closed against open records, a field type clash, rigid row variables, the same tail with
    different labels, a lacks conflict inside the equations, a type variable against a record of
    itself.
-/
import StandardElmMech.Stat.Complete.MguRTerm
import StandardElmMech.Stat.Complete.W

namespace StandardElm.Stat.Complete
open StandardElm.Stat

namespace MguRExamples

def ε (n : Nat) : RowVar := .fresh n
def flexR : RRigid := fun _ => false
/-- Only the named variables are rigid. -/
def namedR : RRigid := fun v => match v with
  | .ty (.named _) | .row (.named _) => true
  | _ => false
def boolTy : Ty := .con [] tBool

def outImg (o : ROut) (v : BVar) : Option Ty :=
  match o with
  | .ok θ _ => some ((toRS θ).img v)
  | _ => none

def outApp (o : ROut) (τ : Ty) : Option Ty :=
  match o with
  | .ok θ _ => some (rsb (toRS θ) τ)
  | _ => none

def recXI : Ty := .record [("x", tIntTy)] (some (ε 0))
def recYB : Ty := .record [("y", boolTy)] (some (ε 1))

/-- `⟨x : Int | ε⟩ ≐ ⟨y : Bool | ε'⟩`: one fresh tail. -/
theorem fresh_tail :
    let o := mguR 10 flexR 2 [(recXI, recYB)] []
    outImg o (.row (ε 0)) = some (.record [("y", boolTy)] (some (ε 2))) ∧
    outImg o (.row (ε 1)) = some (.record [("x", tIntTy)] (some (ε 2))) ∧
    outApp o recXI = some (.record [("x", tIntTy), ("y", boolTy)] (some (ε 2))) ∧
    outApp o recYB = some (.record [("x", tIntTy), ("y", boolTy)] (some (ε 2))) := by
  decide +kernel

/-- A23: `⟨∅ | ε⟩ ≐ ⟨x : String⟩` fails with `⟨x : Int | ε⟩` in the frame. -/
theorem a23_frame :
    mguR 10 flexR 1 [(.record [] (some (ε 0)), .record [("x", tStringTy)] none)] [.record [("x", tIntTy)] (some (ε 0))]
      = .fail := by decide +kernel

/-- Without the frame it succeeds: `ε ↦ ⟨x : String⟩`. -/
theorem a23_noframe :
    outImg (mguR 10 flexR 1 [(.record [] (some (ε 0)), .record [("x", tStringTy)] none)] []) (.row (ε 0)) =
      some (.record [("x", tStringTy)] none) := by decide +kernel

/-- The lacks constraint also comes from the other equations. -/
theorem a23_eqs :
    mguR 10 flexR 1 [(.record [] (some (ε 0)), .record [("x", tStringTy)] none),
      (.record [("x", tIntTy)] (some (ε 0)), .record [("x", tIntTy)] (some (ε 0)))] [] = .fail := by decide +kernel

/-- The occurs check through rows: `⟨a : ⟨∅ | ε⟩ | ε'⟩ ≐ ⟨∅ | ε⟩` fails. -/
theorem occurs_rows :
    mguR 10 flexR 2 [(.record [("a", .record [] (some (ε 0)))] (some (ε 1)), .record [] (some (ε 0)))] [] = .fail := by
  decide +kernel

/-- A type variable against a record that mentions it fails. -/
theorem occurs_field :
    mguR 10 flexR 2 [(.var (.fresh 0 .any), .record [("a", .var (.fresh 0 .any))] (some (ε 1)))] [] = .fail := by
  decide +kernel

/-- A closed record against an open one: the tail is the missing fields. -/
theorem closed_open :
    outImg (mguR 10 flexR 1 [(.record [("x", tIntTy), ("y", tCharTy)] none, .record [("y", tCharTy)] (some (ε 0)))] [])
      (.row (ε 0)) = some (.record [("x", tIntTy)] none) := by decide +kernel

/-- The open side has a field the closed side lacks: fail. -/
theorem closed_open_extra :
    mguR 10 flexR 1 [(.record [("x", tIntTy)] none, .record [("y", tCharTy)] (some (ε 0)))] [] = .fail := by
  decide +kernel

/-- Common fields are unified: a clash fails. -/
theorem field_clash :
    mguR 10 flexR 1 [(.record [("x", tIntTy)] (some (ε 0)), .record [("x", tCharTy)] none)] [] = .fail := by
  decide +kernel

/-- The same tail, different labels: fail. -/
theorem same_tail :
    mguR 10 flexR 1 [(.record [("x", tIntTy)] (some (ε 0)), .record [("y", tIntTy)] (some (ε 0)))] [] = .fail := by
  decide +kernel

/-- A rigid row variable is never extended; two rigid ones never meet; a flexible one may become a
    rigid one. -/
theorem rigid_extend :
    mguR 10 namedR 0 [(.record [] (some (.named "r")), .record [("x", tIntTy)] (some (ε 0)))] [] = .fail := by
  decide +kernel

theorem rigid_rigid :
    mguR 10 namedR 0 [(.record [] (some (.named "r")), .record [] (some (.named "s")))] [] = .fail := by
  decide +kernel

theorem rigid_flex :
    outImg (mguR 10 namedR 1 [(.record [("x", tIntTy)] (some (.named "r")), .record [("x", tIntTy)] (some (ε 0)))] [])
      (.row (ε 0)) = some (.record [] (some (.named "r"))) := by decide +kernel

end MguRExamples

end StandardElm.Stat.Complete
