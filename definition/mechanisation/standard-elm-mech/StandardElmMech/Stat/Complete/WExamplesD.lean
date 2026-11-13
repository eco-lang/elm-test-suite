/-
  A Standard Definition of Elm? Mechanisation: unit examples of W with records (milestone (d) of
  plan step 11), by `decide +kernel`, in the empty context: record expressions, field selection (the
  derived form `(\{x} -> x) e`), updates, and the refusals of a missing field and of an update of
  a record without the field.
-/
import StandardElmMech.Stat.Complete.WD
import StandardElmMech.Stat.Complete.WExamplesC

namespace StandardElm.Stat.Complete
open StandardElm.Stat
open StandardElm.Src (BExp BAtExp BAtPat BDec BValBind SLit)

namespace WExamplesD
open WExamplesC (C0 ev lam letv int str chr v)

def tyOfD : WRes → Option Ty
  | .ok a => some a.ty
  | _ => none

def recE (fs : List (String × BExp)) : BExp := .atexp (.record (fs.foldr (fun p r => some (.field p.1 p.2 r)) none))
def recP (ls : List String) : BAtPat := .record (ls.foldr (fun l r => some (.field l r)) none)
/-- Field selection `e.l`, as its derived form `(\{l} -> l) e`. -/
def sel (e : BAtExp) (l : String) : BExp := .app (.atexp (.paren (.lam (recP [l]) (ev l)))) e
def rv (x : String) : BAtExp := .var ⟨none, x⟩

/-- `{y = 'c', x = 1}` has the sorted closed record `{x : number, y : Char}`. -/
theorem w_record :
    tyOfD (inferExpWD wdFuel C0 (recE [("y", .atexp chr), ("x", .atexp (int 1))])) =
      some (.record [("x", v 0 .num), ("y", tCharTy)] none) := by decide +kernel

/-- `\r -> r.x : { ε | x : α } -> α`. -/
theorem w_select :
    tyOfD (inferExpWD wdFuel C0 (lam "r" (sel (rv "r") "x"))) =
      some (.fn (.record [("x", v 3 .any)] (some (.fresh 2))) (v 3 .any)) := by decide +kernel

/-- `(\r -> r.x) {x = 'c', y = 1} : Char`. -/
theorem w_select_app :
    tyOfD (inferExpWD wdFuel C0 (.app (.atexp (.paren (lam "r" (sel (rv "r") "x"))))
      (.paren (recE [("x", .atexp chr), ("y", .atexp (int 1))])))) = some tCharTy := by decide +kernel

/-- `(\r -> r.z) {x = 'c'}` is refused: the record lacks `z`. -/
theorem w_select_missing :
    (inferExpWD wdFuel C0 (.app (.atexp (.paren (lam "r" (sel (rv "r") "z")))) (.paren (recE [("x", .atexp chr)])))).isFail
      = true := by decide +kernel

/-- `\r -> { r | x = 1 } : { ε | x : number } -> { ε | x : number }`. -/
theorem w_update :
    tyOfD (inferExpWD wdFuel C0 (lam "r" (.atexp (.update "r" (.field "x" (.atexp (int 1)) none))))) =
      some (.fn (.record [("x", v 1 .num)] (some (.fresh 2))) (.record [("x", v 1 .num)] (some (.fresh 2)))) := by
  decide +kernel

/-- `let f = \r -> { r | x = 'c' } in f {y = 1}` is refused (no field `x`). -/
theorem w_update_missing :
    (inferExpWD wdFuel C0 (letv "f" (lam "r" (.atexp (.update "r" (.field "x" (.atexp chr) none))))
      (.app (ev "f") (.paren (recE [("y", .atexp (int 1))]))))).isFail = true := by decide +kernel

/-- Row polymorphism through `let`: `let f = \r -> (r.x, r.y) in f {x = 1, y = 'c', z = "s"}`. -/
theorem w_row_poly :
    tyOfD (inferExpWD wdFuel C0 (letv "f" (lam "r" (.atexp (.tuple (sel (rv "r") "x") (sel (rv "r") "y") none)))
      (.app (ev "f") (.paren (recE [("x", .atexp (int 1)), ("y", .atexp chr), ("z", .atexp str)]))))) =
      some (tupleTy (v 12 .num) tCharTy none) := by decide +kernel

/-- A field of the wrong type is refused: `(\r -> r.x ++ "s") {x = 'c'}`. -/
theorem w_field_clash :
    (inferExpWD wdFuel C0 (.app (.atexp (.paren (lam "r" (.app (.app (.atexp (.op "++")) (.paren (sel (rv "r") "x"))) str))))
      (.paren (recE [("x", .atexp chr)])))).isFail = true := by decide +kernel

/-! ## The extensible-record tests that `coreRefutes` does not refute, at expression level

  Each program's offending phrase, in a root context with the schemes its module's other
  declarations give (constructors and annotated functions, their row parameters bound). W refutes
  each: two images of one row variable with different labels (`⟨a | ε⟩ ≐ ⟨b | ε⟩`) have no
  unifier. The per-test refusal (of the module) needs module-level W (milestone (f)) and the
  refutation theorem for F_d. -/

def ctxOf (VE : ValEnv) : Ctx := { C0 with E := Env.ofVE VE }
def rb (i : Nat) : RowVar := .bnd i
def ab (i : Nat) : Ty := .var (.bnd i .any)
def cn (x : String) : BAtExp := .con ⟨none, x⟩
def cons2 (a b : BAtExp) : BExp := .app (.app (.atexp (.op "::")) a) (.paren (.app (.app (.atexp (.op "::")) b) .nil))

def tTricky : TyName := ⟨100, 1⟩
def tThing : TyName := ⟨101, 1⟩
def tRoom : TyName := ⟨102, 1⟩
def tWindow : TyName := ⟨103, 0⟩
def unitR : Ty := .con [] tUnit

/-- CompilerIssue2027: `type Tricky r = Tricky { r | a : Int } { r | b : Int }`;
    `mkTricky x = Tricky x x` is refused. -/
def trickyCtx : Ctx := ctxOf [("Tricky", (⟨[.row (rb 0)], .fn (.record [("a", tIntTy)] (some (rb 0)))
  (.fn (.record [("b", tIntTy)] (some (rb 0))) (.con [.record [] (some (rb 0))] tTricky))⟩, .c))]

theorem w_issue2027 :
    (inferExpWD wdFuel trickyCtx (lam "x" (.app (.app (.atexp (cn "Tricky")) (rv "x")) (rv "x")))).isFail = true := by
  decide +kernel

/-- (`Tricky x` alone is fine.) -/
theorem w_issue2027_ok : (inferExpWD wdFuel trickyCtx (lam "x" (.app (.atexp (cn "Tricky")) (rv "x")))).isOk = true := by
  decide +kernel

/-- CompilerIssue2108: `changesTypeVariable : Thing { b | something : () } -> Thing { b | somethingElse : () }`
    and `identity` in one list (the two branches of the `if`) are refused. -/
def thingCtx : Ctx := ctxOf [
  ("changesTypeVariable", (⟨[.row (rb 0)], .fn (.con [.record [("something", unitR)] (some (rb 0))] tThing)
    (.con [.record [("somethingElse", unitR)] (some (rb 0))] tThing)⟩, .v)),
  ("identity", (⟨[.ty (.bnd 0 .any)], .fn (ab 0) (ab 0)⟩, .v))]

theorem w_issue2108 : (inferExpWD wdFuel thingCtx (cons2 (rv "changesTypeVariable") (rv "identity"))).isFail = true := by
  decide +kernel

/-- CompilerIssue2106: `foldl withWindow Room windows` with
    `withWindow : Window -> Room a -> Room { a | withWindow : () }` is refused. -/
def roomCtx : Ctx := ctxOf [
  ("foldl", (⟨[.ty (.bnd 0 .any), .ty (.bnd 1 .any)], .fn (.fn (ab 0) (.fn (ab 1) (ab 1))) (.fn (ab 1) (.fn (listTy (ab 0)) (ab 1)))⟩, .v)),
  ("withWindow", (⟨[.row (rb 0)], .fn (.con [] tWindow) (.fn (.con [.record [] (some (rb 0))] tRoom)
    (.con [.record [("withWindow", unitR)] (some (rb 0))] tRoom))⟩, .v)),
  ("Room", (⟨[.ty (.bnd 0 .any)], .con [ab 0] tRoom⟩, .c))]

theorem w_issue2106 :
    (inferExpWD wdFuel roomCtx (lam "windows" (.app (.app (.app (ev "foldl") (rv "withWindow")) (cn "Room")) (rv "windows")))).isFail
      = true := by decide +kernel

/-- CompilerIssue1691: `combineMaybeAB Just`, with
    `combineMaybeAB : (PartialRecordA a -> Maybe (PartialRecordB a)) -> PartialRecordA a -> FullRecord`,
    is refused (`Just` would need `{ a | fieldA : String } = { a | fieldB : String }`). -/
def fullRecordTy : Ty := .record [("fieldA", tStringTy), ("fieldB", .con [tStringTy] tMaybe)] none
def combineCtx : Ctx := ctxOf [
  ("combineMaybeAB", (⟨[.row (rb 0)], .fn (.fn (.record [("fieldA", tStringTy)] (some (rb 0)))
    (.con [.record [("fieldB", tStringTy)] (some (rb 0))] tMaybe)) (.fn (.record [("fieldA", tStringTy)] (some (rb 0))) fullRecordTy)⟩, .v)),
  ("Just", (⟨[.ty (.bnd 0 .any)], .fn (ab 0) (.con [ab 0] tMaybe)⟩, .c))]

theorem w_issue1691 : (inferExpWD wdFuel combineCtx (.app (ev "combineMaybeAB") (cn "Just"))).isFail = true := by
  decide +kernel

/-- TypeMismatchTwoFlexibleRecordsTest, as one expression (its module's declarations are
    unannotated): `let h = \a -> a.name ++ "s" in \c -> let z = c.name + 1 in h c` is refused. -/
theorem w_twoFlexibleRecords :
    (inferExpWD wdFuel C0 (letv "h" (lam "a" (.app (.app (.atexp (.op "++")) (.paren (sel (rv "a") "name"))) str))
      (lam "c" (letv "z" (.app (.app (.atexp (.op "+")) (.paren (sel (rv "c") "name"))) (int 1))
        (.app (ev "h") (rv "c")))))).isFail = true := by decide +kernel

/-- Controls: the contexts are well formed, and the phrases next to the refused ones elaborate. -/
theorem w_controls :
    (inferExpWD wdFuel thingCtx (cons2 (rv "changesTypeVariable") (rv "changesTypeVariable"))).isOk = true ∧
    (inferExpWD wdFuel roomCtx (lam "windows" (.app (.app (.app (ev "foldl")
      (.paren (lam "w" (lam "r" (ev "r"))))) (cn "Room")) (rv "windows")))).isOk = true ∧
    (inferExpWD wdFuel combineCtx (ev "combineMaybeAB")).isOk = true ∧
    (inferExpWD wdFuel C0 (letv "h" (lam "a" (.app (.app (.atexp (.op "++")) (.paren (sel (rv "a") "name"))) str))
      (lam "c" (.app (ev "h") (rv "c"))))).isOk = true := by decide +kernel

end WExamplesD

end StandardElm.Stat.Complete
