/-
  A Standard Definition of Elm? Mechanisation: the unit examples of milestone (b) of plan step 11
  ("Unit examples", W), by `decide +kernel`, in the empty context (no type environment: a
  monomorphic annotation uses `()`). Examples with integer constants, records or annotations with
  type variables are outside F_b (`unsupported`); they belong to milestones (c) to (e).
-/
import StandardElmMech.Stat.Complete.W

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BAtExp BExp BDec BValBind SLit)

namespace WExamples

def C0 : Ctx := ⟨[], [], Env.empty⟩
def v (x : String) : BExp := .atexp (.var ⟨none, x⟩)
def va (x : String) : BAtExp := .var ⟨none, x⟩
def lam (x : String) (e : BExp) : BExp := .lam (.var x) e
def letv (x : String) (e b : BExp) : BExp := .atexp (.letE (.val (.var x none e none)) b)
def ch : BAtExp := .scon (.char 'c')
def str : BAtExp := .scon (.str "s")

def tyOf : WRes → Option Ty
  | .ok a => some a.ty
  | _ => none

def α0 : Ty := .var (.fresh 0 .any)

/-- `\x -> x` gives `α → α`. -/
theorem w_id : tyOf (inferExpW wFuel C0 (lam "x" (v "x"))) = some (.fn α0 α0) := by decide +kernel

/-- Let-polymorphism: `let id = \x -> x in (id 'c', id "s")` elaborates, at `(Char, String)`. -/
theorem w_letPoly :
    tyOf (inferExpW wFuel C0 (letv "id" (lam "x" (v "x")) (.atexp (.tuple (.app (v "id") ch) (.app (v "id") str) none))))
      = some (tupleTy tCharTy tStringTy none) := by decide +kernel

/-- The same with `id` lambda-bound is refused (monomorphic). -/
theorem w_lamMono :
    (inferExpW wFuel C0 (.app (lam "id" (.atexp (.tuple (.app (v "id") ch) (.app (v "id") str) none)))
      (.paren (lam "x" (v "x"))))).isFail = true := by decide +kernel

/-- A24's group: `f b = g b` and `g b = let u = f 'c' in f "s"`; within the group `f` is
    monomorphic, so its two uses at different types fail. -/
theorem w_a24 :
    (inferExpW wFuel C0 (.atexp (.letE (.val (.var "f" none (lam "b" (.app (v "g") (va "b")))
      (some (.var "g" none (lam "b" (letv "u" (.app (v "f") ch) (.app (v "f") str))) none)))) (.atexp .unit)))).isFail
      = true := by decide +kernel

/-- The occurs check: `\x -> x x` fails. -/
theorem w_occurs : (inferExpW wFuel C0 (lam "x" (.app (v "x") (va "x")))).isFail = true := by decide +kernel

/-- A monomorphic annotation: `let f : () -> (); f = \x -> x in f ()` elaborates, `f 'c'` fails. -/
theorem w_monoAnn_ok :
    tyOf (inferExpW wFuel C0 (.atexp (.letE (.val (.var "f" (some (.fn .unit .unit)) (lam "x" (v "x")) none))
      (.app (v "f") .unit)))) = some tUnitTy := by decide +kernel

theorem w_monoAnn_fail :
    (inferExpW wFuel C0 (.atexp (.letE (.val (.var "f" (some (.fn .unit .unit)) (lam "x" (v "x")) none))
      (.app (v "f") ch)))).isFail = true := by decide +kernel

/-- An unbound variable fails; an integer constant is outside F_b. -/
theorem w_unbound : (inferExpW wFuel C0 (v "y")).isFail = true := by decide +kernel
theorem w_int : (match inferExpW wFuel C0 (.atexp (.scon (.int 1))) with
    | .unsupported => true | _ => false) = true := by decide +kernel

/-- `case` and patterns: `\p -> case p of (a, b) -> (b, a)` swaps. -/
theorem w_case :
    (inferExpW wFuel C0 (lam "p" (.caseE (v "p") (.mk (.mk (.atpat (.tuple (.atpat (.var "a")) (.atpat (.var "b")) none))
      (.atexp (.tuple (v "b") (v "a") none))) none)))).isOk = true := by decide +kernel

/-- A pattern binding is a group by itself: `let (a, b) = ('c', "s") in (b, a)`. -/
theorem w_patBind :
    tyOf (inferExpW wFuel C0 (.atexp (.letE (.val (.pat (.tuple (.atpat (.var "a")) (.atpat (.var "b")) none)
      (.atexp (.tuple (.atexp ch) (.atexp str) none)))) (.atexp (.tuple (v "b") (v "a") none)))))
      = some (tupleTy tStringTy tCharTy none) := by decide +kernel

/-- Recursion through a group: `let loop = \x -> loop x in loop` has type `α → β`. -/
theorem w_rec :
    (inferExpW wFuel C0 (letv "loop" (lam "x" (.app (v "loop") (va "x"))) (v "loop"))).isOk = true := by decide +kernel

/-- The mgu: `α ≐ α → Int` fails (occurs); `α → β ≐ β → Char` gives `α, β ↦ Char`. -/
theorem mgu_occurs : mgu 10 (fun _ => false) [(α0, .fn α0 tIntTy)] = .fail := by decide +kernel

theorem mgu_arrow :
    (match mgu 10 (fun _ => false) [(.fn α0 (.var (.fresh 1 .any)), .fn (.var (.fresh 1 .any)) tCharTy)] with
     | .ok θ => decide (lk θ (.fresh 0 .any) = tCharTy ∧ lk θ (.fresh 1 .any) = tCharTy)
     | _ => false) = true := by decide +kernel

/-- A rigid variable is never bound: `a ≐ Char` fails when `a` is rigid. -/
theorem mgu_rigid : mgu 10 (fun _ => true) [(.var (.named "a"), tCharTy)] = .fail := by decide +kernel

end WExamples

end StandardElm.Stat.Complete
