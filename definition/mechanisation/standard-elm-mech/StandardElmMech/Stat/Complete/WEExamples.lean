/-
  A Standard Definition of Elm? Mechanisation: unit examples of W for fragment F_e (milestone (e)
  of plan step 11, "Unit examples"), by `decide +kernel`: annotations with type variables, nested
  and in groups.

  * A20: `f x = let g : a -> a; g y = x in g x` is refused (the escape check);
  * A21: a nested annotation that writes an enclosing annotation's name means the same variable;
  * A93: the closure of a group gives an annotated member the extra `number` variable of another
    member's type;
  * polymorphic recursion through an annotation, `f : number -> Int -> Float` with a recursive
    use at `Float`; without the annotation, `f x = f (x, x)` fails (occurs check);
  * A36: `{ number | x : () }` does not elaborate;
  * the explicit variables W takes (`newU`): a name used as an extension variable is a row
    variable, any other a type variable.
-/
import StandardElmMech.Stat.Complete.WE
import StandardElmMech.Stat.Complete.WExamplesD

namespace StandardElm.Stat.Complete
open StandardElm.Stat
open StandardElm.Src (BTy BExp BAtExp BAtPat BDec BValBind SLit)

namespace WEExamples
open WExamplesC (C0 ev lam int v)

/-- A context with the type names `Int` and `Float`. -/
def C1 : Ctx :=
  ⟨[tInt, tFloat], [], ⟨[], [("Int", (tInt.toFcn, [])), ("Float", (tFloat.toFcn, []))], []⟩⟩

def tv (a : String) : BTy := .tyvar a
def tfn (a b : BTy) : BTy := .fn a b
def tcon (c : String) : BTy := .con ⟨none, c⟩ []
/-- `let x : ty = e in b` (no annotation when `ty` is `none`). -/
def letA (x : String) (ty : Option BTy) (e b : BExp) : BExp := .atexp (.letE (.val (.var x ty e none)) b)
def app (f : BExp) (a : BAtExp) : BExp := .app f a
def pair (a b : BExp) : BAtExp := .tuple a b none
def evA (x : String) : BAtExp := .var ⟨none, x⟩
def op2 (o : String) (a b : BAtExp) : BExp := .app (.app (.atexp (.op o)) a) b

def okTy : WRes → Option Ty
  | .ok a => some a.ty
  | _ => none

/-! ## A20: escape -/

/-- `let f = \x -> let g : a -> a = \y -> x in g x in f` is refused: `g`'s body has type `a -> a`
    only if `x` has the explicit type `a`, which is then free in `g`'s context. -/
theorem we_a20 :
    (WE.inferExpWD wdFuel C0
      (letA "f" none (lam "x" (letA "g" (some (tfn (tv "a") (tv "a"))) (lam "y" (ev "x")) (app (ev "g") (evA "x"))))
        (ev "f"))).isFail = true := by decide +kernel

/-- Without the escape, the same annotation elaborates: `let g : a -> a = \y -> y in g` has a
    fresh instance of `∀a. a -> a`. -/
theorem we_a20_ok :
    (match okTy (WE.inferExpWD wdFuel C0 (letA "g" (some (tfn (tv "a") (tv "a"))) (lam "y" (ev "y")) (ev "g"))) with
      | some (.fn (.var a) (.var b)) => a == b && a.cls == .any
      | _ => false) = true := by decide +kernel

/-! ## A21: nested annotations -/

/-- `f : a -> (a, a)` with `f x = let g : b -> (a, b); g y = (x, y) in g x`: the inner `a` is the
    outer one, so `(x, y)` has the type `g`'s annotation gives. The result is `f`'s instance. -/
theorem we_a21 :
    (match okTy (WE.inferExpWD wdFuel C0
      (letA "f" (some (tfn (tv "a") (.tuple (tv "a") (tv "a") none)))
        (lam "x" (letA "g" (some (tfn (tv "b") (.tuple (tv "a") (tv "b") none))) (lam "y" (.atexp (pair (ev "x") (ev "y"))))
          (app (ev "g") (evA "x"))))
        (ev "f"))) with
      | some (.fn (.var a) τ) => τ == tupleTy (.var a) (.var a) none
      | _ => false) = true := by decide +kernel

/-- If the inner annotation's `a` were new, `(x, y)` could not have its type; with a name that is
    not the outer one the same program is refused: `g : c -> (b, c)` with `g y = (x, y)`. -/
theorem we_a21_new :
    (WE.inferExpWD wdFuel C0
      (letA "f" (some (tfn (tv "a") (.tuple (tv "a") (tv "a") none)))
        (lam "x" (letA "g" (some (tfn (tv "c") (.tuple (tv "b") (tv "c") none))) (lam "y" (.atexp (pair (ev "x") (ev "y"))))
          (app (ev "g") (evA "x"))))
        (ev "f"))).isFail = true := by decide +kernel

/-! ## A93: the closure of a group with an annotated member -/

/-- The group `f : b -> b`, `f n = let u = g 1 in n`, and `g y = y`: `g : γ → γ` with `γ` of class
    number, which `f`'s type does not mention; the closure gives `f` the scheme `∀ b γ. b → b`
    (A93), so the occurrence of `f` in the body records two instances. -/
def a93 : BExp :=
  .atexp (.letE (.val (.var "f" (some (tfn (tv "b") (tv "b")))
      (lam "n" (letA "u" none (app (ev "g") (int 1)) (ev "n")))
      (some (.var "g" none (lam "y" (ev "y")) none))))
    (ev "f"))

def instLen : WRes → Option Nat
  | .ok (.atexp (.letE _ (.atexp (.var _ inst _)))) => some inst.length
  | _ => none

theorem we_a93 : instLen (WE.inferExpWD wdFuel C0 a93) = some 2 := by decide +kernel

/-! ## Polymorphic recursion -/

/-- `f : number -> Int -> Float` with `f x n = f 2.5 (n - 1)`: within its own body `f` is used at
    `Float` while `x` has the explicit type `number`. -/
theorem we_polyrec :
    (match okTy (WE.inferExpWD wdFuel C1
      (letA "f" (some (tfn (tv "number") (tfn (tcon "Int") (tcon "Float"))))
        (lam "x" (lam "n" (app (app (ev "f") (.scon (.float 25 (-1)))) (.paren (op2 "-" (evA "n") (int 1))))))
        (ev "f"))) with
      | some (.fn (.var a) τ) => a.cls == .num && τ == .fn tIntTy tFloatTy
      | _ => false) = true := by decide +kernel

/-- `f : a -> ()` with `f x = f (x, x)` elaborates (the recursive use is at `(a, a)`); without the
    annotation, `f x = f (x, x)` is refused (`α = (α, α)`). -/
theorem we_polyrec_pair :
    (WE.inferExpWD wdFuel C0 (letA "f" (some (tfn (tv "a") .unit)) (lam "x" (app (ev "f") (pair (ev "x") (ev "x"))))
      (ev "f"))).isOk = true := by decide +kernel

theorem we_rec_pair_fails :
    (WE.inferExpWD wdFuel C0 (letA "f" none (lam "x" (app (ev "f") (pair (ev "x") (ev "x")))) (ev "f"))).isFail = true := by
  decide +kernel

/-- An annotation is never more general than the body: `f : a -> a` with `f x = (x, x)` fails. -/
theorem we_too_general :
    (WE.inferExpWD wdFuel C0 (letA "f" (some (tfn (tv "a") (tv "a"))) (lam "x" (.atexp (pair (ev "x") (ev "x"))))
      (ev "f"))).isFail = true := by decide +kernel

/-! ## A36 and the kinds of explicit variables -/

/-- `{ number | x : () }` does not elaborate (A36): the annotation is refused. -/
theorem we_a36 :
    (WE.inferExpWD wdFuel C0 (letA "f" (some (tfn (.openRecord "number" (.field "x" .unit none)) .unit))
      (lam "r" (.atexp .unit)) (ev "f"))).isFail = true := by decide +kernel

/-- `r` in `{ r | x : () } -> r` is a row variable; `a` in `a -> a` a type variable. -/
theorem we_newU :
    Stat.newU [] (tfn (.openRecord "r" (.field "x" .unit none)) (tv "r")) = [.row (.named "r")] ∧
    Stat.newU [] (tfn (tv "a") (tv "a")) = [.ty (.named "a")] ∧
    Stat.newU [.ty (.named "a")] (tfn (tv "a") (tv "b")) = [.ty (.named "b")] := by decide +kernel

/-- `f : { r | x : () } -> r` with `f s = s`: the record with its field is the open record `r`
    stands for, `{ r | x : () } -> { | r }` against `{ ε | x : () } -> { ε | x : () }`: refused,
    since the field `x` would have to belong to `r`'s fields and to the record's own. -/
theorem we_row_rigid :
    (WE.inferExpWD wdFuel C0 (letA "f" (some (tfn (.openRecord "r" (.field "x" .unit none)) (tv "r")))
      (lam "s" (ev "s")) (ev "f"))).isFail = true := by decide +kernel

/-! ## The six rigid-`let` tests, at expression level

  Each of CompilerIssue1639, 1839, 2001, 2077, 2296 and 2301 is a module whose unannotated
  function has a `let` annotation that names a type variable which the function's argument would
  have to equal (A20). Below, the function's body as a lambda, in a hand-built context with the
  module's types and the values it uses (their closed schemes): W refuses each, by the escape
  check. The per-test refusals need module-level W (milestone (f)). -/

def tDict : TyName := ⟨200, 2⟩
def tFoo : TyName := ⟨201, 1⟩
def tAttr : TyName := ⟨202, 1⟩
def tNode : TyName := ⟨203, 1⟩
def b (i : Nat) : Ty := .var (.bnd i .any)

/-- The types and values the six modules use: `Int`, `Float`, `Bool`, `List`, and 2001's `Dict`,
    `Foo`, `toDict : Foo a -> Dict a b`, and 2296's `Attribute`, `Node`, `div`, `map`, `asCell`. -/
def Cm : Ctx :=
  ⟨[tInt, tFloat, tBool, tList, tDict, tFoo, tAttr, tNode], [],
   ⟨[], [("Int", (tInt.toFcn, [])), ("Float", (tFloat.toFcn, [])), ("Bool", (tBool.toFcn, [])),
         ("List", (tList.toFcn, [])), ("Dict", (tDict.toFcn, [])), ("Foo", (tFoo.toFcn, [])),
         ("Attribute", (tAttr.toFcn, [])), ("Node", (tNode.toFcn, []))],
    [("toDict", (⟨[.ty (.bnd 0 .any), .ty (.bnd 1 .any)], .fn (.con [b 0] tFoo) (.con [b 0, b 1] tDict)⟩, .v)),
     ("div", (⟨[.ty (.bnd 0 .any)], .fn (listTy (.con [b 0] tAttr)) (.fn (listTy (.con [b 0] tNode)) (.con [b 0] tNode))⟩, .v)),
     ("map", (⟨[.ty (.bnd 0 .any), .ty (.bnd 1 .any)], .fn (.fn (b 0) (b 1)) (.fn (listTy (b 0)) (listTy (b 1)))⟩, .v)),
     ("asCell", (⟨[.ty (.bnd 0 .any)], .fn (.con [b 0] tNode) (.con [b 0] tNode)⟩, .v))]⟩⟩

def tapp (c : String) (args : List BTy) : BTy := .con ⟨none, c⟩ args

/-- 1639: `\model -> let step : ( a, Int ) = ( model, 3 ) in 5`. -/
theorem we_1639 :
    (WE.inferExpWD wdFuel Cm (lam "model" (letA "step" (some (.tuple (tv "a") (tcon "Int") none))
      (.atexp (pair (ev "model") (.atexp (int 3)))) (.atexp (int 5))))).isFail = true := by decide +kernel

/-- 1839: `\two -> let three : List a = two in 1`. -/
theorem we_1839 :
    (WE.inferExpWD wdFuel Cm (lam "two" (letA "three" (some (tapp "List" [tv "a"])) (ev "two") (.atexp (int 1))))).isFail
      = true := by decide +kernel

/-- 2001: `\value -> let dict : Dict a b = toDict value in ()`. -/
theorem we_2001 :
    (WE.inferExpWD wdFuel Cm (lam "value" (letA "dict" (some (tapp "Dict" [tv "a", tv "b"])) (app (ev "toDict") (evA "value"))
      (.atexp .unit)))).isFail = true := by decide +kernel

/-- 2077: `\fn -> \a -> let fn_ : { a | foo : Int } -> Bool = fn in let a_ : { foo : Int } = a in fn_ a_`
    (the two definitions are independent, so two groups). -/
theorem we_2077 :
    (WE.inferExpWD wdFuel Cm (lam "fn" (lam "a"
      (letA "fn_" (some (tfn (.openRecord "a" (.field "foo" (tcon "Int") none)) (tcon "Bool"))) (ev "fn")
        (letA "a_" (some (.record (some (.field "foo" (tcon "Int") none)))) (ev "a")
          (app (ev "fn_") (evA "a_"))))))).isFail = true := by decide +kernel

/-- 2296: `\attrs -> \children -> let cells : List (Node msg) = map asCell children in div attrs cells`. -/
theorem we_2296 :
    (WE.inferExpWD wdFuel Cm (lam "attrs" (lam "children"
      (letA "cells" (some (tapp "List" [.paren (tapp "Node" [tv "msg"])])) (app (app (ev "map") (evA "asCell")) (evA "children"))
        (app (app (ev "div") (evA "attrs")) (evA "cells")))))).isFail = true := by decide +kernel

/-- 2301: `\x -> let g : (a -> ()) -> () = \h -> h x in x`. -/
theorem we_2301 :
    (WE.inferExpWD wdFuel Cm (lam "x" (letA "g" (some (tfn (.paren (tfn (tv "a") .unit)) .unit)) (lam "h" (app (ev "h") (evA "x")))
      (ev "x")))).isFail = true := by decide +kernel

/-- Their annotations are not at fault: with the argument annotated at the explicit type (2301 with
    `f : a -> a`), the same body elaborates. -/
theorem we_2301_annotated :
    (WE.inferExpWD wdFuel Cm (letA "f" (some (tfn (tv "a") (tv "a")))
      (lam "x" (letA "g" (some (tfn (.paren (tfn (tv "a") .unit)) .unit)) (lam "h" (app (ev "h") (evA "x"))) (ev "x")))
      (ev "f"))).isOk = true := by decide +kernel

end WEExamples

end StandardElm.Stat.Complete
