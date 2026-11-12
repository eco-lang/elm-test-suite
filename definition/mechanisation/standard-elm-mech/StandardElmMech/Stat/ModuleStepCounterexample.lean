/-
  A Standard Definition of Elm? Mechanisation: a regression test of r:sm-topdec-types' side
  condition `tyvars TE = ∅` (plan step 10, found 2026-11-12 while proving the module step of the
  invariance lemma; erratum of the book of the same day).

  r:sm-datbind closes a custom type's constructors with `Clos_C`, where `C` is the context of the
  type declarations, `C ⊕ TE` (r:sm-topdec-types), and `tyvars (C ⊕ TE)` counts the free variables
  of `TE` itself. Without the side condition, `checkTypes`, which checks that TE is a fixed point,
  also accepted a TE whose constructors are not closed: their free variables are in `tyvars TE`
  because they are free in TE. For `type T a = K a` the derivation `mj` gave `K : a -> T a` with
  `a` free; it checked in `Btest`, was an instance of itself, and its interface (the module exposes
  everything) had a free type variable, so `ModuleStep TypesOrdered` was false, and so was the
  book's property after r:sm-module that TE is determined up to the choice of new type names (the
  closed `mp` checked too). Now `mj` does not check and `mp` does.
-/
import StandardElmMech.Stat.Ident

namespace StandardElm.Stat
open StandardElm.Src (BDatBind)

namespace ModuleStepCE

/-- A type name in no basis, of arity 1. -/
def tJ : TyName := ⟨5000, 1⟩

/-- `a -> T a`, with `a` free. -/
def τK : Ty := .fn (.var (.named "a")) (.con [.var (.named "a")] tJ)

def VEK : ValEnv := [("K", (⟨[], τK⟩, .c))]
def TEj : TyEnv := [("T", (tJ.toFcn, VEK))]

/-- `type T a = K a`. -/
def db : BDatBind := [("T", ["a"], [("K", [.tyvar "a"])])]

/-- `module M exposing (..)` with the type declaration, elaborated with `K : a -> T a`. -/
def mj : AModule := ⟨⟨false, "M", .all⟩, [], some (.types TEj VEK (some db) [])⟩

/-- `∀a. a -> T a`. -/
def VEp : ValEnv := [("K", (⟨[.ty (.bnd 0 .any)], .fn (.var (.bnd 0 .any)) (.con [.var (.bnd 0 .any)] tJ)⟩, .c))]
def TEp : TyEnv := [("T", (tJ.toFcn, VEp))]
def mp : AModule := ⟨⟨false, "M", .all⟩, [], some (.types TEp VEp (some db) [])⟩

set_option maxRecDepth 100000 in
/-- The open solution is a fixed point but is refused; the closed one checks. -/
theorem regression : checkTypesFix (modCtx Btest ((elabImports Btest π0 defaultImports).getD [])) TEj VEK (some db) [] = true ∧
    checkModule Btest mj = false ∧ checkModule Btest mp = true ∧ mp.erase = mj.erase := by
  decide +kernel

end ModuleStepCE

end StandardElm.Stat
