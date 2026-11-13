/-
  A Standard Definition of Elm? Mechanisation: algorithm W for fragment F_e (milestone (e) of plan
  step 11, section 6): WD.lean's W (records and rows) with annotations whose type expressions
  name type variables, at the top of a group or nested anywhere.

  * The explicit variables an annotation `ty` adds in a context of explicit variables `U`
    (sec:static-core-explicit) are determined: `newU U ty` holds one variable for each name of
    `tyvars ty` not named by `U`, in the order of first occurrence, a row variable if the name is
    used as the extension variable of a record type expression in `ty` (`{ r | ... }`), a type
    variable (of the class its name gives) otherwise (A19, A36).
  * An annotated member's entry is `∀U'.τ` (`annScheme`, as `AValBind.ve` gives it), so it is
    polymorphic within its group (polymorphic recursion); its body is inferred with `U'` added to
    `U` (A21: a nested annotation that writes one of these names means the same variable). Named
    variables are rigid throughout (`rigidFromD`), so the body cannot instantiate them.
  * Escape (A20): after the members, no explicit variable of an annotated member may be free in
    the group's context under the accumulated substitution (`escapeOK`), else W fails.
  * The closure (A93) is the checker's `closGroup`, as in WD.lean.

  Kinds. The book said that whether a name of `U'` stands for a type or a row variable "is fixed
  by the rules for type expressions"; it was not when the name is used only as a type (`f : a ->
  a` elaborated with `a` a type variable and with `a` a row variable, `{ | a } -> { | a }`), and
  the two derivations are not instances of each other. The erratum of 2026-11-12 fixes the kind
  (sec:static-core-explicit), and step 9's checker asks for exactly W's variables (`newForB`), so
  every derivation's annotations carry them (`canonAnnB`, `WE.canonAnnExp_of_checkExp`).
-/
import StandardElmMech.Stat.Complete.WD

namespace StandardElm.Stat.Complete
namespace WE
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind SLit)

/-! ## The explicit variables of an annotation -/

/-! The explicit variables of an annotation (`nameVar`, `newU0`, `newU`) are step 9's, Schemes.lean:
the checker's `newForB` asks `U' = newU (U of C) ty`. -/

/-- An annotation carries W's variables: its `U'` is the sublist of `newU0 ty` of its members
    (with `NewFor`, this is `U' = newU U ty`, `newU_of_canon`). -/
def canonAnnB : Option (BTy × List BVar) → Bool
  | none => true
  | some (ty, U') => decide (U' = (newU0 ty).filter fun v => decide (v ∈ U'))

/-! ## Groups -/

/-- Step 1 of section 6 for a chain of variable bindings (a pattern binding inside a chain is left
    `unsupported`, as in WD.lean): an annotated member gets `U' = newU (U of C) ty` and the type
    `elabTy (C + U') ty` (an annotation in a context whose explicit variables are ambiguous, which
    no derivation admits, and one whose type has a variable that is not explicit, through an
    alias with a free variable, are left `unsupported`); an unannotated one a fresh variable. -/
def groupEntriesD (C : Ctx) : BValBind → WDM (List (Option (BTy × List BVar) × Ty))
  | .var _ ann _ rest => do
    let e ← match ann with
      | none => do let α ← freshVD; pure ((none : Option (BTy × List BVar)), α)
      | some ty =>
        if decide (Unambiguous C.U) then
          match elabTy (C.plusU (newU C.U ty)) ty with
          | some τ =>
            if τ.vars.all (fun v => v.isNamed && (decide (v ∈ C.U) || decide (v ∈ newU C.U ty))) then
              pure (some (ty, newU C.U ty), τ)
            else wdUnsupported
          | none => wdFail
        else wdUnsupported
    let es ← match rest with
      | none => pure []
      | some vb => groupEntriesD C vb
    pure (e :: es)
  | .pat _ _ => wdUnsupported

/-- A20: no explicit variable of an annotated member is free in `A` (the group's context). -/
def escapeOK (A : List BVar) (es : List (Option (BTy × List BVar) × Ty)) : Bool :=
  es.all fun e => (annU e.1).all fun v => !decide (v ∈ A)

section
variable (fuel : Nat) (R : RRigid)

/-! ## Expressions (WD.lean's, with the escape check after a group) -/

mutual
def wdAtExp (C : Ctx) : BAtExp → WDM (Ty × AAtExp)
  | .scon sc =>
    match sc with
    | .int _ => do let γ ← freshCD .num; pure (γ, .scon sc γ)
    | .float _ _ => pure (tFloatTy, .scon sc tFloatTy)
    | .char _ => pure (tCharTy, .scon sc tCharTy)
    | .str _ => pure (tStringTy, .scon sc tStringTy)
  | .var lv =>
    match C.lookupVal lv with
    | some (σ, _) => do let (ts, τ) ← instantiateD σ; pure (τ, .var lv ts τ)
    | none => wdFail
  | .con lc =>
    match C.lookupVal lc with
    | some (σ, _) => do let (ts, τ) ← instantiateD σ; pure (τ, .con lc ts τ)
    | none => wdFail
  | .op o =>
    match OTstat o with
    | some (σ, _) => do let (ts, τ) ← instantiateD σ; pure (τ, .op o ts τ)
    | none => wdFail
  | .unit => pure (tUnitTy, .unit)
  | .tuple e1 e2 e3 => do
    let (τ1, a1) ← wdExp C e1
    let (τ2, a2) ← wdExp C e2
    let (τ3, a3) ← wdExpOpt C e3
    pure (tupleTy τ1 τ2 τ3, .tuple a1 a2 a3)
  | .nil => do let α ← freshVD; pure (listTy α, .nil (listTy α))
  | .record row => do
    let (ρ, ar) ← wdExpRowOpt C row
    pure (.record ρ none, .record ar)
  | .update x row =>
    match C.lookupVal ⟨none, x⟩ with
    | some (σ, _) => do
      let (ts, τx) ← instantiateD σ
      let (ρ, ar) ← wdExpRow C row
      let e ← freshRowD
      unifyWD fuel R τx (.record ρ (some e))
      pure (τx, .update x ts τx ar)
    | none => wdFail
  | .letE d e => do
    let ad ← wdDec C d
    let θ ← getθD
    let VEc := closGroup (ctxRsb (toRS θ) C).tyvars (rsbVE (toRS θ) (match ad with | .val VE _ => VE))
    let (τ, ae) ← wdExp (C.plusVE VEc) e
    pure (τ, .letE ad ae)
  | .paren e => do let (τ, a) ← wdExp C e; pure (τ, .paren a)
def wdExp (C : Ctx) : BExp → WDM (Ty × AExp)
  | .atexp a => do let (τ, a') ← wdAtExp C a; pure (τ, .atexp a')
  | .app e a => do
    let (τ1, ae) ← wdExp C e
    let (τ2, aa) ← wdAtExp C a
    let β ← freshVD
    unifyWD fuel R τ1 (.fn τ2 β)
    pure (β, .app ae aa)
  | .lam p e => do
    let (τp, ap) ← wdAtPat fuel R C p
    let (τe, ae) ← wdExp (C.plusVE ap.ve) e
    pure (.fn τp τe, .lam ap ae)
  | .caseE e m => do
    let (τe, ae) ← wdExp C e
    let (τm, am) ← wdMatch C m
    let β ← freshVD
    unifyWD fuel R τm (.fn τe β)
    pure (β, .caseE ae am)
/-- A row of fields: its row of types (as `AExpRow.row`, sorted) and the annotated row. -/
def wdExpRow (C : Ctx) : BExpRow → WDM (Row × AExpRow)
  | .field l e rest => do
    let (τ, ae) ← wdExp C e
    let (ρ, ar) ← wdExpRowOpt C rest
    pure (Row.modify [(l, τ)] ρ, .field l ae ar)
def wdExpRowOpt (C : Ctx) : Option BExpRow → WDM (Row × Option AExpRow)
  | none => pure ([], none)
  | some r => do let (ρ, a) ← wdExpRow C r; pure (ρ, some a)
def wdExpOpt (C : Ctx) : Option BExp → WDM (Option Ty × Option AExp)
  | none => pure (none, none)
  | some e => do let (τ, a) ← wdExp C e; pure (some τ, some a)
def wdMatch (C : Ctx) : BMatch → WDM (Ty × AMatch)
  | .mk mr rest => do
    let (τ, amr) ← wdMRule C mr
    let ar ← wdMatchOpt C τ rest
    pure (τ, .mk amr ar)
def wdMatchOpt (C : Ctx) (τ : Ty) : Option BMatch → WDM (Option AMatch)
  | none => pure none
  | some m => do
    let (τm, am) ← wdMatch C m
    unifyWD fuel R τm τ
    pure (some am)
def wdMRule (C : Ctx) : BMRule → WDM (Ty × AMRule)
  | .mk p e => do
    let (τp, ap) ← wdPat fuel R C p
    let (τe, ae) ← wdExp (C.plusVE ap.ve) e
    pure (.fn τp τe, .mk ap ae)
def wdDec (C : Ctx) : BDec → WDM ADec
  | .val (.pat p e) => do
    let (τp, ap) ← wdAtPat fuel R C p
    let VE0 := ap.ve
    if VE0.all (fun q => !conBound C q.1) then
      let (τe, ae) ← wdExp (C.plusVE VE0) e
      unifyWD fuel R τe τp
      pure (.val VE0 (.pat ap ae))
    else wdUnsupported
  | .val (.var x ann e rest) => do
    let es ← groupEntriesD C (.var x ann e rest)
    let VE0 := groupVE (.var x ann e rest) es
    let avb ← wdMembers (C.plusVE VE0) (.var x ann e rest) es
    let θ ← getθD
    if escapeOK (ctxRsb (toRS θ) (C.plusVE VE0)).tyvars es then pure (.val VE0 avb) else wdFail
def wdMembers (Cg : Ctx) : BValBind → List (Option (BTy × List BVar) × Ty) → WDM AValBind
  | .var x _ e rest, (ann, τx) :: es => do
    let (τe, ae) ← wdExp (Cg.plusU (annU ann)) e
    unifyWD fuel R τe τx
    let ar ← wdMembersOpt Cg rest es
    pure (.var x ann τx ae ar)
  | _, _ => wdUnsupported
def wdMembersOpt (Cg : Ctx) : Option BValBind → List (Option (BTy × List BVar) × Ty) → WDM (Option AValBind)
  | none, _ => pure none
  | some vb, es => do let a ← wdMembers Cg vb es; pure (some a)
end

end

/-! ## The root -/

/-- W for F_e on an expression in the root context `C0`, as WD.lean's `inferExpWD`: the form the
    proofs read (`inferExpWD_eq`). -/
def inferExpWDSpec (fuel : Nat) (C0 : Ctx) (e : BExp) : WRes :=
  let n0 := freshAboveD C0
  match wdExp fuel (rigidFromD n0) C0 e ⟨[], n0⟩ with
  | .ok (_, a) st =>
    let af := rsbExp (toRS st.θ) a
    if (nodesExp C0 [] af).all (fun nd => nd.tys.all cnB) then
      (if checkExp C0 af && decide (af.erase = e) then .ok af else .internal)
    else .fail
  | .fail => .fail
  | .unsupported => .unsupported
  | .outOfFuel => .outOfFuel

/-- W for F_e on an expression in the root context `C0`, as WD.lean's `inferExpWD`. The checker is
    asked first: a derivation it accepts has canonical types at its nodes, so the nodes (whose
    paths and contexts are costly for the kernel, milestone (g)) are built only when it refuses. -/
def inferExpWD (fuel : Nat) (C0 : Ctx) (e : BExp) : WRes :=
  let n0 := freshAboveD C0
  match wdExp fuel (rigidFromD n0) C0 e ⟨[], n0⟩ with
  | .ok (_, a) st =>
    let af := rsbExp (toRS st.θ) a
    if checkExp C0 af && decide (af.erase = e) then .ok af
    else if (nodesExp C0 [] af).all (fun nd => nd.tys.all cnB) then .internal else .fail
  | .fail => .fail
  | .unsupported => .unsupported
  | .outOfFuel => .outOfFuel

theorem inferExpWD_eq (fuel : Nat) (C0 : Ctx) (e : BExp) : inferExpWD fuel C0 e = inferExpWDSpec fuel C0 e := by
  unfold inferExpWD inferExpWDSpec
  simp only
  split
  · rename_i a st _
    by_cases hc : (checkExp C0 (rsbExp (toRS st.θ) a) && decide ((rsbExp (toRS st.θ) a).erase = e)) = true
    · have hk : checkExp C0 (rsbExp (toRS st.θ) a) = true := by
        simp only [Bool.and_eq_true] at hc; exact hc.1
      have hcn : ((nodesExp C0 [] (rsbExp (toRS st.θ) a)).all fun nd => nd.tys.all cnB) = true := by
        simp only [List.all_eq_true]
        intro nd hnd τ hτ
        exact ((Ty.okB_iff τ).mp (okB_of_checkExp hk nd hnd τ hτ)).1
      rw [if_pos hc, if_pos hcn, if_pos hc]
    · rw [if_neg hc]
      split <;> simp_all
  · rfl
  · rfl
  · rfl

/-! ## Soundness (L10) -/

/-- Soundness of W for F_e: what it returns is a derivation of the phrase that step 9's checker
    accepts, with canonical types at its nodes. -/
theorem inferExpWD_sound {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (h : inferExpWD fuel C0 e = .ok a) :
    checkExp C0 a = true ∧ a.erase = e ∧ ∀ nd ∈ nodesExp C0 [] a, ∀ τ ∈ nd.tys, cnB τ = true := by
  rw [inferExpWD_eq] at h
  unfold inferExpWDSpec at h
  dsimp only at h
  split at h
  · split at h
    · rename_i hcn
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        simp only [List.all_eq_true] at hcn
        exact ⟨hc.1, hc.2, hcn⟩
      · cases h
    · cases h
  · cases h
  · cases h
  · cases h

theorem inferExpWD_elab {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (h : inferExpWD fuel C0 e = .ok a) :
    ElExp C0 e a.ty := by
  obtain ⟨hc, he, -⟩ := inferExpWD_sound h
  have := checkExp_sound C0 a hc
  rw [he] at this; exact this

end WE

end StandardElm.Stat.Complete

