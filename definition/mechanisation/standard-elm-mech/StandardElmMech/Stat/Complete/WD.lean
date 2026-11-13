/-
  A Standard Definition of Elm? Mechanisation: algorithm W for fragment F_d (records and rows),
  milestone (d) of plan step 11 (section 6).

  W.lean's algorithm with substitutions of type *and row* variables (`RSub`, RSubst.lean) and
  unification with rows (`rLoop`, MguR.lean), and the record phrases:

  * a record expression `{ l1 = e1, ... }` has the closed record of its fields' types (sorted as
    `AExpRow.row` sorts them);
  * an update `{ x | l1 = e1, ... }` instantiates `x`'s scheme to `τ`, and unifies `τ` with the
    row of the fields and a fresh tail (`r:s-atexp-update`); its type is `τ`;
  * a record pattern `{ l1, ..., lk }` gives fresh `αi` and a fresh tail `ε`, type
    `⟨{li ↦ αi} | ε⟩`;
  * a scheme's bound row variable is instantiated with a fresh row variable.

  Field selection and accessors are derived forms (record patterns, Appendix A). Every
  unification runs with an empty frame; definedness on the rest of the derivation (A23: a lacks
  constraint between two unifications) is checked once, on the result: a result with a repeated
  label at a node is a refusal (`inferExpWD`). Soundness is by construction, as for W:
  `inferExpWD_sound` (the checker accepts what W returns).

  W.lean (milestones (b) and (c)) is kept: its theorems (`wRefutation`, `wCompleteness`,
  `wPrincipality`, `inferExpW_terminates`) are about `inferExpW`, which leaves records
  `unsupported`. Their restatement for `inferExpWD` (milestone (d)) is the port of the W chain to
  `RSub` (see the report).
-/
import StandardElmMech.Stat.Complete.MguRTerm
import StandardElmMech.Stat.Complete.W
import StandardElmMech.Stat.Principal

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind SLit)

/-! ## Substitution on annotated phrases (L1) -/

def rsbScheme (s : RSub) (σ : Scheme) : Scheme := ⟨σ.bound, rsb s σ.body⟩

def rsbVE (s : RSub) (VE : ValEnv) : ValEnv := VE.map fun p => (p.1, (rsbScheme s p.2.1, p.2.2))

def ctxRsb (s : RSub) (C : Ctx) : Ctx := { C with E := { C.E with VE := rsbVE s C.E.VE } }

def rsbOpt (s : RSub) : Option Ty → Option Ty
  | none => none
  | some τ => some (rsb s τ)

mutual
def rsbAtPat (s : RSub) : AAtPat → AAtPat
  | .wild τ => .wild (rsb s τ)
  | .scon sc τ => .scon sc (rsb s τ)
  | .var x τ => .var x (rsb s τ)
  | .con lc inst τ => .con lc (rsbList s inst) (rsb s τ)
  | .unit => .unit
  | .tuple p1 p2 p3 => .tuple (rsbPat s p1) (rsbPat s p2) (rsbPatOpt s p3)
  | .nil τ => .nil (rsb s τ)
  | .record row τ => .record (rsbPatRowOpt s row) (rsb s τ)
  | .paren p => .paren (rsbPat s p)
def rsbPatRow (s : RSub) : APatRow → APatRow
  | .field l τ rest => .field l (rsb s τ) (rsbPatRowOpt s rest)
def rsbPatRowOpt (s : RSub) : Option APatRow → Option APatRow
  | none => none
  | some r => some (rsbPatRow s r)
def rsbPat (s : RSub) : APat → APat
  | .atpat a => .atpat (rsbAtPat s a)
  | .con lc inst args τ => .con lc (rsbList s inst) (rsbAtPats s args) (rsb s τ)
  | .cons p1 p2 => .cons (rsbPat s p1) (rsbPat s p2)
  | .as p x => .as (rsbPat s p) x
def rsbPatOpt (s : RSub) : Option APat → Option APat
  | none => none
  | some p => some (rsbPat s p)
def rsbAtPats (s : RSub) : List AAtPat → List AAtPat
  | [] => []
  | a :: as => rsbAtPat s a :: rsbAtPats s as
end

mutual
def rsbAtExp (s : RSub) : AAtExp → AAtExp
  | .scon sc τ => .scon sc (rsb s τ)
  | .var lv inst τ => .var lv (rsbList s inst) (rsb s τ)
  | .con lc inst τ => .con lc (rsbList s inst) (rsb s τ)
  | .op o inst τ => .op o (rsbList s inst) (rsb s τ)
  | .unit => .unit
  | .tuple e1 e2 e3 => .tuple (rsbExp s e1) (rsbExp s e2) (rsbExpOpt s e3)
  | .nil τ => .nil (rsb s τ)
  | .record row => .record (rsbExpRowOpt s row)
  | .update x inst τ row => .update x (rsbList s inst) (rsb s τ) (rsbExpRow s row)
  | .letE d e => .letE (rsbDec s d) (rsbExp s e)
  | .paren e => .paren (rsbExp s e)
def rsbExpRow (s : RSub) : AExpRow → AExpRow
  | .field l e rest => .field l (rsbExp s e) (rsbExpRowOpt s rest)
def rsbExpRowOpt (s : RSub) : Option AExpRow → Option AExpRow
  | none => none
  | some r => some (rsbExpRow s r)
def rsbExp (s : RSub) : AExp → AExp
  | .atexp a => .atexp (rsbAtExp s a)
  | .app e a => .app (rsbExp s e) (rsbAtExp s a)
  | .lam p e => .lam (rsbAtPat s p) (rsbExp s e)
  | .caseE e m => .caseE (rsbExp s e) (rsbMatch s m)
def rsbExpOpt (s : RSub) : Option AExp → Option AExp
  | none => none
  | some e => some (rsbExp s e)
def rsbMatch (s : RSub) : AMatch → AMatch
  | .mk mr rest => .mk (rsbMRule s mr) (rsbMatchOpt s rest)
def rsbMatchOpt (s : RSub) : Option AMatch → Option AMatch
  | none => none
  | some m => some (rsbMatch s m)
def rsbMRule (s : RSub) : AMRule → AMRule
  | .mk p e => .mk (rsbPat s p) (rsbExp s e)
def rsbDec (s : RSub) : ADec → ADec
  | .val VE vb => .val (rsbVE s VE) (rsbValBind s vb)
def rsbValBind (s : RSub) : AValBind → AValBind
  | .var x ann τ e rest => .var x ann (rsb s τ) (rsbExp s e) (rsbValBindOpt s rest)
  | .pat p e => .pat (rsbAtPat s p) (rsbExp s e)
def rsbValBindOpt (s : RSub) : Option AValBind → Option AValBind
  | none => none
  | some vb => some (rsbValBind s vb)
end

/-! ## The state and the monad -/

structure WDSt where
  θ : RBnd
  n : Nat
  deriving Repr

inductive WDOut (α : Type) where
  | ok (a : α) (st : WDSt)
  | fail
  | unsupported
  | outOfFuel

def WDM (α : Type) := WDSt → WDOut α

def WDM.bind {α β : Type} (m : WDM α) (f : α → WDM β) : WDM β := fun st =>
  match m st with
  | .ok a st' => f a st'
  | .fail => .fail
  | .unsupported => .unsupported
  | .outOfFuel => .outOfFuel

instance : Monad WDM where
  pure a := fun st => .ok a st
  bind := WDM.bind

def wdFail {α : Type} : WDM α := fun _ => .fail
def wdUnsupported {α : Type} : WDM α := fun _ => .unsupported

/-- A fresh flexible variable of class any. -/
def freshVD : WDM Ty := fun st => .ok (.var (.fresh st.n .any)) { st with n := st.n + 1 }

/-- A fresh flexible variable of class `c`. -/
def freshCD (c : Cls) : WDM Ty := fun st => .ok (.var (.fresh st.n c)) { st with n := st.n + 1 }

def getθD : WDM RBnd := fun st => .ok st.θ st

/-- A fresh row variable. -/
def freshRowD : WDM RowVar := fun st => .ok (.fresh st.n) { st with n := st.n + 1 }

/-- unify (τ ≐ τ'): MguR.lean's loop from the current substitution and counter, with an empty frame. -/
def unifyWD (fuel : Nat) (R : RRigid) (τ1 τ2 : Ty) : WDM Unit := fun st =>
  match rLoop R fuel [(rsb (toRS st.θ) τ1, rsb (toRS st.θ) τ2)] [] st.θ st.n with
  | .ok θ' n' => .ok () ⟨θ', n'⟩
  | .fail => .fail
  | .outOfFuel => .outOfFuel

/-- Fresh variables for the bound variables of a scheme, each of the class of the bound one; a
    fresh row variable `⟨∅ | ε⟩` for a bound row variable. -/
def instVarsD : List BVar → WDM (List Ty)
  | [] => pure []
  | .ty a :: rest => do
    let t ← freshCD a.cls
    let ts ← instVarsD rest
    pure (t :: ts)
  | .row _ :: rest => do
    let e ← freshRowD
    let ts ← instVarsD rest
    pure (.record [] (some e) :: ts)

/-- The most general instance of a scheme: its instance list and type. -/
def instantiateD (σ : Scheme) : WDM (List Ty × Ty) := do
  let ts ← instVarsD σ.bound
  match bindSubst σ.bound ts with
  | some S =>
    match S.apply σ.body with
    | some τ => pure (ts, τ)
    | none => wdUnsupported
  | none => wdUnsupported

/-! ## Patterns -/

section
variable (fuel : Nat) (R : RRigid)

/-- Unify each argument pattern's type with the constructor's argument type. -/
def unifyArgsD : List Ty → List Ty → WDM Unit
  | [], [] => pure ()
  | t :: ts, u :: us => do unifyWD fuel R t u; unifyArgsD ts us
  | _, _ => wdUnsupported

mutual
def wdAtPat (C : Ctx) : BAtPat → WDM (Ty × AAtPat)
  | .wild => do let α ← freshVD; pure (α, .wild α)
  | .scon sc =>
    match sc with
    | .int _ => pure (tIntTy, .scon sc tIntTy)
    | .char _ => pure (tCharTy, .scon sc tCharTy)
    | .str _ => pure (tStringTy, .scon sc tStringTy)
    | .float _ _ => wdFail
  | .var x => do let α ← freshVD; pure (α, .var x α)
  | .con lc =>
    match C.lookupVal lc with
    | some (σ, .c) => do
      let (ts, τ) ← instantiateD σ
      match τ with
      | .con _ _ => pure (τ, .con lc ts τ)
      | .var _ => wdUnsupported
      | _ => wdFail
    | some (_, .v) => wdFail
    | none => wdFail
  | .unit => pure (tUnitTy, .unit)
  | .tuple p1 p2 p3 => do
    let (τ1, a1) ← wdPat C p1
    let (τ2, a2) ← wdPat C p2
    let (τ3, a3) ← wdPatOpt C p3
    pure (tupleTy τ1 τ2 τ3, .tuple a1 a2 a3)
  | .nil => do let α ← freshVD; pure (listTy α, .nil (listTy α))
  | .record row => do
    let ar ← wdPatRowOpt row
    let e ← freshRowD
    let τ := Ty.record (APatRow.rowOpt ar) (some e)
    pure (τ, .record ar τ)
  | .paren p => do let (τ, a) ← wdPat C p; pure (τ, .paren a)
def wdPatRow : BPatRow → WDM APatRow
  | .field l rest => do
    let α ← freshVD
    let r ← wdPatRowOpt rest
    pure (.field l α r)
def wdPatRowOpt : Option BPatRow → WDM (Option APatRow)
  | none => pure none
  | some r => do let a ← wdPatRow r; pure (some a)
def wdPat (C : Ctx) : BPat → WDM (Ty × APat)
  | .atpat a => do let (τ, a') ← wdAtPat C a; pure (τ, .atpat a')
  | .con lc args =>
    match C.lookupVal lc with
    | some (σ, .c) => do
      let (ts, τb) ← instantiateD σ
      match peel args.length τb with
      | some (τs, .con us t) => do
        let ps ← wdAtPats C args
        unifyArgsD fuel R (ps.map (·.1)) τs
        pure (.con us t, .con lc ts (ps.map (·.2)) (.con us t))
      | some (_, .var _) => wdUnsupported
      | some (_, _) => wdFail
      | none => if peelStuckVar args.length τb then wdUnsupported else wdFail
    | some (_, .v) => wdFail
    | none => wdFail
  | .cons p1 p2 => do
    let (τ1, a1) ← wdPat C p1
    let (τ2, a2) ← wdPat C p2
    unifyWD fuel R τ2 (listTy τ1)
    pure (listTy τ1, .cons a1 a2)
  | .as p x => do let (τ, a) ← wdPat C p; pure (τ, .as a x)
def wdPatOpt (C : Ctx) : Option BPat → WDM (Option Ty × Option APat)
  | none => pure (none, none)
  | some p => do let (τ, a) ← wdPat C p; pure (some τ, some a)
def wdAtPats (C : Ctx) : List BAtPat → WDM (List (Ty × AAtPat))
  | [] => pure []
  | a :: as => do let r ← wdAtPat C a; let rs ← wdAtPats C as; pure (r :: rs)
end

/-! ## Groups: the entries before the members are typed -/

/-- Step 1 of section 6 for a chain of variable bindings (a pattern binding is a group by itself:
    one inside a chain is left `unsupported`): an annotated member's type is its
    annotation's (monomorphic in F_b: U' = [], and closed: an annotation whose type has a variable,
    through an alias with a free variable, is left `unsupported`; so is an annotation in a context
    whose explicit variables are ambiguous, which no derivation admits, `newForB`), an unannotated
    one's a fresh variable. -/
def groupEntriesD (C : Ctx) : BValBind → WDM (List (Option (BTy × List BVar) × Ty))
  | .var _ ann _ rest => do
    let e ← match ann with
      | none => do let α ← freshVD; pure ((none : Option (BTy × List BVar)), α)
      | some ty =>
        if (Stat.bTyNames ty).isEmpty && decide (Unambiguous C.U) then
          match elabTy (C.plusU []) ty with
          | some τ => if τ.vars.isEmpty then pure (some (ty, []), τ) else wdUnsupported
          | none => wdFail
        else wdUnsupported
    let es ← match rest with
      | none => pure []
      | some vb => groupEntriesD C vb
    pure (e :: es)
  | .pat _ _ => wdUnsupported

/-! ## Expressions -/

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
    pure (.val VE0 avb)
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

/-- The first index above every fresh variable of the root context: its free variables and the
    variables of its shadowed bindings (so that W's substitution moves none of the context's
    schemes, `ctxRsb (toRS θ) C0 = C0`). -/
def freshAboveD (C0 : Ctx) : Nat :=
  (C0.tyvars ++ veAllVars C0.E.VE).foldl (fun m v => match v with
    | .ty (.fresh k _) => max m (k + 1)
    | .row (.fresh k) => max m (k + 1)
    | _ => m) 0

/-- The rigid variables of a run from the root context: all but W's own. -/
def rigidFromD (n0 : Nat) : RRigid := fun v =>
  match v with
  | .ty (.fresh k _) => decide (k < n0)
  | .row (.fresh k) => decide (k < n0)
  | _ => true

/-- W on an expression in the root context `C0`, the final substitution applied, the result
    checked by step 9's checker. A result with a non-canonical type at a node (a record with a
    label twice: A23, a lacks constraint between two unifications) is a refusal: every canonical
    derivation is an instance of W's result (to be proved, L11), and an instance of a type with a
    repeated label has it too. -/
def inferExpWD (fuel : Nat) (C0 : Ctx) (e : BExp) : WRes :=
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

def wdFuel : Nat := 2 ^ 32


/-! ## Soundness (L10) -/

/-- Soundness of W for F_d: what it returns is a derivation of the phrase that step 9's checker
    accepts, with canonical types at its nodes. -/
theorem inferExpWD_sound {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (h : inferExpWD fuel C0 e = .ok a) :
    checkExp C0 a = true ∧ a.erase = e ∧ ∀ nd ∈ nodesExp C0 [] a, ∀ τ ∈ nd.tys, cnB τ = true := by
  unfold inferExpWD at h
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

end StandardElm.Stat.Complete
