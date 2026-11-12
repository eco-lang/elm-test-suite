/-
  A Standard Definition of Elm? Mechanisation: algorithm W for fragment F_c (Core phrases with
  let-polymorphism, classes, monomorphic annotations; no records), milestones (b) and (c) of plan
  step 11 (section 6).

  The state is the accumulated substitution `θ` (a binding list, idempotent: MguC.lean's
  `GoodC`) and the counter of fresh variables. Every variable W creates is `fresh n c` with `n`
  at least the first index `n0` above the root context's fresh variables (an integer constant's
  type is a fresh variable of class num, a scheme's bound variable is instantiated with a fresh
  one of its class, and unification refines classes with fresh variables); every other variable
  is rigid (section 1: the root context's free variables, and the explicit variables). A call of
  `unify` runs MguC.lean's loop from the current `θ` and counter on the one equation, with the
  fuel given.

  The annotated phrase is built with the types W chose, not yet substituted; `inferExpW` applies
  the final `θ` to it and then *checks* the result with step 9's checker (and that it erases to
  the phrase). So soundness is by construction (`inferExpW_sound`): whatever W returns is a
  derivation step 9's proved checker accepts. A result W built that the checker refuses would be
  reported as `internal`, never as a refusal.

  Outcomes: `ok`, `fail` (a genuine refusal: a unification failure, an unbound identifier, a
  constant or constructor pattern no derivation can type), `unsupported` (outside F_c: a scheme
  quantifying a row variable, a record, an annotation with type variables; also two shapes no
  derivation types, left `unsupported` rather than refuted: an annotation in a context with
  ambiguous explicit variables, and a pattern binding one of whose variables names a constructor
  of the context), `outOfFuel`, `internal`.
-/
import StandardElmMech.Stat.Complete.MguCVars
import StandardElmMech.SyntaxDecEq
import StandardElmMech.Stat.CheckSound

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind SLit)

/-! ## Substitution on annotated phrases (L1) -/

def sbScheme (s : FSub) (σ : Scheme) : Scheme := ⟨σ.bound, sb s σ.body⟩

def sbVE (s : FSub) (VE : ValEnv) : ValEnv := VE.map fun p => (p.1, (sbScheme s p.2.1, p.2.2))

def ctxSb (s : FSub) (C : Ctx) : Ctx := { C with E := { C.E with VE := sbVE s C.E.VE } }

def sbOpt (s : FSub) : Option Ty → Option Ty
  | none => none
  | some τ => some (sb s τ)

mutual
def sbAtPat (s : FSub) : AAtPat → AAtPat
  | .wild τ => .wild (sb s τ)
  | .scon sc τ => .scon sc (sb s τ)
  | .var x τ => .var x (sb s τ)
  | .con lc inst τ => .con lc (sbList s inst) (sb s τ)
  | .unit => .unit
  | .tuple p1 p2 p3 => .tuple (sbPat s p1) (sbPat s p2) (sbPatOpt s p3)
  | .nil τ => .nil (sb s τ)
  | .record row τ => .record (sbPatRowOpt s row) (sb s τ)
  | .paren p => .paren (sbPat s p)
def sbPatRow (s : FSub) : APatRow → APatRow
  | .field l τ rest => .field l (sb s τ) (sbPatRowOpt s rest)
def sbPatRowOpt (s : FSub) : Option APatRow → Option APatRow
  | none => none
  | some r => some (sbPatRow s r)
def sbPat (s : FSub) : APat → APat
  | .atpat a => .atpat (sbAtPat s a)
  | .con lc inst args τ => .con lc (sbList s inst) (sbAtPats s args) (sb s τ)
  | .cons p1 p2 => .cons (sbPat s p1) (sbPat s p2)
  | .as p x => .as (sbPat s p) x
def sbPatOpt (s : FSub) : Option APat → Option APat
  | none => none
  | some p => some (sbPat s p)
def sbAtPats (s : FSub) : List AAtPat → List AAtPat
  | [] => []
  | a :: as => sbAtPat s a :: sbAtPats s as
end

mutual
def sbAtExp (s : FSub) : AAtExp → AAtExp
  | .scon sc τ => .scon sc (sb s τ)
  | .var lv inst τ => .var lv (sbList s inst) (sb s τ)
  | .con lc inst τ => .con lc (sbList s inst) (sb s τ)
  | .op o inst τ => .op o (sbList s inst) (sb s τ)
  | .unit => .unit
  | .tuple e1 e2 e3 => .tuple (sbExp s e1) (sbExp s e2) (sbExpOpt s e3)
  | .nil τ => .nil (sb s τ)
  | .record row => .record (sbExpRowOpt s row)
  | .update x inst τ row => .update x (sbList s inst) (sb s τ) (sbExpRow s row)
  | .letE d e => .letE (sbDec s d) (sbExp s e)
  | .paren e => .paren (sbExp s e)
def sbExpRow (s : FSub) : AExpRow → AExpRow
  | .field l e rest => .field l (sbExp s e) (sbExpRowOpt s rest)
def sbExpRowOpt (s : FSub) : Option AExpRow → Option AExpRow
  | none => none
  | some r => some (sbExpRow s r)
def sbExp (s : FSub) : AExp → AExp
  | .atexp a => .atexp (sbAtExp s a)
  | .app e a => .app (sbExp s e) (sbAtExp s a)
  | .lam p e => .lam (sbAtPat s p) (sbExp s e)
  | .caseE e m => .caseE (sbExp s e) (sbMatch s m)
def sbExpOpt (s : FSub) : Option AExp → Option AExp
  | none => none
  | some e => some (sbExp s e)
def sbMatch (s : FSub) : AMatch → AMatch
  | .mk mr rest => .mk (sbMRule s mr) (sbMatchOpt s rest)
def sbMatchOpt (s : FSub) : Option AMatch → Option AMatch
  | none => none
  | some m => some (sbMatch s m)
def sbMRule (s : FSub) : AMRule → AMRule
  | .mk p e => .mk (sbPat s p) (sbExp s e)
def sbDec (s : FSub) : ADec → ADec
  | .val VE vb => .val (sbVE s VE) (sbValBind s vb)
def sbValBind (s : FSub) : AValBind → AValBind
  | .var x ann τ e rest => .var x ann (sb s τ) (sbExp s e) (sbValBindOpt s rest)
  | .pat p e => .pat (sbAtPat s p) (sbExp s e)
def sbValBindOpt (s : FSub) : Option AValBind → Option AValBind
  | none => none
  | some vb => some (sbValBind s vb)
end

/-! ## The state and the monad -/

structure WSt where
  θ : Bnd
  n : Nat
  deriving Repr

inductive WOut (α : Type) where
  | ok (a : α) (st : WSt)
  | fail
  | unsupported
  | outOfFuel

def WM (α : Type) := WSt → WOut α

def WM.bind {α β : Type} (m : WM α) (f : α → WM β) : WM β := fun st =>
  match m st with
  | .ok a st' => f a st'
  | .fail => .fail
  | .unsupported => .unsupported
  | .outOfFuel => .outOfFuel

instance : Monad WM where
  pure a := fun st => .ok a st
  bind := WM.bind

def wFail {α : Type} : WM α := fun _ => .fail
def wUnsupported {α : Type} : WM α := fun _ => .unsupported

/-- A fresh flexible variable of class any. -/
def freshV : WM Ty := fun st => .ok (.var (.fresh st.n .any)) { st with n := st.n + 1 }

/-- A fresh flexible variable of class `c`. -/
def freshC (c : Cls) : WM Ty := fun st => .ok (.var (.fresh st.n c)) { st with n := st.n + 1 }

def getθ : WM Bnd := fun st => .ok st.θ st

/-- unify (τ ≐ τ'): MguC.lean's loop from the current substitution and counter. -/
def unifyW (fuel : Nat) (R : Rigid) (τ1 τ2 : Ty) : WM Unit := fun st =>
  match cLoop R fuel [(sb (lk st.θ) τ1, sb (lk st.θ) τ2)] st.θ st.n with
  | .ok θ' n' => .ok () ⟨θ', n'⟩
  | .fail => .fail
  | .unsupported => .unsupported
  | .outOfFuel => .outOfFuel

/-- Fresh variables for the bound variables of a scheme, each of the class of the bound one (a
    bound row variable: records, milestone (d)). -/
def instVars : List BVar → WM (List Ty)
  | [] => pure []
  | .ty a :: rest => do
    let t ← freshC a.cls
    let ts ← instVars rest
    pure (t :: ts)
  | .row _ :: _ => wUnsupported

/-- The most general instance of a scheme: its instance list and type. -/
def instantiate (σ : Scheme) : WM (List Ty × Ty) := do
  let ts ← instVars σ.bound
  match bindSubst σ.bound ts with
  | some S =>
    match S.apply σ.body with
    | some τ => pure (ts, τ)
    | none => wUnsupported
  | none => wUnsupported

/-- Peel `k` argument types off an arrow chain. -/
def peel : Nat → Ty → Option (List Ty × Ty)
  | 0, τ => some ([], τ)
  | k + 1, .fn a b =>
    match peel k b with
    | some (as, r) => some (a :: as, r)
    | none => none
  | _ + 1, _ => none

/-- Why peeling stopped short: a constructed type (no instance can be an arrow) or a record is a
    genuine failure; a variable is not (an instance may substitute an arrow). -/
def peelStuckVar : Nat → Ty → Bool
  | 0, _ => false
  | k + 1, .fn _ b => peelStuckVar k b
  | _ + 1, .var _ => true
  | _ + 1, _ => false

/-! ## Patterns -/

section
variable (fuel : Nat) (R : Rigid)

/-- Unify each argument pattern's type with the constructor's argument type. -/
def unifyArgs : List Ty → List Ty → WM Unit
  | [], [] => pure ()
  | t :: ts, u :: us => do unifyW fuel R t u; unifyArgs ts us
  | _, _ => wUnsupported

mutual
def wAtPat (C : Ctx) : BAtPat → WM (Ty × AAtPat)
  | .wild => do let α ← freshV; pure (α, .wild α)
  | .scon sc =>
    match sc with
    | .int _ => pure (tIntTy, .scon sc tIntTy)
    | .char _ => pure (tCharTy, .scon sc tCharTy)
    | .str _ => pure (tStringTy, .scon sc tStringTy)
    | .float _ _ => wFail
  | .var x => do let α ← freshV; pure (α, .var x α)
  | .con lc =>
    match C.lookupVal lc with
    | some (σ, .c) => do
      let (ts, τ) ← instantiate σ
      match τ with
      | .con _ _ => pure (τ, .con lc ts τ)
      | .var _ => wUnsupported
      | _ => wFail
    | some (_, .v) => wFail
    | none => wFail
  | .unit => pure (tUnitTy, .unit)
  | .tuple p1 p2 p3 => do
    let (τ1, a1) ← wPat C p1
    let (τ2, a2) ← wPat C p2
    let (τ3, a3) ← wPatOpt C p3
    pure (tupleTy τ1 τ2 τ3, .tuple a1 a2 a3)
  | .nil => do let α ← freshV; pure (listTy α, .nil (listTy α))
  | .record _ => wUnsupported
  | .paren p => do let (τ, a) ← wPat C p; pure (τ, .paren a)
def wPat (C : Ctx) : BPat → WM (Ty × APat)
  | .atpat a => do let (τ, a') ← wAtPat C a; pure (τ, .atpat a')
  | .con lc args =>
    match C.lookupVal lc with
    | some (σ, .c) => do
      let (ts, τb) ← instantiate σ
      match peel args.length τb with
      | some (τs, .con us t) => do
        let ps ← wAtPats C args
        unifyArgs fuel R (ps.map (·.1)) τs
        pure (.con us t, .con lc ts (ps.map (·.2)) (.con us t))
      | some (_, .var _) => wUnsupported
      | some (_, _) => wFail
      | none => if peelStuckVar args.length τb then wUnsupported else wFail
    | some (_, .v) => wFail
    | none => wFail
  | .cons p1 p2 => do
    let (τ1, a1) ← wPat C p1
    let (τ2, a2) ← wPat C p2
    unifyW fuel R τ2 (listTy τ1)
    pure (listTy τ1, .cons a1 a2)
  | .as p x => do let (τ, a) ← wPat C p; pure (τ, .as a x)
def wPatOpt (C : Ctx) : Option BPat → WM (Option Ty × Option APat)
  | none => pure (none, none)
  | some p => do let (τ, a) ← wPat C p; pure (some τ, some a)
def wAtPats (C : Ctx) : List BAtPat → WM (List (Ty × AAtPat))
  | [] => pure []
  | a :: as => do let r ← wAtPat C a; let rs ← wAtPats C as; pure (r :: rs)
end

/-- `x`, unqualified, names a constructor in `C`. A pattern binding none of whose variables does
    is checked in the context its variables extend (`r:s-valbind-pat`) as in `C`; W leaves the
    others `unsupported` (no derivation types them: a variable shadowing a constructor of the same
    pattern makes the constructor's lookup find a variable). -/
def conBound (C : Ctx) (x : String) : Bool :=
  match C.lookupVal ⟨none, x⟩ with
  | some (_, .c) => true
  | _ => false

/-! ## Groups: the entries before the members are typed -/

/-- Step 1 of section 6 for a chain of variable bindings (a pattern binding is a group by itself:
    one inside a chain is left `unsupported`): an annotated member's type is its
    annotation's (monomorphic in F_b: U' = [], and closed: an annotation whose type has a variable,
    through an alias with a free variable, is left `unsupported`; so is an annotation in a context
    whose explicit variables are ambiguous, which no derivation admits, `newForB`), an unannotated
    one's a fresh variable. -/
def groupEntries (C : Ctx) : BValBind → WM (List (Option (BTy × List BVar) × Ty))
  | .var _ ann _ rest => do
    let e ← match ann with
      | none => do let α ← freshV; pure ((none : Option (BTy × List BVar)), α)
      | some ty =>
        if (Stat.bTyNames ty).isEmpty && decide (Unambiguous C.U) then
          match elabTy (C.plusU []) ty with
          | some τ => if τ.vars.isEmpty then pure (some (ty, []), τ) else wUnsupported
          | none => wFail
        else wUnsupported
    let es ← match rest with
      | none => pure []
      | some vb => groupEntries C vb
    pure (e :: es)
  | .pat _ _ => wUnsupported

/-- The value environment of a chain of variable bindings with these entries (as `AValBind.ve`). -/
def groupVE : BValBind → List (Option (BTy × List BVar) × Ty) → ValEnv
  | .var x _ _ rest, (ann, τ) :: es =>
    FMap.modify [(x, (if ann.isSome then annScheme (annU ann) τ else mono τ, .v))]
      (match rest with
       | none => []
       | some vb => groupVE vb es)
  | _, _ => []

/-! ## Expressions -/

mutual
def wAtExp (C : Ctx) : BAtExp → WM (Ty × AAtExp)
  | .scon sc =>
    match sc with
    | .int _ => do let γ ← freshC .num; pure (γ, .scon sc γ)
    | .float _ _ => pure (tFloatTy, .scon sc tFloatTy)
    | .char _ => pure (tCharTy, .scon sc tCharTy)
    | .str _ => pure (tStringTy, .scon sc tStringTy)
  | .var lv =>
    match C.lookupVal lv with
    | some (σ, _) => do let (ts, τ) ← instantiate σ; pure (τ, .var lv ts τ)
    | none => wFail
  | .con lc =>
    match C.lookupVal lc with
    | some (σ, _) => do let (ts, τ) ← instantiate σ; pure (τ, .con lc ts τ)
    | none => wFail
  | .op o =>
    match OTstat o with
    | some (σ, _) => do let (ts, τ) ← instantiate σ; pure (τ, .op o ts τ)
    | none => wFail
  | .unit => pure (tUnitTy, .unit)
  | .tuple e1 e2 e3 => do
    let (τ1, a1) ← wExp C e1
    let (τ2, a2) ← wExp C e2
    let (τ3, a3) ← wExpOpt C e3
    pure (tupleTy τ1 τ2 τ3, .tuple a1 a2 a3)
  | .nil => do let α ← freshV; pure (listTy α, .nil (listTy α))
  | .record _ => wUnsupported
  | .update _ _ => wUnsupported
  | .letE d e => do
    let ad ← wDec C d
    let θ ← getθ
    let VEc := closGroup (ctxSb (lk θ) C).tyvars (sbVE (lk θ) (match ad with | .val VE _ => VE))
    let (τ, ae) ← wExp (C.plusVE VEc) e
    pure (τ, .letE ad ae)
  | .paren e => do let (τ, a) ← wExp C e; pure (τ, .paren a)
def wExp (C : Ctx) : BExp → WM (Ty × AExp)
  | .atexp a => do let (τ, a') ← wAtExp C a; pure (τ, .atexp a')
  | .app e a => do
    let (τ1, ae) ← wExp C e
    let (τ2, aa) ← wAtExp C a
    let β ← freshV
    unifyW fuel R τ1 (.fn τ2 β)
    pure (β, .app ae aa)
  | .lam p e => do
    let (τp, ap) ← wAtPat fuel R C p
    let (τe, ae) ← wExp (C.plusVE ap.ve) e
    pure (.fn τp τe, .lam ap ae)
  | .caseE e m => do
    let (τe, ae) ← wExp C e
    let (τm, am) ← wMatch C m
    let β ← freshV
    unifyW fuel R τm (.fn τe β)
    pure (β, .caseE ae am)
def wExpOpt (C : Ctx) : Option BExp → WM (Option Ty × Option AExp)
  | none => pure (none, none)
  | some e => do let (τ, a) ← wExp C e; pure (some τ, some a)
def wMatch (C : Ctx) : BMatch → WM (Ty × AMatch)
  | .mk mr rest => do
    let (τ, amr) ← wMRule C mr
    let ar ← wMatchOpt C τ rest
    pure (τ, .mk amr ar)
def wMatchOpt (C : Ctx) (τ : Ty) : Option BMatch → WM (Option AMatch)
  | none => pure none
  | some m => do
    let (τm, am) ← wMatch C m
    unifyW fuel R τm τ
    pure (some am)
def wMRule (C : Ctx) : BMRule → WM (Ty × AMRule)
  | .mk p e => do
    let (τp, ap) ← wPat fuel R C p
    let (τe, ae) ← wExp (C.plusVE ap.ve) e
    pure (.fn τp τe, .mk ap ae)
def wDec (C : Ctx) : BDec → WM ADec
  | .val (.pat p e) => do
    let (τp, ap) ← wAtPat fuel R C p
    let VE0 := ap.ve
    if VE0.all (fun q => !conBound C q.1) then
      let (τe, ae) ← wExp (C.plusVE VE0) e
      unifyW fuel R τe τp
      pure (.val VE0 (.pat ap ae))
    else wUnsupported
  | .val (.var x ann e rest) => do
    let es ← groupEntries C (.var x ann e rest)
    let VE0 := groupVE (.var x ann e rest) es
    let avb ← wMembers (C.plusVE VE0) (.var x ann e rest) es
    pure (.val VE0 avb)
def wMembers (Cg : Ctx) : BValBind → List (Option (BTy × List BVar) × Ty) → WM AValBind
  | .var x _ e rest, (ann, τx) :: es => do
    let (τe, ae) ← wExp (Cg.plusU (annU ann)) e
    unifyW fuel R τe τx
    let ar ← wMembersOpt Cg rest es
    pure (.var x ann τx ae ar)
  | _, _ => wUnsupported
def wMembersOpt (Cg : Ctx) : Option BValBind → List (Option (BTy × List BVar) × Ty) → WM (Option AValBind)
  | none, _ => pure none
  | some vb, es => do let a ← wMembers Cg vb es; pure (some a)
end

end

/-! ## The root -/

/-- The variables of the bodies of a value environment's schemes, shadowed bindings included. -/
def veAllVars (VE : ValEnv) : List BVar := VE.flatMap fun p => p.2.1.body.vars

/-- The first index above every fresh variable of the root context: its free variables and the
    variables of its shadowed bindings (so that W's substitution moves none of the context's
    schemes, `ctxSb (lk θ) C0 = C0`). -/
def freshAbove (C0 : Ctx) : Nat :=
  (C0.tyvars ++ veAllVars C0.E.VE).foldl (fun m v => match v with
    | .ty (.fresh k _) => max m (k + 1)
    | _ => m) 0

/-- The rigid variables of a run from the root context: all but W's own. -/
def rigidFrom (n0 : Nat) : Rigid := fun a =>
  match a with
  | .fresh k _ => decide (k < n0)
  | _ => true

inductive WRes where
  | ok (a : AExp)
  | fail
  | unsupported
  | outOfFuel
  | internal

def WRes.isFail : WRes → Bool
  | .fail => true
  | _ => false

def WRes.isOk : WRes → Bool
  | .ok _ => true
  | _ => false

/-- W on an expression in the root context `C0`, the final substitution applied, the result
    checked by step 9's checker. -/
def inferExpW (fuel : Nat) (C0 : Ctx) (e : BExp) : WRes :=
  let n0 := freshAbove C0
  match wExp fuel (rigidFrom n0) C0 e ⟨[], n0⟩ with
  | .ok (_, a) st =>
    let af := sbExp (lk st.θ) a
    if checkExp C0 af && decide (af.erase = e) then .ok af else .internal
  | .fail => .fail
  | .unsupported => .unsupported
  | .outOfFuel => .outOfFuel

def wFuel : Nat := 2 ^ 32

/-! ## Soundness (L10) -/

/-- Soundness of W: what it returns is a derivation of the phrase that step 9's checker accepts
    (so `ElExp C0 e a.ty`, by `checkExp_sound`). -/
theorem inferExpW_sound {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (h : inferExpW fuel C0 e = .ok a) :
    checkExp C0 a = true ∧ a.erase = e := by
  unfold inferExpW at h
  dsimp only at h
  split at h
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc
    · cases h
  · cases h
  · cases h
  · cases h

theorem inferExpW_elab {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (h : inferExpW fuel C0 e = .ok a) :
    ElExp C0 e a.ty := by
  obtain ⟨hc, he⟩ := inferExpW_sound h
  have := checkExp_sound C0 a hc
  rw [he] at this; exact this

end StandardElm.Stat.Complete
