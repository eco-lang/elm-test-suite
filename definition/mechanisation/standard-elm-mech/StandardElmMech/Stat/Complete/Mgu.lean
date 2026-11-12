/-
  A Standard Definition of Elm? Mechanisation: the most general unifier without classes and rows,
  milestone (b) of plan step 11 (section 4: the mgu theorem, parts 1 and 2; lemmas K1 to K3, K7).

  Robinson's unification over step 9's types, with a set of rigid variables (a predicate) that no
  unifier may move. The state is the list of pending equations and the accumulated substitution,
  a binding list `θ` kept idempotent and applied to the pending equations (section 4's (I1)).
  The algorithm binds only flexible type variables of class `any`; a flexible variable of another
  class, and two record types, are outside the fragment and give `unsupported` (milestones (c)
  and (d)); a record against a variable, an arrow or a constructed type is handled (binding or
  clash). The definition is structural on fuel.

  Theorems (for every fuel):
  * `uLoop_ok`, `uLoop_fail`: the invariant (I1) and the solution correspondence (I2) of
    section 4, in the form "S unifies the problem and absorbs θ iff S absorbs θ'" (S absorbs θ
    when S ∘ θ = S);
  * `mgu_ok`: the result unifies, fixes the rigid variables, binds only variables of class any
    (so it respects classes, `mgu_respects` in step 9's terms), is idempotent, and every unifier
    S factors through it as S = S ∘ θ (the factor is S itself, which respects classes, fixes the
    rigid variables and is defined everywhere: no rows);
  * `mgu_fail`: failure means no unifier fixing the rigid variables.
-/
import StandardElmMech.Stat.Complete.FSubst

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-- The rigid variables, as a predicate. -/
abbrev Rigid := TyVar → Bool

abbrev Eqs := List (Ty × Ty)

def FixesR (R : Rigid) (s : FSub) : Prop := ∀ a, R a = true → s a = .var a

def Unifies (s : FSub) (E : Eqs) : Prop := ∀ e ∈ E, sb s e.1 = sb s e.2

/-- `s` absorbs `θ`: `s ∘ θ = s`. -/
def Absorbs (s θ : FSub) : Prop := ∀ a, sb s (θ a) = s a

inductive MOut where
  | ok (θ : Bnd)
  | fail
  | unsupported
  | outOfFuel
  deriving Repr, DecidableEq

/-! ## The algorithm -/

def bindV (a : TyVar) (τ : Ty) (θ : Bnd) : Bnd := (a, τ) :: θ.map (fun p => (p.1, sb (upd a τ) p.2))

def substEqs (a : TyVar) (τ : Ty) (E : Eqs) : Eqs :=
  E.map (fun e => (sb (upd a τ) e.1, sb (upd a τ) e.2))

inductive Step where
  | next (E : Eqs) (θ : Bnd)
  | fail
  | unsupported

/-- Bind the flexible `a` to `τ` (U2 without classes): occurs check, then the binding. -/
def bindStepM (a : TyVar) (τ : Ty) (rest : Eqs) (θ : Bnd) : Step :=
  if a.cls = .any then
    if BVar.ty a ∈ τ.vars then .fail else .next (substEqs a τ rest) (bindV a τ θ)
  else .unsupported

/-- One step on the first equation (U0 to U4, U6; U1 and U2 without classes; U5 unsupported). -/
def uStep (R : Rigid) (θ : Bnd) (l r : Ty) (rest : Eqs) : Step :=
  if l = r then .next rest θ else
  match l, r with
  | .var a, .var b =>
    if !R a && a.cls == .any then bindStepM a (.var b) rest θ
    else if !R b && b.cls == .any then bindStepM b (.var a) rest θ
    else if !R a || !R b then .unsupported
    else .fail
  | .var a, r => if !R a then bindStepM a r rest θ else .fail
  | l, .var b => if !R b then bindStepM b l rest θ else .fail
  | .fn a b, .fn c d => .next ((a, c) :: (b, d) :: rest) θ
  | .con as t, .con bs t' =>
    if t = t' ∧ as.length = bs.length then .next (as.zip bs ++ rest) θ else .fail
  | .record _ _, .record _ _ => .unsupported
  | _, _ => .fail

def uLoop (R : Rigid) : Nat → Eqs → Bnd → MOut
  | 0, _, _ => .outOfFuel
  | _ + 1, [], θ => .ok θ
  | n + 1, (l, r) :: rest, θ =>
    match uStep R θ l r rest with
    | .next E θ' => uLoop R n E θ'
    | .fail => .fail
    | .unsupported => .unsupported

/-- The unifier of a problem, from the empty substitution. -/
def mgu (fuel : Nat) (R : Rigid) (E : Eqs) : MOut := uLoop R fuel E []

/-! ## Equations -/

theorem unifies_nil (s : FSub) : Unifies s [] := fun _ h => by cases h

theorem unifies_cons {s : FSub} {l r : Ty} {E : Eqs} :
    Unifies s ((l, r) :: E) ↔ sb s l = sb s r ∧ Unifies s E := by
  constructor
  · intro h; exact ⟨h _ (.head _), fun e he => h e (.tail _ he)⟩
  · rintro ⟨h1, h2⟩ e he
    cases he with
    | head => exact h1
    | tail _ he => exact h2 e he

theorem unifies_append {s : FSub} {E F : Eqs} : Unifies s (E ++ F) ↔ Unifies s E ∧ Unifies s F := by
  simp only [Unifies, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun ⟨h1, h2⟩ e he => he.elim (h1 e) (h2 e)⟩

theorem unifies_zip {s : FSub} : ∀ {as bs : List Ty}, as.length = bs.length →
    (Unifies s (as.zip bs) ↔ sbList s as = sbList s bs)
  | [], [], _ => by simp [unifies_nil, sbList]
  | a :: as, b :: bs, h => by
    simp only [List.zip_cons_cons, unifies_cons, sbList, List.cons.injEq]
    rw [unifies_zip (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem sbList_length (s : FSub) (l : List Ty) : (sbList s l).length = l.length := by
  rw [sbList_eq]; simp

/-! ## Binding lists -/

theorem find?_some_mem {θ : Bnd} {a : TyVar} {τ : Ty} (h : FMap.find? θ a = some τ) : (a, τ) ∈ θ := by
  induction θ with
  | nil => cases h
  | cons p r ih =>
    obtain ⟨b, u⟩ := p
    simp only [FMap.find?] at h
    split at h
    · rename_i hb; cases h; subst hb; exact .head _
    · exact .tail _ (ih h)

theorem lk_key {θ : Bnd} {a : TyVar} (h : lk θ a ≠ .var a) : ∃ τ, (a, τ) ∈ θ := by
  unfold lk at h
  cases hf : FMap.find? θ a with
  | none => rw [hf] at h; exact absurd rfl h
  | some τ => exact ⟨τ, find?_some_mem hf⟩

theorem lk_bindV {θ : Bnd} {a : TyVar} {τ : Ty} (ha : lk θ a = .var a) :
    lk (bindV a τ θ) = comp (upd a τ) (lk θ) := by
  funext b
  simp only [bindV, lk_cons, comp]
  by_cases hab : a = b
  · subst hab; simp [ha, sb, upd_self]
  · simp only [hab, ↓reduceIte]
    unfold lk
    rw [find?_mapSnd]
    cases FMap.find? θ b with
    | none => simp only [Option.map_none, Option.getD_none, sb]; exact (upd_ne τ (Ne.symm hab)).symm
    | some u => rfl

/-! ## The invariant (I1) -/

/-- (I1) without classes: every key of θ is flexible of class any, θ is idempotent, and θ moves no
    variable of the pending equations. -/
structure Good (R : Rigid) (θ : Bnd) (E : Eqs) : Prop where
  keys : ∀ p ∈ θ, R p.1 = false ∧ p.1.cls = .any
  idem : Idem (lk θ)
  stable : ∀ e ∈ E, ∀ a, (BVar.ty a ∈ e.1.vars ∨ BVar.ty a ∈ e.2.vars) → lk θ a = .var a

theorem Good.dom {R : Rigid} {θ : Bnd} {E : Eqs} (g : Good R θ E) {a : TyVar} (h : lk θ a ≠ .var a) :
    R a = false ∧ a.cls = .any := by
  obtain ⟨τ, hm⟩ := lk_key h; exact g.keys _ hm

theorem Good.fixesR {R : Rigid} {θ : Bnd} {E : Eqs} (g : Good R θ E) : FixesR R (lk θ) := by
  intro a ha
  by_cases h : lk θ a = .var a
  · exact h
  · have := (g.dom h).1; rw [ha] at this; cases this

theorem good_nil (R : Rigid) (E : Eqs) : Good R [] E :=
  ⟨fun _ h => (by cases h), fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The solution correspondence (I2) of one step. -/
def Corr (R : Rigid) (E : Eqs) (θ : Bnd) (E' : Eqs) (θ' : Bnd) : Prop :=
  ∀ s, FixesR R s → (Unifies s E ∧ Absorbs s (lk θ) ↔ Unifies s E' ∧ Absorbs s (lk θ'))

/-! ## The binding step (K2) -/

theorem bind_good {R : Rigid} {θ : Bnd} {a : TyVar} {τ : Ty} {rest : Eqs}
    (hR : R a = false) (hc : a.cls = .any) (hocc : BVar.ty a ∉ τ.vars)
    (ha : lk θ a = .var a) (hτ : ∀ b, BVar.ty b ∈ τ.vars → lk θ b = .var b)
    (hrest : ∀ e ∈ rest, ∀ b, (BVar.ty b ∈ e.1.vars ∨ BVar.ty b ∈ e.2.vars) → lk θ b = .var b)
    (g : Good R θ ((.var a, τ) :: rest)) :
    Good R (bindV a τ θ) (substEqs a τ rest) ∧
    ∀ s, (s a = sb s τ ∧ Unifies s rest ∧ Absorbs s (lk θ) ↔
      Unifies s (substEqs a τ rest) ∧ Absorbs s (lk (bindV a τ θ))) := by
  have hlk := lk_bindV (τ := τ) ha
  -- a variable fixed by θ and different from a is fixed by the new substitution
  have fix' : ∀ c, lk θ c = .var c → c ≠ a → lk (bindV a τ θ) c = .var c := by
    intro c hc hca; rw [hlk]; simp only [comp, hc, sb]; exact upd_ne τ hca
  have hτa : ∀ c, BVar.ty c ∈ τ.vars → c ≠ a := fun c hc e => hocc (e ▸ hc)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [bindV, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact ⟨hR, hc⟩
    · exact g.keys q hq
  · intro b c hcv
    rw [hlk] at hcv; simp only [comp] at hcv
    rcases tyvar_sb_upd hcv with ⟨h1, h2⟩ | h1
    · exact fix' c (g.idem b c h1) h2
    · exact fix' c (hτ c h1) (hτa c h1)
  · intro e he c hcv
    simp only [substEqs, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have key : ∀ σ, (BVar.ty c ∈ σ.vars → lk θ c = .var c) → BVar.ty c ∈ (sb (upd a τ) σ).vars →
        lk (bindV a τ θ) c = .var c := by
      intro σ hσ hm
      rcases tyvar_sb_upd hm with ⟨h1, h2⟩ | h1
      · exact fix' c (hσ h1) h2
      · exact fix' c (hτ c h1) (hτa c h1)
    rcases hcv with h | h
    · exact key _ (fun hm => hrest e0 he0 c (.inl hm)) h
    · exact key _ (fun hm => hrest e0 he0 c (.inr hm)) h
  · intro s
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hcs := comp_upd h1
      refine ⟨?_, ?_⟩
      · intro e he
        simp only [substEqs, List.mem_map] at he
        obtain ⟨e0, he0, rfl⟩ := he
        simp only [sb_sb, hcs]; exact h2 e0 he0
      · intro b; rw [hlk]; simp only [comp, sb_sb, hcs]; exact h3 b
    · rintro ⟨h2, h3⟩
      have h1 : s a = sb s τ := by
        have := h3 a; rw [hlk] at this; simp only [comp, ha, sb, upd_self] at this; exact this.symm
      have hcs := comp_upd h1
      refine ⟨h1, ?_, ?_⟩
      · intro e he
        have := h2 _ (List.mem_map.mpr ⟨e, he, rfl⟩)
        simp only [sb_sb, hcs] at this; exact this
      · intro b; have := h3 b; rw [hlk] at this; simp only [comp, sb_sb, hcs] at this; exact this

/-! ## One step -/

theorem stable_cons {R : Rigid} {θ : Bnd} {l r : Ty} {rest : Eqs} (g : Good R θ ((l, r) :: rest)) :
    (∀ b, BVar.ty b ∈ l.vars → lk θ b = .var b) ∧ (∀ b, BVar.ty b ∈ r.vars → lk θ b = .var b) ∧
    (∀ e ∈ rest, ∀ b, (BVar.ty b ∈ e.1.vars ∨ BVar.ty b ∈ e.2.vars) → lk θ b = .var b) :=
  ⟨fun b h => g.stable _ (.head _) b (.inl h), fun b h => g.stable _ (.head _) b (.inr h),
   fun e he => g.stable e (.tail _ he)⟩

/-- A binding step as a step of the loop, for the equation `a ≐ τ` in either order. -/
theorem bindStep_next {R : Rigid} {θ : Bnd} {a : TyVar} {τ : Ty} {rest E' : Eqs} {θ' : Bnd}
    (hR : R a = false) (ha : lk θ a = .var a) (hτ : ∀ b, BVar.ty b ∈ τ.vars → lk θ b = .var b)
    (hrest : ∀ e ∈ rest, ∀ b, (BVar.ty b ∈ e.1.vars ∨ BVar.ty b ∈ e.2.vars) → lk θ b = .var b)
    (g : Good R θ ((.var a, τ) :: rest))
    (h : bindStepM a τ rest θ = .next E' θ') :
    Good R θ' E' ∧ ∀ s, (s a = sb s τ ∧ Unifies s rest ∧ Absorbs s (lk θ) ↔ Unifies s E' ∧ Absorbs s (lk θ')) := by
  unfold bindStepM at h
  split at h
  · rename_i hc
    split at h
    · cases h
    · rename_i hocc; cases h; exact bind_good hR hc hocc ha hτ hrest g
  · cases h

theorem bindStep_fail_mem {a : TyVar} {τ : Ty} {rest : Eqs} {θ : Bnd} (h : bindStepM a τ rest θ = .fail) :
    BVar.ty a ∈ τ.vars := by
  unfold bindStepM at h
  split at h
  · split at h
    · assumption
    · cases h
  · cases h

theorem good_swap {R : Rigid} {θ : Bnd} {l r : Ty} {rest : Eqs} (g : Good R θ ((l, r) :: rest)) :
    Good R θ ((r, l) :: rest) :=
  ⟨g.keys, g.idem, by
    intro e he b hb
    cases he with
    | head => exact g.stable _ (.head _) b hb.symm
    | tail _ he => exact g.stable e (.tail _ he) b hb⟩

theorem unifies_swap {s : FSub} {l r : Ty} {rest : Eqs} :
    Unifies s ((l, r) :: rest) ↔ Unifies s ((r, l) :: rest) := by
  simp only [unifies_cons]; exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b⟩, fun ⟨a, b⟩ => ⟨a.symm, b⟩⟩

/-- A binding step of the loop for the equation `var a ≐ τ`. -/
theorem bind_case {R : Rigid} {θ : Bnd} {a : TyVar} {τ : Ty} {rest E' : Eqs} {θ' : Bnd}
    (hR : R a = false) (g : Good R θ ((.var a, τ) :: rest)) (h : bindStepM a τ rest θ = .next E' θ') :
    Good R θ' E' ∧ Corr R ((.var a, τ) :: rest) θ E' θ' := by
  obtain ⟨hl, hr, hrest⟩ := stable_cons g
  obtain ⟨g', hc⟩ := bindStep_next hR (hl a (mem_vars_var a)) hr hrest g h
  refine ⟨g', fun s _ => ?_⟩
  rw [← hc s, unifies_cons]
  simp only [sb]
  exact ⟨fun ⟨⟨a1, a2⟩, a3⟩ => ⟨a1, a2, a3⟩, fun ⟨a1, a2, a3⟩ => ⟨⟨a1, a2⟩, a3⟩⟩

theorem bind_case' {R : Rigid} {θ : Bnd} {b : TyVar} {l : Ty} {rest E' : Eqs} {θ' : Bnd}
    (hR : R b = false) (g : Good R θ ((l, .var b) :: rest)) (h : bindStepM b l rest θ = .next E' θ') :
    Good R θ' E' ∧ Corr R ((l, .var b) :: rest) θ E' θ' := by
  obtain ⟨g', hc⟩ := bind_case hR (good_swap g) h
  exact ⟨g', fun s hs => by rw [unifies_swap]; exact hc s hs⟩

theorem uStep_next {R : Rigid} {θ : Bnd} {l r : Ty} {rest E' : Eqs} {θ' : Bnd}
    (g : Good R θ ((l, r) :: rest)) (h : uStep R θ l r rest = .next E' θ') :
    Good R θ' E' ∧ Corr R ((l, r) :: rest) θ E' θ' := by
  unfold uStep at h
  split at h
  · rename_i hlr
    cases h; subst hlr
    refine ⟨⟨g.keys, g.idem, fun e he => g.stable e (.tail _ he)⟩, fun s _ => ?_⟩
    rw [unifies_cons]; exact ⟨fun ⟨⟨_, a⟩, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨⟨rfl, a⟩, b⟩⟩
  · split at h
    · -- var, var
      rename_i a b _
      split at h
      · rename_i hc; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        exact bind_case hc.1 g h
      · split at h
        · rename_i hc; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          exact bind_case' hc.1 g h
        · split at h <;> cases h
    · split at h
      · rename_i hc; simp only [Bool.not_eq_true'] at hc; exact bind_case hc g h
      · cases h
    · split at h
      · rename_i hc; simp only [Bool.not_eq_true'] at hc; exact bind_case' hc g h
      · cases h
    · -- fn, fn
      rename_i a b c d
      cases h
      obtain ⟨hl, hr, hrest⟩ := stable_cons g
      refine ⟨⟨g.keys, g.idem, ?_⟩, fun s _ => ?_⟩
      · intro e he x hx
        simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        · rcases hx with hx | hx
          · exact hl x (by simp [Ty.vars, hx])
          · exact hr x (by simp [Ty.vars, hx])
        · rcases hx with hx | hx
          · exact hl x (by simp [Ty.vars, hx])
          · exact hr x (by simp [Ty.vars, hx])
        · exact hrest e he x hx
      · simp only [unifies_cons, sb, Ty.fn.injEq]
        exact ⟨fun ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ => ⟨⟨a1, a2, a3⟩, a4⟩, fun ⟨⟨a1, a2, a3⟩, a4⟩ => ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩⟩
    · -- con, con
      rename_i as t bs t'
      split at h
      · rename_i hc
        obtain ⟨rfl, hlen⟩ := hc
        cases h
        obtain ⟨hl, hr, hrest⟩ := stable_cons g
        refine ⟨⟨g.keys, g.idem, ?_⟩, fun s _ => ?_⟩
        · intro e he x hx
          rcases List.mem_append.mp he with he | he
          · have hm := List.of_mem_zip he
            rcases hx with hx | hx
            · exact hl x (by
                simp only [Ty.vars]
                exact listVars_of_mem hm.1 hx)
            · exact hr x (by
                simp only [Ty.vars]
                exact listVars_of_mem hm.2 hx)
          · exact hrest e he x hx
        · rw [unifies_append, unifies_zip hlen, unifies_cons]
          simp only [sb, Ty.con.injEq, and_true]
      · cases h
    · cases h
    · cases h
where
  listVars_of_mem {τ : Ty} {l : List Ty} {v : BVar} (hm : τ ∈ l) (hv : v ∈ τ.vars) : v ∈ Ty.listVars l := by
    induction l with
    | nil => cases hm
    | cons x r ih =>
      simp only [Ty.listVars, List.mem_append]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact .inl hv
      · exact .inr (ih hm)

theorem fail_var_left {R : Rigid} {θ : Bnd} {a : TyVar} {r : Ty} {rest : Eqs} (hr : ∀ b, r ≠ .var b)
    (h : (if !R a then bindStepM a r rest θ else .fail) = Step.fail) : ∀ s, FixesR R s → s a ≠ sb s r := by
  intro s hs
  split at h
  · exact occurs_neF s (bindStep_fail_mem h) (hr a)
  · rename_i hc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    rw [hs a hc]
    intro e
    cases r with
    | var b => exact hr b rfl
    | _ => simp [sb] at e

/-- K1, K3, K7: a failing step has no unifier fixing the rigid variables. -/
theorem uStep_fail {R : Rigid} {θ : Bnd} {l r : Ty} {rest : Eqs} (h : uStep R θ l r rest = .fail) :
    ∀ s, FixesR R s → sb s l ≠ sb s r := by
  intro s hs
  unfold uStep at h
  by_cases hlr : l = r
  · simp only [hlr, ↓reduceIte] at h; cases h
  simp only [hlr, ↓reduceIte] at h
  match l, r, h, hlr with
  | .var a, .var b, h, hlr =>
    dsimp only at h
    split at h
    · have hm := bindStep_fail_mem h
      simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hm; subst hm; exact absurd rfl hlr
    · split at h
      · have hm := bindStep_fail_mem h
        simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hm; subst hm; exact absurd rfl hlr
      · split at h
        · cases h
        · rename_i hc
          simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
          simp only [sb, hs a hc.1, hs b hc.2]
          exact hlr
  | .var a, .record ρ tl, h, _ => exact fail_var_left (fun _ e => by cases e) h s hs
  | .var a, .fn x y, h, _ => exact fail_var_left (fun _ e => by cases e) h s hs
  | .var a, .con as t, h, _ => exact fail_var_left (fun _ e => by cases e) h s hs
  | .record ρ tl, .var b, h, _ => exact fun e => fail_var_left (fun _ e => by cases e) h s hs e.symm
  | .fn x y, .var b, h, _ => exact fun e => fail_var_left (fun _ e => by cases e) h s hs e.symm
  | .con as t, .var b, h, _ => exact fun e => fail_var_left (fun _ e => by cases e) h s hs e.symm
  | .fn _ _, .fn _ _, h, _ => cases h
  | .con as t, .con bs t', h, _ =>
    dsimp only at h
    split at h
    · cases h
    · rename_i hc
      simp only [sb, ne_eq, Ty.con.injEq]
      rintro ⟨h1, h2⟩
      apply hc
      refine ⟨h2, ?_⟩
      have := congrArg List.length h1
      simpa [sbList_length] using this
  | .record _ _, .record _ _, h, _ => cases h
  | .record _ _, .fn _ _, _, _ => simp [sb]
  | .record _ _, .con _ _, _, _ => simp [sb]
  | .fn _ _, .record _ _, _, _ => simp [sb]
  | .fn _ _, .con _ _, _, _ => simp [sb]
  | .con _ _, .record _ _, _, _ => simp [sb]
  | .con _ _, .fn _ _, _, _ => simp [sb]

/-! ## The loop -/

theorem uLoop_ok {R : Rigid} : ∀ (n : Nat) (E : Eqs) (θ θ' : Bnd), Good R θ E → uLoop R n E θ = .ok θ' →
    Good R θ' [] ∧ Corr R E θ [] θ'
  | 0, _, _, _, _, h => by cases h
  | n + 1, [], θ, θ', g, h => by
    simp only [uLoop, MOut.ok.injEq] at h; subst h
    exact ⟨g, fun _ _ => Iff.rfl⟩
  | n + 1, (l, r) :: rest, θ, θ', g, h => by
    simp only [uLoop] at h
    split at h
    · rename_i E θ1 hs
      obtain ⟨g1, c1⟩ := uStep_next g hs
      obtain ⟨g2, c2⟩ := uLoop_ok n E θ1 θ' g1 h
      exact ⟨g2, fun s hs => (c1 s hs).trans (c2 s hs)⟩
    · cases h
    · cases h

theorem uLoop_fail {R : Rigid} : ∀ (n : Nat) (E : Eqs) (θ : Bnd), Good R θ E → uLoop R n E θ = .fail →
    ∀ s, FixesR R s → ¬ (Unifies s E ∧ Absorbs s (lk θ))
  | 0, _, _, _, h => by cases h
  | n + 1, [], θ, _, h => by cases h
  | n + 1, (l, r) :: rest, θ, g, h => by
    simp only [uLoop] at h
    split at h
    · rename_i E θ1 hs
      obtain ⟨g1, c1⟩ := uStep_next g hs
      intro s hfx hu
      exact uLoop_fail n E θ1 g1 h s hfx ((c1 s hfx).mp hu)
    · rename_i hs
      intro s hfx ⟨hu, _⟩
      exact uStep_fail hs s hfx (unifies_cons.mp hu).1
    · cases h

/-! ## The mgu theorem (section 4, parts 1 and 2, without classes and rows) -/

theorem absorbs_id (s : FSub) : Absorbs s (lk []) := fun _ => rfl

theorem mgu_ok {fuel : Nat} {R : Rigid} {E : Eqs} {θ : Bnd} (h : mgu fuel R E = .ok θ) :
    Unifies (lk θ) E ∧ FixesR R (lk θ) ∧ (∀ p ∈ θ, R p.1 = false ∧ p.1.cls = .any) ∧
    Idem (lk θ) ∧ ∀ s, FixesR R s → Unifies s E → Absorbs s (lk θ) := by
  obtain ⟨g, c⟩ := uLoop_ok fuel E [] θ (good_nil R E) h
  have habs : Absorbs (lk θ) (lk θ) := fun a => sb_eq_self_iff.mpr (g.idem a)
  refine ⟨((c (lk θ) g.fixesR).mpr ⟨unifies_nil _, habs⟩).1, g.fixesR, g.keys, g.idem, ?_⟩
  intro s hs hu
  exact ((c s hs).mp ⟨hu, absorbs_id s⟩).2

theorem mgu_fail {fuel : Nat} {R : Rigid} {E : Eqs} (h : mgu fuel R E = .fail) :
    ∀ s, FixesR R s → ¬ Unifies s E := fun s hs hu =>
  uLoop_fail fuel E [] (good_nil R E) h s hs ⟨hu, absorbs_id s⟩

/-- The mgu in step 9's terms: it respects classes (every binding is of a variable of class any). -/
theorem mgu_respects {fuel : Nat} {R : Rigid} {E : Eqs} {θ : Bnd} (h : mgu fuel R E = .ok θ) :
    (ofBnd θ).Respects := by
  intro p hp
  have := ((mgu_ok h).2.2.1 p hp).2
  simp only [ofBnd] at hp
  rw [this]; exact .any _

end StandardElm.Stat.Complete
