/-
  A Standard Definition of Elm? Mechanisation: which variables the unification of MguC.lean binds
  and introduces (milestone (c) of plan step 11): every step either keeps the substitution and
  shrinks the variables of the equations, or binds a variable of the equations to a type whose
  variables are variables of the equations or new (`uStepC_shape`). Hence (`cLoop_inv`) a
  property of the variables of the equations and of the new variables is inherited by every
  variable the loop binds and by the variables of its images: what W needs for "types W builds"
  (`OkT`) and for "unify moves only the variables of its equation" (`Moves` in WSoundBase.lean).
-/
import StandardElmMech.Stat.Complete.MguCLoop

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-- All the variables of the equations, type and row. -/
def bvars (E : Eqs) : List BVar := E.flatMap fun e => e.1.vars ++ e.2.vars

theorem mem_bvars {v : BVar} {E : Eqs} : v ∈ bvars E ↔ ∃ e ∈ E, v ∈ e.1.vars ∨ v ∈ e.2.vars := by
  simp [bvars]

theorem bvars_cons {l r : Ty} {E : Eqs} {v : BVar} : v ∈ bvars ((l, r) :: E) ↔ v ∈ l.vars ∨ v ∈ r.vars ∨ v ∈ bvars E := by
  simp [bvars, or_assoc]

theorem evars_of_bvars {a : TyVar} {E : Eqs} : a ∈ evars E ↔ BVar.ty a ∈ bvars E := by
  rw [mem_evars, mem_bvars]

theorem zip_bvars : ∀ (as bs : List Ty) (v : BVar), v ∈ bvars (as.zip bs) → v ∈ Ty.listVars as ∨ v ∈ Ty.listVars bs
  | [], _, _, h => by simp [bvars] at h
  | _ :: _, [], _, h => by simp [bvars] at h
  | x :: xs, y :: ys, v, h => by
    simp only [List.zip_cons_cons, bvars_cons] at h
    simp only [Ty.listVars, List.mem_append]
    rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · rcases zip_bvars xs ys v h with h | h
      · exact .inl (.inr h)
      · exact .inr (.inr h)

theorem substEqs_bvars {a : TyVar} {τ : Ty} {rest : Eqs} {v : BVar} (hv : v ∈ bvars (substEqs a τ rest)) :
    v ∈ bvars rest ∨ v ∈ τ.vars := by
  obtain ⟨e, he, hve⟩ := mem_bvars.mp hv
  simp only [substEqs, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  have key : ∀ σ, v ∈ (sb (upd a τ) σ).vars → v ∈ σ.vars ∨ v ∈ τ.vars := fun σ h => by
    rcases vars_sb _ σ v h with ⟨_, rfl, h'⟩ | ⟨c, hc, h'⟩
    · exact .inl h'
    · by_cases e : c = a
      · subst e; rw [upd_self] at h'; exact .inr h'
      · rw [upd_ne τ e] at h'; simp only [Ty.vars, List.mem_singleton] at h'; subst h'; exact .inl hc
  rcases hve with h | h
  · rcases key _ h with h | h
    · exact .inl (mem_bvars.mpr ⟨e0, he0, .inl h⟩)
    · exact .inr h
  · rcases key _ h with h | h
    · exact .inl (mem_bvars.mpr ⟨e0, he0, .inr h⟩)
    · exact .inr h

/-- The shape of a step. -/
theorem uStepC_shape {R : Rigid} {n : Nat} {θ : Bnd} {l r : Ty} {rest E' : Eqs} {θ' : Bnd} {n' : Nat}
    (g : GoodC R n θ ((l, r) :: rest)) (h : uStepC R θ n l r rest = .next E' θ' n') :
    n ≤ n' ∧
    ((θ' = θ ∧ ∀ v, v ∈ bvars E' → v ∈ bvars ((l, r) :: rest)) ∨
     ∃ a τ rest', lk θ a = .var a ∧ BVar.ty a ∈ bvars ((l, r) :: rest) ∧
       (∀ v, v ∈ τ.vars → v ∈ bvars ((l, r) :: rest) ∨ ∃ b, v = .ty b ∧ b.isNew n = true) ∧
       (∀ v, v ∈ bvars rest' → v ∈ bvars ((l, r) :: rest)) ∧ E' = substEqs a τ rest' ∧ θ' = bindV a τ θ) := by
  have hn := (uStepC_next g h).2.1
  refine ⟨hn, ?_⟩
  have hrest : ∀ v, v ∈ bvars rest → v ∈ bvars ((l, r) :: rest) := fun v hv => bvars_cons.mpr (.inr (.inr hv))
  have hl : ∀ v, v ∈ l.vars → v ∈ bvars ((l, r) :: rest) := fun v hv => bvars_cons.mpr (.inl hv)
  have hr : ∀ v, v ∈ r.vars → v ∈ bvars ((l, r) :: rest) := fun v hv => bvars_cons.mpr (.inr (.inl hv))
  have stl : ∀ b, BVar.ty b ∈ l.vars → lk θ b = .var b := fun b h => g.stable _ (.head _) b (.inl h)
  have str : ∀ b, BVar.ty b ∈ r.vars → lk θ b = .var b := fun b h => g.stable _ (.head _) b (.inr h)
  have hγ : ∀ m v, v ∈ (Ty.var (.fresh n m)).vars → v ∈ bvars ((l, r) :: rest) ∨
      ∃ b, v = .ty b ∧ b.isNew n = true :=
    fun m v hv => by simp [Ty.vars] at hv; subst hv; exact .inr ⟨_, rfl, isNew_fresh_self n m⟩
  have hall : ∀ v, v ∈ bvars ((l, r) :: rest) → v ∈ bvars ((l, r) :: rest) := fun _ h => h
  -- (U2) for a variable against a non-variable
  have vs : ∀ {a : TyVar} {τ : Ty} {cur : Eqs}, cur = (l, r) :: rest → lk θ a = .var a →
      BVar.ty a ∈ bvars cur → (∀ v, v ∈ τ.vars → v ∈ bvars cur) →
      (∀ b, BVar.ty b ∈ τ.vars → lk θ b = .var b) →
      varStepC R a τ cur rest θ n = .next E' θ' n' →
      ∃ a τ rest', lk θ a = .var a ∧ BVar.ty a ∈ bvars ((l, r) :: rest) ∧
        (∀ v, v ∈ τ.vars → v ∈ bvars ((l, r) :: rest) ∨ ∃ b, v = .ty b ∧ b.isNew n = true) ∧
        (∀ v, v ∈ bvars rest' → v ∈ bvars ((l, r) :: rest)) ∧ E' = substEqs a τ rest' ∧ θ' = bindV a τ θ := by
    intro a τ cur hcur ha haE hτ hτs h
    subst hcur
    unfold varStepC at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ps hps
        split at h
        · cases h
        · cases h; exact ⟨a, τ, rest, ha, haE, fun v hv => .inl (hτ v hv), hrest, rfl, rfl⟩
        · rename_i b m ht
          cases h
          obtain ⟨k, hk, -, -, -⟩ := refineTarget_some ht
          have hbτ := reqC_vars _ _ _ hps _ hk
          exact ⟨b, _, _, hτs b hbτ, hτ _ hbτ, hγ m, hall, rfl, rfl⟩
  unfold uStepC at h
  split at h
  · cases h; exact .inl ⟨rfl, hrest⟩
  · split at h
    · rename_i a b _
      have ha := hl _ (mem_vars_var a)
      have hb := hr _ (mem_vars_var b)
      have sa := stl a (mem_vars_var a)
      have sb' := str b (mem_vars_var b)
      have vb : ∀ v, v ∈ (Ty.var b).vars → v ∈ bvars ((Ty.var a, Ty.var b) :: rest) ∨
          ∃ c, v = .ty c ∧ c.isNew n = true := fun v hv => .inl (hr v hv)
      have va : ∀ v, v ∈ (Ty.var a).vars → v ∈ bvars ((Ty.var a, Ty.var b) :: rest) ∨
          ∃ c, v = .ty c ∧ c.isNew n = true := fun v hv => .inl (hl v hv)
      split at h
      · split at h
        · cases h
        · split at h
          · cases h; exact .inr ⟨a, _, rest, sa, ha, vb, hrest, rfl, rfl⟩
          · split at h
            · cases h; exact .inr ⟨b, _, rest, sb', hb, va, hrest, rfl, rfl⟩
            · cases h; exact .inr ⟨a, _, _, sa, ha, hγ _, hall, rfl, rfl⟩
      · split at h
        · split at h
          · cases h; exact .inr ⟨a, _, rest, sa, ha, vb, hrest, rfl, rfl⟩
          · cases h
        · split at h
          · split at h
            · cases h; exact .inr ⟨b, _, rest, sb', hb, va, hrest, rfl, rfl⟩
            · cases h
          · cases h
    · rename_i r' a _ _
      split at h
      · exact .inr (vs rfl (stl a (mem_vars_var a)) (hl _ (mem_vars_var a)) hr str h)
      · cases h
    · rename_i l' b _ _
      split at h
      · exact .inr (vs rfl (str b (mem_vars_var b)) (hr _ (mem_vars_var b)) hl stl h)
      · cases h
    · cases h
      refine .inl ⟨rfl, fun v hv => ?_⟩
      simp only [bvars_cons] at hv
      rcases hv with h | h | h | h | h
      · exact hl v (by simp [Ty.vars, h])
      · exact hr v (by simp [Ty.vars, h])
      · exact hl v (by simp [Ty.vars, h])
      · exact hr v (by simp [Ty.vars, h])
      · exact hrest v h
    · split at h
      · rename_i as t bs t' _ _
        cases h
        refine .inl ⟨rfl, fun v hv => ?_⟩
        rcases (mem_bvars.mp hv) with ⟨e, he, hve⟩
        rcases List.mem_append.mp he with he | he
        · rcases zip_bvars as bs v (mem_bvars.mpr ⟨e, he, hve⟩) with h | h
          · exact hl v (by simpa [Ty.vars] using h)
          · exact hr v (by simpa [Ty.vars] using h)
        · exact hrest v (mem_bvars.mpr ⟨e, he, hve⟩)
      · cases h
    · cases h
    · cases h

/-- Every variable `θ` binds, among those `Q` selects, and every variable of its image, has `P`. -/
def InvQP (Q P : TyVar → Prop) (θ : Bnd) : Prop :=
  ∀ d, Q d → lk θ d ≠ .var d → P d ∧ ∀ b, BVar.ty b ∈ (lk θ d).vars → P b

theorem invQP_bind {Q P : TyVar → Prop} {θ : Bnd} {a : TyVar} {τ : Ty} (hinv : InvQP Q P θ)
    (ha : lk θ a = .var a) (hPa : P a) (hτ : ∀ b, BVar.ty b ∈ τ.vars → P b) : InvQP Q P (bindV a τ θ) := by
  intro d hQ hd
  rw [lk_bindV ha] at hd ⊢
  simp only [comp] at hd ⊢
  by_cases e : lk θ d = .var d
  · rw [e] at hd ⊢
    simp only [sb] at hd ⊢
    by_cases hda : d = a
    · subst hda; rw [upd_self]; exact ⟨hPa, hτ⟩
    · rw [upd_ne τ hda] at hd; exact absurd rfl hd
  · obtain ⟨h1, h2⟩ := hinv d hQ e
    refine ⟨h1, fun b hb => ?_⟩
    rcases tyvar_sb_upd hb with ⟨h3, _⟩ | h3
    · exact h2 b h3
    · exact hτ b h3

theorem cLoop_inv {R : Rigid} {Q P : TyVar → Prop} : ∀ (fuel : Nat) (E : Eqs) (θ : Bnd) (n : Nat) (θ' : Bnd) (n' : Nat),
    GoodC R n θ E → (∀ b, BVar.ty b ∈ bvars E → P b) → (∀ b, b.isNew n = true → P b) → InvQP Q P θ →
    cLoop R fuel E θ n = .ok θ' n' → InvQP Q P θ'
  | 0, _, _, _, _, _, _, _, _, _, h => by cases h
  | f + 1, [], θ, n, θ', n', _, _, _, hi, h => by
    simp only [cLoop, COut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hi
  | f + 1, (l, r) :: rest, θ, n, θ', n', g, hE, hN, hi, h => by
    simp only [cLoop] at h
    split at h
    · rename_i E1 θ1 n1 hs
      have g1 := (uStepC_next g hs).1
      obtain ⟨hn, hsh⟩ := uStepC_shape g hs
      have hN1 : ∀ b, b.isNew n1 = true → P b := fun b hb => hN b (by
        cases e : b.isNew n
        · rw [isNew_mono hn e] at hb; cases hb
        · rfl)
      rcases hsh with ⟨rfl, hsub⟩ | ⟨a, τ, rest', ha, haE, hτ, hr', rfl, rfl⟩
      · exact cLoop_inv f E1 _ n1 θ' n' g1 (fun b hb => hE b (hsub _ hb)) hN1 hi h
      · have hτP : ∀ b, BVar.ty b ∈ τ.vars → P b := fun b hb => by
          rcases hτ _ hb with h' | ⟨c, e, h'⟩
          · exact hE b h'
          · injection e with e; subst e; exact hN _ h'
        refine cLoop_inv f _ _ n1 θ' n' g1 (fun b hb => ?_) hN1 (invQP_bind hi ha (hE a haE) hτP) h
        rcases substEqs_bvars hb with h1 | h1
        · exact hE b (hr' _ h1)
        · exact hτP b h1
    · cases h
    · cases h

/-- Every entry of `θ` has its key and the variables of its value in `P`. -/
def EntP (P : BVar → Prop) (θ : Bnd) : Prop := ∀ p ∈ θ, P (.ty p.1) ∧ ∀ v ∈ p.2.vars, P v

theorem entP_bind {P : BVar → Prop} {θ : Bnd} {a : TyVar} {τ : Ty} (hθ : EntP P θ) (ha : P (.ty a))
    (hτ : ∀ v ∈ τ.vars, P v) : EntP P (bindV a τ θ) := by
  intro p hp
  simp only [bindV, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ⟨ha, hτ⟩
  · refine ⟨(hθ q hq).1, fun v hv => ?_⟩
    rcases vars_sb _ q.2 v hv with ⟨_, rfl, h'⟩ | ⟨c, hc, h'⟩
    · exact (hθ q hq).2 _ h'
    · by_cases e : c = a
      · subst e; rw [upd_self] at h'; exact hτ v h'
      · rw [upd_ne τ e] at h'; simp only [Ty.vars, List.mem_singleton] at h'; subst h'; exact (hθ q hq).2 _ hc

theorem cLoop_ent {R : Rigid} {P : BVar → Prop} : ∀ (fuel : Nat) (E : Eqs) (θ : Bnd) (n : Nat) (θ' : Bnd) (n' : Nat),
    GoodC R n θ E → (∀ v, v ∈ bvars E → P v) → (∀ b, b.isNew n = true → P (.ty b)) → EntP P θ →
    cLoop R fuel E θ n = .ok θ' n' → EntP P θ'
  | 0, _, _, _, _, _, _, _, _, _, h => by cases h
  | f + 1, [], θ, n, θ', n', _, _, _, hi, h => by
    simp only [cLoop, COut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hi
  | f + 1, (l, r) :: rest, θ, n, θ', n', g, hE, hN, hi, h => by
    simp only [cLoop] at h
    split at h
    · rename_i E1 θ1 n1 hs
      have g1 := (uStepC_next g hs).1
      obtain ⟨hn, hsh⟩ := uStepC_shape g hs
      have hN1 : ∀ b, b.isNew n1 = true → P (.ty b) := fun b hb => hN b (by
        cases e : b.isNew n
        · rw [isNew_mono hn e] at hb; cases hb
        · rfl)
      rcases hsh with ⟨rfl, hsub⟩ | ⟨a, τ, rest', ha, haE, hτ, hr', rfl, rfl⟩
      · exact cLoop_ent f E1 _ n1 θ' n' g1 (fun v hv => hE v (hsub v hv)) hN1 hi h
      · have hτP : ∀ v ∈ τ.vars, P v := fun v hv => by
          rcases hτ v hv with h' | ⟨c, rfl, h'⟩
          · exact hE v h'
          · exact hN _ h'
        refine cLoop_ent f _ _ n1 θ' n' g1 (fun v hv => ?_) hN1 (entP_bind hi (hE _ haE) hτP) h
        rcases substEqs_bvars hv with h1 | h1
        · exact hE v (hr' v h1)
        · exact hτP v h1
    · cases h
    · cases h

end StandardElm.Stat.Complete
