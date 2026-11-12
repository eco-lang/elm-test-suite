/-
  A Standard Definition of Elm? Mechanisation: termination of the unification of Mgu.lean, part 3
  of section 4's mgu theorem (milestone (b) of plan step 11): for some fuel the outcome is not
  `outOfFuel` (`uLoop_terminates`), and more fuel gives the same outcome (`uLoop_mono`).

  The measure is section 4's: the number of distinct type variables of the pending equations,
  then their size, lexicographically. A binding removes its variable and adds none (the occurs
  check); every other step keeps the variables and shrinks the equations. The measure is used in
  proofs only; the definition stays structural on fuel.
-/
import StandardElmMech.Stat.Complete.Mgu

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-! ## The measure -/

def tvs (τ : Ty) : List TyVar := τ.vars.filterMap fun v => match v with
  | .ty a => some a
  | .row _ => none

theorem mem_tvs {a : TyVar} {τ : Ty} : a ∈ tvs τ ↔ BVar.ty a ∈ τ.vars := by
  simp only [tvs, List.mem_filterMap]
  constructor
  · rintro ⟨v, hv, h⟩
    cases v with
    | ty b => simp at h; subst h; exact hv
    | row _ => simp at h
  · intro h; exact ⟨_, h, rfl⟩

def evars (E : Eqs) : List TyVar := E.flatMap fun e => tvs e.1 ++ tvs e.2

theorem mem_evars {a : TyVar} {E : Eqs} :
    a ∈ evars E ↔ ∃ e ∈ E, BVar.ty a ∈ e.1.vars ∨ BVar.ty a ∈ e.2.vars := by
  simp only [evars, List.mem_flatMap, List.mem_append, mem_tvs]

theorem mem_dedupL {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ dedupL l ↔ x ∈ l
  | [] => by simp [dedupL]
  | y :: ys => by
    simp only [dedupL, List.mem_cons, List.mem_filter, mem_dedupL, decide_eq_true_eq]
    by_cases h : x = y
    · simp [h]
    · simp [h]

theorem nodup_dedupL {α : Type} [DecidableEq α] : ∀ (l : List α), (dedupL l).Nodup
  | [] => List.nodup_nil
  | y :: ys => by
    simp only [dedupL]
    refine List.nodup_cons.mpr ⟨?_, (nodup_dedupL ys).filter _⟩
    simp [List.mem_filter]

/-- The number of distinct type variables of the equations. -/
def nd (E : Eqs) : Nat := (dedupL (evars E)).length

def esize (E : Eqs) : Nat := (E.map fun e => tsize e.1 + tsize e.2).sum

theorem nd_le {E F : Eqs} (h : ∀ a, a ∈ evars F → a ∈ evars E) : nd F ≤ nd E :=
  List.Nodup.length_le_of_subset (nodup_dedupL _) (fun x hx => mem_dedupL.mpr (h x (mem_dedupL.mp hx)))

theorem nd_lt {E F : Eqs} {a : TyVar} (ha : a ∈ evars E) (h : ∀ b, b ∈ evars F → b ∈ evars E ∧ b ≠ a) :
    nd F < nd E := by
  have hle : (dedupL (evars F)).length ≤ ((dedupL (evars E)).erase a).length := by
    apply List.Nodup.length_le_of_subset (nodup_dedupL _)
    intro x hx
    obtain ⟨h1, h2⟩ := h x (mem_dedupL.mp hx)
    exact (List.Nodup.mem_erase_iff (nodup_dedupL _)).mpr ⟨h2, mem_dedupL.mpr h1⟩
  rw [List.length_erase_of_mem (mem_dedupL.mpr ha)] at hle
  have : 0 < (dedupL (evars E)).length := List.length_pos_of_mem (mem_dedupL.mpr ha)
  unfold nd; omega

theorem evars_cons {l r : Ty} {E : Eqs} {a : TyVar} :
    a ∈ evars ((l, r) :: E) ↔ BVar.ty a ∈ l.vars ∨ BVar.ty a ∈ r.vars ∨ a ∈ evars E := by
  simp only [mem_evars, List.mem_cons]
  constructor
  · rintro ⟨e, rfl | he, h⟩
    · exact h.elim .inl (fun h => .inr (.inl h))
    · exact .inr (.inr ⟨e, he, h⟩)
  · rintro (h | h | ⟨e, he, h⟩)
    · exact ⟨_, .inl rfl, .inl h⟩
    · exact ⟨_, .inl rfl, .inr h⟩
    · exact ⟨e, .inr he, h⟩

theorem esize_cons (l r : Ty) (E : Eqs) : esize ((l, r) :: E) = tsize l + tsize r + esize E := by
  simp [esize]

theorem esize_append (E F : Eqs) : esize (E ++ F) = esize E + esize F := by
  simp [esize]

theorem zip_measure : ∀ (as bs : List Ty), esize (as.zip bs) ≤ lsize as + lsize bs ∧
    ∀ a, a ∈ evars (as.zip bs) → BVar.ty a ∈ Ty.listVars as ∨ BVar.ty a ∈ Ty.listVars bs
  | [], _ => ⟨by simp [esize], fun a h => by simp [evars] at h⟩
  | _ :: _, [] => ⟨by simp [esize], fun a h => by simp [evars] at h⟩
  | x :: xs, y :: ys => by
    obtain ⟨h1, h2⟩ := zip_measure xs ys
    refine ⟨?_, ?_⟩
    · simp only [List.zip_cons_cons, esize_cons, lsize]; omega
    · intro a ha
      simp only [List.zip_cons_cons, evars_cons] at ha
      simp only [Ty.listVars, List.mem_append]
      rcases ha with h | h | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · rcases h2 a h with h | h
        · exact .inl (.inr h)
        · exact .inr (.inr h)

/-- The measure decreases along a binding. -/
theorem bind_measure {a : TyVar} {τ : Ty} {rest : Eqs} (hocc : BVar.ty a ∉ τ.vars) :
    ∀ E0 : Eqs, a ∈ evars E0 → (∀ b, b ∈ evars rest → b ∈ evars E0) → (∀ b, BVar.ty b ∈ τ.vars → b ∈ evars E0) →
      nd (substEqs a τ rest) < nd E0 := by
  intro E0 ha hrest hτ0
  apply nd_lt ha
  intro b hb
  obtain ⟨e, he, hbe⟩ := mem_evars.mp hb
  simp only [substEqs, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  have key : ∀ σ, (BVar.ty b ∈ σ.vars → b ∈ evars rest) → BVar.ty b ∈ (sb (upd a τ) σ).vars →
      b ∈ evars E0 ∧ b ≠ a := by
    intro σ hσ hm
    rcases tyvar_sb_upd hm with ⟨h1, h2⟩ | h1
    · exact ⟨hrest b (hσ h1), h2⟩
    · exact ⟨hτ0 b h1, fun e => hocc (e ▸ h1)⟩
  rcases hbe with h | h
  · exact key _ (fun hm => mem_evars.mpr ⟨e0, he0, .inl hm⟩) h
  · exact key _ (fun hm => mem_evars.mpr ⟨e0, he0, .inr hm⟩) h

theorem bindStep_measure {a : TyVar} {τ : Ty} {rest E' : Eqs} {θ θ' : Bnd} (h : bindStep a τ rest θ = .next E' θ')
    (E0 : Eqs) (ha : a ∈ evars E0) (hrest : ∀ b, b ∈ evars rest → b ∈ evars E0)
    (hτ0 : ∀ b, BVar.ty b ∈ τ.vars → b ∈ evars E0) : nd E' < nd E0 := by
  unfold bindStep at h
  split at h
  · split at h
    · cases h
    · rename_i hocc; cases h
      exact bind_measure hocc E0 ha hrest hτ0
  · cases h

/-- Every step decreases the measure. -/
theorem uStep_measure {R : Rigid} {θ θ' : Bnd} {l r : Ty} {rest E' : Eqs} (h : uStep R θ l r rest = .next E' θ') :
    nd E' < nd ((l, r) :: rest) ∨ (nd E' ≤ nd ((l, r) :: rest) ∧ esize E' < esize ((l, r) :: rest)) := by
  have hrest : ∀ b, b ∈ evars rest → b ∈ evars ((l, r) :: rest) := fun b hb => evars_cons.mpr (.inr (.inr hb))
  have hl : ∀ b, BVar.ty b ∈ l.vars → b ∈ evars ((l, r) :: rest) := fun b hb => evars_cons.mpr (.inl hb)
  have hr : ∀ b, BVar.ty b ∈ r.vars → b ∈ evars ((l, r) :: rest) := fun b hb => evars_cons.mpr (.inr (.inl hb))
  unfold uStep at h
  split at h
  · cases h
    refine .inr ⟨nd_le hrest, ?_⟩
    rw [esize_cons]; have := tsize_pos l; omega
  · match l, r, h, hl, hr with
    | .var a, .var b, h, hl, hr =>
      dsimp only at h
      split at h
      · exact .inl (bindStep_measure h _ (hl a (mem_vars_var a)) hrest hr)
      · split at h
        · exact .inl (bindStep_measure h _ (hr b (mem_vars_var b)) hrest hl)
        · split at h <;> cases h
    | .var a, .record _ _, h, hl, hr =>
      dsimp only at h; split at h
      · exact .inl (bindStep_measure h _ (hl a (mem_vars_var a)) hrest hr)
      · cases h
    | .var a, .fn _ _, h, hl, hr =>
      dsimp only at h; split at h
      · exact .inl (bindStep_measure h _ (hl a (mem_vars_var a)) hrest hr)
      · cases h
    | .var a, .con _ _, h, hl, hr =>
      dsimp only at h; split at h
      · exact .inl (bindStep_measure h _ (hl a (mem_vars_var a)) hrest hr)
      · cases h
    | .record _ _, .var b, h, hl, hr =>
      dsimp only at h; split at h
      · exact .inl (bindStep_measure h _ (hr b (mem_vars_var b)) hrest hl)
      · cases h
    | .fn _ _, .var b, h, hl, hr =>
      dsimp only at h; split at h
      · exact .inl (bindStep_measure h _ (hr b (mem_vars_var b)) hrest hl)
      · cases h
    | .con _ _, .var b, h, hl, hr =>
      dsimp only at h; split at h
      · exact .inl (bindStep_measure h _ (hr b (mem_vars_var b)) hrest hl)
      · cases h
    | .fn x y, .fn z w, h, hl, hr =>
      dsimp only at h; cases h
      refine .inr ⟨nd_le ?_, ?_⟩
      · intro b hb
        simp only [evars_cons] at hb
        rcases hb with h | h | h | h | h
        · exact hl b (by simp [Ty.vars, h])
        · exact hr b (by simp [Ty.vars, h])
        · exact hl b (by simp [Ty.vars, h])
        · exact hr b (by simp [Ty.vars, h])
        · exact hrest b h
      · simp only [esize_cons, tsize]; omega
    | .con as t, .con bs t', h, hl, hr =>
      dsimp only at h; split at h
      · cases h
        obtain ⟨hs, hv⟩ := zip_measure as bs
        refine .inr ⟨nd_le ?_, ?_⟩
        · intro b hb
          rcases (mem_evars.mp hb) with ⟨e, he, hbe⟩
          rcases List.mem_append.mp he with he | he
          · rcases hv b (mem_evars.mpr ⟨e, he, hbe⟩) with h | h
            · exact hl b (by simpa [Ty.vars] using h)
            · exact hr b (by simpa [Ty.vars] using h)
          · exact hrest b (mem_evars.mpr ⟨e, he, hbe⟩)
        · rw [esize_append, esize_cons]; simp only [tsize]; omega
      · cases h
    | .record _ _, .record _ _, h, _, _ => cases h
    | .record _ _, .fn _ _, h, _, _ => cases h
    | .record _ _, .con _ _, h, _, _ => cases h
    | .fn _ _, .record _ _, h, _, _ => cases h
    | .fn _ _, .con _ _, h, _, _ => cases h
    | .con _ _, .record _ _, h, _, _ => cases h
    | .con _ _, .fn _ _, h, _, _ => cases h

/-! ## Termination and fuel monotonicity -/

theorem uLoop_term_aux {R : Rigid} : ∀ (N : Nat) (S : Nat) (E : Eqs) (θ : Bnd), nd E < N → esize E < S →
    ∃ n, uLoop R n E θ ≠ .outOfFuel
  | 0, _, _, _, hN, _ => absurd hN (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, hS => absurd hS (Nat.not_lt_zero _)
  | N + 1, S + 1, [], θ, _, _ => ⟨1, by simp [uLoop]⟩
  | N + 1, S + 1, (l, r) :: rest, θ, hN, hS => by
    cases hs : uStep R θ l r rest with
    | next E' θ' =>
      have hm := uStep_measure hs
      obtain ⟨n, hn⟩ : ∃ n, uLoop R n E' θ' ≠ .outOfFuel := by
        rcases hm with hm | ⟨hm1, hm2⟩
        · exact uLoop_term_aux N (esize E' + 1) E' θ' (by omega) (by omega)
        · exact uLoop_term_aux (N + 1) S E' θ' (by omega) (by omega)
      exact ⟨n + 1, by simp only [uLoop, hs]; exact hn⟩
    | fail => exact ⟨1, by simp [uLoop, hs]⟩
    | unsupported => exact ⟨1, by simp [uLoop, hs]⟩

/-- Section 4, part 3: some fuel suffices. -/
theorem uLoop_terminates (R : Rigid) (E : Eqs) (θ : Bnd) : ∃ n, uLoop R n E θ ≠ .outOfFuel :=
  uLoop_term_aux (nd E + 1) (esize E + 1) E θ (Nat.lt_succ_self _) (Nat.lt_succ_self _)

/-- More fuel gives the same outcome. -/
theorem uLoop_mono {R : Rigid} : ∀ (n m : Nat) (E : Eqs) (θ : Bnd), uLoop R n E θ ≠ .outOfFuel →
    uLoop R (n + m) E θ = uLoop R n E θ
  | 0, _, _, _, h => absurd rfl h
  | n + 1, m, [], θ, _ => by simp only [Nat.add_right_comm n 1 m, uLoop]
  | n + 1, m, (l, r) :: rest, θ, h => by
    rw [Nat.add_right_comm n 1 m]
    simp only [uLoop] at h ⊢
    split
    · rename_i E' θ' hs
      rw [hs] at h; simp only at h
      exact uLoop_mono n m E' θ' h
    · rfl
    · rfl

theorem mgu_terminates (R : Rigid) (E : Eqs) : ∃ n, mgu n R E ≠ .outOfFuel := uLoop_terminates R E []

theorem mgu_mono {n m : Nat} {R : Rigid} {E : Eqs} (h : mgu n R E ≠ .outOfFuel) : mgu (n + m) R E = mgu n R E :=
  uLoop_mono n m E [] h

end StandardElm.Stat.Complete
