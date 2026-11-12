/-
  A Standard Definition of Elm? Mechanisation: the mgu theorem with classes, milestone (c) of plan
  step 11 (section 4, parts 1 to 3), for the unification of MguC.lean.

  * `uStepC_fail`: a failing step has no class-respecting unifier fixing the rigid variables (K1,
    K3, K4, K5 through the requirements, K7);
  * `cLoop_ok`, `cLoop_fail`: the invariant and the correspondence along the loop;
  * `mguC_ok`: the result unifies, fixes the rigid variables, respects classes, is idempotent, and
    every class-respecting unifier `s` fixing the rigid variables factors through it,
    `s a = T (θ a)` for every old variable `a`, with `T` respecting classes and fixing the rigid
    variables; `mguC_fail`: failure means no such unifier;
  * `mguC_terminates`, `mguC_mono`: termination (the measure `muC`: distinct variables weighted by
    the height of their classes, then the size) and fuel monotonicity.

  F_b as a special case: on a problem whose flexible variables are all of class any, every
  requirement is met and every meet is `any`, so the algorithm makes Mgu.lean's bindings; and
  every substitution respects classes on variables of class any, so `mguC_ok` gives `mgu_ok`'s
  factorisation with `T` agreeing with `s` on the old variables.
-/
import StandardElmMech.Stat.Complete.MguC

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-! ## Failure -/

theorem varStepC_fail {R : Rigid} {a : TyVar} {τ : Ty} {cur rest : Eqs} {θ : Bnd} {n : Nat}
    (hτ : ∀ b, τ ≠ .var b) (h : varStepC R a τ cur rest θ n = .fail) :
    ∀ s, FixesR R s → RespC s → s a ≠ sb s τ := by
  intro s hs hr e
  unfold varStepC at h
  split at h
  · rename_i hocc; exact occurs_neF s hocc (hτ a) e
  · split at h
    · rename_i hreq; exact reqC_none s _ _ hreq (e ▸ hr a)
    · rename_i ps hps
      split at h
      · rename_i ht
        obtain ⟨⟨b, k⟩, hp, hle, hor⟩ := refineTarget_none ht
        have hk : Adm k (s b) := (reqC_spec s _ _ _ hps).mp (e ▸ hr a) _ hp
        rcases hor with hrb | hm
        · rw [hs b hrb] at hk
          simp only at hle; rw [admC_var_iff.mp hk] at hle; cases hle
        · exact admC_meet_none hm (hr b) hk
      · cases h
      · cases h

theorem uStepC_fail {R : Rigid} {n : Nat} {θ : Bnd} {l r : Ty} {rest : Eqs}
    (h : uStepC R θ n l r rest = .fail) : ∀ s, FixesR R s → RespC s → sb s l ≠ sb s r := by
  intro s hs hr
  unfold uStepC at h
  by_cases hlr : l = r
  · simp only [hlr, ↓reduceIte] at h; cases h
  simp only [hlr, ↓reduceIte] at h
  match l, r, h, hlr with
  | .var a, .var b, h, hlr =>
    dsimp only at h
    have hab : a ≠ b := fun e => hlr (by rw [e])
    simp only [sb]
    split at h
    · split at h
      · rename_i hm; intro e; exact admC_meet_none hm (hr a) (e ▸ hr b)
      · split at h
        · cases h
        · split at h <;> cases h
    · rename_i hfl
      split at h
      · rename_i hra
        simp only [Bool.not_eq_true'] at hra
        have hrb : R b = true := by
          cases hb : R b
          · simp [hra, hb] at hfl
          · rfl
        split at h
        · cases h
        · rename_i hle
          intro e; rw [hs b hrb] at e
          exact hle (admC_var_iff.mp (e ▸ hr a))
      · rename_i hra
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
        split at h
        · rename_i hrb
          simp only [Bool.not_eq_true'] at hrb
          split at h
          · cases h
          · rename_i hle
            intro e; rw [hs a hra] at e
            exact hle (admC_var_iff.mp (e.symm ▸ hr b))
        · rename_i hrb
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
          rw [hs a hra, hs b hrb]
          intro e; injection e with e; exact hab e
  | .var a, .record ρ tl, h, _ =>
    dsimp only at h; split at h
    · exact varStepC_fail (fun _ e => by cases e) h s hs hr
    · rename_i hra; simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
      rw [sb, hs a hra]; simp [sb]
  | .var a, .fn x y, h, _ =>
    dsimp only at h; split at h
    · exact varStepC_fail (fun _ e => by cases e) h s hs hr
    · rename_i hra; simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
      rw [sb, hs a hra]; simp [sb]
  | .var a, .con as t, h, _ =>
    dsimp only at h; split at h
    · exact varStepC_fail (fun _ e => by cases e) h s hs hr
    · rename_i hra; simp only [Bool.not_eq_true', Bool.not_eq_false] at hra
      rw [sb, hs a hra]; simp [sb]
  | .record ρ tl, .var b, h, _ =>
    dsimp only at h; split at h
    · exact fun e => varStepC_fail (fun _ e => by cases e) h s hs hr e.symm
    · rename_i hrb; simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
      conv => rhs; rw [sb, hs b hrb]
      simp [sb]
  | .fn x y, .var b, h, _ =>
    dsimp only at h; split at h
    · exact fun e => varStepC_fail (fun _ e => by cases e) h s hs hr e.symm
    · rename_i hrb; simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
      conv => rhs; rw [sb, hs b hrb]
      simp [sb]
  | .con as t, .var b, h, _ =>
    dsimp only at h; split at h
    · exact fun e => varStepC_fail (fun _ e => by cases e) h s hs hr e.symm
    · rename_i hrb; simp only [Bool.not_eq_true', Bool.not_eq_false] at hrb
      conv => rhs; rw [sb, hs b hrb]
      simp [sb]
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

theorem cLoop_ok {R : Rigid} : ∀ (fuel : Nat) (E : Eqs) (θ : Bnd) (n : Nat) (θ' : Bnd) (n' : Nat),
    NewFlex R n → GoodC R n θ E → cLoop R fuel E θ n = .ok θ' n' →
    GoodC R n' θ' [] ∧ n ≤ n' ∧ CorrC R n E θ [] θ'
  | 0, _, _, _, _, _, _, _, h => by cases h
  | f + 1, [], θ, n, θ', n', _, g, h => by
    simp only [cLoop, COut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨g, Nat.le_refl _, corrC_refl R n [] θ⟩
  | f + 1, (l, r) :: rest, θ, n, θ', n', hN, g, h => by
    simp only [cLoop] at h
    split at h
    · rename_i E1 θ1 n1 hs
      obtain ⟨g1, hn1, c1⟩ := uStepC_next g hs
      obtain ⟨g2, hn2, c2⟩ := cLoop_ok f E1 θ1 n1 θ' n' (hN.mono hn1) g1 h
      exact ⟨g2, Nat.le_trans hn1 hn2, corrC_trans hN hn1 c1 c2⟩
    · cases h
    · cases h

theorem cLoop_fail {R : Rigid} : ∀ (fuel : Nat) (E : Eqs) (θ : Bnd) (n : Nat),
    NewFlex R n → GoodC R n θ E → cLoop R fuel E θ n = .fail →
    ∀ s, FixesR R s → RespC s → Unifies s E → Absorbs s (lk θ) → False
  | 0, _, _, _, _, _, h => by cases h
  | f + 1, [], θ, n, _, _, h => by cases h
  | f + 1, (l, r) :: rest, θ, n, hN, g, h => by
    simp only [cLoop] at h
    split at h
    · rename_i E1 θ1 n1 hs
      obtain ⟨g1, hn1, c1⟩ := uStepC_next g hs
      intro s hs' hr hu ha
      obtain ⟨s1, ag, r1, u1, b1⟩ := c1.2 s hs' hr hu ha
      exact cLoop_fail f E1 θ1 n1 (hN.mono hn1) g1 h s1 (fixesR_of_agree hN hs' ag) r1 u1 b1
    · rename_i hs
      intro s hs' hr hu _
      exact uStepC_fail hs s hs' hr (unifies_cons.mp hu).1
    · cases h

/-! ## The mgu theorem (section 4, parts 1 and 2) -/

theorem mguC_ok {fuel : Nat} {R : Rigid} {n : Nat} {E : Eqs} {θ : Bnd} {n' : Nat}
    (hN : NewFlex R n) (hE : EOld n E) (h : mguC fuel R n E = .ok θ n') :
    Unifies (lk θ) E ∧ FixesR R (lk θ) ∧ RespC (lk θ) ∧ Idem (lk θ) ∧ n ≤ n' ∧ BOld n' θ ∧
    ∀ s, FixesR R s → RespC s → Unifies s E →
      ∃ T, FixesR R T ∧ RespC T ∧ (∀ a, a.isNew n = false → T a = s a) ∧ Absorbs T (lk θ) ∧
        ∀ a, a.isNew n = false → s a = sb T (lk θ a) := by
  obtain ⟨g, hn, c⟩ := cLoop_ok fuel E [] n θ n' hN (goodC_nil R hE) h
  have habs : Absorbs (lk θ) (lk θ) := fun a => sb_eq_self_iff.mpr (g.idem a)
  refine ⟨(c.1 (lk θ) (unifies_nil _) habs).1, g.fixesR, g.respC, g.idem, hn, g.oldθ, ?_⟩
  intro s hs hr hu
  obtain ⟨T, ag, rT, _, aT⟩ := c.2 s hs hr hu (absorbs_id s)
  exact ⟨T, fixesR_of_agree hN hs ag, rT, ag, aT, fun a ha => by rw [aT a, ag a ha]⟩

theorem mguC_fail {fuel : Nat} {R : Rigid} {n : Nat} {E : Eqs}
    (hN : NewFlex R n) (hE : EOld n E) (h : mguC fuel R n E = .fail) :
    ∀ s, FixesR R s → RespC s → ¬ Unifies s E := fun s hs hr hu =>
  cLoop_fail fuel E [] n hN (goodC_nil R hE) h s hs hr hu (absorbs_id s)

/-! ## Termination (section 4, part 3) -/

/-- The height of a class in the order: a refinement lowers it. -/
def hgt : Cls → Nat
  | .any => 2
  | .comp => 1
  | .app => 1
  | .num => 0
  | .capp => 0

theorem hgt_lt {m k : Cls} (h1 : m.le k = true) (h2 : m ≠ k) : hgt m < hgt k := by
  cases m <;> cases k <;> simp_all [Cls.le, hgt]

theorem hgt_le (k : Cls) : hgt k ≤ 2 := by cases k <;> simp [hgt]

/-- The distinct variables of the equations satisfying `P`. -/
def ndP (P : TyVar → Bool) (E : Eqs) : Nat := (dedupL ((evars E).filter P)).length

/-- The measure: distinct variables, weighted by the height of their classes. -/
def muC (E : Eqs) : Nat :=
  ndP (fun _ => true) E + ndP (fun a => decide (1 ≤ hgt a.cls)) E + ndP (fun a => decide (2 ≤ hgt a.cls)) E

theorem mem_filterP {P : TyVar → Bool} {E : Eqs} {a : TyVar} :
    a ∈ dedupL ((evars E).filter P) ↔ a ∈ evars E ∧ P a = true := by
  rw [mem_dedupL, List.mem_filter]

theorem ndP_le {P : TyVar → Bool} {E F : Eqs} (h : ∀ a, a ∈ evars F → P a = true → a ∈ evars E) :
    ndP P F ≤ ndP P E :=
  List.Nodup.length_le_of_subset (nodup_dedupL _) fun x hx => by
    obtain ⟨h1, h2⟩ := mem_filterP.mp hx; exact mem_filterP.mpr ⟨h x h1 h2, h2⟩

theorem ndP_lt {P : TyVar → Bool} {E F : Eqs} {a : TyVar} (ha : a ∈ evars E) (hPa : P a = true)
    (h : ∀ b, b ∈ evars F → P b = true → b ∈ evars E ∧ b ≠ a) : ndP P F < ndP P E := by
  have hle : (dedupL ((evars F).filter P)).length ≤ ((dedupL ((evars E).filter P)).erase a).length := by
    apply List.Nodup.length_le_of_subset (nodup_dedupL _)
    intro x hx
    obtain ⟨h1, h2⟩ := mem_filterP.mp hx
    obtain ⟨h3, h4⟩ := h x h1 h2
    exact (List.Nodup.mem_erase_iff (nodup_dedupL _)).mpr ⟨h4, mem_filterP.mpr ⟨h3, h2⟩⟩
  have hm : a ∈ dedupL ((evars E).filter P) := mem_filterP.mpr ⟨ha, hPa⟩
  rw [List.length_erase_of_mem hm] at hle
  have : 0 < (dedupL ((evars E).filter P)).length := List.length_pos_of_mem hm
  unfold ndP; omega

theorem nodup_map_on {α β : Type} {f : α → β} : ∀ {l : List α},
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hf, hn => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hn
    refine List.nodup_cons.mpr ⟨?_, nodup_map_on (fun a ha b hb => hf a (.tail _ ha) b (.tail _ hb)) h2⟩
    intro hm
    obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
    exact h1 (hf y (.tail _ hy) x (.head _) e ▸ hy)

theorem ndP_rep {P : TyVar → Bool} {E F : Eqs} {b g : TyVar} (hb : b ∈ evars E) (hPb : P b = true)
    (hg : g ∉ evars E) (h : ∀ x, x ∈ evars F → P x = true → (x ∈ evars E ∧ x ≠ b) ∨ x = g) :
    ndP P F ≤ ndP P E := by
  let f : TyVar → TyVar := fun x => if x = g then b else x
  have hgb : g ≠ b := fun e => hg (e ▸ hb)
  have nb : ∀ x ∈ dedupL ((evars F).filter P), x ≠ b := fun x hx e => by
    obtain ⟨h1, h2⟩ := mem_filterP.mp hx
    rcases h x h1 h2 with ⟨_, h3⟩ | h3
    · exact h3 e
    · exact hgb (h3 ▸ e)
  have hinj : ∀ x ∈ dedupL ((evars F).filter P), ∀ y ∈ dedupL ((evars F).filter P), f x = f y → x = y := by
    intro x hx y hy e
    simp only [f] at e
    by_cases hxg : x = g <;> by_cases hyg : y = g <;> simp only [hxg, hyg, ↓reduceIte] at e
    · rw [hxg, hyg]
    · exact absurd e.symm (nb y hy)
    · exact absurd e (nb x hx)
    · exact e
  have hlen := List.Nodup.length_le_of_subset (nodup_map_on hinj (nodup_dedupL _))
    (l₂ := dedupL ((evars E).filter P)) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨h1, h2⟩ := mem_filterP.mp hy
      simp only [f]
      split
      · exact mem_filterP.mpr ⟨hb, hPb⟩
      · rcases h y h1 h2 with ⟨h3, _⟩ | h3
        · exact mem_filterP.mpr ⟨h3, h2⟩
        · contradiction)
  rw [List.length_map] at hlen
  exact hlen

theorem muC_le {E F : Eqs} (h : ∀ a, a ∈ evars F → a ∈ evars E) : muC F ≤ muC E := by
  unfold muC
  have := ndP_le (P := fun _ => true) (fun a ha _ => h a ha)
  have := ndP_le (P := fun a => decide (1 ≤ hgt a.cls)) (fun a ha _ => h a ha)
  have := ndP_le (P := fun a => decide (2 ≤ hgt a.cls)) (fun a ha _ => h a ha)
  omega

theorem muC_lt {E F : Eqs} {a : TyVar} (ha : a ∈ evars E) (h : ∀ b, b ∈ evars F → b ∈ evars E ∧ b ≠ a) :
    muC F < muC E := by
  unfold muC
  have := ndP_lt (P := fun _ => true) ha rfl (fun b hb _ => h b hb)
  have := ndP_le (P := fun a => decide (1 ≤ hgt a.cls)) (fun b hb _ => (h b hb).1)
  have := ndP_le (P := fun a => decide (2 ≤ hgt a.cls)) (fun b hb _ => (h b hb).1)
  omega

/-- A refinement lowers the measure. -/
theorem muC_refine {E F : Eqs} {b g : TyVar} (hb : b ∈ evars E)
    (hh : hgt g.cls < hgt b.cls) (h : ∀ x, x ∈ evars F → (x ∈ evars E ∧ x ≠ b) ∨ x = g) :
    muC F < muC E := by
  by_cases hg : g ∈ evars E
  · have hgb : g ≠ b := fun e => by rw [e] at hh; exact Nat.lt_irrefl _ hh
    exact muC_lt hb fun x hx => by
      rcases h x hx with h' | rfl
      · exact h'
      · exact ⟨hg, hgb⟩
  unfold muC
  have h0 := ndP_rep (P := fun _ => true) hb rfl hg (fun x hx _ => h x hx)
  have hb2 := hgt_le b.cls
  by_cases e2 : hgt b.cls = 2
  · have h2 := ndP_lt (P := fun a => decide (2 ≤ hgt a.cls)) hb (by simp [e2]) (fun x hx hP => by
      rcases h x hx with h' | rfl
      · exact h'
      · simp at hP; omega)
    by_cases e1 : 1 ≤ hgt g.cls
    · have h1 := ndP_rep (P := fun a => decide (1 ≤ hgt a.cls)) hb (by simp; omega) hg (fun x hx _ => h x hx)
      omega
    · have h1 := ndP_lt (P := fun a => decide (1 ≤ hgt a.cls)) hb (by simp; omega) (fun x hx hP => by
        rcases h x hx with h' | rfl
        · exact h'
        · simp at hP; omega)
      omega
  · have h1 := ndP_lt (P := fun a => decide (1 ≤ hgt a.cls)) hb (by simp; omega) (fun x hx hP => by
      rcases h x hx with h' | rfl
      · exact h'
      · simp at hP; omega)
    have h2 := ndP_le (P := fun a => decide (2 ≤ hgt a.cls)) (fun x hx hP => by
      rcases h x hx with h' | rfl
      · exact h'.1
      · simp at hP; omega)
    omega

theorem substEqs_evars {a b : TyVar} {τ : Ty} {rest : Eqs} (hb : b ∈ evars (substEqs a τ rest)) :
    (b ∈ evars rest ∧ b ≠ a) ∨ BVar.ty b ∈ τ.vars := by
  obtain ⟨e, he, hbe⟩ := mem_evars.mp hb
  rcases substEqs_vars he hbe with ⟨e0, he0, h1, h2⟩ | h1
  · exact .inl ⟨mem_evars.mpr ⟨e0, he0, h1⟩, h2⟩
  · exact .inr h1

theorem bindN_measure {a : TyVar} {τ : Ty} {rest : Eqs} (hocc : BVar.ty a ∉ τ.vars) (E0 : Eqs)
    (ha : a ∈ evars E0) (hrest : ∀ b, b ∈ evars rest → b ∈ evars E0) (hτ0 : ∀ b, BVar.ty b ∈ τ.vars → b ∈ evars E0) :
    muC (substEqs a τ rest) < muC E0 :=
  muC_lt ha fun b hb => by
    rcases substEqs_evars hb with ⟨h1, h2⟩ | h1
    · exact ⟨hrest b h1, h2⟩
    · exact ⟨hτ0 b h1, fun e => hocc (e ▸ h1)⟩

theorem refineN_measure {n : Nat} {E : Eqs} {b : TyVar} {m : Cls}
    (hb : b ∈ evars E) (hm1 : m.le b.cls = true) (hm2 : m ≠ b.cls) :
    muC (substEqs b (.var (.fresh n m)) E) < muC E := by
  apply muC_refine hb (g := .fresh n m)
  · exact hgt_lt hm1 hm2
  · intro x hx
    rcases substEqs_evars hx with h1 | h1
    · exact .inl h1
    · simp [Ty.vars] at h1; exact .inr h1

theorem varStepC_measure {R : Rigid} {n : Nat} {θ : Bnd} {a : TyVar} {τ : Ty} {cur rest E' : Eqs} {θ' : Bnd}
    {n' : Nat} (ha : a ∈ evars cur) (hrest : ∀ b, b ∈ evars rest → b ∈ evars cur)
    (hτ0 : ∀ b, BVar.ty b ∈ τ.vars → b ∈ evars cur) (h : varStepC R a τ cur rest θ n = .next E' θ' n') :
    muC E' < muC cur := by
  unfold varStepC at h
  split at h
  · cases h
  · rename_i hocc
    split at h
    · cases h
    · rename_i ps hps
      split at h
      · cases h
      · cases h; exact bindN_measure hocc cur ha hrest hτ0
      · rename_i b m ht
        cases h
        obtain ⟨k, hk, _, hm, hle⟩ := refineTarget_some ht
        obtain ⟨h1, h2⟩ := meet_lt hm hle
        exact refineN_measure (hτ0 b (reqC_vars _ _ _ hps _ hk)) h1 h2

/-- Every step decreases the measure. -/
theorem uStepC_measure {R : Rigid} {n : Nat} {θ : Bnd} {l r : Ty} {rest E' : Eqs} {θ' : Bnd} {n' : Nat}
    (h : uStepC R θ n l r rest = .next E' θ' n') :
    muC E' < muC ((l, r) :: rest) ∨ (muC E' ≤ muC ((l, r) :: rest) ∧ esize E' < esize ((l, r) :: rest)) := by
  have hrest : ∀ b, b ∈ evars rest → b ∈ evars ((l, r) :: rest) := fun b hb => evars_cons.mpr (.inr (.inr hb))
  have hl : ∀ b, BVar.ty b ∈ l.vars → b ∈ evars ((l, r) :: rest) := fun b hb => evars_cons.mpr (.inl hb)
  have hr : ∀ b, BVar.ty b ∈ r.vars → b ∈ evars ((l, r) :: rest) := fun b hb => evars_cons.mpr (.inr (.inl hb))
  unfold uStepC at h
  split at h
  · cases h
    refine .inr ⟨muC_le hrest, ?_⟩
    rw [esize_cons]; have := tsize_pos l; omega
  · split at h
    · rename_i a b hab
      have hab' : a ≠ b := fun e => hab (by rw [e])
      have nab : BVar.ty a ∉ (Ty.var b).vars := by simpa [Ty.vars] using hab'
      have nba : BVar.ty b ∉ (Ty.var a).vars := by simpa [Ty.vars] using fun e => hab' e.symm
      have ha := hl a (mem_vars_var a)
      have hb := hr b (mem_vars_var b)
      split at h
      · split at h
        · cases h
        · rename_i m hm
          obtain ⟨hma, _, _⟩ := (Cls.meet_spec _ _ m).mp hm
          split at h
          · cases h; exact .inl (bindN_measure nab _ ha hrest hr)
          · split at h
            · cases h; exact .inl (bindN_measure nba _ hb hrest hl)
            · rename_i hmb hma'
              cases h
              exact .inl (refineN_measure ha hma hma')
      · split at h
        · split at h
          · cases h; exact .inl (bindN_measure nab _ ha hrest hr)
          · cases h
        · split at h
          · split at h
            · cases h; exact .inl (bindN_measure nba _ hb hrest hl)
            · cases h
          · cases h
    · rename_i r' a _ _
      split at h
      · exact .inl (varStepC_measure (hl a (mem_vars_var a)) hrest hr h)
      · cases h
    · rename_i l' b _ _
      split at h
      · exact .inl (varStepC_measure (hr b (mem_vars_var b)) hrest hl h)
      · cases h
    · cases h
      refine .inr ⟨muC_le ?_, ?_⟩
      · intro b hb
        simp only [evars_cons] at hb
        rcases hb with h | h | h | h | h
        · exact hl b (by simp [Ty.vars, h])
        · exact hr b (by simp [Ty.vars, h])
        · exact hl b (by simp [Ty.vars, h])
        · exact hr b (by simp [Ty.vars, h])
        · exact hrest b h
      · simp only [esize_cons, tsize]; omega
    · split at h
      · rename_i as t bs t' _ _
        cases h
        obtain ⟨hs, hv⟩ := zip_measure as bs
        refine .inr ⟨muC_le ?_, ?_⟩
        · intro b hb
          rcases (mem_evars.mp hb) with ⟨e, he, hbe⟩
          rcases List.mem_append.mp he with he | he
          · rcases hv b (mem_evars.mpr ⟨e, he, hbe⟩) with h | h
            · exact hl b (by simpa [Ty.vars] using h)
            · exact hr b (by simpa [Ty.vars] using h)
          · exact hrest b (mem_evars.mpr ⟨e, he, hbe⟩)
        · rw [esize_append, esize_cons]; simp only [tsize]; omega
      · cases h
    · cases h
    · cases h

theorem cLoop_term_aux {R : Rigid} : ∀ (N S : Nat) (E : Eqs) (θ : Bnd) (n : Nat),
    muC E < N → esize E < S → ∃ f, cLoop R f E θ n ≠ .outOfFuel
  | 0, _, _, _, _, hN, _ => absurd hN (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, _, hS => absurd hS (Nat.not_lt_zero _)
  | N + 1, S + 1, [], θ, n, _, _ => ⟨1, by simp [cLoop]⟩
  | N + 1, S + 1, (l, r) :: rest, θ, n, hN, hS => by
    cases hs : uStepC R θ n l r rest with
    | next E' θ' n' =>
      have hm := uStepC_measure hs
      obtain ⟨f, hf⟩ : ∃ f, cLoop R f E' θ' n' ≠ .outOfFuel := by
        rcases hm with hm | ⟨hm1, hm2⟩
        · exact cLoop_term_aux N (esize E' + 1) E' θ' n' (by omega) (by omega)
        · exact cLoop_term_aux (N + 1) S E' θ' n' (by omega) (by omega)
      exact ⟨f + 1, by simp only [cLoop, hs]; exact hf⟩
    | fail => exact ⟨1, by simp [cLoop, hs]⟩
    | unsupported => exact ⟨1, by simp [cLoop, hs]⟩

theorem cLoop_terminates (R : Rigid) (n : Nat) (θ : Bnd) (E : Eqs) : ∃ f, cLoop R f E θ n ≠ .outOfFuel :=
  cLoop_term_aux (muC E + 1) (esize E + 1) E θ n (Nat.lt_succ_self _) (Nat.lt_succ_self _)

theorem cLoop_mono {R : Rigid} : ∀ (f m : Nat) (E : Eqs) (θ : Bnd) (n : Nat), cLoop R f E θ n ≠ .outOfFuel →
    cLoop R (f + m) E θ n = cLoop R f E θ n
  | 0, _, _, _, _, h => absurd rfl h
  | f + 1, m, [], θ, n, _ => by simp only [Nat.add_right_comm f 1 m, cLoop]
  | f + 1, m, (l, r) :: rest, θ, n, h => by
    rw [Nat.add_right_comm f 1 m]
    simp only [cLoop] at h ⊢
    split
    · rename_i E' θ' n' hs
      rw [hs] at h; simp only at h
      exact cLoop_mono f m E' θ' n' h
    · rfl
    · rfl

theorem mguC_terminates (R : Rigid) (n : Nat) (E : Eqs) : ∃ f, mguC f R n E ≠ .outOfFuel :=
  cLoop_terminates R n [] E

theorem mguC_mono {f m : Nat} {R : Rigid} {n : Nat} {E : Eqs} (h : mguC f R n E ≠ .outOfFuel) :
    mguC (f + m) R n E = mguC f R n E :=
  cLoop_mono f m E [] n h

end StandardElm.Stat.Complete
