/-
  A Standard Definition of Elm? Mechanisation: termination of unification with rows (plan step
  11, section 4, part 3), milestone (d), for every problem.

  The measure is lexicographic: the distinct variables of the equations, type variables weighted
  by the height of their classes as in MguCLoop.lean (`muC`) plus the row variables (`ndR`); then
  the *exponential* size `esz` (the sum over equations of `2 ^ (size of both sides)`). Every
  binding removes a variable (a row binding of (U5) removes one tail; the last case removes two
  and adds one fresh tail); a refinement lowers a class; a decomposition keeps the variables and
  lowers `esz` (exponential, so that the equations of common fields, one per field of the left
  side, stay below the record equation even when a label repeats: termination holds for every
  problem, canonical or not).
-/
import StandardElmMech.Stat.Complete.MguRLoop
import StandardElmMech.Stat.Complete.MguCLoop

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

/-! ## Variables of the equations -/

def InV (w : BVar) (E : Eqs) : Prop := ∃ e ∈ E, w ∈ e.1.vars ∨ w ∈ e.2.vars

def rvs (τ : Ty) : List RowVar := τ.vars.filterMap fun v => match v with
  | .row e => some e
  | .ty _ => none

theorem mem_rvs {e : RowVar} {τ : Ty} : e ∈ rvs τ ↔ BVar.row e ∈ τ.vars := by
  simp only [rvs, List.mem_filterMap]
  constructor
  · rintro ⟨v, hv, h⟩
    cases v with
    | row b => simp at h; subst h; exact hv
    | ty _ => simp at h
  · intro h; exact ⟨_, h, rfl⟩

def rvE (E : Eqs) : List RowVar := E.flatMap fun e => rvs e.1 ++ rvs e.2

theorem mem_rvE {e : RowVar} {E : Eqs} : e ∈ rvE E ↔ InV (.row e) E := by
  simp only [rvE, List.mem_flatMap, List.mem_append, mem_rvs, InV]

theorem mem_evarsV {a : TyVar} {E : Eqs} : a ∈ evars E ↔ InV (.ty a) E := mem_evars

def ndR (E : Eqs) : Nat := (dedupL (rvE E)).length

def muR (E : Eqs) : Nat := muC E + ndR E

theorem ndR_le {E F : Eqs} (h : ∀ e, InV (.row e) F → InV (.row e) E) : ndR F ≤ ndR E :=
  List.Nodup.length_le_of_subset (nodup_dedupL _) fun x hx =>
    mem_dedupL.mpr (mem_rvE.mpr (h x (mem_rvE.mp (mem_dedupL.mp hx))))

theorem ndR_lt {E F : Eqs} {e : RowVar} (he : InV (.row e) E)
    (h : ∀ x, InV (.row x) F → InV (.row x) E ∧ x ≠ e) : ndR F < ndR E := by
  have hle : (dedupL (rvE F)).length ≤ ((dedupL (rvE E)).erase e).length := by
    apply List.Nodup.length_le_of_subset (nodup_dedupL _)
    intro x hx
    obtain ⟨h1, h2⟩ := h x (mem_rvE.mp (mem_dedupL.mp hx))
    exact (List.Nodup.mem_erase_iff (nodup_dedupL _)).mpr ⟨h2, mem_dedupL.mpr (mem_rvE.mpr h1)⟩
  have hm : e ∈ dedupL (rvE E) := mem_dedupL.mpr (mem_rvE.mpr he)
  rw [List.length_erase_of_mem hm] at hle
  have : 0 < (dedupL (rvE E)).length := List.length_pos_of_mem hm
  unfold ndR; omega

/-- Two row variables removed, at most one fresh one added. -/
theorem ndR_two {E F : Eqs} {e1 e2 x : RowVar} (h1 : InV (.row e1) E) (h2 : InV (.row e2) E) (h12 : e1 ≠ e2)
    (hx1 : x ≠ e1) (hx2 : x ≠ e2)
    (h : ∀ y, InV (.row y) F → (InV (.row y) E ∧ y ≠ e1 ∧ y ≠ e2) ∨ y = x) : ndR F < ndR E := by
  by_cases hxE : InV (.row x) E
  · exact ndR_lt h1 fun y hy => by
      rcases h y hy with ⟨a, b, _⟩ | rfl
      · exact ⟨a, b⟩
      · exact ⟨hxE, hx1⟩
  let f : RowVar → RowVar := fun y => if y = x then e1 else y
  have ne1 : ∀ y ∈ dedupL (rvE F), y ≠ e1 := fun y hy e => by
    rcases h y (mem_rvE.mp (mem_dedupL.mp hy)) with ⟨_, h3, _⟩ | h3
    · exact h3 e
    · exact hx1 (h3 ▸ e)
  have hinj : ∀ a ∈ dedupL (rvE F), ∀ b ∈ dedupL (rvE F), f a = f b → a = b := by
    intro a ha b hb e
    simp only [f] at e
    by_cases hax : a = x <;> by_cases hbx : b = x <;> simp only [hax, hbx, ↓reduceIte] at e
    · rw [hax, hbx]
    · exact absurd e.symm (ne1 b hb)
    · exact absurd e (ne1 a ha)
    · exact e
  have hlen := List.Nodup.length_le_of_subset (nodup_map_on hinj (nodup_dedupL _))
    (l₂ := (dedupL (rvE E)).erase e2) (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      rw [List.Nodup.mem_erase_iff (nodup_dedupL _)]
      simp only [f]
      split
      · exact ⟨h12, mem_dedupL.mpr (mem_rvE.mpr h1)⟩
      · rcases h z (mem_rvE.mp (mem_dedupL.mp hz)) with ⟨h3, _, h5⟩ | h3
        · exact ⟨h5, mem_dedupL.mpr (mem_rvE.mpr h3)⟩
        · contradiction)
  rw [List.length_map, List.length_erase_of_mem (mem_dedupL.mpr (mem_rvE.mpr h2))] at hlen
  have : 0 < (dedupL (rvE E)).length := List.length_pos_of_mem (mem_dedupL.mpr (mem_rvE.mpr h2))
  unfold ndR; omega

theorem muR_le {E F : Eqs} (h : ∀ w, InV w F → InV w E) : muR F ≤ muR E := by
  unfold muR
  have := muC_le (E := E) (F := F) fun a ha => mem_evarsV.mpr (h _ (mem_evarsV.mp ha))
  have := ndR_le (E := E) (F := F) fun e he => h _ he
  omega

theorem muR_lt_ty {E F : Eqs} {a : TyVar} (ha : InV (.ty a) E) (h : ∀ w, InV w F → InV w E ∧ w ≠ .ty a) :
    muR F < muR E := by
  unfold muR
  have := muC_lt (E := E) (F := F) (mem_evarsV.mpr ha) fun b hb => by
    obtain ⟨h1, h2⟩ := h _ (mem_evarsV.mp hb)
    exact ⟨mem_evarsV.mpr h1, fun e => h2 (by rw [e])⟩
  have := ndR_le (E := E) (F := F) fun e he => (h _ he).1
  omega

theorem muR_lt_row {E F : Eqs} {e : RowVar} (he : InV (.row e) E) (h : ∀ w, InV w F → InV w E ∧ w ≠ .row e) :
    muR F < muR E := by
  unfold muR
  have := muC_le (E := E) (F := F) fun a ha => mem_evarsV.mpr (h _ (mem_evarsV.mp ha)).1
  have := ndR_lt (E := E) (F := F) he fun x hx => ⟨(h _ hx).1, fun e' => (h _ hx).2 (by rw [e'])⟩
  omega

theorem muR_refine {E F : Eqs} {b g : TyVar} (hb : InV (.ty b) E) (hh : hgt g.cls < hgt b.cls)
    (h : ∀ w, InV w F → (InV w E ∧ w ≠ .ty b) ∨ w = .ty g) : muR F < muR E := by
  unfold muR
  have := muC_refine (E := E) (F := F) (b := b) (g := g) (mem_evarsV.mpr hb) hh fun x hx => by
    rcases h _ (mem_evarsV.mp hx) with ⟨h1, h2⟩ | h1
    · exact .inl ⟨mem_evarsV.mpr h1, fun e => h2 (by rw [e])⟩
    · exact .inr (by cases h1; rfl)
  have := ndR_le (E := E) (F := F) fun e he => by
    rcases h _ he with ⟨h1, _⟩ | h1
    · exact h1
    · cases h1
  omega

/-! ## The exponential size -/

def esz (E : Eqs) : Nat := (E.map fun e => 2 ^ (tsize e.1 + tsize e.2)).sum

theorem esz_cons (l r : Ty) (E : Eqs) : esz ((l, r) :: E) = 2 ^ (tsize l + tsize r) + esz E := by
  simp [esz]

theorem esz_append (E F : Eqs) : esz (E ++ F) = esz E + esz F := by simp [esz]

theorem pow_add_le {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) : 2 ^ a + 2 ^ b ≤ 2 ^ (a + b) := by
  have h1 : 2 ≤ 2 ^ a := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) ha; simpa using this
  have h2 : 2 ≤ 2 ^ b := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hb; simpa using this
  rw [Nat.pow_add]
  have e1 := Nat.mul_le_mul_right (2 ^ b) h1
  have e2 := Nat.mul_le_mul_left (2 ^ a) h2
  omega

theorem pow_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h

/-- The sizes of the fields of a row, exponentially. -/
theorem rowPow_le : ∀ ρ : Row, (ρ.map fun p => 2 ^ tsize p.2).sum ≤ 2 ^ rsize ρ
  | [] => by simp
  | [(l, x)] => by simp [rsize]
  | (l, x) :: (l', y) :: r => by
    have ih := rowPow_le ((l', y) :: r)
    have hx := tsize_pos x
    have hy := tsize_pos y
    have := pow_add_le (a := tsize x) (b := tsize y + rsize r) hx (by omega)
    simp only [List.map_cons, List.sum_cons, rsize] at ih this ⊢
    omega

theorem tsize_le_rsize {ρ : Row} {p : Lab × Ty} (h : p ∈ ρ) : tsize p.2 ≤ rsize ρ := by
  induction ρ with
  | nil => cases h
  | cons q r ih =>
    obtain ⟨l, x⟩ := q
    simp only [rsize]
    rcases List.mem_cons.mp h with rfl | h
    · simp only; omega
    · have := ih h; omega

theorem esz_common_le (ρ1 ρ2 : Row) : esz (commonEqs ρ1 ρ2) ≤ 2 ^ (rsize ρ1 + rsize ρ2) := by
  have key : ∀ ρ : Row, esz (commonEqs ρ ρ2) ≤ (ρ.map fun p => 2 ^ tsize p.2).sum * 2 ^ rsize ρ2 := by
    intro ρ
    induction ρ with
    | nil => simp [esz, commonEqs]
    | cons p r ih =>
      have hc : commonEqs (p :: r) ρ2 = ((FMap.find? ρ2 p.1).map fun τ => (p.2, τ)).toList ++ commonEqs r ρ2 := by
        simp only [commonEqs, List.filterMap_cons]
        cases FMap.find? ρ2 p.1 <;> rfl
      rw [hc, esz_append]
      simp only [List.map_cons, List.sum_cons, Nat.add_mul]
      have : esz ((FMap.find? ρ2 p.1).map fun τ => (p.2, τ)).toList ≤ 2 ^ tsize p.2 * 2 ^ rsize ρ2 := by
        cases hf : FMap.find? ρ2 p.1 with
        | none => simp [esz]
        | some τ =>
          simp only [Option.map_some, Option.toList_some, esz, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, Nat.add_zero]
          rw [← Nat.pow_add]
          exact pow_mono (Nat.add_le_add_left (tsize_le_rsize (p := (p.1, τ)) (rowFind?_mem hf)) _)
      omega
  have := key ρ1
  have h2 := Nat.mul_le_mul_right (2 ^ rsize ρ2) (rowPow_le ρ1)
  rw [← Nat.pow_add] at h2
  omega

theorem esz_zip_le : ∀ (as bs : List Ty), esz (as.zip bs) ≤ 2 ^ (lsize as + lsize bs)
  | [], _ => by simp [esz]
  | _ :: _, [] => by simp [esz]
  | a :: as, b :: bs => by
    have ih := esz_zip_le as bs
    simp only [List.zip_cons_cons, esz_cons, lsize]
    by_cases h0 : lsize as + lsize bs = 0
    · have has : as = [] := by
        cases as with
        | nil => rfl
        | cons x _ => simp only [lsize] at h0; have := tsize_pos x; omega
      subst has
      simp only [List.zip_nil_left, esz, List.map_nil, List.sum_nil, Nat.add_zero]
      exact pow_mono (by omega)
    · have := pow_add_le (a := tsize a + tsize b) (b := lsize as + lsize bs) (by have := tsize_pos a; omega) (by omega)
      have e : tsize a + lsize as + (tsize b + lsize bs) = tsize a + tsize b + (lsize as + lsize bs) := by omega
      rw [e]; omega

theorem fn_esz {a b c d : Ty} {rest : Eqs} : esz ((a, c) :: (b, d) :: rest) < esz ((.fn a b, .fn c d) :: rest) := by
  simp only [esz_cons, tsize]
  have h1 := pow_mono (a := tsize a + tsize c) (b := tsize a + tsize b + tsize c + tsize d) (by omega)
  have h2 := pow_mono (a := tsize b + tsize d) (b := tsize a + tsize b + tsize c + tsize d) (by omega)
  have h4 : 2 ^ (1 + tsize a + tsize b + (1 + tsize c + tsize d)) = 4 * 2 ^ (tsize a + tsize b + tsize c + tsize d) := by
    have e : 1 + tsize a + tsize b + (1 + tsize c + tsize d) = (tsize a + tsize b + tsize c + tsize d) + 1 + 1 := by omega
    rw [e, Nat.pow_succ, Nat.pow_succ]; omega
  have := Nat.two_pow_pos (tsize a + tsize b + tsize c + tsize d)
  omega

theorem con_esz {as bs : List Ty} {t t' : TyName} {rest : Eqs} :
    esz (as.zip bs ++ rest) < esz ((.con as t, .con bs t') :: rest) := by
  rw [esz_append, esz_cons]
  have h1 := esz_zip_le as bs
  have h2 : 2 ^ (lsize as + lsize bs) < 2 ^ (tsize (.con as t) + tsize (.con bs t')) := by
    simp only [tsize]; exact Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-! ## Variables after a binding -/

theorem isRec_row {e : RowVar} {ρ : Row} {tl : Option RowVar} : IsRec (.row e) (.record ρ tl) := ⟨ρ, tl, rfl⟩
theorem isRec_ty {a : TyVar} {τ : Ty} : IsRec (.ty a) τ := trivial

theorem inV_sE_one {v : BVar} {τ : Ty} {E : Eqs} {w : BVar} (hv : IsRec v τ) (h : InV w (sE (one v τ) E)) :
    (InV w E ∧ w ≠ v) ∨ w ∈ τ.vars := by
  obtain ⟨e, he, hw⟩ := h
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  rcases hw with hw | hw
  · rcases vars_rsb_one hw hv with ⟨h1, h2⟩ | h1
    · exact .inl ⟨⟨e0, he0, .inl h1⟩, h2⟩
    · exact .inr h1
  · rcases vars_rsb_one hw hv with ⟨h1, h2⟩ | h1
    · exact .inl ⟨⟨e0, he0, .inr h1⟩, h2⟩
    · exact .inr h1

theorem inV_cons_l {w : BVar} {l r : Ty} {E : Eqs} (h : w ∈ l.vars) : InV w ((l, r) :: E) := ⟨_, .head _, .inl h⟩
theorem inV_cons_r {w : BVar} {l r : Ty} {E : Eqs} (h : w ∈ r.vars) : InV w ((l, r) :: E) := ⟨_, .head _, .inr h⟩
theorem inV_cons_rest {w : BVar} {l r : Ty} {E : Eqs} (h : InV w E) : InV w ((l, r) :: E) := by
  obtain ⟨e, he, h⟩ := h; exact ⟨e, .tail _ he, h⟩

/-- The variables of the problem after the common equations. -/
theorem inV_rec {w : BVar} {ρ1 ρ2 : Row} {t1 t2 : Option RowVar} {rest : Eqs}
    (h : InV w (commonEqs ρ1 ρ2 ++ rest)) : InV w ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
  obtain ⟨e, he, hw⟩ := h
  rcases List.mem_append.mp he with he | he
  · obtain ⟨l', h1, h2⟩ := commonEqs_fields he
    rcases hw with hw | hw
    · exact inV_cons_l (field_vars (p := (l', e.1)) h1 hw)
    · exact inV_cons_r (field_vars (p := (l', e.2)) h2 hw)
  · exact inV_cons_rest ⟨e, he, hw⟩

theorem esz_rec_lt {ρ1 ρ2 : Row} {t1 t2 : Option RowVar} {rest : Eqs} :
    esz (commonEqs ρ1 ρ2 ++ rest) < esz ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
  rw [esz_append, esz_cons]
  have h := esz_common_le ρ1 ρ2
  have : 2 ^ (rsize ρ1 + rsize ρ2) < 2 ^ (tsize (.record ρ1 t1) + tsize (.record ρ2 t2)) := by
    simp only [tsize]; exact Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-! ## Each step lowers the measure -/

section rec
variable {R : RRigid} {n : Nat} {θ : RBnd} {ρ1 ρ2 : Row} {t1 t2 : Option RowVar} {rest : Eqs} {X : List Ty}

theorem recB_measure {e : RowVar} {ϱ : Row} {t : Option RowVar} {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (hb : bindRow R e ϱ t (commonEqs ρ1 ρ2 ++ rest) X θ n = .next E' X' θ' n')
    (hev : InV (.row e) ((.record ρ1 t1, .record ρ2 t2) :: rest))
    (hϱ : ∀ w ∈ (Ty.record ϱ t).vars, InV w ((.record ρ1 t1, .record ρ2 t2) :: rest)) :
    muR E' < muR ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
  obtain ⟨_, hocc, _, rfl, rfl, rfl, rfl⟩ := bindRow_next hb
  refine muR_lt_row hev fun w hw => ?_
  rcases inV_sE_one isRec_row hw with ⟨h1, h2⟩ | h1
  · exact ⟨inV_rec h1, h2⟩
  · exact ⟨hϱ w h1, fun e' => hocc (e' ▸ h1)⟩

theorem fields_inV {ϱ : Row} {t : Option RowVar} (hϱ : ∀ p ∈ ϱ, p ∈ ρ1 ∨ p ∈ ρ2)
    (ht : ∀ e', t = some e' → BVar.row e' ∈ (Ty.record ρ1 t1).vars ∨ BVar.row e' ∈ (Ty.record ρ2 t2).vars) :
    ∀ w ∈ (Ty.record ϱ t).vars, InV w ((.record ρ1 t1, .record ρ2 t2) :: rest) := by
  intro w hw
  rw [vars_record, List.mem_append] at hw
  rcases hw with hw | hw
  · obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp hw
    rcases hϱ p hp with h | h
    · exact inV_cons_l (field_vars h hw)
    · exact inV_cons_r (field_vars h hw)
  · cases t with
    | none => cases hw
    | some e' =>
      simp only [tailVars, List.mem_singleton] at hw; subst hw
      rcases ht e' rfl with h | h
      · exact inV_cons_l h
      · exact inV_cons_r h

theorem recStep_measure {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat}
    (h : recStep R ρ1 t1 ρ2 t2 rest X θ n = .next E' X' θ' n') :
    muR E' < muR ((.record ρ1 t1, .record ρ2 t2) :: rest) ∨
      (muR E' ≤ muR ((.record ρ1 t1, .record ρ2 t2) :: rest) ∧ esz E' < esz ((.record ρ1 t1, .record ρ2 t2) :: rest)) := by
  have caseA : muR (commonEqs ρ1 ρ2 ++ rest) ≤ muR ((.record ρ1 t1, .record ρ2 t2) :: rest) ∧
      esz (commonEqs ρ1 ρ2 ++ rest) < esz ((.record ρ1 t1, .record ρ2 t2) :: rest) :=
    ⟨muR_le fun w hw => inV_rec hw, esz_rec_lt⟩
  have l1 : ∀ p ∈ onlyL ρ1 ρ2, p ∈ ρ1 ∨ p ∈ ρ2 := fun p hp => .inl (mem_onlyL.mp hp).1
  have l2 : ∀ p ∈ onlyL ρ2 ρ1, p ∈ ρ1 ∨ p ∈ ρ2 := fun p hp => .inr (mem_onlyL.mp hp).1
  have l0 : ∀ p ∈ ([] : Row), p ∈ ρ1 ∨ p ∈ ρ2 := fun p hp => by cases hp
  cases t1 with
  | none =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      split at h
      · cases h; exact .inr caseA
      · cases h
    | some e2 =>
      simp only [recStep] at h
      split at h
      · exact .inl (recB_measure h (inV_cons_r tail_vars) (fields_inV l1 fun _ h => by cases h))
      · cases h
  | some e1 =>
    cases t2 with
    | none =>
      simp only [recStep] at h
      split at h
      · exact .inl (recB_measure h (inV_cons_l tail_vars) (fields_inV l2 fun _ h => by cases h))
      · cases h
    | some e2 =>
      simp only [recStep] at h
      split at h
      · subst e1
        split at h
        · cases h; exact .inr caseA
        · cases h
      · rename_i hne
        split at h
        · split at h
          · split at h
            · exact .inl (recB_measure h (inV_cons_l tail_vars) (fields_inV l0 fun _ h => by cases h; exact .inr tail_vars))
            · exact .inl (recB_measure h (inV_cons_r tail_vars) (fields_inV l0 fun _ h => by cases h; exact .inl tail_vars))
          · exact .inl (recB_measure h (inV_cons_r tail_vars) (fields_inV l1 fun _ h => by cases h; exact .inl tail_vars))
        · split at h
          · exact .inl (recB_measure h (inV_cons_l tail_vars) (fields_inV l2 fun _ h => by cases h; exact .inr tail_vars))
          · split at h
            · rename_i F1 X1 θ1 n1 hb1
              obtain ⟨_, hocc1, _, rfl, rfl, rfl, rfl⟩ := bindRow_next hb1
              obtain ⟨_, hocc2, _, rfl, rfl, rfl, rfl⟩ := bindRow_next h
              left
              have hε1 : RowVar.fresh n ≠ e1 := fun e => hocc1 (by rw [← e]; exact tail_vars)
              have hε2 : RowVar.fresh n ≠ e2 := fun e => hocc2 (by rw [← e]; exact tail_vars)
              have hv2 := fields_inV (ρ1 := ρ1) (ρ2 := ρ2) (t1 := some e1) (t2 := some e2) (rest := rest) l2
                (ϱ := onlyL ρ2 ρ1) (t := none) (fun _ h => by cases h)
              unfold muR
              have hmu := muC_le (E := (.record ρ1 (some e1), .record ρ2 (some e2)) :: rest)
                (F := sE (one (.row e2) (.record (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))))
                  (onlyL ρ1 ρ2)) (some (.fresh n)))) (sE (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))))
                    (commonEqs ρ1 ρ2 ++ rest))) fun a ha => by
                have hw := mem_evarsV.mp ha
                apply mem_evarsV.mpr
                rcases inV_sE_one isRec_row hw with ⟨hw, _⟩ | hw
                · rcases inV_sE_one isRec_row hw with ⟨hw, _⟩ | hw
                  · exact inV_rec hw
                  · rw [vars_record, List.mem_append] at hw
                    rcases hw with hw | hw
                    · exact hv2 _ (by rw [vars_record]; exact List.mem_append_left _ hw)
                    · simp [tailVars] at hw
                · rw [vars_record, List.mem_append] at hw
                  rcases hw with hw | hw
                  · rw [rsbRow_eq] at hw
                    obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp hw
                    obtain ⟨q, hq, rfl⟩ := mem_mapV.mp hp
                    rcases vars_rsb_one hw isRec_row with ⟨hw, _⟩ | hw
                    · exact inV_cons_l (field_vars (mem_onlyL.mp hq).1 hw)
                    · rw [vars_record, List.mem_append] at hw
                      rcases hw with hw | hw
                      · exact hv2 _ (by rw [vars_record]; exact List.mem_append_left _ hw)
                      · simp [tailVars] at hw
                  · simp [tailVars] at hw
              have hnd := ndR_two (E := (.record ρ1 (some e1), .record ρ2 (some e2)) :: rest)
                (F := sE (one (.row e2) (.record (rsbRow (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))))
                  (onlyL ρ1 ρ2)) (some (.fresh n)))) (sE (one (.row e1) (.record (onlyL ρ2 ρ1) (some (.fresh n))))
                    (commonEqs ρ1 ρ2 ++ rest))) (x := .fresh n)
                (inV_cons_l tail_vars) (inV_cons_r tail_vars) hne hε1 hε2 fun y hy => by
                rcases inV_sE_one isRec_row hy with ⟨hy, hy2⟩ | hy
                · rcases inV_sE_one isRec_row hy with ⟨hy, hy1⟩ | hy
                  · exact .inl ⟨inV_rec hy, fun e => hy1 (by rw [e]), fun e => hy2 (by rw [e])⟩
                  · rw [vars_record, List.mem_append] at hy
                    rcases hy with hz | hz
                    · refine .inl ⟨hv2 _ (by rw [vars_record]; exact List.mem_append_left _ hz), ?_, fun e => hy2 (by rw [e])⟩
                      intro e; exact hocc1 (by rw [vars_record]; exact List.mem_append_left _ (e ▸ hz))
                    · simp only [tailVars, List.mem_singleton, BVar.row.injEq] at hz; exact .inr hz
                · by_cases hyx : y = .fresh n
                  · exact .inr hyx
                  refine .inl ?_
                  have hy2 : y ≠ e2 := fun e => hocc2 (by rw [← e]; exact hy)
                  rw [vars_record, List.mem_append] at hy
                  rcases hy with hy | hy
                  · rw [rsbRow_eq] at hy
                    obtain ⟨p, hp, hw⟩ := mem_rowVarsR.mp hy
                    obtain ⟨q, hq, rfl⟩ := mem_mapV.mp hp
                    rcases vars_rsb_one hw isRec_row with ⟨hw, hw1⟩ | hw
                    · exact ⟨inV_cons_l (field_vars (mem_onlyL.mp hq).1 hw), fun e => hw1 (by rw [e]), hy2⟩
                    · rw [vars_record, List.mem_append] at hw
                      rcases hw with hz | hz
                      · refine ⟨hv2 _ (by rw [vars_record]; exact List.mem_append_left _ hz), ?_, hy2⟩
                        intro e; exact hocc1 (by rw [vars_record]; exact List.mem_append_left _ (e ▸ hz))
                      · simp only [tailVars, List.mem_singleton, BVar.row.injEq] at hz; exact absurd hz hyx
                  · simp only [tailVars, List.mem_singleton, BVar.row.injEq] at hy; exact absurd hy hyx
              omega
            · cases h

end rec

theorem uStepR_measure {R : RRigid} {n : Nat} {θ : RBnd} {l r : Ty} {rest : Eqs} {X : List Ty}
    {E' : Eqs} {X' : List Ty} {θ' : RBnd} {n' : Nat} (h : uStepR R θ n l r rest X = .next E' X' θ' n') :
    muR E' < muR ((l, r) :: rest) ∨ (muR E' ≤ muR ((l, r) :: rest) ∧ esz E' < esz ((l, r) :: rest)) := by
  have hrest : ∀ w, InV w rest → InV w ((l, r) :: rest) := fun w hw => inV_cons_rest hw
  unfold uStepR at h
  split at h
  · cases h
    refine .inr ⟨muR_le hrest, ?_⟩
    rw [esz_cons]; have := Nat.two_pow_pos (tsize l + tsize r); omega
  · split at h
    · -- var, var
      rename_i a b hab
      have hab' : a ≠ b := fun e => hab (by rw [e])
      have bindA : ∀ {E1 : Eqs} {X1 : List Ty} {θ1 : RBnd} {n1 : Nat}, bindS (.ty a) (.var b) rest (.var a :: X) θ n
          = .next E1 X1 θ1 n1 → muR E1 < muR ((.var a, .var b) :: rest) := by
        intro E1 X1 θ1 n1 hb
        simp only [bindS, RStep.next.injEq] at hb; obtain ⟨rfl, -, -, -⟩ := hb
        refine muR_lt_ty (inV_cons_l (mem_vars_var a)) fun w hw => ?_
        rcases inV_sE_one isRec_ty hw with ⟨h1, h2⟩ | h1
        · exact ⟨hrest w h1, h2⟩
        · simp only [Ty.vars, List.mem_singleton] at h1; subst h1
          exact ⟨inV_cons_r (mem_vars_var b), fun e => hab' (by cases e; rfl)⟩
      have bindB : ∀ {E1 : Eqs} {X1 : List Ty} {θ1 : RBnd} {n1 : Nat}, bindS (.ty b) (.var a) rest (.var a :: X) θ n
          = .next E1 X1 θ1 n1 → muR E1 < muR ((.var a, .var b) :: rest) := by
        intro E1 X1 θ1 n1 hb
        simp only [bindS, RStep.next.injEq] at hb; obtain ⟨rfl, -, -, -⟩ := hb
        refine muR_lt_ty (inV_cons_r (mem_vars_var b)) fun w hw => ?_
        rcases inV_sE_one isRec_ty hw with ⟨h1, h2⟩ | h1
        · exact ⟨hrest w h1, h2⟩
        · simp only [Ty.vars, List.mem_singleton] at h1; subst h1
          exact ⟨inV_cons_l (mem_vars_var a), fun e => hab' (by cases e; rfl)⟩
      split at h
      · split at h
        · cases h
        · rename_i m hm
          obtain ⟨hma, _, _⟩ := (Cls.meet_spec _ _ m).mp hm
          split at h
          · exact .inl (bindA h)
          · split at h
            · exact .inl (bindB h)
            · rename_i hmb hma'
              simp only [refineS, bindS, RStep.next.injEq] at h; obtain ⟨rfl, -, -, -⟩ := h
              refine .inl (muR_refine (g := .fresh n m) (inV_cons_l (mem_vars_var a)) (hgt_lt hma hma') fun w hw => ?_)
              rcases inV_sE_one isRec_ty hw with ⟨h1, h2⟩ | h1
              · exact .inl ⟨h1, h2⟩
              · simp only [Ty.vars, List.mem_singleton] at h1; exact .inr h1
      · split at h
        · split at h
          · exact .inl (bindA h)
          · cases h
        · split at h
          · split at h
            · exact .inl (bindB h)
            · cases h
          · cases h
    · -- var, non-var
      rename_i a r' _ _
      split at h
      · unfold varStepR at h
        split at h
        · cases h
        · rename_i hocc
          split at h
          · cases h
          · rename_i ps hps
            split at h
            · cases h
            · simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, -, -, -⟩ := h
              refine .inl (muR_lt_ty (inV_cons_l (mem_vars_var _)) fun w hw => ?_)
              rcases inV_sE_one isRec_ty hw with ⟨h1, h2⟩ | h1
              · exact ⟨hrest w h1, h2⟩
              · exact ⟨inV_cons_r h1, fun e => hocc (e ▸ h1)⟩
            · rename_i b m ht
              simp only [refineS, bindS, RStep.next.injEq] at h; obtain ⟨rfl, -, -, -⟩ := h
              obtain ⟨k, hk, _, hm, hle⟩ := refineTarget_some ht
              obtain ⟨h1, h2⟩ := meet_lt hm hle
              refine .inl (muR_refine (g := .fresh n m) (inV_cons_r (reqC_vars _ _ _ hps _ hk)) (hgt_lt h1 h2) fun w hw => ?_)
              rcases inV_sE_one isRec_ty hw with ⟨h1, h2⟩ | h1
              · exact .inl ⟨h1, h2⟩
              · simp only [Ty.vars, List.mem_singleton] at h1; exact .inr h1
      · cases h
    · -- non-var, var
      rename_i l' b _ _
      split at h
      · unfold varStepR at h
        split at h
        · cases h
        · rename_i hocc
          split at h
          · cases h
          · rename_i ps hps
            split at h
            · cases h
            · simp only [bindS, RStep.next.injEq] at h; obtain ⟨rfl, -, -, -⟩ := h
              refine .inl (muR_lt_ty (inV_cons_r (mem_vars_var _)) fun w hw => ?_)
              rcases inV_sE_one isRec_ty hw with ⟨h1, h2⟩ | h1
              · exact ⟨hrest w h1, h2⟩
              · exact ⟨inV_cons_l h1, fun e => hocc (e ▸ h1)⟩
            · rename_i c m ht
              simp only [refineS, bindS, RStep.next.injEq] at h; obtain ⟨rfl, -, -, -⟩ := h
              obtain ⟨k, hk, _, hm, hle⟩ := refineTarget_some ht
              obtain ⟨h1, h2⟩ := meet_lt hm hle
              refine .inl (muR_refine (g := .fresh n m) (inV_cons_l (reqC_vars _ _ _ hps _ hk)) (hgt_lt h1 h2) fun w hw => ?_)
              rcases inV_sE_one isRec_ty hw with ⟨h1, h2⟩ | h1
              · exact .inl ⟨h1, h2⟩
              · simp only [Ty.vars, List.mem_singleton] at h1; exact .inr h1
      · cases h
    · -- fn, fn
      cases h
      refine .inr ⟨muR_le fun w hw => ?_, ?_⟩
      · obtain ⟨e, he, hw⟩ := hw
        rcases List.mem_cons.mp he with rfl | he
        · rcases hw with hw | hw
          · exact inV_cons_l (by simp [Ty.vars, hw])
          · exact inV_cons_r (by simp [Ty.vars, hw])
        rcases List.mem_cons.mp he with rfl | he
        · rcases hw with hw | hw
          · exact inV_cons_l (by simp [Ty.vars, hw])
          · exact inV_cons_r (by simp [Ty.vars, hw])
        · exact hrest w ⟨e, he, hw⟩
      · exact fn_esz
    · -- con, con
      split at h
      · rename_i as t bs t' hc
        cases h
        refine .inr ⟨muR_le fun w hw => ?_, ?_⟩
        · obtain ⟨e, he, hw⟩ := hw
          rcases List.mem_append.mp he with he | he
          · have hm := List.of_mem_zip he
            rcases hw with hw | hw
            · exact inV_cons_l (by simp only [Ty.vars]; exact mem_listVarsR.mpr ⟨_, hm.1, hw⟩)
            · exact inV_cons_r (by simp only [Ty.vars]; exact mem_listVarsR.mpr ⟨_, hm.2, hw⟩)
          · exact hrest w ⟨e, he, hw⟩
        · exact con_esz
      · cases h
    · -- record, record
      exact recStep_measure h
    · cases h

/-! ## Termination (section 4, part 3) -/

theorem rLoop_term_aux {R : RRigid} : ∀ (N S : Nat) (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat),
    muR E < N → esz E < S → ∃ f, rLoop R f E X θ n ≠ .outOfFuel
  | 0, _, _, _, _, _, hN, _ => absurd hN (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, _, _, hS => absurd hS (Nat.not_lt_zero _)
  | N + 1, S + 1, [], X, θ, n, _, _ => ⟨1, by simp [rLoop]⟩
  | N + 1, S + 1, (l, r) :: rest, X, θ, n, hN, hS => by
    cases hs : uStepR R θ n l r rest X with
    | next E' X' θ' n' =>
      have hm := uStepR_measure hs
      obtain ⟨f, hf⟩ : ∃ f, rLoop R f E' X' θ' n' ≠ .outOfFuel := by
        rcases hm with hm | ⟨hm1, hm2⟩
        · exact rLoop_term_aux N (esz E' + 1) E' X' θ' n' (by omega) (by omega)
        · exact rLoop_term_aux (N + 1) S E' X' θ' n' (by omega) (by omega)
      exact ⟨f + 1, by simp only [rLoop, hs]; exact hf⟩
    | fail => exact ⟨1, by simp [rLoop, hs]⟩

theorem rLoop_terminates (R : RRigid) (n : Nat) (θ : RBnd) (E : Eqs) (X : List Ty) :
    ∃ f, rLoop R f E X θ n ≠ .outOfFuel :=
  rLoop_term_aux (muR E + 1) (esz E + 1) E X θ n (Nat.lt_succ_self _) (Nat.lt_succ_self _)

theorem rLoop_mono {R : RRigid} : ∀ (f m : Nat) (E : Eqs) (X : List Ty) (θ : RBnd) (n : Nat),
    rLoop R f E X θ n ≠ .outOfFuel → rLoop R (f + m) E X θ n = rLoop R f E X θ n
  | 0, _, _, _, _, _, h => absurd rfl h
  | f + 1, m, [], X, θ, n, _ => by simp only [Nat.add_right_comm f 1 m, rLoop]
  | f + 1, m, (l, r) :: rest, X, θ, n, h => by
    rw [Nat.add_right_comm f 1 m]
    simp only [rLoop] at h ⊢
    split
    · rename_i E' X' θ' n' hs
      rw [hs] at h; simp only at h
      exact rLoop_mono f m E' X' θ' n' h
    · rfl

theorem mguR_terminates (R : RRigid) (n : Nat) (E : Eqs) (X : List Ty) : ∃ f, mguR f R n E X ≠ .outOfFuel :=
  rLoop_terminates R n [] E X

theorem mguR_mono {f m : Nat} {R : RRigid} {n : Nat} {E : Eqs} {X : List Ty} (h : mguR f R n E X ≠ .outOfFuel) :
    mguR (f + m) R n E X = mguR f R n E X :=
  rLoop_mono f m E X [] n h

end StandardElm.Stat.Complete
