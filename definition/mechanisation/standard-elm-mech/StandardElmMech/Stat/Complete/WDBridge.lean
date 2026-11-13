/-
  A Standard Definition of Elm? Mechanisation: step 9's substitutions (`Subst.apply`, partial,
  with row bindings merged by `Row.merge`) against the total substitutions of RSubst.lean
  (`rsb`, rows merged by `mrg`), for milestone (d) of plan step 11.

  * `mergeF_eq_mrg`: a successful merge (`Row.mergeF`, none on a shared label) is the total merge
    `mrg`, for any lists (no sortedness needed: on distinct labels the two choose the same field
    first, `labLt_tri`, `labLt_asymm`).
  * `apply_eq_rsb`: wherever step 9's substitution is defined, it is `rsb` of the substitution
    read as an `RSub` (`Subst.toR`). So an instance of a scheme (`Gen`) is an image under `rsb`
    (`gen_rsb`), and a class-respecting step 9 substitution gives a class-respecting `RSub`.
  * Conversely, on rows with disjoint labels the merge succeeds (`mergeF_of_ldisj`), so step 9's
    substitution is defined wherever `rsb` gives a canonical image (`apply_of_cn`: a canonical
    image has every merged row sorted, so its two parts have disjoint labels), and a canonical
    image of a scheme's body under a class-respecting substitution of its bound variables is an
    instance of the scheme (`gen_of_rsb`).
-/
import StandardElmMech.Stat.Complete.Closure
import StandardElmMech.Stat.Complete.RSubst

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

/-- A step 9 substitution read as a total substitution of type and row variables. -/
def _root_.StandardElm.Stat.Subst.toR (S : Subst) : RSub :=
  ⟨fun a => (FMap.find? S.ty a).getD (.var a), fun e => (FMap.find? S.row e).getD ([], some e)⟩

theorem mergeF_eq_mrg : ∀ (f : Nat) (a b c : Row), Row.mergeF f a b = some c → c = mrg a b
  | _, [], b, c, h => by simp only [Row.mergeF, Option.some.injEq] at h; subst h; rfl
  | _, _ :: _, [], c, h => by simp only [Row.mergeF, Option.some.injEq] at h; subst h; rfl
  | 0, _ :: _, _ :: _, _, h => by simp [Row.mergeF] at h
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2, c, h => by
    simp only [Row.mergeF] at h
    split at h
    · cases h
    · rename_i hne
      split at h
      · rename_i hlt
        split at h
        · rename_i r hr
          cases h
          rw [mergeF_eq_mrg f _ _ _ hr, mrg_cons_cons]
          have : fLe (l1, τ1) (l2, τ2) = true := fLe_iff.mpr (labLt_asymm hlt)
          rw [if_pos this]
        · cases h
      · rename_i hlt
        split at h
        · rename_i r hr
          cases h
          rw [mergeF_eq_mrg f _ _ _ hr, mrg_cons_cons]
          have h21 : labLt l2 l1 = true := by
            rcases labLt_tri l1 l2 with h' | h' | h'
            · exact absurd h' hlt
            · exact absurd h' hne
            · exact h'
          have : ¬ fLe (l1, τ1) (l2, τ2) = true := not_fLe.mpr h21
          rw [if_neg this]
        · cases h

theorem merge_eq_mrg {a b c : Row} (h : Row.merge a b = some c) : c = mrg a b := mergeF_eq_mrg _ _ _ _ h

theorem toR_tl_none (S : Subst) : (Subst.toR S).tl none = ([], none) := rfl

mutual
/-- Step 9's substitution, where defined, is `rsb`. -/
theorem apply_eq_rsb (S : Subst) : ∀ (τ τ' : Ty), S.apply τ = some τ' → τ' = rsb S.toR τ
  | .var a, τ', h => by
    simp only [Subst.apply, Option.some.injEq] at h; subst h; rfl
  | .record ρ none, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i ρ' hr
      cases h
      rw [rsb, applyRow_eq_rsb S ρ ρ' hr, toR_tl_none, mrg_nil_right]
    · cases h
  | .record ρ (some e), τ', h => by
    simp only [Subst.apply] at h
    cases hr : S.applyRow ρ with
    | none => simp only [hr] at h; cases h
    | some ρ' =>
      have e1 := applyRow_eq_rsb S ρ ρ' hr
      cases hf : FMap.find? S.row e with
      | none =>
        simp only [hr, hf, Option.some.injEq] at h; subst h
        rw [e1, rsb]; simp only [RSub.tl, Subst.toR, hf, Option.getD_none, mrg_nil_right]
      | some q =>
        obtain ⟨ρ2, tl⟩ := q
        cases hm : Row.merge ρ' ρ2 with
        | none => simp only [hr, hf, hm] at h; cases h
        | some ρ3 =>
          simp only [hr, hf, hm, Option.some.injEq] at h; subst h
          rw [merge_eq_mrg hm, e1, rsb]; simp only [RSub.tl, Subst.toR, hf, Option.getD_some]
  | .fn a b, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i a' b' ha hb
      cases h
      rw [rsb, ← apply_eq_rsb S a a' ha, ← apply_eq_rsb S b b' hb]
    · cases h
  | .con as t, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i as' hl
      cases h
      rw [rsb, ← applyList_eq_rsb S as as' hl]
    · cases h
theorem applyRow_eq_rsb (S : Subst) : ∀ (ρ ρ' : Row), S.applyRow ρ = some ρ' → ρ' = rsbRow S.toR ρ
  | [], ρ', h => by simp only [Subst.applyRow, Option.some.injEq] at h; subst h; rfl
  | (l, τ) :: r, ρ', h => by
    simp only [Subst.applyRow] at h
    split at h
    · rename_i τ' r' h1 h2
      cases h
      rw [rsbRow, ← apply_eq_rsb S τ τ' h1, ← applyRow_eq_rsb S r r' h2]
    · cases h
theorem applyList_eq_rsb (S : Subst) : ∀ (l l' : List Ty), S.applyList l = some l' → l' = rsbList S.toR l
  | [], l', h => by simp only [Subst.applyList, Option.some.injEq] at h; subst h; rfl
  | τ :: r, l', h => by
    simp only [Subst.applyList] at h
    split at h
    · rename_i τ' r' h1 h2
      cases h
      rw [rsbList, ← apply_eq_rsb S τ τ' h1, ← applyList_eq_rsb S r r' h2]
    · cases h
end

theorem find?_some_memB {K V : Type} [DecidableEq K] : ∀ {θ : FMap K V} {a : K} {τ : V},
    FMap.find? θ a = some τ → (a, τ) ∈ θ
  | [], _, _, h => by cases h
  | (b, u) :: r, a, τ, h => by
    simp only [FMap.find?] at h
    split at h
    · rename_i hb; cases h; subst hb; exact .head _
    · exact .tail _ (find?_some_memB h)

/-- A class-respecting step 9 substitution is a class-respecting `RSub`. -/
theorem respR_toR {S : Subst} (h : S.Respects) : RespR S.toR := fun a => by
  show Adm a.cls ((FMap.find? S.ty a).getD (.var a))
  cases hf : FMap.find? S.ty a with
  | none => exact admC_self a
  | some u => exact h _ (find?_some_memB hf)

/-- Outside its domain, step 9's substitution is the identity. -/
theorem toR_img_of_not_dom {S : Subst} {v : BVar} (h : v ∉ S.dom) : S.toR.img v = vty v := by
  cases v with
  | ty a => simp [RSub.img, Subst.toR, find?_none_of_not_mem_ty h, vty]
  | row e => simp [RSub.img, Subst.toR, find?_none_of_not_mem_row h, vty]

/-- An instance of a scheme is the image of its body under `rsb`, by a class-respecting
    substitution moving only the bound variables. -/
theorem gen_rsb {σ : Scheme} {τ : Ty} (h : Gen σ τ) :
    ∃ g : RSub, RespR g ∧ (∀ v, v ∉ σ.bound → g.img v = vty v) ∧ τ = rsb g σ.body := by
  obtain ⟨ts, S, hb, hr, ha⟩ := h
  exact ⟨S.toR, respR_toR hr, fun v hv => toR_img_of_not_dom fun hd => hv (bindSubst_dom hb v hd),
    apply_eq_rsb S _ _ ha⟩

/-! ## Definedness: disjoint labels -/

/-- On rows with disjoint labels (and enough fuel) the merge succeeds, and is `mrg`. -/
theorem mergeF_of_ldisj : ∀ (f : Nat) (a b : Row), a.length + b.length ≤ f → LDisj a b → Row.mergeF f a b = some (mrg a b)
  | _, [], b, _, _ => by simp only [Row.mergeF]; rfl
  | f, p :: r, [], _, _ => by cases f <;> simp only [Row.mergeF] <;> rfl
  | 0, _ :: _, _ :: _, h, _ => by simp at h
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2, hf, hd => by
    have hne : l1 ≠ l2 := hd _ (.head _) _ (.head _)
    simp only [Row.mergeF, if_neg hne]
    split
    · rename_i hlt
      rw [mergeF_of_ldisj f r1 _ (by simp at hf ⊢; omega) (fun x hx y hy => hd x (.tail _ hx) y hy), mrg_cons_cons,
        if_pos (fLe_iff.mpr (labLt_asymm hlt))]
    · rename_i hlt
      have h21 : labLt l2 l1 = true := by
        rcases labLt_tri l1 l2 with h' | h' | h'
        · exact absurd h' hlt
        · exact absurd h' hne
        · exact h'
      rw [mergeF_of_ldisj f _ r2 (by simp at hf ⊢; omega) (fun x hx y hy => hd x hx y (.tail _ hy)), mrg_cons_cons,
        if_neg (not_fLe.mpr h21)]

theorem merge_of_ldisj {a b : Row} (h : LDisj a b) : Row.merge a b = some (mrg a b) :=
  mergeF_of_ldisj _ a b (Nat.le_refl _) h

mutual
/-- Step 9's substitution is defined, and is `rsb`, wherever `rsb` gives a canonical image. -/
theorem apply_of_cn (S : Subst) : ∀ τ : Ty, cnB (rsb S.toR τ) = true → S.apply τ = some (rsb S.toR τ)
  | .var a, _ => rfl
  | .record ρ none, h => by
    have hf := (cnB_rsb_record.mp h).2.1
    simp only [Subst.apply, applyRow_of_cn S ρ hf, rsb, toR_tl_none, mrg_nil_right]
  | .record ρ (some e), h => by
    obtain ⟨hs, hf, -⟩ := cnB_rsb_record.mp h
    simp only [Subst.apply, applyRow_of_cn S ρ hf]
    cases hfe : FMap.find? S.row e with
    | none =>
      simp only [rsb, RSub.tl, Subst.toR, hfe, Option.getD_none, mrg_nil_right]
    | some q =>
      obtain ⟨ρ2, tl⟩ := q
      have hd : LDisj (rsbRow S.toR ρ) ρ2 := by
        have := (sorted_of_mrg hs).2.2
        simpa [RSub.tl, Subst.toR, hfe] using this
      simp only [hfe]
      rw [merge_of_ldisj hd]
      simp only [rsb, RSub.tl, Subst.toR, hfe, Option.getD_some]
  | .fn a b, h => by
    simp only [rsb, cnB, Bool.and_eq_true] at h
    simp only [Subst.apply, apply_of_cn S a h.1, apply_of_cn S b h.2, rsb]
  | .con as t, h => by
    simp only [rsb, cnB] at h
    simp only [Subst.apply, applyList_of_cn S as h, rsb]
theorem applyRow_of_cn (S : Subst) : ∀ ρ : Row, (∀ p ∈ ρ, cnB (rsb S.toR p.2) = true) → S.applyRow ρ = some (rsbRow S.toR ρ)
  | [], _ => rfl
  | (l, τ) :: r, h => by
    simp only [Subst.applyRow, apply_of_cn S τ (h _ (.head _)), applyRow_of_cn S r (fun p hp => h p (.tail _ hp)), rsbRow]
theorem applyList_of_cn (S : Subst) : ∀ l : List Ty, cnListB (rsbList S.toR l) = true → S.applyList l = some (rsbList S.toR l)
  | [], _ => rfl
  | τ :: r, h => by
    simp only [rsbList, cnListB, Bool.and_eq_true] at h
    simp only [Subst.applyList, apply_of_cn S τ h.1, applyList_of_cn S r h.2, rsbList]
end

/-- Step 9's binding of a scheme's bound variables to their images under `g`. -/
theorem bindSubst_img (g : RSub) : ∀ vs : List BVar, ∃ S, bindSubst vs (vs.map g.img) = some S ∧
    (∀ v, S.toR.img v = if v ∈ vs then g.img v else vty v) ∧ (∀ p ∈ S.ty, g.t p.1 = p.2)
  | [] => ⟨Subst.id, rfl, fun v => by cases v <;> rfl, fun _ h => nomatch h⟩
  | .ty a :: vs => by
    obtain ⟨S, h1, h2, h3⟩ := bindSubst_img g vs
    refine ⟨{ S with ty := (a, g.t a) :: S.ty }, by simp [bindSubst, RSub.img, h1], fun v => ?_, fun p hp => ?_⟩
    · by_cases e : v = .ty a
      · subst e; simp [RSub.img, Subst.toR, FMap.find?]
      · have hS : (Subst.toR { S with ty := (a, g.t a) :: S.ty }).img v = S.toR.img v := by
          cases v with
          | ty b =>
            have : b ≠ a := fun h => e (by rw [h])
            simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
          | row _ => rfl
        rw [hS, h2]
        by_cases hm : v ∈ vs
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        · rw [if_neg hm, if_neg (by simp [e, hm])]
    · rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact h3 p hp
  | .row e0 :: vs => by
    obtain ⟨S, h1, h2, h3⟩ := bindSubst_img g vs
    refine ⟨{ S with row := (e0, g.r e0) :: S.row }, by simp [bindSubst, RSub.img, h1], fun v => ?_, h3⟩
    by_cases e : v = .row e0
    · subst e; simp [RSub.img, Subst.toR, FMap.find?]
    · have hS : (Subst.toR { S with row := (e0, g.r e0) :: S.row }).img v = S.toR.img v := by
        cases v with
        | row b =>
          have : b ≠ e0 := fun h => e (by rw [h])
          simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
        | ty _ => rfl
      rw [hS, h2]
      by_cases hm : v ∈ vs
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
      · rw [if_neg hm, if_neg (by simp [e, hm])]

/-- A canonical image of a scheme's body, by a class-respecting substitution moving only its
    bound variables, is an instance of the scheme (the converse of `gen_rsb`). -/
theorem gen_of_rsb {σ : Scheme} {g : RSub} (hr : RespR g) (hout : ∀ v, v ∉ σ.bound → g.img v = vty v)
    (hc : cnB (rsb g σ.body) = true) : Gen σ (rsb g σ.body) := by
  obtain ⟨S, h1, h2, h3⟩ := bindSubst_img g σ.bound
  have hS : ∀ v, S.toR.img v = g.img v := fun v => by
    rw [h2]; split
    · rfl
    · rename_i hm; rw [hout v hm]
  have he : rsb S.toR σ.body = rsb g σ.body := rsb_congr _ fun w _ => hS w
  refine ⟨σ.bound.map g.img, S, h1, fun p hp => ?_, ?_⟩
  · rw [← h3 p hp]; exact hr p.1
  · rw [← he] at hc ⊢; exact apply_of_cn S _ hc

end StandardElm.Stat.Complete
