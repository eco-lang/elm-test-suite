/-
  A Standard Definition of Elm? Mechanisation: definedness of step 9's substitutions with rows,
  for the principality of W with records (plan step 11, milestone (d), section 7).

  Step 9's `Subst.apply` merges, at a record whose tail is bound, the substituted row with the
  bound row by `Row.merge`, which fails when the walk of the merge meets two equal labels. The
  rows of an instance of a scheme (`Gen`) may be unsorted (an instance list is any list of types),
  so the walk is not "the labels are disjoint"; it is `MOK` (the merge walk meets no equal labels,
  on the labels only).

  * `MOK`: `mergeF_of_mok`, `mok_of_mergeF` (the merge succeeds iff `MOK`, and is then `mrg`);
    `mok_congr` (labels only); `mok_of_ldisj`; and the three-way lemma `mok_assoc`: if the merge
    of `mrg A X` with `Z` succeeds and `A`, `X` have disjoint labels, the merge of `A` with
    `mrg X Z` succeeds.
  * `RecP P τ`: `P` holds at every record of `τ`. `DefR u τ` (`MOK` at every record, with the
    row of the image of its tail): `apply_of_defR`, `defR_of_apply` (step 9's substitution is
    defined iff `DefR`); `defR_rsb` and `recP_of_defR_rsb` (definedness on an image `w τ`, through
    the records of `τ`); `recP_of_cn` (a canonical image has disjoint labels at every record).
-/
import StandardElmMech.Stat.Complete.WDBridge

namespace StandardElm.Stat.Complete.WDP
open StandardElm (Lab)
open StandardElm.Stat
open StandardElm.Stat.Complete

/-! ## The merge walk -/

/-- The walk of `Row.merge` meets no two equal labels. -/
def MOK : Row → Row → Prop
  | [], _ => True
  | _ :: _, [] => True
  | p :: a, q :: b => p.1 ≠ q.1 ∧ (if labLt p.1 q.1 = true then MOK a (q :: b) else MOK (p :: a) b)
termination_by a b => a.length + b.length

theorem mok_nil_left (b : Row) : MOK [] b := by unfold MOK; trivial

theorem mok_nil_right : ∀ a : Row, MOK a []
  | [] => by unfold MOK; trivial
  | _ :: _ => by unfold MOK; trivial

theorem mok_cons {p q : Lab × Ty} {a b : Row} :
    MOK (p :: a) (q :: b) ↔ p.1 ≠ q.1 ∧ (if labLt p.1 q.1 = true then MOK a (q :: b) else MOK (p :: a) b) := by
  rw [MOK]

theorem mergeF_of_mok : ∀ (f : Nat) (a b : Row), a.length + b.length ≤ f → MOK a b → Row.mergeF f a b = some (mrg a b)
  | _, [], b, _, _ => by simp only [Row.mergeF]; rfl
  | f, p :: r, [], _, _ => by cases f <;> simp only [Row.mergeF] <;> rfl
  | 0, _ :: _, _ :: _, h, _ => by simp at h
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2, hf, hm => by
    rw [mok_cons] at hm
    obtain ⟨hne, hm⟩ := hm
    simp only at hne hm
    simp only [Row.mergeF, if_neg hne]
    split
    · rename_i hlt
      rw [if_pos hlt] at hm
      rw [mergeF_of_mok f r1 _ (by simp at hf ⊢; omega) hm, mrg_cons_cons,
        if_pos (fLe_iff.mpr (labLt_asymm hlt))]
    · rename_i hlt
      rw [if_neg hlt] at hm
      have h21 : labLt l2 l1 = true := by
        rcases labLt_tri l1 l2 with h' | h' | h'
        · exact absurd h' hlt
        · exact absurd h' hne
        · exact h'
      rw [mergeF_of_mok f _ r2 (by simp at hf ⊢; omega) hm, mrg_cons_cons, if_neg (not_fLe.mpr h21)]

theorem mok_of_mergeF : ∀ (f : Nat) (a b : Row) (c : Row), Row.mergeF f a b = some c → MOK a b
  | _, [], b, _, _ => mok_nil_left b
  | _, _ :: _, [], _, _ => mok_nil_right _
  | 0, _ :: _, _ :: _, _, h => by simp [Row.mergeF] at h
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2, c, h => by
    simp only [Row.mergeF] at h
    rw [mok_cons]
    split at h
    · cases h
    · rename_i hne
      refine ⟨hne, ?_⟩
      simp only
      split at h
      · rename_i hlt
        rw [if_pos hlt]
        split at h
        · rename_i r hr; exact mok_of_mergeF f _ _ _ hr
        · cases h
      · rename_i hlt
        rw [if_neg hlt]
        split at h
        · rename_i r hr; exact mok_of_mergeF f _ _ _ hr
        · cases h

theorem mok_of_merge {a b c : Row} (h : Row.merge a b = some c) : MOK a b := mok_of_mergeF _ _ _ _ h

theorem merge_of_mok {a b : Row} (h : MOK a b) : Row.merge a b = some (mrg a b) :=
  mergeF_of_mok _ a b (Nat.le_refl _) h

theorem labs_cons (p : Lab × Ty) (r : Row) : labs (p :: r) = p.1 :: labs r := rfl

/-- The walk depends on the labels only. -/
theorem mok_congr : ∀ (a b a' b' : Row), labs a = labs a' → labs b = labs b' → MOK a b → MOK a' b'
  | [], _, [], _, _, _, _ => mok_nil_left _
  | [], _, _ :: _, _, h, _, _ => by simp [labs] at h
  | _ :: _, _, [], _, h, _, _ => by simp [labs] at h
  | _ :: _, [], _ :: _, [], _, _, _ => mok_nil_right _
  | _ :: _, [], _ :: _, _ :: _, _, h, _ => by simp [labs] at h
  | _ :: _, _ :: _, _ :: _, [], _, h, _ => by simp [labs] at h
  | p :: a, q :: b, p' :: a', q' :: b', ha, hb, hm => by
    rw [labs_cons, labs_cons, List.cons.injEq] at ha hb
    rw [mok_cons] at hm ⊢
    rw [← ha.1, ← hb.1]
    refine ⟨hm.1, ?_⟩
    split
    · rename_i hlt
      rw [if_pos hlt] at hm
      exact mok_congr a (q :: b) a' (q' :: b') ha.2 (by rw [labs_cons, labs_cons, hb.1, hb.2]) hm.2
    · rename_i hlt
      rw [if_neg hlt] at hm
      exact mok_congr (p :: a) b (p' :: a') b' (by rw [labs_cons, labs_cons, ha.1, ha.2]) hb.2 hm.2
termination_by a b => a.length + b.length

theorem mok_of_ldisj : ∀ (a b : Row), LDisj a b → MOK a b
  | [], _, _ => mok_nil_left _
  | _ :: _, [], _ => mok_nil_right _
  | p :: a, q :: b, hd => by
    rw [mok_cons]
    refine ⟨hd p (.head _) q (.head _), ?_⟩
    split
    · exact mok_of_ldisj a (q :: b) fun x hx y hy => hd x (.tail _ hx) y hy
    · exact mok_of_ldisj (p :: a) b fun x hx y hy => hd x hx y (.tail _ hy)
termination_by a b => a.length + b.length

/-- The labels of a merge depend on the labels only. -/
theorem labs_mrg_congr : ∀ (a b a' b' : Row), labs a = labs a' → labs b = labs b' → labs (mrg a b) = labs (mrg a' b')
  | [], _, [], _, _, hb => by simpa [mrg_nil_left] using hb
  | [], _, _ :: _, _, h, _ => by simp [labs] at h
  | _ :: _, _, [], _, h, _ => by simp [labs] at h
  | _ :: _, [], _ :: _, [], ha, _ => by rw [mrg_nil_right, mrg_nil_right]; exact ha
  | _ :: _, [], _ :: _, _ :: _, _, h => by simp [labs] at h
  | _ :: _, _ :: _, _ :: _, [], _, h => by simp [labs] at h
  | p :: a, q :: b, p' :: a', q' :: b', ha, hb => by
    have ha' := ha; have hb' := hb
    rw [labs_cons, labs_cons, List.cons.injEq] at ha hb
    rw [mrg_cons_cons, mrg_cons_cons]
    have e : fLe p q = fLe p' q' := by simp only [fLe, ha.1, hb.1]
    rw [e]
    split
    · rw [labs_cons, labs_cons, ha.1, labs_mrg_congr a (q :: b) a' (q' :: b') ha.2 hb']
    · rw [labs_cons, labs_cons, hb.1, labs_mrg_congr (p :: a) b (p' :: a') b' ha' hb.2]
termination_by a b => a.length + b.length

theorem labLt_of_not {a b : Lab} (hne : a ≠ b) (h : ¬ labLt a b = true) : labLt b a = true := by
  rcases labLt_tri a b with h' | h' | h'
  · exact absurd h' h
  · exact absurd h' hne
  · exact h'

/-- The three-way lemma: the merge of `mrg A X` with `Z` succeeding and `A`, `X` disjoint, the
    merge of `A` with `mrg X Z` succeeds. -/
theorem mok_assoc : ∀ (A X Z : Row), MOK (mrg A X) Z → LDisj A X → MOK A (mrg X Z)
  | [], _, _, _, _ => mok_nil_left _
  | _ :: _, [], Z, h, _ => by rw [mrg_nil_right] at h; exact h
  | A, _ :: _, [], _, hd => by rw [mrg_nil_right]; exact mok_of_ldisj _ _ hd
  | a :: A, x :: X, z :: Z, h, hd => by
    have hax : a.1 ≠ x.1 := hd a (.head _) x (.head _)
    have hd1 : LDisj A (x :: X) := fun u hu v hv => hd u (.tail _ hu) v hv
    have hd2 : LDisj (a :: A) X := fun u hu v hv => hd u hu v (.tail _ hv)
    rw [mrg_cons_cons a x] at h
    rw [mrg_cons_cons x z]
    by_cases hlt : labLt a.1 x.1 = true
    · have hle : fLe a x = true := fLe_iff.mpr (labLt_asymm hlt)
      rw [if_pos hle, mok_cons] at h
      obtain ⟨haz, h⟩ := h
      by_cases hxz : fLe x z = true
      · rw [if_pos hxz, mok_cons, if_pos hlt]
        refine ⟨hax, ?_⟩
        have hxz' : labLt z.1 x.1 = false := fLe_iff.mp hxz
        have haz' : labLt a.1 z.1 = true := by
          rcases labLt_tri x.1 z.1 with h' | h' | h'
          · exact labLt_trans hlt h'
          · rw [← h']; exact hlt
          · rw [h'] at hxz'; cases hxz'
        rw [if_pos haz'] at h
        have := mok_assoc A (x :: X) (z :: Z) h hd1
        rwa [mrg_cons_cons x z, if_pos hxz] at this
      · rw [if_neg hxz, mok_cons]
        refine ⟨haz, ?_⟩
        split
        · rename_i haz'
          rw [if_pos haz'] at h
          have := mok_assoc A (x :: X) (z :: Z) h hd1
          rwa [mrg_cons_cons x z, if_neg hxz] at this
        · rename_i haz'
          rw [if_neg haz'] at h
          exact mok_assoc (a :: A) (x :: X) Z (by rw [mrg_cons_cons, if_pos hle]; exact h) hd
    · have hxa : labLt x.1 a.1 = true := labLt_of_not hax hlt
      have hle : ¬ fLe a x = true := not_fLe.mpr hxa
      rw [if_neg hle, mok_cons] at h
      obtain ⟨hxz, h⟩ := h
      by_cases hxz' : labLt x.1 z.1 = true
      · rw [if_pos hxz'] at h
        rw [if_pos (fLe_iff.mpr (labLt_asymm hxz')), mok_cons, if_neg hlt]
        exact ⟨hax, mok_assoc (a :: A) X (z :: Z) h hd2⟩
      · rw [if_neg hxz'] at h
        have hzx : labLt z.1 x.1 = true := labLt_of_not hxz hxz'
        have hza : labLt z.1 a.1 = true := labLt_trans hzx hxa
        rw [if_neg (not_fLe.mpr hzx), mok_cons]
        refine ⟨fun e => (by rw [e, labLt_irrefl] at hza; cases hza), ?_⟩
        rw [if_neg (by rw [labLt_asymm hza]; simp)]
        have h' : MOK (mrg (a :: A) (x :: X)) Z := by rwa [mrg_cons_cons, if_neg hle]
        exact mok_assoc (a :: A) (x :: X) Z h' hd
termination_by A X Z => A.length + X.length + Z.length

/-! ## A property at every record -/

mutual
/-- `P` holds at every record of a type. -/
def RecP (P : Row → Option RowVar → Prop) : Ty → Prop
  | .var _ => True
  | .record ρ tl => P ρ tl ∧ RecPRow P ρ
  | .fn a b => RecP P a ∧ RecP P b
  | .con as _ => RecPList P as
def RecPRow (P : Row → Option RowVar → Prop) : Row → Prop
  | [] => True
  | (_, τ) :: rest => RecP P τ ∧ RecPRow P rest
def RecPList (P : Row → Option RowVar → Prop) : List Ty → Prop
  | [] => True
  | τ :: rest => RecP P τ ∧ RecPList P rest
end

theorem recPRow_iff {P : Row → Option RowVar → Prop} : ∀ {ρ : Row}, RecPRow P ρ ↔ ∀ p ∈ ρ, RecP P p.2
  | [] => by simp [RecPRow]
  | (l, x) :: r => by
    simp only [RecPRow, recPRow_iff (ρ := r), List.mem_cons, forall_eq_or_imp]

theorem recPList_iff {P : Row → Option RowVar → Prop} : ∀ {l : List Ty}, RecPList P l ↔ ∀ τ ∈ l, RecP P τ
  | [] => by simp [RecPList]
  | x :: r => by
    simp only [RecPList, recPList_iff (l := r), List.mem_cons, forall_eq_or_imp]

mutual
theorem RecP.mono2 {P Q R : Row → Option RowVar → Prop} (hPQ : ∀ ρ tl, P ρ tl → Q ρ tl → R ρ tl) :
    ∀ {τ : Ty}, RecP P τ → RecP Q τ → RecP R τ
  | .var _, _, _ => trivial
  | .record ρ tl, h1, h2 => ⟨hPQ ρ tl h1.1 h2.1, RecPRow.mono2 hPQ h1.2 h2.2⟩
  | .fn a b, h1, h2 => ⟨RecP.mono2 hPQ h1.1 h2.1, RecP.mono2 hPQ h1.2 h2.2⟩
  | .con as _, h1, h2 => RecPList.mono2 hPQ h1 h2
theorem RecPRow.mono2 {P Q R : Row → Option RowVar → Prop} (hPQ : ∀ ρ tl, P ρ tl → Q ρ tl → R ρ tl) :
    ∀ {ρ : Row}, RecPRow P ρ → RecPRow Q ρ → RecPRow R ρ
  | [], _, _ => trivial
  | (_, _) :: _, h1, h2 => ⟨RecP.mono2 hPQ h1.1 h2.1, RecPRow.mono2 hPQ h1.2 h2.2⟩
theorem RecPList.mono2 {P Q R : Row → Option RowVar → Prop} (hPQ : ∀ ρ tl, P ρ tl → Q ρ tl → R ρ tl) :
    ∀ {l : List Ty}, RecPList P l → RecPList Q l → RecPList R l
  | [], _, _ => trivial
  | _ :: _, h1, h2 => ⟨RecP.mono2 hPQ h1.1 h2.1, RecPList.mono2 hPQ h1.2 h2.2⟩
end

mutual
/-- Every record of a type has its tail among the type's variables. -/
theorem recP_tails : ∀ (τ : Ty), RecP (fun _ tl => ∀ e, tl = some e → BVar.row e ∈ τ.vars) τ
  | .var _ => trivial
  | .record ρ tl => by
    refine ⟨fun e he => by subst he; simp [Ty.vars], ?_⟩
    have := recPRow_tails ρ
    rw [recPRow_iff] at this ⊢
    intro p hp
    refine RecP.mono2 (fun _ _ h _ e he => ?_) (this p hp) (this p hp)
    have := h e he
    cases tl <;> simp [Ty.vars, this]
  | .fn a b => by
    refine ⟨RecP.mono2 (fun _ _ h _ e he => ?_) (recP_tails a) (recP_tails a),
      RecP.mono2 (fun _ _ h _ e he => ?_) (recP_tails b) (recP_tails b)⟩
    · simp [Ty.vars, h e he]
    · simp [Ty.vars, h e he]
  | .con as _ => by
    have := recPList_tails as
    show RecPList _ as
    rw [recPList_iff] at this ⊢
    intro τ hτ
    exact RecP.mono2 (fun _ _ h _ e he => by simp [Ty.vars, h e he]) (this τ hτ) (this τ hτ)
theorem recPRow_tails : ∀ (ρ : Row), RecPRow (fun _ tl => ∀ e, tl = some e → BVar.row e ∈ Ty.rowVars ρ) ρ
  | [] => trivial
  | (l, x) :: r => by
    refine ⟨RecP.mono2 (fun _ _ h _ e he => ?_) (recP_tails x) (recP_tails x), ?_⟩
    · simp [Ty.rowVars, h e he]
    · have := recPRow_tails r
      rw [recPRow_iff] at this ⊢
      intro p hp
      exact RecP.mono2 (fun _ _ h _ e he => by simp [Ty.rowVars, h e he]) (this p hp) (this p hp)
theorem recPList_tails : ∀ (l : List Ty), RecPList (fun _ tl => ∀ e, tl = some e → BVar.row e ∈ Ty.listVars l) l
  | [] => trivial
  | x :: r => by
    refine ⟨RecP.mono2 (fun _ _ h _ e he => ?_) (recP_tails x) (recP_tails x), ?_⟩
    · simp [Ty.listVars, h e he]
    · have := recPList_tails r
      rw [recPList_iff] at this ⊢
      intro τ hτ
      exact RecP.mono2 (fun _ _ h _ e he => by simp [Ty.listVars, h e he]) (this τ hτ) (this τ hτ)
end

/-! ## Definedness -/

/-- `u` is defined on `τ` in step 9's sense: the merge walk succeeds at every record. -/
def DefR (u : RSub) (τ : Ty) : Prop := RecP (fun ρ tl => MOK ρ (u.tl tl).1) τ

theorem defR_vty (u : RSub) : ∀ v, DefR u (vty v)
  | .ty _ => trivial
  | .row _ => ⟨mok_nil_left _, trivial⟩

theorem mok_rsbRow {s : RSub} {ρ b : Row} : MOK (rsbRow s ρ) b ↔ MOK ρ b :=
  ⟨mok_congr _ _ _ _ (labs_rsbRow s ρ) rfl, mok_congr _ _ _ _ (labs_rsbRow s ρ).symm rfl⟩

mutual
/-- Step 9's substitution is defined, and is `rsb`, where `DefR` holds. -/
theorem apply_of_defR (S : Subst) : ∀ τ : Ty, DefR S.toR τ → S.apply τ = some (rsb S.toR τ)
  | .var a, _ => rfl
  | .record ρ none, h => by
    simp only [Subst.apply, applyRow_of_defR S ρ (recPRow_iff.mp h.2), rsb, toR_tl_none, mrg_nil_right]
  | .record ρ (some e), h => by
    obtain ⟨hm, hf⟩ := h
    simp only [Subst.apply, applyRow_of_defR S ρ (recPRow_iff.mp hf)]
    cases hfe : FMap.find? S.row e with
    | none =>
      simp only [rsb, RSub.tl, Subst.toR, hfe, Option.getD_none, mrg_nil_right]
    | some q =>
      obtain ⟨ρ2, tl⟩ := q
      have hd : MOK (rsbRow S.toR ρ) ρ2 := by
        apply mok_rsbRow.mpr
        simpa [RSub.tl, Subst.toR, hfe] using hm
      simp only [hfe]
      rw [merge_of_mok hd]
      simp only [rsb, RSub.tl, Subst.toR, hfe, Option.getD_some]
  | .fn a b, h => by
    simp only [Subst.apply, apply_of_defR S a h.1, apply_of_defR S b h.2, rsb]
  | .con as t, h => by
    simp only [Subst.apply, applyList_of_defR S as (recPList_iff.mp h), rsb]
theorem applyRow_of_defR (S : Subst) : ∀ ρ : Row, (∀ p ∈ ρ, DefR S.toR p.2) → S.applyRow ρ = some (rsbRow S.toR ρ)
  | [], _ => rfl
  | (l, τ) :: r, h => by
    simp only [Subst.applyRow, apply_of_defR S τ (h _ (.head _)), applyRow_of_defR S r (fun p hp => h p (.tail _ hp)), rsbRow]
theorem applyList_of_defR (S : Subst) : ∀ l : List Ty, (∀ τ ∈ l, DefR S.toR τ) → S.applyList l = some (rsbList S.toR l)
  | [], _ => rfl
  | τ :: r, h => by
    simp only [Subst.applyList, apply_of_defR S τ (h _ (.head _)), applyList_of_defR S r (fun x hx => h x (.tail _ hx)), rsbList]
end

mutual
/-- Where step 9's substitution is defined, `DefR` holds. -/
theorem defR_of_apply (S : Subst) : ∀ (τ τ' : Ty), S.apply τ = some τ' → DefR S.toR τ
  | .var a, _, _ => trivial
  | .record ρ none, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i ρ' hr
      exact ⟨by simpa [toR_tl_none] using mok_nil_right ρ, recPRow_iff.mpr (defR_of_applyRow S ρ ρ' hr)⟩
    · cases h
  | .record ρ (some e), τ', h => by
    simp only [Subst.apply] at h
    cases hr : S.applyRow ρ with
    | none => simp only [hr] at h; cases h
    | some ρ' =>
      have e1 := applyRow_eq_rsb S ρ ρ' hr
      refine ⟨?_, recPRow_iff.mpr (defR_of_applyRow S ρ ρ' hr)⟩
      cases hf : FMap.find? S.row e with
      | none => simp only [RSub.tl, Subst.toR, hf, Option.getD_none]; exact mok_nil_right _
      | some q =>
        obtain ⟨ρ2, tl⟩ := q
        cases hm : Row.merge ρ' ρ2 with
        | none => simp only [hr, hf, hm] at h; cases h
        | some ρ3 =>
          simp only [RSub.tl, Subst.toR, hf, Option.getD_some]
          have := mok_of_merge hm
          rw [e1] at this
          exact mok_rsbRow.mp this
  | .fn a b, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i a' b' ha hb
      exact ⟨defR_of_apply S a a' ha, defR_of_apply S b b' hb⟩
    · cases h
  | .con as t, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i as' hl
      exact recPList_iff.mpr (defR_of_applyList S as as' hl)
    · cases h
theorem defR_of_applyRow (S : Subst) : ∀ (ρ ρ' : Row), S.applyRow ρ = some ρ' → ∀ p ∈ ρ, DefR S.toR p.2
  | [], _, _ => fun _ h => nomatch h
  | (l, τ) :: r, ρ', h => by
    simp only [Subst.applyRow] at h
    split at h
    · rename_i τ' r' h1 h2
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact defR_of_apply S τ τ' h1
      · exact defR_of_applyRow S r r' h2 p hp
    · cases h
theorem defR_of_applyList (S : Subst) : ∀ (l l' : List Ty), S.applyList l = some l' → ∀ τ ∈ l, DefR S.toR τ
  | [], _, _ => fun _ h => nomatch h
  | x :: r, l', h => by
    simp only [Subst.applyList] at h
    split at h
    · rename_i τ' r' h1 h2
      intro τ hτ
      rcases List.mem_cons.mp hτ with e0 | hτ
      · rw [e0]; exact defR_of_apply S x τ' h1
      · exact defR_of_applyList S r r' h2 τ hτ
    · cases h
end

/-! ## Definedness on an image -/

/-- The condition at a record `⟨ρ | tl⟩` of `τ` for `u` to be defined on `w τ`. -/
def ImgOK (u w : RSub) (ρ : Row) (tl : Option RowVar) : Prop :=
  MOK (mrg (rsbRow w ρ) (w.tl tl).1) (u.tl (w.tl tl).2).1

theorem defR_tl_fields {u w : RSub} {tl : Option RowVar} (h : ∀ e, tl = some e → DefR u (w.img (.row e))) :
    ∀ p ∈ (w.tl tl).1, DefR u p.2 := by
  cases tl with
  | none => intro p hp; cases hp
  | some e => exact recPRow_iff.mp (h e rfl).2

mutual
theorem defR_rsb {u w : RSub} : ∀ τ : Ty, (∀ c ∈ τ.vars, DefR u (w.img c)) → RecP (ImgOK u w) τ →
    DefR u (rsb w τ)
  | .var a, hv, _ => hv (.ty a) (by simp [Ty.vars])
  | .record ρ tl, hv, h => by
    refine ⟨h.1, recPRow_iff.mpr fun p hp => ?_⟩
    rcases mem_mrg.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := mem_rsbRow.mp hp
      exact defR_rsbRow ρ (fun c hc => hv c (by rw [vars_record]; exact List.mem_append_left _ hc))
        (recPRow_iff.mp h.2) q hq
    · exact defR_tl_fields (fun e he => hv _ (by subst he; simp [Ty.vars])) p hp
  | .fn a b, hv, h =>
    ⟨defR_rsb a (fun c hc => hv c (by simp [Ty.vars, hc])) h.1,
      defR_rsb b (fun c hc => hv c (by simp [Ty.vars, hc])) h.2⟩
  | .con as _, hv, h => by
    show RecPList _ (rsbList w as)
    rw [recPList_iff, rsbList_eq]
    intro τ hτ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hτ
    exact defR_rsbList as (fun c hc => hv c (by simpa [Ty.vars] using hc)) (recPList_iff.mp h) x hx
theorem defR_rsbRow {u w : RSub} : ∀ ρ : Row, (∀ c ∈ Ty.rowVars ρ, DefR u (w.img c)) → (∀ p ∈ ρ, RecP (ImgOK u w) p.2) →
    ∀ p ∈ ρ, DefR u (rsb w p.2)
  | [], _, _, _, hp => nomatch hp
  | (l, x) :: r, hv, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact defR_rsb x (fun c hc => hv c (by simp [Ty.rowVars, hc])) (h _ (.head _))
    · exact defR_rsbRow r (fun c hc => hv c (by simp [Ty.rowVars, hc])) (fun q hq => h q (.tail _ hq)) p hp
theorem defR_rsbList {u w : RSub} : ∀ l : List Ty, (∀ c ∈ Ty.listVars l, DefR u (w.img c)) → (∀ τ ∈ l, RecP (ImgOK u w) τ) →
    ∀ τ ∈ l, DefR u (rsb w τ)
  | [], _, _, _, hp => nomatch hp
  | x :: r, hv, h, τ, hτ => by
    rcases List.mem_cons.mp hτ with e0 | hτ
    · rw [e0]; exact defR_rsb x (fun c hc => hv c (by simp [Ty.listVars, hc])) (h _ (.head _))
    · exact defR_rsbList r (fun c hc => hv c (by simp [Ty.listVars, hc])) (fun q hq => h q (.tail _ hq)) τ hτ
end

mutual
theorem recP_of_defR_rsb {u w : RSub} : ∀ τ : Ty, DefR u (rsb w τ) → RecP (ImgOK u w) τ
  | .var _, _ => trivial
  | .record ρ tl, h => by
    refine ⟨h.1, recPRow_iff.mpr (recP_of_defR_rsbRow ρ fun p hp => ?_)⟩
    exact recPRow_iff.mp h.2 (p.1, rsb w p.2) (mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨p, hp, rfl⟩)))
  | .fn a b, h => ⟨recP_of_defR_rsb a h.1, recP_of_defR_rsb b h.2⟩
  | .con as _, h => by
    have h' : RecPList _ (rsbList w as) := h
    rw [recPList_iff, rsbList_eq] at h'
    exact recPList_iff.mpr (recP_of_defR_rsbList as fun τ hτ => h' _ (List.mem_map_of_mem hτ))
theorem recP_of_defR_rsbRow {u w : RSub} : ∀ ρ : Row, (∀ p ∈ ρ, DefR u (rsb w p.2)) → ∀ p ∈ ρ, RecP (ImgOK u w) p.2
  | [], _, _, hp => nomatch hp
  | (l, x) :: r, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact recP_of_defR_rsb x (h _ (.head _))
    · exact recP_of_defR_rsbRow r (fun q hq => h q (.tail _ hq)) p hp
theorem recP_of_defR_rsbList {u w : RSub} : ∀ l : List Ty, (∀ τ ∈ l, DefR u (rsb w τ)) → ∀ τ ∈ l, RecP (ImgOK u w) τ
  | [], _, _, hp => nomatch hp
  | x :: r, h, τ, hτ => by
    rcases List.mem_cons.mp hτ with e0 | hτ
    · rw [e0]; exact recP_of_defR_rsb x (h _ (.head _))
    · exact recP_of_defR_rsbList r (fun q hq => h q (.tail _ hq)) τ hτ
end

mutual
/-- A canonical image has, at every record, the substituted row disjoint from the tail's row. -/
theorem recP_of_cn {s : RSub} : ∀ τ : Ty, cnB (rsb s τ) = true → RecP (fun ρ tl => LDisj (rsbRow s ρ) (s.tl tl).1) τ
  | .var _, _ => trivial
  | .record ρ tl, h => by
    obtain ⟨h1, h2, -⟩ := cnB_rsb_record.mp h
    exact ⟨(sorted_of_mrg h1).2.2, recPRow_iff.mpr (recP_of_cnRow ρ h2)⟩
  | .fn a b, h => by
    simp only [rsb, cnB, Bool.and_eq_true] at h
    exact ⟨recP_of_cn a h.1, recP_of_cn b h.2⟩
  | .con as _, h => by
    simp only [rsb, cnB, cnListB_iff, rsbList_eq, List.mem_map] at h
    exact recPList_iff.mpr (recP_of_cnList as fun τ hτ => h _ ⟨τ, hτ, rfl⟩)
theorem recP_of_cnRow {s : RSub} : ∀ ρ : Row, (∀ p ∈ ρ, cnB (rsb s p.2) = true) →
    ∀ p ∈ ρ, RecP (fun ρ tl => LDisj (rsbRow s ρ) (s.tl tl).1) p.2
  | [], _, _, hp => nomatch hp
  | (l, x) :: r, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact recP_of_cn x (h _ (.head _))
    · exact recP_of_cnRow r (fun q hq => h q (.tail _ hq)) p hp
theorem recP_of_cnList {s : RSub} : ∀ l : List Ty, (∀ τ ∈ l, cnB (rsb s τ) = true) →
    ∀ τ ∈ l, RecP (fun ρ tl => LDisj (rsbRow s ρ) (s.tl tl).1) τ
  | [], _, _, hp => nomatch hp
  | x :: r, h, τ, hτ => by
    rcases List.mem_cons.mp hτ with e0 | hτ
    · rw [e0]; exact recP_of_cn x (h _ (.head _))
    · exact recP_of_cnList r (fun q hq => h q (.tail _ hq)) τ hτ
end

mutual
/-- A substitution whose row images have empty rows on the tails of `τ` is defined on `τ`. -/
theorem defR_of_tails {u : RSub} : ∀ τ : Ty, (∀ e, BVar.row e ∈ τ.vars → (u.r e).1 = []) → DefR u τ
  | .var _, _ => trivial
  | .record ρ tl, h => by
    refine ⟨?_, recPRow_iff.mpr (defR_of_tailsRow ρ fun e he => h e (by rw [vars_record]; exact List.mem_append_left _ he))⟩
    cases tl with
    | none => exact mok_nil_right _
    | some e => simp only [RSub.tl, h e (by simp [Ty.vars])]; exact mok_nil_right _
  | .fn a b, h => ⟨defR_of_tails a fun e he => h e (by simp [Ty.vars, he]),
      defR_of_tails b fun e he => h e (by simp [Ty.vars, he])⟩
  | .con as _, h => recPList_iff.mpr (defR_of_tailsList as fun e he => h e (by simpa [Ty.vars] using he))
theorem defR_of_tailsRow {u : RSub} : ∀ ρ : Row, (∀ e, BVar.row e ∈ Ty.rowVars ρ → (u.r e).1 = []) → ∀ p ∈ ρ, DefR u p.2
  | [], _, _, hp => nomatch hp
  | (l, x) :: r, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact defR_of_tails x fun e he => h e (by simp [Ty.rowVars, he])
    · exact defR_of_tailsRow r (fun e he => h e (by simp [Ty.rowVars, he])) p hp
theorem defR_of_tailsList {u : RSub} : ∀ l : List Ty, (∀ e, BVar.row e ∈ Ty.listVars l → (u.r e).1 = []) → ∀ τ ∈ l, DefR u τ
  | [], _, _, hp => nomatch hp
  | x :: r, h, τ, hτ => by
    rcases List.mem_cons.mp hτ with e0 | hτ
    · rw [e0]; exact defR_of_tails x fun e he => h e (by simp [Ty.listVars, he])
    · exact defR_of_tailsList r (fun e he => h e (by simp [Ty.listVars, he])) τ hτ
end

end StandardElm.Stat.Complete.WDP
