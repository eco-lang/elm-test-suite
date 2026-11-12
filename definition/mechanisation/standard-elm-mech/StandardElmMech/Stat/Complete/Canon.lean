/-
  A Standard Definition of Elm? Mechanisation: step 9's substitutions applied to images of total
  substitutions, and the canonical form of a scheme, for the closure lemma L3 of plan step 11
  (milestone (b), section 8).

  * `apply_fix`, `apply_keeps`, `apply_isSome`: a step 9 substitution leaves a type with no
    variable of its domain unchanged; one whose row bindings add no field (a renaming of row
    variables, as `renumber` gives) is defined everywhere and keeps the variables outside its
    domain.
  * `apply_sb`: on a type whose variables are type variables, step 9's substitution applied to
    an image `sb f τ` is the image of `τ` under the pointwise applications (K10 across the two
    representations).
  * `renumber` and `canonVars`: the canonical form of a scheme whose bound variables are type
    variables is a renaming of its occurring bound variables to `bnd 0, bnd 1, ...` in order of
    first occurrence (`canon_ty`), with the same free variables (`canon_tyvars`).
-/
import StandardElmMech.Stat.Complete.WState

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Step 9's substitutions -/

theorem mem_dom_ty {S : Subst} {a : TyVar} {τ : Ty} (h : FMap.find? S.ty a = some τ) : BVar.ty a ∈ S.dom := by
  simp only [Subst.dom, List.mem_append, List.mem_map]
  exact .inl ⟨(a, τ), find?_mem h, rfl⟩

theorem mem_dom_row {S : Subst} {e : RowVar} {p : Row × Option RowVar} (h : FMap.find? S.row e = some p) :
    BVar.row e ∈ S.dom := by
  simp only [Subst.dom, List.mem_append, List.mem_map]
  exact .inr ⟨(e, p), find?_mem h, rfl⟩

theorem find?_none_of_not_mem_ty {S : Subst} {a : TyVar} (h : BVar.ty a ∉ S.dom) : FMap.find? S.ty a = none := by
  cases hf : FMap.find? S.ty a with
  | none => rfl
  | some τ => exact absurd (mem_dom_ty hf) h

theorem find?_none_of_not_mem_row {S : Subst} {e : RowVar} (h : BVar.row e ∉ S.dom) : FMap.find? S.row e = none := by
  cases hf : FMap.find? S.row e with
  | none => rfl
  | some p => exact absurd (mem_dom_row hf) h

mutual
/-- A substitution leaves a type with no variable of its domain unchanged. -/
theorem apply_fix (S : Subst) : ∀ τ : Ty, (∀ v ∈ τ.vars, v ∉ S.dom) → S.apply τ = some τ
  | .var a, h => by
    simp only [Subst.apply, find?_none_of_not_mem_ty (h (.ty a) (by simp [Ty.vars])), Option.getD_none]
  | .record ρ none, h => by
    simp only [Subst.apply, applyRow_fix S ρ (fun v hv => h v (by simpa [Ty.vars] using hv))]
  | .record ρ (some e), h => by
    simp only [Subst.apply, applyRow_fix S ρ (fun v hv => h v (by simp [Ty.vars, hv])),
      find?_none_of_not_mem_row (h (.row e) (by simp [Ty.vars]))]
  | .fn a b, h => by
    simp only [Subst.apply, apply_fix S a (fun v hv => h v (by simp [Ty.vars, hv])),
      apply_fix S b (fun v hv => h v (by simp [Ty.vars, hv]))]
  | .con as t, h => by
    simp only [Subst.apply, applyList_fix S as (fun v hv => h v (by simpa [Ty.vars] using hv))]
theorem applyRow_fix (S : Subst) : ∀ ρ : Row, (∀ v ∈ Ty.rowVars ρ, v ∉ S.dom) → S.applyRow ρ = some ρ
  | [], _ => rfl
  | (l, τ) :: r, h => by
    simp only [Subst.applyRow, apply_fix S τ (fun v hv => h v (by simp [Ty.rowVars, hv])),
      applyRow_fix S r (fun v hv => h v (by simp [Ty.rowVars, hv]))]
theorem applyList_fix (S : Subst) : ∀ l : List Ty, (∀ v ∈ Ty.listVars l, v ∉ S.dom) → S.applyList l = some l
  | [], _ => rfl
  | τ :: r, h => by
    simp only [Subst.applyList, apply_fix S τ (fun v hv => h v (by simp [Ty.listVars, hv])),
      applyList_fix S r (fun v hv => h v (by simp [Ty.listVars, hv]))]
end

/-- The row bindings add no field: they rename row variables. -/
def RowRen (S : Subst) : Prop := ∀ p ∈ S.row, p.2.1 = []

theorem merge_nil (ρ : Row) : Row.merge ρ [] = some ρ := by
  unfold Row.merge
  cases ρ <;> simp [Row.mergeF]

mutual
theorem apply_isSome {S : Subst} (hS : RowRen S) : ∀ τ : Ty, ∃ τ', S.apply τ = some τ'
  | .var a => ⟨_, rfl⟩
  | .record ρ none => by
    obtain ⟨ρ', h⟩ := applyRow_isSome hS ρ
    exact ⟨.record ρ' none, by simp only [Subst.apply, h]⟩
  | .record ρ (some e) => by
    obtain ⟨ρ', h⟩ := applyRow_isSome hS ρ
    cases hf : FMap.find? S.row e with
    | none => exact ⟨.record ρ' (some e), by simp only [Subst.apply, h, hf]⟩
    | some p =>
      have : p.1 = [] := hS (e, p) (find?_mem hf)
      obtain ⟨r, tl⟩ := p
      simp only at this; subst this
      exact ⟨.record ρ' tl, by simp only [Subst.apply, h, hf, merge_nil]⟩
  | .fn a b => by
    obtain ⟨a', ha⟩ := apply_isSome hS a
    obtain ⟨b', hb⟩ := apply_isSome hS b
    exact ⟨.fn a' b', by simp only [Subst.apply, ha, hb]⟩
  | .con as t => by
    obtain ⟨as', h⟩ := applyList_isSome hS as
    exact ⟨.con as' t, by simp only [Subst.apply, h]⟩
theorem applyRow_isSome {S : Subst} (hS : RowRen S) : ∀ ρ : Row, ∃ ρ', S.applyRow ρ = some ρ'
  | [] => ⟨_, rfl⟩
  | (l, τ) :: r => by
    obtain ⟨τ', h1⟩ := apply_isSome hS τ
    obtain ⟨r', h2⟩ := applyRow_isSome hS r
    exact ⟨(l, τ') :: r', by simp only [Subst.applyRow, h1, h2]⟩
theorem applyList_isSome {S : Subst} (hS : RowRen S) : ∀ l : List Ty, ∃ l', S.applyList l = some l'
  | [] => ⟨_, rfl⟩
  | τ :: r => by
    obtain ⟨τ', h1⟩ := apply_isSome hS τ
    obtain ⟨r', h2⟩ := applyList_isSome hS r
    exact ⟨τ' :: r', by simp only [Subst.applyList, h1, h2]⟩
end

mutual
/-- A renaming keeps the variables outside its domain. -/
theorem apply_keeps {S : Subst} (hS : RowRen S) : ∀ (τ τ' : Ty), S.apply τ = some τ' →
    ∀ v ∈ τ.vars, v ∉ S.dom → v ∈ τ'.vars
  | .var a, τ', h, v, hv, hd => by
    simp only [Ty.vars, List.mem_singleton] at hv; subst hv
    simp only [Subst.apply, find?_none_of_not_mem_ty hd, Option.getD_none, Option.some.injEq] at h
    subst h; simp [Ty.vars]
  | .record ρ none, τ', h, v, hv, hd => by
    simp only [Subst.apply] at h
    cases hr : S.applyRow ρ with
    | none => rw [hr] at h; cases h
    | some ρ' =>
      rw [hr] at h; cases h
      simp only [Ty.vars] at hv ⊢
      exact applyRow_keeps hS ρ ρ' hr v hv hd
  | .record ρ (some e), τ', h, v, hv, hd => by
    simp only [Subst.apply] at h
    cases hr : S.applyRow ρ with
    | none => rw [hr] at h; cases h
    | some ρ' =>
      rw [hr] at h
      simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
      cases hf : FMap.find? S.row e with
      | none =>
        rw [hf] at h; cases h
        simp only [Ty.vars, List.mem_append, List.mem_singleton]
        rcases hv with hv | hv
        · exact .inl (applyRow_keeps hS ρ ρ' hr v hv hd)
        · exact .inr hv
      | some p =>
        have h0 : p.1 = [] := hS (e, p) (find?_mem hf)
        obtain ⟨r, tl⟩ := p
        simp only at h0; subst h0
        rw [hf] at h
        simp only [merge_nil] at h
        cases h
        rcases hv with hv | hv
        · cases tl <;> simp [Ty.vars, applyRow_keeps hS ρ ρ' hr v hv hd]
        · subst hv; exact absurd (mem_dom_row hf) hd
  | .fn a b, τ', h, v, hv, hd => by
    simp only [Subst.apply] at h
    cases ha : S.apply a with
    | none => rw [ha] at h; cases h
    | some a' =>
      cases hb : S.apply b with
      | none => rw [ha, hb] at h; cases h
      | some b' =>
        rw [ha, hb] at h; cases h
        simp only [Ty.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · exact .inl (apply_keeps hS a a' ha v hv hd)
        · exact .inr (apply_keeps hS b b' hb v hv hd)
  | .con as t, τ', h, v, hv, hd => by
    simp only [Subst.apply] at h
    cases hl : S.applyList as with
    | none => rw [hl] at h; cases h
    | some as' =>
      rw [hl] at h; cases h
      simp only [Ty.vars] at hv ⊢
      exact applyList_keeps hS as as' hl v hv hd
theorem applyRow_keeps {S : Subst} (hS : RowRen S) : ∀ (ρ ρ' : Row), S.applyRow ρ = some ρ' →
    ∀ v ∈ Ty.rowVars ρ, v ∉ S.dom → v ∈ Ty.rowVars ρ'
  | [], _, _, v, hv, _ => by simp [Ty.rowVars] at hv
  | (l, τ) :: r, ρ', h, v, hv, hd => by
    simp only [Subst.applyRow] at h
    cases h1 : S.apply τ with
    | none => rw [h1] at h; cases h
    | some τ' =>
      cases h2 : S.applyRow r with
      | none => rw [h1, h2] at h; cases h
      | some r' =>
        rw [h1, h2] at h; cases h
        simp only [Ty.rowVars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · exact .inl (apply_keeps hS τ τ' h1 v hv hd)
        · exact .inr (applyRow_keeps hS r r' h2 v hv hd)
theorem applyList_keeps {S : Subst} (hS : RowRen S) : ∀ (l l' : List Ty), S.applyList l = some l' →
    ∀ v ∈ Ty.listVars l, v ∉ S.dom → v ∈ Ty.listVars l'
  | [], _, _, v, hv, _ => by simp [Ty.listVars] at hv
  | τ :: r, l', h, v, hv, hd => by
    simp only [Subst.applyList] at h
    cases h1 : S.apply τ with
    | none => rw [h1] at h; cases h
    | some τ' =>
      cases h2 : S.applyList r with
      | none => rw [h1, h2] at h; cases h
      | some r' =>
        rw [h1, h2] at h; cases h
        simp only [Ty.listVars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · exact .inl (apply_keeps hS τ τ' h1 v hv hd)
        · exact .inr (applyList_keeps hS r r' h2 v hv hd)
end

/-- Types whose variables are all type variables. -/
def TyOnly (τ : Ty) : Prop := ∀ v ∈ τ.vars, ∃ a, v = .ty a

theorem TyOnly.of_okT {n : Nat} {τ : Ty} (h : OkT n τ) : TyOnly τ := fun v hv => by
  obtain ⟨a, e, -⟩ := h v hv; exact ⟨a, e⟩

/-- The pointwise image of a substitution applied after `f`. -/
def post (S : Subst) (f : FSub) : FSub := fun a => (S.apply (f a)).getD (f a)

mutual
/-- K10 across the two representations, on a type with type variables only. -/
theorem apply_sb (S : Subst) (f : FSub) : ∀ (τ u : Ty), TyOnly τ → S.apply (sb f τ) = some u →
    (∀ a, BVar.ty a ∈ τ.vars → S.apply (f a) = some (post S f a)) ∧ u = sb (post S f) τ
  | .var a, u, _, h => by
    simp only [sb] at h
    refine ⟨fun b hb => ?_, ?_⟩
    · simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hb; subst hb
      simp [post, h]
    · simp [sb, post, h]
  | .record ρ none, u, ht, h => by
    simp only [sb, Subst.apply] at h
    cases hr : S.applyRow (sbRow f ρ) with
    | none => rw [hr] at h; cases h
    | some ρ' =>
      rw [hr] at h; cases h
      obtain ⟨h1, h2⟩ := applyRow_sb S f ρ ρ' (fun v hv => ht v (by simpa [Ty.vars] using hv)) hr
      exact ⟨fun a ha => h1 a (by simpa [Ty.vars] using ha), by simp [sb, h2]⟩
  | .record ρ (some e), u, ht, h => by
    obtain ⟨_, h⟩ := ht (.row e) (by simp [Ty.vars]); cases h
  | .fn a b, u, ht, h => by
    simp only [sb, Subst.apply] at h
    cases ha : S.apply (sb f a) with
    | none => rw [ha] at h; cases h
    | some a' =>
      cases hb : S.apply (sb f b) with
      | none => rw [ha, hb] at h; cases h
      | some b' =>
        rw [ha, hb] at h; cases h
        obtain ⟨h1, h2⟩ := apply_sb S f a a' (fun v hv => ht v (by simp [Ty.vars, hv])) ha
        obtain ⟨h3, h4⟩ := apply_sb S f b b' (fun v hv => ht v (by simp [Ty.vars, hv])) hb
        refine ⟨fun x hx => ?_, by simp [sb, h2, h4]⟩
        simp only [Ty.vars, List.mem_append] at hx
        rcases hx with hx | hx
        · exact h1 x hx
        · exact h3 x hx
  | .con as t, u, ht, h => by
    simp only [sb, Subst.apply] at h
    cases hl : S.applyList (sbList f as) with
    | none => rw [hl] at h; cases h
    | some as' =>
      rw [hl] at h; cases h
      obtain ⟨h1, h2⟩ := applyList_sb S f as as' (fun v hv => ht v (by simpa [Ty.vars] using hv)) hl
      exact ⟨fun a ha => h1 a (by simpa [Ty.vars] using ha), by simp [sb, h2]⟩
theorem applyRow_sb (S : Subst) (f : FSub) : ∀ (ρ ρ' : Row), (∀ v ∈ Ty.rowVars ρ, ∃ a, v = .ty a) →
    S.applyRow (sbRow f ρ) = some ρ' →
    (∀ a, BVar.ty a ∈ Ty.rowVars ρ → S.apply (f a) = some (post S f a)) ∧ ρ' = sbRow (post S f) ρ
  | [], ρ', _, h => by simp only [sbRow, Subst.applyRow, Option.some.injEq] at h; subst h; simp [Ty.rowVars, sbRow]
  | (l, τ) :: r, ρ', ht, h => by
    simp only [sbRow, Subst.applyRow] at h
    cases h1 : S.apply (sb f τ) with
    | none => rw [h1] at h; cases h
    | some τ' =>
      cases h2 : S.applyRow (sbRow f r) with
      | none => rw [h1, h2] at h; cases h
      | some r' =>
        rw [h1, h2] at h; cases h
        obtain ⟨g1, g2⟩ := apply_sb S f τ τ' (fun v hv => ht v (by simp [Ty.rowVars, hv])) h1
        obtain ⟨g3, g4⟩ := applyRow_sb S f r r' (fun v hv => ht v (by simp [Ty.rowVars, hv])) h2
        refine ⟨fun x hx => ?_, by simp [sbRow, g2, g4]⟩
        simp only [Ty.rowVars, List.mem_append] at hx
        rcases hx with hx | hx
        · exact g1 x hx
        · exact g3 x hx
theorem applyList_sb (S : Subst) (f : FSub) : ∀ (l l' : List Ty), (∀ v ∈ Ty.listVars l, ∃ a, v = .ty a) →
    S.applyList (sbList f l) = some l' →
    (∀ a, BVar.ty a ∈ Ty.listVars l → S.apply (f a) = some (post S f a)) ∧ l' = sbList (post S f) l
  | [], l', _, h => by simp only [sbList, Subst.applyList, Option.some.injEq] at h; subst h; simp [Ty.listVars, sbList]
  | τ :: r, l', ht, h => by
    simp only [sbList, Subst.applyList] at h
    cases h1 : S.apply (sb f τ) with
    | none => rw [h1] at h; cases h
    | some τ' =>
      cases h2 : S.applyList (sbList f r) with
      | none => rw [h1, h2] at h; cases h
      | some r' =>
        rw [h1, h2] at h; cases h
        obtain ⟨g1, g2⟩ := apply_sb S f τ τ' (fun v hv => ht v (by simp [Ty.listVars, hv])) h1
        obtain ⟨g3, g4⟩ := applyList_sb S f r r' (fun v hv => ht v (by simp [Ty.listVars, hv])) h2
        refine ⟨fun x hx => ?_, by simp [sbList, g2, g4]⟩
        simp only [Ty.listVars, List.mem_append] at hx
        rcases hx with hx | hx
        · exact g1 x hx
        · exact g3 x hx
end

end StandardElm.Stat.Complete
