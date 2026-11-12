/-
  A Standard Definition of Elm? Mechanisation: mutual instances are renamings, first layer (plan
  step 10, `mutualInstanceMod_renaming`): what a substitution does to the variables of a type when
  another substitution undoes it.

  If `S (ν τ) = τ''` and `S' (ν' τ'') = τ` (substitutions after renamings of type names), then `S`
  takes every variable of `τ` to a variable of `τ''` that `S'` takes back (`var_corr`): a type
  variable that `S` replaced by a non-variable could not come back, and a row variable that `S`
  extended by fields could not lose them. Classes are preserved because both substitutions respect
  them (`cls_of_corr`). Conversely, a substitution that takes each variable of `τ` to the
  variable a renaming `r` gives it applies to `ν τ` as `r` does (`apply_renameNames`).
-/
import StandardElmMech.Stat.RenameExtend

namespace StandardElm.Stat

/-! ## Type names -/

theorem renameName_eq (ρ : List (TyName × TyName)) (t : TyName) : renameName ρ t = (ρ.lookup t).getD t := by
  induction ρ with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [renameName, List.find?_cons, List.lookup] at ih ⊢
    by_cases h : t = k
    · subst h; simp
    · have e1 : (k == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      have e2 : (t == k) = false := beq_eq_false_iff_ne.mpr h
      simp only [e1, e2]; exact ih

/-! ## Rows -/

theorem merge_nil_left (ρ : Row) : Row.merge [] ρ = some ρ := by
  unfold Row.merge; cases ρ <;> rfl

theorem merge_nil_right (ρ : Row) : Row.merge ρ [] = some ρ := by
  unfold Row.merge; cases ρ <;> simp [Row.mergeF] <;> rfl

theorem mergeF_length : ∀ (n : Nat) (a b c : Row), Row.mergeF n a b = some c → c.length = a.length + b.length
  | _, [], b, c, h => by simp [Row.mergeF] at h; subst h; simp
  | _, _ :: _, [], c, h => by simp [Row.mergeF] at h; subst h; simp
  | 0, _ :: _, _ :: _, _, h => by simp [Row.mergeF] at h
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2, c, h => by
    simp only [Row.mergeF] at h
    split at h
    · cases h
    · split at h
      · split at h
        · rename_i r hr
          cases h
          have := mergeF_length n r1 ((l2, τ2) :: r2) r hr
          simp only [List.length_cons] at this ⊢; omega
        · cases h
      · split at h
        · rename_i r hr
          cases h
          have := mergeF_length n ((l1, τ1) :: r1) r2 r hr
          simp only [List.length_cons] at this ⊢; omega
        · cases h

theorem merge_length {a b c : Row} (h : Row.merge a b = some c) : c.length = a.length + b.length :=
  mergeF_length _ a b c h

mutual
theorem applyRow_length {S : Subst} : (ρ : Row) → ∀ {ρ' : Row}, S.applyRow ρ = some ρ' → ρ'.length = ρ.length
  | [], _, h => by simp [Subst.applyRow] at h; subst h; rfl
  | (l, τ) :: rest, ρ', h => by
    simp only [Subst.applyRow] at h
    cases h1 : S.apply τ <;> cases h2 : S.applyRow rest <;> rw [h1, h2] at h <;> simp at h
    subst h; simp [applyRow_length rest h2]
end

theorem renameRow_length (ν : List (TyName × TyName)) : ∀ ρ : Row, (Ty.renameRow ν ρ).length = ρ.length
  | [] => rfl
  | (_, _) :: rest => by simp [Ty.renameRow, renameRow_length ν rest]

/-! ## A substitution applied to a renamed type -/

theorem rowVar_shape {S : Subst} {e e' : RowVar} (h : S.applyVar (.row e) = some (.row e')) :
    (FMap.find? S.row e = none ∧ e' = e) ∨ FMap.find? S.row e = some ([], some e') := by
  simp only [Subst.applyVar, Subst.apply, Subst.applyRow] at h
  cases hf : FMap.find? S.row e with
  | none => rw [hf] at h; simp at h; exact .inl ⟨rfl, h.symm⟩
  | some p =>
    obtain ⟨ρ2, tl⟩ := p
    rw [hf] at h
    simp only [merge_nil_left] at h
    cases tl with
    | none => simp at h
    | some e3 =>
      cases ρ2 with
      | nil => simp at h; subst h; exact .inr rfl
      | cons _ _ => simp at h

mutual
theorem apply_renameNames {S : Subst} {r : Renaming} {ν : List (TyName × TyName)} (hν : r.tn = ν) :
    (τ : Ty) → (∀ v ∈ τ.vars, S.applyVar v = some (r.bvar v)) → S.apply (Ty.renameNames ν τ) = some (r.ty τ)
  | .var a, h => by
    have := h (.ty a) (by simp [Ty.vars])
    simp only [Subst.applyVar, Renaming.bvar] at this
    simp only [Ty.renameNames, Renaming.ty]
    split at this
    · rename_i b hb; cases this; exact hb
    · cases this
  | .record ρ none, h => by
    simp only [Ty.renameNames, Renaming.ty, Option.map_none, Subst.apply]
    rw [applyRow_renameNames hν ρ (fun v hv => h v (by simpa [Ty.vars] using hv))]
  | .record ρ (some e), h => by
    simp only [Ty.renameNames, Renaming.ty, Option.map_some, Subst.apply]
    rw [applyRow_renameNames hν ρ (fun v hv => h v (by simp [Ty.vars, hv]))]
    have he := h (.row e) (by simp [Ty.vars])
    simp only [Renaming.bvar] at he
    rcases rowVar_shape he with ⟨hf, hee⟩ | hf
    · rw [hf]; simp only [hee]
    · rw [hf]; simp only [merge_nil_right]
  | .fn a b, h => by
    simp only [Ty.renameNames, Renaming.ty, Subst.apply]
    rw [apply_renameNames hν a (fun v hv => h v (by simp [Ty.vars, hv])),
      apply_renameNames hν b (fun v hv => h v (by simp [Ty.vars, hv]))]
  | .con as t, h => by
    simp only [Ty.renameNames, Renaming.ty, Subst.apply]
    rw [applyList_renameNames hν as (fun v hv => h v (by simpa [Ty.vars] using hv))]
    simp only [Renaming.tnApply, hν, renameName_eq]
theorem applyRow_renameNames {S : Subst} {r : Renaming} {ν : List (TyName × TyName)} (hν : r.tn = ν) :
    (ρ : Row) → (∀ v ∈ Ty.rowVars ρ, S.applyVar v = some (r.bvar v)) →
      S.applyRow (Ty.renameRow ν ρ) = some (r.row ρ)
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [Ty.renameRow, Renaming.row, Subst.applyRow]
    rw [apply_renameNames hν τ (fun v hv => h v (by simp [Ty.rowVars, hv])),
      applyRow_renameNames hν rest (fun v hv => h v (by simp [Ty.rowVars, hv]))]
theorem applyList_renameNames {S : Subst} {r : Renaming} {ν : List (TyName × TyName)} (hν : r.tn = ν) :
    (l : List Ty) → (∀ v ∈ Ty.listVars l, S.applyVar v = some (r.bvar v)) →
      S.applyList (Ty.renameList ν l) = some (r.tys l)
  | [], _ => rfl
  | τ :: rest, h => by
    simp only [Ty.renameList, Renaming.tys, Subst.applyList]
    rw [apply_renameNames hν τ (fun v hv => h v (by simp [Ty.listVars, hv])),
      applyList_renameNames hν rest (fun v hv => h v (by simp [Ty.listVars, hv]))]
end

/-! ## Substitutions that undo each other rename variables -/

theorem applyVar_row_none {S : Subst} {e : RowVar} (h : FMap.find? S.row e = none) :
    S.applyVar (.row e) = some (.row e) := by
  simp [Subst.applyVar, Subst.apply, Subst.applyRow, h]

theorem applyVar_row_some {S : Subst} {e e' : RowVar} (h : FMap.find? S.row e = some ([], some e')) :
    S.applyVar (.row e) = some (.row e') := by
  simp [Subst.applyVar, Subst.apply, Subst.applyRow, h, merge_nil_left]

theorem apply_var_inv {S : Subst} {σ : Ty} {b : TyVar} (h : S.apply σ = some (.var b)) : ∃ a, σ = .var a := by
  cases σ with
  | var a => exact ⟨a, rfl⟩
  | record ρ tl =>
    cases tl with
    | none =>
      simp only [Subst.apply] at h
      split at h <;> cases h
    | some e =>
      simp only [Subst.apply] at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h
  | fn a c =>
    simp only [Subst.apply] at h
    split at h <;> cases h
  | con as t =>
    simp only [Subst.apply] at h
    split at h <;> cases h

theorem renameNames_var {ν : List (TyName × TyName)} {σ : Ty} {a : TyVar} (h : Ty.renameNames ν σ = .var a) :
    σ = .var a := by
  cases σ <;> simp [Ty.renameNames] at h; subst h; rfl

mutual
theorem var_corr {S S' : Subst} {ν ν' : List (TyName × TyName)} :
    (τ : Ty) → ∀ {τ'' : Ty}, S.apply (Ty.renameNames ν τ) = some τ'' → S'.apply (Ty.renameNames ν' τ'') = some τ →
      ∀ v ∈ τ.vars, ∃ w ∈ τ''.vars, S.applyVar v = some w ∧ S'.applyVar w = some v
  | .var a, τ'', hS, hS' => by
    intro v hv
    simp only [Ty.vars, List.mem_singleton] at hv
    subst hv
    obtain ⟨b, hb⟩ := apply_var_inv hS'
    have e := renameNames_var hb
    subst e
    simp only [Ty.renameNames] at hS hS'
    refine ⟨.ty b, by simp [Ty.vars], ?_, ?_⟩
    · simp only [Subst.applyVar, hS]
    · simp only [Subst.applyVar, hS']
  | .fn A B, τ'', hS, hS' => by
    simp only [Ty.renameNames, Subst.apply] at hS
    cases h1 : S.apply (Ty.renameNames ν A) <;> cases h2 : S.apply (Ty.renameNames ν B) <;>
      rw [h1, h2] at hS <;> simp only [reduceCtorEq] at hS
    rename_i A'' B''
    simp only [Option.some.injEq] at hS; subst hS
    simp only [Ty.renameNames, Subst.apply] at hS'
    cases h3 : S'.apply (Ty.renameNames ν' A'') <;> cases h4 : S'.apply (Ty.renameNames ν' B'') <;>
      rw [h3, h4] at hS' <;> simp only [reduceCtorEq] at hS'
    simp only [Option.some.injEq, Ty.fn.injEq] at hS'
    obtain ⟨rfl, rfl⟩ := hS'
    intro v hv
    simp only [Ty.vars, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨w, hw, h5, h6⟩ := var_corr _ h1 h3 v hv
      exact ⟨w, by simp [Ty.vars, hw], h5, h6⟩
    · obtain ⟨w, hw, h5, h6⟩ := var_corr _ h2 h4 v hv
      exact ⟨w, by simp [Ty.vars, hw], h5, h6⟩
  | .con as t, τ'', hS, hS' => by
    simp only [Ty.renameNames, Subst.apply] at hS
    cases h1 : S.applyList (Ty.renameList ν as) <;> rw [h1] at hS <;> simp only [reduceCtorEq] at hS
    rename_i as''
    simp only [Option.some.injEq] at hS; subst hS
    simp only [Ty.renameNames, Subst.apply] at hS'
    cases h3 : S'.applyList (Ty.renameList ν' as'') <;> rw [h3] at hS' <;> simp only [reduceCtorEq] at hS'
    simp only [Option.some.injEq, Ty.con.injEq] at hS'
    obtain ⟨rfl, _⟩ := hS'
    intro v hv
    simp only [Ty.vars] at hv
    obtain ⟨w, hw, h5, h6⟩ := var_corr_list _ h1 h3 v hv
    exact ⟨w, by simp [Ty.vars, hw], h5, h6⟩
  | .record ρ none, τ'', hS, hS' => by
    simp only [Ty.renameNames, Subst.apply] at hS
    cases h1 : S.applyRow (Ty.renameRow ν ρ) <;> rw [h1] at hS <;> simp only [reduceCtorEq] at hS
    rename_i ρ''
    simp only [Option.some.injEq] at hS; subst hS
    simp only [Ty.renameNames, Subst.apply] at hS'
    cases h3 : S'.applyRow (Ty.renameRow ν' ρ'') <;> rw [h3] at hS' <;> simp only [reduceCtorEq] at hS'
    simp only [Option.some.injEq, Ty.record.injEq] at hS'
    obtain ⟨rfl, _⟩ := hS'
    intro v hv
    simp only [Ty.vars] at hv
    obtain ⟨w, hw, h5, h6⟩ := var_corr_row _ h1 h3 v hv
    exact ⟨w, by simp [Ty.vars, hw], h5, h6⟩
  | .record ρ (some e), τ'', hS, hS' => by
    have lρ := renameRow_length ν ρ
    simp only [Ty.renameNames, Subst.apply] at hS
    cases h1 : S.applyRow (Ty.renameRow ν ρ) with
    | none => rw [h1] at hS; cases hS
    | some ρ1 =>
      have l1 := applyRow_length _ h1
      rw [h1] at hS
      simp only at hS
      cases h2 : FMap.find? S.row e with
      | none =>
        rw [h2] at hS; simp only [Option.some.injEq] at hS; subst hS
        simp only [Ty.renameNames, Subst.apply] at hS'
        cases h3 : S'.applyRow (Ty.renameRow ν' ρ1) with
        | none => rw [h3] at hS'; cases hS'
        | some ρ1' =>
          have l3 := applyRow_length _ h3
          rw [renameRow_length] at l3
          rw [h3] at hS'; simp only at hS'
          cases h4 : FMap.find? S'.row e with
          | none =>
            rw [h4] at hS'; simp only [Option.some.injEq, Ty.record.injEq, true_and, and_true] at hS'
            subst ρ1'
            intro v hv
            simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · obtain ⟨w, hw, h5, h6⟩ := var_corr_row ρ h1 h3 v hv
              exact ⟨w, by simp [Ty.vars, hw], h5, h6⟩
            · exact ⟨.row e, by simp [Ty.vars], applyVar_row_none h2, applyVar_row_none h4⟩
          | some p =>
            obtain ⟨ρ3, tl3⟩ := p
            rw [h4] at hS'; simp only at hS'
            cases h5 : Row.merge ρ1' ρ3 with
            | none => rw [h5] at hS'; cases hS'
            | some ρ4 =>
              rw [h5] at hS'; simp only [Option.some.injEq, Ty.record.injEq] at hS'
              obtain ⟨h7, h8⟩ := hS'
              subst ρ4; subst tl3
              have hl := merge_length h5
              have : ρ3 = [] := List.eq_nil_of_length_eq_zero (by omega)
              subst this
              rw [merge_nil_right, Option.some.injEq] at h5
              subst ρ1'
              intro v hv
              simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
              rcases hv with hv | rfl
              · obtain ⟨w, hw, h5, h6⟩ := var_corr_row ρ h1 h3 v hv
                exact ⟨w, by simp [Ty.vars, hw], h5, h6⟩
              · exact ⟨.row e, by simp [Ty.vars], applyVar_row_none h2, applyVar_row_some h4⟩
      | some p =>
        obtain ⟨ρ2, tl⟩ := p
        rw [h2] at hS; simp only at hS
        cases h3 : Row.merge ρ1 ρ2 with
        | none => rw [h3] at hS; cases hS
        | some ρ3 =>
          have l3 := merge_length h3
          rw [h3] at hS; simp only [Option.some.injEq] at hS; subst hS
          cases tl with
          | none =>
            simp only [Ty.renameNames, Subst.apply] at hS'
            split at hS' <;> simp at hS'
          | some e2 =>
            simp only [Ty.renameNames, Subst.apply] at hS'
            cases h4 : S'.applyRow (Ty.renameRow ν' ρ3) with
            | none => rw [h4] at hS'; cases hS'
            | some ρ3' =>
              have l4 := applyRow_length _ h4
              rw [renameRow_length] at l4
              rw [h4] at hS'; simp only at hS'
              cases h5 : FMap.find? S'.row e2 with
              | none =>
                rw [h5] at hS'; simp only [Option.some.injEq, Ty.record.injEq, Option.some.injEq] at hS'
                obtain ⟨h7, h8⟩ := hS'
                subst ρ3'; subst e2
                have : ρ2 = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst this
                rw [merge_nil_right, Option.some.injEq] at h3
                subst ρ3
                intro v hv
                simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
                rcases hv with hv | rfl
                · obtain ⟨w, hw, h6, h7⟩ := var_corr_row ρ h1 h4 v hv
                  exact ⟨w, by simp [Ty.vars, hw], h6, h7⟩
                · exact ⟨.row e, by simp [Ty.vars], applyVar_row_some h2, applyVar_row_none h5⟩
              | some p5 =>
                obtain ⟨ρ5, tl5⟩ := p5
                rw [h5] at hS'; simp only at hS'
                cases h6 : Row.merge ρ3' ρ5 with
                | none => rw [h6] at hS'; cases hS'
                | some ρ6 =>
                  rw [h6] at hS'; simp only [Option.some.injEq, Ty.record.injEq] at hS'
                  obtain ⟨h7, h8⟩ := hS'
                  subst ρ6; subst tl5
                  have l6 := merge_length h6
                  have e2' : ρ2 = [] := List.eq_nil_of_length_eq_zero (by omega)
                  have e5' : ρ5 = [] := List.eq_nil_of_length_eq_zero (by omega)
                  subst e2' e5'
                  rw [merge_nil_right, Option.some.injEq] at h3 h6
                  subst ρ3; subst ρ3'
                  intro v hv
                  simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
                  rcases hv with hv | rfl
                  · obtain ⟨w, hw, h7, h8⟩ := var_corr_row ρ h1 h4 v hv
                    exact ⟨w, by simp [Ty.vars, hw], h7, h8⟩
                  · exact ⟨.row e2, by simp [Ty.vars], applyVar_row_some h2, applyVar_row_some h5⟩
theorem var_corr_row {S S' : Subst} {ν ν' : List (TyName × TyName)} :
    (ρ : Row) → ∀ {ρ'' : Row}, S.applyRow (Ty.renameRow ν ρ) = some ρ'' → S'.applyRow (Ty.renameRow ν' ρ'') = some ρ →
      ∀ v ∈ Ty.rowVars ρ, ∃ w ∈ Ty.rowVars ρ'', S.applyVar v = some w ∧ S'.applyVar w = some v
  | [], _, _, _ => by simp [Ty.rowVars]
  | (l, τ) :: rest, ρ'', hS, hS' => by
    simp only [Ty.renameRow, Subst.applyRow] at hS
    cases h1 : S.apply (Ty.renameNames ν τ) <;> cases h2 : S.applyRow (Ty.renameRow ν rest) <;>
      rw [h1, h2] at hS <;> simp only [reduceCtorEq] at hS
    rename_i τ1 rest1
    simp only [Option.some.injEq] at hS; subst hS
    simp only [Ty.renameRow, Subst.applyRow] at hS'
    cases h3 : S'.apply (Ty.renameNames ν' τ1) <;> cases h4 : S'.applyRow (Ty.renameRow ν' rest1) <;>
      rw [h3, h4] at hS' <;> simp only [reduceCtorEq] at hS'
    simp only [Option.some.injEq, List.cons.injEq, Prod.mk.injEq, true_and] at hS'
    obtain ⟨rfl, rfl⟩ := hS'
    intro v hv
    simp only [Ty.rowVars, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨w, hw, h5, h6⟩ := var_corr _ h1 h3 v hv
      exact ⟨w, by simp [Ty.rowVars, hw], h5, h6⟩
    · obtain ⟨w, hw, h5, h6⟩ := var_corr_row _ h2 h4 v hv
      exact ⟨w, by simp [Ty.rowVars, hw], h5, h6⟩
theorem var_corr_list {S S' : Subst} {ν ν' : List (TyName × TyName)} :
    (l : List Ty) → ∀ {l'' : List Ty}, S.applyList (Ty.renameList ν l) = some l'' → S'.applyList (Ty.renameList ν' l'') = some l →
      ∀ v ∈ Ty.listVars l, ∃ w ∈ Ty.listVars l'', S.applyVar v = some w ∧ S'.applyVar w = some v
  | [], _, _, _ => by simp [Ty.listVars]
  | τ :: rest, l'', hS, hS' => by
    simp only [Ty.renameList, Subst.applyList] at hS
    cases h1 : S.apply (Ty.renameNames ν τ) <;> cases h2 : S.applyList (Ty.renameList ν rest) <;>
      rw [h1, h2] at hS <;> simp only [reduceCtorEq] at hS
    rename_i τ1 rest1
    simp only [Option.some.injEq] at hS; subst hS
    simp only [Ty.renameList, Subst.applyList] at hS'
    cases h3 : S'.apply (Ty.renameNames ν' τ1) <;> cases h4 : S'.applyList (Ty.renameList ν' rest1) <;>
      rw [h3, h4] at hS' <;> simp only [reduceCtorEq] at hS'
    simp only [Option.some.injEq, List.cons.injEq] at hS'
    obtain ⟨rfl, rfl⟩ := hS'
    intro v hv
    simp only [Ty.listVars, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨w, hw, h5, h6⟩ := var_corr _ h1 h3 v hv
      exact ⟨w, by simp [Ty.listVars, hw], h5, h6⟩
    · obtain ⟨w, hw, h5, h6⟩ := var_corr_list _ h2 h4 v hv
      exact ⟨w, by simp [Ty.listVars, hw], h5, h6⟩
end

/-! ## Classes -/

theorem find?_mem {K V : Type} [DecidableEq K] {k : K} {v : V} : ∀ {l : FMap K V}, FMap.find? l k = some v → (k, v) ∈ l
  | [], h => by simp at h
  | (k', v') :: rest, h => by
    simp only [FMap.find?] at h
    split at h
    · rename_i e; subst e; cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (find?_mem h)

theorem adm_var_le {k : Cls} {b : TyVar} (h : Adm k (.var b)) : b.cls.le k = true := by
  cases h with
  | any => cases b.cls <;> rfl
  | num_var _ hb => rw [hb]; rfl
  | comp_var _ hb => exact hb
  | app_var _ hb => exact hb
  | capp_var _ hb => rw [hb]; rfl

theorem cls_le_of_applyVar {S : Subst} (hS : S.Respects) {a b : TyVar} (h : S.applyVar (.ty a) = some (.ty b)) :
    b.cls.le a.cls = true := by
  simp only [Subst.applyVar, Subst.apply] at h
  cases hf : FMap.find? S.ty a with
  | none => rw [hf] at h; simp at h; subst h; cases a.cls <;> rfl
  | some τ =>
    rw [hf] at h
    simp only [Option.getD_some] at h
    split at h
    · rename_i c hc
      cases hc; cases h
      exact adm_var_le (hS _ (find?_mem hf))
    · cases h

theorem Cls.le_antisymm (a b : Cls) : a.le b = true → b.le a = true → a = b := by
  cases a <;> cases b <;> decide

theorem cls_of_corr {S S' : Subst} (hS : S.Respects) (hS' : S'.Respects) {a b : TyVar}
    (h : S.applyVar (.ty a) = some (.ty b)) (h' : S'.applyVar (.ty b) = some (.ty a)) : b.cls = a.cls :=
  Cls.le_antisymm _ _ (cls_le_of_applyVar hS h) (cls_le_of_applyVar hS' h')

/-- What `applyVar` gives a variable: a variable of the same kind. -/
theorem applyVar_kind {S : Subst} {v w : BVar} (h : S.applyVar v = some w) :
    (∃ a b, v = .ty a ∧ w = .ty b) ∨ (∃ e e', v = .row e ∧ w = .row e') := by
  cases v with
  | ty a =>
    simp only [Subst.applyVar] at h
    split at h
    · cases h; exact .inl ⟨_, _, rfl, rfl⟩
    · cases h
  | row e =>
    simp only [Subst.applyVar] at h
    split at h
    · cases h; exact .inr ⟨_, _, rfl, rfl⟩
    · cases h

end StandardElm.Stat
