/-
  A Standard Definition of Elm? Mechanisation: rows and canonical types of derivations, for the
  main induction L11 with records (plan step 11, milestone (d)).

  * `NBD l`: the types of `l` have no `bnd` variable and are canonical (the hypothesis on a
    derivation in the main induction: `NoFreeBndExp` and `CanonExp`, read on the types the
    phrase records).
  * The row of a record expression or pattern (`Row.modify` one field at a time) is sorted
    (`sorted_modify1`); a derivation's type is canonical when the types it records are
    (`cn_exp_ty`, `cn_pat_ty`, ...).
  * `mrg_onlyL_eq`: a sorted row is the merge of a sorted sub-row and the fields it lacks (the
    image of a record pattern's or an update's type `⟨ρ | ε⟩` with `ε` bound to the missing
    fields).
-/
import StandardElmMech.Stat.Complete.WDUnifyW
import StandardElmMech.Stat.Complete.NodesOk

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## The hypothesis on a derivation's types -/

def NBD (l : List Ty) : Prop := ∀ τ ∈ l, (∀ v ∈ τ.vars, v.isBnd = false) ∧ cnB τ = true

theorem NBD.app {l1 l2 : List Ty} (h : NBD (l1 ++ l2)) : NBD l1 ∧ NBD l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩

theorem NBD.cons {τ : Ty} {l : List Ty} (h : NBD (τ :: l)) : NBD [τ] ∧ NBD l :=
  ⟨fun x hx => h x (by simp at hx; simp [hx]), fun x hx => h x (.tail _ hx)⟩

theorem NBD.cn {l : List Ty} (h : NBD l) : ∀ τ ∈ l, cnB τ = true := fun τ hτ => (h τ hτ).2

/-! ## Canonical types -/

theorem cnB_fn {a b : Ty} : cnB (.fn a b) = true ↔ cnB a = true ∧ cnB b = true := by
  simp [cnB]

theorem cnB_con {as : List Ty} {t : TyName} : cnB (.con as t) = true ↔ ∀ τ ∈ as, cnB τ = true := by
  rw [cnB, cnListB_iff]

theorem cnB_cod {τ : Ty} (h : cnB τ = true) : cnB τ.cod = true := by
  cases τ with
  | fn a b => exact (cnB_fn.mp h).2
  | _ => exact h

theorem cnB_list {τ : Ty} (h : cnB τ = true) : cnB (listTy τ) = true :=
  cnB_con.mpr fun x hx => by simp at hx; subst hx; exact h

theorem cnB_tuple {τ1 τ2 : Ty} {τ3 : Option Ty} (h1 : cnB τ1 = true) (h2 : cnB τ2 = true)
    (h3 : ∀ τ, τ3 = some τ → cnB τ = true) : cnB (tupleTy τ1 τ2 τ3) = true := by
  cases τ3 with
  | none => exact cnB_con.mpr fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption
  | some τ =>
    exact cnB_con.mpr fun x hx => by
      simp at hx; rcases hx with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3 _ rfl

/-! ## The row of a record phrase -/

def CnRow (ρ : Row) : Prop := Sorted ρ ∧ ∀ p ∈ ρ, cnB p.2 = true

theorem cnRow_nil : CnRow [] := ⟨sorted_nil, fun _ h => nomatch h⟩

theorem cnRow_modify1 {l : Lab} {τ : Ty} {ρ : Row} (h1 : cnB τ = true) (h2 : CnRow ρ) :
    CnRow (Row.modify [(l, τ)] ρ) :=
  ⟨sorted_modify1 h2.1, fun p hp => by
    rcases mem_modify1 hp with rfl | hp
    · exact h1
    · exact h2.2 p hp⟩

theorem cnB_record_of {ρ : Row} {tl : Option RowVar} (h : CnRow ρ) : cnB (.record ρ tl) = true :=
  cnB_record.mpr h

/-! ## A derivation's types are canonical when the types it records are -/

mutual
theorem cn_atpat_ty : ∀ p : AAtPat, (∀ τ ∈ tysAtPat p, cnB τ = true) → cnB p.ty = true
  | .wild _, h | .scon _ _, h | .var _ _, h | .con _ _ _, h | .nil _, h | .record _ _, h => h _ (by simp [tysAtPat, AAtPat.ty])
  | .unit, _ => rfl
  | .tuple p1 p2 p3, h => by
    simp only [tysAtPat, List.mem_append] at h
    exact cnB_tuple (cn_pat_ty p1 fun τ hτ => h τ (.inl (.inl hτ))) (cn_pat_ty p2 fun τ hτ => h τ (.inl (.inr hτ)))
      (cn_patopt_ty p3 fun τ hτ => h τ (.inr hτ))
  | .paren p, h => by simp only [tysAtPat] at h; exact cn_pat_ty p h
theorem cn_pat_ty : ∀ p : APat, (∀ τ ∈ tysPat p, cnB τ = true) → cnB p.ty = true
  | .atpat a, h => by simp only [tysPat] at h; exact cn_atpat_ty a h
  | .con _ _ _ _, h => h _ (by simp [tysPat, APat.ty])
  | .cons p1 p2, h => by
    simp only [tysPat, List.mem_append] at h
    exact cnB_list (cn_pat_ty p1 fun τ hτ => h τ (.inl hτ))
  | .as p _, h => by simp only [tysPat] at h; exact cn_pat_ty p h
theorem cn_patopt_ty : ∀ p : Option APat, (∀ τ ∈ tysPatOpt p, cnB τ = true) → ∀ τ, APat.tyOpt p = some τ → cnB τ = true
  | none, _, _, h => by cases h
  | some p, h, τ, e => by
    simp only [APat.tyOpt, Option.some.injEq] at e; subst e
    exact cn_pat_ty p h
end

theorem cn_patrowopt_row : ∀ r : Option APatRow, (∀ τ ∈ tysPatRowOpt r, cnB τ = true) → CnRow (APatRow.rowOpt r)
  | none, _ => cnRow_nil
  | some (.field l τ rest), h => by
    simp only [tysPatRowOpt, tysPatRow, List.mem_cons] at h
    exact cnRow_modify1 (h τ (.inl rfl)) (cn_patrowopt_row rest fun x hx => h x (.inr hx))

mutual
theorem cn_atexp_ty : ∀ a : AAtExp, (∀ τ ∈ tysAtExp false a, cnB τ = true) → cnB a.ty = true
  | .scon _ _, h | .var _ _ _, h | .con _ _ _, h | .op _ _ _, h | .nil _, h | .update _ _ _ _, h =>
    h _ (by simp [tysAtExp, AAtExp.ty])
  | .unit, _ => rfl
  | .tuple e1 e2 e3, h => by
    simp only [tysAtExp, List.mem_append] at h
    exact cnB_tuple (cn_exp_ty e1 fun τ hτ => h τ (.inl (.inl hτ))) (cn_exp_ty e2 fun τ hτ => h τ (.inl (.inr hτ)))
      (cn_expopt_ty e3 fun τ hτ => h τ (.inr hτ))
  | .record r, h => by
    simp only [tysAtExp] at h
    exact cnB_record_of (cn_exprowopt_row r h)
  | .letE d e, h => by
    simp only [tysAtExp, List.mem_append] at h
    exact cn_exp_ty e fun τ hτ => h τ (.inr hτ)
  | .paren e, h => by simp only [tysAtExp] at h; exact cn_exp_ty e h
theorem cn_exprow_row : ∀ r : AExpRow, (∀ τ ∈ tysExpRow false r, cnB τ = true) → CnRow r.row
  | .field l e rest, h => by
    simp only [tysExpRow, List.mem_append] at h
    exact cnRow_modify1 (cn_exp_ty e fun τ hτ => h τ (.inl hτ)) (cn_exprowopt_row rest fun τ hτ => h τ (.inr hτ))
theorem cn_exprowopt_row : ∀ r : Option AExpRow, (∀ τ ∈ tysExpRowOpt false r, cnB τ = true) → CnRow (AExpRow.rowOpt r)
  | none, _ => cnRow_nil
  | some r, h => by simp only [tysExpRowOpt] at h; exact cn_exprow_row r h
theorem cn_exp_ty : ∀ e : AExp, (∀ τ ∈ tysExp false e, cnB τ = true) → cnB e.ty = true
  | .atexp a, h => by simp only [tysExp] at h; exact cn_atexp_ty a h
  | .app e a, h => by
    simp only [tysExp, List.mem_append] at h
    exact cnB_cod (cn_exp_ty e fun τ hτ => h τ (.inl hτ))
  | .lam p e, h => by
    simp only [tysExp, List.mem_append] at h
    exact cnB_fn.mpr ⟨cn_atpat_ty p fun τ hτ => h τ (.inl hτ), cn_exp_ty e fun τ hτ => h τ (.inr hτ)⟩
  | .caseE e m, h => by
    simp only [tysExp, List.mem_append] at h
    exact cnB_cod (cn_match_ty m fun τ hτ => h τ (.inr hτ))
theorem cn_expopt_ty : ∀ e : Option AExp, (∀ τ ∈ tysExpOpt false e, cnB τ = true) → ∀ τ, AExp.tyOpt e = some τ → cnB τ = true
  | none, _, _, h => by cases h
  | some e, h, τ, h' => by
    simp only [AExp.tyOpt, Option.some.injEq] at h'; subst h'
    exact cn_exp_ty e h
theorem cn_match_ty : ∀ m : AMatch, (∀ τ ∈ tysMatch false m, cnB τ = true) → cnB m.ty = true
  | .mk (.mk p e) rest, h => by
    simp only [tysMatch, tysMRule, List.mem_append] at h
    exact cnB_fn.mpr ⟨cn_pat_ty p fun τ hτ => h τ (.inl (.inl hτ)), cn_exp_ty e fun τ hτ => h τ (.inl (.inr hτ))⟩
end

theorem cn_mrule_ty : ∀ mr : AMRule, (∀ τ ∈ tysMRule false mr, cnB τ = true) → cnB mr.ty = true
  | .mk p e, h => by
    simp only [tysMRule, List.mem_append] at h
    exact cnB_fn.mpr ⟨cn_pat_ty p fun τ hτ => h τ (.inl hτ), cn_exp_ty e fun τ hτ => h τ (.inr hτ)⟩

/-! ## A sorted row as a merge -/

theorem lookup_mem {ρ : Row} {l : Lab} {τ : Ty} (h : Row.lookup ρ l = some τ) : (l, τ) ∈ ρ := find?_mem h

/-- A sorted row is the merge of a sorted sub-row and the fields the sub-row lacks. -/
theorem mrg_onlyL_eq {a ρ : Row} (ha : Sorted a) (hρ : Sorted ρ) (hsub : Row.Sub a ρ) : mrg a (onlyL ρ a) = ρ := by
  have hd : LDisj a (onlyL ρ a) := by
    intro x hx y hy e
    simp only [onlyL, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hy
    exact hy.2 (e ▸ mem_labs.mpr ⟨x.2, hx⟩)
  refine sorted_ext (sorted_mrg ha (sorted_filter _ hρ) hd) hρ fun x => ?_
  rw [mem_mrg]
  constructor
  · rintro (hx | hx)
    · exact lookup_mem (hsub x.1 x.2 hx)
    · simp only [onlyL, List.mem_filter] at hx; exact hx.1
  · intro hx
    by_cases hl : x.1 ∈ labs a
    · obtain ⟨τa, hτa⟩ := mem_labs.mp hl
      have hm := lookup_mem (hsub x.1 τa hτa)
      have : x = (x.1, τa) := sorted_unique hρ hx hm rfl
      rw [this]; exact .inl hτa
    · exact .inr (by simp only [onlyL, List.mem_filter]; exact ⟨hx, by simpa using hl⟩)

end StandardElm.Stat.Complete
