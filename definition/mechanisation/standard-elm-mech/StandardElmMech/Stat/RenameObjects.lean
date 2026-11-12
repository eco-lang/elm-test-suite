/-
  A Standard Definition of Elm? Mechanisation: renamings commute with the operations on semantic
  objects that specialisation uses, plan step 10 (Theorems, "The variables of a group and the
  invariance lemma"): free variables, set difference and first occurrences on lists, substitutions,
  canonical forms of schemes (`Scheme.canon`), closure of a group (`closGroup`), and the members
  of a group as specialisation reads them (`memberOf`).

  A context is compared with its image only on a set `D` of variables (the variables of the types
  of the derivation): the U of an annotation may contain variables that no type mentions, and two
  derivations need not agree on those.
-/
import StandardElmMech.Stat.RenameSyntax

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## Lists -/

theorem diffL_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (l A : List α) (A' : List β)
    (h : ∀ x ∈ l, (f x ∈ A' ↔ x ∈ A)) : diffL (l.map f) A' = (diffL l A).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [diffL] at ih' ⊢
    simp only [List.map_cons, List.filter_cons]
    by_cases hA : x ∈ A
    · have : f x ∈ A' := hx.mpr hA
      simp only [this, hA, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih']
    · have : f x ∉ A' := fun e => hA (hx.mp e)
      simp only [this, hA, decide_false, Bool.not_false, ↓reduceIte, ih', List.map_cons]

theorem mem_map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) {x : α} {l : List α} :
    f x ∈ l.map f ↔ x ∈ l := by
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := List.mem_map.mp h
    rw [hf _ _ e] at hy; exact hy
  · exact List.mem_map_of_mem

theorem diffL_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (l A : List α) : diffL (l.map f) (A.map f) = (diffL l A).map f :=
  diffL_map f l A _ fun _ _ => mem_map_inj hf

theorem dedupL_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) : ∀ l : List α, dedupL (l.map f) = (dedupL l).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, dedupL, dedupL_map f hf xs, List.cons.injEq, true_and]
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro a _
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr ⟨fun h e => h (congrArg f e), fun h e => h (hf _ _ e)⟩

theorem mem_diffL {α : Type} [DecidableEq α] {x : α} {l A : List α} : x ∈ diffL l A ↔ x ∈ l ∧ x ∉ A := by
  simp [diffL, List.mem_filter]

/-! ## Variables -/

theorem Renaming.WF.bvar_inj {r : Renaming} (hr : r.WF) : ∀ v w, r.bvar v = r.bvar w → v = w
  | .ty a, .ty b, h => by
    simp only [Renaming.bvar, BVar.ty.injEq] at h; rw [hr.tv_inj a b h]
  | .row e, .row e', h => by
    simp only [Renaming.bvar, BVar.row.injEq] at h; rw [hr.rv_inj e e' h]
  | .ty _, .row _, h => by simp [Renaming.bvar] at h
  | .row _, .ty _, h => by simp [Renaming.bvar] at h

theorem Renaming.WF.tv_isBnd {r : Renaming} (hr : r.WF) (a : TyVar) :
    (∃ i c, r.tvApply a = .bnd i c) ↔ ∃ i c, a = .bnd i c := by
  constructor
  · rintro ⟨i, c, h⟩
    exact ⟨i, c, hr.tv_inj _ _ (h.trans (hr.tv_bnd i c).symm)⟩
  · rintro ⟨i, c, rfl⟩
    exact ⟨i, c, hr.tv_bnd i c⟩

theorem Renaming.WF.isBnd_bvar {r : Renaming} (hr : r.WF) (v : BVar) : (r.bvar v).isBnd = v.isBnd := by
  cases v with
  | ty a =>
    simp only [Renaming.bvar]
    by_cases h : ∃ i c, a = .bnd i c
    · obtain ⟨i, c, rfl⟩ := h; rw [hr.tv_bnd]
    · have h' : ¬ ∃ i c, r.tvApply a = .bnd i c := fun e => h ((hr.tv_isBnd a).mp e)
      cases ha : r.tvApply a with
      | bnd i c => exact absurd ⟨i, c, ha⟩ h'
      | named s =>
        cases a with
        | bnd i c => exact absurd ⟨i, c, rfl⟩ h
        | _ => rfl
      | fresh n c =>
        cases a with
        | bnd i c => exact absurd ⟨i, c, rfl⟩ h
        | _ => rfl
  | row e =>
    simp only [Renaming.bvar]
    by_cases h : ∃ i, e = .bnd i
    · obtain ⟨i, rfl⟩ := h; rw [hr.rv_bnd]
    · have h' : ∀ i, r.rvApply e ≠ .bnd i := fun i e' => h ⟨i, hr.rv_inj _ _ (e'.trans (hr.rv_bnd i).symm)⟩
      cases he : r.rvApply e with
      | bnd i => exact absurd he (h' i)
      | named s =>
        cases e with
        | bnd i => exact absurd ⟨i, rfl⟩ h
        | _ => rfl
      | fresh n =>
        cases e with
        | bnd i => exact absurd ⟨i, rfl⟩ h
        | _ => rfl

theorem Renaming.WF.isNumTyVar_bvar {r : Renaming} (hr : r.WF) (v : BVar) :
    (r.bvar v).isNumTyVar = v.isNumTyVar := by
  cases v <;> simp [Renaming.bvar, BVar.isNumTyVar, hr.tv_cls]

theorem Renaming.tyVar?_bvar (r : Renaming) (v : BVar) : (r.bvar v).tyVar? = v.tyVar?.map r.tvApply := by
  cases v <;> rfl

theorem Renaming.row_eq_map (r : Renaming) : ∀ ρ : Row, r.row ρ = ρ.map fun p => (p.1, r.ty p.2)
  | [] => rfl
  | (l, τ) :: rest => by simp [Renaming.row, Renaming.row_eq_map r rest]

mutual
theorem vars_rename (r : Renaming) : (τ : Ty) → (r.ty τ).vars = τ.vars.map r.bvar
  | .var a => rfl
  | .record ρ none => by simp only [Renaming.ty, Option.map_none, Ty.vars]; exact rowVars_rename r ρ
  | .record ρ (some e) => by
    simp only [Renaming.ty, Option.map_some, Ty.vars, List.map_append, rowVars_rename r ρ]; rfl
  | .fn a b => by simp [Renaming.ty, Ty.vars, vars_rename r a, vars_rename r b]
  | .con as t => by simp only [Renaming.ty, Ty.vars]; exact listVars_rename r as
theorem rowVars_rename (r : Renaming) : (ρ : Row) → Ty.rowVars (r.row ρ) = (Ty.rowVars ρ).map r.bvar
  | [] => rfl
  | (l, τ) :: rest => by simp [Renaming.row, Ty.rowVars, vars_rename r τ, rowVars_rename r rest]
theorem listVars_rename (r : Renaming) : (l : List Ty) → Ty.listVars (r.tys l) = (Ty.listVars l).map r.bvar
  | [] => rfl
  | τ :: rest => by simp [Renaming.tys, Ty.listVars, vars_rename r τ, listVars_rename r rest]
end

theorem tyvars_rename {r : Renaming} (hr : r.WF) (τ : Ty) : (r.ty τ).tyvars = τ.tyvars.map r.bvar := by
  simp only [Ty.tyvars, vars_rename, List.filter_map]
  congr 1
  apply List.filter_congr
  intro v _
  simp [Function.comp_apply, hr.isBnd_bvar v]

theorem scheme_tyvars_rename {r : Renaming} (hr : r.WF) (σ : Scheme) :
    (r.scheme σ).tyvars = σ.tyvars.map r.bvar := by
  simp only [Scheme.tyvars, Renaming.scheme, tyvars_rename hr]
  exact diffL_map_inj _ (hr.bvar_inj) _ _

mutual
theorem mem_vars_of_tyVarsSeq {α : TyVar} : (τ : Ty) → α ∈ τ.tyVarsSeq → BVar.ty α ∈ τ.vars
  | .var a, h => by simp only [Ty.tyVarsSeq, List.mem_singleton] at h; subst h; simp [Ty.vars]
  | .record ρ none, h => by simp only [Ty.tyVarsSeq] at h; simp only [Ty.vars]; exact mem_rowVars_of h
  | .record ρ (some e), h => by
    simp only [Ty.tyVarsSeq] at h; simp only [Ty.vars]; exact List.mem_append_left _ (mem_rowVars_of h)
  | .fn a b, h => by
    simp only [Ty.tyVarsSeq, List.mem_append] at h; simp only [Ty.vars, List.mem_append]
    rcases h with h | h
    · exact .inl (mem_vars_of_tyVarsSeq a h)
    · exact .inr (mem_vars_of_tyVarsSeq b h)
  | .con as _, h => by simp only [Ty.tyVarsSeq] at h; simp only [Ty.vars]; exact mem_listVars_of h
theorem mem_rowVars_of {α : TyVar} : {ρ : Row} → α ∈ Ty.rowTyVarsSeq ρ → BVar.ty α ∈ Ty.rowVars ρ
  | [], h => by simp [Ty.rowTyVarsSeq] at h
  | (l, τ) :: rest, h => by
    simp only [Ty.rowTyVarsSeq, List.mem_append] at h; simp only [Ty.rowVars, List.mem_append]
    rcases h with h | h
    · exact .inl (mem_vars_of_tyVarsSeq τ h)
    · exact .inr (mem_rowVars_of h)
theorem mem_listVars_of {α : TyVar} : {l : List Ty} → α ∈ Ty.listTyVarsSeq l → BVar.ty α ∈ Ty.listVars l
  | [], h => by simp [Ty.listTyVarsSeq] at h
  | τ :: rest, h => by
    simp only [Ty.listTyVarsSeq, List.mem_append] at h; simp only [Ty.listVars, List.mem_append]
    rcases h with h | h
    · exact .inl (mem_vars_of_tyVarsSeq τ h)
    · exact .inr (mem_listVars_of h)
end

theorem mem_vars_of_tyvars {v : BVar} {τ : Ty} (h : v ∈ τ.tyvars) : v ∈ τ.vars :=
  (List.mem_filter.mp h).1

/-! ## Environments -/

theorem tyvarsBy_rename {V W : Type} {r : Renaming} (hr : r.WF) (f : V → List BVar) (g : W → List BVar)
    (h : V → W) (hfg : ∀ v, g (h v) = (f v).map r.bvar) :
    ∀ (seen : List String) (l : FMap String V),
      FMap.tyvarsBy g seen (l.map fun p => (p.1, h p.2)) = (FMap.tyvarsBy f seen l).map r.bvar
  | _, [] => rfl
  | seen, (k, v) :: rest => by
    simp only [List.map_cons, FMap.tyvarsBy, hfg, List.isEmpty_map, List.map_append,
      tyvarsBy_rename hr f g h hfg (k :: seen) rest]
    split <;> simp

theorem valEnv_tyvars_rename {r : Renaming} (hr : r.WF) (VE : ValEnv) :
    ValEnv.tyvars (r.valEnv VE) = (ValEnv.tyvars VE).map r.bvar := by
  unfold ValEnv.tyvars Renaming.valEnv
  exact tyvarsBy_rename hr (fun b => b.1.tyvars) (fun b => b.1.tyvars) (fun b => (r.scheme b.1, b.2))
    (fun b => scheme_tyvars_rename hr b.1) [] VE

theorem mem_tyvarsBy {V : Type} {f : V → List BVar} {x : BVar} :
    ∀ {seen : List String} {l : FMap String V}, x ∈ FMap.tyvarsBy f seen l → ∃ p ∈ l, x ∈ f p.2
  | _, [], h => by simp [FMap.tyvarsBy] at h
  | seen, (k, v) :: rest, h => by
    simp only [FMap.tyvarsBy, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h
      · exact ⟨(k, v), List.mem_cons_self .., h⟩
    · obtain ⟨p, hp, hx⟩ := mem_tyvarsBy h
      exact ⟨p, List.mem_cons_of_mem _ hp, hx⟩

theorem Renaming.valEnv_append (r : Renaming) (VE VE' : ValEnv) :
    r.valEnv (VE ++ VE') = r.valEnv VE ++ r.valEnv VE' := List.map_append ..

/-! ## Substitutions -/

/-- A substitution renamed: its domain by `r`, its range by `r.ty`. -/
def Renaming.subst (r : Renaming) (S : Subst) : Subst :=
  ⟨S.ty.map fun p => (r.tvApply p.1, r.ty p.2),
   S.row.map fun p => (r.rvApply p.1, (r.row p.2.1, p.2.2.map r.rvApply))⟩

theorem find?_map_inj {K K' V V' : Type} [DecidableEq K] [DecidableEq K'] (f : K → K') (g : V → V')
    (hf : ∀ a b, f a = f b → a = b) :
    ∀ (m : List (K × V)) (a : K), FMap.find? (m.map fun p => (f p.1, g p.2)) (f a) = (FMap.find? m a).map g
  | [], _ => rfl
  | (x, v) :: rest, a => by
    simp only [List.map_cons, FMap.find?]
    by_cases h : x = a
    · subst h; simp
    · have h' : f x ≠ f a := fun e => h (hf _ _ e)
      simp only [h, h', ↓reduceIte]
      exact find?_map_inj f g hf rest a

theorem mergeF_rename (r : Renaming) : ∀ (n : Nat) (a b : Row),
    Row.mergeF n (r.row a) (r.row b) = (Row.mergeF n a b).map r.row
  | n, [], b => by cases b <;> simp only [Renaming.row] <;> cases n <;> rfl
  | n, (l, τ) :: rest, [] => by simp only [Renaming.row]; cases n <;> rfl
  | 0, (l, τ) :: rest, (l', τ') :: rest' => rfl
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    simp only [Renaming.row, Row.mergeF]
    by_cases h1 : l1 = l2
    · simp [h1]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : labLt l1 l2 = true
      · simp only [h2, ↓reduceIte]
        have := mergeF_rename r n r1 ((l2, τ2) :: r2)
        simp only [Renaming.row] at this
        rw [this]; cases Row.mergeF n r1 ((l2, τ2) :: r2) <;> rfl
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        have := mergeF_rename r n ((l1, τ1) :: r1) r2
        simp only [Renaming.row] at this
        rw [this]; cases Row.mergeF n ((l1, τ1) :: r1) r2 <;> rfl

theorem row_length (r : Renaming) (ρ : Row) : (r.row ρ).length = ρ.length := by
  rw [Renaming.row_eq_map]; simp

theorem merge_rename (r : Renaming) (a b : Row) : Row.merge (r.row a) (r.row b) = (Row.merge a b).map r.row := by
  simp only [Row.merge, row_length]; exact mergeF_rename r _ a b

mutual
theorem apply_subst_rename {r : Renaming} (hr : r.WF) (S : Subst) :
    (τ : Ty) → (r.subst S).apply (r.ty τ) = (S.apply τ).map r.ty
  | .var a => by
    simp only [Renaming.ty, Subst.apply, Renaming.subst, Option.map_some]
    rw [find?_map_inj r.tvApply r.ty hr.tv_inj S.ty a]
    cases FMap.find? S.ty a <;> rfl
  | .record ρ none => by
    simp only [Renaming.ty, Option.map_none, Subst.apply]
    rw [applyRow_subst_rename hr S ρ]
    cases Subst.applyRow S ρ <;> rfl
  | .record ρ (some e) => by
    simp only [Renaming.ty, Option.map_some, Subst.apply]
    rw [applyRow_subst_rename hr S ρ]
    cases Subst.applyRow S ρ with
    | none => rfl
    | some ρ' =>
      simp only [Option.map_some]
      have hf : FMap.find? (r.subst S).row (r.rvApply e) = (FMap.find? S.row e).map
          (fun p => (r.row p.1, p.2.map r.rvApply)) :=
        @find?_map_inj RowVar RowVar (Row × Option RowVar) (Row × Option RowVar) _ _ r.rvApply
          (fun q => (r.row q.1, q.2.map r.rvApply)) hr.rv_inj S.row e
      rw [hf]
      cases FMap.find? S.row e with
      | none => rfl
      | some p =>
        obtain ⟨ρ2, tl⟩ := p
        simp only [Option.map_some]
        rw [merge_rename]
        cases Row.merge ρ' ρ2 <;> rfl
  | .fn a b => by
    simp only [Renaming.ty, Subst.apply]
    rw [apply_subst_rename hr S a, apply_subst_rename hr S b]
    cases Subst.apply S a <;> cases Subst.apply S b <;> rfl
  | .con as t => by
    simp only [Renaming.ty, Subst.apply]
    rw [applyList_subst_rename hr S as]
    cases Subst.applyList S as <;> rfl
theorem applyRow_subst_rename {r : Renaming} (hr : r.WF) (S : Subst) :
    (ρ : Row) → (r.subst S).applyRow (r.row ρ) = (Subst.applyRow S ρ).map r.row
  | [] => rfl
  | (l, τ) :: rest => by
    simp only [Renaming.row, Subst.applyRow]
    rw [apply_subst_rename hr S τ, applyRow_subst_rename hr S rest]
    cases Subst.apply S τ <;> cases Subst.applyRow S rest <;> rfl
theorem applyList_subst_rename {r : Renaming} (hr : r.WF) (S : Subst) :
    (l : List Ty) → (r.subst S).applyList (r.tys l) = (Subst.applyList S l).map r.tys
  | [] => rfl
  | τ :: rest => by
    simp only [Renaming.tys, Subst.applyList]
    rw [apply_subst_rename hr S τ, applyList_subst_rename hr S rest]
    cases Subst.apply S τ <;> cases Subst.applyList S rest <;> rfl
end

/-! ## Canonical forms -/

theorem renumber_rename {r : Renaming} (hr : r.WF) : ∀ (i : Nat) (l : List BVar),
    renumber true i (l.map r.bvar) = (r.subst (renumber true i l).1, (renumber true i l).2)
  | _, [] => rfl
  | i, .ty a :: vs => by
    have ih := renumber_rename hr (i + 1) vs
    simp only [List.map_cons, Renaming.bvar, renumber, ↓reduceIte, hr.tv_cls]
    rw [ih]
    simp only [Renaming.subst, List.map_cons, Renaming.ty, hr.tv_bnd]
  | i, .row e :: vs => by
    have ih := renumber_rename hr (i + 1) vs
    simp only [List.map_cons, Renaming.bvar, renumber]
    rw [ih]
    simp only [Renaming.subst, List.map_cons, Renaming.row, Option.map_some, hr.rv_bnd]

theorem renumber_isBnd : ∀ (k : Bool) (i : Nat) (l : List BVar), ∀ v ∈ (renumber k i l).2, v.isBnd = true
  | _, _, [] => by simp [renumber]
  | k, i, .ty a :: vs => by
    simp only [renumber, List.mem_cons]
    rintro v (rfl | h)
    · rfl
    · exact renumber_isBnd k (i + 1) vs v h
  | k, i, .row e :: vs => by
    simp only [renumber, List.mem_cons]
    rintro v (rfl | h)
    · rfl
    · exact renumber_isBnd k (i + 1) vs v h

theorem Renaming.WF.bvar_of_isBnd {r : Renaming} (hr : r.WF) : ∀ v : BVar, v.isBnd = true → r.bvar v = v
  | .ty (.bnd i c), _ => by simp [Renaming.bvar, hr.tv_bnd]
  | .row (.bnd i), _ => by simp [Renaming.bvar, hr.rv_bnd]
  | .ty (.named _), h | .ty (.fresh _ _), h | .row (.named _), h | .row (.fresh _), h => by
    simp [BVar.isBnd] at h

theorem canonVars_rename {r : Renaming} (hr : r.WF) (bound : List BVar) (body : Ty) :
    canonVars (bound.map r.bvar) (r.ty body) = (canonVars bound body).map r.bvar := by
  have hi := hr.bvar_inj
  simp only [canonVars, vars_rename]
  have h1 : (List.map r.bvar body.vars).filter (fun v => decide (v ∈ bound.map r.bvar)) =
      (body.vars.filter fun v => decide (v ∈ bound)).map r.bvar := by
    rw [List.filter_map]; congr 1; apply List.filter_congr; intro v _
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr (mem_map_inj hi)
  rw [h1, dedupL_map _ hi]
  have h2 : (bound.map r.bvar).filter (fun v => v.isNumTyVar &&
        !decide (v ∈ (dedupL (body.vars.filter fun v => decide (v ∈ bound))).map r.bvar)) =
      (bound.filter fun v => v.isNumTyVar &&
        !decide (v ∈ dedupL (body.vars.filter fun v => decide (v ∈ bound)))).map r.bvar := by
    rw [List.filter_map]; congr 1; apply List.filter_congr; intro v _
    simp only [Function.comp_apply, hr.isNumTyVar_bvar]
    rw [decide_eq_decide.mpr (mem_map_inj hi)]
  rw [h2, dedupL_map _ hi, List.map_append]

theorem canon_rename {r : Renaming} (hr : r.WF) (σ : Scheme) :
    Scheme.canon (r.scheme σ) = r.scheme (Scheme.canon σ) := by
  simp only [Scheme.canon, Renaming.scheme]
  rw [canonVars_rename hr, renumber_rename hr]
  simp only [Scheme.mk.injEq]
  constructor
  · symm
    rw [List.map_congr_left (fun v hv => hr.bvar_of_isBnd v (renumber_isBnd _ _ _ v hv))]
    simp
  · rw [apply_subst_rename hr]
    cases Subst.apply (renumber true 0 (canonVars σ.bound σ.body)).1 σ.body <;> rfl

/-- `canonVars` reads its bound list only on the variables of the body and through its other
    elements in order. -/
theorem canonVars_congr {b1 b2 : List BVar} {body : Ty} (hm : ∀ x ∈ body.vars, x ∈ b1 ↔ x ∈ b2)
    (hf : b1.filter (fun v => !decide (v ∈ body.vars)) = b2.filter (fun v => !decide (v ∈ body.vars))) :
    canonVars b1 body = canonVars b2 body := by
  have hocc : body.vars.filter (fun v => decide (v ∈ b1)) = body.vars.filter (fun v => decide (v ∈ b2)) :=
    List.filter_congr fun x hx => by simp [hm x hx]
  simp only [canonVars, hocc]
  congr 2
  -- an element of the body is in occ, so the vacuous part reads only the others
  have key : ∀ b : List BVar, (∀ x ∈ body.vars, x ∈ b → x ∈ dedupL (body.vars.filter fun v => decide (v ∈ b2))) →
      b.filter (fun v => v.isNumTyVar && !decide (v ∈ dedupL (body.vars.filter fun v => decide (v ∈ b2)))) =
      (b.filter fun v => !decide (v ∈ body.vars)).filter
        (fun v => v.isNumTyVar && !decide (v ∈ dedupL (body.vars.filter fun v => decide (v ∈ b2)))) := by
    intro b hb
    rw [List.filter_filter]
    apply List.filter_congr
    intro x hx
    by_cases hv : x ∈ body.vars
    · have := hb x hv hx
      simp [this, hv]
    · simp [hv]
  rw [key b1 (fun x hx h1 => mem_dedupL.mpr (List.mem_filter.mpr ⟨hx, by simpa using (hm x hx).mp h1⟩)),
    key b2 (fun x hx h2 => mem_dedupL.mpr (List.mem_filter.mpr ⟨hx, by simpa using h2⟩)), hf]

/-! ## Closure and members -/

theorem filter_map_isNum {r : Renaming} (hr : r.WF) (l : List BVar) :
    (l.map r.bvar).filter BVar.isNumTyVar = (l.filter BVar.isNumTyVar).map r.bvar := by
  rw [List.filter_map]; congr 1; apply List.filter_congr; intro v _
  simp [Function.comp_apply, hr.isNumTyVar_bvar]

theorem mem_valEnv_tyvars {VE : ValEnv} {x : BVar} (h : x ∈ ValEnv.tyvars VE) : ∃ p ∈ VE, x ∈ p.2.1.tyvars :=
  mem_tyvarsBy h

theorem closGroup_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {A A' : List BVar}
    (hA : ∀ v, D v → (v ∈ A ↔ r.bvar v ∈ A')) (VE : ValEnv) (hD : ∀ p ∈ VE, ∀ v ∈ p.2.1.tyvars, D v) :
    closGroup A' (r.valEnv VE) = r.valEnv (closGroup A VE) := by
  have hi := hr.bvar_inj
  unfold closGroup FMap.mapV Renaming.valEnv
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, Prod.mk.injEq, and_true, true_and]
  rw [← canon_rename hr]
  congr 1
  simp only [Renaming.scheme, Scheme.mk.injEq, and_true]
  have hVE : ValEnv.tyvars (VE.map fun p => (p.1, ({ bound := p.2.1.bound.map r.bvar, body := r.ty p.2.1.body } : Scheme), p.2.2)) =
      (ValEnv.tyvars VE).map r.bvar := valEnv_tyvars_rename hr VE
  have e0 : ({ bound := p.2.1.bound.map r.bvar, body := r.ty p.2.1.body } : Scheme).tyvars = p.2.1.tyvars.map r.bvar :=
    scheme_tyvars_rename hr p.2.1
  rw [hVE, e0, dedupL_map _ hi, dedupL_map _ hi]
  have e1 : diffL ((dedupL p.2.1.tyvars).map r.bvar) A' = (diffL (dedupL p.2.1.tyvars) A).map r.bvar :=
    diffL_map _ _ _ _ fun x hx => (hA x (hD p hp x (mem_dedupL.mp hx))).symm
  have e2 : diffL ((dedupL (ValEnv.tyvars VE)).map r.bvar) (p.2.1.tyvars.map r.bvar ++ A') =
      (diffL (dedupL (ValEnv.tyvars VE)) (p.2.1.tyvars ++ A)).map r.bvar := by
    apply diffL_map
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_valEnv_tyvars (mem_dedupL.mp hx)
    simp only [List.mem_append, mem_map_inj hi, hA x (hD q hq x hxq)]
  rw [e1, e2, filter_map_isNum hr]
  simp only [List.map_append]

theorem mem_filterMap_tyVar {α : TyVar} {U : List BVar} : α ∈ U.filterMap BVar.tyVar? ↔ BVar.ty α ∈ U := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨v, hv, e⟩
    cases v with
    | ty b => simp only [BVar.tyVar?, Option.some.injEq] at e; subst e; exact hv
    | row _ => simp [BVar.tyVar?] at e
  · intro h; exact ⟨_, h, rfl⟩

/-- A member and its image: the same except the variables of U' that the derivation's types do
    not mention. -/
structure MemberRel (r : Renaming) (D : BVar → Prop) (m m' : Member) : Prop where
  x : m'.x = m.x
  body : m'.body = r.ty m.body
  bOut : m'.bOut = m.bOut.map r.bvar
  bIn : m'.bIn = m.bIn.map r.bvar
  uvars : ∀ α, D (.ty α) → (α ∈ m.uvars ↔ r.tvApply α ∈ m'.uvars)
  bodyD : ∀ v ∈ m.body.vars, D v

theorem memberOf_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {A A' : List BVar}
    (hA : ∀ v, D v → (v ∈ A ↔ r.bvar v ∈ A')) {VEtv : List BVar} (hVE : ∀ v ∈ VEtv, D v)
    (x : Var) (τ : Ty) (hτ : ∀ v ∈ τ.vars, D v) {U U' : List BVar}
    (hU : ∀ v, D v → (v ∈ U ↔ r.bvar v ∈ U')) (ann : Bool) :
    MemberRel r D (memberOf A VEtv x τ U ann) (memberOf A' (VEtv.map r.bvar) x (r.ty τ) U' ann) := by
  have hi := hr.bvar_inj
  -- the variables of U' that τ mentions
  have hUf : ∀ y ∈ τ.vars, (r.bvar y ∈ U'.filter (fun v => decide (v ∈ (r.ty τ).vars)) ↔
      y ∈ U.filter (fun v => decide (v ∈ τ.vars))) := by
    intro y hy
    simp only [List.mem_filter, decide_eq_true_eq, vars_rename, mem_map_inj hi]
    rw [← hU y (hτ y hy)]
  have hσ : diffL (r.ty τ).tyvars (U'.filter fun v => decide (v ∈ (r.ty τ).vars)) =
      (diffL τ.tyvars (U.filter fun v => decide (v ∈ τ.vars))).map r.bvar := by
    rw [tyvars_rename hr]
    exact diffL_map _ _ _ _ fun y hy => hUf y (mem_vars_of_tyvars hy)
  have hσD : ∀ y ∈ diffL τ.tyvars (U.filter fun v => decide (v ∈ τ.vars)), y ∈ τ.vars :=
    fun y hy => mem_vars_of_tyvars (mem_diffL.mp hy).1
  have h2 : diffL (dedupL (diffL (r.ty τ).tyvars (U'.filter fun v => decide (v ∈ (r.ty τ).vars)))) A' =
      (diffL (dedupL (diffL τ.tyvars (U.filter fun v => decide (v ∈ τ.vars)))) A).map r.bvar := by
    rw [hσ, dedupL_map _ hi]
    exact diffL_map _ _ _ _ fun y hy => (hA y (hτ y (hσD y (mem_dedupL.mp hy)))).symm
  have h3 : (diffL (VEtv.map r.bvar) (diffL (r.ty τ).tyvars (U'.filter fun v => decide (v ∈ (r.ty τ).vars)) ++ A')).filter
        BVar.isNumTyVar =
      ((diffL VEtv (diffL τ.tyvars (U.filter fun v => decide (v ∈ τ.vars)) ++ A)).filter BVar.isNumTyVar).map r.bvar := by
    rw [hσ, ← filter_map_isNum hr]
    congr 1
    apply diffL_map
    intro y hy
    simp only [List.mem_append, mem_map_inj hi, hA y (hVE y hy)]
  -- the canonical order reads U' only on the variables of τ
  have hc : ∀ (l1 : List BVar) (l2 : List BVar), (∀ y ∈ l1, y ∈ τ.vars) →
      canonVars ((U'.filter fun v => decide (v ∈ (r.ty τ).vars)) ++ l2.map r.bvar) (r.ty τ) =
      (canonVars ((U.filter fun v => decide (v ∈ τ.vars)) ++ l2) τ).map r.bvar := by
    intro _ l2 _
    rw [← canonVars_rename hr, List.map_append]
    apply canonVars_congr
    · intro y hy
      rw [vars_rename] at hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      simp only [List.mem_append, hUf z hz, mem_map_inj hi]
    · rw [List.filter_append, List.filter_append]
      have n1 : (U'.filter fun v => decide (v ∈ (r.ty τ).vars)).filter (fun v => !decide (v ∈ (r.ty τ).vars)) = [] := by
        rw [List.filter_filter, List.filter_eq_nil_iff]; intro a _
        by_cases h : a ∈ (r.ty τ).vars <;> simp [h]
      have n2 : ((U.filter fun v => decide (v ∈ τ.vars)).map r.bvar).filter (fun v => !decide (v ∈ (r.ty τ).vars)) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
        have : z ∈ τ.vars := by simpa using (List.mem_filter.mp hz).2
        simp [vars_rename, mem_map_inj hi, this]
      rw [n1, n2]
  refine ⟨rfl, rfl, ?_, ?_, ?_, hτ⟩
  · simp only [memberOf]
    rw [h2, h3, List.append_assoc, List.append_assoc, ← List.map_append]
    exact hc [] _ (by simp)
  · simp only [memberOf]
    split
    · have := hc [] [] (by simp); simpa using this
    · rfl
  · intro α hα
    simp only [memberOf, mem_filterMap_tyVar]
    exact hU _ hα

end StandardElm.Stat
