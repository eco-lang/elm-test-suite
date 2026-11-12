/-
  A Standard Definition of Elm? Mechanisation: a renaming followed by a renaming of type names
  (plan step 10). The relation of RenameSpec.lean between the value declarations of two
  derivations, by a renaming r, gives the relation between the first and the second renamed by a
  bijection of type names, by r followed by that bijection (`ItemsRel.thenNames`).
-/
import StandardElmMech.Stat.NameRenInst

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

theorem lookup_graph (f : TyName → TyName) : ∀ (l : List TyName) (t : TyName),
    (l.map fun x => (x, f x)).lookup t = if t ∈ l then some (f t) else none
  | [], _ => by simp
  | x :: xs, t => by
    simp only [List.map_cons, List.lookup, List.mem_cons]
    by_cases e : t = x
    · subst e; simp
    · have : (t == x) = false := beq_eq_false_iff_ne.mpr e
      simp only [this, e, false_or]
      exact lookup_graph f xs t

theorem lookup_none_of_not_mem : ∀ (l : List (TyName × TyName)) (t : TyName), t ∉ l.map (·.1) → l.lookup t = none
  | [], _, _ => rfl
  | (x, y) :: rest, t, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have : (t == x) = false := beq_eq_false_iff_ne.mpr h.1
    simp only [List.lookup, this]
    exact lookup_none_of_not_mem rest t h.2

/-- The type-name part of r followed by ρ, as a finite map. -/
def tnComp (r : Renaming) (ρ : List (TyName × TyName)) : List (TyName × TyName) :=
  (r.tn.map (·.1) ++ ρ.map (·.1)).map fun t => (t, (nr ρ).tnApply (r.tnApply t))

/-- r followed by the renaming of type names ρ. -/
def Renaming.thenNames (r : Renaming) (ρ : List (TyName × TyName)) : Renaming := ⟨r.tv, r.rv, tnComp r ρ⟩

section
variable {r : Renaming} {ρ : List (TyName × TyName)}

theorem thenNames_tn (t : TyName) : (r.thenNames ρ).tnApply t = (nr ρ).tnApply (r.tnApply t) := by
  show ((tnComp r ρ).lookup t).getD t = _
  unfold tnComp
  rw [lookup_graph]
  split
  · rfl
  · rename_i hn
    simp only [List.mem_append, not_or] at hn
    simp only [Option.getD_none]
    show t = ((ρ.lookup ((r.tn.lookup t).getD t)).getD ((r.tn.lookup t).getD t))
    rw [lookup_none_of_not_mem _ _ hn.1]
    simp only [Option.getD_none]
    rw [lookup_none_of_not_mem _ _ hn.2]
    rfl

@[simp] theorem thenNames_tv (a : TyVar) : (r.thenNames ρ).tvApply a = r.tvApply a := rfl
@[simp] theorem thenNames_rv (e : RowVar) : (r.thenNames ρ).rvApply e = r.rvApply e := rfl
@[simp] theorem thenNames_bvar (v : BVar) : (r.thenNames ρ).bvar v = r.bvar v := by cases v <;> rfl

mutual
theorem thenNames_ty : (τ : Ty) → (r.thenNames ρ).ty τ = (nr ρ).ty (r.ty τ)
  | .var _ => rfl
  | .record x tl => by
    simp only [Renaming.ty, thenNames_row x, nr_ty_record]
    cases tl <;> simp
  | .fn a b => by simp only [Renaming.ty, thenNames_ty a, thenNames_ty b, nr_ty_fn]
  | .con as t => by
    simp only [Renaming.ty, thenNames_tys as, thenNames_tn, nr_ty_con, nr_tys]
theorem thenNames_row : (x : Row) → (r.thenNames ρ).row x = (nr ρ).row (r.row x)
  | [] => rfl
  | (l, τ) :: rest => by simp only [Renaming.row, thenNames_ty τ, thenNames_row rest]
theorem thenNames_tys : (l : List Ty) → (r.thenNames ρ).tys l = (nr ρ).tys (r.tys l)
  | [] => rfl
  | τ :: rest => by simp only [Renaming.tys, thenNames_ty τ, thenNames_tys rest]
end

theorem thenNames_scheme (σ : Scheme) : (r.thenNames ρ).scheme σ = (nr ρ).scheme (r.scheme σ) := by
  simp [Renaming.scheme, thenNames_ty, List.map_map, Function.comp_def]

theorem thenNames_valEnv (VE : ValEnv) : (r.thenNames ρ).valEnv VE = (nr ρ).valEnv (r.valEnv VE) := by
  simp [Renaming.valEnv, thenNames_scheme, List.map_map, Function.comp_def]

theorem thenNames_wf (hr : r.WF) (h : NR ρ) : (r.thenNames ρ).WF :=
  ⟨hr.tv_inj, hr.tv_cls, hr.tv_bnd, hr.rv_inj, hr.rv_bnd, fun t t0 h0 => by
    rw [thenNames_tn, h.eq h0, hr.tn_T0 t t0 h0]⟩

theorem thenNames_annRel {D : BVar → Prop} {ann ann' : Option (Src.BTy × List BVar)} (ha : AnnRel r D ann ann') :
    AnnRel (r.thenNames ρ) D ann ((nr ρ).ann ann') := by
  rw [nr_ann_eq]
  rcases ann with _ | ⟨_, U⟩ <;> rcases ann' with _ | ⟨_, U'⟩ <;> simp_all [AnnRel]

variable {D : BVar → Prop}

mutual
theorem RAtExp.thenNames (h : NR ρ) : (a : AAtExp) → ∀ {a' : AAtExp}, RAtExp r D a a' →
    RAtExp (r.thenNames ρ) D a ((nr ρ).atExp a')
  | .scon sc τ, _, hh => by cases hh; rw [Renaming.atExp, ← thenNames_ty]; exact .scon sc τ
  | .var lv inst τ, _, hh => by
    cases hh with
    | var _ _ _ inst'' =>
      rw [Renaming.atExp, ← thenNames_ty]
      exact RAtExp.var (r := r.thenNames ρ) (D := D) lv inst τ ((nr ρ).tys inst'')
  | .con lc inst τ, _, hh => by cases hh; exact .con _ _ _ _ _
  | .op o inst τ, _, hh => by cases hh; exact .op _ _ _ _ _
  | .unit, _, hh => by cases hh; exact .unit
  | .tuple e1 e2 e3, _, hh => by
    cases hh with
    | tuple h1 h2 h3 => exact .tuple (RExp.thenNames h e1 h1) (RExp.thenNames h e2 h2) (RExpOpt.thenNames h e3 h3)
  | .nil τ, _, hh => by cases hh; exact .nil _ _
  | .record row, _, hh => by
    cases hh with
    | record h1 => exact .record (RExpRowOpt.thenNames h row h1)
  | .update x inst τ row, _, hh => by
    cases hh with
    | @update _ _ _ inst'' _ _ h1 =>
      rw [Renaming.atExp, ← thenNames_ty]
      exact RAtExp.update (r := r.thenNames ρ) (D := D) (x := x) (inst := inst) (τ := τ)
        (inst' := (nr ρ).tys inst'') (RExpRow.thenNames h row h1)
  | .letE (.val VE vb) e, _, hh => by
    cases hh with
    | letE hD hvb he =>
      rw [Renaming.atExp, Renaming.dec]
      have := RAtExp.letE (r := r.thenNames ρ) (D := D) hD (RValBind.thenNames h vb hvb) (RExp.thenNames h e he)
      rwa [thenNames_valEnv] at this
  | .paren e, _, hh => by
    cases hh with
    | paren h1 => exact .paren (RExp.thenNames h e h1)
theorem RExpRow.thenNames (h : NR ρ) : (x : AExpRow) → ∀ {x' : AExpRow}, RExpRow r D x x' →
    RExpRow (r.thenNames ρ) D x ((nr ρ).expRow x')
  | .field l e rest, _, hh => by
    cases hh with
    | field h1 h2 => exact .field (RExp.thenNames h e h1) (RExpRowOpt.thenNames h rest h2)
theorem RExpRowOpt.thenNames (h : NR ρ) : (x : Option AExpRow) → ∀ {x' : Option AExpRow}, RExpRowOpt r D x x' →
    RExpRowOpt (r.thenNames ρ) D x ((nr ρ).expRowOpt x')
  | none, _, hh => by cases hh; exact .none
  | some x, _, hh => by cases hh with | some h1 => exact .some (RExpRow.thenNames h x h1)
theorem RExp.thenNames (h : NR ρ) : (e : AExp) → ∀ {e' : AExp}, RExp r D e e' → RExp (r.thenNames ρ) D e ((nr ρ).exp e')
  | .atexp a, _, hh => by cases hh with | atexp h1 => exact .atexp (RAtExp.thenNames h a h1)
  | .app e a, _, hh => by
    cases hh with | app h1 h2 => exact .app (RExp.thenNames h e h1) (RAtExp.thenNames h a h2)
  | .lam p e, _, hh => by
    cases hh with
    | lam he hve h1 =>
      refine .lam (by rw [erase_atPat]; exact he) ?_ (RExp.thenNames h e h1)
      rw [nr_atPat_ve h, hve, thenNames_valEnv]
  | .caseE e m, _, hh => by
    cases hh with | caseE h1 h2 => exact .caseE (RExp.thenNames h e h1) (RMatch.thenNames h m h2)
theorem RExpOpt.thenNames (h : NR ρ) : (e : Option AExp) → ∀ {e' : Option AExp}, RExpOpt r D e e' →
    RExpOpt (r.thenNames ρ) D e ((nr ρ).expOpt e')
  | none, _, hh => by cases hh; exact .none
  | some e, _, hh => by cases hh with | some h1 => exact .some (RExp.thenNames h e h1)
theorem RMatch.thenNames (h : NR ρ) : (m : AMatch) → ∀ {m' : AMatch}, RMatch r D m m' →
    RMatch (r.thenNames ρ) D m ((nr ρ).match_ m')
  | .mk mr rest, _, hh => by
    cases hh with | mk h1 h2 => exact .mk (RMRule.thenNames h mr h1) (RMatchOpt.thenNames h rest h2)
theorem RMatchOpt.thenNames (h : NR ρ) : (m : Option AMatch) → ∀ {m' : Option AMatch}, RMatchOpt r D m m' →
    RMatchOpt (r.thenNames ρ) D m ((nr ρ).matchOpt m')
  | none, _, hh => by cases hh; exact .none
  | some m, _, hh => by cases hh with | some h1 => exact .some (RMatch.thenNames h m h1)
theorem RMRule.thenNames (h : NR ρ) : (mr : AMRule) → ∀ {mr' : AMRule}, RMRule r D mr mr' →
    RMRule (r.thenNames ρ) D mr ((nr ρ).mrule mr')
  | .mk p e, _, hh => by
    cases hh with
    | mk he hve h1 =>
      refine .mk (by rw [erase_pat]; exact he) ?_ (RExp.thenNames h e h1)
      rw [nr_pat_ve h, hve, thenNames_valEnv]
theorem RValBind.thenNames (h : NR ρ) : (vb : AValBind) → ∀ {vb' : AValBind}, RValBind r D vb vb' →
    RValBind (r.thenNames ρ) D vb ((nr ρ).valBind vb')
  | .var x ann τ e rest, _, hh => by
    cases hh with
    | var hann hτ h1 h2 =>
      rw [Renaming.valBind, ← thenNames_ty]
      exact .var (thenNames_annRel hann) hτ (RExp.thenNames h e h1) (RValBindOpt.thenNames h rest h2)
  | .pat p e, _, hh => by
    cases hh with
    | pat he hve hD h1 =>
      refine .pat (by rw [erase_atPat]; exact he) ?_ hD (RExp.thenNames h e h1)
      rw [nr_atPat_ve h, hve, thenNames_valEnv]
theorem RValBindOpt.thenNames (h : NR ρ) : (vb : Option AValBind) → ∀ {vb' : Option AValBind}, RValBindOpt r D vb vb' →
    RValBindOpt (r.thenNames ρ) D vb ((nr ρ).valBindOpt vb')
  | none, _, hh => by cases hh; exact .none
  | some vb, _, hh => by cases hh with | some h1 => exact .some (RValBind.thenNames h vb h1)
end

/-- A top-level item renamed. -/
def TopItem.nrn (ρ : List (TyName × TyName)) : TopItem → TopItem
  | .value VE vb => .value ((nr ρ).valEnv VE) ((nr ρ).valBind vb)
  | it => it

theorem ItemsRel.thenNames (hr : r.WF) (h : NR ρ) :
    ∀ {is is' : List TopItem}, ItemsRel r D is is' → ItemsRel (r.thenNames ρ) D is (is'.map (TopItem.nrn ρ))
  | [], [], _ => trivial
  | .value VE vb :: is, .value VE' vb' :: is', hh => by
    obtain ⟨⟨e1, e2, e3⟩, e4⟩ := hh
    refine ⟨⟨?_, e2, RValBind.thenNames h vb e3⟩, ItemsRel.thenNames hr h e4⟩
    rw [e1, thenNames_valEnv]
  | .types _ _ :: is, .types _ _ :: is', hh => ⟨hh.1, ItemsRel.thenNames hr h hh.2⟩
  | .port _ :: is, .port _ :: is', hh => ⟨hh.1, ItemsRel.thenNames hr h hh.2⟩
  | .value _ _ :: _, .types _ _ :: _, hh | .value _ _ :: _, .port _ :: _, hh
  | .types _ _ :: _, .value _ _ :: _, hh | .types _ _ :: _, .port _ :: _, hh
  | .port _ :: _, .value _ _ :: _, hh | .port _ :: _, .types _ _ :: _, hh
  | [], _ :: _, hh | _ :: _, [], hh => by simp [ItemsRel, ItemRel] at hh

theorem items_nr (d : ATopDec) : ((nr ρ).topDec d).items = d.items.map (TopItem.nrn ρ) := by
  induction d with
  | value VE vb => simp [Renaming.topDec, ATopDec.items, TopItem.nrn]
  | types => simp [Renaming.topDec, ATopDec.items, TopItem.nrn]
  | port => simp [Renaming.topDec, ATopDec.items, TopItem.nrn]
  | seq a1 a2 ih1 ih2 => simp [Renaming.topDec, ATopDec.items, ih1, ih2]

theorem valuesOnly_nr (is : List TopItem) : valuesOnly (is.map (TopItem.nrn ρ)) = (valuesOnly is).map (TopItem.nrn ρ) := by
  induction is with
  | nil => rfl
  | cons it is ih =>
    cases it <;> simp only [valuesOnly, List.map_cons, List.filter_cons, TopItem.isValue, TopItem.nrn] at ih ⊢ <;>
      simp [ih, TopItem.nrn]

end

end StandardElm.Stat
