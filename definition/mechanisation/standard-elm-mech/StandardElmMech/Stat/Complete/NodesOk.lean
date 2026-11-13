/-
  A Standard Definition of Elm? Mechanisation: the types at the nodes of a derivation from the types
  it records (plan step 11; step 9's checker asks every type at a node to be `Ty.okB`).

  `pNodesExp`: a property of types closed under the type constructors the rules build (function
  types, constructed types, closed records with a sorted row) and under taking a codomain holds at
  every node of a derivation when it holds of the types the derivation records (`tysExp false`).
  Instances: `Ty.okB` (`okNodesExp`), from which W's results pass the checker.
-/
import StandardElmMech.Stat.Complete.WPhrase
import StandardElmMech.Stat.Complete.RSubst

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## The row of a record phrase -/

theorem modifyF_single (l : Lab) (τ : Ty) : ∀ (f : Nat) (ρ : Row), ρ.length + 1 ≤ f →
    (Sorted ρ → Sorted (Row.modifyF f [(l, τ)] ρ)) ∧ ∀ x ∈ Row.modifyF f [(l, τ)] ρ, x = (l, τ) ∨ x ∈ ρ
  | f, [], _ => by
    cases f <;> simp only [Row.modifyF] <;>
      exact ⟨fun _ => List.pairwise_singleton _ _, fun x hx => .inl (List.mem_singleton.mp hx)⟩
  | 0, _ :: _, h => by simp at h
  | f + 1, (l2, τ2) :: r2, h => by
    simp only [Row.modifyF]
    split
    · refine ⟨fun hs => ?_, fun x hx => .inr ?_⟩
      · cases r2 <;> simpa [Row.modifyF] using hs
      · cases r2 <;> simpa [Row.modifyF] using hx
    · split
      · rename_i hne hlt
        refine ⟨fun hs => sorted_cons.mpr ⟨fun q hq => ?_, hs⟩, fun x hx => ?_⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact hlt
          · exact labLt_trans hlt ((sorted_cons.mp hs).1 q hq)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inl rfl
          · exact .inr hx
      · rename_i hne hlt
        have h21 : labLt l2 l = true := by
          rcases labLt_tri l l2 with h' | h' | h'
          · exact absurd h' hlt
          · exact absurd h' hne
          · exact h'
        obtain ⟨ih1, ih2⟩ := modifyF_single l τ f r2 (by simp at h; omega)
        refine ⟨fun hs => sorted_cons.mpr ⟨fun q hq => ?_, ih1 (sorted_cons.mp hs).2⟩, fun x hx => ?_⟩
        · rcases ih2 q hq with rfl | hq
          · exact h21
          · exact (sorted_cons.mp hs).1 q hq
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inr (.head _)
          · rcases ih2 x hx with e | e
            · exact .inl e
            · exact .inr (.tail _ e)

theorem sorted_modify1 {l : Lab} {τ : Ty} {ρ : Row} (h : Sorted ρ) : Sorted (Row.modify [(l, τ)] ρ) :=
  (modifyF_single l τ _ ρ (by simp; omega)).1 h

theorem mem_modify1 {l : Lab} {τ : Ty} {ρ : Row} {x : Lab × Ty} (h : x ∈ Row.modify [(l, τ)] ρ) :
    x = (l, τ) ∨ x ∈ ρ :=
  (modifyF_single l τ _ ρ (by simp; omega)).2 x h

theorem mem_rowOpt_tys : ∀ {r : Option APatRow} {p : Lab × Ty}, p ∈ APatRow.rowOpt r → p.2 ∈ tysPatRowOpt r
  | none, _, h => by cases h
  | some (.field l τ rest), p, h => by
    simp only [APatRow.rowOpt, APatRow.row] at h
    simp only [tysPatRowOpt, tysPatRow, List.mem_cons]
    rcases mem_modify1 h with rfl | h
    · exact .inl rfl
    · exact .inr (mem_rowOpt_tys h)


/-! ## Properties closed under the type constructors -/

/-- A property of types closed under the constructors the rules build types with. -/
structure TyClosed (P : Ty → Prop) : Prop where
  fn : ∀ {a b : Ty}, P a → P b → P (.fn a b)
  cod : ∀ {τ : Ty}, P τ → P τ.cod
  con : ∀ {as : List Ty} {t : TyName}, (∀ τ ∈ as, P τ) → P (.con as t)
  record : ∀ {ρ : Row}, Sorted ρ → (∀ p ∈ ρ, P p.2) → P (.record ρ none)

section
variable {P : Ty → Prop}

theorem TyClosed.list (hP : TyClosed P) {τ : Ty} (h : P τ) : P (listTy τ) :=
  hP.con fun x hx => by simp at hx; subst hx; exact h

theorem TyClosed.tuple (hP : TyClosed P) {τ1 τ2 : Ty} {τ3 : Option Ty} (h1 : P τ1) (h2 : P τ2)
    (h3 : ∀ τ, τ3 = some τ → P τ) : P (tupleTy τ1 τ2 τ3) := by
  cases τ3 with
  | none => exact hP.con fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption
  | some τ =>
    exact hP.con fun x hx => by
      simp at hx; rcases hx with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3 _ rfl

theorem TyClosed.unit (hP : TyClosed P) : P tUnitTy := hP.con fun _ h => nomatch h

def PRow (P : Ty → Prop) (ρ : Row) : Prop := Sorted ρ ∧ ∀ p ∈ ρ, P p.2

theorem pRow_nil : PRow P [] := ⟨sorted_nil, fun _ h => nomatch h⟩

theorem pRow_modify1 {l : Lab} {τ : Ty} {ρ : Row} (h1 : P τ) (h2 : PRow P ρ) : PRow P (Row.modify [(l, τ)] ρ) :=
  ⟨sorted_modify1 h2.1, fun p hp => by
    rcases mem_modify1 hp with rfl | hp
    · exact h1
    · exact h2.2 p hp⟩

/-! ## The types of a phrase -/

mutual
theorem p_atpat_ty (hP : TyClosed P) : ∀ p : AAtPat, (∀ τ ∈ tysAtPat p, P τ) → P p.ty
  | .wild _, h | .scon _ _, h | .var _ _, h | .con _ _ _, h | .nil _, h | .record _ _, h => h _ (by simp [tysAtPat, AAtPat.ty])
  | .unit, _ => hP.unit
  | .tuple p1 p2 p3, h => by
    simp only [tysAtPat, List.mem_append] at h
    exact hP.tuple (p_pat_ty hP p1 fun τ hτ => h τ (.inl (.inl hτ))) (p_pat_ty hP p2 fun τ hτ => h τ (.inl (.inr hτ)))
      (p_patopt_ty hP p3 fun τ hτ => h τ (.inr hτ))
  | .paren p, h => by simp only [tysAtPat] at h; exact p_pat_ty hP p h
theorem p_pat_ty (hP : TyClosed P) : ∀ p : APat, (∀ τ ∈ tysPat p, P τ) → P p.ty
  | .atpat a, h => by simp only [tysPat] at h; exact p_atpat_ty hP a h
  | .con _ _ _ _, h => h _ (by simp [tysPat, APat.ty])
  | .cons p1 p2, h => by
    simp only [tysPat, List.mem_append] at h
    exact hP.list (p_pat_ty hP p1 fun τ hτ => h τ (.inl hτ))
  | .as p _, h => by simp only [tysPat] at h; exact p_pat_ty hP p h
theorem p_patopt_ty (hP : TyClosed P) : ∀ p : Option APat, (∀ τ ∈ tysPatOpt p, P τ) → ∀ τ, APat.tyOpt p = some τ → P τ
  | none, _, _, h => by cases h
  | some p, h, τ, e => by
    simp only [APat.tyOpt, Option.some.injEq] at e; subst e
    exact p_pat_ty hP p h
end

mutual
theorem p_atexp_ty (hP : TyClosed P) : ∀ a : AAtExp, (∀ τ ∈ tysAtExp false a, P τ) → P a.ty
  | .scon _ _, h | .var _ _ _, h | .con _ _ _, h | .op _ _ _, h | .nil _, h | .update _ _ _ _, h =>
    h _ (by simp [tysAtExp, AAtExp.ty])
  | .unit, _ => hP.unit
  | .tuple e1 e2 e3, h => by
    simp only [tysAtExp, List.mem_append] at h
    exact hP.tuple (p_exp_ty hP e1 fun τ hτ => h τ (.inl (.inl hτ))) (p_exp_ty hP e2 fun τ hτ => h τ (.inl (.inr hτ)))
      (p_expopt_ty hP e3 fun τ hτ => h τ (.inr hτ))
  | .record r, h => by
    simp only [tysAtExp] at h
    have := p_exprowopt_row hP r h
    exact hP.record this.1 this.2
  | .letE d e, h => by
    simp only [tysAtExp, List.mem_append] at h
    exact p_exp_ty hP e fun τ hτ => h τ (.inr hτ)
  | .paren e, h => by simp only [tysAtExp] at h; exact p_exp_ty hP e h
theorem p_exprow_row (hP : TyClosed P) : ∀ r : AExpRow, (∀ τ ∈ tysExpRow false r, P τ) → PRow P r.row
  | .field l e rest, h => by
    simp only [tysExpRow, List.mem_append] at h
    exact pRow_modify1 (p_exp_ty hP e fun τ hτ => h τ (.inl hτ)) (p_exprowopt_row hP rest fun τ hτ => h τ (.inr hτ))
theorem p_exprowopt_row (hP : TyClosed P) : ∀ r : Option AExpRow, (∀ τ ∈ tysExpRowOpt false r, P τ) → PRow P (AExpRow.rowOpt r)
  | none, _ => pRow_nil
  | some r, h => by simp only [tysExpRowOpt] at h; exact p_exprow_row hP r h
theorem p_exp_ty (hP : TyClosed P) : ∀ e : AExp, (∀ τ ∈ tysExp false e, P τ) → P e.ty
  | .atexp a, h => by simp only [tysExp] at h; exact p_atexp_ty hP a h
  | .app e a, h => by
    simp only [tysExp, List.mem_append] at h
    exact hP.cod (p_exp_ty hP e fun τ hτ => h τ (.inl hτ))
  | .lam p e, h => by
    simp only [tysExp, List.mem_append] at h
    exact hP.fn (p_atpat_ty hP p fun τ hτ => h τ (.inl hτ)) (p_exp_ty hP e fun τ hτ => h τ (.inr hτ))
  | .caseE e m, h => by
    simp only [tysExp, List.mem_append] at h
    exact hP.cod (p_match_ty hP m fun τ hτ => h τ (.inr hτ))
theorem p_expopt_ty (hP : TyClosed P) : ∀ e : Option AExp, (∀ τ ∈ tysExpOpt false e, P τ) → ∀ τ, AExp.tyOpt e = some τ → P τ
  | none, _, _, h => by cases h
  | some e, h, τ, h' => by
    simp only [AExp.tyOpt, Option.some.injEq] at h'; subst h'
    exact p_exp_ty hP e h
theorem p_match_ty (hP : TyClosed P) : ∀ m : AMatch, (∀ τ ∈ tysMatch false m, P τ) → P m.ty
  | .mk (.mk p e) rest, h => by
    simp only [tysMatch, tysMRule, List.mem_append] at h
    exact hP.fn (p_pat_ty hP p fun τ hτ => h τ (.inl (.inl hτ))) (p_exp_ty hP e fun τ hτ => h τ (.inl (.inr hτ)))
end

theorem p_mrule_ty (hP : TyClosed P) : ∀ mr : AMRule, (∀ τ ∈ tysMRule false mr, P τ) → P mr.ty
  | .mk p e, h => by
    simp only [tysMRule, List.mem_append] at h
    exact hP.fn (p_pat_ty hP p fun τ hτ => h τ (.inl hτ)) (p_exp_ty hP e fun τ hτ => h τ (.inr hτ))

/-! ## The nodes of a phrase -/

def PNodes (P : Ty → Prop) (l : List Node) : Prop := ∀ nd ∈ l, ∀ τ ∈ nd.tys, P τ

theorem PNodes.app {P : Ty → Prop} {l1 l2 : List Node} (h1 : PNodes P l1) (h2 : PNodes P l2) : PNodes P (l1 ++ l2) := fun nd hnd => by
  rcases List.mem_append.mp hnd with h | h
  · exact h1 nd h
  · exact h2 nd h

theorem PNodes.single {P : Ty → Prop} {path : List Nat} {U : List BVar} {ts : List Ty} {ss : List Scheme}
    (h : ∀ τ ∈ ts, P τ) : PNodes P [⟨path, U, ts, ss⟩] := fun nd hnd => by
  simp only [List.mem_singleton] at hnd; subst hnd; exact h


mutual
theorem pNodesAtPat (hP : TyClosed P) (U : List BVar) (path : List Nat) : ∀ p : AAtPat, (∀ τ ∈ tysAtPat p, P τ) →
    PNodes P (nodesAtPat U path p)
  | .wild τ0, h | .scon _ τ0, h | .nil τ0, h => by
    simp only [nodesAtPat]
    refine PNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve] at hτ; subst hτ; exact h _ (by simp [tysAtPat])
  | .var x τ0, h => by
    simp only [nodesAtPat]
    refine PNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve, mono] at hτ; subst hτ; exact h _ (by simp [tysAtPat])
  | .con lc inst τ0, h => by
    simp only [nodesAtPat]
    refine PNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve] at hτ; subst hτ; exact h _ (by simp [tysAtPat])
  | .unit, h => by
    simp only [nodesAtPat]
    refine PNodes.single fun τ hτ => ?_
    simp [AAtPat.ty, AAtPat.ve] at hτ; subst hτ; exact hP.unit
  | .tuple p1 p2 p3, h => by
    have hty := p_atpat_ty hP (.tuple p1 p2 p3) h
    simp only [tysAtPat, List.mem_append] at h
    simp only [nodesAtPat]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesPat hP U _ p1 fun τ hτ => h τ (.inl (.inl hτ)))).app
      (pNodesPat hP U _ p2 fun τ hτ => h τ (.inl (.inr hτ))) |>.app (pNodesPatOpt hP U _ p3 fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .record r τ0, h => by
    simp only [tysAtPat, List.mem_cons] at h
    simp only [nodesAtPat]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesPatRowOpt hP U _ r fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .paren p, h => by
    simp only [tysAtPat] at h
    simp only [nodesAtPat]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesPat hP U _ p h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact p_pat_ty hP p h
theorem pNodesPatRowOpt (hP : TyClosed P) (U : List BVar) (path : List Nat) : ∀ r : Option APatRow, (∀ τ ∈ tysPatRowOpt r, P τ) →
    PNodes P (nodesPatRowOpt U path r)
  | none, _ => fun _ h => nomatch h
  | some (.field l τ0 rest), h => by
    simp only [nodesPatRowOpt, nodesPatRow]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesPatRowOpt hP U _ rest fun τ hτ => h τ (by
      simp only [tysPatRowOpt, tysPatRow, List.mem_cons]; exact .inr hτ))
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hτ
    rcases hτ with rfl | ⟨p, hp, rfl⟩
    · exact h _ (by simp [tysPatRowOpt, tysPatRow])
    · exact h _ (mem_rowOpt_tys (r := some (.field l τ0 rest)) hp)
theorem pNodesPat (hP : TyClosed P) (U : List BVar) (path : List Nat) : ∀ p : APat, (∀ τ ∈ tysPat p, P τ) →
    PNodes P (nodesPat U path p)
  | .atpat a, h => by
    simp only [tysPat] at h
    simp only [nodesPat]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesAtPat hP U _ a h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact p_atpat_ty hP a h
  | .con lc inst args τ0, h => by
    simp only [tysPat, List.mem_cons] at h
    simp only [nodesPat]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesAtPats hP U path 0 args fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .cons p1 p2, h => by
    have hty := p_pat_ty hP (.cons p1 p2) h
    simp only [tysPat, List.mem_append] at h
    simp only [nodesPat]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesPat hP U _ p1 fun τ hτ => h τ (.inl hτ))).app
      (pNodesPat hP U _ p2 fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .as p x, h => by
    simp only [tysPat] at h
    simp only [nodesPat]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesPat hP U _ p h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact p_pat_ty hP p h
theorem pNodesPatOpt (hP : TyClosed P) (U : List BVar) (path : List Nat) : ∀ p : Option APat, (∀ τ ∈ tysPatOpt p, P τ) →
    PNodes P (nodesPatOpt U path p)
  | none, _ => fun _ h => nomatch h
  | some p, h => by simp only [tysPatOpt] at h; simp only [nodesPatOpt]; exact pNodesPat hP U path p h
theorem pNodesAtPats (hP : TyClosed P) (U : List BVar) (path : List Nat) : ∀ (i : Nat) (l : List AAtPat), (∀ τ ∈ tysAtPats l, P τ) →
    PNodes P (nodesAtPats U path i l)
  | _, [], _ => fun _ h => nomatch h
  | i, a :: as, h => by
    simp only [tysAtPats, List.mem_append] at h
    simp only [nodesAtPats]
    exact (pNodesAtPat hP U _ a fun τ hτ => h τ (.inl hτ)).app (pNodesAtPats hP U path (i + 1) as fun τ hτ => h τ (.inr hτ))
end

mutual
theorem pNodesAtExp (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ a : AAtExp, (∀ τ ∈ tysAtExp false a, P τ) →
    PNodes P (nodesAtExp C path a)
  | .scon _ τ0, h | .var _ _ τ0, h | .con _ _ τ0, h | .op _ _ τ0, h | .nil τ0, h => by
    simp only [nodesAtExp]
    refine PNodes.single fun τ hτ => ?_
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (by simp [tysAtExp])
  | .unit, _ => by
    simp only [nodesAtExp]
    refine PNodes.single fun τ hτ => ?_
    simp only [List.mem_singleton] at hτ; subst hτ; exact hP.unit
  | .tuple e1 e2 e3, h => by
    have hty := p_atexp_ty hP (.tuple e1 e2 e3) h
    simp only [tysAtExp, List.mem_append] at h
    simp only [nodesAtExp]
    refine (((PNodes.single fun τ hτ => ?_).app (pNodesExp hP C _ e1 fun τ hτ => h τ (.inl (.inl hτ)))).app
      (pNodesExp hP C _ e2 fun τ hτ => h τ (.inl (.inr hτ)))).app (pNodesExpOpt hP C _ e3 fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .record r, h => by
    have hty := p_atexp_ty hP (.record r) h
    simp only [tysAtExp] at h
    simp only [nodesAtExp]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesExpRowOpt hP C _ r h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .update x inst τ0 r, h => by
    simp only [tysAtExp, List.mem_cons] at h
    simp only [nodesAtExp]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesExpRow hP C _ r fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .letE d e, h => by
    simp only [tysAtExp, List.mem_append] at h
    simp only [nodesAtExp]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesDec hP C _ d fun τ hτ => h τ (.inl hτ))).app
      (pNodesExp hP _ _ e fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact p_exp_ty hP e fun τ hτ => h τ (.inr hτ)
  | .paren e, h => by
    simp only [tysAtExp] at h
    simp only [nodesAtExp]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesExp hP C _ e h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact p_exp_ty hP e h
theorem pNodesExpRow (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ r : AExpRow, (∀ τ ∈ tysExpRow false r, P τ) →
    PNodes P (nodesExpRow C path r)
  | .field l e rest, h => by
    have hrow := p_exprow_row hP (.field l e rest) h
    simp only [tysExpRow, List.mem_append] at h
    simp only [nodesExpRow]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesExp hP C _ e fun τ hτ => h τ (.inl hτ))).app
      (pNodesExpRowOpt hP C _ rest fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_map] at hτ
    obtain ⟨p, hp, rfl⟩ := hτ
    exact hrow.2 p hp
theorem pNodesExpRowOpt (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ r : Option AExpRow, (∀ τ ∈ tysExpRowOpt false r, P τ) →
    PNodes P (nodesExpRowOpt C path r)
  | none, _ => fun _ h => nomatch h
  | some r, h => by simp only [tysExpRowOpt] at h; simp only [nodesExpRowOpt]; exact pNodesExpRow hP C path r h
theorem pNodesExp (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ e : AExp, (∀ τ ∈ tysExp false e, P τ) →
    PNodes P (nodesExp C path e)
  | .atexp a, h => by
    simp only [tysExp] at h
    simp only [nodesExp]
    refine (PNodes.single fun τ hτ => ?_).app (pNodesAtExp hP C _ a h)
    simp only [List.mem_singleton] at hτ; subst hτ; exact p_atexp_ty hP a h
  | .app e a, h => by
    have hty := p_exp_ty hP (.app e a) h
    simp only [tysExp, List.mem_append] at h
    simp only [nodesExp]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesExp hP C _ e fun τ hτ => h τ (.inl hτ))).app
      (pNodesAtExp hP C _ a fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .lam p e, h => by
    have hty := p_exp_ty hP (.lam p e) h
    simp only [tysExp, List.mem_append] at h
    simp only [nodesExp]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesAtPat hP C.U _ p fun τ hτ => h τ (.inl hτ))).app
      (pNodesExp hP _ _ e fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
  | .caseE e m, h => by
    have hty := p_exp_ty hP (.caseE e m) h
    simp only [tysExp, List.mem_append] at h
    simp only [nodesExp]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesExp hP C _ e fun τ hτ => h τ (.inl hτ))).app
      (pNodesMatch hP C _ m fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
theorem pNodesExpOpt (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ e : Option AExp, (∀ τ ∈ tysExpOpt false e, P τ) →
    PNodes P (nodesExpOpt C path e)
  | none, _ => fun _ h => nomatch h
  | some e, h => by simp only [tysExpOpt] at h; simp only [nodesExpOpt]; exact pNodesExp hP C path e h
theorem pNodesMatch (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ m : AMatch, (∀ τ ∈ tysMatch false m, P τ) →
    PNodes P (nodesMatch C path m)
  | .mk (.mk p e) rest, h => by
    have hty := p_mrule_ty hP (.mk p e) fun τ hτ => h τ (by simp only [tysMatch, List.mem_append]; exact .inl hτ)
    simp only [tysMatch, tysMRule, List.mem_append] at h
    simp only [nodesMatch]
    refine (((PNodes.single fun τ hτ => ?_).app (pNodesPat hP C.U _ p fun τ hτ => h τ (.inl (.inl hτ)))).app
      (pNodesExp hP _ _ e fun τ hτ => h τ (.inl (.inr hτ)))).app (pNodesMatchOpt hP C _ rest fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact hty
theorem pNodesMatchOpt (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ m : Option AMatch, (∀ τ ∈ tysMatchOpt false m, P τ) →
    PNodes P (nodesMatchOpt C path m)
  | none, _ => fun _ h => nomatch h
  | some m, h => by simp only [tysMatchOpt] at h; simp only [nodesMatchOpt]; exact pNodesMatch hP C path m h
theorem pNodesDec (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ d : ADec, (∀ τ ∈ tysDec false d, P τ) →
    PNodes P (nodesDec C path d)
  | .val VE vb, h => by
    simp only [tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h
    simp only [nodesDec]
    exact (PNodes.single fun τ hτ => by cases hτ).app (pNodesValBind hP _ _ vb h)
theorem pNodesValBind (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ vb : AValBind, (∀ τ ∈ tysValBind false vb, P τ) →
    PNodes P (nodesValBind C path vb)
  | .var x ann τ0 e rest, h => by
    simp only [tysValBind, annMark, List.nil_append, List.cons_append, List.mem_cons, List.mem_append] at h
    simp only [nodesValBind]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesExp hP _ _ e fun τ hτ => h τ (.inr (.inl hτ)))).app
      (pNodesValBindOpt hP C _ rest fun τ hτ => h τ (.inr (.inr hτ)))
    simp only [List.mem_singleton] at hτ; subst hτ; exact h _ (.inl rfl)
  | .pat p e, h => by
    simp only [tysValBind, List.mem_append] at h
    simp only [nodesValBind]
    refine ((PNodes.single fun τ hτ => ?_).app (pNodesAtPat hP C.U _ p fun τ hτ => h τ (.inl hτ))).app
      (pNodesExp hP C _ e fun τ hτ => h τ (.inr hτ))
    simp only [List.mem_singleton] at hτ; subst hτ; exact p_atpat_ty hP p fun τ hτ => h τ (.inl hτ)
theorem pNodesValBindOpt (hP : TyClosed P) (C : Ctx) (path : List Nat) : ∀ vb : Option AValBind, (∀ τ ∈ tysValBindOpt false vb, P τ) →
    PNodes P (nodesValBindOpt C path vb)
  | none, _ => fun _ h => nomatch h
  | some vb, h => by simp only [tysValBindOpt] at h; simp only [nodesValBindOpt]; exact pNodesValBind hP C path vb h
end

end

/-! ## `Ty.okB` -/

theorem okB_closed : TyClosed fun τ => Ty.okB τ = true where
  fn h1 h2 := by
    simp only [Ty.okB, cnB, Ty.vars, List.all_append, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
  cod {τ} h := by
    cases τ with
    | fn a b =>
      simp only [Ty.okB, cnB, Ty.vars, List.all_append, Bool.and_eq_true] at h
      simp only [Ty.cod, Ty.okB, Bool.and_eq_true]; exact ⟨h.1.2, h.2.2⟩
    | _ => exact h
  con {as t} h := by
    simp only [Ty.okB_iff] at h ⊢
    refine ⟨cnListB_iff.mpr fun τ hτ => (h τ hτ).1, fun v hv => ?_⟩
    simp only [Ty.vars] at hv
    obtain ⟨τ, hτ, hv⟩ := mem_listVarsR.mp hv
    exact (h τ hτ).2 v hv
  record {ρ} hs h := by
    simp only [Ty.okB_iff] at h ⊢
    refine ⟨cnB_record.mpr ⟨hs, fun p hp => (h p hp).1⟩, fun v hv => ?_⟩
    simp only [Ty.vars] at hv
    obtain ⟨p, hp, hv⟩ := mem_rowVarsR.mp hv
    exact (h p hp).2 v hv

/-- Every type at a node of a derivation is `Ty.okB` when every type it records is. -/
theorem okNodesExp (C : Ctx) (path : List Nat) (e : AExp) (h : ∀ τ ∈ tysExp false e, Ty.okB τ = true) :
    ∀ n ∈ nodesExp C path e, ∀ τ ∈ n.tys, Ty.okB τ = true :=
  pNodesExp okB_closed C path e h

/-! ## Types whose image is `Ty.okB` -/

theorem labs_sbRow (s : FSub) : ∀ ρ : Row, labs (sbRow s ρ) = labs ρ
  | [] => rfl
  | (l, τ) :: rest => by simp only [sbRow, labs, List.map_cons]; exact congrArg _ (labs_sbRow s rest)

mutual
theorem cnB_of_sb (s : FSub) : ∀ τ : Ty, cnB (sb s τ) = true → cnB τ = true
  | .var _, _ => rfl
  | .record ρ tl, h => by
    simp only [sb, cnB, Bool.and_eq_true, labs_sbRow] at h ⊢
    exact ⟨h.1, cnRowB_of_sb s ρ h.2⟩
  | .fn a b, h => by
    simp only [sb, cnB, Bool.and_eq_true] at h ⊢; exact ⟨cnB_of_sb s a h.1, cnB_of_sb s b h.2⟩
  | .con as t, h => by simp only [sb, cnB] at h ⊢; exact cnListB_of_sb s as h
theorem cnRowB_of_sb (s : FSub) : ∀ ρ : Row, cnRowB (sbRow s ρ) = true → cnRowB ρ = true
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [sbRow, cnRowB, Bool.and_eq_true] at h ⊢; exact ⟨cnB_of_sb s τ h.1, cnRowB_of_sb s rest h.2⟩
theorem cnListB_of_sb (s : FSub) : ∀ l : List Ty, cnListB (sbList s l) = true → cnListB l = true
  | [], _ => rfl
  | τ :: rest, h => by
    simp only [sbList, cnListB, Bool.and_eq_true] at h ⊢; exact ⟨cnB_of_sb s τ h.1, cnListB_of_sb s rest h.2⟩
end

mutual
theorem rowVar_sb (s : FSub) (e : RowVar) : ∀ τ : Ty, BVar.row e ∈ τ.vars → BVar.row e ∈ (sb s τ).vars
  | .var _, h => by simp [Ty.vars] at h
  | .record ρ none, h => by simp only [sb, Ty.vars] at h ⊢; exact rowVar_sbRow s e ρ h
  | .record ρ (some e'), h => by
    simp only [sb, Ty.vars, List.mem_append, List.mem_singleton] at h ⊢
    rcases h with h | h
    · exact .inl (rowVar_sbRow s e ρ h)
    · exact .inr h
  | .fn a b, h => by
    simp only [sb, Ty.vars, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (rowVar_sb s e a h)
    · exact .inr (rowVar_sb s e b h)
  | .con as _, h => by simp only [sb, Ty.vars] at h ⊢; exact rowVar_sbList s e as h
theorem rowVar_sbRow (s : FSub) (e : RowVar) : ∀ ρ : Row, BVar.row e ∈ Ty.rowVars ρ → BVar.row e ∈ Ty.rowVars (sbRow s ρ)
  | [], h => by simp [Ty.rowVars] at h
  | (l, τ) :: rest, h => by
    simp only [sbRow, Ty.rowVars, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (rowVar_sb s e τ h)
    · exact .inr (rowVar_sbRow s e rest h)
theorem rowVar_sbList (s : FSub) (e : RowVar) : ∀ l : List Ty, BVar.row e ∈ Ty.listVars l → BVar.row e ∈ Ty.listVars (sbList s l)
  | [], h => by simp [Ty.listVars] at h
  | τ :: rest, h => by
    simp only [sbList, Ty.listVars, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (rowVar_sb s e τ h)
    · exact .inr (rowVar_sbList s e rest h)
end

/-- A type whose image, under a substitution fixing the `bnd` variables, is `Ty.okB` is `Ty.okB`. -/
theorem okB_of_sb {T : FSub} (hT : ∀ i c, T (.bnd i c) = .var (.bnd i c)) {τ : Ty}
    (h : Ty.okB (sb T τ) = true) : Ty.okB τ = true := by
  rw [Ty.okB_iff] at h ⊢
  refine ⟨cnB_of_sb T τ h.1, fun v hv => ?_⟩
  cases hb : v.isBnd with
  | false => rfl
  | true =>
    exfalso
    rcases v with ((_ | _ | ⟨i, c⟩) | (_ | _ | i)) <;> simp [BVar.isBnd] at hb
    · have := h.2 (.ty (.bnd i c)) (vars_sb_of T τ (.bnd i c) _ hv (by rw [hT]; simp [Ty.vars]))
      simp [BVar.isBnd] at this
    · have := h.2 _ (rowVar_sb T _ τ hv)
      simp [BVar.isBnd] at this

end StandardElm.Stat.Complete
