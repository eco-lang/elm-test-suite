/-
  A Standard Definition of Elm? Mechanisation: templates for the completeness of `coreGen`, plan
  step 11, milestone (a).

  A *template* (`GInfo.tmpl t K`, Core.lean) stands for a value whose scheme a derivation gives
  as a canonical form of a type `τ0` known up to the names of local types and the sorts of
  annotation variables (an annotated member: its annotation; a local constructor: its
  declaration). Every instance of such a scheme is `S τ0` for a class-respecting substitution
  `S` (`InstOf`, `instOf_gen`), also after the closure of a group (`instOf_close`); and every
  such `S τ0`, normalised, is the template under a valuation of its metavariables that satisfies
  its class constraints (`tmpl_ok`). An occurrence names the template's metavariables by their
  first positions, read off the occurrence's type (`reloc_ev`).
-/
import StandardElmMech.Stat.Complete.Core

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Finite maps and rows -/

theorem tfind?_mem {K V : Type} [DecidableEq K] {k : K} {v : V} : ∀ {l : FMap K V}, FMap.find? l k = some v → (k, v) ∈ l
  | [], h => by cases h
  | (k', v') :: rest, h => by
    simp only [FMap.find?] at h
    split at h
    · rename_i e; subst e; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (tfind?_mem h)

theorem tmerge_nil (ρ : Row) : Row.merge ρ [] = some ρ := by
  cases ρ <;> simp [Row.merge, Row.mergeF]

theorem tmerge_nil_left (ρ : Row) : Row.merge [] ρ = some ρ := by
  cases ρ <;> simp [Row.merge, Row.mergeF]

/-! ## Inverting the normalisation -/

theorem hN_fn_inv {τ a b : Ty} (h : hN τ = .fn a b) : ∃ x y, τ = .fn x y ∧ hN x = a ∧ hN y = b := by
  cases τ with
  | var _ => simp [hN] at h
  | record ρ tl =>
    exfalso
    simp only [hN] at h
    rcases hRec_cases (hNRow ρ) tl with ⟨e, _⟩ | ⟨s, _, _, _, e⟩ <;> rw [e] at h <;> cases h
  | fn x y => simp only [hN, Ty.fn.injEq] at h; exact ⟨x, y, rfl, h.1, h.2⟩
  | con _ _ => simp [hN] at h

theorem hN_con_inv {τ : Ty} {as : List Ty} {tn : TyName} (h : hN τ = .con as tn) :
    ∃ xs t, τ = .con xs t ∧ hNList xs = as ∧ gN t = tn := by
  cases τ with
  | var _ => simp [hN] at h
  | record ρ tl =>
    exfalso
    simp only [hN] at h
    rcases hRec_cases (hNRow ρ) tl with ⟨e, _⟩ | ⟨s, _, _, _, e⟩ <;> rw [e] at h <;> cases h
  | fn x y => simp [hN] at h
  | con xs t => simp only [hN, Ty.con.injEq] at h; exact ⟨xs, t, rfl, h.1, h.2⟩

theorem hN_rec_inv' {τ : Ty} {ρ : Row} {tl : Option RowVar} (h : hN τ = .record ρ tl) :
    ∃ xs, τ = .record xs tl ∧ hNRow xs = ρ := by
  cases τ with
  | var _ => simp [hN] at h
  | fn _ _ => simp [hN] at h
  | con _ _ => simp [hN] at h
  | record xs tl' =>
    simp only [hN] at h
    rcases hRec_cases (hNRow xs) tl' with ⟨e, _⟩ | ⟨s, _, _, _, e⟩ <;> rw [e] at h
    · simp only [Ty.record.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact ⟨xs, rfl, h1⟩
    · cases h

theorem hN_rec_inv {τ : Ty} {ρ : Row} (h : hN τ = .record ρ none) : ∃ xs, τ = .record xs none ∧ hNRow xs = ρ :=
  hN_rec_inv' h

/-! ## Renamings and composition -/

/-- A substitution that renames type variables (keeping classes) and maps row variables to rows
    with no field. -/
def RenS (R : Subst) : Prop :=
  (∀ p ∈ R.ty, ∃ a', p.2 = .var a' ∧ a'.cls = p.1.cls) ∧ (∀ p ∈ R.row, p.2.1 = [])

def tailComp (S : Subst) : Option RowVar → Row × Option RowVar
  | some e' => (FMap.find? S.row e').getD ([], some e')
  | none => ([], none)

/-- S after R, for a renaming R. -/
def compS (S R : Subst) : Subst :=
  ⟨R.ty.map (fun p => (p.1, (S.apply p.2).getD p.2)) ++ S.ty,
   R.row.map (fun p => (p.1, tailComp S p.2.2)) ++ S.row⟩

theorem find?_map_snd' {K V W : Type} [DecidableEq K] (g : V → W) (k : K) (l : List (K × V)) :
    FMap.find? (l.map (fun p => (p.1, g p.2))) k = (FMap.find? l k).map g := find?_map_val g k l

theorem renS_id : RenS Subst.id := ⟨fun _ h => (by simp [Subst.id] at h), fun _ h => (by simp [Subst.id] at h)⟩

mutual
theorem tapply_id : ∀ τ : Ty, Subst.id.apply τ = some τ
  | .var _ => rfl
  | .record ρ none => by simp only [Subst.apply, tapplyRow_id ρ]
  | .record ρ (some e) => by simp only [Subst.apply, tapplyRow_id ρ]; rfl
  | .fn a b => by simp only [Subst.apply, tapply_id a, tapply_id b]
  | .con as t => by simp only [Subst.apply, tapplyList_id as]
theorem tapplyRow_id : ∀ ρ : Row, Subst.id.applyRow ρ = some ρ
  | [] => rfl
  | (l, x) :: r => by simp only [Subst.applyRow, tapply_id x, tapplyRow_id r]
theorem tapplyList_id : ∀ l : List Ty, Subst.id.applyList l = some l
  | [] => rfl
  | x :: r => by simp only [Subst.applyList, tapply_id x, tapplyList_id r]
end

section comp
set_option linter.unusedSectionVars false
variable {S R : Subst} (hR : RenS R)
include hR

theorem compS_row (e : RowVar) :
    FMap.find? (compS S R).row e =
      match FMap.find? R.row e with
      | some p => some (tailComp S p.2)
      | none => FMap.find? S.row e := by
  simp only [compS, FMap.find?_append, find?_map_snd' (fun p : Row × Option RowVar => tailComp S p.2)]
  cases FMap.find? R.row e <;> rfl

mutual
theorem apply_comp : ∀ (τ X Y : Ty), R.apply τ = some X → S.apply X = some Y → (compS S R).apply τ = some Y
  | .var a, X, Y, h1, h2 => by
    simp only [Subst.apply, Option.some.injEq] at h1
    subst h1
    simp only [Subst.apply, compS, FMap.find?_append, find?_map_snd' (fun t => (S.apply t).getD t)]
    cases hf : FMap.find? R.ty a with
    | none => simp only [hf, Option.getD_none, Subst.apply] at h2; simpa [hf] using h2
    | some t => simp only [hf, Option.getD_some] at h2; simp [hf, h2]
  | .record ρ none, X, Y, h1, h2 => by
    simp only [Subst.apply] at h1
    cases hρ : R.applyRow ρ with
    | none => rw [hρ] at h1; cases h1
    | some ρ1 =>
      rw [hρ] at h1
      simp only [Option.some.injEq] at h1
      subst h1
      simp only [Subst.apply] at h2
      cases hρ1 : S.applyRow ρ1 with
      | none => rw [hρ1] at h2; cases h2
      | some ρ2 =>
        rw [hρ1] at h2
        simp only [Subst.apply, applyRow_comp ρ ρ1 ρ2 hρ hρ1]
        exact h2
  | .record ρ (some e), X, Y, h1, h2 => by
    simp only [Subst.apply] at h1
    cases hρ : R.applyRow ρ with
    | none => rw [hρ] at h1; cases h1
    | some ρ1 =>
      rw [hρ] at h1
      simp only at h1
      simp only [Subst.apply]
      cases hRe : FMap.find? R.row e with
      | none =>
        rw [hRe] at h1
        simp only [Option.some.injEq] at h1
        subst h1
        simp only [Subst.apply] at h2
        cases hρ1 : S.applyRow ρ1 with
        | none => rw [hρ1] at h2; cases h2
        | some ρ2 =>
          rw [hρ1] at h2
          simp only at h2
          rw [applyRow_comp ρ ρ1 ρ2 hρ hρ1, compS_row hR, hRe]
          exact h2
      | some p =>
        obtain ⟨ρr, tl⟩ := p
        have hρr : ρr = [] := hR.2 _ (tfind?_mem hRe)
        subst hρr
        rw [hRe] at h1
        simp only [tmerge_nil, Option.some.injEq] at h1
        subst h1
        rw [compS_row hR, hRe]
        simp only
        cases tl with
        | none =>
          simp only [Subst.apply] at h2
          cases hρ1 : S.applyRow ρ1 with
          | none => rw [hρ1] at h2; cases h2
          | some ρ2 =>
            rw [hρ1] at h2
            simp only [Option.some.injEq] at h2
            subst h2
            rw [applyRow_comp ρ ρ1 ρ2 hρ hρ1]
            simp [tailComp, tmerge_nil]
        | some e' =>
          simp only [Subst.apply] at h2
          cases hρ1 : S.applyRow ρ1 with
          | none => rw [hρ1] at h2; cases h2
          | some ρ2 =>
            rw [hρ1] at h2
            simp only at h2
            rw [applyRow_comp ρ ρ1 ρ2 hρ hρ1]
            simp only [tailComp]
            cases hSe : FMap.find? S.row e' with
            | none =>
              rw [hSe] at h2
              simp only [Option.getD_none, tmerge_nil]
              exact h2
            | some q =>
              rw [hSe] at h2
              simp only [Option.getD_some]
              exact h2
  | .fn a b, X, Y, h1, h2 => by
    simp only [Subst.apply] at h1
    cases ha : R.apply a with
    | none => rw [ha] at h1; cases h1
    | some a1 =>
      cases hb : R.apply b with
      | none => rw [ha, hb] at h1; cases h1
      | some b1 =>
        rw [ha, hb] at h1
        simp only [Option.some.injEq] at h1
        subst h1
        simp only [Subst.apply] at h2
        cases ha' : S.apply a1 with
        | none => rw [ha'] at h2; cases h2
        | some a2 =>
          cases hb' : S.apply b1 with
          | none => rw [ha', hb'] at h2; cases h2
          | some b2 =>
            rw [ha', hb'] at h2
            simp only [Subst.apply, apply_comp a a1 a2 ha ha', apply_comp b b1 b2 hb hb']
            exact h2
  | .con as t, X, Y, h1, h2 => by
    simp only [Subst.apply] at h1
    cases has : R.applyList as with
    | none => rw [has] at h1; cases h1
    | some as1 =>
      rw [has] at h1
      simp only [Option.some.injEq] at h1
      subst h1
      simp only [Subst.apply] at h2
      cases has' : S.applyList as1 with
      | none => rw [has'] at h2; cases h2
      | some as2 =>
        rw [has'] at h2
        simp only [Subst.apply, applyList_comp as as1 as2 has has']
        exact h2
theorem applyRow_comp : ∀ (ρ X Y : Row), R.applyRow ρ = some X → S.applyRow X = some Y →
    (compS S R).applyRow ρ = some Y
  | [], X, Y, h1, h2 => by
    simp only [Subst.applyRow, Option.some.injEq] at h1
    subst h1
    simpa [Subst.applyRow] using h2
  | (l, x) :: r, X, Y, h1, h2 => by
    simp only [Subst.applyRow] at h1
    cases hx : R.apply x with
    | none => rw [hx] at h1; cases h1
    | some x1 =>
      cases hr : R.applyRow r with
      | none => rw [hx, hr] at h1; cases h1
      | some r1 =>
        rw [hx, hr] at h1
        simp only [Option.some.injEq] at h1
        subst h1
        simp only [Subst.applyRow] at h2
        cases hx' : S.apply x1 with
        | none => rw [hx'] at h2; cases h2
        | some x2 =>
          cases hr' : S.applyRow r1 with
          | none => rw [hx', hr'] at h2; cases h2
          | some r2 =>
            rw [hx', hr'] at h2
            simp only [Subst.applyRow, apply_comp x x1 x2 hx hx', applyRow_comp r r1 r2 hr hr']
            exact h2
theorem applyList_comp : ∀ (l X Y : List Ty), R.applyList l = some X → S.applyList X = some Y →
    (compS S R).applyList l = some Y
  | [], X, Y, h1, h2 => by
    simp only [Subst.applyList, Option.some.injEq] at h1
    subst h1
    simpa [Subst.applyList] using h2
  | x :: r, X, Y, h1, h2 => by
    simp only [Subst.applyList] at h1
    cases hx : R.apply x with
    | none => rw [hx] at h1; cases h1
    | some x1 =>
      cases hr : R.applyList r with
      | none => rw [hx, hr] at h1; cases h1
      | some r1 =>
        rw [hx, hr] at h1
        simp only [Option.some.injEq] at h1
        subst h1
        simp only [Subst.applyList] at h2
        cases hx' : S.apply x1 with
        | none => rw [hx'] at h2; cases h2
        | some x2 =>
          cases hr' : S.applyList r1 with
          | none => rw [hx', hr'] at h2; cases h2
          | some r2 =>
            rw [hx', hr'] at h2
            simp only [Subst.applyList, apply_comp x x1 x2 hx hx', applyList_comp r r1 r2 hr hr']
            exact h2
end

end comp

theorem adm_var_self (a : TyVar) : Adm a.cls (.var a) := by
  cases h : a.cls
  · exact .any _
  · exact .num_var a h
  · exact .comp_var a (by rw [h]; rfl)
  · exact .app_var a (by rw [h]; rfl)
  · exact .capp_var a h

theorem adm_apply_var {S : Subst} (hS : S.Respects) (a : TyVar) :
    Adm a.cls ((FMap.find? S.ty a).getD (.var a)) := by
  cases hf : FMap.find? S.ty a with
  | none => exact adm_var_self a
  | some τ => exact hS _ (tfind?_mem hf)

theorem respects_comp {S R : Subst} (hR : RenS R) (hS : S.Respects) : (compS S R).Respects := by
  intro p hp
  simp only [compS, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩ | hp
  · obtain ⟨a', he, hc⟩ := hR.1 q hq
    simp only [he, Subst.apply, Option.getD_some, ← hc]
    exact adm_apply_var hS a'
  · exact hS p hp

theorem renS_comp {R2 R1 : Subst} (h2 : RenS R2) (h1 : RenS R1) : RenS (compS R2 R1) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [compS, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · obtain ⟨a', he, hc⟩ := h1.1 q hq
      simp only [he, Subst.apply, Option.getD_some, ← hc]
      cases hf : FMap.find? R2.ty a' with
      | none => exact ⟨a', rfl, rfl⟩
      | some τ =>
        obtain ⟨a'', he', hc'⟩ := h2.1 _ (tfind?_mem hf)
        exact ⟨a'', by simpa using he', hc'⟩
    · exact h2.1 p hp
  · simp only [compS, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, _, rfl⟩ | hp
    · simp only [tailComp]
      split
      · rename_i e' _
        cases hf : FMap.find? R2.row e' with
        | none => rfl
        | some r => simpa [hf] using h2.2 _ (tfind?_mem hf)
      · rfl
    · exact h2.2 p hp

theorem renumber_ren : ∀ (i : Nat) (l : List BVar), RenS (renumber true i l).1
  | _, [] => renS_id
  | i, .ty a :: vs => by
    have ih := renumber_ren (i + 1) vs
    simp only [renumber]
    revert ih
    generalize renumber true (i + 1) vs = r
    obtain ⟨S, bs⟩ := r
    intro ih
    refine ⟨fun p hp => ?_, fun p hp => ih.2 p hp⟩
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨_, rfl, by simp [TyVar.cls]⟩
    · exact ih.1 p hp
  | i, .row e :: vs => by
    have ih := renumber_ren (i + 1) vs
    simp only [renumber]
    revert ih
    generalize renumber true (i + 1) vs = r
    obtain ⟨S, bs⟩ := r
    intro ih
    refine ⟨fun p hp => ih.1 p hp, fun p hp => ?_⟩
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact ih.2 p hp

mutual
theorem ren_apply_some {R : Subst} (hR : RenS R) : ∀ τ : Ty, ∃ τ', R.apply τ = some τ'
  | .var _ => ⟨_, rfl⟩
  | .record ρ none => by
    obtain ⟨ρ', h⟩ := ren_applyRow_some hR ρ
    exact ⟨.record ρ' none, by simp [Subst.apply, h]⟩
  | .record ρ (some e) => by
    obtain ⟨ρ', h⟩ := ren_applyRow_some hR ρ
    cases hf : FMap.find? R.row e with
    | none => exact ⟨.record ρ' (some e), by simp [Subst.apply, h, hf]⟩
    | some p =>
      obtain ⟨ρr, tl⟩ := p
      have : ρr = [] := hR.2 _ (tfind?_mem hf)
      subst this
      exact ⟨.record ρ' tl, by simp [Subst.apply, h, hf, tmerge_nil]⟩
  | .fn a b => by
    obtain ⟨a', ha⟩ := ren_apply_some hR a
    obtain ⟨b', hb⟩ := ren_apply_some hR b
    exact ⟨.fn a' b', by simp [Subst.apply, ha, hb]⟩
  | .con as t => by
    obtain ⟨as', h⟩ := ren_applyList_some hR as
    exact ⟨.con as' t, by simp [Subst.apply, h]⟩
theorem ren_applyRow_some {R : Subst} (hR : RenS R) : ∀ ρ : Row, ∃ ρ', R.applyRow ρ = some ρ'
  | [] => ⟨_, rfl⟩
  | (l, x) :: r => by
    obtain ⟨x', hx⟩ := ren_apply_some hR x
    obtain ⟨r', hr⟩ := ren_applyRow_some hR r
    exact ⟨(l, x') :: r', by simp [Subst.applyRow, hx, hr]⟩
theorem ren_applyList_some {R : Subst} (hR : RenS R) : ∀ l : List Ty, ∃ l', R.applyList l = some l'
  | [] => ⟨_, rfl⟩
  | x :: r => by
    obtain ⟨x', hx⟩ := ren_apply_some hR x
    obtain ⟨r', hr⟩ := ren_applyList_some hR r
    exact ⟨x' :: r', by simp [Subst.applyList, hx, hr]⟩
end

/-- The canonical form is a renaming of the body. -/
theorem canon_ren (σ : Scheme) : ∃ Rc X', RenS Rc ∧ Rc.apply σ.body = some X' ∧
    Scheme.canon σ = ⟨(Scheme.canon σ).bound, X'⟩ := by
  have hR := renumber_ren 0 (canonVars σ.bound σ.body)
  unfold Scheme.canon
  revert hR
  generalize renumber true 0 (canonVars σ.bound σ.body) = r
  obtain ⟨Rc, bs⟩ := r
  intro hR
  obtain ⟨X', hX⟩ := ren_apply_some hR σ.body
  exact ⟨Rc, X', hR, hX, by simp [hX]⟩

/-! ## Instances of a canonical form of a known type -/

/-- σd is a canonical form of a renaming of τ0. -/
def InstOf (σd : Scheme) (τ0 : Ty) : Prop :=
  ∃ b R X, RenS R ∧ R.apply τ0 = some X ∧ σd = Scheme.canon ⟨b, X⟩

theorem instOf_canon (b : List BVar) (τ0 : Ty) : InstOf (Scheme.canon ⟨b, τ0⟩) τ0 :=
  ⟨b, Subst.id, τ0, renS_id, tapply_id τ0, rfl⟩

theorem instOf_gen {σd : Scheme} {τ0 : Ty} (h : InstOf σd τ0) {inst : List Ty} {τ : Ty}
    (hg : genAt σd inst τ = true) : ∃ S : Subst, S.Respects ∧ S.apply τ0 = some τ := by
  obtain ⟨b, R, X, hR, hX, rfl⟩ := h
  obtain ⟨Rc, X', hRc, hX', he⟩ := canon_ren ⟨b, X⟩
  rw [he] at hg
  unfold genAt at hg
  split at hg
  · rename_i S _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    have hS := (Subst.respectsB_iff S).mp hg.1
    have h1 := apply_comp hRc X X' τ hX' hg.2
    exact ⟨_, respects_comp hR (respects_comp hRc hS), apply_comp hR τ0 X τ hX h1⟩
  · cases hg

theorem instOf_close {σd : Scheme} {τ0 : Ty} (h : InstOf σd τ0) (b' : List BVar) :
    InstOf (Scheme.canon ⟨b', σd.body⟩) τ0 := by
  obtain ⟨b, R, X, hR, hX, rfl⟩ := h
  obtain ⟨Rc, X', hRc, hX', he⟩ := canon_ren ⟨b, X⟩
  rw [he]
  exact ⟨b', compS Rc R, X', renS_comp hRc hR, apply_comp hR τ0 X X' hX hX', rfl⟩

/-! ## More inversions of the normalisation -/

theorem hN_var_inv {τ : Ty} {x : TyVar} (h : hN τ = .var x) :
    τ = .var x ∨ ∃ s, x = .named s ∧ τ = .record [] (some (.named s)) := by
  cases τ with
  | var a => simp only [hN, Ty.var.injEq] at h; exact .inl (by rw [h])
  | fn _ _ => simp [hN] at h
  | con _ _ => simp [hN] at h
  | record ρ tl =>
    simp only [hN] at h
    rcases hRec_cases (hNRow ρ) tl with ⟨e, _⟩ | ⟨s, h1, h2, _, e⟩ <;> rw [e] at h
    · cases h
    · simp only [Ty.var.injEq] at h
      subst h h2
      exact .inr ⟨s, rfl, by rw [(hNRow_nil_iff ρ).mp h1]⟩

/-- The normalisation of a record that it does not turn into a variable. -/
theorem hN_record_of {ρ : Row} {tl : Option RowVar}
    (h : ¬ (ρ = [] ∧ ∃ s, tl = some (.named s) ∧ classOfName s = .any)) :
    hN (.record ρ tl) = .record (hNRow ρ) tl := by
  simp only [hN]
  rcases hRec_cases (hNRow ρ) tl with ⟨e, _⟩ | ⟨s, h1, h2, hc, _⟩
  · exact e
  · exact absurd ⟨(hNRow_nil_iff ρ).mp h1, s, h2, hc⟩ h

theorem hN_named_any {s : String} (hc : classOfName s = .any) :
    hN (.record [] (some (.named s))) = .var (.named s) := by
  simp [hN, hNRow, hRec, hc]

/-! ## hN-equal types have hN-equal instances, when no name has two sorts -/

/-- No name is both a type and a row variable. -/
def OneSort (V : List BVar) : Prop := ∀ s, BVar.ty (.named s) ∈ V → BVar.row (.named s) ∉ V

theorem hNRow_eq_rowMap (ρ : Row) : hNRow ρ = RTypes.rowMap hN ρ := by
  rw [hNRow_eq]; rfl

section congr
set_option linter.unusedSectionVars false
variable {S : Subst} {V : List BVar} (hV : OneSort V)
include hV

mutual
theorem hN_apply_congr : ∀ (τ1 τ2 a b : Ty), (∀ v ∈ τ1.vars, v ∈ V) → (∀ v ∈ τ2.vars, v ∈ V) →
    hN τ1 = hN τ2 → S.apply τ1 = some a → S.apply τ2 = some b → hN a = hN b
  | .var x, τ2, a, b, h1, h2, he, ha, hb => by
    rcases hN_var_inv he.symm with rfl | ⟨s, rfl, rfl⟩
    · rw [ha] at hb; cases hb; rfl
    · exact absurd (h2 _ (by simp [Ty.vars])) (hV s (h1 _ (by simp [Ty.vars])))
  | .record ρ1 tl1, τ2, a, b, h1, h2, he, ha, hb => by
    by_cases hm : ρ1 = [] ∧ ∃ s, tl1 = some (.named s) ∧ classOfName s = .any
    · obtain ⟨rfl, s, rfl, hc⟩ := hm
      rw [hN_named_any hc] at he
      rcases hN_var_inv he.symm with rfl | ⟨s', e, rfl⟩
      · exact absurd (h1 _ (by simp [Ty.vars, Ty.rowVars])) (hV s (h2 _ (by simp [Ty.vars])))
      · cases e; rw [ha] at hb; cases hb; rfl
    · rw [hN_record_of hm] at he
      obtain ⟨ρ2, rfl, hρ⟩ := hN_rec_inv' he.symm
      have hv1 : ∀ v ∈ Ty.rowVars ρ1, v ∈ V := fun v hv => h1 v (by cases tl1 <;> simp [Ty.vars, hv])
      have hv2 : ∀ v ∈ Ty.rowVars ρ2, v ∈ V := fun v hv => h2 v (by cases tl1 <;> simp [Ty.vars, hv])
      cases tl1 with
      | none =>
        simp only [Subst.apply] at ha hb
        cases hr1 : S.applyRow ρ1 with
        | none => rw [hr1] at ha; cases ha
        | some a1 =>
          cases hr2 : S.applyRow ρ2 with
          | none => rw [hr2] at hb; cases hb
          | some b1 =>
            have hab := hN_applyRow_congr ρ1 ρ2 a1 b1 hv1 hv2 hρ.symm hr1 hr2
            rw [hr1] at ha
            rw [hr2] at hb
            simp only [Option.some.injEq] at ha hb
            subst ha hb
            simp only [hN, hab]
      | some e =>
        simp only [Subst.apply] at ha hb
        cases hr1 : S.applyRow ρ1 with
        | none => rw [hr1] at ha; cases ha
        | some a1 =>
          cases hr2 : S.applyRow ρ2 with
          | none => rw [hr2] at hb; cases hb
          | some b1 =>
            have hab := hN_applyRow_congr ρ1 ρ2 a1 b1 hv1 hv2 hρ.symm hr1 hr2
            rw [hr1] at ha
            rw [hr2] at hb
            simp only at ha hb
            cases hSe : FMap.find? S.row e with
            | none =>
              rw [hSe] at ha hb
              simp only [Option.some.injEq] at ha hb
              subst ha hb
              simp only [hN, hab]
            | some q =>
              obtain ⟨ρs, tls⟩ := q
              rw [hSe] at ha hb
              simp only at ha hb
              cases hm1 : Row.merge a1 ρs with
              | none => rw [hm1] at ha; cases ha
              | some m1 =>
                cases hm2 : Row.merge b1 ρs with
                | none => rw [hm2] at hb; cases hb
                | some m2 =>
                  rw [hm1] at ha
                  rw [hm2] at hb
                  simp only [Option.some.injEq] at ha hb
                  subst ha hb
                  have e1 := RTypes.merge_map hN a1 ρs
                  have e2 := RTypes.merge_map hN b1 ρs
                  rw [hm1] at e1
                  rw [hm2] at e2
                  rw [← hNRow_eq_rowMap, ← hNRow_eq_rowMap] at e1 e2
                  rw [hab] at e1
                  rw [e1] at e2
                  simp only [Option.map_some, Option.some.injEq] at e2
                  simp only [hN, hNRow_eq_rowMap, e2]
  | .fn x y, τ2, a, b, h1, h2, he, ha, hb => by
    obtain ⟨x2, y2, rfl, hx, hy⟩ := hN_fn_inv he.symm
    simp only [Subst.apply] at ha hb
    cases hxa : S.apply x with
    | none => simp [hxa] at ha
    | some xa =>
      cases hya : S.apply y with
      | none => simp [hxa, hya] at ha
      | some ya =>
        cases hxb : S.apply x2 with
        | none => simp [hxb] at hb
        | some xb =>
          cases hyb : S.apply y2 with
          | none => simp [hxb, hyb] at hb
          | some yb =>
            rw [hxa, hya] at ha
            rw [hxb, hyb] at hb
            simp only [Option.some.injEq] at ha hb
            subst ha hb
            simp only [hN]
            rw [hN_apply_congr x x2 xa xb (fun v hv => h1 v (by simp [Ty.vars, hv]))
                (fun v hv => h2 v (by simp [Ty.vars, hv])) hx.symm hxa hxb,
              hN_apply_congr y y2 ya yb (fun v hv => h1 v (by simp [Ty.vars, hv]))
                (fun v hv => h2 v (by simp [Ty.vars, hv])) hy.symm hya hyb]
  | .con as t, τ2, a, b, h1, h2, he, ha, hb => by
    obtain ⟨xs, t2, rfl, hxs, ht⟩ := hN_con_inv he.symm
    simp only [Subst.apply] at ha hb
    cases has : S.applyList as with
    | none => simp [has] at ha
    | some as' =>
      cases hxs' : S.applyList xs with
      | none => simp [hxs'] at hb
      | some xs' =>
        rw [has] at ha
        rw [hxs'] at hb
        simp only [Option.some.injEq] at ha hb
        subst ha hb
        simp only [hN]
        rw [hN_applyList_congr as xs as' xs' (fun v hv => h1 v (by simpa [Ty.vars] using hv))
          (fun v hv => h2 v (by simpa [Ty.vars] using hv)) hxs.symm has hxs', ht]
theorem hN_applyRow_congr : ∀ (ρ1 ρ2 a b : Row), (∀ v ∈ Ty.rowVars ρ1, v ∈ V) → (∀ v ∈ Ty.rowVars ρ2, v ∈ V) →
    hNRow ρ1 = hNRow ρ2 → S.applyRow ρ1 = some a → S.applyRow ρ2 = some b → hNRow a = hNRow b
  | [], [], a, b, _, _, _, ha, hb => by
    simp only [Subst.applyRow, Option.some.injEq] at ha hb; subst ha hb; rfl
  | [], _ :: _, _, _, _, _, he, _, _ => by simp [hNRow] at he
  | _ :: _, [], _, _, _, _, he, _, _ => by simp [hNRow] at he
  | (l, x) :: r, (l', x') :: r', a, b, h1, h2, he, ha, hb => by
    simp only [hNRow, List.cons.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨rfl, hx⟩, hr⟩ := he
    simp only [Subst.applyRow] at ha hb
    cases hxa : S.apply x with
    | none => simp [hxa] at ha
    | some xa =>
      cases hra : S.applyRow r with
      | none => simp [hxa, hra] at ha
      | some ra =>
        cases hxb : S.apply x' with
        | none => simp [hxb] at hb
        | some xb =>
          cases hrb : S.applyRow r' with
          | none => simp [hxb, hrb] at hb
          | some rb =>
            rw [hxa, hra] at ha
            rw [hxb, hrb] at hb
            simp only [Option.some.injEq] at ha hb
            subst ha hb
            simp only [hNRow]
            rw [hN_apply_congr x x' xa xb (fun v hv => h1 v (by simp [Ty.rowVars, hv]))
                (fun v hv => h2 v (by simp [Ty.rowVars, hv])) hx hxa hxb,
              hN_applyRow_congr r r' ra rb (fun v hv => h1 v (by simp [Ty.rowVars, hv]))
                (fun v hv => h2 v (by simp [Ty.rowVars, hv])) hr hra hrb]
theorem hN_applyList_congr : ∀ (l1 l2 a b : List Ty), (∀ v ∈ Ty.listVars l1, v ∈ V) → (∀ v ∈ Ty.listVars l2, v ∈ V) →
    hNList l1 = hNList l2 → S.applyList l1 = some a → S.applyList l2 = some b → hNList a = hNList b
  | [], [], a, b, _, _, _, ha, hb => by
    simp only [Subst.applyList, Option.some.injEq] at ha hb; subst ha hb; rfl
  | [], _ :: _, _, _, _, _, he, _, _ => by simp [hNList] at he
  | _ :: _, [], _, _, _, _, he, _, _ => by simp [hNList] at he
  | x :: r, x' :: r', a, b, h1, h2, he, ha, hb => by
    simp only [hNList, List.cons.injEq] at he
    obtain ⟨hx, hr⟩ := he
    simp only [Subst.applyList] at ha hb
    cases hxa : S.apply x with
    | none => simp [hxa] at ha
    | some xa =>
      cases hra : S.applyList r with
      | none => simp [hxa, hra] at ha
      | some ra =>
        cases hxb : S.apply x' with
        | none => simp [hxb] at hb
        | some xb =>
          cases hrb : S.applyList r' with
          | none => simp [hxb, hrb] at hb
          | some rb =>
            rw [hxa, hra] at ha
            rw [hxb, hrb] at hb
            simp only [Option.some.injEq] at ha hb
            subst ha hb
            simp only [hNList]
            rw [hN_apply_congr x x' xa xb (fun v hv => h1 v (by simp [Ty.listVars, hv]))
                (fun v hv => h2 v (by simp [Ty.listVars, hv])) hx hxa hxb,
              hN_applyList_congr r r' ra rb (fun v hv => h1 v (by simp [Ty.listVars, hv]))
                (fun v hv => h2 v (by simp [Ty.listVars, hv])) hr hra hrb]
end

end congr

/-! ## Names, subterms and records -/

theorem hRec_names (ρ : Row) (tl : Option RowVar) :
    (hRec ρ tl).vars.filterMap BVar.name? = (Ty.record ρ tl).vars.filterMap BVar.name? := by
  cases tl with
  | none => rfl
  | some e =>
    cases e with
    | named s =>
      cases ρ with
      | nil => simp only [hRec]; split <;> simp [Ty.vars, Ty.rowVars, BVar.name?]
      | cons _ _ => simp [hRec, Ty.vars, Ty.rowVars, BVar.name?]
    | fresh _ => rfl
    | bnd _ => rfl

mutual
theorem names_hN : ∀ τ : Ty, (hN τ).vars.filterMap BVar.name? = τ.vars.filterMap BVar.name?
  | .var _ => rfl
  | .record ρ tl => by
    simp only [hN]
    rw [hRec_names]
    cases tl with
    | none => simp only [Ty.vars]; exact namesRow_hN ρ
    | some e => simp only [Ty.vars, List.filterMap_append, namesRow_hN ρ]
  | .fn a b => by simp only [hN, Ty.vars, List.filterMap_append, names_hN a, names_hN b]
  | .con as _ => by simp only [hN, Ty.vars]; exact namesList_hN as
theorem namesRow_hN : ∀ ρ : Row, (Ty.rowVars (hNRow ρ)).filterMap BVar.name? = (Ty.rowVars ρ).filterMap BVar.name?
  | [] => rfl
  | (_, x) :: r => by simp only [hNRow, Ty.rowVars, List.filterMap_append, names_hN x, namesRow_hN r]
theorem namesList_hN : ∀ l : List Ty, (Ty.listVars (hNList l)).filterMap BVar.name? = (Ty.listVars l).filterMap BVar.name?
  | [] => rfl
  | x :: r => by simp only [hNList, Ty.listVars, List.filterMap_append, names_hN x, namesList_hN r]
end

mutual
/-- The subterms of a type. -/
def subsT : Ty → List Ty
  | .var a => [.var a]
  | .record ρ tl => .record ρ tl :: subsRow ρ
  | .fn a b => .fn a b :: (subsT a ++ subsT b)
  | .con as t => .con as t :: subsList as
def subsRow : Row → List Ty
  | [] => []
  | (_, x) :: r => subsT x ++ subsRow r
def subsList : List Ty → List Ty
  | [] => []
  | x :: r => subsT x ++ subsList r
end

theorem self_mem_subsT (τ : Ty) : τ ∈ subsT τ := by
  cases τ <;> simp [subsT]

mutual
theorem subsT_vars : ∀ (τ x : Ty), x ∈ subsT τ → ∀ v ∈ x.vars, v ∈ τ.vars
  | .var a, x, hx, v, hv => by simp only [subsT, List.mem_singleton] at hx; subst hx; exact hv
  | .record ρ tl, x, hx, v, hv => by
    simp only [subsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hv
    · have := subsRow_vars ρ x hx v hv
      cases tl <;> simp [Ty.vars, this]
  | .fn a b, x, hx, v, hv => by
    simp only [subsT, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact hv
    · simp [Ty.vars, subsT_vars a x hx v hv]
    · simp [Ty.vars, subsT_vars b x hx v hv]
  | .con as t, x, hx, v, hv => by
    simp only [subsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hv
    · simp only [Ty.vars]; exact subsList_vars as x hx v hv
theorem subsRow_vars : ∀ (ρ : Row) (x : Ty), x ∈ subsRow ρ → ∀ v ∈ x.vars, v ∈ Ty.rowVars ρ
  | [], x, hx, _, _ => by simp [subsRow] at hx
  | (_, y) :: r, x, hx, v, hv => by
    simp only [subsRow, List.mem_append] at hx
    rcases hx with hx | hx
    · simp [Ty.rowVars, subsT_vars y x hx v hv]
    · simp [Ty.rowVars, subsRow_vars r x hx v hv]
theorem subsList_vars : ∀ (l : List Ty) (x : Ty), x ∈ subsList l → ∀ v ∈ x.vars, v ∈ Ty.listVars l
  | [], x, hx, _, _ => by simp [subsList] at hx
  | y :: r, x, hx, v, hv => by
    simp only [subsList, List.mem_append] at hx
    rcases hx with hx | hx
    · simp [Ty.listVars, subsT_vars y x hx v hv]
    · simp [Ty.listVars, subsList_vars r x hx v hv]
end

mutual
theorem subsT_apply (S : Subst) : ∀ (τ τ' x : Ty), S.apply τ = some τ' → x ∈ subsT τ → ∃ x', S.apply x = some x'
  | .var a, τ', x, h, hx => by simp only [subsT, List.mem_singleton] at hx; subst hx; exact ⟨_, h⟩
  | .record ρ tl, τ', x, h, hx => by
    simp only [subsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, h⟩
    · have hr : ∃ ρ', S.applyRow ρ = some ρ' := by
        cases tl with
        | none =>
          simp only [Subst.apply] at h
          cases hρ : S.applyRow ρ with
          | none => rw [hρ] at h; cases h
          | some ρ' => exact ⟨ρ', rfl⟩
        | some e =>
          simp only [Subst.apply] at h
          cases hρ : S.applyRow ρ with
          | none => rw [hρ] at h; cases h
          | some ρ' => exact ⟨ρ', rfl⟩
      obtain ⟨ρ', hρ⟩ := hr
      exact subsRow_apply S ρ ρ' x hρ hx
  | .fn a b, τ', x, h, hx => by
    simp only [Subst.apply] at h
    cases ha : S.apply a with
    | none => rw [ha] at h; cases h
    | some a' =>
      cases hb : S.apply b with
      | none => rw [ha, hb] at h; cases h
      | some b' =>
        simp only [subsT, List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨.fn a' b', by simp [Subst.apply, ha, hb]⟩
        · exact subsT_apply S a a' x ha hx
        · exact subsT_apply S b b' x hb hx
  | .con as t, τ', x, h, hx => by
    simp only [Subst.apply] at h
    cases has : S.applyList as with
    | none => rw [has] at h; cases h
    | some as' =>
      simp only [subsT, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨.con as' t, by simp [Subst.apply, has]⟩
      · exact subsList_apply S as as' x has hx
theorem subsRow_apply (S : Subst) : ∀ (ρ ρ' : Row) (x : Ty), S.applyRow ρ = some ρ' → x ∈ subsRow ρ →
    ∃ x', S.apply x = some x'
  | [], _, x, _, hx => by simp [subsRow] at hx
  | (_, y) :: r, ρ', x, h, hx => by
    simp only [Subst.applyRow] at h
    cases hy : S.apply y with
    | none => rw [hy] at h; cases h
    | some y' =>
      cases hr : S.applyRow r with
      | none => rw [hy, hr] at h; cases h
      | some r' =>
        simp only [subsRow, List.mem_append] at hx
        rcases hx with hx | hx
        · exact subsT_apply S y y' x hy hx
        · exact subsRow_apply S r r' x hr hx
theorem subsList_apply (S : Subst) : ∀ (l l' : List Ty) (x : Ty), S.applyList l = some l' → x ∈ subsList l →
    ∃ x', S.apply x = some x'
  | [], _, x, _, hx => by simp [subsList] at hx
  | y :: r, l', x, h, hx => by
    simp only [Subst.applyList] at h
    cases hy : S.apply y with
    | none => rw [hy] at h; cases h
    | some y' =>
      cases hr : S.applyList r with
      | none => rw [hy, hr] at h; cases h
      | some r' =>
        simp only [subsList, List.mem_append] at hx
        rcases hx with hx | hx
        · exact subsT_apply S y y' x hy hx
        · exact subsList_apply S r r' x hr hx
end

theorem idxL_some {α : Type} [DecidableEq α] {x : α} (d : α) : ∀ {l : List α}, x ∈ l →
    ∃ i, idxL x l = some i ∧ l.getD i d = x
  | [], h => by cases h
  | y :: ys, h => by
    simp only [idxL]
    by_cases e : y = x
    · subst e; exact ⟨0, by simp, rfl⟩
    · simp only [e, ite_false]
      have hm : x ∈ ys := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      obtain ⟨i, hi, hg⟩ := idxL_some d hm
      exact ⟨i + 1, by simp [hi], by simpa using hg⟩

/-- The variable of a name in a type: of the sort the type gives it. -/
def vOf (τg : Ty) (s : String) : Ty :=
  if BVar.ty (.named s) ∈ τg.vars then .var (.named s) else .record [] (some (.named s))

/-- A subterm of τg with a given normal form. -/
def firstRec (τg target : Ty) : Ty := ((subsT τg).find? (fun x => hN x == target)).getD default

/-- The valuation of a template's metavariables for an instance `S τg`. -/
def tmplVal (S : Subst) (τg : Ty) : Val := fun q =>
  match q with
  | [0, i] => hN ((S.apply (vOf τg ((tyNames (hN τg)).getD i ""))).getD default)
  | [1, j] => hN ((S.apply (firstRec τg ((dedupL (recsT (hN τg))).getD j default))).getD default)
  | _ => default

theorem good_var {τ : Ty} (h : goodTmpl τ = true) {v : BVar} (hv : v ∈ τ.vars) :
    (∃ s, v = .ty (.named s) ∧ BVar.row (.named s) ∉ τ.vars) ∨
      (∃ s, v = .row (.named s) ∧ classOfName s = .any) := by
  simp only [goodTmpl, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.1 v hv
  match v, this with
  | .ty (.named s), h' => exact .inl ⟨s, rfl, by simpa using h'⟩
  | .row (.named s), h' => exact .inr ⟨s, rfl, by simpa using h'⟩

theorem good_oneSort {τ : Ty} (h : goodTmpl τ = true) : OneSort τ.vars := by
  intro s hs
  rcases good_var h hs with ⟨s', e, h'⟩ | ⟨s', e, _⟩
  · cases e; exact h'
  · cases e

theorem mem_names {τ : Ty} {s : String} {v : BVar} (hv : v ∈ τ.vars) (hn : v.name? = some s) :
    s ∈ tyNames (hN τ) := by
  unfold tyNames
  rw [mem_dedupL, names_hN]
  exact List.mem_filterMap.mpr ⟨v, hv, hn⟩

theorem names_mem {τ : Ty} {s : String} (h : s ∈ tyNames (hN τ)) :
    BVar.ty (.named s) ∈ τ.vars ∨ BVar.row (.named s) ∈ τ.vars := by
  unfold tyNames at h
  rw [mem_dedupL, names_hN] at h
  obtain ⟨v, hv, hn⟩ := List.mem_filterMap.mp h
  match v, hn with
  | .ty (.named s'), hn => simp only [BVar.name?, Option.some.injEq] at hn; subst hn; exact .inl hv
  | .row (.named s'), hn => simp only [BVar.name?, Option.some.injEq] at hn; subst hn; exact .inr hv

/-! ## The template of a type describes its instances -/

section tmpl
set_option linter.unusedSectionVars false
variable {S : Subst} {τg τg' : Ty} (hgood : goodTmpl τg = true) (hSg : S.apply τg = some τg')
include hgood hSg

mutual
theorem tmpl_ok : ∀ (τ0 τ0' : Ty), (∀ x ∈ subsT τ0, x ∈ subsT τg) → (∀ x ∈ recsT (hN τ0), x ∈ recsT (hN τg)) →
    S.apply τ0 = some τ0' →
    (tmplT (tyNames (hN τg)) (dedupL (recsT (hN τg))) (hN τ0)).ev (tmplVal S τg) = hN τ0'
  | .var a, τ0', hs, _, ha => by
    have hv : BVar.ty a ∈ τg.vars := subsT_vars τg _ (hs _ (self_mem_subsT _)) _ (by simp [Ty.vars])
    rcases good_var hgood hv with ⟨s, e, _⟩ | ⟨s, e, _⟩
    · cases e
      obtain ⟨i, hi, hg⟩ := idxL_some "" (mem_names hv (s := s) rfl)
      have hvo : vOf τg s = .var (.named s) := by simp [vOf, hv]
      simp only [hN, tmplT, hi, T.ev, tmplVal, hg, hvo, ha, Option.getD_some]
    · cases e
  | .record ρ none, τ0', hs, hr, ha => by
    simp only [Subst.apply] at ha
    cases hρ : S.applyRow ρ with
    | none => rw [hρ] at ha; cases ha
    | some ρ' =>
      rw [hρ] at ha
      simp only [Option.some.injEq] at ha
      subst ha
      have ih := tmplRow_ok ρ ρ' (fun x hx => hs x (by simp [subsT, hx]))
        (fun x hx => hr x (by simpa [hN, hRec, recsT] using hx)) hρ
      simp only [hN, hRec, tmplT, T.ev, ih]
  | .record ρ (some e), τ0', hs, hr, ha => by
    have hm : Ty.record ρ (some e) ∈ subsT τg := hs _ (self_mem_subsT _)
    have hv : BVar.row e ∈ τg.vars := subsT_vars τg _ hm _ (by simp [Ty.vars])
    rcases good_var hgood hv with ⟨s, e', _⟩ | ⟨s, e', hcls⟩
    · cases e'
    · cases e'
      have hnt : BVar.ty (.named s) ∉ τg.vars := fun h => good_oneSort hgood s h hv
      cases ρ with
      | nil =>
        obtain ⟨i, hi, hg⟩ := idxL_some "" (mem_names hv (s := s) rfl)
        have hvo : vOf τg s = .record [] (some (.named s)) := by simp [vOf, hnt]
        rw [hN_named_any hcls]
        simp only [tmplT, hi, T.ev, tmplVal, hg, hvo, ha, Option.getD_some]
      | cons f rest =>
        have hne : ¬ ((f :: rest) = [] ∧ ∃ s', some (RowVar.named s) = some (.named s') ∧ classOfName s' = .any) :=
          fun h => by cases h.1
        have hN0 := hN_record_of hne
        have hmem : hN (.record (f :: rest) (some (.named s))) ∈ recsT (hN τg) :=
          hr _ (by rw [hN0]; simp [recsT])
        obtain ⟨j, hj, hg⟩ := idxL_some default (mem_dedupL.mpr hmem)
        rw [hN0] at hj hg ⊢
        simp only [tmplT, hj, T.ev, tmplVal, hg]
        cases hf : (subsT τg).find? (fun x => hN x == Ty.record (hNRow (f :: rest)) (some (.named s))) with
        | none =>
          exfalso
          have := List.find?_eq_none.mp hf _ hm
          simp [hN0] at this
        | some x =>
          have hxm := List.mem_of_find?_eq_some hf
          have hxe : hN x = hN (.record (f :: rest) (some (.named s))) := by
            have := List.find?_some hf
            rw [hN0]; simpa using this
          obtain ⟨x', hx'⟩ := subsT_apply S τg τg' x hSg hxm
          simp only [firstRec, hf, Option.getD_some, hx']
          exact hN_apply_congr (good_oneSort hgood) x _ x' τ0' (subsT_vars τg x hxm)
            (subsT_vars τg _ hm) hxe hx' ha
  | .fn a b, τ0', hs, hr, ha => by
    simp only [Subst.apply] at ha
    cases ha' : S.apply a with
    | none => rw [ha'] at ha; cases ha
    | some a' =>
      cases hb' : S.apply b with
      | none => rw [ha', hb'] at ha; cases ha
      | some b' =>
        rw [ha', hb'] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        have iha := tmpl_ok a a' (fun x hx => hs x (by simp [subsT, hx]))
          (fun x hx => hr x (by simp [hN, recsT, hx])) ha'
        have ihb := tmpl_ok b b' (fun x hx => hs x (by simp [subsT, hx]))
          (fun x hx => hr x (by simp [hN, recsT, hx])) hb'
        simp only [hN, tmplT, T.ev] at iha ihb ⊢
        rw [iha, ihb]
  | .con as t, τ0', hs, hr, ha => by
    simp only [Subst.apply] at ha
    cases has : S.applyList as with
    | none => rw [has] at ha; cases ha
    | some as' =>
      rw [has] at ha
      simp only [Option.some.injEq] at ha
      subst ha
      have ih := tmplList_ok as as' (fun x hx => hs x (by simp [subsT, hx]))
        (fun x hx => hr x (by simpa [hN, recsT] using hx)) has
      simp only [hN, tmplT, T.ev, ih]
theorem tmplRow_ok : ∀ (ρ ρ' : Row), (∀ x ∈ subsRow ρ, x ∈ subsT τg) → (∀ x ∈ recsRow (hNRow ρ), x ∈ recsT (hN τg)) →
    S.applyRow ρ = some ρ' →
    T.evRow (tmplVal S τg) (tmplRow (tyNames (hN τg)) (dedupL (recsT (hN τg))) (hNRow ρ)) = hNRow ρ'
  | [], ρ', _, _, h => by simp only [Subst.applyRow, Option.some.injEq] at h; subst h; rfl
  | (l, x) :: r, ρ', hs, hr, h => by
    simp only [Subst.applyRow] at h
    cases hx : S.apply x with
    | none => rw [hx] at h; cases h
    | some x' =>
      cases hrr : S.applyRow r with
      | none => rw [hx, hrr] at h; cases h
      | some r' =>
        rw [hx, hrr] at h
        simp only [Option.some.injEq] at h
        subst h
        have ihx := tmpl_ok x x' (fun y hy => hs y (by simp [subsRow, hy]))
          (fun y hy => hr y (by simp [hNRow, recsRow, hy])) hx
        have ihr := tmplRow_ok r r' (fun y hy => hs y (by simp [subsRow, hy]))
          (fun y hy => hr y (by simp [hNRow, recsRow, hy])) hrr
        simp only [hNRow, tmplRow, T.evRow, ihx, ihr]
theorem tmplList_ok : ∀ (l l' : List Ty), (∀ x ∈ subsList l, x ∈ subsT τg) → (∀ x ∈ recsList (hNList l), x ∈ recsT (hN τg)) →
    S.applyList l = some l' →
    T.evList (tmplVal S τg) (tmplList (tyNames (hN τg)) (dedupL (recsT (hN τg))) (hNList l)) = hNList l'
  | [], l', _, _, h => by simp only [Subst.applyList, Option.some.injEq] at h; subst h; rfl
  | x :: r, l', hs, hr, h => by
    simp only [Subst.applyList] at h
    cases hx : S.apply x with
    | none => rw [hx] at h; cases h
    | some x' =>
      cases hrr : S.applyList r with
      | none => rw [hx, hrr] at h; cases h
      | some r' =>
        rw [hx, hrr] at h
        simp only [Option.some.injEq] at h
        subst h
        have ihx := tmpl_ok x x' (fun y hy => hs y (by simp [subsList, hy]))
          (fun y hy => hr y (by simp [hNList, recsList, hy])) hx
        have ihr := tmplList_ok r r' (fun y hy => hs y (by simp [subsList, hy]))
          (fun y hy => hr y (by simp [hNList, recsList, hy])) hrr
        simp only [hNList, tmplList, T.evList, ihx, ihr]
end

end tmpl

theorem mem_tmplCls {c : Con} : ∀ (i : Nat) (l : List String), c ∈ tmplCls i l →
    ∃ j, j < l.length ∧ c = .cls (.mv [0, i + j]) (classOfName (l.getD j "")) ∧ classOfName (l.getD j "") ≠ .any
  | _, [], h => by simp [tmplCls] at h
  | i, s :: ns, h => by
    simp only [tmplCls] at h
    split at h
    · obtain ⟨j, hj, rfl, hc⟩ := mem_tmplCls (i + 1) ns h
      exact ⟨j + 1, by simp [hj], by simp [Nat.add_assoc, Nat.add_comm 1 j], by simpa using hc⟩
    · rename_i hc
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, by simp, by simpa using hc⟩
      · obtain ⟨j, hj, rfl, hc⟩ := mem_tmplCls (i + 1) ns h
        exact ⟨j + 1, by simp [hj], by simp [Nat.add_assoc, Nat.add_comm 1 j], by simpa using hc⟩

/-- Every respecting instance of τg is described by its template. -/
def TmplOK (t : T) (K : List Con) (τ0 : Ty) : Prop :=
  ∀ (S : Subst) (τ : Ty), S.Respects → S.apply τ0 = some τ → ∃ μ, t.ev μ = hN τ ∧ Holds μ K

/-! ## Fields of records with an extension -/

theorem sortedB_cons {l : Lab} {τ : Ty} {r : Row} (h : sortedB ((l, τ) :: r) = true) :
    (∀ p ∈ r, labLt l p.1 = true) ∧ sortedB r = true := by
  simp only [sortedB, Bool.and_eq_true, List.all_eq_true] at h
  exact h

/-- A merge keeps the fields of a sorted row. -/
theorem mergeF_find {l : Lab} {v : Ty} : ∀ (n : Nat) (a b c : Row), Row.mergeF n a b = some c →
    sortedB a = true → FMap.find? a l = some v → FMap.find? c l = some v
  | _, [], _, _, _, _, hf => by simp [FMap.find?] at hf
  | n, (l1, τ1) :: r1, [], c, h, _, hf => by
    cases n <;> (simp only [Row.mergeF, Option.some.injEq] at h; subst h; exact hf)
  | 0, (l1, τ1) :: r1, (l2, τ2) :: r2, c, h, _, _ => by simp [Row.mergeF] at h
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2, c, h, hs, hf => by
    obtain ⟨hlt, hs1⟩ := sortedB_cons hs
    simp only [Row.mergeF] at h
    split at h
    · cases h
    · rename_i hne
      split at h
      · rename_i hl
        cases hm : Row.mergeF n r1 ((l2, τ2) :: r2) with
        | none => rw [hm] at h; cases h
        | some r =>
          rw [hm] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [FMap.find?] at hf ⊢
          split
          · rename_i e; rw [if_pos e] at hf; exact hf
          · rename_i e; rw [if_neg e] at hf; exact mergeF_find n r1 _ r hm hs1 hf
      · rename_i hl
        cases hm : Row.mergeF n ((l1, τ1) :: r1) r2 with
        | none => rw [hm] at h; cases h
        | some r =>
          rw [hm] at h
          simp only [Option.some.injEq] at h
          subst h
          have hl2 : l2 ≠ l := by
            intro e
            subst e
            simp only [FMap.find?] at hf
            split at hf
            · rename_i e'; exact hne e'
            · have hm1 : (l2, v) ∈ r1 := tfind?_mem hf
              exact hl (hlt _ hm1)
          simp only [FMap.find?, if_neg hl2]
          exact mergeF_find n _ r2 r hm hs hf

theorem merge_find {l : Lab} {v : Ty} {a b c : Row} (h : Row.merge a b = some c) (hs : sortedB a = true)
    (hf : FMap.find? a l = some v) : FMap.find? c l = some v := mergeF_find _ a b c h hs hf

theorem applyRow_find {S : Subst} {l : Lab} : ∀ {ρ ρ' : Row} {y : Ty}, S.applyRow ρ = some ρ' →
    FMap.find? ρ l = some y → ∃ y', FMap.find? ρ' l = some y' ∧ S.apply y = some y'
  | [], _, _, _, hf => by simp [FMap.find?] at hf
  | (l', x) :: r, ρ', y, h, hf => by
    simp only [Subst.applyRow] at h
    cases hx : S.apply x with
    | none => rw [hx] at h; cases h
    | some x' =>
      cases hr : S.applyRow r with
      | none => rw [hx, hr] at h; cases h
      | some r' =>
        rw [hx, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [FMap.find?] at hf ⊢
        split
        · rename_i e; rw [if_pos e] at hf; cases hf; exact ⟨x', rfl, hx⟩
        · rename_i e; rw [if_neg e] at hf; exact applyRow_find hr hf

theorem applyRow_labels {S : Subst} : ∀ {ρ ρ' : Row}, S.applyRow ρ = some ρ' → ρ'.map (·.1) = ρ.map (·.1)
  | [], _, h => by simp only [Subst.applyRow, Option.some.injEq] at h; subst h; rfl
  | (l, x) :: r, ρ', h => by
    simp only [Subst.applyRow] at h
    cases hx : S.apply x with
    | none => rw [hx] at h; cases h
    | some x' =>
      cases hr : S.applyRow r with
      | none => rw [hx, hr] at h; cases h
      | some r' =>
        rw [hx, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [applyRow_labels hr]

theorem sortedB_labels : ∀ {ρ ρ' : Row}, ρ.map (·.1) = ρ'.map (·.1) → sortedB ρ = sortedB ρ'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (l, x) :: r, (l', x') :: r', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have e : (r.all fun p => labLt l p.1) = (r'.all fun p => labLt l p.1) := by
      have : r.all (fun p => labLt l p.1) = (r.map (·.1)).all (labLt l) := by simp [List.all_map, Function.comp_def]
      rw [this, h]; simp [List.all_map, Function.comp_def]
    simp only [sortedB, e, sortedB_labels h]

mutual
theorem recSorted_sub : ∀ (τ x : Ty), recSorted τ = true → x ∈ subsT τ →
    ∀ ρ e, x = .record ρ (some e) → sortedB ρ = true
  | .var _, x, _, hx, ρ, e, he => by simp only [subsT, List.mem_singleton] at hx; subst hx; cases he
  | .record ρ0 tl, x, h, hx, ρ, e, he => by
    simp only [recSorted, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at h
    simp only [subsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [Ty.record.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases h.1 with h | h
      · cases h
      · exact h
    · exact recSortedRow_sub ρ0 x h.2 hx ρ e he
  | .fn a b, x, h, hx, ρ, e, he => by
    simp only [recSorted, Bool.and_eq_true] at h
    simp only [subsT, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · cases he
    · exact recSorted_sub a x h.1 hx ρ e he
    · exact recSorted_sub b x h.2 hx ρ e he
  | .con as _, x, h, hx, ρ, e, he => by
    simp only [recSorted] at h
    simp only [subsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · cases he
    · exact recSortedList_sub as x h hx ρ e he
theorem recSortedRow_sub : ∀ (r : Row) (x : Ty), recSortedRow r = true → x ∈ subsRow r →
    ∀ ρ e, x = .record ρ (some e) → sortedB ρ = true
  | [], x, _, hx, _, _, _ => by simp [subsRow] at hx
  | (_, y) :: r, x, h, hx, ρ, e, he => by
    simp only [recSortedRow, Bool.and_eq_true] at h
    simp only [subsRow, List.mem_append] at hx
    rcases hx with hx | hx
    · exact recSorted_sub y x h.1 hx ρ e he
    · exact recSortedRow_sub r x h.2 hx ρ e he
theorem recSortedList_sub : ∀ (l : List Ty) (x : Ty), recSortedList l = true → x ∈ subsList l →
    ∀ ρ e, x = .record ρ (some e) → sortedB ρ = true
  | [], x, _, hx, _, _, _ => by simp [subsList] at hx
  | y :: r, x, h, hx, ρ, e, he => by
    simp only [recSortedList, Bool.and_eq_true] at h
    simp only [subsList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact recSorted_sub y x h.1 hx ρ e he
    · exact recSortedList_sub r x h.2 hx ρ e he
end

mutual
theorem subsT_trans : ∀ (τ x : Ty), x ∈ subsT τ → ∀ y ∈ subsT x, y ∈ subsT τ
  | .var a, x, hx, y, hy => by simp only [subsT, List.mem_singleton] at hx; subst hx; exact hy
  | .record ρ tl, x, hx, y, hy => by
    simp only [subsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hy
    · exact List.mem_cons_of_mem _ (subsRow_trans ρ x hx y hy)
  | .fn a b, x, hx, y, hy => by
    simp only [subsT, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact hy
    · simp [subsT, subsT_trans a x hx y hy]
    · simp [subsT, subsT_trans b x hx y hy]
  | .con as t, x, hx, y, hy => by
    simp only [subsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hy
    · exact List.mem_cons_of_mem _ (subsList_trans as x hx y hy)
theorem subsRow_trans : ∀ (ρ : Row) (x : Ty), x ∈ subsRow ρ → ∀ y ∈ subsT x, y ∈ subsRow ρ
  | [], x, hx, _, _ => by simp [subsRow] at hx
  | (_, z) :: r, x, hx, y, hy => by
    simp only [subsRow, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact .inl (subsT_trans z x hx y hy)
    · exact .inr (subsRow_trans r x hx y hy)
theorem subsList_trans : ∀ (l : List Ty) (x : Ty), x ∈ subsList l → ∀ y ∈ subsT x, y ∈ subsList l
  | [], x, hx, _, _ => by simp [subsList] at hx
  | z :: r, x, hx, y, hy => by
    simp only [subsList, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact .inl (subsT_trans z x hx y hy)
    · exact .inr (subsList_trans r x hx y hy)
end

theorem mem_subsRow {l : Lab} {y : Ty} : ∀ {ρ : Row}, (l, y) ∈ ρ → y ∈ subsRow ρ
  | [], h => by cases h
  | (l', z) :: r, h => by
    simp only [subsRow, List.mem_append]
    rcases List.mem_cons.mp h with e | h
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact .inl (self_mem_subsT _)
    · exact .inr (mem_subsRow h)

mutual
theorem recs_sub : ∀ (τ x : Ty), x ∈ recsT (hN τ) → ∃ y ∈ subsT τ, hN y = x
  | .var _, x, hx => by simp [hN, recsT] at hx
  | .record ρ tl, x, hx => by
    by_cases hm : ρ = [] ∧ ∃ s, tl = some (.named s) ∧ classOfName s = .any
    · obtain ⟨rfl, s, rfl, hc⟩ := hm
      rw [hN_named_any hc] at hx; simp [recsT] at hx
    · rw [hN_record_of hm] at hx
      cases tl with
      | none =>
        simp only [recsT] at hx
        obtain ⟨y, hy, he⟩ := recsRow_sub ρ x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, he⟩
      | some e =>
        simp only [recsT, List.mem_singleton] at hx
        subst hx
        exact ⟨_, self_mem_subsT _, hN_record_of hm⟩
  | .fn a b, x, hx => by
    simp only [hN, recsT, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, he⟩ := recs_sub a x hx
      exact ⟨y, by simp [subsT, hy], he⟩
    · obtain ⟨y, hy, he⟩ := recs_sub b x hx
      exact ⟨y, by simp [subsT, hy], he⟩
  | .con as t, x, hx => by
    simp only [hN, recsT] at hx
    obtain ⟨y, hy, he⟩ := recsList_sub as x hx
    exact ⟨y, List.mem_cons_of_mem _ hy, he⟩
theorem recsRow_sub : ∀ (ρ : Row) (x : Ty), x ∈ recsRow (hNRow ρ) → ∃ y ∈ subsRow ρ, hN y = x
  | [], x, hx => by simp [hNRow, recsRow] at hx
  | (_, z) :: r, x, hx => by
    simp only [hNRow, recsRow, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, he⟩ := recs_sub z x hx
      exact ⟨y, by simp [subsRow, hy], he⟩
    · obtain ⟨y, hy, he⟩ := recsRow_sub r x hx
      exact ⟨y, by simp [subsRow, hy], he⟩
theorem recsList_sub : ∀ (l : List Ty) (x : Ty), x ∈ recsList (hNList l) → ∃ y ∈ subsList l, hN y = x
  | [], x, hx => by simp [hNList, recsList] at hx
  | z :: r, x, hx => by
    simp only [hNList, recsList, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, he⟩ := recs_sub z x hx
      exact ⟨y, by simp [subsList, hy], he⟩
    · obtain ⟨y, hy, he⟩ := recsList_sub r x hx
      exact ⟨y, by simp [subsList, hy], he⟩
end

theorem mem_tmplHasRec {ns : List String} {rs : List Ty} {j : Nat} {c : Con} : ∀ {r : Ty}, c ∈ tmplHasRec ns rs j r →
    ∃ ρ e l x, r = .record ρ (some e) ∧ FMap.find? ρ l = some x ∧ recsT x = [] ∧
      c = .has (.mv [1, j]) l (tmplT ns rs x)
  | .record ρ (some e), h => by
    simp only [tmplHasRec, List.mem_filterMap] at h
    obtain ⟨l, _, hc⟩ := h
    split at hc
    · rename_i x hx
      split at hc
      · rename_i he
        cases hc
        exact ⟨ρ, e, l, x, rfl, hx, List.isEmpty_iff.mp he, rfl⟩
      · cases hc
    · cases hc
  | .record _ none, h => by simp [tmplHasRec] at h
  | .var _, h => by simp [tmplHasRec] at h
  | .fn _ _, h => by simp [tmplHasRec] at h
  | .con _ _, h => by simp [tmplHasRec] at h

theorem mem_tmplHasL {ns : List String} {rs : List Ty} {c : Con} : ∀ (i : Nat) (l : List Ty), c ∈ tmplHasL ns rs i l →
    ∃ j, j < l.length ∧ c ∈ tmplHasRec ns rs (i + j) (l.getD j default)
  | _, [], h => by simp [tmplHasL] at h
  | i, r :: rest, h => by
    simp only [tmplHasL, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, by simp, by simpa using h⟩
    · obtain ⟨j, hj, h⟩ := mem_tmplHasL (i + 1) rest h
      exact ⟨j + 1, by simp [hj], by simpa [Nat.add_assoc, Nat.add_comm 1 j] using h⟩

theorem tmplHas_ok {S : Subst} {τg τg' : Ty} (hgood : goodTmpl τg = true) (hSg : S.apply τg = some τg') :
    Holds (tmplVal S τg) (tmplHasL (tyNames (hN τg)) (dedupL (recsT (hN τg))) 0 (dedupL (recsT (hN τg)))) := by
  intro c hc
  obtain ⟨j, hj, hc⟩ := mem_tmplHasL 0 _ hc
  rw [Nat.zero_add] at hc
  obtain ⟨ρh, e, l, x, hr, hx, hrx, rfl⟩ := mem_tmplHasRec hc
  have hmem : (dedupL (recsT (hN τg))).getD j default ∈ recsT (hN τg) := by
    have e1 : (dedupL (recsT (hN τg))).getD j default = (dedupL (recsT (hN τg)))[j] := by
      simp [List.getD, List.getElem?_eq_getElem hj]
    rw [e1]; exact mem_dedupL.mp (List.getElem_mem hj)
  rw [hr] at hmem
  obtain ⟨y, hy, hye⟩ := recs_sub τg _ hmem
  simp only [Con.holds, T.ev, tmplVal, hr]
  cases hf : (subsT τg).find? (fun x => hN x == Ty.record ρh (some e)) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf _ hy
    simp [hye] at this
  | some x0 =>
    have hx0m := List.mem_of_find?_eq_some hf
    have hx0e : hN x0 = .record ρh (some e) := by have := List.find?_some hf; simpa using this
    obtain ⟨ρ0, rfl, hρ0⟩ := hN_rec_inv' hx0e
    obtain ⟨x0', hx0'⟩ := subsT_apply S τg τg' _ hSg hx0m
    simp only [firstRec, hf, Option.getD_some, hx0']
    have hs0 : sortedB ρ0 = true := recSorted_sub τg _ (by simp only [goodTmpl, Bool.and_eq_true] at hgood; exact hgood.2)
      hx0m ρ0 e rfl
    rw [← hρ0, hNRow_eq, find?_map_val] at hx
    cases hy0 : FMap.find? ρ0 l with
    | none => rw [hy0] at hx; cases hx
    | some y0 =>
      rw [hy0] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      subst hx
      have hy0m : y0 ∈ subsT τg := subsT_trans τg _ hx0m y0
        (List.mem_cons_of_mem _ (mem_subsRow (tfind?_mem hy0)))
      simp only [Subst.apply] at hx0'
      cases hρ1 : S.applyRow ρ0 with
      | none => rw [hρ1] at hx0'; cases hx0'
      | some ρ1 =>
        rw [hρ1] at hx0'
        simp only at hx0'
        obtain ⟨y1, hy1, hy01⟩ := applyRow_find hρ1 hy0
        have hev := tmpl_ok hgood hSg y0 y1 (fun z hz => subsT_trans τg y0 hy0m z hz)
          (fun z hz => by simp [hrx] at hz) hy01
        have hne : ∀ ρ3 : Row, FMap.find? ρ3 l = some y1 → ∀ tl,
            ¬ (ρ3 = [] ∧ ∃ s, tl = some (RowVar.named s) ∧ classOfName s = .any) :=
          fun ρ3 h3 tl hm => by rw [hm.1] at h3; simp [FMap.find?] at h3
        cases hSe : FMap.find? S.row e with
        | none =>
          rw [hSe] at hx0'
          simp only [Option.some.injEq] at hx0'
          subst hx0'
          refine ⟨hNRow ρ1, some e, hN_record_of (hne ρ1 hy1 _), ?_⟩
          simp only [Row.lookup, hNRow_eq, find?_map_val, hy1, Option.map_some, hev]
        | some q =>
          obtain ⟨ρs, tls⟩ := q
          rw [hSe] at hx0'
          simp only at hx0'
          cases hm : Row.merge ρ1 ρs with
          | none => rw [hm] at hx0'; cases hx0'
          | some ρ3 =>
            rw [hm] at hx0'
            simp only [Option.some.injEq] at hx0'
            subst hx0'
            have hs1 : sortedB ρ1 = true := by rw [sortedB_labels (applyRow_labels hρ1)]; exact hs0
            have hy3 := merge_find hm hs1 hy1
            refine ⟨hNRow ρ3, tls, hN_record_of (hne ρ3 hy3 _), ?_⟩
            simp only [Row.lookup, hNRow_eq, find?_map_val, hy3, Option.map_some, hev]

theorem tmplInfo_ok {τg : Ty} (hgood : goodTmpl τg = true) :
    TmplOK (tmplT (tyNames (hN τg)) (dedupL (recsT (hN τg))) (hN τg))
      (tmplCls 0 (tyNames (hN τg)) ++ tmplHasL (tyNames (hN τg)) (dedupL (recsT (hN τg))) 0 (dedupL (recsT (hN τg))))
      τg := by
  intro S τ hS hSg
  refine ⟨tmplVal S τg, tmpl_ok hgood hSg τg τ (fun x hx => hx) (fun x hx => hx) hSg,
    Holds.append.mpr ⟨?_, tmplHas_ok hgood hSg⟩⟩
  intro c hc
  obtain ⟨j, hj, rfl, hcls⟩ := mem_tmplCls 0 _ hc
  simp only [Nat.zero_add, Con.holds, T.ev, tmplVal]
  have hs : (tyNames (hN τg)).getD j "" ∈ tyNames (hN τg) := by
    have e : (tyNames (hN τg)).getD j "" = (tyNames (hN τg))[j] := by
      simp [List.getD, List.getElem?_eq_getElem hj]
    rw [e]; exact List.getElem_mem hj
  generalize (tyNames (hN τg)).getD j "" = s at hs hcls ⊢
  rcases names_mem hs with h | h
  · have hvo : vOf τg s = .var (.named s) := by simp [vOf, h]
    rw [hvo]
    simp only [Subst.apply, Option.getD_some]
    exact adm_hN (adm_apply_var hS (.named s))
  · rcases good_var hgood h with ⟨_, e, _⟩ | ⟨s', e, hc'⟩
    · cases e
    · cases e; exact absurd hc' hcls

/-! ## Occurrences of a template -/

section reloc
variable {μ : Val}

mutual
theorem fpos_spec (q : Path) : ∀ (t : T) (r r' : Path), fpos q r t = some r' →
    ∃ w, r' = w ++ r ∧ subAt (t.ev μ) w.reverse = μ q
  | .mv q', r, r', h => by
    simp only [fpos] at h
    split at h
    · rename_i e; subst e; cases h; exact ⟨[], rfl, rfl⟩
    · cases h
  | .var _, _, _, h => by simp [fpos] at h
  | .record ρ tl, r, r', h => by
    simp only [fpos] at h
    obtain ⟨j, w, rfl, hw⟩ := fposRow_spec q ρ r 0 r' h
    refine ⟨w ++ [j], by simp, ?_⟩
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      subAt, T.ev, tyChild]
    exact hw
  | .fn a b, r, r', h => by
    simp only [fpos] at h
    cases ha : fpos q (0 :: r) a with
    | some r1 =>
      rw [ha] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      obtain ⟨w, rfl, hw⟩ := fpos_spec q a (0 :: r) r1 ha
      exact ⟨w ++ [0], by simp, by simpa [subAt, T.ev, tyChild] using hw⟩
    | none =>
      rw [ha] at h
      simp only [Option.none_or] at h
      obtain ⟨w, rfl, hw⟩ := fpos_spec q b (1 :: r) r' h
      exact ⟨w ++ [1], by simp, by simpa [subAt, T.ev, tyChild] using hw⟩
  | .con as tn, r, r', h => by
    simp only [fpos] at h
    obtain ⟨j, w, rfl, hw⟩ := fposList_spec q as r 0 r' h
    refine ⟨w ++ [j], by simp, ?_⟩
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      subAt, T.ev, tyChild]
    exact hw
theorem fposRow_spec (q : Path) : ∀ (ρ : List (Lab × T)) (r : Path) (i : Nat) (r' : Path), fposRow q r i ρ = some r' →
    ∃ j w, r' = w ++ ((i + j) :: r) ∧ subAt (((T.evRow μ ρ).getD j default).2) w.reverse = μ q
  | [], _, _, _, h => by simp [fposRow] at h
  | (l, x) :: rest, r, i, r', h => by
    simp only [fposRow] at h
    cases hx : fpos q (i :: r) x with
    | some r1 =>
      rw [hx] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      obtain ⟨w, rfl, hw⟩ := fpos_spec q x (i :: r) r1 hx
      exact ⟨0, w, by simp, by simpa [T.evRow] using hw⟩
    | none =>
      rw [hx] at h
      simp only [Option.none_or] at h
      obtain ⟨j, w, rfl, hw⟩ := fposRow_spec q rest r (i + 1) r' h
      exact ⟨j + 1, w, by simp [Nat.add_assoc, Nat.add_comm 1 j], by simpa [T.evRow] using hw⟩
theorem fposList_spec (q : Path) : ∀ (l : List T) (r : Path) (i : Nat) (r' : Path), fposList q r i l = some r' →
    ∃ j w, r' = w ++ ((i + j) :: r) ∧ subAt ((T.evList μ l).getD j default) w.reverse = μ q
  | [], _, _, _, h => by simp [fposList] at h
  | x :: rest, r, i, r', h => by
    simp only [fposList] at h
    cases hx : fpos q (i :: r) x with
    | some r1 =>
      rw [hx] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      obtain ⟨w, rfl, hw⟩ := fpos_spec q x (i :: r) r1 hx
      exact ⟨0, w, by simp, by simpa [T.evList] using hw⟩
    | none =>
      rw [hx] at h
      simp only [Option.none_or] at h
      obtain ⟨j, w, rfl, hw⟩ := fposList_spec q rest r (i + 1) r' h
      exact ⟨j + 1, w, by simp [Nat.add_assoc, Nat.add_comm 1 j], by simpa [T.evList] using hw⟩
end

end reloc

mutual
theorem occ_fpos (q : Path) : ∀ (t : T) (r : Path), t.occ q = true → (fpos q r t).isSome
  | .mv q', r, h => by simp only [T.occ, beq_iff_eq] at h; subst h; simp [fpos]
  | .var _, _, h => by simp [T.occ] at h
  | .record ρ _, r, h => by simp only [T.occ] at h; simp only [fpos]; exact occRow_fpos q ρ r 0 h
  | .fn a b, r, h => by
    simp only [T.occ, Bool.or_eq_true] at h
    simp only [fpos]
    rcases h with h | h
    · have := occ_fpos q a (0 :: r) h
      cases hx : fpos q (0 :: r) a with
      | none => rw [hx] at this; cases this
      | some _ => rfl
    · have := occ_fpos q b (1 :: r) h
      cases fpos q (0 :: r) a <;> simpa using this
  | .con as _, r, h => by simp only [T.occ] at h; simp only [fpos]; exact occList_fpos q as r 0 h
theorem occRow_fpos (q : Path) : ∀ (ρ : List (Lab × T)) (r : Path) (i : Nat), T.occRow q ρ = true → (fposRow q r i ρ).isSome
  | [], _, _, h => by simp [T.occRow] at h
  | (_, x) :: rest, r, i, h => by
    simp only [T.occRow, Bool.or_eq_true] at h
    simp only [fposRow]
    rcases h with h | h
    · have := occ_fpos q x (i :: r) h
      cases hx : fpos q (i :: r) x with
      | none => rw [hx] at this; cases this
      | some _ => rfl
    · have := occRow_fpos q rest r (i + 1) h
      cases fpos q (i :: r) x <;> simpa using this
theorem occList_fpos (q : Path) : ∀ (l : List T) (r : Path) (i : Nat), T.occList q l = true → (fposList q r i l).isSome
  | [], _, _, h => by simp [T.occList] at h
  | x :: rest, r, i, h => by
    simp only [T.occList, Bool.or_eq_true] at h
    simp only [fposList]
    rcases h with h | h
    · have := occ_fpos q x (i :: r) h
      cases hx : fpos q (i :: r) x with
      | none => rw [hx] at this; cases this
      | some _ => rfl
    · have := occList_fpos q rest r (i + 1) h
      cases fpos q (i :: r) x <;> simpa using this
end

section reloc2
variable {ν μ : Val} {base : Path} {t0 : T}

mutual
theorem reloc_ev (hs : ∀ q, t0.occ q = true → ν (slotOf base t0 q) = μ q) :
    ∀ t : T, (∀ q, t.occ q = true → t0.occ q = true) → (reloc base t0 t).ev ν = t.ev μ
  | .mv q, ho => by simp only [reloc, T.ev]; exact hs q (ho q (by simp [T.occ]))
  | .var _, _ => rfl
  | .record ρ tl, ho => by
    simp only [reloc, T.ev, relocRow_ev hs ρ (fun q h => ho q (by simpa [T.occ] using h))]
  | .fn a b, ho => by
    simp only [reloc, T.ev, reloc_ev hs a (fun q h => ho q (by simp [T.occ, h])),
      reloc_ev hs b (fun q h => ho q (by simp [T.occ, h]))]
  | .con as tn, ho => by
    simp only [reloc, T.ev, relocList_ev hs as (fun q h => ho q (by simpa [T.occ] using h))]
theorem relocRow_ev (hs : ∀ q, t0.occ q = true → ν (slotOf base t0 q) = μ q) :
    ∀ ρ : List (Lab × T), (∀ q, T.occRow q ρ = true → t0.occ q = true) →
      T.evRow ν (relocRow base t0 ρ) = T.evRow μ ρ
  | [], _ => rfl
  | (l, x) :: r, ho => by
    simp only [relocRow, T.evRow, reloc_ev hs x (fun q h => ho q (by simp [T.occRow, h])),
      relocRow_ev hs r (fun q h => ho q (by simp [T.occRow, h]))]
theorem relocList_ev (hs : ∀ q, t0.occ q = true → ν (slotOf base t0 q) = μ q) :
    ∀ l : List T, (∀ q, T.occList q l = true → t0.occ q = true) →
      T.evList ν (relocList base t0 l) = T.evList μ l
  | [], _ => rfl
  | x :: r, ho => by
    simp only [relocList, T.evList, reloc_ev hs x (fun q h => ho q (by simp [T.occList, h])),
      relocList_ev hs r (fun q h => ho q (by simp [T.occList, h]))]
end

mutual
theorem reloc_ev' (hs : ∀ q, (fpos q [] t0).isSome → ν (slotOf base t0 q) = μ q) :
    ∀ t : T, occIn t0 t = true → (reloc base t0 t).ev ν = t.ev μ
  | .mv q, ho => by simp only [reloc, T.ev]; exact hs q ho
  | .var _, _ => rfl
  | .record ρ tl, ho => by
    simp only [occIn] at ho
    simp only [reloc, T.ev, relocRow_ev' hs ρ ho]
  | .fn a b, ho => by
    simp only [occIn, Bool.and_eq_true] at ho
    simp only [reloc, T.ev, reloc_ev' hs a ho.1, reloc_ev' hs b ho.2]
  | .con as tn, ho => by
    simp only [occIn] at ho
    simp only [reloc, T.ev, relocList_ev' hs as ho]
theorem relocRow_ev' (hs : ∀ q, (fpos q [] t0).isSome → ν (slotOf base t0 q) = μ q) :
    ∀ ρ : List (Lab × T), occInRow t0 ρ = true → T.evRow ν (relocRow base t0 ρ) = T.evRow μ ρ
  | [], _ => rfl
  | (l, x) :: r, ho => by
    simp only [occInRow, Bool.and_eq_true] at ho
    simp only [relocRow, T.evRow, reloc_ev' hs x ho.1, relocRow_ev' hs r ho.2]
theorem relocList_ev' (hs : ∀ q, (fpos q [] t0).isSome → ν (slotOf base t0 q) = μ q) :
    ∀ l : List T, occInList t0 l = true → T.evList ν (relocList base t0 l) = T.evList μ l
  | [], _ => rfl
  | x :: r, ho => by
    simp only [occInList, Bool.and_eq_true] at ho
    simp only [relocList, T.evList, reloc_ev' hs x ho.1, relocList_ev' hs r ho.2]
end

end reloc2

/-- An occurrence of a template: its metavariables at their first positions in the
    occurrence's type. -/
theorem occ_tmpl {ν μ : Val} {p : Path} {t : T} {K : List Con} {τ : Ty}
    (h00 : ∀ w, ν (w.reverse ++ 0 :: 0 :: p) = subAt (hN τ) w) (he : t.ev μ = hN τ) (hK : Holds μ K) :
    Holds ν (relocK (0 :: 0 :: p) t K) ∧ (reloc (0 :: 0 :: p) t t).ev ν = hN τ := by
  have hslot : ∀ q, (fpos q [] t).isSome → ν (slotOf (0 :: 0 :: p) t q) = μ q := by
    intro q hq
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hq
    obtain ⟨w, rfl, hw⟩ := fpos_spec (μ := μ) q t [] r hr
    simp only [slotOf, hr, List.append_nil]
    have := h00 w.reverse
    rw [List.reverse_reverse] at this
    rw [this, ← he, hw]
  refine ⟨?_, ?_⟩
  · intro c hc
    simp only [relocK, List.mem_filterMap] at hc
    obtain ⟨c', hc', he'⟩ := hc
    match c', he' with
    | .cls (.mv q) k, he' =>
      simp only at he'
      split at he'
      · rename_i hq
        cases he'
        have := hK _ hc'
        simp only [Con.holds, T.ev] at this ⊢
        rw [hslot q hq]; exact this
      · cases he'
    | .has (.mv q) l u, he' =>
      simp only at he'
      split at he'
      · rename_i hq
        simp only [Bool.and_eq_true] at hq
        cases he'
        have := hK _ hc'
        simp only [Con.holds, T.ev] at this ⊢
        rw [hslot q hq.1, reloc_ev' hslot u hq.2]; exact this
      · cases he'
  · rw [reloc_ev (μ := μ) (fun q hq => hslot q (occ_fpos q t [] hq)) t (fun q h => h), he]

/-! ## Instances keep the classes of a normalised type -/

/-- K5, backward: a constructed type with arguments of the classes D(κ, t) is in Adm κ. -/
theorem adm_of_prop {k : Cls} {t : TyName} {ks : List Cls} {xs : List Ty} (hp : Cls.prop k t = some ks)
    (hz : zipAdm xs ks) : Adm k (.con xs t) := by
  cases k with
  | any => simp [Cls.prop] at hp
  | num =>
    simp only [Cls.prop] at hp
    split at hp
    · rename_i h
      cases hp
      cases xs with
      | cons _ _ => simp [zipAdm] at hz
      | nil => rcases h with rfl | rfl; exact .num_int; exact .num_float
    · cases hp
  | comp =>
    simp only [Cls.prop] at hp
    split at hp
    · rename_i h
      cases hp
      cases xs with
      | cons _ _ => simp [zipAdm] at hz
      | nil =>
        rcases h with rfl | rfl | rfl | rfl
        · exact .comp_int
        · exact .comp_float
        · exact .comp_char
        · exact .comp_string
    · split at hp
      · rename_i _ h
        subst h; cases hp
        match xs, hz with
        | [x], hz => exact .comp_list x hz.1
      · split at hp
        · rename_i _ _ h
          subst h; cases hp
          match xs, hz with
          | [x, y], hz => exact .comp_tuple2 x y hz.1 hz.2.1
        · split at hp
          · rename_i _ _ _ h
            subst h; cases hp
            match xs, hz with
            | [x, y, z], hz => exact .comp_tuple3 x y z hz.1 hz.2.1 hz.2.2.1
          · cases hp
  | app =>
    simp only [Cls.prop] at hp
    split at hp
    · rename_i h
      subst h; cases hp
      cases xs with
      | cons _ _ => simp [zipAdm] at hz
      | nil => exact .app_string
    · split at hp
      · rename_i _ h
        subst h; cases hp
        match xs, hz with
        | [x], _ => exact .app_list x
      · cases hp
  | capp =>
    simp only [Cls.prop] at hp
    split at hp
    · rename_i h
      subst h; cases hp
      cases xs with
      | cons _ _ => simp [zipAdm] at hz
      | nil => exact .capp_string
    · split at hp
      · rename_i _ h
        subst h; cases hp
        match xs, hz with
        | [x], hz => exact .capp_list x hz.1
      · cases hp

theorem any_le {k : Cls} (h : Cls.le .any k = true) : k = .any := by
  cases k <;> simp_all [Cls.le]

section admApply
variable {S : Subst} (hS : S.Respects)
include hS

mutual
theorem adm_hN_apply : ∀ (k : Cls) (τ0 τ : Ty), Adm k (hN τ0) → S.apply τ0 = some τ → Adm k (hN τ)
  | .any, _, τ, _, _ => .any _
  | .num, τ0, τ, h, ha => adm_hN_apply_ne .num (by decide) τ0 τ h ha
  | .comp, τ0, τ, h, ha => adm_hN_apply_ne .comp (by decide) τ0 τ h ha
  | .app, τ0, τ, h, ha => adm_hN_apply_ne .app (by decide) τ0 τ h ha
  | .capp, τ0, τ, h, ha => adm_hN_apply_ne .capp (by decide) τ0 τ h ha
theorem adm_hN_apply_ne : ∀ (k : Cls), k ≠ .any → ∀ (τ0 τ : Ty), Adm k (hN τ0) → S.apply τ0 = some τ → Adm k (hN τ)
  | k, hk, .var a, τ, h, ha => by
    simp only [Subst.apply, Option.some.injEq] at ha
    subst ha
    exact adm_hN (adm_mono (adm_var h) (adm_apply_var hS a))
  | k, hk, .record ρ tl, τ, h, ha => by
    exfalso
    simp only [hN] at h
    rcases hRec_cases (hNRow ρ) tl with ⟨e, _⟩ | ⟨s, _, _, hc, e⟩ <;> rw [e] at h
    · exact hk (adm_record h)
    · have := adm_var h
      simp only [TyVar.cls, hc] at this
      exact hk (any_le this)
  | k, hk, .fn a b, τ, h, _ => absurd (adm_fn h) hk
  | k, hk, .con as t, τ, h, ha => by
    simp only [hN] at h
    obtain ⟨ks, hp, hz⟩ := adm_con hk h
    simp only [Subst.apply] at ha
    cases has : S.applyList as with
    | none => rw [has] at ha; cases ha
    | some as' =>
      rw [has] at ha
      simp only [Option.some.injEq] at ha
      subst ha
      simp only [hN]
      exact adm_of_prop hp (zipAdm_hN_apply as as' ks hz has)
theorem zipAdm_hN_apply : ∀ (as as' : List Ty) (ks : List Cls), zipAdm (hNList as) ks → S.applyList as = some as' →
    zipAdm (hNList as') ks
  | [], as', ks, hz, ha => by simp only [Subst.applyList, Option.some.injEq] at ha; subst ha; exact hz
  | x :: r, as', [], hz, _ => by simp [hNList, zipAdm] at hz
  | x :: r, as', k :: ks, hz, ha => by
    simp only [hNList, zipAdm] at hz
    simp only [Subst.applyList] at ha
    cases hx : S.apply x with
    | none => rw [hx] at ha; cases ha
    | some x' =>
      cases hr : S.applyList r with
      | none => rw [hx, hr] at ha; cases ha
      | some r' =>
        rw [hx, hr] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        exact ⟨adm_hN_apply k x x' hz.1 hx, zipAdm_hN_apply r r' ks hz.2 hr⟩
end

end admApply

/-- A metavariable with classes: every respecting instance of a type with those classes. -/
theorem tmplMv_ok {τ0 : Ty} {ks : List Cls} (h : ∀ k ∈ ks, Adm k (hN τ0)) :
    TmplOK (.mv [0]) (ks.map fun k => .cls (.mv [0]) k) τ0 := by
  intro S τ hS ha
  refine ⟨fun _ => hN τ, rfl, fun c hc => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  exact adm_hN_apply hS k τ0 τ (h k hk) ha

theorem mem_clsOf {q : Path} {sol : List Con} {k : Cls} (h : k ∈ clsOf q sol) : Con.cls (.mv q) k ∈ sol := by
  obtain ⟨c, hc, hs⟩ := List.mem_filterMap.mp h
  unfold clsSelOf at hs
  split at hs
  · rename_i q' k'
    split at hs
    · rename_i e; subst e; cases hs; exact hc
    · cases hs
  · cases hs

end StandardElm.Stat.Complete
