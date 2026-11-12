/-
  A Standard Definition of Elm? Mechanisation: the module step (plan step 10), second part:
  closedness. A module context built from a basis whose interfaces are closed has no free type
  variables, and each declaration a module checks gives a closed environment (values by
  `closGroup []`, ports by `closScheme []`, type declarations by r:sm-topdec-types' side condition
  `tyvars TE = ∅` and the closure of their constructors), so the context of the next declaration
  and the module's interface are closed.
-/
import StandardElmMech.Stat.ModuleStepSwap

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BDatBind BTypBind BItem BExpList)

namespace Closed

/-! ## Free variables of finite maps -/

section
variable {K V : Type} [DecidableEq K] {f : V → List BVar}

theorem tvb_head {seen : List K} {k : K} {v : V} :
    (if (f v).isEmpty || decide (k ∈ seen) then [] else f v) = [] ↔ (f v = [] ∨ k ∈ seen) := by
  by_cases h1 : f v = [] <;> by_cases h2 : k ∈ seen <;> simp [h1, h2]

theorem tvb_mono : ∀ {seen seen' : List K} {l : FMap K V}, FMap.tyvarsBy f seen l = [] →
    (∀ x ∈ seen, x ∈ seen') → FMap.tyvarsBy f seen' l = []
  | _, _, [], _, _ => rfl
  | seen, seen', (k, v) :: rest, h, hs => by
    simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head] at h ⊢
    refine ⟨h.1.imp id (hs k), tvb_mono h.2 fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hs x hx)

theorem tvb_allNil : ∀ {seen : List K} {l : FMap K V}, (∀ p ∈ l, f p.2 = []) → FMap.tyvarsBy f seen l = []
  | _, [], _ => rfl
  | _, (k, v) :: rest, h => by
    simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head]
    exact ⟨.inl (h _ (List.mem_cons_self ..)), tvb_allNil fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

theorem tvb_append : ∀ {seen : List K} {l l' : FMap K V}, FMap.tyvarsBy f seen l = [] →
    FMap.tyvarsBy f (l.map (·.1) ++ seen) l' = [] → FMap.tyvarsBy f seen (l ++ l') = []
  | _, [], _, _, h' => by simpa using h'
  | seen, (k, v) :: rest, l', h, h' => by
    simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head, List.cons_append] at h ⊢
    refine ⟨h.1, tvb_append h.2 (tvb_mono h' fun x hx => ?_)⟩
    simp only [List.map_cons, List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with (rfl | hx) | hx
    · exact .inr (.inl rfl)
    · exact .inl hx
    · exact .inr (.inr hx)

theorem tvb_filter (ks : List K) : ∀ {seen : List K} {l : FMap K V}, FMap.tyvarsBy f seen l = [] →
    FMap.tyvarsBy f (ks ++ seen) (l.filter fun p => !decide (p.1 ∈ ks)) = []
  | _, [], _ => rfl
  | seen, (k, v) :: rest, h => by
    simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head] at h
    have ih := tvb_filter ks (seen := k :: seen) h.2
    rw [List.filter_cons]
    by_cases hk : k ∈ ks
    · simp only [hk, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact tvb_mono ih fun x hx => by
        simp only [List.mem_append, List.mem_cons] at hx ⊢; rcases hx with hx | rfl | hx <;> simp_all
    · simp only [hk, decide_false, Bool.not_false, ↓reduceIte, FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head]
      refine ⟨h.1.imp id fun hs => List.mem_append_right _ hs, tvb_mono ih fun x hx => ?_⟩
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | rfl | hx
      · exact .inr (.inl hx)
      · exact .inl rfl
      · exact .inr (.inr hx)

theorem tvb_modify {g h : FMap K V} (hh : FMap.tyvarsBy f [] h = []) (hg : FMap.tyvarsBy f [] g = []) :
    FMap.tyvarsBy f [] (FMap.modify h g) = [] := by
  unfold FMap.modify
  refine tvb_append hg ?_
  have := tvb_filter (f := f) (FMap.keys g) (seen := []) hh
  simpa [FMap.keys] using this

theorem tvb_find : ∀ {seen : List K} {l : FMap K V} {k : K} {v : V}, FMap.tyvarsBy f seen l = [] →
    FMap.find? l k = some v → k ∉ seen → f v = []
  | _, [], _, _, _, h, _ => by simp at h
  | seen, (k', v') :: rest, k, v, h, hf, hk => by
    simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head] at h
    simp only [FMap.find?] at hf
    split at hf
    · rename_i e; subst e; cases hf
      exact h.1.resolve_right hk
    · rename_i e
      exact tvb_find h.2 hf fun hm => by
        rcases List.mem_cons.mp hm with e' | hm
        · exact e e'.symm
        · exact hk hm

theorem mem_modify {x : K × V} {g h : FMap K V} (hx : x ∈ FMap.modify h g) : x ∈ g ∨ x ∈ h := by
  unfold FMap.modify at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact .inl hx
  · exact .inr (List.mem_filter.mp hx).1

theorem mem_foldl_modify {x : K × V} : ∀ {acc : FMap K V} {fs : List (FMap K V)},
    x ∈ fs.foldl FMap.modify acc → x ∈ acc ∨ ∃ g ∈ fs, x ∈ g
  | _, [], hx => .inl hx
  | acc, g :: gs, hx => by
    rcases mem_foldl_modify (acc := FMap.modify acc g) (fs := gs) hx with h | ⟨g', hg', h⟩
    · rcases mem_modify h with h | h
      · exact .inr ⟨g, List.mem_cons_self .., h⟩
      · exact .inl h
    · exact .inr ⟨g', List.mem_cons_of_mem _ hg', h⟩

theorem mem_plusAll {x : K × V} {fs : List (FMap K V)} (hx : x ∈ FMap.plusAll fs) : ∃ g ∈ fs, x ∈ g := by
  rcases mem_foldl_modify (acc := []) hx with h | h
  · simp at h
  · exact h

end

/-! ## Closed environments -/

theorem env_tyvars_nil {E : Env} : E.tyvars = [] ↔
    FMap.tyvarsBy IEnv.tyvars [] E.QE = [] ∧ TyEnv.tyvars E.TE = [] ∧ ValEnv.tyvars E.VE = [] := by
  simp [Env.tyvars, List.append_eq_nil_iff]

theorem plus_closed {E E' : Env} (h : E.tyvars = []) (h' : E'.tyvars = []) : (E.plus E').tyvars = [] := by
  rw [env_tyvars_nil] at h h' ⊢
  exact ⟨tvb_modify h.1 h'.1, tvb_modify h.2.1 h'.2.1, tvb_modify h.2.2 h'.2.2⟩

theorem oplusE_closed {C : Ctx} {E : Env} (hC : C.tyvars = []) (hE : E.tyvars = []) : (C.oplusE E).tyvars = [] := by
  simp only [Ctx.tyvars, List.append_eq_nil_iff] at hC ⊢
  exact ⟨plus_closed hC.1 hE, hC.2⟩

theorem oplusTE_closed {C : Ctx} {TE : TyEnv} (hC : C.tyvars = []) (hTE : TyEnv.tyvars TE = []) :
    (C.oplusTE TE).tyvars = [] := by
  simp only [Ctx.tyvars, List.append_eq_nil_iff, Ctx.oplusTE] at hC ⊢
  rw [env_tyvars_nil] at hC ⊢
  exact ⟨⟨hC.1.1, tvb_modify hC.1.2.1 hTE, hC.1.2.2⟩, hC.2⟩

theorem plusU_tyvars (C : Ctx) (hU : C.U = []) : C.tyvars = C.E.tyvars := by simp [Ctx.tyvars, hU]

/-! ## Closed schemes -/

theorem not_mem_dom_ty {S : Subst} {a : TyVar} (h : FMap.find? S.ty a = none) : BVar.ty a ∉ S.dom := by
  intro hm
  simp only [Subst.dom, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨p, hp, e⟩ | ⟨p, hp, e⟩
  · cases e
    have := (FMap.find?_isSome_iff S.ty p.1).mpr (List.mem_map_of_mem hp)
    rw [h] at this; cases this
  · cases e

theorem not_mem_dom_row {S : Subst} {e : RowVar} (h : FMap.find? S.row e = none) : BVar.row e ∉ S.dom := by
  intro hm
  simp only [Subst.dom, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨p, hp, e'⟩ | ⟨p, hp, e'⟩
  · cases e'
  · cases e'
    have := (FMap.find?_isSome_iff S.row p.1).mpr (List.mem_map_of_mem hp)
    rw [h] at this; cases this

mutual
theorem apply_vars_dom {S : Subst} (hS : BndRange S) :
    (τ : Ty) → ∀ {τ' : Ty}, S.apply τ = some τ' → ∀ v ∈ τ'.vars, v.isBnd = true ∨ (v ∈ τ.vars ∧ v ∉ S.dom)
  | .var a, τ', h, v, hv => by
    simp only [Subst.apply, Option.some.injEq] at h
    subst h
    cases hf : FMap.find? S.ty a with
    | none =>
      simp [hf, Ty.vars] at hv; subst hv
      exact .inr ⟨by simp [Ty.vars], not_mem_dom_ty hf⟩
    | some σ => simp [hf] at hv; exact .inl (hS.1 _ (find?_mem hf) v hv)
  | .record ρ none, τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.applyRow ρ <;> rw [h1] at h <;> simp at h
    subst h
    rcases applyRow_vars_dom hS ρ h1 v (by simpa [Ty.vars] using hv) with h | h
    · exact .inl h
    · exact .inr ⟨by simpa [Ty.vars] using h.1, h.2⟩
  | .record ρ (some e), τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.applyRow ρ with
    | none => rw [h1] at h; cases h
    | some ρ1 =>
      rw [h1] at h; simp only at h
      cases h2 : FMap.find? S.row e with
      | none =>
        rw [h2] at h; simp only [Option.some.injEq] at h; subst h
        simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · rcases applyRow_vars_dom hS ρ h1 v hv with h | h
          · exact .inl h
          · exact .inr ⟨by simp [Ty.vars, h.1], h.2⟩
        · exact .inr ⟨by simp [Ty.vars], not_mem_dom_row h2⟩
      | some p =>
        obtain ⟨ρ2, tl⟩ := p
        rw [h2] at h; simp only at h
        cases h3 : Row.merge ρ1 ρ2 with
        | none => rw [h3] at h; cases h
        | some ρ3 =>
          rw [h3] at h; simp only [Option.some.injEq] at h; subst h
          have hb := hS.2 _ (find?_mem h2)
          have hrow : ∀ x ∈ Ty.rowVars ρ3, x.isBnd = true ∨ (x ∈ (Ty.record ρ (some e)).vars ∧ x ∉ S.dom) := by
            intro x hx
            obtain ⟨q, hq, hxq⟩ := mem_rowVars.mp hx
            rcases merge_mem h3 q hq with hq | hq
            · rcases applyRow_vars_dom hS ρ h1 x (mem_rowVars.mpr ⟨q, hq, hxq⟩) with h | h
              · exact .inl h
              · exact .inr ⟨by simp [Ty.vars, h.1], h.2⟩
            · exact .inl (hb.1 x (mem_rowVars.mpr ⟨q, hq, hxq⟩))
          cases tl with
          | none => exact hrow v (by simpa [Ty.vars] using hv)
          | some e' =>
            simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact hrow v hv
            · exact .inl (hb.2 e' rfl)
  | .fn a b, τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.apply a <;> cases h2 : S.apply b <;> rw [h1, h2] at h <;> simp at h
    subst h
    simp only [Ty.vars, List.mem_append] at hv
    rcases hv with hv | hv
    · rcases apply_vars_dom hS a h1 v hv with h | h
      · exact .inl h
      · exact .inr ⟨by simp [Ty.vars, h.1], h.2⟩
    · rcases apply_vars_dom hS b h2 v hv with h | h
      · exact .inl h
      · exact .inr ⟨by simp [Ty.vars, h.1], h.2⟩
  | .con as t, τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.applyList as <;> rw [h1] at h <;> simp at h
    subst h
    simp only [Ty.vars] at hv ⊢
    exact applyList_vars_dom hS as h1 v hv
theorem applyRow_vars_dom {S : Subst} (hS : BndRange S) :
    (ρ : Row) → ∀ {ρ' : Row}, S.applyRow ρ = some ρ' → ∀ v ∈ Ty.rowVars ρ', v.isBnd = true ∨ (v ∈ Ty.rowVars ρ ∧ v ∉ S.dom)
  | [], ρ', h, v, hv => by simp [Subst.applyRow] at h; subst h; simp [Ty.rowVars] at hv
  | (l, τ) :: rest, ρ', h, v, hv => by
    simp only [Subst.applyRow] at h
    cases h1 : S.apply τ <;> cases h2 : S.applyRow rest <;> rw [h1, h2] at h <;> simp at h
    subst h
    simp only [Ty.rowVars, List.mem_append] at hv
    rcases hv with hv | hv
    · rcases apply_vars_dom hS τ h1 v hv with h | h
      · exact .inl h
      · exact .inr ⟨by simp [Ty.rowVars, h.1], h.2⟩
    · rcases applyRow_vars_dom hS rest h2 v hv with h | h
      · exact .inl h
      · exact .inr ⟨by simp [Ty.rowVars, h.1], h.2⟩
theorem applyList_vars_dom {S : Subst} (hS : BndRange S) :
    (l : List Ty) → ∀ {l' : List Ty}, S.applyList l = some l' → ∀ v ∈ Ty.listVars l', v.isBnd = true ∨ (v ∈ Ty.listVars l ∧ v ∉ S.dom)
  | [], l', h, v, hv => by simp [Subst.applyList] at h; subst h; simp [Ty.listVars] at hv
  | τ :: rest, l', h, v, hv => by
    simp only [Subst.applyList] at h
    cases h1 : S.apply τ <;> cases h2 : S.applyList rest <;> rw [h1, h2] at h <;> simp at h
    subst h
    simp only [Ty.listVars, List.mem_append] at hv
    rcases hv with hv | hv
    · rcases apply_vars_dom hS τ h1 v hv with h | h
      · exact .inl h
      · exact .inr ⟨by simp [Ty.listVars, h.1], h.2⟩
    · rcases applyList_vars_dom hS rest h2 v hv with h | h
      · exact .inl h
      · exact .inr ⟨by simp [Ty.listVars, h.1], h.2⟩
end

/-- A substitution replacing row variables by empty rows is defined on every type. -/
def RowNil (S : Subst) : Prop := ∀ p ∈ S.row, p.2.1 = []

mutual
theorem apply_isSome {S : Subst} (hS : RowNil S) : (τ : Ty) → (S.apply τ).isSome
  | .var _ => rfl
  | .record ρ none => by
    have := applyRow_isSome hS ρ
    simp only [Subst.apply]
    cases h : S.applyRow ρ <;> simp_all
  | .record ρ (some e) => by
    have := applyRow_isSome hS ρ
    simp only [Subst.apply]
    cases h : S.applyRow ρ with
    | none => simp_all
    | some ρ1 =>
      simp only
      cases h2 : FMap.find? S.row e with
      | none => rfl
      | some p =>
        obtain ⟨ρ2, tl⟩ := p
        have : ρ2 = [] := hS _ (find?_mem h2)
        subst this
        simp [merge_nil_right]
  | .fn a b => by
    have h1 := apply_isSome hS a
    have h2 := apply_isSome hS b
    simp only [Subst.apply]
    cases e1 : S.apply a <;> cases e2 : S.apply b <;> simp_all
  | .con as _ => by
    have := applyList_isSome hS as
    simp only [Subst.apply]
    cases h : S.applyList as <;> simp_all
theorem applyRow_isSome {S : Subst} (hS : RowNil S) : (ρ : Row) → (S.applyRow ρ).isSome
  | [] => rfl
  | (_, τ) :: rest => by
    have h1 := apply_isSome hS τ
    have h2 := applyRow_isSome hS rest
    simp only [Subst.applyRow]
    cases e1 : S.apply τ <;> cases e2 : S.applyRow rest <;> simp_all
theorem applyList_isSome {S : Subst} (hS : RowNil S) : (l : List Ty) → (S.applyList l).isSome
  | [] => rfl
  | τ :: rest => by
    have h1 := apply_isSome hS τ
    have h2 := applyList_isSome hS rest
    simp only [Subst.applyList]
    cases e1 : S.apply τ <;> cases e2 : S.applyList rest <;> simp_all
end

theorem renumber_rowNil : ∀ (k : Bool) (i : Nat) (l : List BVar), RowNil (renumber k i l).1
  | _, _, [] => by simp [RowNil, renumber, Subst.id]
  | k, i, .ty a :: vs => by
    have := renumber_rowNil k (i + 1) vs
    simpa [RowNil, renumber] using this
  | k, i, .row e :: vs => by
    have := renumber_rowNil k (i + 1) vs
    simp only [RowNil, renumber, List.mem_cons] at this ⊢
    rintro p (rfl | hp)
    · rfl
    · exact this p hp

theorem renumber_dom : ∀ (k : Bool) (i : Nat) (l : List BVar), ∀ v ∈ l, v ∈ (renumber k i l).1.dom
  | _, _, [], _, h => by simp at h
  | k, i, .ty a :: vs, v, h => by
    have ih := renumber_dom k (i + 1) vs
    simp only [renumber, Subst.dom, List.map_cons, List.mem_cons, List.mem_append] at h ih ⊢
    rcases h with rfl | h
    · exact .inl (.inl rfl)
    · rcases ih v h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | k, i, .row e :: vs, v, h => by
    have ih := renumber_dom k (i + 1) vs
    simp only [renumber, Subst.dom, List.map_cons, List.mem_cons, List.mem_append] at h ih ⊢
    rcases h with rfl | h
    · exact .inr (.inl rfl)
    · rcases ih v h with h | h
      · exact .inl h
      · exact .inr (.inr h)

theorem mem_tyvars_of {v : BVar} {τ : Ty} (h : v ∈ τ.vars) (hb : v.isBnd = false) : v ∈ τ.tyvars :=
  List.mem_filter.mpr ⟨h, by simp [hb]⟩

/-- A canonical form whose bound list holds every free variable of its body is closed. -/
theorem canon_closed {bound : List BVar} {body : Ty} (h : ∀ v ∈ body.vars, v.isBnd = false → v ∈ bound) :
    (Scheme.canon ⟨bound, body⟩).tyvars = [] := by
  unfold Scheme.canon
  have hsome := apply_isSome (renumber_rowNil true 0 (canonVars bound body)) body
  obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp hsome
  simp only [hτ', Option.getD_some, Scheme.tyvars]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  have hv' := (mem_diffL.mp hv).1
  have hnb : v.isBnd = false := by simp only [Ty.tyvars, List.mem_filter] at hv'; simpa using hv'.2
  rcases apply_vars_dom (renumber_bndRange _ _ _) body hτ' v (mem_vars_of_tyvars hv') with hb | ⟨hb, hd⟩
  · rw [hnb] at hb; cases hb
  · apply hd
    apply renumber_dom
    simp only [canonVars, List.mem_append]
    exact .inl (mem_dedupL.mpr (List.mem_filter.mpr ⟨hb, by simpa using h v hb hnb⟩))

theorem closScheme_closed (σ : Scheme) : (closScheme [] σ).tyvars = [] := by
  unfold closScheme
  apply canon_closed
  intro v hv hb
  by_cases h : v ∈ σ.bound
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ (mem_diffL.mpr ⟨mem_dedupL.mpr ?_, by simp⟩)
    exact mem_diffL.mpr ⟨mem_tyvars_of hv hb, h⟩

theorem closVE_closed (VE : ValEnv) : ∀ p ∈ closVE [] VE, p.2.1.tyvars = [] := by
  intro p hp
  simp only [closVE, FMap.mapV, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  exact closScheme_closed _

theorem closGroup_closed (VE : ValEnv) : ∀ p ∈ closGroup [] VE, p.2.1.tyvars = [] := by
  intro p hp
  simp only [closGroup, FMap.mapV, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  apply canon_closed
  intro v hv hb
  by_cases h : v ∈ q.2.1.bound
  · exact List.mem_append_left _ (List.mem_append_left _ h)
  · refine List.mem_append_left _ (List.mem_append_right _ (mem_diffL.mpr ⟨mem_dedupL.mpr ?_, by simp⟩))
    exact mem_diffL.mpr ⟨mem_tyvars_of hv hb, h⟩

theorem valEnv_closed {VE : ValEnv} (h : ∀ p ∈ VE, p.2.1.tyvars = []) : ValEnv.tyvars VE = [] :=
  tvb_allNil fun p hp => h p hp

/-! ## The context of a module's imports -/

theorem E0_closed : TyEnv.tyvars E0.TE = [] ∧ ValEnv.tyvars E0.VE = [] := by decide +kernel

theorem teFind_closed {ME : ModEnv} (hME : ∀ p ∈ ME, p.2.tyvars = []) {m : ModId} {c : String} {s : TyStr}
    (h : teFind ME m c = some s) : s.1.tyvars ++ ValEnv.tyvars s.2 = [] := by
  unfold teFind at h
  cases h1 : FMap.find? (((FMap.find? ME m).map (·.TE)).getD []) c with
  | some s' =>
    rw [h1] at h; cases h
    cases h2 : FMap.find? ME m with
    | none => rw [h2] at h1; simp at h1
    | some I =>
      rw [h2] at h1
      have hI := hME _ (find?_mem h2)
      simp only [IEnv.tyvars, List.append_eq_nil_iff] at hI
      exact tvb_find (f := fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2) hI.1 h1 (by simp)
  | none =>
    rw [h1] at h; simp only [Option.none_or] at h
    split at h
    · exact tvb_find (f := fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2) E0_closed.1 h (by simp)
    · cases h

theorem veFind_closed {ME : ModEnv} (hME : ∀ p ∈ ME, p.2.tyvars = []) {m : ModId} {x : String} {b : Scheme × IdStatus}
    (h : veFind ME m x = some b) : b.1.tyvars = [] := by
  unfold veFind at h
  cases h1 : FMap.find? (((FMap.find? ME m).map (·.VE)).getD []) x with
  | some b' =>
    rw [h1] at h; cases h
    cases h2 : FMap.find? ME m with
    | none => rw [h2] at h1; simp at h1
    | some I =>
      rw [h2] at h1
      have hI := hME _ (find?_mem h2)
      simp only [IEnv.tyvars, List.append_eq_nil_iff] at hI
      exact tvb_find (f := fun b : Scheme × IdStatus => b.1.tyvars) hI.2 h1 (by simp)
  | none =>
    rw [h1] at h; simp only [Option.none_or] at h
    split at h
    · exact tvb_find (f := fun b : Scheme × IdStatus => b.1.tyvars) E0_closed.2 h (by simp)
    · cases h

theorem tvb_cons_nil {K V : Type} [DecidableEq K] {f : V → List BVar} {k : K} {v : V} {l : FMap K V}
    (hv : f v = []) (hl : FMap.tyvarsBy f [] l = []) : FMap.tyvarsBy f [] ((k, v) :: l) = [] := by
  simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head]
  exact ⟨.inl hv, tvb_mono hl (by simp)⟩

theorem addQ_closed (q : ModId) (g : IEnv → IEnv) (hg : ∀ I, I.tyvars = [] → (g I).tyvars = []) (he : (g IEnv.empty).tyvars = []) :
    ∀ {seen : List ModId} {QE : FMap ModId IEnv}, FMap.tyvarsBy IEnv.tyvars seen QE = [] →
      FMap.tyvarsBy IEnv.tyvars seen (addQ q g QE) = []
  | seen, [], _ => by
    simp only [addQ, FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head]; exact ⟨.inl he, trivial⟩
  | seen, (q', I) :: rest, h => by
    simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head] at h
    simp only [addQ]
    split
    · rename_i e; subst e
      simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head]
      exact ⟨h.1.imp (hg I) id, h.2⟩
    · simp only [FMap.tyvarsBy, List.append_eq_nil_iff, tvb_head]
      exact ⟨h.1, addQ_closed q g hg he h.2⟩

theorem envStep_closed {ME : ModEnv} (hME : ∀ p ∈ ME, p.2.tyvars = []) (p : SmLongId × List ModId) {E : Env}
    (hE : E.tyvars = []) : (envStep ME p E).tyvars = [] := by
  rw [env_tyvars_nil] at hE
  have hTE : ∀ (c : String) (s : TyStr) (TE : TyEnv), teFind ME (p.2.headD "") c = some s → True := fun _ _ _ _ => trivial
  clear hTE
  have gTE : ∀ (c : String) (s : TyStr), s.1.tyvars ++ ValEnv.tyvars s.2 = [] → ∀ I : IEnv, I.tyvars = [] →
      ({ I with TE := (c, s) :: I.TE } : IEnv).tyvars = [] := by
    intro c s hs I hI
    simp only [IEnv.tyvars, List.append_eq_nil_iff] at hI ⊢
    exact ⟨tvb_cons_nil (f := fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2) hs hI.1, hI.2⟩
  have gVE : ∀ (x : String) (b : Scheme × IdStatus), b.1.tyvars = [] → ∀ I : IEnv, I.tyvars = [] →
      ({ I with VE := (x, b) :: I.VE } : IEnv).tyvars = [] := by
    intro x b hb I hI
    simp only [IEnv.tyvars, List.append_eq_nil_iff] at hI ⊢
    exact ⟨hI.1, tvb_cons_nil (f := fun b : Scheme × IdStatus => b.1.tyvars) hb hI.2⟩
  have hempty : IEnv.empty.tyvars = [] := rfl
  rw [env_tyvars_nil]
  unfold envStep
  split
  · split
    · rename_i s hs
      exact ⟨hE.1, tvb_cons_nil (f := fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2) (teFind_closed hME hs) hE.2.1, hE.2.2⟩
    · exact hE
  · split
    · rename_i b hb
      exact ⟨hE.1, hE.2.1, tvb_cons_nil (f := fun b : Scheme × IdStatus => b.1.tyvars) (veFind_closed hME hb) hE.2.2⟩
    · exact hE
  · split
    · rename_i s hs
      have hs' := teFind_closed hME hs
      exact ⟨addQ_closed _ _ (gTE _ _ hs') (gTE _ _ hs' _ hempty) hE.1, hE.2.1, hE.2.2⟩
    · exact ⟨addQ_closed _ _ (fun I h => h) hempty hE.1, hE.2.1, hE.2.2⟩
  · split
    · rename_i b hb
      have hb' := veFind_closed hME hb
      exact ⟨addQ_closed _ _ (gVE _ _ hb') (gVE _ _ hb' _ hempty) hE.1, hE.2.1, hE.2.2⟩
    · exact ⟨addQ_closed _ _ (fun I h => h) hempty hE.1, hE.2.1, hE.2.2⟩
  · exact ⟨addQ_closed _ _ (fun I h => h) hempty hE.1, hE.2.1, hE.2.2⟩
  · exact hE

theorem envOf_closed {ME : ModEnv} (hME : ∀ p ∈ ME, p.2.tyvars = []) : ∀ π : ProvMap, (envOf ME π).tyvars = []
  | [] => rfl
  | p :: ps => by
    have := envOf_closed hME ps
    simp only [envOf, List.foldr_cons] at this ⊢
    exact envStep_closed hME p this

theorem importCtx_closed {B : SBasis} (hB : ∀ p ∈ B.ME, p.2.tyvars = []) {imps : List Src.BImport} {C : Ctx}
    (h : importCtx B imps = some C) : C.tyvars = [] ∧ C.U = [] ∧ C.T = B.T := by
  unfold importCtx at h
  cases h1 : elabImports B π0 (defaultImports ++ imps) with
  | none => rw [h1] at h; cases h
  | some π =>
    rw [h1] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact ⟨by simpa [Ctx.tyvars, modCtx] using envOf_closed hB π, rfl, rfl⟩

end Closed

end StandardElm.Stat
