/-
  A Standard Definition of Elm? Mechanisation: the module step (plan step 10), `ModuleStep
  TypesOrdered`, and with it the uniqueness of the specialisation of a program (`ident_of_spec'`),
  under D11 (`InferPrincipalFor`) and the decidable restriction on type declarations alone.

  Two module derivations in a basis `B` that are instances of each other: the instance's bijection
  ν between the names their custom types get keeps arities (`Walk.arity_walk`), so it extends to a
  bijection σ of all type names that fixes `B` and every other name of the first derivation's
  environments (`Swap.extend_pairs`). The walk (`Walk.walk`) gives the second's declarations σ of
  the first's, so the second's result is σ of the first's; the first's environment is closed and
  its port types are port types, so the next basis keeps `BasisInv`.
-/
import StandardElmMech.Stat.ModuleStepWalk

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BItem BExpList)

namespace MStep

/-! ## Interfaces -/

theorem tynames_modify_VE {f g : ValEnv} {t : TyName} (h : t ∈ ValEnv.tynames (FMap.modify f g)) :
    t ∈ ValEnv.tynames f ∨ t ∈ ValEnv.tynames g := by
  obtain ⟨p, hp, ht⟩ := List.mem_flatMap.mp h
  rcases Closed.mem_modify hp with hp | hp
  · exact .inr (List.mem_flatMap.mpr ⟨p, hp, ht⟩)
  · exact .inl (List.mem_flatMap.mpr ⟨p, hp, ht⟩)

theorem tynames_modify_TE {f g : TyEnv} {t : TyName} (h : t ∈ TyEnv.tynames (FMap.modify f g)) :
    t ∈ TyEnv.tynames f ∨ t ∈ TyEnv.tynames g := by
  obtain ⟨p, hp, ht⟩ := List.mem_flatMap.mp h
  rcases Closed.mem_modify hp with hp | hp
  · exact .inr (List.mem_flatMap.mpr ⟨p, hp, ht⟩)
  · exact .inl (List.mem_flatMap.mpr ⟨p, hp, ht⟩)

theorem env_tynames_mem {E : Env} {t : TyName} :
    (t ∈ TyEnv.tynames E.TE → t ∈ E.tynames) ∧ (t ∈ ValEnv.tynames E.VE → t ∈ E.tynames) :=
  ⟨fun h => by simp [Env.tynames, h], fun h => by simp [Env.tynames, h]⟩

section
variable {E : Env} (hE : E.tyvars = []) (hTE : ∀ p ∈ E.TE, ∀ q ∈ p.2.2, q.2.1.tyvars = [])
include hE hTE

theorem exposeItem_ok {it : BItem} {I : IEnv} (h : exposeItem E it = some I) :
    I.tyvars = [] ∧ ∀ t ∈ I.tynames, t ∈ E.tynames := by
  obtain ⟨-, hT, hV⟩ := Closed.env_tyvars_nil.mp hE
  cases it with
  | var x =>
    simp only [exposeItem] at h
    cases hf : FMap.find? E.VE x with
    | none => rw [hf] at h; cases h
    | some b =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      have hb := Closed.tvb_find (f := fun b : Scheme × IdStatus => b.1.tyvars) hV hf (by simp)
      refine ⟨by simp [IEnv.tyvars, TyEnv.tyvars, ValEnv.tyvars, FMap.tyvarsBy, hb], fun t ht => ?_⟩
      simp only [IEnv.tynames, TyEnv.tynames, ValEnv.tynames, List.flatMap_nil, List.nil_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] at ht
      exact env_tynames_mem.2 (List.mem_flatMap.mpr ⟨_, find?_mem hf, ht⟩)
  | op _ => simp [exposeItem] at h
  | ty c =>
    simp only [exposeItem] at h
    cases hf : FMap.find? E.TE c with
    | none => rw [hf] at h; cases h
    | some s =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      have hs := Closed.tvb_find (f := fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2) hT hf (by simp)
      have hin := hTE _ (find?_mem hf)
      refine ⟨?_, fun t ht => ?_⟩
      · simp only [IEnv.tyvars, List.append_eq_nil_iff]
        refine ⟨Closed.tvb_allNil fun p hp => by simp at hp; subst hp; exact hs, Closed.valEnv_closed fun q hq => ?_⟩
        exact hin q (List.mem_filter.mp hq).1
      · simp only [IEnv.tynames, TyEnv.tynames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append] at ht
        rcases ht with ht | ht
        · exact env_tynames_mem.1 (List.mem_flatMap.mpr ⟨_, find?_mem hf, List.mem_append.mpr ht⟩)
        · obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp ht
          exact env_tynames_mem.1 (List.mem_flatMap.mpr ⟨_, find?_mem hf,
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, (List.mem_filter.mp hq).1, ht⟩)⟩)
  | tyAll c =>
    simp only [exposeItem] at h
    cases hf : FMap.find? E.TE c with
    | none => rw [hf] at h; cases h
    | some s =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      have hs := Closed.tvb_find (f := fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2) hT hf (by simp)
      refine ⟨?_, fun t ht => ?_⟩
      · simp only [IEnv.tyvars, List.append_eq_nil_iff]
        exact ⟨Closed.tvb_allNil fun p hp => by simp at hp; subst hp; exact hs,
          (List.append_eq_nil_iff.mp hs).2⟩
      · simp only [IEnv.tynames, TyEnv.tynames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append] at ht
        rcases ht with ht | ht
        · exact env_tynames_mem.1 (List.mem_flatMap.mpr ⟨_, find?_mem hf, List.mem_append.mpr ht⟩)
        · exact env_tynames_mem.1 (List.mem_flatMap.mpr ⟨_, find?_mem hf, List.mem_append_right _ ht⟩)

theorem exposeItems_ok : ∀ {is : List BItem} {I : IEnv}, exposeItems E is = some I →
    I.tyvars = [] ∧ ∀ t ∈ I.tynames, t ∈ E.tynames
  | [], I, h => by simp [exposeItems] at h; subst h; exact ⟨rfl, by simp [IEnv.empty, IEnv.tynames, TyEnv.tynames, ValEnv.tynames]⟩
  | it :: rest, I, h => by
    simp only [exposeItems] at h
    split at h
    · rename_i I1 I2 h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨c1, n1⟩ := exposeItem_ok hE hTE h1
      obtain ⟨c2, n2⟩ := exposeItems_ok h2
      simp only [IEnv.tyvars, List.append_eq_nil_iff] at c1 c2
      refine ⟨by simp only [IEnv.plus, IEnv.tyvars, List.append_eq_nil_iff]; exact
        ⟨Closed.tvb_modify c1.1 c2.1, Closed.tvb_modify c1.2 c2.2⟩, fun t ht => ?_⟩
      simp only [IEnv.plus, IEnv.tynames, List.mem_append] at ht
      rcases ht with ht | ht
      · rcases tynames_modify_TE ht with ht | ht
        · exact n1 t (by simp [IEnv.tynames, ht])
        · exact n2 t (by simp [IEnv.tynames, ht])
      · rcases tynames_modify_VE ht with ht | ht
        · exact n1 t (by simp [IEnv.tynames, ht])
        · exact n2 t (by simp [IEnv.tynames, ht])
    · cases h

theorem expose_ok {el : BExpList} {I : IEnv} (h : expose E el = some I) :
    I.tyvars = [] ∧ ∀ t ∈ I.tynames, t ∈ E.tynames := by
  cases el with
  | all =>
    simp only [expose, Option.some.injEq] at h; subst h
    obtain ⟨-, hT, hV⟩ := Closed.env_tyvars_nil.mp hE
    refine ⟨by simp [IEnv.tyvars, Env.toI, hT, hV], fun t ht => ?_⟩
    simp only [Env.toI, IEnv.tynames, List.mem_append] at ht
    rcases ht with ht | ht
    · exact env_tynames_mem.1 ht
    · exact env_tynames_mem.2 ht
  | items is => exact exposeItems_ok hE hTE h

end

/-! ## Port types are made of type names of T0 -/

mutual
theorem portB_names : (τ : Ty) → portB τ = true → ∀ t ∈ τ.tynames, t ∈ T0
  | .con [] t, h, u, hu => by
    simp only [Ty.tynames, Ty.listTynames, List.mem_singleton] at hu; subst hu
    simp only [portB, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((((((h | h) | h) | h) | h) | h) | h) <;> subst h <;> decide
  | .con [τ] t, h, u, hu => by
    simp only [portB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    simp only [Ty.tynames, Ty.listTynames, List.append_nil, List.mem_cons] at hu
    rcases hu with rfl | hu
    · rcases h.1 with ((h | h) | h) <;> subst h <;> decide
    · exact portB_names τ h.2 u hu
  | .con [τ1, τ2] t, h, u, hu => by
    simp only [portB, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Ty.tynames, Ty.listTynames, List.append_nil, List.mem_cons, List.mem_append] at hu
    rcases hu with rfl | hu | hu
    · rw [h.1.1]; decide
    · exact portB_names τ1 h.1.2 u hu
    · exact portB_names τ2 h.2 u hu
  | .con [τ1, τ2, τ3] t, h, u, hu => by
    simp only [portB, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Ty.tynames, Ty.listTynames, List.append_nil, List.mem_cons, List.mem_append] at hu
    rcases hu with rfl | hu | hu | hu
    · rw [h.1.1.1]; decide
    · exact portB_names τ1 h.1.1.2 u hu
    · exact portB_names τ2 h.1.2 u hu
    · exact portB_names τ3 h.2 u hu
  | .con (_ :: _ :: _ :: _ :: _) _, h, _, _ => by simp [portB] at h
  | .record ρ none, h, u, hu => by
    simp only [portB] at h; simp only [Ty.tynames] at hu; exact portRowB_names ρ h u hu
  | .record _ (some _), h, _, _ => by simp [portB] at h
  | .var _, h, _, _ => by simp [portB] at h
  | .fn _ _, h, _, _ => by simp [portB] at h
theorem portRowB_names : (ρ : Row) → portRowB ρ = true → ∀ t ∈ Ty.rowTynames ρ, t ∈ T0
  | [], _, _, hu => by simp [Ty.rowTynames] at hu
  | (_, τ) :: rest, h, u, hu => by
    simp only [portRowB, Bool.and_eq_true] at h
    simp only [Ty.rowTynames, List.mem_append] at hu
    rcases hu with hu | hu
    · exact portB_names τ h.1 u hu
    · exact portRowB_names rest h.2 u hu
end

/-! ## The next basis -/

theorem resultIn_inv {B : SBasis} {C : Ctx} {a : AModule} {R : SBasis} {E : Env} (h : a.resultIn B C = some (R, E)) :
    ∃ PE I, checkTopDecOpt C a.body = some (E, PE) ∧ expose E a.header.exposing = some I ∧
      R = ⟨diffL (dedupL E.tynames) B.T, [(a.header.name, I)], PE⟩ := by
  unfold AModule.resultIn at h
  split at h
  · cases h
  · rename_i E' PE hk
    split at h
    · cases h
    · rename_i I hI
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨PE, I, hk, hI, rfl⟩

theorem mem_unionL {α : Type} [DecidableEq α] {x : α} {A B : List α} (h : x ∈ A ∨ x ∈ B) : x ∈ unionL A B := by
  unfold unionL
  by_cases hA : x ∈ A
  · exact List.mem_append_left _ hA
  · exact List.mem_append_right _ (mem_diffL.mpr ⟨h.resolve_left hA, hA⟩)

theorem basisInv_next {B : SBasis} (hB : BasisInv B) {C : Ctx} {a : AModule} {R : SBasis} {E : Env} {PE : PortEnv}
    (hk : checkTopDecOpt C a.body = some (E, PE)) (hg : Walk.Good E PE) (hr : a.resultIn B C = some (R, E)) :
    BasisInv (B.plus R) := by
  obtain ⟨PE', I, hk', hI, rfl⟩ := resultIn_inv hr
  rw [hk] at hk'; cases hk'
  obtain ⟨hIc, hIn⟩ := expose_ok hg.1 hg.2.1 hI
  have hT : ∀ t, t ∈ B.T ∨ t ∈ E.tynames → t ∈ (B.plus ⟨diffL (dedupL E.tynames) B.T, [(a.header.name, I)], PE⟩).T := by
    intro t ht
    simp only [SBasis.plus]
    apply mem_unionL
    by_cases h : t ∈ B.T
    · exact .inl h
    · exact .inr (mem_diffL.mpr ⟨mem_dedupL.mpr (ht.resolve_left h), h⟩)
  refine ⟨fun t ht => hT t (.inl (hB.t0 t ht)), ?_, ?_, ?_⟩
  · intro p hp t ht
    rcases Closed.mem_modify hp with hp | hp
    · simp at hp; subst hp; exact hT t (.inr (hIn t ht))
    · exact hT t (.inl (hB.names p hp t ht))
  · intro p hp t ht
    rcases Closed.mem_modify hp with hp | hp
    · exact hT t (.inl (hB.t0 t (portB_names _ (hg.2.2 p hp) t ht)))
    · exact hT t (.inl (hB.pe p hp t ht))
  · intro p hp
    rcases Closed.mem_modify hp with hp | hp
    · simp at hp; subst hp; exact hIc
    · exact hB.closed p hp

/-- The second derivation's result, when its declarations give σ of the first's. -/
theorem result_transfer {σ : List (TyName × TyName)} (hσ : NR σ) {B : SBasis} (hσB : (nr σ).basis B = B)
    {a a2 : AModule} {C : Ctx} (hC : importCtx B a.imports = some C) (himp : a2.imports = a.imports)
    (hhead : a2.header = a.header) {E0 : Env} {PE0 : PortEnv}
    (hk : checkTopDecOpt C a.body = some (E0, PE0))
    (hk2 : checkTopDecOpt C a2.body = some ((nr σ).env E0, (nr σ).portEnv PE0)) :
    a2.result B = (a.result B).map fun p => ((nr σ).basis p.1, (nr σ).env p.2) := by
  have hσC : (nr σ).ctx C = C := by
    have := nr_importCtx hσ B a.imports
    rw [hσB, hC] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact this.symm
  rw [AModule.result_of_ctx (by rw [himp]; exact hC), AModule.result_of_ctx hC]
  have e1 : a2.resultIn B C = (a.rename (nr σ)).resultIn B C := by
    unfold AModule.resultIn
    have : checkTopDecOpt C (a.rename (nr σ)).body = some ((nr σ).env E0, (nr σ).portEnv PE0) := by
      rw [nr_rename_body, ← hσC, nr_checkTopDecOpt hσ, hk]; rfl
    rw [hk2, this, nr_rename_header, hhead]
  rw [e1]
  have := nr_resultIn hσ B C a
  rw [hσB, hσC] at this
  exact this

/-! ## The module step -/

/-- Two module derivations in a basis with `BasisInv`, each an instance of the other, give results
    that differ by a bijection of type names fixing the basis, when the module's type declarations
    are ordered (plan step 10). -/
theorem moduleStep : ModuleStep TypesOrdered := by
  intro B m m2 hB hT hc hc2 hn hn2 h1 h2
  have himp : m2.imports = m.imports := congrArg Src.BModule.imports h1.1
  have hhead : m2.header = m.header := congrArg Src.BModule.header h1.1
  have hbody : m2.body.map ATopDec.erase = m.body.map ATopDec.erase := congrArg Src.BModule.body h1.1
  obtain ⟨C, hC⟩ : ∃ C, importCtx B m.imports = some C := by
    unfold checkModule AModule.result at hc
    cases e : importCtx B m.imports with
    | none => rw [e] at hc; cases hc
    | some C => exact ⟨C, rfl⟩
  have hC2 : importCtx B m2.imports = some C := by rw [himp, hC]
  obtain ⟨hcl, hU, hCT⟩ := Closed.importCtx_closed hB.closed hC
  obtain ⟨⟨R, E⟩, hr⟩ : ∃ p, m.result B = some p := Option.isSome_iff_exists.mp hc
  rw [AModule.result_of_ctx hC] at hr
  obtain ⟨PE, I, hk, -, -⟩ := resultIn_inv hr
  have hk2s : (checkTopDecOpt C m2.body).isSome := by
    have := hc2; unfold checkModule at this; rw [AModule.result_of_ctx hC2] at this
    unfold AModule.resultIn at this
    cases e : checkTopDecOpt C m2.body <;> rw [e] at this <;> simp_all
  obtain ⟨_, ν, hbij, S, hRes, _, _, hni⟩ := h1
  obtain ⟨_, ν', hbij', S', hRes', _, _, hni'⟩ := h2
  have hni1 := nodes_instance hni
  have hni2 := nodes_instance hni'
  have hν : ∀ p ∈ ν, p.1 ∉ T0 ∧ p.2 ∉ T0 := by
    intro p hp
    have e1 : p.1 ∈ genNames B m := (hbij.1 p.1).mp (List.mem_map_of_mem hp)
    have e2 : p.2 ∈ genNames B m2 := (hbij.2.1 p.2).mp (List.mem_map_of_mem hp)
    exact ⟨fun h => genNames_new e1 (hB.t0 _ h), fun h => genNames_new e2 (hB.t0 _ h)⟩
  have hν' : ∀ p ∈ ν', p.1 ∉ T0 ∧ p.2 ∉ T0 := by
    intro p hp
    have e1 : p.1 ∈ genNames B m2 := (hbij'.1 p.1).mp (List.mem_map_of_mem hp)
    have e2 : p.2 ∈ genNames B m := (hbij'.2.1 p.2).mp (List.mem_map_of_mem hp)
    exact ⟨fun h => genNames_new e1 (hB.t0 _ h), fun h => genNames_new e2 (hB.t0 _ h)⟩
  have hw := modRenaming_walkHyp hRes hRes' hni1 (fun x hx y hy e => hni2 x hx y hy e) hν
  have hw' := modRenaming_walkHyp hRes' hRes hni2 (fun x hx y hy e => hni1 x hx y hy e) hν'
  have hn1 : nodesModule B m = match m.body with | some d => nodesTopDec C [] d | none => [] := by
    unfold nodesModule; rw [hC]; cases m.body <;> rfl
  have hn3 : nodesModule B m2 = match m2.body with | some d => nodesTopDec C [] d | none => [] := by
    unfold nodesModule; rw [hC2]; cases m2.body <;> rfl
  cases hb : m.body with
  | none =>
    have hb2 : m2.body = none := by
      rw [hb] at hbody; cases e : m2.body with
      | none => rfl
      | some _ => rw [e] at hbody; cases hbody
    rw [hb] at hk
    simp only [checkTopDecOpt, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine ⟨[], [], R, Env.empty, NRInv.nil, nr_nil_basis B, by rw [AModule.result_of_ctx hC]; exact hr, ?_,
      basisInv_next hB (by rw [hb]; rfl) ⟨rfl, by simp [Env.empty], by simp⟩ hr⟩
    rw [result_transfer NRInv.nil.h (nr_nil_basis B) hC himp hhead (by rw [hb]; rfl) (by rw [hb2]; rfl),
      AModule.result_of_ctx hC, hr]
    rfl
  | some d =>
    cases hb2 : m2.body with
    | none => rw [hb, hb2] at hbody; cases hbody
    | some d2 =>
      rw [hb, hb2] at hbody
      simp only [Option.map_some, Option.some.injEq] at hbody
      have hcd : checkTopDec C d = some (E, PE) := by rw [hb] at hk; exact hk
      have hcd2 : (checkTopDec C d2).isSome := by rw [hb2] at hk2s; exact hk2s
      have ho : topTypesOrdered d.erase = true := by simpa [TypesOrdered, AModule.erase, hb] using hT
      have hG : ∀ t, t ∈ genNames B m ↔ t ∈ d.custNames ∧ t ∉ B.T := by
        intro t; unfold genNames; rw [hb]; simp
      have hni1d : ∀ n ∈ nodesTopDec C [] d, ∀ n2 ∈ nodesTopDec C [] d2, n.path = n2.path →
          NodeInstance S (n.renameNames ν) n2 := fun n hn' n2 hn2' e =>
        hni1 n (by rw [hn1, hb]; exact hn') n2 (by rw [hn3, hb2]; exact hn2') e
      have harw := Walk.arity_walk d d2 C C [] hbody (by rw [hcd]; rfl) hcd2 ho hni1d
      have har : ∀ p ∈ ν, p.2.arity = p.1.arity := fun p hp => by
        have e1 : p.1 ∈ genNames B m := (hbij.1 p.1).mp (List.mem_map_of_mem hp)
        rw [← Walk.renameName_of_mem hbij.2.2.1 hp]; exact harw p.1 ((hG p.1).mp e1).1
      obtain ⟨σ, σ', hσ, hpair, hfix⟩ :=
        Swap.extend_pairs ν hbij.2.2.1 hbij.2.2.2 har hν (B.T ++ Walk.declNames C d)
      have notG : ∀ t, t ∉ genNames B m → t ∉ ν.map (·.1) := fun t h hm => h ((hbij.1 t).mp hm)
      have notG2 : ∀ t, t ∉ genNames B m2 → t ∉ ν.map (·.2) := fun t h hm => h ((hbij.2.1 t).mp hm)
      have pν : ∀ t ∈ genNames B m, (nr σ).tnApply t = renameName ν t := by
        intro t ht
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((hbij.1 t).mpr ht)
        rw [hpair p hp, Walk.renameName_of_mem hbij.2.2.1 hp]
      have fixB : ∀ t ∈ B.T, (nr σ).tnApply t = t := fun t ht =>
        hfix t (List.mem_append_left _ ht) (notG t fun h => genNames_new h ht) (notG2 t fun h => genNames_new h ht)
      have hσB := Walk.nr_fix_basis hB fixB
      have hσC : (nr σ).ctx C = C := by
        have := nr_importCtx hσ.h B m.imports
        rw [hσB, hC] at this
        simp only [Option.map_some, Option.some.injEq] at this
        exact this.symm
      have H : Walk.Hyps (genNames B m) (genNames B m2) S S' ν ν' _ _ _ _ σ :=
        ⟨hw, hw', rfl, rfl, hσ.h, pν, hbij, hbij'⟩
      have TH : TopHyp S S' ν ν' (· ∈ modVars S (nodesModule B m) (nodesModule B m2))
          (nodesTopDec C [] d) (nodesTopDec C [] d2) := by
        refine ⟨?_, ?_, ?_⟩
        · intro n hk' n2 hm e
          exact hni1 n (by rw [hn1, hb]; exact hk') n2 (by rw [hn3, hb2]; exact hm) e
        · intro n2 hm n hk' e
          exact hni2 n2 (by rw [hn3, hb2]; exact hm) n (by rw [hn1, hb]; exact hk') e
        · intro n hk' n2 hm e τ hτ v hv hvb w hwv hwb
          exact mem_modVars.mpr ⟨⟨n, by rw [hn1, hb]; exact hk', ⟨n2, by rw [hn3, hb2]; exact hm, e.symm⟩, τ, hτ, hv⟩,
            hvb, w, hwv, hwb⟩
      have TH' : TopHyp S' S ν' ν (· ∈ modVars S' (nodesModule B m2) (nodesModule B m))
          (nodesTopDec C [] d2) (nodesTopDec C [] d) := by
        refine ⟨?_, ?_, ?_⟩
        · intro n2 hm n hk' e
          exact hni2 n2 (by rw [hn3, hb2]; exact hm) n (by rw [hn1, hb]; exact hk') e
        · intro n hk' n2 hm e
          exact hni1 n (by rw [hn1, hb]; exact hk') n2 (by rw [hn3, hb2]; exact hm) e
        · intro n2 hm n hk' e τ hτ v hv hvb w hwv hwb
          exact mem_modVars.mpr ⟨⟨n2, by rw [hn3, hb2]; exact hm, ⟨n, by rw [hn1, hb]; exact hk', e.symm⟩, τ, hτ, hv⟩,
            hvb, w, hwv, hwb⟩
      obtain ⟨kd, good⟩ := Walk.walk H (BT := B.T) d d2 C C [] E PE hbody hcd hcd2 hσC.symm hcl hU
        (fun t ht => by rw [hCT]; exact ht) (fun t ht hBT => (hG t).mpr ⟨ht, hBT⟩)
        (fun t ht e1 e2 => hfix t (List.mem_append_right _ ht) (notG t e1) (notG2 t e2)) ho
        (hn d hb) (hn2 d2 hb2) TH TH'
      refine ⟨σ, σ', R, E, hσ, hσB, by rw [AModule.result_of_ctx hC]; exact hr, ?_,
        basisInv_next hB (by rw [hb]; exact hcd) good hr⟩
      rw [result_transfer hσ.h hσB hC himp hhead (by rw [hb]; exact hcd) (by rw [hb2]; exact kd),
        AModule.result_of_ctx hC, hr]
      rfl

end MStep

/-- What the pipeline gives is the specialisation of the program (plan step 10), under D11 and the
    decidable restriction on each module's type declarations. -/
theorem ident_of_spec' {s : Src.SProgram} {q : Mod.Reduced}
    (hT : ∀ m ∈ (bareOf s).modules, TypesOrdered m)
    (hI : InferPrincipalFor Btest (bareOf s)) (h : endToEnd Btest s = .ok q) :
    ∀ r, SpecOf Btest (bareOf s) r → r = q :=
  ident_of_spec MStep.moduleStep hT hI h

end StandardElm.Stat
