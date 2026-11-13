/-
  A Standard Definition of Elm? Mechanisation: the node relation for W on F_e (milestone (e) of
  plan step 11, section 9; WDNodeRel.lean and WDNodeClos.lean for WE.lean's W).

  * `NRelE T n n'`: `NRelD` with, in place of one `U` for every node, `T` fixing the node's `U`
    (inside an annotated member `U` holds the member's explicit variables, named, so fixed by every
    substitution of the induction).
  * The schemes at a member's node: monotypes with canonical images, or annotated members'
    schemes `∀U'.τ` over named variables, which `T` fixes (`SchOK`, `schInst_fixed`).
  * The closure of an annotated member's scheme `σ` (bound variables `bnd`, every other variable
    named, so fixed by `T`), in W's context (free variables `A`) and in the derivation's (`A'`),
    where a variable of `σ` free in `A` is free in `A'`: the derivation generalises fewer of `σ`'s
    variables, so every instance of its closure is an instance of W's (`gen_rn_sub`). Hence the
    scheme clause at a declaration node (`closE_instAnn`) and the relation of the contexts of a
    `let` body (`closE_relAnnE`, `closE_relAnn` with the weaker hypothesis on `A` and `A'`).
  * The value bindings of W's result: annotated members carry W's variables and have types over
    named variables (`AnnOKV`, from the annotation marks of `tysValBind true`).
-/
import StandardElmMech.Stat.Complete.WETheorems
import StandardElmMech.Stat.Complete.WDNodeRelExp
import StandardElmMech.Stat.Complete.WSoundPost

namespace StandardElm.Stat.Complete.WE.WDP
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Stat.Complete
open StandardElm.Stat.Complete.WDP

/-! ## Instances of a closure generalising more variables -/

/-- A canonical form generalising a superset of the variables of another (on the body) has every
    instance of the other: the instance substitution of the smaller form, composed with its
    renumbering, read back through the larger form's renumbering. -/
theorem gen_rn_sub {cv0 cv1 : List BVar} {body : Ty}
    (hsub : ∀ c ∈ body.vars, c ∈ cv1 → c ∈ cv0) (hnb : ∀ c ∈ body.vars, c ∉ cv0 → c.isBnd = false) {t : Ty}
    (hg : Gen ⟨(renumber true 0 cv1).2, rsb (renumber true 0 cv1).1.toR body⟩ t) :
    Gen ⟨(renumber true 0 cv0).2, rsb (renumber true 0 cv0).1.toR body⟩ t := by
  obtain ⟨ts, S2, hb2, hr2, ha2⟩ := hg
  simp only at hb2 ha2
  have ht := apply_eq_rsb S2 _ _ ha2
  have hdef2 := defR_of_apply S2 _ _ ha2
  have hout2 : ∀ v, v ∉ (renumber true 0 cv1).2 → S2.toR.img v = vty v :=
    fun v hv => toR_img_of_not_dom fun hd => hv (bindSubst_dom hb2 v hd)
  let h : RSub := rcomp S2.toR (renumber true 0 cv1).1.toR
  have hh : RespR h := respR_rcomp (respR_toR (renumber_respectsC 0 cv1)) (respR_toR hr2)
  let f : BVar → Ty := fun b => match pickB cv0 b with
    | some v => h.img v
    | none => vty b
  have hf : ∀ e, ∃ ρ tl, f (.row e) = .record ρ tl := fun e => by
    simp only [f]; split
    · rename_i v hv
      cases v with
      | row e' => exact img_row_record h e'
      | ty a =>
        exfalso
        rcases e with (_ | _ | j) <;> simp only [pickB, reduceCtorEq] at hv
        split at hv <;> cases hv
    · exact ⟨[], some e, rfl⟩
  have hT : ∀ v, (ofImg f).img v = f v := ofImg_img hf
  obtain ⟨S3, hb3, h3img, h3ty⟩ := bindSubst_img (ofImg f) (renumber true 0 cv0).2
  have hS3fix : ∀ v, v.isBnd = false → S3.toR.img v = vty v := fun v hv => by
    rw [h3img, if_neg (bnd_not_bound hv)]
  have hagree : ∀ c ∈ body.vars, (rcomp S3.toR (renumber true 0 cv0).1.toR).img c = h.img c := by
    intro c hc
    rw [img_rcomp, renumber_img]
    split
    · rename_i hm
      rw [rsb_vty, h3img, if_pos (renumber_mem 0 cv0 c hm), hT]
      simp only [f, pickB_inst hm]
    · rename_i hm
      have hcb := hnb c hc hm
      have hm1 : c ∉ cv1 := fun h1 => hm (hsub c hc h1)
      rw [rsb_vty, hS3fix c hcb]
      simp only [h, img_rcomp]
      rw [renumber_img, if_neg hm1, rsb_vty, hout2 c (bnd_not_bound hcb)]
  have heq : rsb S3.toR (rsb (renumber true 0 cv0).1.toR body) = t := by
    rw [ht, rsb_rsb, rsb_rsb]; exact rsb_congr _ hagree
  have hdef3 : DefR S3.toR (rsb (renumber true 0 cv0).1.toR body) := by
    refine defR_rsb body (fun c _ => by rw [renumber_img]; split <;> exact defR_vty _ _) ?_
    refine RecP.mono2 (fun ρ tl h1 h2 => ?_) (recP_tails body) (recP_of_defR_rsb body hdef2)
    simp only [ImgOK, rn_tl_nil, mrg_nil_right, mok_rsbRow] at h2 ⊢
    cases tl with
    | none => exact mok_nil_right _
    | some e =>
      have he := hagree (.row e) (h1 e rfl)
      simp only [h, rcomp, RSub.rx, RSub.img, Ty.record.injEq] at he
      rw [rn_r_nil, rn_r_nil] at he
      simp only [rsbRow, mrg_nil_left] at he
      show MOK ρ (S3.toR.tl ((renumber true 0 cv0).1.toR.r e).2).1
      rw [he.1]; exact h2
  refine ⟨(renumber true 0 cv0).2.map (ofImg f).img, S3, hb3, fun p hp => ?_, ?_⟩
  · have hpd : BVar.ty p.1 ∈ (renumber true 0 cv0).2 :=
      bindSubst_dom hb3 _ (by simp only [Subst.dom, List.mem_append, List.mem_map]; exact .inl ⟨p, hp, rfl⟩)
    obtain ⟨v, -, hp', hk, hk'⟩ := pickB_bound hpd
    rw [← h3ty p hp]
    show Adm p.1.cls (f (.ty p.1))
    simp only [f, hp']
    cases v with
    | ty b =>
      obtain ⟨j, hj⟩ := hk b rfl
      injection hj with hj
      rw [hj]
      exact hh b
    | row e => obtain ⟨j, hj⟩ := hk' e rfl; cases hj
  · show S3.apply (rsb (renumber true 0 cv0).1.toR body) = some t
    rw [← heq]; exact apply_of_defR S3 _ hdef3

/-- The scheme of an annotated member: bound variables `bnd`, every `bnd` variable of the body
    bound. -/
structure AnnSch (σ : Scheme) : Prop where
  bound : ∀ v ∈ σ.bound, v.isBnd = true
  body : ∀ v ∈ σ.body.vars, v.isBnd = true → v ∈ σ.bound

theorem mem_closB_iff {A : List BVar} {VE : ValEnv} {σ : Scheme} {v : BVar} :
    v ∈ closB A VE σ ↔ v ∈ σ.bound ∨ (v ∈ σ.tyvars ∧ v ∉ A) ∨
      ((v ∈ ValEnv.tyvars VE ∧ v ∉ σ.tyvars ∧ v ∉ A) ∧ v.isNumTyVar = true) := by
  simp only [closB, List.mem_append, diffL, List.mem_filter, mem_dedupL, decide_eq_false_iff_not,
    Bool.not_eq_true', not_or, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | h)
    · exact .inl h
    · exact .inr (.inl ⟨h.1, by simpa using h.2⟩)
    · exact .inr (.inr ⟨⟨h.1.1, by simpa using h.1.2⟩, h.2⟩)
  · rintro (h | h | h)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨h.1, by simpa using h.2⟩)
    · exact .inr ⟨⟨h.1.1, by simpa using h.1.2⟩, h.2⟩

/-- The closure of an annotated member's scheme in the derivation's context generalises fewer of
    its variables than W's, when a variable free in W's context is free in the derivation's. -/
theorem gen_closE_ann {A A' : List BVar} {VE VE' : ValEnv} {σ : Scheme} (hσ : AnnSch σ)
    (hA : ∀ v ∈ σ.body.vars, v.isBnd = false → v ∈ A → v ∈ A') {t : Ty}
    (hg : Gen (closE A' VE' σ) t) : Gen (closE A VE σ) t := by
  unfold closE at hg ⊢
  rw [canon_eqD] at hg ⊢
  refine gen_rn_sub (fun c hc h1 => ?_) (fun c hc h0 => ?_) hg
  · rw [mem_canonVars_iff hc] at h1 ⊢
    rcases mem_closB_iff.mp h1 with h | ⟨h, hA'⟩ | ⟨⟨-, h, -⟩, -⟩
    · exact mem_closB_bound h
    · refine mem_closB_iff.mpr (.inr (.inl ⟨h, fun hcA => hA' (hA c hc ?_ hcA)⟩))
      exact (mem_scheme_tyvars.mp h).2.1
    · by_cases hb : c.isBnd = true
      · exact mem_closB_bound (hσ.body c hc hb)
      · exfalso; apply h
        refine mem_scheme_tyvars.mpr ⟨hc, by simpa using hb, fun hb' => hb (hσ.bound c hb')⟩
  · cases hb : c.isBnd with
    | false => rfl
    | true => exact absurd ((mem_canonVars_iff hc).mpr (mem_closB_bound (hσ.body c hc hb))) h0

/-- The variables of W's closure of an annotated member's scheme: `bnd` ones, or the scheme's own. -/
theorem closE_vars {A : List BVar} {VE : ValEnv} {σ : Scheme} {v : BVar} (hv : v ∈ (closE A VE σ).body.vars) :
    v.isBnd = true ∨ (v ∈ σ.body.vars ∧ v ∉ canonVars (closB A VE σ) σ.body) := by
  unfold closE at hv
  rw [canon_eqD] at hv
  obtain ⟨c, hc, hvc⟩ := (mem_vars_rsb _ _ v).mp hv
  rw [renumber_img] at hvc
  split at hvc
  · rw [vars_vty, List.mem_singleton] at hvc; subst hvc; exact .inl (bndV_isBnd _ _)
  · rename_i hm
    rw [vars_vty, List.mem_singleton] at hvc; subst hvc; exact .inr ⟨hc, hm⟩

theorem cnB_renumber (vs : List BVar) {τ : Ty} (h : cnB τ = true) : cnB (rsb (renumber true 0 vs).1.toR τ) = true := by
  refine cn_rsb h (fun w _ => by rw [renumber_img]; split <;> exact cnB_vty _) fun e l _ hl => ?_
  rw [rn_r_nil] at hl; cases hl

theorem cnB_closE {A : List BVar} {VE : ValEnv} {σ : Scheme} (h : cnB σ.body = true) : cnB (closE A VE σ).body = true := by
  unfold closE; rw [canon_eqD]; exact cnB_renumber _ h

/-- A scheme whose body `T` fixes, canonical, is its own instance's scheme under `T`: every
    substitution agreeing with `T` on it leaves it unchanged. -/
theorem schInst_fixed {T : RSub} {σ σ' : Scheme} (hfix : ∀ v ∈ σ.body.vars, T.img v = vty v) (hcn : cnB σ.body = true)
    (hg : ∀ t, Gen σ' t → Gen σ t) : SchInstD T σ σ' := by
  intro S hS t ht
  have he : rsb S.toR σ.body = σ.body := rsb_eq_self fun v hv => (hS v hv).trans (hfix v hv)
  refine ⟨σ, ?_, hg t ht⟩
  simp only [Subst.applyScheme, apply_of_cn S σ.body (by rw [he]; exact hcn), he, Option.map_some]

/-- The scheme clause at a declaration node for an annotated member. -/
theorem closE_instAnn {A A' : List BVar} {VE VE' : ValEnv} {σ : Scheme} {T : RSub} (hσ : AnnSch σ)
    (hbnd : ∀ v, v.isBnd = true → T.img v = vty v) (hfix : ∀ v ∈ σ.body.vars, T.img v = vty v)
    (hA : ∀ v ∈ σ.body.vars, v.isBnd = false → v ∈ A → v ∈ A') (hcn : cnB σ.body = true) :
    SchInstD T (closE A VE σ) (closE A' VE' σ) :=
  schInst_fixed (fun v hv => by
      rcases closE_vars hv with h | ⟨h, -⟩
      · exact hbnd v h
      · exact hfix v h) (cnB_closE hcn) fun _ hg => gen_closE_ann (VE := VE) hσ hA hg

/-- The relation of the contexts of a `let` body at an annotated member (`closE_relAnn` with the
    weaker hypothesis on the free variables). -/
theorem closE_relAnnE {A A' : List BVar} {VE VE' : ValEnv} {σ : Scheme} {T : RSub} (hσ : AnnSch σ)
    (hbnd : ∀ v, v.isBnd = true → T.img v = vty v) (hfix : ∀ v ∈ σ.body.vars, T.img v = vty v)
    (hA : ∀ v ∈ σ.body.vars, v.isBnd = false → v ∈ A → v ∈ A') :
    SchRelD T (closE A VE σ) (closE A' VE' σ) := by
  have hfixW : ∀ v ∈ (closE A VE σ).body.vars, T.img v = vty v := fun v hv => by
    rcases closE_vars hv with h | ⟨h, -⟩
    · exact hbnd v h
    · exact hfix v h
  refine ⟨fun w hw v hv => ?_, fun t hg => ?_⟩
  · obtain ⟨hw1, hw2, hw3⟩ := mem_scheme_tyvars.mp hw
    rw [hfixW w hw1, vty_tyvars hv] at *
    rcases closE_vars hw1 with h | ⟨hc, hm⟩
    · rw [h] at hw2; cases hw2
    · -- `w` is free in W's closure, so in `A`, so in `A'`, so free in the derivation's
      have hwA : w ∈ A := by
        rw [mem_canonVars_iff hc] at hm
        refine Classical.byContradiction fun hA' => hm (mem_closB_iff.mpr (.inr (.inl ⟨?_, hA'⟩)))
        refine mem_scheme_tyvars.mpr ⟨hc, hw2, fun hb => ?_⟩
        rw [hσ.bound w hb] at hw2; cases hw2
      have hwA' := hA w hc hw2 hwA
      have hm1 : w ∉ canonVars (closB A' VE' σ) σ.body := by
        rw [mem_canonVars_iff hc]
        exact closB_not_memAnn hwA' fun hb => by rw [hσ.bound w hb] at hw2; cases hw2
      refine mem_scheme_tyvars.mpr ⟨?_, hw2, fun hb => ?_⟩
      · unfold closE; rw [canon_eqD]
        exact (mem_vars_rsb _ _ w).mpr ⟨w, hc, by rw [renumber_img, if_neg hm1, vars_vty]; exact List.mem_singleton_self _⟩
      · unfold closE at hb; rw [canon_eqD] at hb
        exact absurd hb (bnd_not_bound hw2)
  · obtain ⟨g, hr, hout, rfl⟩ := gen_rsb (gen_closE_ann (VE := VE) hσ hA hg)
    refine ⟨g, fun a _ => hr a, rsb_congr _ fun w hw => ?_⟩
    rw [extS_img]
    split
    · rfl
    · rename_i hb; rw [hout w hb, hfixW w hw]

/-! ## Corresponding nodes -/

/-- `NRelD` with, in place of a fixed `U`, the explicit variables of the node fixed by `T`. -/
def NRelE (T : RSub) (n n' : Node) : Prop :=
  (∀ v ∈ n.U, T.img v = vty v) ∧ n'.path = n.path ∧ n'.U = n.U ∧ n'.tys = n.tys.map (rsb T) ∧
    n'.schemes.length = n.schemes.length ∧
    ∀ i (h : i < n.schemes.length) (h' : i < n'.schemes.length), SchInstD T n.schemes[i] n'.schemes[i]

theorem F2.monoE {α β : Type} {R Q : α → β → Prop} (hRQ : ∀ a b, R a b → Q a b) :
    ∀ {l : List α} {l' : List β}, F2 R l l' → F2 Q l l'
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hRQ _ _ h) (F2.monoE hRQ t)

theorem nrelE_of_D {T : RSub} {U0 : List BVar} (hU0 : ∀ v ∈ U0, T.img v = vty v) :
    ∀ n n', NRelD T U0 n n' → NRelE T n n' := fun _ _ h => ⟨by rw [h.1]; exact hU0, h.2⟩

/-- A scheme at a member's node: a monotype with a canonical image, or a canonical scheme `T`
    fixes. -/
def SchOK (T : RSub) (σ : Scheme) : Prop :=
  (σ.bound = [] ∧ cnB (rsb T σ.body) = true) ∨ ((∀ v ∈ σ.body.vars, T.img v = vty v) ∧ cnB σ.body = true)

theorem schInst_ok {T : RSub} {σ : Scheme} (h : SchOK T σ) : SchInstD T σ (rsbScheme T σ) := by
  rcases h with ⟨hb, hc⟩ | ⟨hf, hc⟩
  · exact schInst_monoCn hb hc
  · have e : rsbScheme T σ = σ := by
      obtain ⟨bd, body⟩ := σ
      simp only [rsbScheme, Scheme.mk.injEq, true_and]; exact rsb_eq_self hf
    rw [e]; exact schInst_fixed hf hc fun _ h => h

theorem schOK_nil (T : RSub) : ∀ σ ∈ ([] : List Scheme), SchOK T σ := fun _ h => nomatch h

theorem nrelE_mk {T : RSub} {U U' : List BVar} {path : List Nat} {tys tys' : List Ty} {ss ss' : List Scheme}
    (hU : ∀ v ∈ U, T.img v = vty v) (hU' : U' = U) (h1 : tys' = tys.map (rsb T)) (h2 : ss' = ss.map (rsbScheme T))
    (hss : ∀ σ ∈ ss, SchOK T σ) : NRelE T ⟨path, U, tys, ss⟩ ⟨path, U', tys', ss'⟩ := by
  subst hU' h1 h2
  refine ⟨hU, rfl, rfl, rfl, by simp, fun i h h' => ?_⟩
  simp only [List.getElem_map]
  exact schInst_ok (hss _ (List.getElem_mem h))

theorem nodesAtPat_relE (T : RSub) {U U' : List BVar} (hU : ∀ v ∈ U, T.img v = vty v) (hU' : U' = U) (p : AAtPat)
    (path : List Nat) (hcn : CnT T (tysAtPat p)) :
    F2 (NRelE T) (nodesAtPat U path (stripAtPat p)) (nodesAtPat U' path (stripAtPat (rsbAtPat T p))) :=
  F2.monoE (nrelE_of_D hU) (nodesAtPat_relD' T rfl hU' p path hcn)

theorem nodesPat_relE (T : RSub) {U U' : List BVar} (hU : ∀ v ∈ U, T.img v = vty v) (hU' : U' = U) (p : APat)
    (path : List Nat) (hcn : CnT T (tysPat p)) :
    F2 (NRelE T) (nodesPat U path (stripPat p)) (nodesPat U' path (stripPat (rsbPat T p))) :=
  F2.monoE (nrelE_of_D hU) (nodesPat_relD' T rfl hU' p path hcn)

theorem schOK_of_monoCn {T : RSub} {ss : List Scheme} (h : MonoCn T ss) : ∀ σ ∈ ss, SchOK T σ :=
  fun σ hσ => .inl (h σ hσ)

/-! ## Contexts -/

/-- The explicit variables of related contexts are fixed. -/
theorem uFix {n0 : Nat} {T : RSub} {C C' : Ctx} (hfx : FixR (rigidFromD n0) T)
    (hrel : CtxRelD (SchRelD T) (rigidFromD n0) C C') : ∀ v ∈ C.U, T.img v = vty v :=
  fun v hv => hfx v (hrel.2.2.2.2.2 v (by simp [restTv, hv]))

theorem named_rigid {n0 : Nat} {v : BVar} (h : v.isNamed = true) : rigidFromD n0 v = true := by
  rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isNamed, rigidFromD]

/-- An annotated member's body: both contexts with the member's explicit variables added. -/
theorem CtxRelD.plusUE {P : Scheme → Scheme → Prop} {n0 : Nat} {C C' : Ctx}
    (h : CtxRelD P (rigidFromD n0) C C') {U' : List BVar} (hU' : ∀ v ∈ U', v.isNamed = true) :
    CtxRelD P (rigidFromD n0) (C.plusU U') (C'.plusU U') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, by simp [Ctx.plusU, h2], h3, h4, h5, fun v hv => ?_⟩
  simp only [restTv, Ctx.plusU, List.mem_append, unionL, diffL, List.mem_filter] at hv
  rcases hv with (h | h) | (h | ⟨h, -⟩)
  · exact h6 v (by simp [restTv, h])
  · exact h6 v (by simp [restTv, h])
  · exact h6 v (by simp [restTv, h])
  · exact named_rigid (hU' v h)

/-! ## Value bindings -/

/-- The annotated members of a chain of W's result carry W's explicit variables, and their types
    are over named variables. -/
def AnnOKV : AValBind → Prop
  | .var _ ann τ _ rest => canonAnnB ann = true ∧ (ann.isSome = true → ∀ v ∈ τ.vars, v.isNamed = true) ∧
      (match rest with
       | none => True
       | some vb => AnnOKV vb)
  | .pat _ _ => True

theorem annOKV_of_okAD {n : Nat} : ∀ vb : AValBind, OkAD n (tysValBind true vb) → AnnOKV vb
  | .var _ ann τ _ rest, h => by
    simp only [tysValBind, List.cons_append] at h
    have hm : ∀ t ∈ annMark true ann τ, OkTD n t := fun t ht => h t (by simp [ht])
    unfold AnnOKV
    refine ⟨canon_of_okAD hm, named_of_okAD hm, ?_⟩
    cases rest with
    | none => trivial
    | some vb => exact annOKV_of_okAD vb fun t ht => h t (by simp [tysValBindOpt, ht])
  | .pat _ _, _ => trivial

theorem annOKV_rsb {n0 : Nat} {T : RSub} (hfx : FixR (rigidFromD n0) T) :
    ∀ vb : AValBind, AnnOKV vb → AnnOKV (rsbValBind T vb)
  | .var _ ann τ _ rest, h => by
    unfold AnnOKV at h
    simp only [rsbValBind]
    unfold AnnOKV
    refine ⟨h.1, fun hs => ?_, ?_⟩
    · rw [rsb_named hfx (h.2.1 hs)]; exact h.2.1 hs
    · cases rest with
      | none => trivial
      | some vb => exact annOKV_rsb hfx vb h.2.2
  | .pat _ _, _ => trivial

theorem valbind_ve_rsbE {n0 : Nat} {T : RSub} (hfx : FixR (rigidFromD n0) T) :
    ∀ vb : AValBind, AnnOKV vb → (rsbValBind T vb).ve = rsbVE T vb.ve
  | .var x ann τ e rest, h => by
    unfold AnnOKV at h
    simp only [rsbValBind]
    unfold AValBind.ve
    rw [rsbVE_modifyD]
    congr 1
    · by_cases hs : ann.isSome = true
      · simp only [hs, ↓reduceIte, rsbVE, List.map_cons, List.map_nil]
        rw [rsb_named hfx (h.2.1 hs), rsbScheme_ann hfx (h.2.1 hs)]
      · simp [hs, rsbVE, rsbScheme, mono]
    · cases rest with
      | none => rfl
      | some vb => exact valbind_ve_rsbE hfx vb h.2.2
  | .pat p e, _ => by simp only [rsbValBind, AValBind.ve, rsbAtPat_veD]

/-- An entry of an annotated member: its scheme, over a type of the list with named variables. -/
def AEnt (l : List Ty) (q : String × (Scheme × IdStatus)) : Prop :=
  q.2.2 = .v ∧ ∃ U' τ, q.2.1 = annScheme U' τ ∧ τ ∈ l ∧ ∀ v ∈ τ.vars, v.isNamed = true

theorem valbind_ve_entE (w : Bool) : ∀ vb : AValBind, AnnOKV vb →
    ∀ q ∈ vb.ve, PEnt (tysValBind w vb) q ∨ AEnt (tysValBind w vb) q
  | .var x ann τ e rest, h, q, hq => by
    unfold AnnOKV at h
    unfold AValBind.ve at hq
    rcases mem_modify hq with hq | hq
    · simp only [List.mem_singleton] at hq; subst hq
      by_cases hs : ann.isSome = true
      · exact .inr ⟨rfl, annU ann, τ, by simp [hs], by simp [tysValBind], h.2.1 hs⟩
      · refine .inl ⟨by simp [hs, mono], rfl, fun v hv => ⟨τ, by simp [tysValBind], by simpa [hs, mono] using hv⟩⟩
    · cases rest with
      | none => cases hq
      | some vb =>
        rcases valbind_ve_entE w vb h.2.2 q hq with h' | h'
        · exact .inl (PEnt.mono (fun t ht => by simp [tysValBind, tysValBindOpt, ht]) h')
        · obtain ⟨h1, U', τ', h2, h3, h4⟩ := h'
          exact .inr ⟨h1, U', τ', h2, by simp [tysValBind, tysValBindOpt, h3], h4⟩
  | .pat p e, _, q, hq => by
    simp only [AValBind.ve] at hq
    exact .inl (PEnt.mono (fun t ht => by simp [tysValBind, ht]) (atpat_ve p q hq))

theorem annSch_ann {U' : List BVar} {τ : Ty} (hτ : ∀ v ∈ τ.vars, v.isNamed = true) : AnnSch (annScheme U' τ) :=
  ⟨annScheme_bound, fun v hv hb => by
    rcases annScheme_vars v hv with h | h
    · exact h.2
    · have := hτ v h
      rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isNamed, BVar.isBnd]⟩

theorem fix_annScheme {n0 : Nat} {T : RSub} (hfx : FixR (rigidFromD n0) T) {U' : List BVar} {τ : Ty}
    (hτ : ∀ v ∈ τ.vars, v.isNamed = true) : ∀ v ∈ (annScheme U' τ).body.vars, T.img v = vty v :=
  fun v hv => img_BN hfx (annScheme_BN hτ v hv)

theorem cnB_annScheme {U' : List BVar} {τ : Ty} (h : cnB τ = true) : cnB (annScheme U' τ).body = true := by
  rw [annScheme_eq]; exact cnB_renumber _ h

theorem nb_annScheme {U' : List BVar} {τ : Ty} (hτ : ∀ v ∈ τ.vars, v.isNamed = true) :
    ∀ v ∈ (annScheme U' τ).body.vars, v.isBnd = false → v.isNamed = true := fun v hv hb => by
  rcases annScheme_vars v hv with h | h
  · rw [h.1] at hb; cases hb
  · exact hτ v h

end StandardElm.Stat.Complete.WE.WDP
