/-
  A Standard Definition of Elm? Mechanisation: the scheme clause of the instance relation for W
  with records (plan step 11, milestone (d), section 7 with L3).

  `SchInstD T σ σ'`: for every step 9 substitution `S` agreeing with `T` on the variables of `σ`'s
  body, `S σ` is defined and every instance of `σ'` is an instance of `S σ`. It holds

  * for monotypes with a canonical image (`schInst_mono`), and
  * at a declaration node (`closE_instD`): `σ` is W's closure of a member's type `τ`, `σ'` the
    derivation's closure of `T τ` (canonical). An instance `t` of `σ'` is `S2 (RN1 (T τ))` for a
    step 9 substitution `S2` of `σ'`'s bound variables, defined there; `t` is `S3 (S σ)` for the
    substitution `S3` of `σ`'s bound variables to their images under `S2 ∘ RN1 ∘ T`, and `S3` is
    defined on `S σ`: at a record `⟨ρ | ε⟩` of `τ` with `ε` generalised, the merge of `ρ` with the
    row of `S3 ε` (the row of `T ε`, then the instance's row) is the merge of `ρ ∪ T ε` with the
    instance's row, reassociated (`mok_assoc`, `ρ` and `T ε` disjoint as `T τ` is canonical).
-/
import StandardElmMech.Stat.Complete.WDNodeDef
import StandardElmMech.Stat.Complete.WDClosure

namespace StandardElm.Stat.Complete.WDP
open StandardElm (Lab)
open StandardElm.Stat
open StandardElm.Stat.Complete

/-- The scheme clause of an instance, for every step 9 substitution agreeing with `T` on `σ`. -/
def SchInstD (T : RSub) (σ σ' : Scheme) : Prop :=
  ∀ S : Subst, (∀ v ∈ σ.body.vars, S.toR.img v = T.img v) →
    ∀ t, Gen σ' t → ∃ σS, S.applyScheme σ = some σS ∧ Gen σS t

theorem toR_id : Subst.id.toR = rid := RSub.eq_of (fun _ => rfl) (fun _ => rfl)

theorem rsb_toR_congr {S : Subst} {T : RSub} {τ : Ty} (h : ∀ v ∈ τ.vars, S.toR.img v = T.img v) :
    rsb S.toR τ = rsb T τ := rsb_congr τ h

/-- A canonical image is an instance of its monotype (by the empty substitution). -/
theorem gen_mono_self {τ : Ty} (h : cnB τ = true) : Gen (mono τ) τ := by
  refine ⟨[], Subst.id, rfl, fun p hp => by simp [Subst.id] at hp, ?_⟩
  have := apply_of_cn Subst.id τ (by rw [toR_id, rsb_rid]; exact h)
  rw [toR_id, rsb_rid] at this; exact this

theorem schInst_mono {T : RSub} {τ : Ty} (hcn : cnB (rsb T τ) = true) : SchInstD T (mono τ) (mono (rsb T τ)) := by
  intro S hS t hg
  obtain ⟨ts, S', hb, -, ha⟩ := hg
  have hS' : S' = Subst.id := by
    cases ts with
    | nil => simp only [mono, bindSubst, Option.some.injEq] at hb; exact hb.symm
    | cons _ _ => simp [mono, bindSubst] at hb
  subst hS'
  have ht := apply_eq_rsb _ _ _ ha
  rw [toR_id, rsb_rid] at ht; subst ht
  have he : rsb S.toR τ = rsb T τ := rsb_toR_congr hS
  refine ⟨mono (rsb T τ), ?_, gen_mono_self hcn⟩
  simp only [Subst.applyScheme, mono_body, apply_of_cn S τ (by rw [he]; exact hcn), he]
  rfl

/-! ## Renumberings move row variables to row variables -/

theorem img_row_inj {s t : RSub} {e e' : RowVar} (h : s.img (.row e) = t.img (.row e')) : s.r e = t.r e' := by
  simp only [RSub.img, Ty.record.injEq] at h; exact Prod.ext h.1 h.2

theorem rn_r_mem {cv : List BVar} {e : RowVar} (hm : BVar.row e ∈ cv) :
    (renumber true 0 cv).1.toR.r e = ([], some (.bnd (0 + cv.idxOf (.row e)))) := by
  have := renumber_img 0 cv (.row e)
  rw [if_pos hm] at this
  exact img_row_inj (e' := e) (t := ⟨fun _ => .var (.bnd 0 .any), fun _ => ([], some (.bnd (0 + cv.idxOf (.row e))))⟩) this

theorem rn_r_not {cv : List BVar} {e : RowVar} (hm : BVar.row e ∉ cv) :
    (renumber true 0 cv).1.toR.r e = ([], some e) := by
  have := renumber_img 0 cv (.row e)
  rw [if_neg hm] at this
  exact img_row_inj (t := rid) this

theorem rn_r_nil (cv : List BVar) (e : RowVar) : ((renumber true 0 cv).1.toR.r e).1 = [] := by
  by_cases hm : BVar.row e ∈ cv
  · rw [rn_r_mem hm]
  · rw [rn_r_not hm]

theorem rn_tl_nil (cv : List BVar) (tl : Option RowVar) : ((renumber true 0 cv).1.toR.tl tl).1 = [] := by
  cases tl with
  | none => rfl
  | some e => exact rn_r_nil cv e

theorem labs_ldisj {a b a' b' : Row} (ha : labs a = labs a') (hb : labs b = labs b') (h : LDisj a b) : LDisj a' b' := by
  intro x hx y hy e
  obtain ⟨u, hu⟩ := mem_labs.mp (show x.1 ∈ labs a by rw [ha]; exact mem_labs.mpr ⟨x.2, hx⟩)
  obtain ⟨u', hu'⟩ := mem_labs.mp (show y.1 ∈ labs b by rw [hb]; exact mem_labs.mpr ⟨y.2, hy⟩)
  exact h _ hu _ hu' e

theorem bnd_not_bound {cv : List BVar} {v : BVar} (hv : v.isBnd = false) : v ∉ (renumber true 0 cv).2 := by
  intro h
  obtain ⟨j, hj, hx⟩ := renumber_bound 0 cv v h
  rw [hx, bndV_isBnd] at hv; cases hv

/-! ## The closure clause -/

/-- L3 for the instance relation: at a declaration node, the scheme clause between W's closure of
    a member's type and the derivation's closure of its image. -/
theorem closE_instD {A A' : List BVar} {VE VE' : ValEnv} {τ : Ty} {T : RSub} {n : Nat}
    (hτ : OkTD n τ) (hTadm : RespR T) (hbnd : ∀ v, v.isBnd = true → T.img v = vty v)
    (hA : ∀ w ∈ A, w ∈ τ.vars → ∀ v ∈ (T.img w).tyvars, v ∈ A')
    (hNB : ∀ v ∈ (rsb T τ).vars, v.isBnd = false) (hcn : cnB (rsb T τ) = true) :
    SchInstD T (closE A VE (mono τ)) (closE A' VE' (mono (rsb T τ))) := by
  unfold closE
  simp only [mono_body]
  rw [canon_eqD, canon_eqD]
  generalize hcv0 : canonVars (closB A VE (mono τ)) τ = cv0
  generalize hcv1 : canonVars (closB A' VE' (mono (rsb T τ))) (rsb T τ) = cv1
  have hR0 := renumber_img 0 cv0
  have hR1 := renumber_img 0 cv1
  have hfix : ∀ c ∈ τ.vars, c ∈ A → ∀ v ∈ (T.img c).vars, v ∉ cv1 ∧ v.isBnd = false := by
    intro c hc hcA v hv
    have hnb : v.isBnd = false := hNB v ((mem_vars_rsb T τ v).mpr ⟨c, hc, hv⟩)
    have hA'v : v ∈ A' := hA c hcA hc v (mem_tyvars_iff.mpr ⟨hv, hnb⟩)
    refine ⟨fun hm => ?_, hnb⟩
    rw [← hcv1] at hm
    exact closB_not_mem hA'v (mem_canonVars hm)
  have inA : ∀ c ∈ τ.vars, c ∉ cv0 → c ∈ A := fun c hc hn =>
    inA_of hc (hτ c hc).1 (by rw [hcv0]; exact hn)
  intro S hS t hg
  simp only at hS
  obtain ⟨ts, S2, hb2, hr2, ha2⟩ := hg
  simp only at hb2 ha2
  have ht := apply_eq_rsb S2 _ _ ha2
  have hdef2 := defR_of_apply S2 _ _ ha2
  rw [rsb_rsb] at ht hdef2
  rw [rsb_rsb, ← rcomp_assoc] at ht
  have hout2 : ∀ v, v ∉ (renumber true 0 cv1).2 → S2.toR.img v = vty v :=
    fun v hv => toR_img_of_not_dom fun hd => hv (bindSubst_dom hb2 v hd)
  let h : RSub := rcomp S2.toR (rcomp (renumber true 0 cv1).1.toR T)
  have hh : RespR h := respR_rcomp (respR_rcomp hTadm (respR_toR (renumber_respectsC 0 cv1)))
    (respR_toR hr2)
  have hpost : ∀ c ∈ τ.vars, c ∈ A → h.img c = T.img c := by
    intro c hc hcA
    simp only [h, img_rcomp]
    rw [rsb_eq_self (s := (renumber true 0 cv1).1.toR) fun v hv => by rw [hR1, if_neg (hfix c hc hcA v hv).1]]
    exact rsb_eq_self fun v hv => hout2 v (bnd_not_bound (hfix c hc hcA v hv).2)
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
  -- the image of `τ` under `S ∘ (renumber true 0 cv0).1.toR`
  let w : RSub := rcomp S.toR (renumber true 0 cv0).1.toR
  have hmem : ∀ c ∈ τ.vars, ∀ x ∈ ((renumber true 0 cv0).1.toR.img c).vars, x ∈ (rsb (renumber true 0 cv0).1.toR τ).vars := fun c hc x hx =>
    (mem_vars_rsb (renumber true 0 cv0).1.toR τ x).mpr ⟨c, hc, hx⟩
  have hw : ∀ c ∈ τ.vars, w.img c = if c ∈ cv0 then vty (bndV (0 + cv0.idxOf c) c) else T.img c := by
    intro c hc
    simp only [w, img_rcomp]
    have hm := hmem c hc
    rw [hR0] at hm ⊢
    by_cases hc0 : c ∈ cv0
    · rw [if_pos hc0] at hm ⊢
      rw [if_pos hc0, rsb_vty, hS _ (hm _ (by simp [vars_vty])), hbnd _ (bndV_isBnd _ _)]
    · rw [if_neg hc0] at hm ⊢
      rw [if_neg hc0, rsb_vty, hS _ (hm _ (by simp [vars_vty]))]
  have hbody : rsb S.toR (rsb (renumber true 0 cv0).1.toR τ) = rsb w τ := rsb_rsb _ _ τ
  have htails := recP_tails τ
  have hcnP := recP_of_cn τ hcn
  -- (a) `S` is defined on W's closure
  have hdefS : DefR S.toR (rsb (renumber true 0 cv0).1.toR τ) := by
    refine defR_rsb τ (fun c _ => by rw [hR0]; split <;> exact defR_vty _ _) ?_
    refine RecP.mono2 (fun ρ tl h1 h2 => ?_) htails hcnP
    show MOK _ _
    cases tl with
    | none => exact mok_nil_right _
    | some e =>
      have he := h1 e rfl
      simp only [RSub.tl]
      by_cases hm : BVar.row e ∈ cv0
      · have := rn_r_mem hm
        rw [this]
        have hb := hS (.row (.bnd (0 + cv0.idxOf (.row e)))) (hmem _ he _ (by rw [hR0, if_pos hm]; simp [vty, bndV, Ty.vars]))
        rw [hbnd _ rfl] at hb
        simp only [RSub.tl, img_row_inj (t := rid) hb, rid, mrg_nil_right]
        exact mok_nil_right _
      · have := rn_r_not hm
        rw [this]
        have hb := hS (.row e) (hmem _ he _ (by rw [hR0, if_neg hm]; simp [vty, Ty.vars]))
        simp only [RSub.tl, img_row_inj hb, mrg_nil_right]
        exact mok_of_ldisj _ _ (labs_ldisj (by rw [labs_rsbRow, labs_rsbRow]) rfl h2)
  have happ : S.apply (rsb (renumber true 0 cv0).1.toR τ) = some (rsb S.toR (rsb (renumber true 0 cv0).1.toR τ)) := apply_of_defR S _ hdefS
  refine ⟨⟨(renumber true 0 cv0).2, rsb S.toR (rsb (renumber true 0 cv0).1.toR τ)⟩,
    by simp only [Subst.applyScheme, happ, Option.map_some], ?_⟩
  -- (b) the instance
  have hS3fix : ∀ v, v.isBnd = false → S3.toR.img v = vty v := fun v hv => by
    rw [h3img, if_neg (bnd_not_bound hv)]
  have hS3r : ∀ e, BVar.isBnd (.row e) = false → (S3.toR.r e) = ([], some e) := fun e he =>
    img_row_inj (t := rid) (hS3fix _ he)
  have heq : rsb S3.toR (rsb w τ) = t := by
    rw [rsb_rsb, ht]
    apply rsb_congr
    intro c hc
    rw [img_rcomp, hw c hc]
    split
    · rename_i hm
      rw [rsb_vty, h3img, if_pos (renumber_mem 0 cv0 c hm), hT]
      simp only [f, pickB_inst hm, h]
    · rename_i hm
      rw [rsb_eq_self fun v hv => hS3fix v (hNB v ((mem_vars_rsb T τ v).mpr ⟨c, hc, hv⟩))]
      exact (hpost c hc (inA c hc hm)).symm
  have hdef3 : DefR S3.toR (rsb w τ) := by
    refine defR_rsb τ (fun c hc => ?_) ?_
    · rw [hw c hc]
      split
      · exact defR_vty _ _
      · exact defR_of_tails _ fun e he => by
          rw [hS3r e (hNB _ ((mem_vars_rsb T τ _).mpr ⟨c, hc, he⟩))]
    · have h2 := recP_of_defR_rsb τ hdef2
      refine RecP.mono2 (fun ρ tl h1 h2 => ?_) (RecP.mono2 (fun ρ tl h1 h2 => And.intro h1 h2) htails hcnP) h2
      obtain ⟨h1, hc1⟩ := h1
      show MOK _ _
      cases tl with
      | none => exact mok_nil_right _
      | some e =>
        have he := h1 e rfl
        have hwe := hw (.row e) he
        simp only [RSub.tl]
        by_cases hm : BVar.row e ∈ cv0
        · rw [if_pos hm] at hwe
          have hwr : w.r e = ([], some (.bnd (0 + cv0.idxOf (.row e)))) :=
            img_row_inj (e' := e) (t := ⟨fun _ => .var (.bnd 0 .any), fun _ => ([], some (.bnd (0 + cv0.idxOf (.row e))))⟩) hwe
          rw [hwr]
          have h3 : S3.toR.r (.bnd (0 + cv0.idxOf (.row e))) = h.r e := by
            have := h3img (bndV (0 + cv0.idxOf (.row e)) (.row e))
            rw [if_pos (renumber_mem 0 cv0 _ hm), hT] at this
            simp only [f, pickB_inst hm] at this
            exact img_row_inj this
          simp only [RSub.tl, h3, mrg_nil_right]
          -- the derivation's merge, reassociated
          have h2' : MOK (mrg (rsbRow (rcomp (renumber true 0 cv1).1.toR T) ρ) ((rcomp (renumber true 0 cv1).1.toR T).r e).1) (S2.toR.tl ((rcomp (renumber true 0 cv1).1.toR T).r e).2).1 := h2
          have hY : ((rcomp (renumber true 0 cv1).1.toR T).r e).1 = rsbRow (renumber true 0 cv1).1.toR (T.r e).1 := by
            simp only [rcomp, RSub.rx]
            rw [rn_tl_nil, mrg_nil_right]
          have hd : LDisj (rsbRow (rcomp (renumber true 0 cv1).1.toR T) ρ) ((rcomp (renumber true 0 cv1).1.toR T).r e).1 := by
            rw [hY]
            exact labs_ldisj (by rw [labs_rsbRow, labs_rsbRow]) (by rw [labs_rsbRow]; rfl) hc1
          have := mok_assoc _ _ _ h2' hd
          simp only [h, rcomp, RSub.rx] at this ⊢
          refine mok_congr _ _ _ _ (by rw [labs_rsbRow, labs_rsbRow]) ?_ this
          exact labs_mrg_congr _ _ _ _ (by rw [labs_rsbRow]) rfl
        · rw [if_neg hm] at hwe
          rw [img_row_inj hwe]
          have hTe : ∀ e', (T.r e).2 = some e' → BVar.isBnd (.row e') = false := fun e' he' =>
            hNB _ ((mem_vars_rsb T τ _).mpr ⟨.row e, he, by simp [RSub.img, he', Ty.vars]⟩)
          cases htl : (T.r e).2 with
          | none => exact mok_nil_right _
          | some e' => simp only [RSub.tl, hS3r e' (hTe e' htl)]; exact mok_nil_right _
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
  · show S3.apply (rsb S.toR (rsb (renumber true 0 cv0).1.toR τ)) = some t
    rw [hbody, ← heq]
    exact apply_of_defR S3 _ hdef3

end StandardElm.Stat.Complete.WDP
