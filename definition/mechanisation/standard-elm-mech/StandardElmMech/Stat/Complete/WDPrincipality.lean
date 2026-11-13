/-
  A Standard Definition of Elm? Mechanisation: principality of W with records and rows (plan
  step 11, milestone (d), section 7 and L12): `wdPrincipality : WDPrincipality`.

  From L12 (`wdExp_root`, WDTheorems.lean) every canonical derivation `a'` without free `bnd`
  variables is `T x` with the instance lists left out, where `x = θ ar` is W's result and `T` fixes
  the root context's variables. The nodes of `x` and of `T x` correspond one to one, in order
  (`nodesExp_relD`, WDNodeRelExp.lean); the paths are distinct (`nodesExp_pd`, WPrincipality.lean),
  so nodes with the same path correspond (`f2_pickD`). The instance substitution of
  sec:static-core-principal is `T` restricted to the variables at the nodes of `x` (`mkS`, a step 9
  substitution with type and row bindings): it respects classes, moves no variable of the root
  context, is defined on the nodes' types (their images are the canonical types of `a'`,
  `apply_of_cn`), and maps each node of `x` to the corresponding node of `a'`; at the schemes, by
  the scheme clause (`SchInstD`, WDNodeClos.lean).

  `isPrincipalD_iff` and `inferExpWD_principal`: W's result is principal in step 9's sense
  (`InstanceOf`, nodes without instance lists) among the canonical derivations without free `bnd`
  variables.
-/
import StandardElmMech.Stat.Complete.WDNodeOk

namespace StandardElm.Stat.Complete.WDP
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Stat.Complete

/-! ## Corresponding nodes -/

theorem f2_mem_left {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} (h : F2 R l l') :
    ∀ x ∈ l, ∃ y ∈ l', R x y := by
  induction h with
  | nil => intro x hx; cases hx
  | cons hab _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, .head _, hab⟩
    · obtain ⟨y, hy, hr⟩ := ih x hx; exact ⟨y, .tail _ hy, hr⟩

/-- With distinct paths, nodes of the two lists with the same path are corresponding nodes. -/
theorem f2_pickD {T : RSub} {U0 : List BVar} {l l' : List Node} (h : F2 (NRelD T U0) l l') (hpd : PD l) :
    ∀ n ∈ l, ∀ n' ∈ l', n.path = n'.path → NRelD T U0 n n' := by
  induction h with
  | nil => intro n hn; cases hn
  | @cons a b l l' hab hrest ih =>
    unfold PD at hpd
    simp only [List.map_cons, List.nodup_cons] at hpd
    intro n hn n' hn' e
    rcases List.mem_cons.mp hn with rfl | hn <;> rcases List.mem_cons.mp hn' with rfl | hn'
    · exact hab
    · obtain ⟨m, hm, hr⟩ := f2_mem_right hrest n' hn'
      exact absurd (List.mem_map.mpr ⟨m, hm, (e.trans hr.2.1).symm⟩) hpd.1
    · exact absurd (List.mem_map.mpr ⟨n, hn, e.trans hab.2.1⟩) hpd.1
    · exact ih hpd.2 n hn n' hn' e

/-! ## The instance substitution -/

/-- `T` restricted to the variables of a list it moves, as a step 9 substitution. -/
def mkS (T : RSub) : List BVar → Subst
  | [] => Subst.id
  | .ty a :: L => if T.t a = .var a then mkS T L else { mkS T L with ty := (a, T.t a) :: (mkS T L).ty }
  | .row e :: L => if T.r e = ([], some e) then mkS T L else { mkS T L with row := (e, T.r e) :: (mkS T L).row }

theorem img_mkS (T : RSub) : ∀ (L : List BVar) (v : BVar), (mkS T L).toR.img v = if v ∈ L then T.img v else vty v
  | [], v => by simp only [mkS, toR_id, img_rid, List.not_mem_nil, if_false]
  | .ty a :: L, v => by
    have ih := img_mkS T L v
    by_cases hT : T.t a = .var a
    · simp only [mkS, hT, if_true]
      rw [ih]
      by_cases hv : v = .ty a
      · subst hv
        simp only [List.mem_cons, true_or, if_true]
        split <;> simp [RSub.img, hT, vty]
      · simp [hv]
    · simp only [mkS, hT, if_false]
      by_cases hv : v = .ty a
      · subst hv; simp [RSub.img, Subst.toR, FMap.find?]
      · have hS : (Subst.toR { mkS T L with ty := (a, T.t a) :: (mkS T L).ty }).img v = (mkS T L).toR.img v := by
          cases v with
          | ty b =>
            have : b ≠ a := fun h => hv (by rw [h])
            simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
          | row _ => rfl
        rw [hS, ih]; simp [hv]
  | .row e :: L, v => by
    have ih := img_mkS T L v
    by_cases hT : T.r e = ([], some e)
    · simp only [mkS, hT, if_true]
      rw [ih]
      by_cases hv : v = .row e
      · subst hv
        simp only [List.mem_cons, true_or, if_true]
        split <;> simp [RSub.img, hT, vty]
      · simp [hv]
    · simp only [mkS, hT, if_false]
      by_cases hv : v = .row e
      · subst hv; simp [RSub.img, Subst.toR, FMap.find?]
      · have hS : (Subst.toR { mkS T L with row := (e, T.r e) :: (mkS T L).row }).img v = (mkS T L).toR.img v := by
          cases v with
          | row b =>
            have : b ≠ e := fun h => hv (by rw [h])
            simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
          | ty _ => rfl
        rw [hS, ih]; simp [hv]

theorem resp_mkS {T : RSub} (hT : RespR T) : ∀ L : List BVar, (mkS T L).Respects
  | [] => fun p hp => by simp [mkS, Subst.id] at hp
  | .ty a :: L => by
    simp only [mkS]
    split
    · exact resp_mkS hT L
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hT a
      · exact resp_mkS hT L p hp
  | .row e :: L => by
    simp only [mkS]
    split
    · exact resp_mkS hT L
    · exact resp_mkS hT L

theorem dom_mkS (T : RSub) : ∀ (L : List BVar), ∀ v ∈ (mkS T L).dom, T.img v ≠ vty v
  | [] => fun v hv => by simp [mkS, Subst.id, Subst.dom] at hv
  | .ty a :: L => by
    simp only [mkS]
    split
    · exact dom_mkS T L
    · rename_i hT
      intro v hv
      simp only [Subst.dom, List.map_cons, List.cons_append, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hT
      · exact dom_mkS T L v (by simpa [Subst.dom] using hv)
  | .row e :: L => by
    simp only [mkS]
    split
    · exact dom_mkS T L
    · rename_i hT
      intro v hv
      simp only [Subst.dom, List.map_cons, List.mem_append, List.mem_cons] at hv
      rcases hv with hv | rfl | hv
      · exact dom_mkS T L v (by simp [Subst.dom, hv])
      · intro h
        simp only [RSub.img, vty, Ty.record.injEq] at h
        exact hT (Prod.ext h.1 h.2)
      · exact dom_mkS T L v (by simp [Subst.dom, hv])

/-- A variable a step 9 substitution fixes is taken to itself. -/
theorem applyVar_of_fix {S : Subst} {v : BVar} (h : S.toR.img v = vty v) : S.applyVar v = some v := by
  have := apply_of_defR S (vty v) (defR_vty _ v)
  rw [rsb_vty, h] at this
  cases v with
  | ty a => simp only [Subst.applyVar, show Ty.var a = vty (.ty a) from rfl, this]; rfl
  | row e => simp only [Subst.applyVar, show Ty.record [] (some e) = vty (.row e) from rfl, this]; rfl

/-- The node-wise correspondence with distinct paths is an instance (step 9's `InstanceNodes`), for
    a class-respecting `T` fixing the free variables of the root context, whose images of the
    nodes' types are canonical. -/
theorem instanceNodes_of_F2D {T : RSub} {U0 A0 : List BVar} {ns ns' : List Node}
    (hF : F2 (NRelD T U0) ns ns') (hpd : PD ns) (hcls : RespR T)
    (hA0 : ∀ v ∈ A0, T.img v = vty v) (hU0 : ∀ v ∈ U0, T.img v = vty v)
    (hcn : ∀ n ∈ ns, ∀ τ ∈ n.tys, cnB (rsb T τ) = true) : InstanceNodes A0 ns' ns := by
  let L : List BVar := (ns.flatMap fun n => n.tys ++ n.schemes.map (·.body)).flatMap Ty.vars
  let S := mkS T L
  have hagree : ∀ n ∈ ns, ∀ τ, (τ ∈ n.tys ∨ τ ∈ n.schemes.map (·.body)) → ∀ v ∈ τ.vars, S.toR.img v = T.img v := by
    intro n hn τ hτ v hv
    rw [img_mkS, if_pos (List.mem_flatMap.mpr ⟨τ, List.mem_flatMap.mpr ⟨n, hn, List.mem_append.mpr hτ⟩, hv⟩)]
  have happ : ∀ n ∈ ns, ∀ τ ∈ n.tys, S.apply τ = some (rsb T τ) := by
    intro n hn τ hτ
    have he : rsb S.toR τ = rsb T τ := rsb_congr τ (hagree n hn τ (.inl hτ))
    rw [← he]; exact apply_of_cn S τ (by rw [he]; exact hcn n hn τ hτ)
  refine ⟨S, resp_mkS hcls L, fun v hv hvA => dom_mkS T L v hv (hA0 v hvA), fun τ hτ => ?_, fun n hn n' hn' hp => ?_⟩
  · obtain ⟨n, hn, hτ⟩ := List.mem_flatMap.mp hτ
    rw [happ n hn τ hτ]; rfl
  · obtain ⟨hU, -, hU', htys, hlen, hsch⟩ := f2_pickD hF hpd n hn n' hn' hp
    refine ⟨⟨n.U, ?_, fun x => by rw [hU']⟩, ?_, hlen.symm, fun i hi hi' t hg => ?_⟩
    · have := mapM_some S.applyVar id n.U fun v hv => applyVar_of_fix (by
        rw [img_mkS]; split
        · exact hU0 v (by rw [← hU]; exact hv)
        · rfl)
      rwa [List.map_id] at this
    · rw [htys]
      exact mapM_some _ _ n.tys fun τ hτ => happ n hn τ hτ
    · exact hsch i hi hi' S (fun v hv => hagree n hn _ (.inr (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)) v hv) t hg

/-! ## The recorded types -/

mutual
theorem tysAtExp_ft : ∀ (y : AAtExp), ∀ τ ∈ tysAtExp false y, τ ∈ tysAtExp true y
  | .scon _ _, _, h | .var _ _ _, _, h | .con _ _ _, _, h | .op _ _ _, _, h | .nil _, _, h | .unit, _, h => h
  | .tuple e1 e2 e3, τ, h => by
    simp only [tysAtExp, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl (tysExp_ft e1 τ h))
    · exact .inl (.inr (tysExp_ft e2 τ h))
    · exact .inr (tysExpOpt_ft e3 τ h)
  | .record r, τ, h => by simp only [tysAtExp] at h ⊢; exact tysExpRowOpt_ft r τ h
  | .update _ _ _ r, τ, h => by
    simp only [tysAtExp, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (tysExpRow_ft r τ h)
  | .letE d e, τ, h => by
    simp only [tysAtExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysDec_ft d τ h)
    · exact .inr (tysExp_ft e τ h)
  | .paren e, τ, h => by simp only [tysAtExp] at h ⊢; exact tysExp_ft e τ h
theorem tysExpRow_ft : ∀ (y : AExpRow), ∀ τ ∈ tysExpRow false y, τ ∈ tysExpRow true y
  | .field _ e rest, τ, h => by
    simp only [tysExpRow, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysExp_ft e τ h)
    · exact .inr (tysExpRowOpt_ft rest τ h)
theorem tysExpRowOpt_ft : ∀ (y : Option AExpRow), ∀ τ ∈ tysExpRowOpt false y, τ ∈ tysExpRowOpt true y
  | none, _, h => h
  | some r, τ, h => by simp only [tysExpRowOpt] at h ⊢; exact tysExpRow_ft r τ h
theorem tysExp_ft : ∀ (y : AExp), ∀ τ ∈ tysExp false y, τ ∈ tysExp true y
  | .atexp a, τ, h => by simp only [tysExp] at h ⊢; exact tysAtExp_ft a τ h
  | .app e a, τ, h => by
    simp only [tysExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysExp_ft e τ h)
    · exact .inr (tysAtExp_ft a τ h)
  | .lam p e, τ, h => by
    simp only [tysExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (tysExp_ft e τ h)
  | .caseE e m, τ, h => by
    simp only [tysExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysExp_ft e τ h)
    · exact .inr (tysMatch_ft m τ h)
theorem tysExpOpt_ft : ∀ (y : Option AExp), ∀ τ ∈ tysExpOpt false y, τ ∈ tysExpOpt true y
  | none, _, h => h
  | some e, τ, h => by simp only [tysExpOpt] at h ⊢; exact tysExp_ft e τ h
theorem tysMatch_ft : ∀ (y : AMatch), ∀ τ ∈ tysMatch false y, τ ∈ tysMatch true y
  | .mk (.mk p e) rest, τ, h => by
    simp only [tysMatch, tysMRule, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl h)
    · exact .inl (.inr (tysExp_ft e τ h))
    · exact .inr (tysMatchOpt_ft rest τ h)
theorem tysMatchOpt_ft : ∀ (y : Option AMatch), ∀ τ ∈ tysMatchOpt false y, τ ∈ tysMatchOpt true y
  | none, _, h => h
  | some m, τ, h => by simp only [tysMatchOpt] at h ⊢; exact tysMatch_ft m τ h
theorem tysDec_ft : ∀ (y : ADec), ∀ τ ∈ tysDec false y, τ ∈ tysDec true y
  | .val VE vb, τ, h => by
    simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.mem_append] at h ⊢
    exact .inr (tysValBind_ft vb τ h)
theorem tysValBind_ft : ∀ (y : AValBind), ∀ τ ∈ tysValBind false y, τ ∈ tysValBind true y
  | .var _ ann _ e rest, τ, h => by
    simp only [tysValBind, annMark, List.nil_append, List.cons_append, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl (.inr (tysExp_ft e τ h)))
    · exact .inr (.inr (tysValBindOpt_ft rest τ h))
  | .pat p e, τ, h => by
    simp only [tysValBind, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (tysExp_ft e τ h)
theorem tysValBindOpt_ft : ∀ (y : Option AValBind), ∀ τ ∈ tysValBindOpt false y, τ ∈ tysValBindOpt true y
  | none, _, h => h
  | some vb, τ, h => by simp only [tysValBindOpt] at h ⊢; exact tysValBind_ft vb τ h
end

end StandardElm.Stat.Complete.WDP

namespace StandardElm.Stat.Complete
open StandardElm.Stat
open StandardElm.Stat.Complete.WDP

/-! ## Principality (section 7, L12) -/

/-- Principality of W for F_d: what W returns is a checked derivation of which every canonical
    derivation without free `bnd` variables is an instance (sec:static-core-principal, the instance
    lists left out). -/
theorem wdPrincipality : WDPrincipality := by
  intro fuel C0 e a hC h
  obtain ⟨hc, he, -⟩ := inferExpWD_sound h
  refine ⟨hc, fun a' hc' he' => ?_⟩
  have hnb := noFreeBndExp_of_checkExp hc'
  have hcn' := canonExp_of_checkExp hc'
  have hw := wdExp_root (fuel := fuel) hC hc' (he'.trans he)
  unfold inferExpWD at h
  simp only at h
  split at h
  · rename_i τ ar st hok
    split at h
    · split at h
      · cases h
        rw [hok] at hw
        obtain ⟨-, hinv, -, hokA, T, hF, -, hs⟩ := hw
        have hfx : FixR (rigidFromD (freshAboveD C0)) T := hF.fix
        have hcls : RespR T := hF.resp respR_rid
        have hb0 : T.r (.bnd 0) = ([], some (.bnd 0)) := fix_bnd0 hfx
        have hTa : rsbExp T (rsbExp (toRS st.θ) ar) = rsbExp T ar := by rw [rsbExp_sbD, comp_of_absorbsD hF.abs]
        have hs' : stripExp (rsbExp T (rsbExp (toRS st.θ) ar)) = stripExp a' := by rw [hTa]; exact hs
        have hnbd := nbd_of_derivation hnb hcn'
        have himg : ∀ τ ∈ tysExp false (rsbExp (toRS st.θ) ar), rsb T τ ∈ tysExp false a' := by
          intro τ hτ
          rw [← tysExp_strip, ← hs', tysExp_strip, tysExp_sbD false T hb0]
          exact List.mem_map_of_mem hτ
        have hNBT : NBT T (tysExp false (rsbExp (toRS st.θ) ar)) := fun τ hτ => hnbd _ (himg τ hτ)
        have hfalse : OkAD st.n (tysExp false (rsbExp (toRS st.θ) ar)) := by
          intro τ hτ
          have hτ' := hτ
          rw [tysExp_sbD false _ (fix_bnd0 fun v hv => goodR_fix hinv.good hv)] at hτ'
          obtain ⟨τ0, h0, rfl⟩ := List.mem_map.mp hτ'
          refine okT_theta hinv (hokA τ0 (tysExp_ft ar τ0 h0)) hfx hF.abs ?_
          rw [← absR_rsb hF.abs]
          exact (hNBT _ hτ).1
        have hok' : OkAD st.n (tysExp true (rsbExp (toRS st.θ) ar)) :=
          okAD_trueExp (toRS st.θ) st.n ar C0 (checkExpS_of_checkExp hc) hokA hfalse
        have hF2 := nodesExp_relD T (freshAboveD C0) st.n C0.U hfx hcls _ C0 C0 [] rfl (checkExpS_of_checkExp hc) (root_relD hfx) hok' hNBT
        rw [hs'] at hF2
        have hroot : ∀ v ∈ C0.tyvars, T.img v = vty v := fun v hv => hfx v (rigid_of_oldD (old_of_rootD hv))
        refine ⟨by rw [stripExp_erase, stripExp_erase]; exact he', instanceNodes_of_F2D hF2
          (nodesExp_pd C0 _ []).1 hcls hroot
          (fun v hv => hroot v (mem_ctx_tyvars.mpr (.inl (by simp [restTv, hv])))) fun n hn τ hτ => ?_⟩
        obtain ⟨n', hn', hr⟩ := f2_mem_left hF2 n hn
        rw [nodesExp_strip] at hn'
        exact hcn' n' hn' _ (by rw [hr.2.2.2.1]; exact List.mem_map_of_mem hτ)
      · cases h
    · cases h
  · cases h
  · cases h
  · cases h

/-- `IsPrincipalB` (WPrincipal.lean) for F_d: a checked derivation of which every canonical
    derivation without free `bnd` variables is an instance. -/
def IsPrincipalD (C0 : Ctx) (a : AExp) : Prop :=
  checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true →
    a'.erase = a.erase → InstanceOfB C0 a' a

/-- `IsPrincipalD` is step 9's `IsPrincipal` with the derivations compared restricted to the
    canonical ones without free `bnd` variables. -/
theorem isPrincipalD_iff {C0 : Ctx} {a : AExp} : IsPrincipalD C0 a ↔
    checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true →
      a'.erase = a.erase → InstanceOf C0 a' a := by
  unfold IsPrincipalD
  simp only [instanceOfB_iff]

/-- Section 7's principality of W for F_d, in step 9's terms: W's result is a derivation of the
    phrase, with canonical types at its nodes, and every canonical derivation of it without free
    `bnd` variables is an instance of it (`InstanceOf`, sec:static-core-principal). -/
theorem inferExpWD_principal {fuel : Nat} {C0 : Ctx} {e : StandardElm.Src.BExp} {a : AExp} (hC : RootOKD C0)
    (h : inferExpWD fuel C0 e = .ok a) :
    a.erase = e ∧ CanonExp C0 a ∧ IsPrincipalD C0 a ∧ checkExp C0 a = true ∧
      ∀ a', checkExp C0 a' = true → a'.erase = a.erase → InstanceOf C0 a' a := by
  obtain ⟨hc, he, hcn⟩ := inferExpWD_sound h
  have hp := wdPrincipality fuel C0 e a hC h
  exact ⟨he, hcn, hp, isPrincipalD_iff.mp hp⟩

end StandardElm.Stat.Complete
