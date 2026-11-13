/-
  A Standard Definition of Elm? Mechanisation: principality of W for F_e (milestone (e) of plan
  step 11, section 7 and L12; WDNodeOk.lean and WDPrincipality.lean for WE.lean's W):
  `wePrincipality : WEPrincipality`.

  From L12 (`weExp_root`, WETheorems.lean) every derivation `a'` is `T x` with the instance lists
  left out, where `x = θ ar` is W's result and `T` fixes the rigid variables (the root context's,
  the `bnd` and the named ones). The types `x` records are `OkTD` (`okAD_trueExpE`: W's annotations
  carry its explicit variables and have types over named variables, which `θ` fixes); the nodes
  of `x` and of `T x` correspond one to one, in order (`nodesExp_relE`, WENodeRelExp.lean); the
  paths are distinct, so nodes with the same path correspond. The instance substitution of
  sec:static-core-principal is `T` restricted to the variables at the nodes of `x` (`mkS`): it
  respects classes, moves no variable of the root context and no explicit variable of a node
  (both rigid), is defined on the nodes' types, maps each node of `x` to the corresponding node of
  `a'`, and at the schemes satisfies the scheme clause (`SchInstD`): at a member's node by
  `SchOK`, at a declaration node by `closE_instD` (monotypes) or `closE_instAnn` (annotated
  members).

  `isPrincipalE_iff` and `inferExpWD_principal`: W's result is principal in step 9's sense
  (`IsPrincipal`, `InstanceOf`, nodes without instance lists).
-/
import StandardElmMech.Stat.Complete.WENodeRelExp
import StandardElmMech.Stat.Complete.WDPrincipality

set_option linter.unusedSectionVars false

namespace StandardElm.Stat.Complete.WE.WDP
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Stat.Complete
open StandardElm.Stat.Complete.WDP

/-! ## The types of W's result are `OkTD` -/

section
variable (s : RSub) (n n0 : Nat) (hs0 : FixR (rigidFromD n0) s)
include hs0

mutual
theorem okAD_trueAtE : ∀ (y : AAtExp) (C : Ctx), checkAtExp C (rsbAtExp s y) = true → OkAD n (tysAtExp true y) →
    OkAD n (tysAtExp false (rsbAtExp s y)) → OkAD n (tysAtExp true (rsbAtExp s y))
  | .scon _ _, _, _, _, h | .var _ _ _, _, _, _, h | .con _ _ _, _, _, _, h | .op _ _ _, _, _, _, h
  | .nil _, _, _, _, h | .unit, _, _, _, h => h
  | .tuple e1 e2 e3, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp, Bool.and_eq_true] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    obtain ⟨hy12, hy3⟩ := OkAD.split hy; obtain ⟨hy1, hy2⟩ := OkAD.split hy12
    obtain ⟨hf12, hf3⟩ := OkAD.split hf; obtain ⟨hf1, hf2⟩ := OkAD.split hf12
    exact OkAD.app' (OkAD.app' (okAD_trueExpE e1 C hc.1.1 hy1 hf1) (okAD_trueExpE e2 C hc.1.2 hy2 hf2))
      (okAD_trueExpOptE e3 C hc.2 hy3 hf3)
  | .record r, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    exact okAD_trueRowOptE r C hc hy hf
  | .update x inst τ r, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp, Bool.and_eq_true] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    exact OkAD.cons (hf _ (.head _)) (okAD_trueRowE r C hc.1.2 (OkAD.tail hy) (OkAD.tail hf))
  | .letE d e, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp, Bool.and_eq_true] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueDecE d C hc.1 hy1 hf1) (okAD_trueExpE e _ hc.2 hy2 hf2)
  | .paren e, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    exact okAD_trueExpE e C hc hy hf
theorem okAD_trueRowE : ∀ (y : AExpRow) (C : Ctx), checkExpRow C (rsbExpRow s y) = true → OkAD n (tysExpRow true y) →
    OkAD n (tysExpRow false (rsbExpRow s y)) → OkAD n (tysExpRow true (rsbExpRow s y))
  | .field l e rest, C, hc, hy, hf => by
    simp only [rsbExpRow, checkExpRow, Bool.and_eq_true] at hc
    simp only [rsbExpRow, tysExpRow] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueExpE e C hc.1 hy1 hf1) (okAD_trueRowOptE rest C hc.2 hy2 hf2)
theorem okAD_trueRowOptE : ∀ (y : Option AExpRow) (C : Ctx), checkExpRowOpt C (rsbExpRowOpt s y) = true →
    OkAD n (tysExpRowOpt true y) → OkAD n (tysExpRowOpt false (rsbExpRowOpt s y)) →
    OkAD n (tysExpRowOpt true (rsbExpRowOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some r, C, hc, hy, hf => by
    simp only [rsbExpRowOpt, checkExpRowOpt, tysExpRowOpt] at hc hy hf ⊢
    exact okAD_trueRowE r C hc hy hf
theorem okAD_trueExpE : ∀ (y : AExp) (C : Ctx), checkExpS C (rsbExp s y) = true → OkAD n (tysExp true y) →
    OkAD n (tysExp false (rsbExp s y)) → OkAD n (tysExp true (rsbExp s y))
  | .atexp a, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    exact okAD_trueAtE a C hc hy hf
  | .app e a, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS, Bool.and_eq_true] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueExpE e C hc.1.1 hy1 hf1) (okAD_trueAtE a C hc.1.2 hy2 hf2)
  | .lam p e, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS, Bool.and_eq_true] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' hf1 (okAD_trueExpE e _ hc.2 hy2 hf2)
  | .caseE e m, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS, Bool.and_eq_true] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueExpE e C hc.1.1 hy1 hf1) (okAD_trueMatchE m C hc.1.2 hy2 hf2)
theorem okAD_trueExpOptE : ∀ (y : Option AExp) (C : Ctx), checkExpOpt C (rsbExpOpt s y) = true →
    OkAD n (tysExpOpt true y) → OkAD n (tysExpOpt false (rsbExpOpt s y)) → OkAD n (tysExpOpt true (rsbExpOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some e, C, hc, hy, hf => by
    simp only [rsbExpOpt, checkExpOpt, tysExpOpt] at hc hy hf ⊢
    exact okAD_trueExpE e C hc hy hf
theorem okAD_trueMatchE : ∀ (y : AMatch) (C : Ctx), checkMatch C (rsbMatch s y) = true → OkAD n (tysMatch true y) →
    OkAD n (tysMatch false (rsbMatch s y)) → OkAD n (tysMatch true (rsbMatch s y))
  | .mk (.mk p e) rest, C, hc, hy, hf => by
    simp only [rsbMatch, rsbMRule, checkMatch, checkMRule, Bool.and_eq_true] at hc
    simp only [rsbMatch, rsbMRule, tysMatch, tysMRule] at hy hf ⊢
    obtain ⟨hy12, hy3⟩ := OkAD.split hy; obtain ⟨hy1, hy2⟩ := OkAD.split hy12
    obtain ⟨hf12, hf3⟩ := OkAD.split hf; obtain ⟨hf1, hf2⟩ := OkAD.split hf12
    refine OkAD.app' (OkAD.app' hf1 (okAD_trueExpE e _ hc.1.2 hy2 hf2)) (okAD_trueMatchOptE rest C (fun m0 hm0 => ?_) hy3 hf3)
    have := hc.2
    cases rest with
    | none => cases hm0
    | some m =>
      simp only [rsbMatchOpt, Option.some.injEq] at hm0; subst hm0
      simp only [rsbMatchOpt, checkMatchOptAt, Bool.and_eq_true] at this
      exact this.1
theorem okAD_trueMatchOptE : ∀ (y : Option AMatch) (C : Ctx), (∀ m0, rsbMatchOpt s y = some m0 → checkMatch C m0 = true) →
    OkAD n (tysMatchOpt true y) → OkAD n (tysMatchOpt false (rsbMatchOpt s y)) → OkAD n (tysMatchOpt true (rsbMatchOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some m, C, hc, hy, hf => by
    simp only [rsbMatchOpt, tysMatchOpt] at hy hf ⊢
    exact okAD_trueMatchE m C (hc _ rfl) hy hf
theorem okAD_trueDecE : ∀ (y : ADec) (C : Ctx), checkDec C (rsbDec s y) = true → OkAD n (tysDec true y) →
    OkAD n (tysDec false (rsbDec s y)) → OkAD n (tysDec true (rsbDec s y))
  | .val VE vb, C, hc, hy, hf => by
    simp only [rsbDec, checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [rsbDec, tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hy hf ⊢
    obtain ⟨-, hy2⟩ := OkAD.split hy
    have hvb := okAD_trueValBindE vb _ hc.1 hy2 hf
    refine OkAD.app' (fun τ hτ => ?_) hvb
    have hann := annOKV_of_okAD _ hvb
    simp only [veTys, List.mem_flatMap] at hτ
    obtain ⟨q, hq, hτ⟩ := hτ
    rw [← hc.2] at hq
    rcases valbind_ve_entE2 _ hann q hq with hP | hA
    · have h2 := hP false
      simp [schTys, h2.1] at hτ; subst hτ
      exact okT_pentD hf h2
    · obtain ⟨-, U', τ', he, -, hnam⟩ := hA false
      rw [he] at hτ; exact okAD_schTys_ann hnam τ hτ
theorem okAD_trueValBindE : ∀ (y : AValBind) (C : Ctx), checkValBind C (rsbValBind s y) = true →
    OkAD n (tysValBind true y) → OkAD n (tysValBind false (rsbValBind s y)) → OkAD n (tysValBind true (rsbValBind s y))
  | .var x ann τ e rest, C, hc, hy, hf => by
    simp only [rsbValBind, checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [rsbValBind, tysValBind, List.cons_append] at hy hf ⊢
    have hm : ∀ t ∈ annMark true ann τ, OkTD n t := fun t ht => hy t (by simp [ht])
    have hcan := canon_of_okAD hm
    have hnam := named_of_okAD hm
    have hm1 : annMark true ann τ = [] := by unfold annMark; rw [if_pos ⟨hcan, fun _ hs => hnam hs⟩]
    have hm1' : annMark true ann (rsb s τ) = [] := by
      unfold annMark; rw [if_pos ⟨hcan, fun _ hs => by rw [rsb_named hs0 (hnam hs)]; exact hnam hs⟩]
    have hm0 : annMark false ann (rsb s τ) = [] := by rw [annMark_false, if_pos hcan]
    rw [hm1] at hy; rw [hm0] at hf; rw [hm1']
    simp only [List.nil_append] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split (OkAD.tail hy); obtain ⟨hf1, hf2⟩ := OkAD.split (OkAD.tail hf)
    exact OkAD.cons (hf _ (.head _)) (OkAD.app' (okAD_trueExpE e _ hc.1.1.2 hy1 hf1)
      (okAD_trueValBindOptE rest C hc.2 hy2 hf2))
  | .pat p e, C, hc, hy, hf => by
    simp only [rsbValBind, checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [rsbValBind, tysValBind] at hy hf ⊢
    obtain ⟨-, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' hf1 (okAD_trueExpE e C hc.1.2 hy2 hf2)
theorem okAD_trueValBindOptE : ∀ (y : Option AValBind) (C : Ctx), checkValBindOpt C (rsbValBindOpt s y) = true →
    OkAD n (tysValBindOpt true y) → OkAD n (tysValBindOpt false (rsbValBindOpt s y)) →
    OkAD n (tysValBindOpt true (rsbValBindOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some vb, C, hc, hy, hf => by
    simp only [rsbValBindOpt, checkValBindOpt, tysValBindOpt] at hc hy hf ⊢
    exact okAD_trueValBindE vb C hc hy hf
end

end

/-! ## Corresponding nodes are instances -/

/-- With distinct paths, nodes of the two lists with the same path are corresponding nodes. -/
theorem f2_pickE {T : RSub} {l l' : List Node} (h : F2 (NRelE T) l l') (hpd : PD l) :
    ∀ n ∈ l, ∀ n' ∈ l', n.path = n'.path → NRelE T n n' := by
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

/-- The node-wise correspondence with distinct paths is an instance (step 9's `InstanceNodes`), for
    a class-respecting `T` fixing the free variables of the root context, whose images of the
    nodes' types are canonical. -/
theorem instanceNodes_of_F2E {T : RSub} {A0 : List BVar} {ns ns' : List Node}
    (hF : F2 (NRelE T) ns ns') (hpd : PD ns) (hcls : RespR T)
    (hA0 : ∀ v ∈ A0, T.img v = vty v)
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
  · obtain ⟨hU, -, hU', htys, hlen, hsch⟩ := f2_pickE hF hpd n hn n' hn' hp
    refine ⟨⟨n.U, ?_, fun x => by rw [hU']⟩, ?_, hlen.symm, fun i hi hi' t hg => ?_⟩
    · have := mapM_some S.applyVar id n.U fun v hv => applyVar_of_fix (by
        rw [img_mkS]; split
        · exact hU v hv
        · rfl)
      rwa [List.map_id] at this
    · rw [htys]
      exact mapM_some _ _ n.tys fun τ hτ => happ n hn τ hτ
    · exact hsch i hi hi' S (fun v hv => hagree n hn _ (.inr (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩)) v hv) t hg

/-! ## The recorded types -/

theorem annMark_ft {ann : Option (StandardElm.Src.BTy × List BVar)} {τ0 τ : Ty} (h : τ ∈ annMark false ann τ0) :
    τ ∈ annMark true ann τ0 := by
  rw [annMark_false] at h
  split at h
  · cases h
  · rename_i hc; unfold annMark; rw [if_neg fun h' => hc h'.1]; exact h

mutual
theorem tysAtExp_ftE : ∀ (y : AAtExp), ∀ τ ∈ tysAtExp false y, τ ∈ tysAtExp true y
  | .scon _ _, _, h | .var _ _ _, _, h | .con _ _ _, _, h | .op _ _ _, _, h | .nil _, _, h | .unit, _, h => h
  | .tuple e1 e2 e3, τ, h => by
    simp only [tysAtExp, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl (tysExp_ftE e1 τ h))
    · exact .inl (.inr (tysExp_ftE e2 τ h))
    · exact .inr (tysExpOpt_ftE e3 τ h)
  | .record r, τ, h => by simp only [tysAtExp] at h ⊢; exact tysExpRowOpt_ftE r τ h
  | .update _ _ _ r, τ, h => by
    simp only [tysAtExp, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (tysExpRow_ftE r τ h)
  | .letE d e, τ, h => by
    simp only [tysAtExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysDec_ftE d τ h)
    · exact .inr (tysExp_ftE e τ h)
  | .paren e, τ, h => by simp only [tysAtExp] at h ⊢; exact tysExp_ftE e τ h
theorem tysExpRow_ftE : ∀ (y : AExpRow), ∀ τ ∈ tysExpRow false y, τ ∈ tysExpRow true y
  | .field _ e rest, τ, h => by
    simp only [tysExpRow, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysExp_ftE e τ h)
    · exact .inr (tysExpRowOpt_ftE rest τ h)
theorem tysExpRowOpt_ftE : ∀ (y : Option AExpRow), ∀ τ ∈ tysExpRowOpt false y, τ ∈ tysExpRowOpt true y
  | none, _, h => h
  | some r, τ, h => by simp only [tysExpRowOpt] at h ⊢; exact tysExpRow_ftE r τ h
theorem tysExp_ftE : ∀ (y : AExp), ∀ τ ∈ tysExp false y, τ ∈ tysExp true y
  | .atexp a, τ, h => by simp only [tysExp] at h ⊢; exact tysAtExp_ftE a τ h
  | .app e a, τ, h => by
    simp only [tysExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysExp_ftE e τ h)
    · exact .inr (tysAtExp_ftE a τ h)
  | .lam p e, τ, h => by
    simp only [tysExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (tysExp_ftE e τ h)
  | .caseE e m, τ, h => by
    simp only [tysExp, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (tysExp_ftE e τ h)
    · exact .inr (tysMatch_ftE m τ h)
theorem tysExpOpt_ftE : ∀ (y : Option AExp), ∀ τ ∈ tysExpOpt false y, τ ∈ tysExpOpt true y
  | none, _, h => h
  | some e, τ, h => by simp only [tysExpOpt] at h ⊢; exact tysExp_ftE e τ h
theorem tysMatch_ftE : ∀ (y : AMatch), ∀ τ ∈ tysMatch false y, τ ∈ tysMatch true y
  | .mk (.mk p e) rest, τ, h => by
    simp only [tysMatch, tysMRule, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl h)
    · exact .inl (.inr (tysExp_ftE e τ h))
    · exact .inr (tysMatchOpt_ftE rest τ h)
theorem tysMatchOpt_ftE : ∀ (y : Option AMatch), ∀ τ ∈ tysMatchOpt false y, τ ∈ tysMatchOpt true y
  | none, _, h => h
  | some m, τ, h => by simp only [tysMatchOpt] at h ⊢; exact tysMatch_ftE m τ h
theorem tysDec_ftE : ∀ (y : ADec), ∀ τ ∈ tysDec false y, τ ∈ tysDec true y
  | .val VE vb, τ, h => by
    simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.mem_append] at h ⊢
    exact .inr (tysValBind_ftE vb τ h)
theorem tysValBind_ftE : ∀ (y : AValBind), ∀ τ ∈ tysValBind false y, τ ∈ tysValBind true y
  | .var _ ann τ0 e rest, τ, h => by
    simp only [tysValBind, List.mem_append, List.mem_cons] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr (annMark_ft h)))
    · exact .inl (.inr (tysExp_ftE e τ h))
    · exact .inr (tysValBindOpt_ftE rest τ h)
  | .pat p e, τ, h => by
    simp only [tysValBind, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (tysExp_ftE e τ h)
theorem tysValBindOpt_ftE : ∀ (y : Option AValBind), ∀ τ ∈ tysValBindOpt false y, τ ∈ tysValBindOpt true y
  | none, _, h => h
  | some vb, τ, h => by simp only [tysValBindOpt] at h ⊢; exact tysValBind_ftE vb τ h
end

end StandardElm.Stat.Complete.WE.WDP

namespace StandardElm.Stat.Complete
namespace WE
open StandardElm.Stat
open StandardElm.Stat.Complete.WDP
open StandardElm.Stat.Complete.WE.WDP

/-! ## Principality (section 7, L12) -/

/-- Principality of W for F_e: what W returns is a checked derivation of which every derivation is
    an instance (sec:static-core-principal, the instance lists left out). -/
theorem wePrincipality : WEPrincipality := by
  intro fuel C0 e a hC h
  obtain ⟨hc, he, -⟩ := inferExpWD_sound h
  refine ⟨hc, fun a' hc' he' => ?_⟩
  have hcn' := canonExp_of_checkExp hc'
  have hnbd := nbd_of_derivation (noFreeBndExp_of_checkExp hc') hcn' (canonAnnExp_of_checkExp hc')
  have hw := weExp_root (fuel := fuel) hC hc' (he'.trans he)
  rw [inferExpWD_eq] at h; unfold inferExpWDSpec at h
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
        have hθfx : FixR (rigidFromD (freshAboveD C0)) (toRS st.θ) := fun v hv => goodR_fix hinv.good hv
        have hTa : rsbExp T (rsbExp (toRS st.θ) ar) = rsbExp T ar := by rw [rsbExp_sbD, comp_of_absorbsD hF.abs]
        have hs' : stripExp (rsbExp T (rsbExp (toRS st.θ) ar)) = stripExp a' := by rw [hTa]; exact hs
        have himg : ∀ τ ∈ tysExp false (rsbExp (toRS st.θ) ar), rsb T τ ∈ tysExp false a' := by
          intro τ hτ
          rw [← tysExp_strip, ← hs', tysExp_strip, tysExp_sbD T hb0]
          exact List.mem_map_of_mem hτ
        have hNBT : NBT T (tysExp false (rsbExp (toRS st.θ) ar)) := fun τ hτ => hnbd _ (himg τ hτ)
        have hfalse : OkAD st.n (tysExp false (rsbExp (toRS st.θ) ar)) := by
          intro τ hτ
          have hτ' := hτ
          rw [tysExp_sbD _ (fix_bnd0 hθfx)] at hτ'
          obtain ⟨τ0, h0, rfl⟩ := List.mem_map.mp hτ'
          refine okT_theta hinv (hokA τ0 (tysExp_ftE ar τ0 h0)) hfx hF.abs ?_
          rw [← absR_rsb hF.abs]
          exact (hNBT _ hτ).1
        have hok' : OkAD st.n (tysExp true (rsbExp (toRS st.θ) ar)) :=
          okAD_trueExpE (toRS st.θ) st.n (freshAboveD C0) hθfx ar C0 (checkExpS_of_checkExp hc) hokA hfalse
        have hF2 := nodesExp_relE T (freshAboveD C0) st.n hfx hcls _ C0 C0 [] (checkExpS_of_checkExp hc)
          (root_relD hfx) hok' hNBT
        rw [hs'] at hF2
        have hroot : ∀ v ∈ C0.tyvars, T.img v = vty v := fun v hv => hfx v (rigid_of_oldD (old_of_rootD hv))
        refine ⟨by rw [stripExp_erase, stripExp_erase]; exact he', instanceNodes_of_F2E hF2
          (nodesExp_pd C0 _ []).1 hcls hroot fun n hn τ hτ => ?_⟩
        obtain ⟨n', hn', hr⟩ := f2_mem_left hF2 n hn
        rw [nodesExp_strip] at hn'
        exact hcn' n' hn' _ (by rw [hr.2.2.2.1]; exact List.mem_map_of_mem hτ)
      · cases h
    · cases h
  · cases h
  · cases h
  · cases h

/-- `IsPrincipalB` (WPrincipal.lean) for F_e: a checked derivation of which every derivation is an
    instance, the instance lists left out. -/
def IsPrincipalE (C0 : Ctx) (a : AExp) : Prop :=
  checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true →
    a'.erase = a.erase → InstanceOfB C0 a' a

/-- `IsPrincipalE` is step 9's `IsPrincipal`. -/
theorem isPrincipalE_iff {C0 : Ctx} {a : AExp} : IsPrincipalE C0 a ↔ IsPrincipal C0 a := by
  unfold IsPrincipalE IsPrincipal
  simp only [instanceOfB_iff]

/-- Section 7's principality of W for F_e, in step 9's terms: W's result is a derivation of the
    phrase, with canonical types at its nodes, and it is principal (`IsPrincipal`,
    sec:static-core-principal): every derivation of the phrase is an instance of it. -/
theorem inferExpWD_principal {fuel : Nat} {C0 : Ctx} {e : StandardElm.Src.BExp} {a : AExp} (hC : RootOKD C0)
    (h : inferExpWD fuel C0 e = .ok a) :
    a.erase = e ∧ (∀ nd ∈ nodesExp C0 [] a, ∀ τ ∈ nd.tys, cnB τ = true) ∧ IsPrincipal C0 a := by
  obtain ⟨-, he, hcn⟩ := inferExpWD_sound h
  exact ⟨he, hcn, isPrincipalE_iff.mp (wePrincipality fuel C0 e a hC h)⟩

end WE

end StandardElm.Stat.Complete
