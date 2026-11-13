/-
  A Standard Definition of Elm? Mechanisation: ports in module-level W (milestone (g) of plan
  step 11). A port `port x : ty` is elaborated as the annotated group `x : ty; x = x` in the nested
  `let` (`MW.portVB`). Every context at the top level of a module is closed (its free variables are
  none), and the contexts of two derivations of a module's declarations differ only in their values
  (`PA`: the same explicit variables and types as a fixed context `Cp`, and closed). So:

  * the port's node is the same in every derivation (`elabPort_congr`, `elabPort_U`: the rule fixes
    the port's explicit variables and its type);
  * W's group for the port checks in the context of any derivation at the same place
    (`checkDec_portGroup`): its occurrence of `x` is found in its own environment;
  * after the port, the module's context and the `let` body's agree (`portsOKB` asks that the
    group's closed environment be the port rule's).

  `toExp_checkT` is `toExp_check` with ports: a derivation of a module's declarations gives a
  derivation of the nested `let`, its ports' groups taken from W's derivation (the template).
-/
import StandardElmMech.Stat.Complete.ModulesFail

namespace StandardElm.Stat.Complete
namespace MW
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtExp BExp BDec BValBind BTopDec BModule BProgram BDatBind BTypBind)

/-! ## Closed contexts with the types of `Cp` -/

/-- `C` has the explicit variables and the types of `Cp`, and no free variable. -/
structure PA (Cp C : Ctx) : Prop where
  U : C.U = Cp.U
  QE : C.E.QE = Cp.E.QE
  TE : C.E.TE = Cp.E.TE
  cl : ∀ v, v ∉ C.tyvars

theorem PA.refl {Cp : Ctx} (h : ∀ v, v ∉ Cp.tyvars) : PA Cp Cp := ⟨rfl, rfl, rfl, h⟩

theorem notin_of_nil {C : Ctx} (h : C.tyvars = []) : ∀ v, v ∉ C.tyvars := fun v hv => by rw [h] at hv; cases hv

theorem PA.ofCEq {Cp C D : Ctx} (h : PA Cp C) (hc : CEq C D) : PA Cp D :=
  ⟨hc.U ▸ h.U, hc.QE ▸ h.QE, hc.TE ▸ h.TE, fun v hv => h.cl v ((hc.tyvars_mem v).mpr hv)⟩

theorem mem_ctx_tyvars' {C : Ctx} {v : BVar} :
    v ∈ C.tyvars ↔ v ∈ FMap.tyvarsBy IEnv.tyvars [] C.E.QE ∨ v ∈ TyEnv.tyvars C.E.TE ∨
      (∃ k b, FMap.find? C.E.VE k = some b ∧ v ∈ b.1.tyvars) ∨ v ∈ C.U := by
  simp only [Ctx.tyvars, Env.tyvars, ValEnv.tyvars, List.mem_append, mem_tyvarsBy _ v C.E.VE []]
  constructor
  · rintro ((⟨h | h⟩ | ⟨k, b, -, hf, hv⟩) | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨k, b, hf, hv⟩))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | ⟨k, b, hf, hv⟩ | h)
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr ⟨k, b, List.not_mem_nil, hf, hv⟩)
    · exact .inr h

/-- Closed: adding a closed value environment by `+`. -/
theorem closed_plusVE {C : Ctx} (hC : ∀ v, v ∉ C.tyvars) {VE : ValEnv} (hVE : ∀ p ∈ VE, p.2.1.tyvars = []) :
    ∀ v, v ∉ (C.plusVE VE).tyvars := by
  intro v hv
  rcases mem_ctx_tyvars'.mp hv with h | h | ⟨k, b, hf, hb⟩ | h
  · exact hC v (mem_ctx_tyvars'.mpr (.inl h))
  · exact hC v (mem_ctx_tyvars'.mpr (.inr (.inl h)))
  · simp only [Ctx.plusVE, FMap.find?_append] at hf
    cases h1 : FMap.find? VE k with
    | some b' =>
      rw [h1] at hf; cases hf
      rw [hVE _ (mem_of_find? h1)] at hb; cases hb
    | none =>
      rw [h1] at hf
      exact hC v (mem_ctx_tyvars'.mpr (.inr (.inr (.inl ⟨k, b, hf, hb⟩))))
  · exact hC v (mem_ctx_tyvars'.mpr (.inr (.inr (.inr h))))

/-- Closed: adding a closed value environment by `⊕`. -/
theorem closed_oplusVE {C : Ctx} (hC : ∀ v, v ∉ C.tyvars) {VE : ValEnv} (hVE : ∀ p ∈ VE, p.2.1.tyvars = []) :
    ∀ v, v ∉ (C.oplusE (Env.ofVE VE)).tyvars := by
  intro v hv
  rcases mem_ctx_tyvars'.mp hv with h | h | ⟨k, b, hf, hb⟩ | h
  · simp only [Ctx.oplusE, Env.plus, Env.ofVE, modify_nil] at h
    exact hC v (mem_ctx_tyvars'.mpr (.inl h))
  · simp only [Ctx.oplusE, Env.plus, Env.ofVE, modify_nil] at h
    exact hC v (mem_ctx_tyvars'.mpr (.inr (.inl h)))
  · simp only [Ctx.oplusE, Env.plus, Env.ofVE, FMap.find?_modify] at hf
    cases h1 : FMap.find? VE k with
    | some b' =>
      rw [h1] at hf; cases hf
      rw [hVE _ (mem_of_find? h1)] at hb; cases hb
    | none =>
      rw [h1] at hf
      exact hC v (mem_ctx_tyvars'.mpr (.inr (.inr (.inl ⟨k, b, hf, hb⟩))))
  · exact hC v (mem_ctx_tyvars'.mpr (.inr (.inr (.inr h))))

theorem PA.plusVE {Cp C : Ctx} (h : PA Cp C) {VE : ValEnv} (hVE : ∀ p ∈ VE, p.2.1.tyvars = []) :
    PA Cp (C.plusVE VE) := ⟨h.U, h.QE, h.TE, closed_plusVE h.cl hVE⟩

theorem PA.oplusVE {Cp C : Ctx} (h : PA Cp C) {VE : ValEnv} (hVE : ∀ p ∈ VE, p.2.1.tyvars = []) :
    PA Cp (C.oplusE (Env.ofVE VE)) :=
  ⟨h.U, by simp only [Ctx.oplusE, Env.plus, Env.ofVE, modify_nil, h.QE],
    by simp only [Ctx.oplusE, Env.plus, Env.ofVE, modify_nil, h.TE], closed_oplusVE h.cl hVE⟩

theorem closGroup_nil_of {A : List BVar} (h : ∀ v, v ∉ A) (VE : ValEnv) : closGroup A VE = closGroup [] VE :=
  closGroup_congr (fun v => ⟨fun hv => absurd hv (h v), fun hv => by cases hv⟩) VE

/-- A group's closed environment in a closed context is closed. -/
theorem closGroup_closed_of {A : List BVar} (h : ∀ v, v ∉ A) (VE : ValEnv) :
    ∀ p ∈ closGroup A VE, p.2.1.tyvars = [] := by
  rw [closGroup_nil_of h]; exact Closed.closGroup_closed VE

/-! ## The port's node -/

theorem elabPort_congr {C D : Ctx} (hU : C.U = D.U) (hQ : C.E.QE = D.E.QE) (hT : C.E.TE = D.E.TE)
    (hv : ∀ v, v ∈ C.tyvars ↔ v ∈ D.tyvars) (x : Var) (ty : BTy) (U : List BVar) :
    elabPort C x ty U = elabPort D x ty U := by
  have hl : ∀ c, C.lookupTy c = D.lookupTy c := fun c => by simp only [Ctx.lookupTy, Env.lookupTy, hQ, hT]
  have he : elabTy (C.plusU U) ty = elabTy (D.plusU U) ty :=
    Types.elabTy_congr ty ⟨by simp only [Ctx.plusU, hU], fun c _ => by
      have := hl c; simp only [Ctx.lookupTy, Ctx.plusU] at this ⊢; rw [this]⟩
  have hd : ∀ σ : Scheme, closScheme C.tyvars σ = closScheme D.tyvars σ := fun σ => by
    unfold closScheme; rw [diffL_congr hv]
  unfold elabPort
  rw [hU, he]
  simp only [hd]

theorem PA.elabPort {Cp C : Ctx} (h : PA Cp C) (hp : ∀ v, v ∉ Cp.tyvars) (x : Var) (ty : BTy) (U : List BVar) :
    elabPort C x ty U = elabPort Cp x ty U :=
  elabPort_congr h.U h.QE h.TE (fun v => ⟨fun hv => absurd hv (h.cl v), fun hv => absurd hv (hp v)⟩) x ty U

theorem elabPort_U {C : Ctx} {x : Var} {ty : BTy} {U : List BVar} {p : Env × PortEnv}
    (h : elabPort C x ty U = some p) : U = newU C.U ty := by
  unfold elabPort at h
  split at h
  · rename_i hn
    simp only [newForB, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact hn.1
  · cases h

theorem elabPort_ofVE {C : Ctx} {x : Var} {ty : BTy} {U : List BVar} {E : Env} {PE : PortEnv}
    (h : elabPort C x ty U = some (E, PE)) : E = Env.ofVE E.VE := by
  unfold elabPort at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · split at h
        · split at h
          · cases h; rfl
          · cases h
        · cases h
    · cases h
  · cases h

theorem elabPort_closed {C : Ctx} (hC : ∀ v, v ∉ C.tyvars) {x : Var} {ty : BTy} {U : List BVar} {E : Env}
    {PE : PortEnv} (h : elabPort C x ty U = some (E, PE)) : ∀ p ∈ E.VE, p.2.1.tyvars = [] := by
  have hA : ∀ σ : Scheme, closScheme C.tyvars σ = closScheme [] σ := fun σ => by
    unfold closScheme; rw [diffL_congr (A' := []) (fun v => ⟨fun hv => absurd hv (hC v), fun hv => by cases hv⟩)]
  unfold elabPort at h
  split at h
  · split at h
    · split at h
      · cases h
        intro p hp
        simp only [Env.ofVE, List.mem_singleton] at hp; subst hp
        simp only [hA]; exact Closed.closScheme_closed _
      · split at h
        · split at h
          · cases h
            intro p hp
            simp only [Env.ofVE, List.mem_singleton] at hp; subst hp
            simp only [hA]; exact Closed.closScheme_closed _
          · cases h
        · cases h
    · cases h
  · cases h

/-! ## W's group for a port, in another context -/

/-- In a closed context, the free variables of `C + VE` are those of `VE`. -/
theorem tyvars_plusVE_closed {C : Ctx} (hC : ∀ v, v ∉ C.tyvars) (VE : ValEnv) (v : BVar) :
    v ∈ (C.plusVE VE).tyvars ↔ ∃ k b, FMap.find? VE k = some b ∧ v ∈ b.1.tyvars := by
  constructor
  · intro hv
    rcases mem_ctx_tyvars'.mp hv with h | h | ⟨k, b, hf, hb⟩ | h
    · exact absurd ((mem_ctx_tyvars' (C := C)).mpr (.inl h)) (hC v)
    · exact absurd ((mem_ctx_tyvars' (C := C)).mpr (.inr (.inl h))) (hC v)
    · simp only [Ctx.plusVE, FMap.find?_append] at hf
      cases h1 : FMap.find? VE k with
      | some b' => rw [h1] at hf; cases hf; exact ⟨k, b, h1, hb⟩
      | none =>
        rw [h1] at hf
        exact absurd ((mem_ctx_tyvars' (C := C)).mpr (.inr (.inr (.inl ⟨k, b, hf, hb⟩)))) (hC v)
    · exact absurd ((mem_ctx_tyvars' (C := C)).mpr (.inr (.inr (.inr h)))) (hC v)
  · rintro ⟨k, b, hf, hb⟩
    refine mem_ctx_tyvars'.mpr (.inr (.inr (.inl ⟨k, b, ?_, hb⟩)))
    simp only [Ctx.plusVE, FMap.find?_append, hf]; rfl

/-- W's group for a port checks in any closed context with the same explicit variables and types:
    its occurrence of `x` is found in its own environment. -/
theorem checkDec_portGroup {D D' : Ctx} (hU : D.U = D'.U) (hQ : D.E.QE = D'.E.QE) (hT : D.E.TE = D'.E.TE)
    (hc : ∀ v, v ∉ D.tyvars) (hc' : ∀ v, v ∉ D'.tyvars) (VE : ValEnv) (x : Var) (ty : BTy) (U : List BVar)
    (τ : Ty) (ts : List Ty) (τ' : Ty) :
    checkDec D (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) =
      checkDec D' (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) := by
  have hl : ∀ c, (D.plusVE VE).lookupTy c = (D'.plusVE VE).lookupTy c := fun c => by
    simp only [Ctx.lookupTy, Env.lookupTy, Ctx.plusVE, hQ, hT]
  have he : elabTy ((D.plusVE VE).plusU U) ty = elabTy ((D'.plusVE VE).plusU U) ty :=
    Types.elabTy_congr ty ⟨by simp only [Ctx.plusU, Ctx.plusVE, hU], fun c _ => by
      have := hl c; simp only [Ctx.lookupTy, Ctx.plusU] at this ⊢; rw [this]⟩
  have hv : ∀ v, v ∈ (D.plusVE VE).tyvars ↔ v ∈ (D'.plusVE VE).tyvars := fun v => by
    rw [tyvars_plusVE_closed hc, tyvars_plusVE_closed hc']
  have hlv : ((D.plusVE VE).plusU U).lookupVal ⟨none, x⟩ = ((D'.plusVE VE).plusU U).lookupVal ⟨none, x⟩ ∨
      (AValBind.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none).ve ≠ VE := by
    by_cases hve : (AValBind.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none).ve = VE
    · left
      rw [← hve]
      simp [Ctx.lookupVal, Env.lookupVal, Ctx.plusU, Ctx.plusVE, AValBind.ve, FMap.modify,
        FMap.find?, FMap.keys]
    · exact .inr hve
  simp only [checkDec, checkValBind, checkAnn, checkExpS, checkAtExp, checkValBindOpt, annU]
  rcases hlv with hlv | hve
  · rw [hlv, he, show (D.plusVE VE).U = (D'.plusVE VE).U by simp only [Ctx.plusVE, hU]]
    have hall : (U.all fun v => !decide (v ∈ (D.plusVE VE).tyvars)) =
        (U.all fun v => !decide (v ∈ (D'.plusVE VE).tyvars)) := by
      congr 1; funext v; rw [decide_eq_decide.mpr (hv v)]
    rw [hall]
  · simp [hve]

/-! ## Templates -/

/-- The context after a template's declaration. -/
def tmplCtx (D : Ctx) : AExp → Ctx
  | .atexp (.letE d _) => D.plusVE (d.result D)
  | _ => D

theorem tmpl_check {D : Ctx} {t : AExp} (h : checkExp D t = true) : checkExp (tmplCtx D t) (tmplBody t) = true := by
  cases t with
  | atexp a =>
    cases a with
    | letE d e =>
      simp only [checkExp, checkExpS, checkAtExp, okExpB, okAtExpB, Bool.and_eq_true] at h
      simp only [tmplCtx, tmplBody, checkExp, Bool.and_eq_true]
      exact ⟨h.1.2, h.2.2.2⟩
    | _ => exact h
  | _ => exact h

theorem tmplCtx_PA {Cp D : Ctx} (h : PA Cp D) (t : AExp) : PA Cp (tmplCtx D t) := by
  cases t with
  | atexp a =>
    cases a with
    | letE d e =>
      cases d with
      | val VE vb => exact h.plusVE (closGroup_closed_of h.cl VE)
    | _ => exact h
  | _ => exact h

/-- What `portOKB` says of W's group for a port. -/
theorem portOKB_inv {Cp : Ctx} {x : Var} {ty : BTy} {od : Option ADec} (h : portOKB Cp x ty od = true) :
    ∃ VE U τ ts τ' E PE, od = some (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) ∧
      elabPort Cp x ty U = some (E, PE) ∧ closGroup [] VE = E.VE ∧ (portNodeVars E PE U).all rigidB = true := by
  unfold portOKB at h
  split at h
  · rename_i VE x' ty' U τ lv ts τ'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
    split at h
    · rename_i E PE hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨VE, U, τ, ts, τ', E, PE, rfl, hp, h.1, h.2⟩
    · cases h
  · cases h

theorem portOKB_tmpl {Cp : Ctx} {x : Var} {ty : BTy} {t : AExp} (h : portOKB Cp x ty (tmplDec t) = true) :
    ∃ VE U τ ts τ' t' E PE, t = .atexp (.letE (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) t') ∧
      elabPort Cp x ty U = some (E, PE) ∧ closGroup [] VE = E.VE ∧ (portNodeVars E PE U).all rigidB = true := by
  obtain ⟨VE, U, τ, ts, τ', E, PE, hd, hp, hv, hr⟩ := portOKB_inv h
  cases t with
  | atexp a =>
    cases a with
    | letE d t' =>
      simp only [tmplDec, Option.some.injEq] at hd
      subst hd
      exact ⟨VE, U, τ, ts, τ', t', E, PE, rfl, hp, hv, hr⟩
    | _ => simp [tmplDec] at hd
  | _ => simp [tmplDec] at hd

/-! ## A derivation of the declarations gives one of the nested `let`, ports included -/

theorem checkExp_letE {D : Ctx} {d : ADec} {e : AExp} :
    checkExp D (.atexp (.letE d e)) = (checkDec D d && okDecB d && checkExp (D.plusVE (d.result D)) e) := by
  simp only [checkExp, checkExpS, checkAtExp, okExpB, okAtExpB]
  have : ∀ e : AExp, okExpB e = true → e.ty.okB = true := okExpB_ty
  cases h1 : checkDec D d <;> cases h2 : okDecB d <;> cases h3 : checkExpS (D.plusVE (d.result D)) e <;>
    cases h4 : okExpB e <;> simp_all [AAtExp.ty]

theorem erase_portGroup (VE : ValEnv) (x : Var) (ty : BTy) (U : List BVar) (τ : Ty) (ts : List Ty) (τ' : Ty) :
    ADec.erase (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) = .val (portVB x ty) := by
  simp [ADec.erase, AValBind.erase, AValBind.eraseOpt, AExp.erase, AAtExp.erase, portVB]

/-- `toExp_check` with ports: a port's group is W's (the template `t`, checked in `Dw`). -/
theorem toExp_checkT {Cp : Ctx} (hp : ∀ v, v ∉ Cp.tyvars) : ∀ (ad : ATopDec) (C D Dw : Ctx) (E : Env) (PE : PortEnv)
    (e : BExp) (t : AExp),
    checkTopDec C ad = some (E, PE) → bodyExp ad.erase = some e → CEq C D → PA Cp C → PA Cp Dw →
    checkExp Dw t = true → portsOKB Cp ad.erase t = true →
      ∃ a', toExpA ad t = some a' ∧ checkExp D a' = true ∧ a'.erase = e
  | .value VE vb, C, D, Dw, E, PE, e, t, hc, hb, h, _, _, _, _ =>
    toExp_check (.value VE vb) C D E PE e t hc hb rfl h
  | .port x ty U, C, D, Dw, E, PE, e, t, hc, hb, h, hC, hDw, ht, hpo => by
    simp only [ATopDec.erase, bodyExp, Option.some.injEq] at hb
    subst hb
    simp only [ATopDec.erase, portsOKB] at hpo
    obtain ⟨VE, U', τ, ts, τ', t', E', PE', rfl, hel, hcl, -⟩ := portOKB_tmpl hpo
    have hD := hC.ofCEq h
    have hcd : checkDec D (.val VE (.var x (some (ty, U')) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) = true := by
      rw [checkExp_letE] at ht
      simp only [Bool.and_eq_true] at ht
      rw [checkDec_portGroup (hD.U.trans hDw.U.symm) (hD.QE.trans hDw.QE.symm) (hD.TE.trans hDw.TE.symm) hD.cl hDw.cl]
      exact ht.1.1
    have hok : okDecB (.val VE (.var x (some (ty, U')) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) = true := by
      rw [checkExp_letE] at ht; simp only [Bool.and_eq_true] at ht; exact ht.1.2
    refine ⟨_, rfl, ?_, by simp only [AExp.erase, AAtExp.erase, erase_portGroup]⟩
    rw [checkExp_letE]
    simp only [hcd, hok, Bool.true_and]
    simp [checkExp, checkExpS, checkAtExp, okExpB, okAtExpB, AAtExp.ty, unit_ok]
  | .seq a1 a2, C, D, Dw, E, PE, e, t, hc, hb, h, hC, hDw, ht, hpo => by
    obtain ⟨E1, PE1, E2, PE2, hc1, hc2⟩ := checkTopDec_seq hc
    cases a1 with
    | value VE vb =>
      simp only [ATopDec.erase, bodyExp] at hb
      simp only [ATopDec.erase, portsOKB] at hpo
      obtain ⟨e2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨hv, hve, hok, rfl⟩ := checkTopDec_value hc1
      have hv' : checkValBind (D.plusVE VE) vb = true := by rw [← cg_valBind vb (h.plusVE VE)]; exact hv
      have h2 : CEq (C.oplusE (Env.ofVE (closGroup C.tyvars VE))) (D.plusVE (ADec.result D (.val VE vb))) := by
        simp only [ADec.result]; rw [← h.closG VE]; exact h.oplus_plus _
      obtain ⟨a2', hx2, hc2', he2⟩ := toExp_checkT hp a2 _ _ (tmplCtx Dw t) E2 PE2 e2 (tmplBody t) hc2 hb2 h2
        (hC.oplusVE (closGroup_closed_of hC.cl VE)) (tmplCtx_PA hDw t) (tmpl_check ht) hpo
      refine ⟨.atexp (.letE (.val VE vb) a2'), by simp [toExpA, hx2], ?_,
        by simp [AExp.erase, AAtExp.erase, ADec.erase, he2]⟩
      rw [checkExp_letE]
      simp only [checkDec, hv', hve, decide_true, Bool.and_self, okDecB, hok, hc2']
    | port x ty U =>
      simp only [ATopDec.erase, bodyExp] at hb
      simp only [ATopDec.erase, portsOKB, Bool.and_eq_true] at hpo
      obtain ⟨e2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨VE, U', τ, ts, τ', t', E', PE', rfl, hel, hcl, -⟩ := portOKB_tmpl hpo.1
      have hD := hC.ofCEq h
      have hEq : elabPort C x ty U = elabPort Cp x ty U := hC.elabPort hp x ty U
      have hc1' : elabPort C x ty U = some (E1, PE1) := hc1
      have hUU : U = U' := by
        rw [elabPort_U hc1', elabPort_U hel, hC.U]
      subst hUU
      rw [hEq, hel] at hc1'
      cases hc1'
      rw [checkExp_letE] at ht
      simp only [Bool.and_eq_true] at ht
      have hcd : checkDec D (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) = true := by
        rw [checkDec_portGroup (hD.U.trans hDw.U.symm) (hD.QE.trans hDw.QE.symm) (hD.TE.trans hDw.TE.symm) hD.cl hDw.cl]
        exact ht.1.1
      have hres : ∀ D0 : Ctx, (∀ v, v ∉ D0.tyvars) →
          ADec.result D0 (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) = E1.VE := by
        intro D0 h0; simp only [ADec.result]; rw [closGroup_nil_of h0, hcl]
      have h2 : CEq (C.oplusE E1) (D.plusVE (ADec.result D
          (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)))) := by
        rw [hres D hD.cl, elabPort_ofVE hel]; exact h.oplus_plus _
      have hDw' : PA Cp (Dw.plusVE (ADec.result Dw
          (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)))) := by
        rw [hres Dw hDw.cl]; exact hDw.plusVE (elabPort_closed hp hel)
      have hC2 : PA Cp (C.oplusE E1) := by
        rw [elabPort_ofVE hel]; exact hC.oplusVE (elabPort_closed hp hel)
      obtain ⟨a2', hx2, hc2', he2⟩ := toExp_checkT hp a2 _ _ _ E2 PE2 e2 t' hc2 hb2 h2 hC2 hDw' ht.2 hpo.2
      refine ⟨.atexp (.letE (.val VE (.var x (some (ty, U)) τ (.atexp (.var ⟨none, x⟩ ts τ')) none)) a2'),
        by simp [toExpA, tmplDec, tmplBody, hx2], ?_,
        by simp only [AExp.erase, AAtExp.erase, erase_portGroup, he2]⟩
      rw [checkExp_letE]
      simp only [hcd, ht.1.2, hc2', Bool.and_self]
    | types _ _ _ _ | seq _ _ => simp [ATopDec.erase, bodyExp] at hb
  | .types _ _ _ _, _, _, _, _, _, _, _, _, hb, _, _, _, _, _ => by simp [ATopDec.erase, bodyExp] at hb

end MW
end StandardElm.Stat.Complete
