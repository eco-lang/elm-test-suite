/-
  A Standard Definition of Elm? Mechanisation: refutation for module-level W (milestone (f) of
  plan step 11, "Modules and programs"): if `inferModuleW` fails, the module has no derivation
  (`inferModuleW_fail`), and a program whose first module W refutes is not legal
  (`not_legal_of_wRefutes`). No principality hypothesis, and no coherence hypothesis: by ruling A98
  a module's type declarations are one phrase, elaborated whole.

  The argument. Take any derivation of the module (an annotated module step 9's checker accepts).
  Its type declarations give an environment `E'` that satisfies `r:sm-topdec-types`, as W's `E`
  does; the custom types' names of the two correspond, and a bijection of type names fixing the
  basis takes the derivation's names to W's (`types_rename`, from step 10's `Swap.extend_pairs`);
  renamed by it, the derivation is still one (`nr_checkTopDec`), and its type declarations now
  have W's names, so W's environment (`Types.checkTypes_unique`, the phrase being ordered). Its
  value declarations, checked in `C ⊕ E`, give a derivation of the nested `let` W elaborated
  (`toExp_check`, by `CEq`), which W's refutation for expressions excludes (`WE.weRefutation`).
-/
import StandardElmMech.Stat.Complete.ModulesCongr
import StandardElmMech.Stat.Complete.WETheorems
import StandardElmMech.Stat.ModuleStep
import StandardElmMech.Stat.Refusals

namespace StandardElm.Stat.Complete
namespace MW
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtExp BExp BDec BValBind BTopDec BModule BProgram BDatBind BTypBind)

/-! ## The root context -/

theorem mem_of_find? {K V : Type} [DecidableEq K] {k : K} {v : V} : ∀ {f : FMap K V}, f.find? k = some v → (k, v) ∈ f
  | [], h => by cases h
  | (k', v') :: r, h => by
    simp only [FMap.find?] at h
    split at h
    · rename_i e; subst e; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_find? h)

theorem schemeOKB_sound {σ : Scheme} (h : schemeOKB σ = true) :
    (∀ v ∈ σ.bound, v.isBnd = true) ∧ ∀ v ∈ σ.body.vars, v ∉ σ.bound → v.isBnd = false := by
  simp only [schemeOKB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  exact ⟨h.1, fun v hv hb => (h.2 v hv).resolve_left hb⟩

theorem rootOKB_sound {C : Ctx} (h : rootOKB C = true) : RootOKD C := by
  intro lv σ st hl
  simp only [rootOKB, Bool.and_eq_true, List.all_eq_true] at h
  apply schemeOKB_sound
  simp only [Ctx.lookupVal, Env.lookupVal] at hl
  split at hl
  · exact h.1 _ (mem_of_find? hl)
  · rename_i m _
    cases hq : C.E.QE.find? m with
    | none => rw [hq] at hl; cases hl
    | some I =>
      rw [hq] at hl
      exact h.2 _ (mem_of_find? hq) _ (mem_of_find? hl)

/-! ## The value declarations as a nested `let` -/

theorem okExpB_ty : ∀ e : AExp, okExpB e = true → e.ty.okB = true
  | .atexp a, h | .app _ a, h | .lam _ _, h | .caseE _ _, h => by
    simp only [okExpB, Bool.and_eq_true] at h
    first | exact h.1 | exact h.1.1 | exact h.1.1.1

theorem unit_ok : tUnitTy.okB = true := by decide

theorem checkTopDec_value {C : Ctx} {VE : ValEnv} {vb : AValBind} {E : Env} {PE : PortEnv}
    (h : checkTopDec C (.value VE vb) = some (E, PE)) :
    checkValBind (C.plusVE VE) vb = true ∧ vb.ve = VE ∧ okValBindB vb = true ∧
      E = Env.ofVE (closGroup C.tyvars VE) := by
  simp only [checkTopDec] at h
  split at h
  · rename_i hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hk.1.1, hk.1.2, hk.2, h.1.symm⟩
  · cases h

theorem checkTopDec_seq {C : Ctx} {a1 a2 : ATopDec} {E : Env} {PE : PortEnv}
    (h : checkTopDec C (.seq a1 a2) = some (E, PE)) :
    ∃ E1 PE1 E2 PE2, checkTopDec C a1 = some (E1, PE1) ∧ checkTopDec (C.oplusE E1) a2 = some (E2, PE2) := by
  simp only [checkTopDec] at h
  cases h1 : checkTopDec C a1 with
  | none => rw [h1] at h; cases h
  | some p =>
    obtain ⟨E1, PE1⟩ := p
    rw [h1] at h
    simp only at h
    cases h2 : checkTopDec (C.oplusE E1) a2 with
    | none => rw [h2] at h; cases h
    | some q => exact ⟨E1, PE1, q.1, q.2, rfl, h2⟩

theorem checkTopDec_types {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    {E : Env} {PE : PortEnv} (h : checkTopDec C (.types TE VE db tbs) = some (E, PE)) :
    checkTypes C TE VE db tbs = true ∧ E = ⟨[], TE, VE⟩ := by
  simp only [checkTopDec] at h
  split at h
  · rename_i hk; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨hk, h.1.symm⟩
  · cases h

/-- A derivation of a module's value declarations (no port), in a context the checker cannot tell
    from `D`, gives a derivation of the nested `let` in `D` (any template). -/
theorem toExp_check : ∀ (ad : ATopDec) (C D : Ctx) (E : Env) (PE : PortEnv) (e : BExp) (t : AExp),
    checkTopDec C ad = some (E, PE) → bodyExp ad.erase = some e → hasPortB ad.erase = false → CEq C D →
      ∃ a', toExpA ad t = some a' ∧ checkExp D a' = true ∧ a'.erase = e
  | .value VE vb, C, D, E, PE, e, t, hc, hb, _, h => by
    simp only [ATopDec.erase, bodyExp, Option.some.injEq] at hb
    subst hb
    obtain ⟨hv, hve, hok, -⟩ := checkTopDec_value hc
    have hv' : checkValBind (D.plusVE VE) vb = true := by rw [← cg_valBind vb (h.plusVE VE)]; exact hv
    refine ⟨.atexp (.letE (.val VE vb) (.atexp .unit)), rfl, ?_, rfl⟩
    simp [checkExp, checkExpS, checkAtExp, checkDec, okExpB, okAtExpB, okDecB, AAtExp.ty, AExp.ty,
      hv', hve, hok, unit_ok]
  | .seq a1 a2, C, D, E, PE, e, t, hc, hb, hp, h => by
    cases a1 with
    | value VE vb =>
      simp only [ATopDec.erase, bodyExp] at hb
      simp only [ATopDec.erase, hasPortB, Bool.false_or] at hp
      obtain ⟨e2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨E1, PE1, E2, PE2, hc1, hc2⟩ := checkTopDec_seq hc
      obtain ⟨hv, hve, hok, rfl⟩ := checkTopDec_value hc1
      have hv' : checkValBind (D.plusVE VE) vb = true := by rw [← cg_valBind vb (h.plusVE VE)]; exact hv
      have h2 : CEq (C.oplusE (Env.ofVE (closGroup C.tyvars VE))) (D.plusVE (ADec.result D (.val VE vb))) := by
        simp only [ADec.result]; rw [← h.closG VE]; exact h.oplus_plus _
      obtain ⟨a2', hx2, hc2', he2⟩ := toExp_check a2 _ _ E2 PE2 e2 (tmplBody t) hc2 hb2 hp h2
      refine ⟨.atexp (.letE (.val VE vb) a2'), by simp [toExpA, hx2], ?_,
        by simp [AExp.erase, AAtExp.erase, ADec.erase, he2]⟩
      simp only [checkExp, Bool.and_eq_true] at hc2'
      have := okExpB_ty a2' hc2'.2
      simp [checkExp, checkExpS, checkAtExp, checkDec, okExpB, okAtExpB, okDecB, AAtExp.ty,
        hv', hve, hok, hc2'.1, hc2'.2, this]
    | port _ _ _ => simp [ATopDec.erase, hasPortB] at hp
    | types _ _ _ _ | seq _ _ =>
      simp [ATopDec.erase, bodyExp] at hb
  | .port _ _ _, _, _, _, _, _, _, _, _, hp, _ => by simp [ATopDec.erase, hasPortB] at hp
  | .types _ _ _ _, _, _, _, _, _, _, _, hb, _, _ => by
    simp [ATopDec.erase, bodyExp] at hb

/-! ## Type declarations: renaming a derivation's names to W's -/

theorem dat_names {C : Ctx} {names : String → Option TyName} : ∀ {d : BDatBind} {VE' : ValEnv} {TE' : TyEnv},
    elabDatBind C names d = some (VE', TE') → (d.map (·.1)).Nodup →
    ∃ ts : List TyName, d.map (fun e => names e.1) = ts.map some ∧ ts.Nodup ∧
      d.map (fun e => e.2.1.length) = ts.map (·.arity)
  | [], _, _, _, _ => ⟨[], rfl, .nil, rfl⟩
  | (c, ps, cb) :: rest, VE', TE', h, hn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [elabDatBind] at h
    split at h
    · cases h
    rename_i t ht
    split at h
    · rename_i τs VE1 TE1 h1 h2
      split at h
      · split at h
        · rename_i hc
          obtain ⟨ts, e1, e2, e3⟩ := dat_names h2 hn.2
          refine ⟨t :: ts, by simp [ht, e1], List.nodup_cons.mpr ⟨?_, e2⟩, by simp [hc.2.1, e3]⟩
          intro hm
          have : some t ∈ rest.map (fun e => names e.1) := by rw [e1]; exact List.mem_map_of_mem hm
          obtain ⟨e, he, het⟩ := List.mem_map.mp this
          obtain ⟨t2, ht2, s, hs, es⟩ := Types.elabDatBind_names h2 hn.2 e he
          rw [het] at ht2; cases ht2
          exact hc.2.2 s hs es
        · cases h
      · cases h
    · cases h

theorem map_eq_of_zip {β : Type} (f : TyName → β) : ∀ (l1 l2 : List TyName), l1.map f = l2.map f →
    ∀ p ∈ l1.zip l2, f p.2 = f p.1
  | [], _, _, _, hp => by simp at hp
  | _ :: _, [], _, _, hp => by simp at hp
  | a :: as, b :: bs, h, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1.symm
    · exact map_eq_of_zip f as bs h.2 p hp

theorem names_corr {X : Type} (g' g : X → Option TyName) (f : TyName → TyName) :
    ∀ (d : List X) (ts' ts : List TyName), d.map g' = ts'.map some → d.map g = ts.map some →
      (∀ p ∈ ts'.zip ts, f p.1 = p.2) → ∀ e ∈ d, (g' e).map f = g e
  | [], _, _, _, _, _, e, he => by simp at he
  | _ :: _, [], _, h1, _, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, h2, _, _, _ => by simp at h2
  | x :: d, t' :: ts', t :: ts, h1, h2, hf, e, he => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    rcases List.mem_cons.mp he with rfl | he
    · rw [h1.1, h2.1, Option.map_some, hf (t', t) List.mem_cons_self]
    · exact names_corr g' g f d ts' ts h1.2 h2.2 (fun p hp => hf p (List.mem_cons_of_mem _ hp)) e he

/-- The names a checked type declaration gives its custom types: one each, distinct, of the
    custom type's arity, new for `C`. -/
theorem checked_names {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (h : checkTypes C TE VE db tbs = true) (hnd : ((db.getD []).map (·.1)).Nodup) :
    ∃ ts : List TyName, (db.getD []).map (fun e => namesOf TE e.1) = ts.map some ∧ ts.Nodup ∧
      (db.getD []).map (fun e => e.2.1.length) = ts.map (·.arity) ∧ ∀ t ∈ ts, t ∉ C.T := by
  obtain ⟨VEs, TEs, VEd, TEd, -, -, hd, -, -⟩ := Types.fix_parts (checkTypes_fix h)
  cases db with
  | none => exact ⟨[], rfl, .nil, rfl, by simp⟩
  | some d =>
    obtain ⟨hel, hnew⟩ := hd d rfl
    obtain ⟨ts, e1, e2, e3⟩ := dat_names hel hnd
    refine ⟨ts, e1, e2, e3, fun t ht => ?_⟩
    have : some t ∈ d.map (fun e => namesOf TE e.1) := by
      rw [e1]; exact List.mem_map_of_mem ht
    obtain ⟨e, he, het⟩ := List.mem_map.mp this
    obtain ⟨t2, ht2, s, hs, es⟩ := Types.elabDatBind_names hel hnd e he
    rw [het] at ht2; cases ht2
    exact namesNewB_spec _ _ hnew s hs t (by rw [es, Types.name?_toFcn])

/-- Two solutions of a module's ordered type declarations in the context of its imports differ by a
    bijection of type names that fixes the basis and takes the first's custom types' names `ts'` to
    the second's `ts`, in order. -/
theorem types_bij {B : SBasis} (hB : BasisInv B) {imps : List Src.BImport} {C : Ctx}
    (hC : importCtx B imps = some C) {TE' TE : TyEnv} {VE' VE : ValEnv} {db : Option BDatBind}
    {tbs : List BTypBind} (h' : checkTypes C TE' VE' db tbs = true) (h : checkTypes C TE VE db tbs = true)
    (ho : typesOrdered db tbs = true) :
    ∃ (σ σ' : List (TyName × TyName)) (ts' ts : List TyName), NRInv σ σ' ∧ (nr σ).basis B = B ∧ (nr σ).ctx C = C ∧
      (nr σ).tyEnv TE' = TE ∧ (nr σ).valEnv VE' = VE ∧
      (db.getD []).map (fun e => namesOf TE' e.1) = ts'.map some ∧
      (db.getD []).map (fun e => namesOf TE e.1) = ts.map some ∧
      (∀ p ∈ ts'.zip ts, (nr σ).tnApply p.1 = p.2) ∧ ts'.length = ts.length ∧ ts'.Nodup ∧ ts.Nodup ∧
      (∀ t ∈ ts', t ∉ B.T) ∧ (∀ t ∈ ts, t ∉ B.T) := by
  obtain ⟨hcl, -, hCT⟩ := Closed.importCtx_closed hB.closed hC
  obtain ⟨hnd, -⟩ := Types.typesOrdered_dec ho
  have hndd : ((db.getD []).map (·.1)).Nodup := (List.nodup_append.mp hnd).1
  obtain ⟨ts', e1', n1', a1', new1'⟩ := checked_names h' hndd
  obtain ⟨ts, e1, n1, a1, new1⟩ := checked_names h hndd
  have hl : ts'.length = ts.length := by
    have l1 := congrArg List.length a1'; have l2 := congrArg List.length a1
    simp only [List.length_map] at l1 l2; omega
  let ν := ts'.zip ts
  have hfst : ν.map (·.1) = ts' := List.map_fst_zip (by omega)
  have hsnd : ν.map (·.2) = ts := List.map_snd_zip (by omega)
  have har : ∀ p ∈ ν, p.2.arity = p.1.arity := map_eq_of_zip (·.arity) ts' ts (by rw [← a1', a1])
  have h0 : ∀ p ∈ ν, p.1 ∉ T0 ∧ p.2 ∉ T0 := fun p hp => by
    have m1 : p.1 ∈ ts' := hfst ▸ List.mem_map_of_mem hp
    have m2 : p.2 ∈ ts := hsnd ▸ List.mem_map_of_mem hp
    exact ⟨fun h0 => new1' _ m1 (hCT ▸ hB.t0 _ h0), fun h0 => new1 _ m2 (hCT ▸ hB.t0 _ h0)⟩
  obtain ⟨σ, σ', hσ, hpair, hfix⟩ := Swap.extend_pairs ν (hfst ▸ n1') (hsnd ▸ n1) har h0 B.T
  have fixB : ∀ t ∈ B.T, (nr σ).tnApply t = t := fun t ht =>
    hfix t ht (fun hm => new1' t (hfst ▸ hm) (hCT ▸ ht)) (fun hm => new1 t (hsnd ▸ hm) (hCT ▸ ht))
  have hσB := Walk.nr_fix_basis hB fixB
  have hσC : (nr σ).ctx C = C := by
    have := nr_importCtx hσ.h B imps
    rw [hσB, hC] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact this.symm
  have hc2 : checkTypes C ((nr σ).tyEnv TE') ((nr σ).valEnv VE') db tbs = true := by
    rw [← nr_checkTypes hσ.h C TE' VE' db tbs] at h'; rw [hσC] at h'; exact h'
  have hn : ∀ e ∈ db.getD [], namesOf ((nr σ).tyEnv TE') e.1 = namesOf TE e.1 := fun e he => by
    rw [nr_namesOf hσ.h]
    exact names_corr _ _ _ _ ts' ts e1' e1 (fun p hp => hpair p hp) e he
  obtain ⟨eT, eV⟩ := Types.checkTypes_unique hcl hc2 h ho hn
  exact ⟨σ, σ', ts', ts, hσ, hσB, hσC, eT, eV, e1', e1, fun p hp => hpair p hp, hl, n1', n1,
    fun t ht => hCT ▸ new1' t ht, fun t ht => hCT ▸ new1 t ht⟩

/-- Two solutions of a module's ordered type declarations in the context of its imports differ by a
    bijection of type names that fixes the basis. -/
theorem types_rename {B : SBasis} (hB : BasisInv B) {imps : List Src.BImport} {C : Ctx}
    (hC : importCtx B imps = some C) {TE' TE : TyEnv} {VE' VE : ValEnv} {db : Option BDatBind}
    {tbs : List BTypBind} (h' : checkTypes C TE' VE' db tbs = true) (h : checkTypes C TE VE db tbs = true)
    (ho : typesOrdered db tbs = true) :
    ∃ σ, NR σ ∧ (nr σ).ctx C = C ∧ (nr σ).tyEnv TE' = TE ∧ (nr σ).valEnv VE' = VE := by
  obtain ⟨σ, _σ', _ts', _ts, hσ, -, hσC, eT, eV, -⟩ := types_bij hB hC h' h ho
  exact ⟨σ, hσ.h, hσC, eT, eV⟩

/-! ## W's failure -/

theorem finish_ne_fail (B : SBasis) (a : AModule) : finish B a ≠ .fail := by
  unfold finish; split <;> simp

theorem valuesW_fail {fuel : Nat} {B : SBasis} {m : BModule} {at? : Option ATopDec} {C1 : Ctx}
    {rest : Option BTopDec} (h : valuesW fuel B m at? C1 rest = .fail) :
    ∃ r e, rest = some r ∧ bodyExp r = some e ∧ rootOKB C1 = true ∧ WE.inferExpWD fuel C1 e = .fail ∧
      hasPortB r = false := by
  unfold valuesW at h
  split at h
  · exact absurd h (finish_ne_fail _ _)
  · rename_i r
    split at h
    · cases h
    · rename_i e he
      split at h
      · rename_i hroot
        split at h
        · split at h
          · split at h
            · exact absurd h (finish_ne_fail _ _)
            · cases h
          · cases h
        · rename_i hw
          split at h
          · cases h
          · rename_i hp
            exact ⟨r, e, rfl, he, hroot, hw, by simpa using hp⟩
        · cases h
        · cases h
        · cases h
      · cases h

theorem typesPart_some {C C1 : Ctx} {ts : Option (Option BDatBind × List BTypBind)} {at? : Option ATopDec}
    (h : typesPart C ts = some (at?, C1)) :
    (ts = none ∧ C1 = C) ∨ ∃ db tbs TE VE, ts = some (db, tbs) ∧ typesW C db tbs = some (TE, VE) ∧
      C1 = C.oplusE ⟨[], TE, VE⟩ := by
  cases ts with
  | none => simp only [typesPart, Option.some.injEq, Prod.mk.injEq] at h; exact .inl ⟨rfl, h.2.symm⟩
  | some q =>
    obtain ⟨db, tbs⟩ := q
    simp only [typesPart] at h
    split at h
    · rename_i TE VE ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact .inr ⟨db, tbs, TE, VE, rfl, ht, h.2.symm⟩
    · cases h

/-- What W's failure on a module says. -/
theorem inferModuleW_fail_inv {fuel : Nat} {B : SBasis} {m : BModule} (h : inferModuleW fuel B m = .fail) :
    ∃ C d r e C1, importCtx B m.imports = some C ∧ m.body = some d ∧ (splitBody d).2 = some r ∧
      bodyExp r = some e ∧ rootOKB C1 = true ∧ WE.inferExpWD fuel C1 e = .fail ∧ hasPortB r = false ∧
      (((splitBody d).1 = none ∧ C1 = C) ∨
        ∃ db tbs TE VE, (splitBody d).1 = some (db, tbs) ∧ typesW C db tbs = some (TE, VE) ∧
          C1 = C.oplusE ⟨[], TE, VE⟩) := by
  unfold inferModuleW at h
  split at h
  · cases h
  · rename_i C hC
    split at h
    · exact absurd h (finish_ne_fail _ _)
    · rename_i d hd
      split at h
      · cases h
      · rename_i at? C1 hty
        obtain ⟨r, e, hr, he, hroot, hw, hp⟩ := valuesW_fail h
        exact ⟨C, d, r, e, C1, hC, hd, hr, he, hroot, hw, hp, typesPart_some hty⟩

theorem typesW_spec {C : Ctx} {db : Option BDatBind} {tbs : List BTypBind} {TE : TyEnv} {VE : ValEnv}
    (h : typesW C db tbs = some (TE, VE)) :
    checkTypes C TE VE db tbs = true ∧ typesOrdered db tbs = true ∧ typesBndB TE VE = true := by
  unfold typesW at h
  split at h
  · split at h
    · rename_i hc; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hc
      exact ⟨hc.1.1, hc.1.2, hc.2⟩
    · cases h
  · cases h

/-- Refutation for modules (section 7, "Modules"): if W fails on a module, no derivation of it
    checks. -/
theorem inferModuleW_fail {fuel : Nat} {B : SBasis} {m : BModule} (hB : BasisInv B)
    (h : inferModuleW fuel B m = .fail) : NoDeriv B m := by
  obtain ⟨C, d, r, e, C1, hC, hd, hr, he, hroot, hw, hp, hty⟩ := inferModuleW_fail_inv h
  intro a hae
  cases hc : checkModule B a with
  | false => rfl
  | true =>
    exfalso
    have himp : a.imports = m.imports := by rw [← hae]; rfl
    have hbody : a.body.map ATopDec.erase = m.body := by rw [← hae]; rfl
    obtain ⟨ad, had, hade⟩ : ∃ ad, a.body = some ad ∧ ad.erase = d := by
      rw [hd] at hbody
      obtain ⟨ad, h1, h2⟩ := Option.map_eq_some_iff.mp hbody
      exact ⟨ad, h1, h2⟩
    have hCa : importCtx B a.imports = some C := by rw [himp]; exact hC
    unfold checkModule at hc
    rw [AModule.result_of_ctx hCa] at hc
    obtain ⟨⟨B', E⟩, hres⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨PE, I, hk, -, -⟩ := MStep.resultIn_inv hres
    rw [had] at hk
    simp only [checkTopDecOpt] at hk
    have hRoot := rootOKB_sound hroot
    rcases hty with ⟨hs, hC1⟩ | ⟨db, tbs, TE, VE, hs, htw, rfl⟩
    · -- no type declarations: the body is the value declarations
      subst C1
      have hrd : r = d := by
        cases d with
        | types _ _ => simp [splitBody] at hs
        | seq d1 d2 =>
          cases d1 <;> simp only [splitBody, Option.some.injEq, reduceCtorEq] at hs hr <;> exact hr.symm
        | value _ | port _ _ => simp only [splitBody, Option.some.injEq] at hr; exact hr.symm
      subst hrd
      obtain ⟨a', -, hca', hea'⟩ := toExp_check ad C C E PE e (.atexp .unit) hk (by rw [hade]; exact he)
        (by rw [hade]; exact hp) (CEq.refl C)
      exact WE.weRefutation fuel C e hRoot hw ⟨a', hca', hea'⟩
    · obtain ⟨hct, hord, -⟩ := typesW_spec htw
      have hdr : d = .seq (.types db tbs) r := by
        cases d with
        | types _ _ => simp [splitBody] at hr
        | seq d1 d2 =>
          cases d1 with
          | types db' tbs' =>
            simp only [splitBody, Option.some.injEq, Prod.mk.injEq] at hs hr
            obtain ⟨rfl, rfl⟩ := hs; rw [hr]
          | value _ | port _ _ | seq _ _ => simp [splitBody] at hs
        | value _ | port _ _ => simp [splitBody] at hs
      subst hdr
      cases ad with
      | seq a1 a2 =>
        cases a1 with
        | types TE' VE' db' tbs' =>
          simp only [ATopDec.erase, BTopDec.seq.injEq, BTopDec.types.injEq] at hade
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hade
          obtain ⟨E1, PE1, E2, PE2, hk1, hk2⟩ := checkTopDec_seq hk
          obtain ⟨hct', rfl⟩ := checkTopDec_types hk1
          obtain ⟨σ, hσ, hσC, eT, eV⟩ := types_rename hB hC hct' hct hord
          have hk3 := nr_checkTopDec hσ a2 (C.oplusE ⟨[], TE', VE'⟩)
          rw [hk2, ← nr_oplusE hσ, hσC] at hk3
          have hEnv : (nr σ).env (⟨[], TE', VE'⟩ : Env) = ⟨[], TE, VE⟩ := by
            simp only [Renaming.env, List.map_nil, eT, eV]
          rw [hEnv] at hk3
          obtain ⟨a', -, hca', hea'⟩ := toExp_check ((nr σ).topDec a2) _ _ _ _ e (.atexp .unit) hk3
            (by rw [erase_topDec]; exact he) (by rw [erase_topDec]; exact hp) (CEq.refl _)
          exact WE.weRefutation fuel _ e hRoot hw ⟨a', hca', hea'⟩
        | value _ _ | port _ _ _ | seq _ _ =>
          simp [ATopDec.erase] at hade
      | value _ _ | types _ _ _ _ | port _ _ _ =>
        simp [ATopDec.erase] at hade

end MW
end StandardElm.Stat.Complete

