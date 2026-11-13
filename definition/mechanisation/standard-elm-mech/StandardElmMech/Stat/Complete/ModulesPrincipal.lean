/-
  A Standard Definition of Elm? Mechanisation: principality of module-level W (milestone (f) of
  plan step 11, "Modules and programs"): what `inferModuleW` returns is a derivation of the module
  of which every derivation is an instance (`IsPrincipalMod`, sec:static-modules-principal), and a
  program's derivation W returns gives every module a principal derivation in the basis the
  earlier ones build (`PrincipalProgDeriv`).

  The argument for a module, given any derivation `a'` of it:
  * L14 (`types_bij`): `a'`'s type declarations are W's up to a bijection `σ` of type names fixing
    the basis; `a'' = a'` renamed by `σ` is a derivation with W's type declarations.
  * L11 at the root (`WE.wePrincipalityA`): the nested `let` of `a''`'s value declarations is an
    instance of W's, by a substitution `S` that leaves the type declarations' node alone (its
    variables are `bnd`, checked by `typesW`).
  * Section 9's node correspondence (`pi_values`, ModulesNodes.lean): the module nodes of `a''` are
    then instances of W's by `S`, node by node.
  * L16 (`transport`): renaming back by `σ⁻¹` makes `a'` an instance of W's derivation up to the
    bijection between the custom types' names (the names at W's nodes are the basis's and the
    module's own, checked by `finish`).
-/
import StandardElmMech.Stat.Complete.ModulesNodes
import StandardElmMech.Stat.Complete.ModulesPrincipalExp
import StandardElmMech.Stat.Complete.CheckedDeriv

namespace StandardElm.Stat.Complete
namespace MW
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtExp BExp BDec BValBind BTopDec BModule BProgram BDatBind BTypBind)

/-! ## The nested `let` and the module's declarations -/

theorem isUnitE_eq {e : AExp} (h : isUnitE e = true) : e = .atexp .unit := by
  cases e with
  | atexp a => cases a <;> simp_all [isUnitE]
  | _ => simp [isUnitE] at h

theorem unLet_inv {r : BTopDec} {ae : AExp} {av : ATopDec} (h : unLet r ae = some av) :
    (∃ vb VE vab, r = .value vb ∧ ae = .atexp (.letE (.val VE vab) (.atexp .unit)) ∧ av = .value VE vab) ∨
    (∃ x t VE vab, r = .port x t ∧ ae = .atexp (.letE (.val VE vab) (.atexp .unit)) ∧ av = .port x t (annUOf vab)) ∨
    (∃ vb r2 VE vab e av2, r = .seq (.value vb) r2 ∧ ae = .atexp (.letE (.val VE vab) e) ∧ unLet r2 e = some av2 ∧
      av = .seq (.value VE vab) av2) ∨
    (∃ x t r2 VE vab e av2, r = .seq (.port x t) r2 ∧ ae = .atexp (.letE (.val VE vab) e) ∧ unLet r2 e = some av2 ∧
      av = .seq (.port x t (annUOf vab)) av2) := by
  unfold unLet at h
  split at h
  · split at h
    · rename_i hu; cases h; exact .inl ⟨_, _, _, rfl, by rw [isUnitE_eq hu], rfl⟩
    · cases h
  · split at h
    · rename_i hu; cases h; exact .inr (.inl ⟨_, _, _, _, rfl, by rw [isUnitE_eq hu], rfl⟩)
    · cases h
  · obtain ⟨av2, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, h2, rfl⟩))
  · obtain ⟨av2, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, rfl, rfl, h2, rfl⟩))
  · cases h

theorem toExpA_of_unLet : ∀ (r : BTopDec) (ae : AExp) (av : ATopDec), unLet r ae = some av → toExpA av ae = some ae
  | r, ae, av, h => by
    rcases unLet_inv h with ⟨vb, VE, vab, rfl, rfl, rfl⟩ | ⟨x, t, VE, vab, rfl, rfl, rfl⟩ |
        ⟨vb, r2, VE, vab, e, av2, rfl, rfl, h2, rfl⟩ | ⟨x, t, r2, VE, vab, e, av2, rfl, rfl, h2, rfl⟩
    · rfl
    · rfl
    · simp [toExpA, tmplBody, toExpA_of_unLet r2 e av2 h2]
    · simp [toExpA, tmplBody, tmplDec, toExpA_of_unLet r2 e av2 h2]

/-- W's declarations from its nested `let` erase to the module's. -/
theorem unLet_erase : ∀ (r : BTopDec) (e : BExp) (ae : AExp) (av : ATopDec), bodyExp r = some e → ae.erase = e →
    unLet r ae = some av → av.erase = r
  | r, e, ae, av, hb, he, h => by
    rcases unLet_inv h with ⟨vb, VE, vab, rfl, rfl, rfl⟩ | ⟨x, t, VE, vab, rfl, rfl, rfl⟩ |
        ⟨vb, r2, VE, vab, e', av2, rfl, rfl, h2, rfl⟩ | ⟨x, t, r2, VE, vab, e', av2, rfl, rfl, h2, rfl⟩
    · simp only [bodyExp, Option.some.injEq] at hb
      subst hb
      simp only [AExp.erase, AAtExp.erase, ADec.erase, BExp.atexp.injEq, BAtExp.letE.injEq, BDec.val.injEq] at he
      simp only [ATopDec.erase, he.1]
    · rfl
    · simp only [bodyExp] at hb
      obtain ⟨e2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb
      simp only [AExp.erase, AAtExp.erase, ADec.erase, BExp.atexp.injEq, BAtExp.letE.injEq, BDec.val.injEq] at he
      simp only [ATopDec.erase, he.1, unLet_erase r2 e2 e' av2 hb2 he.2 h2]
    · simp only [bodyExp] at hb
      obtain ⟨e2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb
      simp only [AExp.erase, AAtExp.erase, BExp.atexp.injEq, BAtExp.letE.injEq] at he
      simp only [ATopDec.erase, unLet_erase r2 e2 e' av2 hb2 he.2 h2]

/-- The ports' variables of W's declarations are `bnd` or named. -/
theorem portsVars_rigid {Cp : Ctx} : ∀ (r : BTopDec) (ae : AExp) (av : ATopDec), unLet r ae = some av →
    portsOKB Cp r ae = true → ∀ v ∈ portsVars Cp av, rigidB v = true
  | r, ae, av, h, hp, v, hv => by
    rcases unLet_inv h with ⟨vb, VE, vab, rfl, rfl, rfl⟩ | ⟨x, t, VE, vab, rfl, rfl, rfl⟩ |
        ⟨vb, r2, VE, vab, e, av2, rfl, rfl, h2, rfl⟩ | ⟨x, t, r2, VE, vab, e, av2, rfl, rfl, h2, rfl⟩
    · simp [portsVars] at hv
    · simp only [portsOKB, tmplDec] at hp
      obtain ⟨VE', U, τ, ts, τ', E, PE, hd, hel, -, hr⟩ := portOKB_inv hp
      simp only [Option.some.injEq, ADec.val.injEq] at hd
      obtain ⟨-, rfl⟩ := hd
      simp only [portsVars, annUOf, annU, hel] at hv
      exact List.all_eq_true.mp hr v hv
    · simp only [portsOKB, tmplBody] at hp
      simp only [portsVars, List.nil_append] at hv
      exact portsVars_rigid r2 e av2 h2 hp v hv
    · simp only [portsOKB, tmplBody, tmplDec, Bool.and_eq_true] at hp
      simp only [portsVars, List.mem_append] at hv
      rcases hv with hv | hv
      · obtain ⟨VE', U, τ, ts, τ', E, PE, hd, hel, -, hr⟩ := portOKB_inv hp.1
        simp only [Option.some.injEq, ADec.val.injEq] at hd
        obtain ⟨-, rfl⟩ := hd
        simp only [annUOf, annU, hel] at hv
        exact List.all_eq_true.mp hr v hv
      · exact portsVars_rigid r2 e av2 h2 hp.2 v hv

/-! ## W's answer -/

theorem finish_ok {B : SBasis} {a a' : AModule} (h : finish B a = .ok a') :
    a' = a ∧ checkModule B a = true ∧ namesB B a = true := by
  unfold finish at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true] at hc; cases h; exact ⟨rfl, hc.1, hc.2⟩
  · cases h

theorem valuesW_ok {fuel : Nat} {B : SBasis} {m : BModule} {at? : Option ATopDec} {C1 : Ctx}
    {rest : Option BTopDec} {a : AModule} (h : valuesW fuel B m at? C1 rest = .ok a) :
    checkModule B a = true ∧ namesB B a = true ∧ a.header = m.header ∧ a.imports = m.imports ∧
      ((rest = none ∧ a.body = joinBody at? none) ∨
        ∃ r e ae av, rest = some r ∧ bodyExp r = some e ∧ rootOKB C1 = true ∧
          WE.inferExpWD fuel C1 e = .ok ae ∧ unLet r ae = some av ∧ portsOKB C1 r ae = true ∧
          a.body = joinBody at? (some av)) := by
  unfold valuesW at h
  split at h
  · obtain ⟨rfl, hc, hn⟩ := finish_ok h
    exact ⟨hc, hn, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  · rename_i r
    split at h
    · cases h
    · rename_i e he
      split at h
      · rename_i hroot
        split at h
        · rename_i ae hw
          split at h
          · rename_i av hu
            split at h
            · rename_i hpo
              obtain ⟨rfl, hc, hn⟩ := finish_ok h
              exact ⟨hc, hn, rfl, rfl, .inr ⟨r, e, ae, av, rfl, he, hroot, hw, hu, hpo, rfl⟩⟩
            · cases h
          · cases h
        · split at h <;> cases h
        · cases h
        · cases h
        · cases h
      · cases h

/-- What W's success on a module says. -/
theorem inferModuleW_ok_inv {fuel : Nat} {B : SBasis} {m : BModule} {a : AModule} (h : inferModuleW fuel B m = .ok a) :
    ∃ C, importCtx B m.imports = some C ∧ checkModule B a = true ∧ namesB B a = true ∧
      a.header = m.header ∧ a.imports = m.imports ∧
      ((m.body = none ∧ a.body = none) ∨
        ∃ d at? C1, m.body = some d ∧ typesPart C (splitBody d).1 = some (at?, C1) ∧
          (((splitBody d).2 = none ∧ a.body = joinBody at? none) ∨
            ∃ r e ae av, (splitBody d).2 = some r ∧ bodyExp r = some e ∧ rootOKB C1 = true ∧
              WE.inferExpWD fuel C1 e = .ok ae ∧ unLet r ae = some av ∧ portsOKB C1 r ae = true ∧
              a.body = joinBody at? (some av))) := by
  unfold inferModuleW at h
  split at h
  · cases h
  · rename_i C hC
    split at h
    · rename_i hd
      obtain ⟨rfl, hc, hn⟩ := finish_ok h
      exact ⟨C, hC, hc, hn, rfl, rfl, .inl ⟨hd, rfl⟩⟩
    · rename_i d hd
      split at h
      · cases h
      · rename_i at? C1 hty
        obtain ⟨hc, hn, hh, hi, hr⟩ := valuesW_ok h
        exact ⟨C, hC, hc, hn, hh, hi, .inr ⟨d, at?, C1, hd, hty, hr⟩⟩

/-! ## Instances of nodes -/

/-- A node whose variables the substitution leaves alone is an instance of itself. -/
theorem nodeInstance_fixed {S : Subst} {n : Node} (hU : n.U = [])
    (hfix : ∀ τ ∈ n.tys ++ n.schemes.map (·.body), ∀ v ∈ τ.vars, v ∉ S.dom) : NodeInstance S n n := by
  refine ⟨⟨[], by rw [hU]; rfl, fun x => by rw [hU]⟩, ?_, rfl, fun i hi _ τ hg => ⟨n.schemes[i], ?_, hg⟩⟩
  · have := mapM_some S.apply id n.tys fun τ hτ => apply_fix S τ (hfix τ (List.mem_append_left _ hτ))
    rwa [List.map_id] at this
  · simp only [Subst.applyScheme]
    rw [apply_fix S _ (hfix _ (List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hi))))]
    rfl

theorem renameNames_id_nil (n : Node) : n.renameNames [] = n := by
  rw [node_renameNames]
  obtain ⟨p, U, ts, ss⟩ := n
  simp only [Node.mk.injEq, true_and]
  refine ⟨?_, ?_⟩
  · conv => rhs; rw [← List.map_id ts]
    exact List.map_congr_left fun τ _ => nr_nil_ty τ
  · conv => rhs; rw [← List.map_id ss]
    exact List.map_congr_left fun σ _ => by simp [Renaming.scheme, nr_nil_ty]

theorem filterMap_of_map {X : Type} (f : X → Option TyName) : ∀ (l : List X) (ts : List TyName),
    l.map f = ts.map some → l.filterMap f = ts
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, t :: ts, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.filterMap_cons, h.1, filterMap_of_map f l ts h.2]

theorem custNames_values : ∀ (ad : ATopDec) (e : BExp), bodyExp ad.erase = some e → ad.custNames = []
  | .value _ _, _, _ => rfl
  | .port _ _ _, _, _ => rfl
  | .seq a1 a2, e, h => by
    cases a1 with
    | value VE vb =>
      simp only [ATopDec.erase, bodyExp] at h
      obtain ⟨e2, h2, -⟩ := Option.map_eq_some_iff.mp h
      simp only [ATopDec.custNames, custNames_values a2 e2 h2, List.append_nil]
    | port x ty U =>
      simp only [ATopDec.erase, bodyExp] at h
      obtain ⟨e2, h2, -⟩ := Option.map_eq_some_iff.mp h
      simp only [ATopDec.custNames, custNames_values a2 e2 h2, List.append_nil]
    | types _ _ _ _ | seq _ _ => simp [ATopDec.erase, bodyExp] at h
  | .types _ _ _ _, _, h => by simp [ATopDec.erase, bodyExp] at h

/-- The custom types' names of a module whose body starts with its type declarations. -/
theorem genNames_types {B : SBasis} {a : AModule} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind}
    {tbs : List BTypBind} {rest : Option ATopDec} {ts : List TyName}
    (hb : a.body = joinBody (some (.types TE VE db tbs)) rest) (hr : ∀ r, rest = some r → r.custNames = [])
    (hts : (db.getD []).map (fun e => namesOf TE e.1) = ts.map some) (hT : ∀ t ∈ ts, t ∉ B.T) :
    genNames B a = ts := by
  have hc : ((a.body.map ATopDec.custNames).getD []) = ts := by
    cases rest with
    | none =>
      simp only [joinBody] at hb
      simp only [hb, Option.map_some, Option.getD_some, ATopDec.custNames]
      exact filterMap_of_map _ _ _ hts
    | some r =>
      simp only [joinBody] at hb
      simp only [hb, Option.map_some, Option.getD_some, ATopDec.custNames, hr r rfl, List.append_nil]
      exact filterMap_of_map _ _ _ hts
  unfold genNames
  rw [hc]
  apply List.filter_eq_self.mpr
  intro t ht
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  exact hT t ht

/-! ## L16: renaming back -/

theorem zip_lookup {ts ts' : List TyName} (hnd : ts.Nodup) (hl : ts'.length = ts.length) {t t' : TyName}
    (hm : (t, t') ∈ ts.zip ts') : (ts.zip ts').lookup t = some t' :=
  Swap.lookup_of_mem (by rw [List.map_fst_zip (by omega)]; exact hnd) hm

theorem mem_zip_swap : ∀ {ts ts' : List TyName} {t t' : TyName}, (t, t') ∈ ts.zip ts' → (t', t) ∈ ts'.zip ts
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, t, t', h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr (mem_zip_swap h)

theorem map_eq_self_mem {f : TyName → TyName} : ∀ {l : List TyName}, l.map f = l → ∀ t ∈ l, f t = t
  | [], _, _, ht => by simp at ht
  | a :: as, h, t, ht => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h.1
    · exact map_eq_self_mem h.2 t ht

theorem lookup_none_of_not_mem {L : List (TyName × TyName)} {t : TyName} (h : t ∉ L.map (·.1)) : L.lookup t = none :=
  Swap.lookup_none h

/-- A derivation that, renamed by `σ` (fixing the basis, taking its custom types' names `ts'` to W's
    `ts`), is an instance of W's derivation is itself an instance of it, up to `ts ↦ ts'`. -/
theorem transport {B : SBasis} {a a' : AModule} {σ σ' : List (TyName × TyName)} {ts ts' : List TyName}
    (hσ : NRInv σ σ') (hσB : (nr σ).basis B = B) (hG : genNames B a = ts) (hG' : genNames B a' = ts')
    (hl : ts'.length = ts.length) (hnd : ts.Nodup) (hnd' : ts'.Nodup)
    (hpair : ∀ p ∈ ts'.zip ts, (nr σ).tnApply p.1 = p.2) (hT : ∀ t ∈ ts, t ∉ B.T)
    (hnames : namesB B a = true) (he : a'.erase = a.erase)
    (hI : InstanceNodes [] (nodesModule B (a'.rename (nr σ))) (nodesModule B a)) : InstanceOfMod B a' a := by
  have hσ' := hσ.symm
  have hσ'B : (nr σ').basis B = B := by
    have := nr_inv_basis hσ.left B; rw [hσB] at this; exact this
  have ha' : (a'.rename (nr σ)).rename (nr σ') = a' := nr_inv_module hσ.left a'
  -- the names of the basis are fixed
  have fixB : ∀ t ∈ B.T, (nr σ').tnApply t = t := by
    intro t ht
    have e1 : B.T.map (nr σ).tnApply = B.T := congrArg SBasis.T hσB
    have h1 : (nr σ).tnApply t = t := map_eq_self_mem e1 t ht
    have h2 := hσ.left t
    rw [h1] at h2; exact h2
  have hpair' : ∀ p ∈ ts.zip ts', (nr σ').tnApply p.1 = p.2 := by
    intro p hp
    have := hpair (p.2, p.1) (mem_zip_swap hp)
    simp only at this
    rw [← this]; exact hσ.left p.2
  let ρ := ts.zip ts'
  -- W's nodes renamed by ρ are W's nodes renamed by σ'
  have hren : ∀ n ∈ nodesModule B a, n.renameNames ρ = n.renameNames σ' := by
    intro n hn
    have hok : ∀ t, (decide (t ∈ B.T) || decide (t ∈ genNames B a)) = true →
        (nr ρ).tnApply t = (nr σ').tnApply t := by
      intro t ht
      simp only [Bool.or_eq_true, decide_eq_true_eq] at ht
      rw [hG] at ht
      rcases ht with ht | ht
      · rw [fixB t ht]
        show (ρ.lookup t).getD t = t
        rw [lookup_none_of_not_mem (by rw [List.map_fst_zip (by omega)]; exact fun h => hT t h ht)]; rfl
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
        have hm : (ts[i], ts'[i]'(by omega)) ∈ ts.zip ts' := by
          rw [List.mem_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩
        rw [hpair' _ hm]
        show (ρ.lookup ts[i]).getD ts[i] = ts'[i]
        rw [zip_lookup hnd hl hm]; rfl
    simp only [namesB, List.all_eq_true, Bool.and_eq_true] at hnames
    obtain ⟨h1, h2⟩ := hnames n hn
    rw [node_renameNames, node_renameNames]
    simp only [Node.mk.injEq, true_and]
    refine ⟨List.map_congr_left fun τ hτ => Walk.nr_congr τ fun t ht => hok t (h1 τ hτ t ht),
      List.map_congr_left fun σ0 hσ0 => ?_⟩
    unfold Renaming.scheme
    rw [Walk.nr_congr σ0.body (fun t ht => hok t (h2 σ0 hσ0 t ht))]
    rfl
  refine ⟨he, ρ, ?_, ?_⟩
  · rw [hG, hG']
    refine ⟨fun x => by rw [List.map_fst_zip (by omega)], fun x => by rw [List.map_snd_zip (by omega)], ?_, ?_⟩
    · rw [List.map_fst_zip (by omega)]; exact hnd
    · rw [List.map_snd_zip (by omega)]; exact hnd'
  · obtain ⟨S, hR, -, hdef, hni⟩ := hI
    have hnodes' : nodesModule B a' = nrNodes σ' (nodesModule B (a'.rename (nr σ))) := by
      have := nr_nodesModule hσ'.h B (a'.rename (nr σ)); rw [hσ'B, ha'] at this; exact this
    have hnodes : (nodesModule B a).map (Node.renameNames ρ) = nrNodes σ' (nodesModule B a) :=
      List.map_congr_left hren
    rw [hnodes', hnodes]
    refine ⟨(nr σ').subst S, ?_, fun v _ => List.not_mem_nil, ?_, ?_⟩
    · rw [← Subst.respectsB_iff, nr_respectsB hσ'.h]; exact (Subst.respectsB_iff _).mpr hR
    · intro τ hτ
      simp only [nrNodes, List.flatMap_map, List.mem_flatMap] at hτ
      obtain ⟨n, hn, hτn⟩ := hτ
      rw [node_renameNames] at hτn
      simp only [List.mem_map] at hτn
      obtain ⟨τ0, hτ0, rfl⟩ := hτn
      rw [nr_apply hσ'.h]
      have := hdef τ0 (List.mem_flatMap.mpr ⟨n, hn, hτ0⟩)
      cases e : S.apply τ0 <;> simp_all
    · intro n hn n' hn' ep
      simp only [nrNodes, List.mem_map] at hn hn'
      obtain ⟨n0, hn0, rfl⟩ := hn
      obtain ⟨n0', hn0', rfl⟩ := hn'
      have ep' : n0.path = n0'.path := by
        rw [node_renameNames, node_renameNames] at ep; exact ep
      exact nr_nodeInstance hσ' (hni n0 hn0 n0' hn0' ep')

/-! ## The value declarations -/

/-- L11 at the root, read on the module's value declarations and ports: a derivation of them in the
    context of W's type declarations is an instance of W's, by a substitution leaving `A` (and the
    ports' variables) alone. -/
theorem values_core {fuel : Nat} {C1 : Ctx} {r : BTopDec} {e : BExp} {ae : AExp} {av ar : ATopDec} {A : List BVar}
    {E : Env} {PE : PortEnv}
    (hroot : rootOKB C1 = true) (hw : WE.inferExpWD fuel C1 e = .ok ae) (hu : unLet r ae = some av)
    (hpo : portsOKB C1 r ae = true)
    (hA : ∀ v ∈ A, v.isBnd = true) (hcl : ∀ v, v ∉ C1.tyvars) (hb : bodyExp r = some e)
    (hka : (checkTopDec C1 av).isSome) (hkr : checkTopDec C1 ar = some (E, PE)) (her : ar.erase = av.erase)
    (q : List Nat) :
    ∃ S : Subst, S.Respects ∧ (∀ v ∈ S.dom, v ∉ A) ∧
      (∀ τ ∈ (nodesTopDec C1 q av).flatMap (·.tys), (S.apply τ).isSome) ∧
      PI S (nodesTopDec C1 q av) (nodesTopDec C1 q ar) := by
  have hx := toExpA_of_unLet r ae av hu
  obtain ⟨hc, he, -⟩ := WE.inferExpWD_sound hw
  have hae : av.erase = r := unLet_erase r e ae av hb he hu
  subst hae
  obtain ⟨x'', hx'', hcx, hex⟩ := toExp_checkT hcl ar C1 C1 C1 E PE e ae hkr (by rw [her]; exact hb) (CEq.refl _)
    (PA.refl hcl) (PA.refl hcl) hc (by rw [her]; exact hpo)
  have hrig := portsVars_rigid (Cp := C1) av.erase ae av hu hpo
  obtain ⟨S, hR, hdom, hdef, hni⟩ :=
    WE.wePrincipalityA fuel C1 e ae (rootOKB_sound hroot) hw (A ++ portsVars C1 av) (fun v hv => by
      rcases List.mem_append.mp hv with hv | hv
      · exact rigidFromD_bnd _ (hA v hv)
      · have := hrig v hv
        rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [rigidB, rigidFromD])
      x'' hcx (hex.trans he.symm)
  have hdomP : ∀ v ∈ portsVars C1 av, v ∉ S.dom := fun v hv hd =>
    hdom v hd (List.mem_append_right _ (List.mem_append_right _ hv))
  refine ⟨S, hR, fun v hv hA' => hdom v hv (List.mem_append_right _ (List.mem_append_left _ hA')), ?_, ?_⟩
  · intro τ hτ
    obtain ⟨n, hn, hτn⟩ := List.mem_flatMap.mp hτ
    rcases tys_values hcl av C1 C1 q [] ae ae hx (CEq.refl _) (PA.refl hcl) hka hpo n hn τ hτn with h | h
    · obtain ⟨m, hm, hτm⟩ := h
      exact hdef τ (List.mem_flatMap.mpr ⟨m, hm, hτm⟩)
    · rw [apply_fix S τ (fun v hv => hdomP v (h v hv))]; rfl
  · exact pi_values hcl av ar C1 C1 C1 C1 q [] ae ae x'' hx hx'' her.symm (CEq.refl _) (CEq.refl _)
      (PA.refl hcl) (PA.refl hcl) hka (by rw [hkr]; rfl) hpo hdomP hni

/-! ## The shapes of W's answer -/

theorem typesPart_inv {C C1 : Ctx} {ts : Option (Option BDatBind × List BTypBind)} {at? : Option ATopDec}
    (h : typesPart C ts = some (at?, C1)) :
    (ts = none ∧ at? = none ∧ C1 = C) ∨ ∃ db tbs TE VE, ts = some (db, tbs) ∧ typesW C db tbs = some (TE, VE) ∧
      at? = some (.types TE VE db tbs) ∧ C1 = C.oplusE ⟨[], TE, VE⟩ := by
  cases ts with
  | none => simp only [typesPart, Option.some.injEq, Prod.mk.injEq] at h; exact .inl ⟨rfl, h.1.symm, h.2.symm⟩
  | some q =>
    obtain ⟨db, tbs⟩ := q
    simp only [typesPart] at h
    split at h
    · rename_i TE VE ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact .inr ⟨db, tbs, TE, VE, rfl, ht, h.1.symm, h.2.symm⟩
    · cases h

/-- The four shapes of a module W elaborates: no body; value declarations only; type declarations
    only; type declarations, then value declarations. -/
theorem shape {fuel : Nat} {B : SBasis} {m : BModule} {a : AModule} {C : Ctx} (h : inferModuleW fuel B m = .ok a)
    (hC : importCtx B m.imports = some C) :
    (m.body = none ∧ a.body = none) ∨
    (∃ av ae e, m.body = some av.erase ∧ a.body = some av ∧ bodyExp av.erase = some e ∧ rootOKB C = true ∧
      WE.inferExpWD fuel C e = .ok ae ∧ unLet av.erase ae = some av ∧ portsOKB C av.erase ae = true) ∨
    (∃ db tbs TE VE, m.body = some (.types db tbs) ∧ a.body = some (.types TE VE db tbs) ∧
      typesW C db tbs = some (TE, VE)) ∨
    (∃ db tbs TE VE av ae e, m.body = some (.seq (.types db tbs) av.erase) ∧
      a.body = some (.seq (.types TE VE db tbs) av) ∧ typesW C db tbs = some (TE, VE) ∧
      bodyExp av.erase = some e ∧ rootOKB (C.oplusE ⟨[], TE, VE⟩) = true ∧
      WE.inferExpWD fuel (C.oplusE ⟨[], TE, VE⟩) e = .ok ae ∧ unLet av.erase ae = some av ∧
      portsOKB (C.oplusE ⟨[], TE, VE⟩) av.erase ae = true) := by
  obtain ⟨C', hC', -, -, -, -, hcase⟩ := inferModuleW_ok_inv h
  rw [hC] at hC'; cases hC'
  rcases hcase with ⟨hm, ha⟩ | ⟨d, at?, C1, hd, hty, hrest⟩
  · exact .inl ⟨hm, ha⟩
  right
  rcases typesPart_inv hty with ⟨hs, rfl, rfl⟩ | ⟨db, tbs, TE, VE, hs, htw, rfl, rfl⟩
  · -- no type declarations
    have hd2 : (splitBody d).2 = some d := by
      cases d with
      | types _ _ => simp [splitBody] at hs
      | seq d1 d2 => cases d1 <;> simp_all [splitBody]
      | value _ | port _ _ => rfl
    rcases hrest with ⟨hn, -⟩ | ⟨r, e, ae, av, hr, he, hroot, hw, hu, hpo, hb⟩
    · rw [hd2] at hn; cases hn
    · rw [hd2] at hr; cases hr
      obtain ⟨-, he', -⟩ := WE.inferExpWD_sound hw
      have hae := unLet_erase _ e ae av he he' hu
      refine .inl ⟨av, ae, e, by rw [hd, hae], by rw [hb]; rfl, by rw [hae]; exact he, hroot, hw,
        by rw [hae]; exact hu, by rw [hae]; exact hpo⟩
  · right
    rcases hrest with ⟨hn, hb⟩ | ⟨r, e, ae, av, hr, he, hroot, hw, hu, hpo, hb⟩
    · have hdd : d = .types db tbs := by
        cases d with
        | types db' tbs' => simp only [splitBody, Option.some.injEq, Prod.mk.injEq] at hs; rw [hs.1, hs.2]
        | seq d1 d2 => cases d1 <;> simp_all [splitBody]
        | value _ | port _ _ => simp [splitBody] at hs
      exact .inl ⟨db, tbs, TE, VE, by rw [hd, hdd], by rw [hb]; rfl, htw⟩
    · have hdd : d = .seq (.types db tbs) r := by
        cases d with
        | types _ _ => simp [splitBody] at hr
        | seq d1 d2 =>
          cases d1 with
          | types db' tbs' =>
            simp only [splitBody, Option.some.injEq, Prod.mk.injEq] at hs hr
            rw [hs.1, hs.2, hr]
          | value _ | port _ _ | seq _ _ => simp [splitBody] at hs
        | value _ | port _ _ => simp [splitBody] at hs
      obtain ⟨-, he', -⟩ := WE.inferExpWD_sound hw
      have hae := unLet_erase _ e ae av he he' hu
      exact .inr ⟨db, tbs, TE, VE, av, ae, e, by rw [hd, hdd, hae], by rw [hb]; rfl, htw,
        by rw [hae]; exact he, hroot, hw, by rw [hae]; exact hu, by rw [hae]; exact hpo⟩

theorem body_check {B : SBasis} {a : AModule} {C : Ctx} (hC : importCtx B a.imports = some C)
    (hc : checkModule B a = true) : ∃ E PE, checkTopDecOpt C a.body = some (E, PE) := by
  unfold checkModule at hc
  rw [AModule.result_of_ctx hC] at hc
  obtain ⟨⟨B', E⟩, hres⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨PE, I, hk, -, -⟩ := MStep.resultIn_inv hres
  exact ⟨E, PE, hk⟩

theorem typesBnd_vars {TE : TyEnv} {VE : ValEnv} (h : typesBndB TE VE = true) :
    ∀ v ∈ ((TE.map (·.2.1.body)) ++ (veSchemes VE).map (·.body)).flatMap Ty.vars, v.isBnd = true := by
  intro v hv
  simp only [typesBndB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨τ, hτ, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_append.mp hτ with hτ | hτ
  · exact h.1 τ hτ v hv
  · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
    exact h.2 σ hσ v hv

theorem map_renameNames_nil (ns : List Node) : ns.map (Node.renameNames []) = ns := by
  conv => rhs; rw [← List.map_id ns]
  exact List.map_congr_left fun n _ => renameNames_id_nil n

theorem bij_nil : Bijective [] [] [] := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, .nil, .nil⟩

/-! ## Module principality -/

/-- Module principality (section 7, "Modules"; sec:static-modules-principal): what W returns for a
    module is a derivation of it of which every derivation is an instance, up to a bijection of
    the custom types' names. By ruling A98 every module is coherent: no coherence hypothesis. -/
theorem inferModuleW_principal {fuel : Nat} {B : SBasis} {m : BModule} {a : AModule} (hB : BasisInv B)
    (h : inferModuleW fuel B m = .ok a) : a.erase = m ∧ IsPrincipalMod B a := by
  obtain ⟨C, hC, hc, hn, hh, hi, -⟩ := inferModuleW_ok_inv h
  obtain ⟨hCcl, hCU, -⟩ := Closed.importCtx_closed hB.closed hC
  have hCa : importCtx B a.imports = some C := by rw [hi]; exact hC
  have hsh := shape h hC
  have herase : a.erase = m := by
    obtain ⟨mh, mi, mb⟩ := m
    simp only at hh hi hsh
    simp only [AModule.erase, BModule.mk.injEq]
    refine ⟨hh, hi, ?_⟩
    rcases hsh with ⟨hm, ha⟩ | ⟨av, -, -, hm, ha, -⟩ | ⟨db, tbs, TE, VE, hm, ha, -⟩ |
        ⟨db, tbs, TE, VE, av, -, -, hm, ha, -⟩ <;> simp_all [ATopDec.erase]
  refine ⟨herase, isPrincipalMod_iff.mpr ⟨hc, fun a' hc' he' => ?_⟩⟩
  have he'm : a'.erase = m := he'.trans herase
  have hCa' : importCtx B a'.imports = some C := by
    rw [show a'.imports = m.imports from congrArg BModule.imports he'm]; exact hC
  have hb' : a'.body.map ATopDec.erase = m.body := congrArg BModule.body he'm
  obtain ⟨E', PE', hk'⟩ := body_check hCa' hc'
  obtain ⟨E, PE, hk⟩ := body_check hCa hc
  have hnA : ∀ (d : ATopDec), a.body = some d → nodesModule B a = nodesTopDec C [] d := fun d hd => by
    simp only [nodesModule, hCa, hd]
  rcases hsh with ⟨hm, ha⟩ | ⟨av, ae, e, hm, ha, hbe, hroot, hw, hu, hpo⟩ | ⟨db, tbs, TE, VE, hm, ha, htw⟩ |
      ⟨db, tbs, TE, VE, av, ae, e, hm, ha, htw, hbe, hroot, hw, hu, hpo⟩
  · -- no body
    have ha' : a'.body = none := by
      rw [hm] at hb'; cases e : a'.body with
      | none => rfl
      | some _ => rw [e] at hb'; cases hb'
    have hg : genNames B a = [] := by simp [genNames, ha]
    have hg' : genNames B a' = [] := by simp [genNames, ha']
    refine ⟨he', [], by rw [hg, hg']; exact bij_nil, Subst.id, fun p hp => by simp [Subst.id] at hp,
      fun v hv => by simp [Subst.id, Subst.dom] at hv, fun τ hτ => ?_, fun n hn => ?_⟩
    · simp [nodesModule, ha] at hτ
    · simp [nodesModule, ha] at hn
  · -- value declarations only
    obtain ⟨ar, ha', har⟩ : ∃ ar, a'.body = some ar ∧ ar.erase = av.erase := by
      rw [hm] at hb'; obtain ⟨ar, h1, h2⟩ := Option.map_eq_some_iff.mp hb'; exact ⟨ar, h1, h2⟩
    rw [ha'] at hk'; rw [ha] at hk
    simp only [checkTopDecOpt] at hk hk'
    obtain ⟨S, hR, -, hdef, hpi⟩ := values_core (A := []) hroot hw hu hpo (fun _ h => by cases h)
      (notin_of_nil hCcl) hbe (by rw [hk]; rfl) hk' har []
    have hg : genNames B a = [] := by simp [genNames, ha, custNames_values av e hbe]
    have hg' : genNames B a' = [] := by simp [genNames, ha', custNames_values ar e (by rw [har]; exact hbe)]
    refine ⟨he', [], by rw [hg, hg']; exact bij_nil, S, hR, fun v _ => List.not_mem_nil, ?_, ?_⟩
    · rw [map_renameNames_nil, hnA av ha]; exact hdef
    · rw [map_renameNames_nil, hnA av ha]
      have : nodesModule B a' = nodesTopDec C [] ar := by simp only [nodesModule, hCa', ha']
      rw [this]; exact hpi
  · -- type declarations only
    have ha' : ∃ TE' VE', a'.body = some (.types TE' VE' db tbs) := by
      rw [hm] at hb'; obtain ⟨ad, h1, h2⟩ := Option.map_eq_some_iff.mp hb'
      cases ad with
      | types TE' VE' db' tbs' =>
        simp only [ATopDec.erase, BTopDec.types.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2; exact ⟨TE', VE', h1⟩
      | value _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at h2
    obtain ⟨TE', VE', ha'⟩ := ha'
    rw [ha'] at hk'
    simp only [checkTopDecOpt] at hk'
    obtain ⟨hct', -⟩ := checkTopDec_types hk'
    obtain ⟨hct, hord, -⟩ := typesW_spec htw
    obtain ⟨σ, σ', ts', ts, hσ, hσB, hσC, eT, eV, e1', e1, hpair, hl, nd', nd, new', new⟩ :=
      types_bij hB hC hct' hct hord
    have hG : genNames B a = ts := genNames_types (rest := none) (by rw [ha]; rfl) (fun _ h => by cases h) e1 new
    have hG' : genNames B a' = ts' := genNames_types (rest := none) (by rw [ha']; rfl) (fun _ h => by cases h) e1' new'
    refine transport hσ hσB hG hG' hl nd nd' hpair new hn he' ?_
    have hn'' : nodesModule B (a'.rename (nr σ)) = nodesTopDec C [] (.types TE VE db tbs) := by
      simp only [nodesModule, nr_rename_imports, hCa', nr_rename_body, ha', Option.map_some, Renaming.topDec, eT, eV]
    rw [hn'', hnA _ ha]
    refine ⟨Subst.id, fun p hp => by simp [Subst.id] at hp, fun v hv => by simp [Subst.id, Subst.dom] at hv,
      fun τ _ => ?_, fun n hn n' hn' _ => ?_⟩
    · rw [apply_fix Subst.id τ (fun v _ hv => by simp [Subst.id, Subst.dom] at hv)]; rfl
    · simp only [nodesTopDec, List.mem_singleton] at hn hn'
      subst hn; subst hn'
      exact nodeInstance_fixed hCU (fun _ _ v _ hv => by simp [Subst.id, Subst.dom] at hv)
  · -- type declarations, then value declarations
    have ha' : ∃ TE' VE' ar, a'.body = some (.seq (.types TE' VE' db tbs) ar) ∧ ar.erase = av.erase := by
      rw [hm] at hb'; obtain ⟨ad, h1, h2⟩ := Option.map_eq_some_iff.mp hb'
      cases ad with
      | seq d1 ar =>
        cases d1 with
        | types TE' VE' db' tbs' =>
          simp only [ATopDec.erase, BTopDec.seq.injEq, BTopDec.types.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, h3⟩ := h2; exact ⟨TE', VE', ar, h1, h3⟩
        | value _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at h2
      | value _ _ | port _ _ _ | types _ _ _ _ => simp [ATopDec.erase] at h2
    obtain ⟨TE', VE', ar, ha', har⟩ := ha'
    rw [ha'] at hk'; rw [ha] at hk
    simp only [checkTopDecOpt] at hk hk'
    obtain ⟨E1', PE1', E2', PE2', hk1', hk2'⟩ := checkTopDec_seq hk'
    obtain ⟨hct', rfl⟩ := checkTopDec_types hk1'
    obtain ⟨E1, PE1, E2, PE2, hk1, hk2⟩ := checkTopDec_seq hk
    obtain ⟨-, rfl⟩ := checkTopDec_types hk1
    obtain ⟨hct, hord, hbnd⟩ := typesW_spec htw
    obtain ⟨σ, σ', ts', ts, hσ, hσB, hσC, eT, eV, e1', e1, hpair, hl, nd', nd, new', new⟩ :=
      types_bij hB hC hct' hct hord
    have hG : genNames B a = ts := genNames_types (rest := some av) (by rw [ha]; rfl)
      (fun r hr => by cases hr; exact custNames_values av e hbe) e1 new
    have hG' : genNames B a' = ts' := genNames_types (rest := some ar) (by rw [ha']; rfl)
      (fun r hr => by cases hr; exact custNames_values ar e (by rw [har]; exact hbe)) e1' new'
    refine transport hσ hσB hG hG' hl nd nd' hpair new hn he' ?_
    -- the renamed derivation's value declarations, in W's context
    have hk3 := nr_checkTopDec hσ.h ar (C.oplusE ⟨[], TE', VE'⟩)
    rw [hk2', ← nr_oplusE hσ.h, hσC] at hk3
    have hEnv : (nr σ).env (⟨[], TE', VE'⟩ : Env) = ⟨[], TE, VE⟩ := by
      simp only [Renaming.env, List.map_nil, eT, eV]
    rw [hEnv] at hk3
    have hkt : checkTopDec C (.types TE VE db tbs) = some (⟨[], TE, VE⟩, []) := by
      simp only [checkTopDec, hct, ite_true]
    let A := ((TE.map (·.2.1.body)) ++ (veSchemes VE).map (·.body)).flatMap Ty.vars
    have hC1cl : (C.oplusE ⟨[], TE, VE⟩).tyvars = [] := Closed.oplusE_closed hCcl (Types.types_closed hCcl hct).1
    obtain ⟨S, hR, hdomA, hdef, hpi⟩ := values_core (A := A) hroot hw hu hpo (typesBnd_vars hbnd)
      (notin_of_nil hC1cl) hbe (by rw [hk2]; rfl) hk3 (by rw [erase_topDec, har]) ([] ++ [1])
    have hn'' : nodesModule B (a'.rename (nr σ)) =
        nodesTopDec C [] (.seq (.types TE VE db tbs) ((nr σ).topDec ar)) := by
      simp only [nodesModule, nr_rename_imports, hCa', nr_rename_body, ha', Option.map_some, Renaming.topDec, eT, eV]
    rw [hn'', hnA _ ha, nodesTopDec_seq hkt, nodesTopDec_seq hkt]
    have hfixT : ∀ τ ∈ (TE.map (·.2.1.body)) ++ (veSchemes VE).map (·.body), ∀ v ∈ τ.vars, v ∉ S.dom :=
      fun τ hτ v hv hd => hdomA v hd (List.mem_flatMap.mpr ⟨τ, hτ, hv⟩)
    refine ⟨S, hR, fun v _ => List.not_mem_nil, fun τ hτ => ?_, ?_⟩
    · rcases List.mem_flatMap.mp hτ with ⟨n, hn, hτn⟩
      rcases List.mem_append.mp hn with hn | hn
      · rcases List.mem_append.mp hn with hn | hn
        · simp only [List.mem_singleton] at hn; subst hn; cases hτn
        · simp only [nodesTopDec, List.mem_singleton] at hn; subst hn
          rw [apply_fix S τ (hfixT τ (List.mem_append_left _ hτn))]; rfl
      · exact hdef τ (List.mem_flatMap.mpr ⟨n, hn, hτn⟩)
    · have hroot0 : PI S [⟨[], C.U, [], []⟩] [⟨[], C.U, [], []⟩] := fun n hn n'' hn'' _ => by
        simp only [List.mem_singleton] at hn hn''; subst hn; subst hn''
        exact nodeInstance_empty S _ _ hCU rfl rfl hCU rfl rfl
      have htyp : PI S (nodesTopDec C ([] ++ [0]) (.types TE VE db tbs)) (nodesTopDec C ([] ++ [0]) (.types TE VE db tbs)) := by
        intro n hn n'' hn'' _
        simp only [nodesTopDec, List.mem_singleton] at hn hn''
        subst hn; subst hn''
        exact nodeInstance_fixed hCU hfixT
      refine PI.append (PI.append hroot0 htyp ?_ ?_) hpi ?_ ?_
      · intro x hx y hy
        simp only [List.mem_singleton] at hx; subst hx
        obtain ⟨s, hs⟩ := topDec_prefix _ _ _ y hy
        simp only [hs]; exact prefix_long
      · intro y hy x hx
        simp only [List.mem_singleton] at hx; subst hx
        obtain ⟨s, hs⟩ := topDec_prefix _ _ _ y hy
        simp only [hs]; exact fun e => prefix_long e.symm
      · intro x hx y hy
        obtain ⟨s2, hs2⟩ := topDec_prefix _ _ _ y hy
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_singleton] at hx; subst hx
          simp only [hs2]; exact prefix_long
        · obtain ⟨s1, hs1⟩ := topDec_prefix _ _ _ x hx
          rw [hs1, hs2]; exact prefix_ne (by decide)
      · intro y hy x hx
        obtain ⟨s2, hs2⟩ := topDec_prefix _ _ _ y hy
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_singleton] at hx; subst hx
          simp only [hs2]; exact fun e => prefix_long e.symm
        · obtain ⟨s1, hs1⟩ := topDec_prefix _ _ _ x hx
          rw [hs1, hs2]; exact prefix_ne (by decide)

end MW
end StandardElm.Stat.Complete
