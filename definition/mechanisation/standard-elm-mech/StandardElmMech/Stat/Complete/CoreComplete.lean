/-
  A Standard Definition of Elm? Mechanisation: completeness of `coreGen` for derivations and the
  refusal theorem of milestone (a), plan step 11 ("Theorems", "Constraint generation").

  `coreGen_complete`: every derivation of the module (an annotated module that `checkModule`
  accepts) solves the constraints `coreGen` generates, under the valuation read off it (`rdTop`).
  With `unifyCs_fail` (Unify.lean): when unification fails, the first module has no derivation, so
  the program is not legal (`not_legal_of_coreRefutes`, through Refusals.lean's
  `not_legal_of_noDeriv`). No principality hypothesis is involved.
-/
import StandardElmMech.Stat.Complete.CoreExp

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BModule)

variable {ν : Val}

theorem RelL.append_modify {L1 L2 : FMap Var GInfo} {V1 V2 : ValEnv} (h1 : RelL ν L1 V1) (h2 : RelL ν L2 V2) :
    RelL ν (L2 ++ L1) (FMap.modify V1 V2) := by
  intro x
  rw [FMap.find?_append, FMap.find?_modify]
  exact RelOpt.or (h2 x) (h1 x)

/-! ## The values type declarations bind -/

theorem mem_keys_modify {K V : Type} [DecidableEq K] {f g : FMap K V} {x : K} (h : x ∈ (FMap.modify f g).keys) :
    x ∈ f.keys ∨ x ∈ g.keys := by
  unfold FMap.modify FMap.keys at h
  simp only [List.map_append, List.mem_append] at h
  rcases h with h | h
  · exact .inr h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact .inl (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)

theorem mem_keys_plusAll {K V : Type} [DecidableEq K] {x : K} : ∀ (Ls : List (FMap K V)) (acc : FMap K V),
    x ∈ (Ls.foldl FMap.modify acc).keys → x ∈ acc.keys ∨ ∃ L ∈ Ls, x ∈ L.keys
  | [], _, h => .inl h
  | L :: Ls, acc, h => by
    rcases mem_keys_plusAll Ls (FMap.modify acc L) h with h | ⟨L', hL', h⟩
    · rcases mem_keys_modify h with h | h
      · exact .inl h
      · exact .inr ⟨L, List.mem_cons_self, h⟩
    · exact .inr ⟨L', List.mem_cons_of_mem _ hL', h⟩

theorem keys_mapV {K V W : Type} (f : FMap K V) (g : V → W) : (FMap.mapV f g).keys = f.keys := by
  simp [FMap.mapV, FMap.keys]

theorem keys_conBind {C : Ctx} {τ : Ty} : ∀ (cb : Src.BConBind) (VE : ValEnv), elabConBind C τ cb = some VE →
    ∀ x ∈ VE.keys, x ∈ cb.map (·.1)
  | [], VE, h, x, hx => by simp only [elabConBind, Option.some.injEq] at h; subst h; simp [FMap.keys] at hx
  | (k, tys) :: rest, VE, h, x, hx => by
    simp only [elabConBind] at h
    split at h
    · rename_i τs VE' _ h2
      cases h
      rcases mem_keys_modify hx with h | h
      · simp only [FMap.keys, List.map_cons, List.map_nil, List.mem_singleton] at h
        subst h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keys_conBind rest VE' h2 x h)
    · cases h

theorem keys_datBind {C : Ctx} {names : String → Option TyName} : ∀ (d : Src.BDatBind) (VE : ValEnv) (TE : TyEnv),
    elabDatBind C names d = some (VE, TE) → ∀ x ∈ VE.keys, ∃ c ∈ d, x ∈ c.2.2.map (·.1)
  | [], VE, TE, h, x, hx => by
    simp only [elabDatBind, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [FMap.keys] at hx
  | (c, ps, cb) :: rest, VE, TE, h, x, hx => by
    simp only [elabDatBind] at h
    split at h
    · cases h
    · split at h
      · rename_i τs VE' TE' _ h2
        split at h
        · rename_i VEc h3
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rcases mem_keys_modify hx with h | h
            · unfold closVE at h; rw [keys_mapV] at h
              exact ⟨(c, ps, cb), List.mem_cons_self, keys_conBind cb VEc h3 x h⟩
            · obtain ⟨c', hc', hx'⟩ := keys_datBind rest VE' TE' h2 x h
              exact ⟨c', List.mem_cons_of_mem _ hc', hx'⟩
          · cases h
        · cases h
      · cases h

theorem keys_typBind {C : Ctx} {tb : Src.BTypBind} {VE : ValEnv} {TE : TyEnv} (h : elabTypBind C tb = some (VE, TE)) :
    ∀ x ∈ VE.keys, x = tb.c := by
  intro x hx
  unfold elabTypBind at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp [FMap.keys] at hx
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            unfold closVE at hx; rw [keys_mapV] at hx
            simpa [FMap.keys] using hx
          · cases h
        · cases h
      · cases h

theorem keys_typBinds {C : Ctx} : ∀ (tbs : List Src.BTypBind) (VEs : List ValEnv) (TEs : List TyEnv),
    elabTypBinds C tbs = some (VEs, TEs) → ∀ VE ∈ VEs, ∀ x ∈ VE.keys, x ∈ tbs.map (·.c)
  | [], VEs, TEs, h, VE, hVE, x, _ => by
    simp only [elabTypBinds, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; cases hVE
  | tb :: tbs, VEs, TEs, h, VE, hVE, x, hx => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE1 TE1 VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases List.mem_cons.mp hVE with rfl | hVE
      · rw [keys_typBind h1 x hx]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keys_typBinds tbs VEs' TEs' h2 VE hVE x hx)
    · cases h

theorem keys_checkTypes {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option Src.BDatBind} {tbs : List Src.BTypBind}
    (h : checkTypes C TE VE db tbs = true) : ∀ x ∈ VE.keys, x ∈ tdNames db tbs := by
  intro x hx
  have hplus : ∀ (VEs : List ValEnv), (∀ VE ∈ VEs, ∀ x ∈ VE.keys, x ∈ tbs.map (·.c)) →
      x ∈ (FMap.plusAll VEs).keys → x ∈ tdNames db tbs := by
    intro VEs hk hx
    rcases mem_keys_plusAll VEs [] hx with h | ⟨L, hL, h⟩
    · simp [FMap.keys] at h
    · exact List.mem_append_right _ (hk L hL x h)
  replace h := checkTypes_fix h
  unfold checkTypesFix at h
  cases db with
  | none =>
    simp only at h
    split at h
    · rename_i VEs TEs hb
      simp only [decide_eq_true_eq] at h
      obtain ⟨_, _, rfl⟩ := h
      exact hplus VEs (keys_typBinds tbs VEs TEs hb) hx
    · cases h
  | some d =>
    simp only at h
    split at h
    · rename_i VE' TE' VEs TEs hd hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      rcases mem_keys_modify hx with h | h
      · obtain ⟨c, hc, hx'⟩ := keys_datBind d VE' TE' hd x h
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, by simpa using hc, hx'⟩)
      · exact hplus VEs (keys_typBinds tbs VEs TEs hb) h
    · cases h

theorem find?_weak (ns : List Var) (x : Var) :
    FMap.find? (ns.map fun y => (y, GInfo.weak)) x = if x ∈ ns then some .weak else none := by
  induction ns with
  | nil => rfl
  | cons y ns ih =>
    simp only [List.map_cons, FMap.find?, List.mem_cons, ih]
    by_cases e : y = x
    · subst e; simp
    · simp only [e, ite_false]
      by_cases hm : x ∈ ns
      · simp [hm]
      · simp [hm, Ne.symm e]

theorem relL_weak {ns : List Var} {VE : ValEnv} (h : ∀ x ∈ VE.keys, x ∈ ns) :
    RelL ν (ns.map fun y => (y, GInfo.weak)) VE := by
  intro x
  rw [find?_weak]
  cases e : FMap.find? VE x with
  | none => split <;> trivial
  | some v =>
    have hk : x ∈ VE.keys := (FMap.find?_isSome_iff VE x).mp (by rw [e]; rfl)
    simp only [h x hk, ite_true]
    obtain ⟨σ, s⟩ := v
    trivial

/-! ## Modules -/

section top
variable {B : SBasis} (hcol : RTypes.Col B (RTypes.fcol B.T)) (hg : ∀ t, gN (RTypes.fcol B.T t) = gN t)
  {A : Ctx} (hAU : A.U = [])
include hcol hg hAU

theorem gTop_ok : (a : ATopDec) → ∀ {C : Ctx} {Γ : GCtx} {p : Path} {E : Env} {PE : PortEnv}
    {L : FMap Var GInfo} {cs : List Con}, Γ.A = A → Sim ν (RTypes.fcol B.T) Γ C → RTypes.Inv B (RTypes.fcol B.T) A C →
    RTypes.preserves A a.erase = true → checkTopDec C a = some (E, PE) →
    gTop Γ p a.erase = some (L, cs) → (∀ q, ν (q.reverse ++ p) = rdTop a q) →
    Holds ν cs ∧ RelL ν L E.VE ∧ E.QE = []
  | .value VE vb, C, Γ, p, E, PE, L, cs, _, hS, _, _, h, hgt, hr => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨h1, h2⟩ := hc
      simp only [ATopDec.erase, gTop, Option.some.injEq, Prod.mk.injEq] at hgt
      obtain ⟨rfl, rfl⟩ := hgt
      have hrv := child 0 hr (fun q => rfl)
      have hR : RelL ν (gVBEnv Γ.A (0 :: p) vb.erase) VE :=
        h2 ▸ gVBEnv_rel vb (C := C.plusVE VE) (hS.ty.same (C' := C.plusVE VE) (fun _ => rfl)) h1 hrv
      have hc := gValBind_ok vb (Sim.plusVE hS hR) h1 hrv
      exact ⟨hc, RelL.close _ (groupSol_holds hc) hR, rfl⟩
    · cases h
  | .types TE VE db tbs, C, Γ, p, E, PE, L, cs, _, _, _, _, h, hgt, _ => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [ATopDec.erase, gTop, Option.some.injEq, Prod.mk.injEq] at hgt
      obtain ⟨rfl, rfl⟩ := hgt
      exact ⟨Holds.nil, relL_weak (keys_checkTypes hc), rfl⟩
    · cases h
  | .port x ty U, C, Γ, p, E, PE, L, cs, _, _, _, _, h, hgt, _ => by
    obtain ⟨_, _, s, PE', hr⟩ := RTypes.elabPort_shape h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp only [ATopDec.erase, gTop, Option.some.injEq, Prod.mk.injEq] at hgt
    obtain ⟨rfl, rfl⟩ := hgt
    exact ⟨Holds.nil, RelL.single (g := .weak) (σ := s.1) (s := s.2) trivial, rfl⟩
  | .seq a1 a2, C, Γ, p, E, PE, L, cs, hA, hS, hI, hp, h, hgt, hr => by
    simp only [ATopDec.erase, RTypes.preserves, Bool.and_eq_true] at hp
    simp only [checkTopDec] at h
    cases h1 : checkTopDec C a1 with
    | none => rw [h1] at h; cases h
    | some r1 =>
      obtain ⟨E1, PE1⟩ := r1
      rw [h1] at h
      simp only at h
      cases h2 : checkTopDec (C.oplusE E1) a2 with
      | none => rw [h2] at h; cases h
      | some r2 =>
        obtain ⟨E2, PE2⟩ := r2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [ATopDec.erase, gTop] at hgt
        cases g1 : gTop Γ (0 :: p) a1.erase with
        | none => rw [g1] at hgt; cases hgt
        | some s1 =>
          obtain ⟨L1, c1⟩ := s1
          rw [g1] at hgt
          simp only at hgt
          cases g2 : gTop (Γ.add L1) (1 :: p) a2.erase with
          | none => rw [g2] at hgt; cases hgt
          | some s2 =>
            obtain ⟨L2, c2⟩ := s2
            rw [g2] at hgt
            simp only [Option.some.injEq, Prod.mk.injEq] at hgt
            obtain ⟨rfl, rfl⟩ := hgt
            obtain ⟨hc1, hR1, hQ1⟩ := gTop_ok a1 hA hS hI hp.1 h1 g1 (child 0 hr (fun q => rfl))
            have hI1 := RTypes.pres hcol hAU a1 C E1 PE1 hI hp.1 h1
            have hS1 : Sim ν (RTypes.fcol B.T) (Γ.add L1) (C.oplusE E1) :=
              Sim.oplusE hS hR1 hQ1 ⟨fun lc => hA ▸ hI1.look lc, hcol.builtins, hg⟩
            obtain ⟨hc2, hR2, hQ2⟩ := gTop_ok a2 (Γ := Γ.add L1) hA hS1 hI1 hp.2 h2 g2 (child 1 hr (fun q => rfl))
            refine ⟨Holds.append.mpr ⟨hc1, hc2⟩, RelL.append_modify hR1 hR2, ?_⟩
            simp [Env.plus, hQ1, hQ2, FMap.modify]

end top

theorem gN_fcol {B : SBasis} (h : T0.all (· ∈ B.T) = true) : ∀ t, gN (RTypes.fcol B.T t) = gN t := by
  intro t
  unfold RTypes.fcol
  by_cases ht : t ∈ B.T
  · simp [ht]
  · have h0 : t ∉ T0 := fun hm => ht (by have := List.all_eq_true.mp h t hm; simpa using this)
    have hD : (⟨RTypes.Did, t.arity⟩ : TyName) ∉ T0 := by
      intro hm; simp [T0, RTypes.Did, tInt, tFloat, tChar, tString, tUnit, tList, tTuple2, tTuple3, tBool, tOrder,
        tNever, tMaybe, tResult, tArray, tBytes, tValue, tCmd, tSub, tTask, tProcessId, tProgram, tNode] at hm
    simp only [ht, ite_false, gN, h0, hD]

/-- Completeness of generation: every derivation of the module solves the constraints. -/
theorem coreGen_complete {B : SBasis} {m : BModule} {cs : List Con} (h : coreGen B m = some cs)
    (a : AModule) (he : a.erase = m) (hc : checkModule B a = true) : ∃ ν, Holds ν cs := by
  unfold coreGen at h
  split at h
  · rename_i C0 d hC hd
    split at h
    · rename_i hok
      simp only [typesOK, Bool.and_eq_true] at hok
      obtain ⟨⟨⟨hfix, hT0⟩, hun⟩, hpres⟩ := hok
      obtain ⟨⟨L, cs'⟩, hgt, e⟩ := Option.map_eq_some_iff.mp h
      simp only at e
      subst e
      have hC' : importCtx B a.imports = some C0 := by rw [RTypes.imports_erase he]; exact hC
      unfold checkModule at hc
      rw [AModule.result_of_ctx hC'] at hc
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hc
      obtain ⟨PE', hchk⟩ := RTypes.resultIn_check (B' := r.1) (E := r.2) hr
      obtain ⟨ad, hb, had⟩ := RTypes.body_erase he hd
      rw [hb] at hchk
      simp only [checkTopDecOpt] at hchk
      obtain ⟨hU, hTT⟩ := RTypes.importCtx_UT hC
      have hcol := RTypes.col_fcol B hfix
      have hg := gN_fcol hT0
      have hI := RTypes.inv_base B (RTypes.fcol B.T) C0 _ hU hTT hun
      have hS : Sim (fun r => rdTop ad r.reverse) (RTypes.fcol B.T) ⟨[], C0, absOf B C0 d⟩ C0 :=
        Sim.base C0 _ ⟨hI.look, hcol.builtins, hg⟩
      refine ⟨fun r => rdTop ad r.reverse, (gTop_ok hcol hg (A := absOf B C0 d) rfl ad rfl hS hI
        (by rw [had]; exact hpres) hchk (by rw [had]; exact hgt) (fun q => by simp)).1⟩
    · cases h
  · cases h

/-- If unification of the first module's constraints fails, the module has no derivation. -/
theorem noDeriv_of_core {B : SBasis} {m : BModule} {cs : List Con} (h : coreGen B m = some cs)
    (hu : unifyCs cs = .fail) : NoDeriv B m := by
  intro a he
  cases hc : checkModule B a with
  | false => rfl
  | true =>
    obtain ⟨ν, hh⟩ := coreGen_complete h a he hc
    exact absurd hh (unifyCs_fail hu ν)

end StandardElm.Stat.Complete

namespace StandardElm.Stat
open StandardElm.Stat.Complete

/-- The refusal theorem of milestone (a): unconditional (no principality hypothesis). -/
theorem not_legal_of_coreRefutes {B : SBasis} {sp : Src.SProgram} (h : coreRefutes B sp = true) :
    ¬ LegalProgram B sp := by
  unfold coreRefutes at h
  split at h
  · rename_i m rest hms
    split at h
    · rename_i cs hg
      have hu : unifyCs cs = .fail := by
        simp only [Bool.and_eq_true] at h
        revert h; cases unifyCs cs <;> simp [UOutcome.isFail]
      exact not_legal_of_noDeriv hms (noDeriv_of_core hg hu)
    · cases h
  · cases h

end StandardElm.Stat
