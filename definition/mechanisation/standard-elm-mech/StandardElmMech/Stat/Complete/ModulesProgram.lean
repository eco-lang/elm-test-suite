/-
  A Standard Definition of Elm? Mechanisation: W for programs (milestone (f) of plan step 11,
  "Modules and programs"; finding B1). `inferProgramW` elaborates the modules in order, each in the
  basis `r:p-stat-module` builds from W's results for the earlier ones.

  * Principality (`inferProgramW_principal`): W's derivation of the program gives every module a
    principal derivation in its basis (`PrincipalProgDeriv`). Each module's by
    `inferModuleW_principal`; the next basis keeps the invariant by step 10's module step applied
    to the principal derivation and itself.
  * Refutation (`inferProgramW_fail`): if W fails on a module, the program has no derivation. The
    earlier modules' principal derivations in any derivation of the program are W's up to a
    bijection of type names fixing the basis (step 10's module step, from the two being instances
    of each other: L15), so the derivation's basis for the failing module is W's renamed, in which
    the module has no derivation either (L16, `nr_checkModule`).

  No coherence hypothesis: every module is coherent since ruling A98.
-/
import StandardElmMech.Stat.Complete.ModulesPrincipal
import StandardElmMech.Stat.ProgInduction

namespace StandardElm.Stat.Complete
namespace MW
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTopDec BModule BProgram)

/-! ## The restriction on type declarations the module step needs holds of W's modules -/

theorem topTypesOrdered_values : ∀ (r : BTopDec) (e : Src.BExp), bodyExp r = some e → topTypesOrdered r = true
  | .value _, _, _ => rfl
  | .port _ _, _, _ => rfl
  | .seq (.value _) r2, e, h => by
    simp only [bodyExp] at h
    obtain ⟨e2, h2, -⟩ := Option.map_eq_some_iff.mp h
    simp only [topTypesOrdered, topTypesOrdered_values r2 e2 h2]; rfl
  | .seq (.port _ _) r2, e, h => by
    simp only [bodyExp] at h
    obtain ⟨e2, h2, -⟩ := Option.map_eq_some_iff.mp h
    simp only [topTypesOrdered, topTypesOrdered_values r2 e2 h2]; rfl
  | .seq (.types _ _) _, _, h | .seq (.seq _ _) _, _, h
  | .types _ _, _, h => by simp [bodyExp] at h

theorem typesOrdered_of_W {fuel : Nat} {B : SBasis} {m : BModule} {a : AModule} {C : Ctx}
    (h : inferModuleW fuel B m = .ok a) (hC : importCtx B m.imports = some C) : TypesOrdered m := by
  unfold TypesOrdered
  rcases shape h hC with ⟨hm, -⟩ | ⟨av, -, e, hm, -, hbe, -⟩ | ⟨db, tbs, TE, VE, hm, -, htw⟩ |
      ⟨db, tbs, TE, VE, av, -, e, hm, -, htw, hbe, -⟩
  · rw [hm]; rfl
  · rw [hm]; exact topTypesOrdered_values _ e hbe
  · rw [hm]; exact (typesW_spec htw).2.1
  · rw [hm]
    simp only [Option.map_some, Option.getD_some, topTypesOrdered, Bool.and_eq_true]
    exact ⟨(typesW_spec htw).2.1, topTypesOrdered_values _ e hbe⟩

theorem importCtx_of_ok {fuel : Nat} {B : SBasis} {m : BModule} {a : AModule} (h : inferModuleW fuel B m = .ok a) :
    ∃ C, importCtx B m.imports = some C := by
  obtain ⟨C, hC, -⟩ := inferModuleW_ok_inv h; exact ⟨C, hC⟩

/-- The next basis keeps the invariant, and W's module has its result. -/
theorem step_ok {fuel : Nat} {B : SBasis} {m : BModule} {a : AModule} (hB : BasisInv B)
    (h : inferModuleW fuel B m = .ok a) :
    a.erase = m ∧ IsPrincipalMod B a ∧ ∃ R E, a.result B = some (R, E) ∧ BasisInv (B.plus R) := by
  obtain ⟨he, hp⟩ := inferModuleW_principal hB h
  obtain ⟨C, hC⟩ := importCtx_of_ok h
  have ho : TypesOrdered a.erase := he ▸ typesOrdered_of_W h hC
  have hI : InstanceOfMod B a a := hp.2.2 a hp.1 hp.2.1 rfl
  obtain ⟨-, -, R, E, -, -, hr, -, hBn⟩ := MStep.moduleStep B a a hB ho hp.1 hp.1 hp.2.1 hp.2.1 hI hI
  exact ⟨he, hp, R, E, hr, hBn⟩

/-! ## Principality -/

theorem principal_gen {fuel : Nat} : ∀ (ms : List BModule) (B : SBasis) (as : AProgram), BasisInv B →
    inferProgramW fuel B ms = .ok as →
      as.map AModule.erase = ms ∧ ∃ Bs, AProgram.bases B as = some Bs ∧
        ∀ i (h : i < as.length) (h' : i < Bs.length), IsPrincipalMod Bs[i] as[i]
  | [], B, as, _, h => by
    simp only [inferProgramW, PRes.ok.injEq] at h; subst h
    exact ⟨rfl, [], rfl, fun i h => by simp at h⟩
  | m :: ms, B, as, hB, h => by
    simp only [inferProgramW] at h
    split at h
    · rename_i a hw
      obtain ⟨he, hp, R, E, hr, hBn⟩ := step_ok hB hw
      rw [hr] at h
      simp only at h
      cases hrest : inferProgramW fuel (B.plus R) ms with
      | ok as' =>
        rw [hrest] at h
        cases h
        obtain ⟨he', Bs', hbs, hps⟩ := principal_gen ms (B.plus R) as' hBn hrest
        refine ⟨by simp [he, he'], B :: Bs', by simp [AProgram.bases, hr, hbs], fun i hi hi' => ?_⟩
        cases i with
        | zero => exact hp
        | succ j => exact hps j (by simpa using hi) (by simpa using hi')
      | fail => rw [hrest] at h; cases h
      | other => rw [hrest] at h; cases h
    · cases h
    · cases h

/-- Program principality (finding B1): W's derivation of a program gives every module a principal
    derivation in the basis the earlier ones build. -/
theorem inferProgramW_principal {fuel : Nat} {B : SBasis} {p : BProgram} {as : AProgram} (hB : BasisInv B)
    (h : inferProgramW fuel B p.modules = .ok as) : PrincipalProgDeriv B p as := by
  obtain ⟨he, Bs, hbs, hps⟩ := principal_gen p.modules B as hB h
  exact ⟨⟨by simp [checkProgram, hbs], he⟩, Bs, hbs, hps⟩

/-! ## Refutation -/

theorem fail_gen {fuel : Nat} : ∀ (ms : List BModule) (B : SBasis) (ρ ρ' : List (TyName × TyName)),
    NRInv ρ ρ' → BasisInv B → inferProgramW fuel B ms = .fail → ∀ τ PE, ¬ ElProgram ((nr ρ).basis B) ms τ PE
  | [], B, _, _, _, _, h, _, _, _ => by simp [inferProgramW] at h
  | m :: ms, B, ρ, ρ', hi, hB, h, τ, PE, hel => by
    obtain ⟨m0, rest, B', E', hc, hd, -, hrest⟩ := elProgram_inv hel
    simp only [List.cons.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨a', hea', hPa', hra', -⟩ := hd
    have hB2 : (nr ρ').basis ((nr ρ).basis B) = B := nr_inv_basis hi.left B
    have hc'' : checkModule B (a'.rename (nr ρ')) = true := by rw [← hB2, nr_checkModule hi.h', hPa'.1]
    have hn'' : (a'.rename (nr ρ')).NoFreeBnd := nr_noFreeBnd hi.symm hPa'.2.1
    have he'' : (a'.rename (nr ρ')).erase = m := by rw [AModule.erase_rename, hea']
    simp only [inferProgramW] at h
    split at h
    · rename_i a hw
      obtain ⟨hea, hPa, R, E, hr, hBn⟩ := step_ok hB hw
      rw [hr] at h
      simp only at h
      have hrestW : inferProgramW fuel (B.plus R) ms = .fail := by
        cases hrest : inferProgramW fuel (B.plus R) ms with
        | ok _ => rw [hrest] at h; cases h
        | fail => rfl
        | other => rw [hrest] at h; cases h
      · -- the two principal derivations of the module are instances of each other
        have hI1 : InstanceOfMod B (a'.rename (nr ρ')) a := hPa.2.2 _ hc'' hn'' (by rw [he'', hea])
        have hcs : checkModule ((nr ρ).basis B) (a.rename (nr ρ)) = true := by rw [nr_checkModule hi.h, hPa.1]
        have hI2' : InstanceOfMod ((nr ρ).basis B) (a.rename (nr ρ)) a' :=
          hPa'.2.2 _ hcs (nr_noFreeBnd hi hPa.2.1) (by rw [AModule.erase_rename, hea, hea'])
        have hI2 : InstanceOfMod B a (a'.rename (nr ρ')) := by
          have := instanceOfMod_nr hi.symm hI2'
          rwa [hB2, nr_inv_module hi.left] at this
        obtain ⟨C, hC⟩ := importCtx_of_ok hw
        have ho : TypesOrdered a.erase := hea ▸ typesOrdered_of_W hw hC
        obtain ⟨σ, σ', R1, E1, hσ, hfix, hr1, hr'', -⟩ :=
          MStep.moduleStep B a (a'.rename (nr ρ')) hB ho hPa.1 hc'' hPa.2.1 hn'' hI1 hI2
        rw [hr] at hr1
        simp only [Option.some.injEq, Prod.mk.injEq] at hr1
        obtain ⟨rfl, rfl⟩ := hr1
        have hback : (a'.rename (nr ρ')).rename (nr ρ) = a' := nr_inv_module hi.right a'
        have hr' : a'.result ((nr ρ).basis B) = some ((nr ρ).basis ((nr σ).basis R), (nr ρ).env ((nr σ).env E)) := by
          rw [← hback, nr_result hi.h, hr'']; rfl
        rw [hra'] at hr'
        simp only [Option.some.injEq, Prod.mk.injEq] at hr'
        obtain ⟨rfl, -⟩ := hr'
        cases ms with
        | nil => simp [inferProgramW] at hrestW
        | cons m2 ms2 =>
          obtain ⟨τ', PE', hel'⟩ := hrest (by simp)
          have hcomp := fun t => (nrComp_tn (ρ := ρ) (σ := σ) t).symm
          have hBnext : ((nr ρ).basis B).plus ((nr ρ).basis ((nr σ).basis R)) = (nr (nrComp ρ σ)).basis (B.plus R) := by
            rw [nr_basis_plus (hi.comp hσ).h, ← nr_comp2_basis hcomp, ← nr_comp2_basis hcomp, hfix]
          rw [hBnext] at hel'
          exact fail_gen (m2 :: ms2) (B.plus R) _ _ (hi.comp hσ) hBn hrestW τ' PE' hel'
    · rename_i hw
      -- the module itself fails: no derivation of it in `B`, so none in the renamed basis
      have hnd := inferModuleW_fail hB hw
      rw [hnd _ he''] at hc''
      cases hc''
    · cases h

/-- Refutation for programs (section 7, "Programs"): if W fails on a module of the program, the
    program has no derivation. -/
theorem inferProgramW_fail {fuel : Nat} {B : SBasis} {p : BProgram} (hB : BasisInv B)
    (h : inferProgramW fuel B p.modules = .fail) : ¬ ∃ τ PE, ElProgram B p.modules τ PE := by
  rintro ⟨τ, PE, hel⟩
  rw [← nr_nil_basis B] at hel
  exact fail_gen p.modules B [] [] NRInv.nil hB h τ PE hel

end MW
end StandardElm.Stat.Complete

namespace StandardElm.Stat
open StandardElm.Stat.Complete

/-- The refusal theorem of milestone (f): a program on a module of which W fails is not legal.
    Unconditional: no principality hypothesis (W's own principality is proved) and no coherence
    hypothesis (ruling A98). -/
theorem not_legal_of_wRefutes {B : SBasis} {sp : Src.SProgram} (hB : BasisInv B)
    (h : MW.wRefutes B sp = true) : ¬ LegalProgram B sp := by
  unfold MW.wRefutes at h
  split at h
  · rename_i hf
    exact fun hl => MW.inferProgramW_fail (p := Src.deriveProgram (Src.canonOrder sp)) hB hf hl.2
  · cases h

end StandardElm.Stat
