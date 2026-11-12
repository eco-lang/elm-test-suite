/-
  A Standard Definition of Elm? Mechanisation: refusals, plan step 9 (section "Theorems", group 8,
  milestone 9d). A program is not legal when it breaks a syntactic restriction, or when its first
  module has no derivation that checks, or when no derivation of its one module meets the further
  restrictions, or gives `main` a type of Chapter 9.

  Every refusal is unconditional: it holds of every derivation, so in particular of the principal
  one, and needs no hypothesis about principality (D11). The deciders that discharge the premises of
  these lemmas for a given program (by the kernel) are in RefuseScope.lean, RefuseTypes.lean and
  RefuseFurther.lean.
-/
import StandardElmMech.Stat.Legal

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BModule SProgram)

/-! ## Inversion of the rules of Chapter 9 -/

/-- What r:p-stat-main-program or r:p-stat-main-view asks of the main module's environment. -/
def MainOK (E : Env) : Prop :=
  ∃ σ, E.VE.find? "main" = some (σ, .v) ∧
    ((∃ τ1 τ2 τ3, σ.body = .con [τ1, τ2, τ3] tProgram ∧ Port τ1) ∨ ∃ τ, dflt σ = .con [τ] tNode)

theorem elProgram_inv {B : SBasis} {ms : List BModule} {τ : Ty} {PE : PortEnv}
    (h : ElProgram B ms τ PE) :
    ∃ m rest B' E, ms = m :: rest ∧ PrincipalModDer B m B' E ∧
      (rest = [] → MainOK E) ∧ (rest ≠ [] → ∃ τ' PE', ElProgram (B.plus B') rest τ' PE') := by
  cases h with
  | r_p_stat_module hd _ hne hrest => exact ⟨_, _, _, _, rfl, hd, fun h => absurd h hne, fun _ => ⟨_, _, hrest⟩⟩
  | r_p_stat_main_program hd _ hm hb hp =>
    exact ⟨_, _, _, _, rfl, hd, fun _ => ⟨_, hm, .inl ⟨_, _, _, hb, hp⟩⟩, fun h => absurd rfl h⟩
  | r_p_stat_main_view hd _ hm hv =>
    exact ⟨_, _, _, _, rfl, hd, fun _ => ⟨_, hm, .inr ⟨_, hv⟩⟩, fun h => absurd rfl h⟩

theorem principalModDer_check {B : SBasis} {m : BModule} {B' : SBasis} {E : Env}
    (h : PrincipalModDer B m B' E) :
    ∃ a, a.erase = m ∧ checkModule B a = true ∧ a.result B = some (B', E) ∧ FurtherMod B a := by
  obtain ⟨a, he, hp, hr, hf⟩ := h
  exact ⟨a, he, hp.1, hr, hf⟩

/-! ## The refusals -/

/-- A program that breaks a syntactic restriction (whatever the order of its modules, step 8). -/
theorem not_legal_of_syn {B : SBasis} {sp : SProgram} (h : ¬ Src.SynOKSet sp) : ¬ LegalProgram B sp :=
  fun hl => h hl.1

/-- No derivation of `m` checks in `B`. -/
def NoDeriv (B : SBasis) (m : BModule) : Prop :=
  ∀ a : AModule, a.erase = m → checkModule B a = false

/-- The first module has no derivation. -/
theorem not_legal_of_noDeriv {B : SBasis} {sp : SProgram} {m : BModule} {rest : List BModule}
    (hms : (Src.deriveProgram (Src.canonOrder sp)).modules = m :: rest) (h : NoDeriv B m) :
    ¬ LegalProgram B sp := by
  rintro ⟨_, τ, PE, hel⟩
  rw [hms] at hel
  obtain ⟨m', _, B', E, hc, hd, _, _⟩ := elProgram_inv hel
  cases hc
  obtain ⟨a, he, hck, _, _⟩ := principalModDer_check hd
  rw [h a he] at hck
  cases hck

/-- The second module has no derivation, whatever the derivation of the first. -/
theorem not_legal_of_noDeriv2 {B : SBasis} {sp : SProgram} {m1 m2 : BModule} {rest : List BModule}
    (hms : (Src.deriveProgram (Src.canonOrder sp)).modules = m1 :: m2 :: rest)
    (h : ∀ a1 B' E, a1.erase = m1 → checkModule B a1 = true → a1.result B = some (B', E) →
      NoDeriv (B.plus B') m2) :
    ¬ LegalProgram B sp := by
  rintro ⟨_, τ, PE, hel⟩
  rw [hms] at hel
  obtain ⟨m', rest', B', E, hc, hd, _, hrest⟩ := elProgram_inv hel
  cases hc
  obtain ⟨a1, he1, hck1, hr1, _⟩ := principalModDer_check hd
  obtain ⟨τ', PE', hel2⟩ := hrest (by simp)
  obtain ⟨m'', _, B'', E'', hc2, hd2, _, _⟩ := elProgram_inv hel2
  cases hc2
  obtain ⟨a2, he2, hck2, _, _⟩ := principalModDer_check hd2
  rw [h a1 B' E he1 hck1 hr1 a2 he2] at hck2
  cases hck2

/-- No derivation of the one module meets the further restrictions. -/
theorem not_legal_of_further {B : SBasis} {sp : SProgram} {m : BModule}
    (hms : (Src.deriveProgram (Src.canonOrder sp)).modules = [m])
    (h : ∀ a : AModule, a.erase = m → checkModule B a = true → ¬ FurtherMod B a) :
    ¬ LegalProgram B sp := by
  rintro ⟨_, τ, PE, hel⟩
  rw [hms] at hel
  obtain ⟨m', _, B', E, hc, hd, _, _⟩ := elProgram_inv hel
  cases hc
  obtain ⟨a, he, hck, _, hf⟩ := principalModDer_check hd
  exact h a he hck hf

/-- No derivation of the one module gives `main` a type of Chapter 9. -/
theorem not_legal_of_main {B : SBasis} {sp : SProgram} {m : BModule}
    (hms : (Src.deriveProgram (Src.canonOrder sp)).modules = [m])
    (h : ∀ (a : AModule) B' E, a.erase = m → a.result B = some (B', E) → ¬ MainOK E) :
    ¬ LegalProgram B sp := by
  rintro ⟨_, τ, PE, hel⟩
  rw [hms] at hel
  obtain ⟨m', rest, B', E, hc, hd, hmain, _⟩ := elProgram_inv hel
  cases hc
  obtain ⟨a, he, _, hr, _⟩ := principalModDer_check hd
  exact h a B' E he hr (hmain rfl)

/-- A module whose imports do not elaborate has no derivation. -/
theorem noDeriv_of_imports {B : SBasis} {m : BModule} (h : importCtx B m.imports = none) : NoDeriv B m := by
  intro a he
  have : a.imports = m.imports := by rw [← he]; rfl
  simp [checkModule, AModule.result, this, h]

/-- The decider for a first module whose imports do not elaborate. -/
def importsFailB (B : SBasis) (sp : SProgram) : Bool :=
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | m :: _ => (importCtx B m.imports).isNone
  | [] => false

theorem not_legal_of_imports {B : SBasis} {sp : SProgram} (h : importsFailB B sp = true) :
    ¬ LegalProgram B sp := by
  unfold importsFailB at h
  split at h
  · rename_i m rest hms
    exact not_legal_of_noDeriv hms (noDeriv_of_imports (Option.isNone_iff_eq_none.mp h))
  · cases h

end StandardElm.Stat
