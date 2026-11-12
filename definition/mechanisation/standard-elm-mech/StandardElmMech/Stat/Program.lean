/-
  A Standard Definition of Elm? Mechanisation: the static rules of Chapter 9 (programs.tex,
  sec:programs-elaboration), plan step 9 (section 5): Dflt, the three rules, and legality of a
  program as written.
-/
import StandardElmMech.Stat.Principal
import StandardElmMech.Stat.PatternsProof
import StandardElmMech.Src.SynSet
import StandardElmMech.Src.Derive

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BModule)

/-- Dflt σ: Float for each bound type variable of class num. -/
def dflt (σ : Scheme) : Ty :=
  let S : Subst := ⟨σ.bound.filterMap (fun v => match v with
    | .ty a => if a.cls = .num then some (a, tFloatTy) else none
    | .row _ => none), []⟩
  (S.apply σ.body).getD σ.body

/-- The premise "B ⊢ mod ⇒ B', E, inferred by a principal derivation for the module", with the
    further restrictions judged on that derivation (sec:static-modules-further, A96). -/
def PrincipalModDer (B : SBasis) (m : BModule) (B' : SBasis) (E : Env) : Prop :=
  ∃ a : AModule, a.erase = m ∧ IsPrincipalMod B a ∧ a.result B = some (B', E) ∧ FurtherMod B a

/-- Dom(PE of B') ∩ (Dom(PE of B) ∪ Mgr_plat) = ∅. -/
def PortsDisjoint (B B' : SBasis) : Prop := ∀ x ∈ B'.PE.keys, x ∉ B.PE.keys ∧ x ∉ Src.managersPlat

set_option autoImplicit true

/-- B_stat ⊢_STAT program ⇒ (τ, PE) -/
inductive ElProgram : SBasis → List BModule → Ty → PortEnv → Prop where
  /-- r:p-stat-module -/
  | r_p_stat_module : PrincipalModDer B m B' E → PortsDisjoint B B' → ms ≠ [] →
      ElProgram (B.plus B') ms τ PE → ElProgram B (m :: ms) τ PE
  /-- r:p-stat-main-program -/
  | r_p_stat_main_program : PrincipalModDer B m B' E → PortsDisjoint B B' →
      E.VE.find? "main" = some (σ, .v) → σ.body = .con [τ1, τ2, τ3] tProgram → Port τ1 →
      ElProgram B [m] (dflt σ) (B.plus B').PE
  /-- r:p-stat-main-view -/
  | r_p_stat_main_view : PrincipalModDer B m B' E → PortsDisjoint B B' →
      E.VE.find? "main" = some (σ, .v) → dflt σ = .con [τ] tNode →
      ElProgram B [m] (.con [τ] tNode) (B.plus B').PE

/-- A program as written is legal: it meets the syntactic restrictions (as a set of modules) and
    elaborates by Chapter 9's rules, every module by a principal derivation meeting the further
    restrictions. The derived forms are step 8's canonical choice (B4). -/
def LegalProgram (B : SBasis) (sp : Src.SProgram) : Prop :=
  Src.SynOKSet sp ∧ ∃ τ PE, ElProgram B (Src.deriveProgram (Src.canonOrder sp)).modules τ PE

end StandardElm.Stat
