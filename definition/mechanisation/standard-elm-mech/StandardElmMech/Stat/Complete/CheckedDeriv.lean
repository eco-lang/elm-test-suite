/-
  A Standard Definition of Elm? Mechanisation: what step 9's checker guarantees of the derivations
  it accepts (plan step 11). The checker asks every type at a node of a derivation to be `Ty.okB`
  (canonical rows, no free `bnd` variable) and every annotation's `U'` to be `newU`; so the
  restrictions step 11 first put on the derivations compared are consequences:
  `noFreeBndExp_of_checkExp` (WPrincipal.lean), `canonExp_of_checkExp` (WDUnify.lean),
  `WE.canonAnnExp_of_checkExp` (WETheorems.lean) for expressions, and here for modules
  `noFreeBnd_of_checkModule`: `IsPrincipalMod`'s restriction to derivations without free `bnd`
  variables is no restriction (`isPrincipalMod_iff`).
-/
import StandardElmMech.Stat.Complete.WTheorems
import StandardElmMech.Stat.Complete.NodesOk

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-- The types at the nodes of a value declaration, in any context and at any path, are `Ty.okB`
    when the checker's `okValBindB` holds. -/
theorem okB_nodesValBind {vb : AValBind} (h : okValBindB vb = true) (C : Ctx) (path : List Nat) :
    ∀ n ∈ nodesValBind C path vb, ∀ τ ∈ n.tys, Ty.okB τ = true :=
  (nodesOkB_iff _).mp ((nodesOkB_nodesValBind C path vb).trans h)

theorem checkTopDec_noFreeBnd : ∀ (d : ATopDec) (C : Ctx) (p : Env × PortEnv), checkTopDec C d = some p → d.NoFreeBnd
  | .value VE vb, C, p, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      intro C' path' n hn τ hτ v hv
      exact ((Ty.okB_iff τ).mp (okB_nodesValBind hc.2 C' path' n hn τ hτ)).2 v hv
    · cases h
  | .types _ _ _ _, _, _, _ => trivial
  | .port _ _ _, _, _, _ => trivial
  | .seq a1 a2, C, p, h => by
    simp only [checkTopDec] at h
    cases h1 : checkTopDec C a1 with
    | none => rw [h1] at h; cases h
    | some p1 =>
      obtain ⟨E1, PE1⟩ := p1
      rw [h1] at h
      simp only at h
      cases h2 : checkTopDec (C.oplusE E1) a2 with
      | none => rw [h2] at h; cases h
      | some p2 => exact ⟨checkTopDec_noFreeBnd a1 C _ h1, checkTopDec_noFreeBnd a2 _ p2 h2⟩

/-- Step 9's checker rejects a free `bnd` variable at a node of a module's value declarations. -/
theorem noFreeBnd_of_checkModule {B : SBasis} {a : AModule} (h : checkModule B a = true) : a.NoFreeBnd := by
  intro d hd
  simp only [checkModule, AModule.result] at h
  cases hC : importCtx B a.imports with
  | none => rw [hC] at h; cases h
  | some C =>
    rw [hC] at h
    simp only [AModule.resultIn, checkTopDecOpt, hd] at h
    cases hp : checkTopDec C d with
    | none => rw [hp] at h; cases h
    | some p => exact checkTopDec_noFreeBnd d C p hp

/-- `IsPrincipalMod` restricts to derivations without free `bnd` variables, which every
    derivation the checker accepts is: it is principality among all derivations. -/
theorem isPrincipalMod_iff {B : SBasis} {a : AModule} :
    IsPrincipalMod B a ↔
      checkModule B a = true ∧ ∀ a', checkModule B a' = true → a'.erase = a.erase → InstanceOfMod B a' a := by
  constructor
  · rintro ⟨hc, -, h⟩
    exact ⟨hc, fun a' hc' he => h a' hc' (noFreeBnd_of_checkModule hc') he⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, noFreeBnd_of_checkModule hc, fun a' hc' _ he => h a' hc' he⟩

end StandardElm.Stat.Complete
