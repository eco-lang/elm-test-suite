/-
  A Standard Definition of Elm? Mechanisation: L10 of plan step 11 (milestone (b), section 8) and
  the completeness of W for fragment F_c.

  * `wResultChecks`: on a successful run from the root, step 9's checker accepts W's final
    result (`WResultChecks`); the induction is `WSoundExp.lean`'s, instantiated with the final
    substitution itself (it fixes the rigid variables, absorbs itself and respects every
    closure's constraint), in the root context, which the final substitution leaves unchanged
    (`ctxSb_root`).
  * `wCompleteness`: section 7's completeness for F_c (`WCompleteness`): when a derivation
    exists, W neither fails nor returns `internal` for any fuel, and for some fuel it does not run
    out.
-/
import StandardElmMech.Stat.Complete.WSoundExp

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-- The root context and the initial state satisfy the precondition of the induction. -/
theorem root_spre {C0 : Ctx} (hC : RootOK C0) : SPre (freshAbove C0) C0 ⟨[], freshAbove C0⟩ :=
  ⟨⟨Nat.le_refl _, goodC_nil _ (fun _ h => nomatch h), fun _ h => nomatch h⟩, fun a _ h => absurd (lk_nil a) h,
   root_ctxW hC, fun a ha => rigid_of_old (old_of_root (mem_ctx_tyvars.mpr (.inl ha))), fun _ _ => trivial⟩

/-- L10: the checker accepts the final substitution applied to what W built. -/
theorem wResultChecks : WResultChecks := by
  intro fuel C0 e τ ar st hC h _
  obtain ⟨K, P⟩ := wExp_sound fuel _ e C0 _ (τ, ar) st (root_spre hC) h
  have hi := P.seg.inv
  have hc := (P.chk (lk st.θ) hi.sok (absorbs_self hi.good.idem) P.ks.dead).1
  rwa [ctxSb_root hi.good.fixesR] at hc

/-- Completeness of W for F_c (section 7). -/
theorem wCompleteness : WCompleteness := wCompleteness_of_checks wResultChecks

end StandardElm.Stat.Complete
