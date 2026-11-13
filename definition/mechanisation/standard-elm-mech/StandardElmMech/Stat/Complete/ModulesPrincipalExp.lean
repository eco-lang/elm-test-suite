/-
  A Standard Definition of Elm? Mechanisation: W's principality for expressions with the instance
  fixing given `bnd` variables (milestone (f) of plan step 11). `WE.wePrincipality`'s argument,
  with the substitution of the instance asked also to leave alone a list of `bnd` variables: the
  substitution is the one W's main induction gives (L11), which fixes every rigid variable, and
  every `bnd` variable is rigid (`rigidFromD_bnd`). Used for a module, whose type declarations'
  node holds `bnd` variables only (the parameters of type functions and the bound variables of
  closed schemes), which the instance must then leave alone.
-/
import StandardElmMech.Stat.Complete.WEPrincipality

set_option linter.unusedSectionVars false

namespace StandardElm.Stat.Complete
namespace WE
open StandardElm.Stat
open StandardElm.Stat.Complete.WDP
open StandardElm.Stat.Complete.WE.WDP

/-- `wePrincipality` with the instance's substitution fixing the rigid (`bnd` or named) variables of `A` too. -/
theorem wePrincipalityA (fuel : Nat) (C0 : Ctx) (e : StandardElm.Src.BExp) (a : AExp) (hC : RootOKD C0)
    (h : inferExpWD fuel C0 e = .ok a) (A : List BVar) (hA : ∀ v ∈ A, rigidFromD (freshAboveD C0) v = true) :
    ∀ a', checkExp C0 a' = true → a'.erase = a.erase →
      InstanceNodes (C0.tyvars ++ A) (nodesExp C0 [] a') (nodesExp C0 [] a) := by
  obtain ⟨hc, he, -⟩ := inferExpWD_sound h
  intro a' hc' he'
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
        rw [hs', nodesExp_strip, nodesExp_strip] at hF2
        have hroot : ∀ v ∈ C0.tyvars ++ A, T.img v = vty v := by
          intro v hv
          rcases List.mem_append.mp hv with hv | hv
          · exact hfx v (rigid_of_oldD (old_of_rootD hv))
          · exact hfx v (hA v hv)
        refine instanceNodes_of_F2E hF2 (nodesExp_pd C0 _ []).1 hcls hroot fun n hn τ hτ => ?_
        obtain ⟨n', hn', hr⟩ := f2_mem_left hF2 n hn
        exact hcn' n' hn' _ (by rw [hr.2.2.2.1]; exact List.mem_map_of_mem hτ)
      · cases h
    · cases h
  · cases h
  · cases h
  · cases h

end WE
end StandardElm.Stat.Complete
