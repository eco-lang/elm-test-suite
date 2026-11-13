/-
  A Standard Definition of Elm? Mechanisation: the types W's final result records are `OkTD`
  (plan step 11, milestone (d), section 7), for the node correspondence at the root.

  W returns `ar` with its recorded types `OkTD` (`tysExp true`, the declarations' environments and
  the annotation marks included), and its result is `x = θ ar`, which the checker accepts. The
  types `x` records outside declarations' environments are `OkTD` when the derivation fixes them
  (`tysExp false`); then all are (`okAD_true`): the annotation marks are those of `ar` (none), and
  a declaration's environment in `x` is its value binding's (the checker), whose variables are
  among the binding's types.
-/
import StandardElmMech.Stat.Complete.WDNodeRelExp

namespace StandardElm.Stat.Complete.WDP
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Stat.Complete

theorem OkAD.app' {n : Nat} {l1 l2 : List Ty} (h1 : OkAD n l1) (h2 : OkAD n l2) : OkAD n (l1 ++ l2) := fun τ hτ => by
  rcases List.mem_append.mp hτ with h | h
  · exact h1 τ h
  · exact h2 τ h

section
variable (s : RSub) (n : Nat)

mutual
theorem okAD_trueAt : ∀ (y : AAtExp) (C : Ctx), checkAtExp C (rsbAtExp s y) = true → OkAD n (tysAtExp true y) →
    OkAD n (tysAtExp false (rsbAtExp s y)) → OkAD n (tysAtExp true (rsbAtExp s y))
  | .scon _ _, _, _, _, h | .var _ _ _, _, _, _, h | .con _ _ _, _, _, _, h | .op _ _ _, _, _, _, h
  | .nil _, _, _, _, h | .unit, _, _, _, h => h
  | .tuple e1 e2 e3, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp, Bool.and_eq_true] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    obtain ⟨hy12, hy3⟩ := OkAD.split hy; obtain ⟨hy1, hy2⟩ := OkAD.split hy12
    obtain ⟨hf12, hf3⟩ := OkAD.split hf; obtain ⟨hf1, hf2⟩ := OkAD.split hf12
    exact OkAD.app' (OkAD.app' (okAD_trueExp e1 C hc.1.1 hy1 hf1) (okAD_trueExp e2 C hc.1.2 hy2 hf2))
      (okAD_trueExpOpt e3 C hc.2 hy3 hf3)
  | .record r, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    exact okAD_trueRowOpt r C hc hy hf
  | .update x inst τ r, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp, Bool.and_eq_true] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    exact OkAD.cons (hf _ (.head _)) (okAD_trueRow r C hc.1.2 (OkAD.tail hy) (OkAD.tail hf))
  | .letE d e, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp, Bool.and_eq_true] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueDec d C hc.1 hy1 hf1) (okAD_trueExp e _ hc.2 hy2 hf2)
  | .paren e, C, hc, hy, hf => by
    simp only [rsbAtExp, checkAtExp] at hc
    simp only [rsbAtExp, tysAtExp] at hy hf ⊢
    exact okAD_trueExp e C hc hy hf
theorem okAD_trueRow : ∀ (y : AExpRow) (C : Ctx), checkExpRow C (rsbExpRow s y) = true → OkAD n (tysExpRow true y) →
    OkAD n (tysExpRow false (rsbExpRow s y)) → OkAD n (tysExpRow true (rsbExpRow s y))
  | .field l e rest, C, hc, hy, hf => by
    simp only [rsbExpRow, checkExpRow, Bool.and_eq_true] at hc
    simp only [rsbExpRow, tysExpRow] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueExp e C hc.1 hy1 hf1) (okAD_trueRowOpt rest C hc.2 hy2 hf2)
theorem okAD_trueRowOpt : ∀ (y : Option AExpRow) (C : Ctx), checkExpRowOpt C (rsbExpRowOpt s y) = true →
    OkAD n (tysExpRowOpt true y) → OkAD n (tysExpRowOpt false (rsbExpRowOpt s y)) →
    OkAD n (tysExpRowOpt true (rsbExpRowOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some r, C, hc, hy, hf => by
    simp only [rsbExpRowOpt, checkExpRowOpt, tysExpRowOpt] at hc hy hf ⊢
    exact okAD_trueRow r C hc hy hf
theorem okAD_trueExp : ∀ (y : AExp) (C : Ctx), checkExpS C (rsbExp s y) = true → OkAD n (tysExp true y) →
    OkAD n (tysExp false (rsbExp s y)) → OkAD n (tysExp true (rsbExp s y))
  | .atexp a, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    exact okAD_trueAt a C hc hy hf
  | .app e a, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS, Bool.and_eq_true] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueExp e C hc.1.1 hy1 hf1) (okAD_trueAt a C hc.1.2 hy2 hf2)
  | .lam p e, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS, Bool.and_eq_true] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' hf1 (okAD_trueExp e _ hc.2 hy2 hf2)
  | .caseE e m, C, hc, hy, hf => by
    simp only [rsbExp, checkExpS, Bool.and_eq_true] at hc
    simp only [rsbExp, tysExp] at hy hf ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' (okAD_trueExp e C hc.1.1 hy1 hf1) (okAD_trueMatch m C hc.1.2 hy2 hf2)
theorem okAD_trueExpOpt : ∀ (y : Option AExp) (C : Ctx), checkExpOpt C (rsbExpOpt s y) = true →
    OkAD n (tysExpOpt true y) → OkAD n (tysExpOpt false (rsbExpOpt s y)) → OkAD n (tysExpOpt true (rsbExpOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some e, C, hc, hy, hf => by
    simp only [rsbExpOpt, checkExpOpt, tysExpOpt] at hc hy hf ⊢
    exact okAD_trueExp e C hc hy hf
theorem okAD_trueMatch : ∀ (y : AMatch) (C : Ctx), checkMatch C (rsbMatch s y) = true → OkAD n (tysMatch true y) →
    OkAD n (tysMatch false (rsbMatch s y)) → OkAD n (tysMatch true (rsbMatch s y))
  | .mk (.mk p e) rest, C, hc, hy, hf => by
    simp only [rsbMatch, rsbMRule, checkMatch, checkMRule, Bool.and_eq_true] at hc
    simp only [rsbMatch, rsbMRule, tysMatch, tysMRule] at hy hf ⊢
    obtain ⟨hy12, hy3⟩ := OkAD.split hy; obtain ⟨hy1, hy2⟩ := OkAD.split hy12
    obtain ⟨hf12, hf3⟩ := OkAD.split hf; obtain ⟨hf1, hf2⟩ := OkAD.split hf12
    refine OkAD.app' (OkAD.app' hf1 (okAD_trueExp e _ hc.1.2 hy2 hf2)) (okAD_trueMatchOpt rest C (fun m0 hm0 => ?_) hy3 hf3)
    have := hc.2
    cases rest with
    | none => cases hm0
    | some m =>
      simp only [rsbMatchOpt, Option.some.injEq] at hm0; subst hm0
      simp only [rsbMatchOpt, checkMatchOptAt, Bool.and_eq_true] at this
      exact this.1
theorem okAD_trueMatchOpt : ∀ (y : Option AMatch) (C : Ctx), (∀ m0, rsbMatchOpt s y = some m0 → checkMatch C m0 = true) →
    OkAD n (tysMatchOpt true y) → OkAD n (tysMatchOpt false (rsbMatchOpt s y)) → OkAD n (tysMatchOpt true (rsbMatchOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some m, C, hc, hy, hf => by
    simp only [rsbMatchOpt, tysMatchOpt] at hy hf ⊢
    exact okAD_trueMatch m C (hc _ rfl) hy hf
theorem okAD_trueDec : ∀ (y : ADec) (C : Ctx), checkDec C (rsbDec s y) = true → OkAD n (tysDec true y) →
    OkAD n (tysDec false (rsbDec s y)) → OkAD n (tysDec true (rsbDec s y))
  | .val VE vb, C, hc, hy, hf => by
    simp only [rsbDec, checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [rsbDec, tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hy hf ⊢
    obtain ⟨-, hy2⟩ := OkAD.split hy
    have hvb := okAD_trueValBind vb _ hc.1 hy2 hf
    refine OkAD.app' (fun τ hτ => ?_) hvb
    have hann := annNilV_of_okAD _ hvb
    simp only [veBodies, List.mem_map] at hτ
    obtain ⟨q, hq, rfl⟩ := hτ
    rw [← hc.2] at hq
    exact okT_pentD hf (valbind_ve_pent false _ hann q hq)
theorem okAD_trueValBind : ∀ (y : AValBind) (C : Ctx), checkValBind C (rsbValBind s y) = true →
    OkAD n (tysValBind true y) → OkAD n (tysValBind false (rsbValBind s y)) → OkAD n (tysValBind true (rsbValBind s y))
  | .var x ann τ e rest, C, hc, hy, hf => by
    simp only [rsbValBind, checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [rsbValBind, tysValBind, List.cons_append, annMark, Bool.false_eq_true, ↓reduceIte,
      List.nil_append] at hy hf ⊢
    have hann : annU ann = [] := annU_of_okAD fun τ hτ => hy τ (by simp only [annMark] at hτ ⊢; simp [hτ])
    simp only [hann, ↓reduceIte, List.nil_append] at hy ⊢
    obtain ⟨hy1, hy2⟩ := OkAD.split (OkAD.tail hy); obtain ⟨hf1, hf2⟩ := OkAD.split (OkAD.tail hf)
    exact OkAD.cons (hf _ (.head _)) (OkAD.app' (okAD_trueExp e _ hc.1.1.2 hy1 hf1)
      (okAD_trueValBindOpt rest C hc.2 hy2 hf2))
  | .pat p e, C, hc, hy, hf => by
    simp only [rsbValBind, checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [rsbValBind, tysValBind] at hy hf ⊢
    obtain ⟨-, hy2⟩ := OkAD.split hy; obtain ⟨hf1, hf2⟩ := OkAD.split hf
    exact OkAD.app' hf1 (okAD_trueExp e C hc.1.2 hy2 hf2)
theorem okAD_trueValBindOpt : ∀ (y : Option AValBind) (C : Ctx), checkValBindOpt C (rsbValBindOpt s y) = true →
    OkAD n (tysValBindOpt true y) → OkAD n (tysValBindOpt false (rsbValBindOpt s y)) →
    OkAD n (tysValBindOpt true (rsbValBindOpt s y))
  | none, _, _, _, _ => fun _ h => nomatch h
  | some vb, C, hc, hy, hf => by
    simp only [rsbValBindOpt, checkValBindOpt, tysValBindOpt] at hc hy hf ⊢
    exact okAD_trueValBind vb C hc hy hf
end

end

end StandardElm.Stat.Complete.WDP
