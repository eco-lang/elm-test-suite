/-
  A Standard Definition of Elm? Mechanisation: L10 for W with records and rows (plan step 11,
  milestone (d), section 8) and the completeness of `inferExpWD` (`wdCompleteness`).

  * `wdResultChecks`: on a successful run from a `RootOKD` context, when a derivation exists,
    step 9's checker accepts W's final result (the types W records are `Ty.okB`: their images by
    the substitution relating W's result to the derivation are the derivation's). The
    induction (WDSoundExp.lean) is instantiated with the final substitution itself and, for the
    canonicity unification needs, with the substitution `T` relating W's result to the
    derivation (L11, `wdExp_root`): `T` absorbs the final substitution and maps the types W
    records to the derivation's, which are canonical; the derivation's instances of the
    constructors of its patterns are the witnesses (`cwExp_nav`).
  * The hypothesis is needed: from a `RootOKD` context whose constructor has a lacks constraint
    between two arguments (`C : ∀ρ. ⟨ρ⟩ → ⟨a : Int | ρ⟩ → T`), the pattern `C {a} {a}` binds
    `ρ ↦ ⟨a : α | ε⟩` at the first argument; the second argument's type `⟨a : Int | ρ⟩`, never
    recorded, then has a label twice, unification of `⟨a : β | ε'⟩` with it succeeds, every
    recorded type is canonical, and the checker refuses the instance: `inferExpWD` returns
    `internal`. No derivation of that pattern exists.
  * `wdCompleteness : WDCompleteness`, by `wdCompleteness_of_ne_internal`.
-/
import StandardElmMech.Stat.Complete.WDSoundExp
import StandardElmMech.Stat.Complete.NodesOk

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind)

namespace WDS

/-! ## Erasure under substitution -/

mutual
theorem rsbAtPat_eraseD (s : RSub) : ∀ p : AAtPat, (rsbAtPat s p).erase = p.erase
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit => rfl
  | .tuple p1 p2 p3 => by
    simp only [rsbAtPat, AAtPat.erase, rsbPat_eraseD s p1, rsbPat_eraseD s p2, rsbPatOpt_eraseD s p3]
  | .record r _ => by simp only [rsbAtPat, AAtPat.erase, rsbPatRowOpt_eraseD s r]
  | .paren p => by simp only [rsbAtPat, AAtPat.erase, rsbPat_eraseD s p]
theorem rsbPatRowOpt_eraseD (s : RSub) : ∀ r : Option APatRow, APatRow.eraseOpt (rsbPatRowOpt s r) = APatRow.eraseOpt r
  | none => rfl
  | some (.field _ _ rest) => by
    simp only [rsbPatRowOpt, rsbPatRow, APatRow.eraseOpt, APatRow.erase, rsbPatRowOpt_eraseD s rest]
theorem rsbPat_eraseD (s : RSub) : ∀ p : APat, (rsbPat s p).erase = p.erase
  | .atpat a => by simp only [rsbPat, APat.erase, rsbAtPat_eraseD s a]
  | .con _ _ args _ => by simp only [rsbPat, APat.erase, rsbAtPats_eraseD s args]
  | .cons p1 p2 => by simp only [rsbPat, APat.erase, rsbPat_eraseD s p1, rsbPat_eraseD s p2]
  | .as p _ => by simp only [rsbPat, APat.erase, rsbPat_eraseD s p]
theorem rsbPatOpt_eraseD (s : RSub) : ∀ p : Option APat, APat.eraseOpt (rsbPatOpt s p) = APat.eraseOpt p
  | none => rfl
  | some p => by simp only [rsbPatOpt, APat.eraseOpt, rsbPat_eraseD s p]
theorem rsbAtPats_eraseD (s : RSub) : ∀ l : List AAtPat, AAtPat.eraseList (rsbAtPats s l) = AAtPat.eraseList l
  | [] => rfl
  | a :: as => by simp only [rsbAtPats, AAtPat.eraseList, rsbAtPat_eraseD s a, rsbAtPats_eraseD s as]
end

mutual
theorem rsbAtExp_eraseD (s : RSub) : ∀ a : AAtExp, (rsbAtExp s a).erase = a.erase
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [rsbAtExp, AAtExp.erase, rsbExp_eraseD s e1, rsbExp_eraseD s e2, rsbExpOpt_eraseD s e3]
  | .record r => by simp only [rsbAtExp, AAtExp.erase, rsbExpRowOpt_eraseD s r]
  | .update _ _ _ r => by simp only [rsbAtExp, AAtExp.erase, rsbExpRow_eraseD s r]
  | .letE d e => by simp only [rsbAtExp, AAtExp.erase, rsbDec_eraseD s d, rsbExp_eraseD s e]
  | .paren e => by simp only [rsbAtExp, AAtExp.erase, rsbExp_eraseD s e]
theorem rsbExpRow_eraseD (s : RSub) : ∀ r : AExpRow, (rsbExpRow s r).erase = r.erase
  | .field _ e rest => by simp only [rsbExpRow, AExpRow.erase, rsbExp_eraseD s e, rsbExpRowOpt_eraseD s rest]
theorem rsbExpRowOpt_eraseD (s : RSub) : ∀ r : Option AExpRow, AExpRow.eraseOpt (rsbExpRowOpt s r) = AExpRow.eraseOpt r
  | none => rfl
  | some r => by simp only [rsbExpRowOpt, AExpRow.eraseOpt, rsbExpRow_eraseD s r]
theorem rsbExp_eraseD (s : RSub) : ∀ e : AExp, (rsbExp s e).erase = e.erase
  | .atexp a => by simp only [rsbExp, AExp.erase, rsbAtExp_eraseD s a]
  | .app e a => by simp only [rsbExp, AExp.erase, rsbExp_eraseD s e, rsbAtExp_eraseD s a]
  | .lam p e => by simp only [rsbExp, AExp.erase, rsbAtPat_eraseD s p, rsbExp_eraseD s e]
  | .caseE e m => by simp only [rsbExp, AExp.erase, rsbExp_eraseD s e, rsbMatch_eraseD s m]
theorem rsbExpOpt_eraseD (s : RSub) : ∀ e : Option AExp, AExp.eraseOpt (rsbExpOpt s e) = AExp.eraseOpt e
  | none => rfl
  | some e => by simp only [rsbExpOpt, AExp.eraseOpt, rsbExp_eraseD s e]
theorem rsbMatch_eraseD (s : RSub) : ∀ m : AMatch, (rsbMatch s m).erase = m.erase
  | .mk mr rest => by simp only [rsbMatch, AMatch.erase, rsbMRule_eraseD s mr, rsbMatchOpt_eraseD s rest]
theorem rsbMatchOpt_eraseD (s : RSub) : ∀ m : Option AMatch, AMatch.eraseOpt (rsbMatchOpt s m) = AMatch.eraseOpt m
  | none => rfl
  | some m => by simp only [rsbMatchOpt, AMatch.eraseOpt, rsbMatch_eraseD s m]
theorem rsbMRule_eraseD (s : RSub) : ∀ mr : AMRule, (rsbMRule s mr).erase = mr.erase
  | .mk p e => by simp only [rsbMRule, AMRule.erase, rsbPat_eraseD s p, rsbExp_eraseD s e]
theorem rsbDec_eraseD (s : RSub) : ∀ d : ADec, (rsbDec s d).erase = d.erase
  | .val _ vb => by simp only [rsbDec, ADec.erase, rsbValBind_eraseD s vb]
theorem rsbValBind_eraseD (s : RSub) : ∀ vb : AValBind, (rsbValBind s vb).erase = vb.erase
  | .var _ _ _ e rest => by simp only [rsbValBind, AValBind.erase, rsbExp_eraseD s e, rsbValBindOpt_eraseD s rest]
  | .pat p e => by simp only [rsbValBind, AValBind.erase, rsbAtPat_eraseD s p, rsbExp_eraseD s e]
theorem rsbValBindOpt_eraseD (s : RSub) : ∀ vb : Option AValBind, AValBind.eraseOpt (rsbValBindOpt s vb) = AValBind.eraseOpt vb
  | none => rfl
  | some vb => by simp only [rsbValBindOpt, AValBind.eraseOpt, rsbValBind_eraseD s vb]
end

/-! ## Statuses -/

theorem allV_closGroup {A : List BVar} {VE : ValEnv} (h : AllV VE) : AllV (closGroup A VE) := by
  intro q hq
  rw [closGroup_eq] at hq
  simp only [FMap.mapV, List.mem_map] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  exact h q0 hq0

theorem allV_modify {f g : ValEnv} (hf : AllV f) (hg : AllV g) : AllV (FMap.modify f g) := by
  intro q hq
  rcases mem_modify hq with h | h
  · exact hf q h
  · exact hg q h

theorem allV_valbind : ∀ vb : AValBind, AllV vb.ve
  | .var x ann τ e rest => by
    unfold AValBind.ve
    refine allV_modify (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; rfl) ?_
    cases rest with
    | none => exact fun _ h => nomatch h
    | some vb => exact allV_valbind vb
  | .pat p e => fun q hq => (atpat_ve p q hq).2.1

theorem consOK_plusU {L : LongId → Option Scheme} {C : Ctx} (h : ConsOK L C) (U' : List BVar) :
    ConsOK L (C.plusU U') := h

theorem tyList_stripAtPats : ∀ l : List AAtPat, AAtPat.tyList (stripAtPats l) = AAtPat.tyList l
  | [] => rfl
  | a :: as => by simp only [stripAtPats, AAtPat.tyList, stripAtPat_ty, tyList_stripAtPats as]

/-! ## The constructor witnesses of the derivation -/

section nav
variable {L : LongId → Option Scheme} {T : RSub}

mutual
theorem cwAtPat_nav : ∀ (p p' : AAtPat) (C' : Ctx), ConsOK L C' → stripAtPat (rsbAtPat T p) = stripAtPat p' →
    checkAtPat C' p' = true → CWAtPat L T p
  | .tuple p1 p2 p3, p', C', hC, h, hc => by
    cases p' with
    | tuple q1 q2 q3 =>
      simp only [rsbAtPat, stripAtPat, AAtPat.tuple.injEq] at h
      simp only [checkAtPat, Bool.and_eq_true] at hc
      exact ⟨cwPat_nav p1 q1 C' hC h.1 hc.1.1, cwPat_nav p2 q2 C' hC h.2.1 hc.1.2, cwPatOpt_nav p3 q3 C' hC h.2.2 hc.2⟩
    | _ => simp [rsbAtPat, stripAtPat] at h
  | .paren p, p', C', hC, h, hc => by
    cases p' with
    | paren q =>
      simp only [rsbAtPat, stripAtPat, AAtPat.paren.injEq] at h
      simp only [checkAtPat] at hc
      exact cwPat_nav p q C' hC h hc
    | _ => simp [rsbAtPat, stripAtPat] at h
  | .wild _, _, _, _, _, _ | .scon _ _, _, _, _, _, _ | .var _ _, _, _, _, _, _ | .con _ _ _, _, _, _, _, _
  | .unit, _, _, _, _, _ | .nil _, _, _, _, _, _ | .record _ _, _, _, _, _, _ => by simp [CWAtPat]
theorem cwPat_nav : ∀ (p p' : APat) (C' : Ctx), ConsOK L C' → stripPat (rsbPat T p) = stripPat p' →
    checkPat C' p' = true → CWPat L T p
  | .atpat a, p', C', hC, h, hc => by
    cases p' with
    | atpat b =>
      simp only [rsbPat, stripPat, APat.atpat.injEq] at h
      simp only [checkPat] at hc
      exact cwAtPat_nav a b C' hC h hc
    | _ => simp [rsbPat, stripPat] at h
  | .con lc inst args τ, p', C', hC, h, hc => by
    cases p' with
    | con lc' inst' args' τ' =>
      simp only [rsbPat, stripPat, APat.con.injEq] at h
      obtain ⟨rfl, -, h2, h3⟩ := h
      simp only [checkPat, Bool.and_eq_true] at hc
      obtain ⟨hc1, hc2⟩ := hc
      refine ⟨fun σ hσ => ?_, cwAtPats_nav args args' C' hC h2 hc2⟩
      split at hc1
      · rename_i σ' hl
        simp only [Bool.and_eq_true] at hc1
        have := hC _ _ hl
        rw [hσ] at this; cases this
        refine ⟨inst', ?_⟩
        have e1 : AAtPat.tyList args' = rsbList T (AAtPat.tyList args) := by
          rw [← tyList_stripAtPats args', ← h2, tyList_stripAtPats, rsbAtPats_tyListD]
        have := hc1.1
        rw [e1, ← h3] at this
        exact this
      · cases hc1
    | _ => simp [rsbPat, stripPat] at h
  | .cons p1 p2, p', C', hC, h, hc => by
    cases p' with
    | cons q1 q2 =>
      simp only [rsbPat, stripPat, APat.cons.injEq] at h
      simp only [checkPat, Bool.and_eq_true] at hc
      exact ⟨cwPat_nav p1 q1 C' hC h.1 hc.1.1, cwPat_nav p2 q2 C' hC h.2 hc.1.2⟩
    | _ => simp [rsbPat, stripPat] at h
  | .as p x, p', C', hC, h, hc => by
    cases p' with
    | as q y =>
      simp only [rsbPat, stripPat, APat.as.injEq] at h
      simp only [checkPat] at hc
      exact cwPat_nav p q C' hC h.1 hc
    | _ => simp [rsbPat, stripPat] at h
theorem cwPatOpt_nav : ∀ (p p' : Option APat) (C' : Ctx), ConsOK L C' → stripPatOpt (rsbPatOpt T p) = stripPatOpt p' →
    checkPatOpt C' p' = true → CWPatOpt L T p
  | none, _, _, _, _, _ => trivial
  | some p, some q, C', hC, h, hc => by
    simp only [rsbPatOpt, stripPatOpt, Option.some.injEq] at h
    simp only [checkPatOpt] at hc
    exact cwPat_nav p q C' hC h hc
  | some p, none, _, _, h, _ => by simp [rsbPatOpt, stripPatOpt] at h
theorem cwAtPats_nav : ∀ (l l' : List AAtPat) (C' : Ctx), ConsOK L C' → stripAtPats (rsbAtPats T l) = stripAtPats l' →
    checkAtPatList C' l' = true → CWAtPats L T l
  | [], _, _, _, _, _ => trivial
  | a :: as, b :: bs, C', hC, h, hc => by
    simp only [rsbAtPats, stripAtPats, List.cons.injEq] at h
    simp only [checkAtPatList, Bool.and_eq_true] at hc
    exact ⟨cwAtPat_nav a b C' hC h.1 hc.1, cwAtPats_nav as bs C' hC h.2 hc.2⟩
  | _ :: _, [], _, _, h, _ => by simp [rsbAtPats, stripAtPats] at h
end

theorem allV_atpat (p : AAtPat) : AllV p.ve := fun q hq => (atpat_ve p q hq).2.1

theorem allV_pat (p : APat) : AllV p.ve := fun q hq => (pat_ve p q hq).2.1

mutual
theorem cwAtExp_nav : ∀ (a a' : AAtExp) (C' : Ctx), ConsOK L C' → stripAtExp (rsbAtExp T a) = stripAtExp a' →
    checkAtExp C' a' = true → CWAtExp L T a
  | .tuple e1 e2 e3, a', C', hC, h, hc => by
    cases a' with
    | tuple f1 f2 f3 =>
      simp only [rsbAtExp, stripAtExp, AAtExp.tuple.injEq] at h
      simp only [checkAtExp, Bool.and_eq_true] at hc
      exact ⟨cwExp_nav e1 f1 C' hC h.1 hc.1.1, cwExp_nav e2 f2 C' hC h.2.1 hc.1.2, cwExpOpt_nav e3 f3 C' hC h.2.2 hc.2⟩
    | _ => simp [rsbAtExp, stripAtExp] at h
  | .record r, a', C', hC, h, hc => by
    cases a' with
    | record r' =>
      simp only [rsbAtExp, stripAtExp, AAtExp.record.injEq] at h
      simp only [checkAtExp] at hc
      exact cwExpRowOpt_nav r r' C' hC h hc
    | _ => simp [rsbAtExp, stripAtExp] at h
  | .update x inst τ r, a', C', hC, h, hc => by
    cases a' with
    | update x' inst' τ' r' =>
      simp only [rsbAtExp, stripAtExp, AAtExp.update.injEq] at h
      simp only [checkAtExp, Bool.and_eq_true] at hc
      exact cwExpRow_nav r r' C' hC h.2.2.2 hc.1.2
    | _ => simp [rsbAtExp, stripAtExp] at h
  | .letE d e, a', C', hC, h, hc => by
    cases a' with
    | letE d' e' =>
      simp only [rsbAtExp, stripAtExp, AAtExp.letE.injEq] at h
      simp only [checkAtExp, Bool.and_eq_true] at hc
      refine ⟨cwDec_nav d d' C' hC h.1 hc.1, cwExp_nav e e' _ ?_ h.2 hc.2⟩
      obtain ⟨VE', vb'⟩ := d'
      simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [ADec.result]
      refine consOK_plusVE hC (allV_closGroup ?_)
      rw [← hc.1.2]; exact allV_valbind vb'
    | _ => simp [rsbAtExp, stripAtExp] at h
  | .paren e, a', C', hC, h, hc => by
    cases a' with
    | paren e' =>
      simp only [rsbAtExp, stripAtExp, AAtExp.paren.injEq] at h
      simp only [checkAtExp] at hc
      exact cwExp_nav e e' C' hC h hc
    | _ => simp [rsbAtExp, stripAtExp] at h
  | .scon _ _, _, _, _, _, _ | .var _ _ _, _, _, _, _, _ | .con _ _ _, _, _, _, _, _ | .op _ _ _, _, _, _, _, _
  | .unit, _, _, _, _, _ | .nil _, _, _, _, _, _ => by simp [CWAtExp]
theorem cwExpRow_nav : ∀ (r r' : AExpRow) (C' : Ctx), ConsOK L C' → stripExpRow (rsbExpRow T r) = stripExpRow r' →
    checkExpRow C' r' = true → CWExpRow L T r
  | .field l e rest, .field l' e' rest', C', hC, h, hc => by
    simp only [rsbExpRow, stripExpRow, AExpRow.field.injEq] at h
    simp only [checkExpRow, Bool.and_eq_true] at hc
    exact ⟨cwExp_nav e e' C' hC h.2.1 hc.1, cwExpRowOpt_nav rest rest' C' hC h.2.2 hc.2⟩
theorem cwExpRowOpt_nav : ∀ (r r' : Option AExpRow) (C' : Ctx), ConsOK L C' →
    stripExpRowOpt (rsbExpRowOpt T r) = stripExpRowOpt r' → checkExpRowOpt C' r' = true → CWExpRowOpt L T r
  | none, _, _, _, _, _ => trivial
  | some r, some r', C', hC, h, hc => by
    simp only [rsbExpRowOpt, stripExpRowOpt, Option.some.injEq] at h
    simp only [checkExpRowOpt] at hc
    exact cwExpRow_nav r r' C' hC h hc
  | some r, none, _, _, h, _ => by simp [rsbExpRowOpt, stripExpRowOpt] at h
theorem cwExp_nav : ∀ (e e' : AExp) (C' : Ctx), ConsOK L C' → stripExp (rsbExp T e) = stripExp e' →
    checkExpS C' e' = true → CWExp L T e
  | .atexp a, e', C', hC, h, hc => by
    cases e' with
    | atexp a' =>
      simp only [rsbExp, stripExp, AExp.atexp.injEq] at h
      simp only [checkExpS] at hc
      exact cwAtExp_nav a a' C' hC h hc
    | _ => simp [rsbExp, stripExp] at h
  | .app e a, e', C', hC, h, hc => by
    cases e' with
    | app f a' =>
      simp only [rsbExp, stripExp, AExp.app.injEq] at h
      simp only [checkExpS, Bool.and_eq_true] at hc
      exact ⟨cwExp_nav e f C' hC h.1 hc.1.1, cwAtExp_nav a a' C' hC h.2 hc.1.2⟩
    | _ => simp [rsbExp, stripExp] at h
  | .lam p e, e', C', hC, h, hc => by
    cases e' with
    | lam p' f =>
      simp only [rsbExp, stripExp, AExp.lam.injEq] at h
      simp only [checkExpS, Bool.and_eq_true] at hc
      exact ⟨cwAtPat_nav p p' C' hC h.1 hc.1, cwExp_nav e f _ (consOK_plusVE hC (allV_atpat p')) h.2 hc.2⟩
    | _ => simp [rsbExp, stripExp] at h
  | .caseE e m, e', C', hC, h, hc => by
    cases e' with
    | caseE f m' =>
      simp only [rsbExp, stripExp, AExp.caseE.injEq] at h
      simp only [checkExpS, Bool.and_eq_true] at hc
      exact ⟨cwExp_nav e f C' hC h.1 hc.1.1, cwMatch_nav m m' C' hC h.2 hc.1.2⟩
    | _ => simp [rsbExp, stripExp] at h
theorem cwExpOpt_nav : ∀ (e e' : Option AExp) (C' : Ctx), ConsOK L C' → stripExpOpt (rsbExpOpt T e) = stripExpOpt e' →
    checkExpOpt C' e' = true → CWExpOpt L T e
  | none, _, _, _, _, _ => trivial
  | some e, some f, C', hC, h, hc => by
    simp only [rsbExpOpt, stripExpOpt, Option.some.injEq] at h
    simp only [checkExpOpt] at hc
    exact cwExp_nav e f C' hC h hc
  | some e, none, _, _, h, _ => by simp [rsbExpOpt, stripExpOpt] at h
theorem cwMatch_nav : ∀ (m m' : AMatch) (C' : Ctx), ConsOK L C' → stripMatch (rsbMatch T m) = stripMatch m' →
    checkMatch C' m' = true → CWMatch L T m
  | .mk mr rest, .mk mr' rest', C', hC, h, hc => by
    simp only [rsbMatch, stripMatch, AMatch.mk.injEq] at h
    simp only [checkMatch, Bool.and_eq_true] at hc
    refine ⟨cwMRule_nav mr mr' C' hC h.1 hc.1, ?_⟩
    cases rest with
    | none => trivial
    | some m =>
      cases rest' with
      | none => simp [rsbMatchOpt, stripMatchOpt] at h
      | some m' =>
        simp only [rsbMatchOpt, stripMatchOpt, Option.some.injEq] at h
        simp only [checkMatchOptAt, Bool.and_eq_true] at hc
        exact cwMatch_nav m m' C' hC h.2 hc.2.1
theorem cwMRule_nav : ∀ (mr mr' : AMRule) (C' : Ctx), ConsOK L C' → stripMRule (rsbMRule T mr) = stripMRule mr' →
    checkMRule C' mr' = true → CWMRule L T mr
  | .mk p e, .mk p' e', C', hC, h, hc => by
    simp only [rsbMRule, stripMRule, AMRule.mk.injEq] at h
    simp only [checkMRule, Bool.and_eq_true] at hc
    exact ⟨cwPat_nav p p' C' hC h.1 hc.1, cwExp_nav e e' _ (consOK_plusVE hC (allV_pat p')) h.2 hc.2⟩
theorem cwDec_nav : ∀ (d d' : ADec) (C' : Ctx), ConsOK L C' → stripDec (rsbDec T d) = stripDec d' →
    checkDec C' d' = true → CWDec L T d
  | .val VE vb, .val VE' vb', C', hC, h, hc => by
    simp only [rsbDec, stripDec, ADec.val.injEq] at h
    simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
    refine cwValBind_nav vb vb' _ (consOK_plusVE hC ?_) h.2 hc.1
    rw [← hc.2]; exact allV_valbind vb'
theorem cwValBind_nav : ∀ (vb vb' : AValBind) (C' : Ctx), ConsOK L C' → stripValBind (rsbValBind T vb) = stripValBind vb' →
    checkValBind C' vb' = true → CWValBind L T vb
  | .var x ann τ e rest, vb', C', hC, h, hc => by
    cases vb' with
    | var x' ann' τ' e' rest' =>
      simp only [rsbValBind, stripValBind, AValBind.var.injEq] at h
      simp only [checkValBind, Bool.and_eq_true] at hc
      exact ⟨cwExp_nav e e' _ (consOK_plusU hC _) h.2.2.2.1 hc.1.1.2, cwValBindOpt_nav rest rest' C' hC h.2.2.2.2 hc.2⟩
    | _ => simp [rsbValBind, stripValBind] at h
  | .pat p e, vb', C', hC, h, hc => by
    cases vb' with
    | pat p' e' =>
      simp only [rsbValBind, stripValBind, AValBind.pat.injEq] at h
      simp only [checkValBind, Bool.and_eq_true] at hc
      exact ⟨cwAtPat_nav p p' C' hC h.1 hc.1.1, cwExp_nav e e' C' hC h.2 hc.1.2⟩
    | _ => simp [rsbValBind, stripValBind] at h
theorem cwValBindOpt_nav : ∀ (vb vb' : Option AValBind) (C' : Ctx), ConsOK L C' →
    stripValBindOpt (rsbValBindOpt T vb) = stripValBindOpt vb' → checkValBindOpt C' vb' = true → CWValBindOpt L T vb
  | none, _, _, _, _, _ => trivial
  | some vb, some vb', C', hC, h, hc => by
    simp only [rsbValBindOpt, stripValBindOpt, Option.some.injEq] at h
    simp only [checkValBindOpt] at hc
    exact cwValBind_nav vb vb' C' hC h hc
  | some vb, none, _, _, h, _ => by simp [rsbValBindOpt, stripValBindOpt] at h
end

end nav

/-! ## The root -/

/-- The constructor lookups of the root context. -/
def rootL (C0 : Ctx) (lv : LongId) : Option Scheme :=
  match C0.lookupVal lv with
  | some (σ, .c) => some σ
  | _ => none

theorem rootL_consOK (C0 : Ctx) : ConsOK (rootL C0) C0 := fun lv σ h => by simp [rootL, h]

theorem rootL_ok {C0 : Ctx} (hC : RootOKD C0) : LOk (freshAboveD C0) (rootL C0) := by
  intro lv σ h
  simp only [rootL] at h
  split at h
  · rename_i σ' hl; cases h; exact root_ctxWD hC lv _ _ hl
  · cases h

theorem nbθ_nil : NBθ [] := fun v hv w hw => by
  have : (toRS ([] : RBnd)).img v = vty v := by rw [img_toRS (fun _ h => by cases h)]; rfl
  rw [this, vars_vty, List.mem_singleton] at hw; subst hw; exact hv

theorem root_spreD {C0 : Ctx} (hC : RootOKD C0) : SPre (freshAboveD C0) (rootL C0) C0 ⟨[], freshAboveD C0⟩ :=
  ⟨⟨(root_preD C0 hC).inv, nbθ_nil⟩, root_ctxWD hC,
    fun v hv => rigid_of_oldD (old_of_rootD (mem_ctx_tyvars.mpr (.inl hv))), rootL_consOK C0⟩

/-- A type whose image, under a substitution fixing the `bnd` variables, is `Ty.okB` is `Ty.okB`. -/
theorem okB_of_rsb {n0 : Nat} {T : RSub} (hT : FixR (rigidFromD n0) T) {τ : Ty}
    (h : Ty.okB (rsb T τ) = true) : Ty.okB τ = true := by
  rw [Ty.okB_iff] at h ⊢
  refine ⟨cnB_of_rsb h.1, fun v hv => ?_⟩
  cases hb : v.isBnd with
  | false => rfl
  | true =>
    exfalso
    have hfix : T.img v = vty v := hT v (by
      rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isBnd, rigidFromD])
    have := h.2 v ((mem_vars_rsb T τ v).mpr ⟨v, hv, by rw [hfix, vars_vty]; exact List.mem_singleton_self _⟩)
    rw [hb] at this; cases this

end WDS

open WDS in
/-- L10 for W with records and rows: on a successful run from a `RootOKD` context, when a canonical
    derivation without free `bnd` variables exists, step 9's checker accepts W's final result,
    which erases to the phrase. -/
theorem wdResultChecks {fuel : Nat} {C0 : Ctx} {e : BExp} {τ : Ty} {ar : AExp} {st : WDSt} (hC : RootOKD C0)
    (h : wdExp fuel (rigidFromD (freshAboveD C0)) C0 e ⟨[], freshAboveD C0⟩ = .ok (τ, ar) st)
    (hd : ∃ a', checkExp C0 a' = true ∧ a'.erase = e) :
    checkExp C0 (rsbExp (toRS st.θ) ar) = true ∧ (rsbExp (toRS st.θ) ar).erase = e := by
  obtain ⟨a', hc, he⟩ := hd
  have hp := root_spreD hC
  obtain ⟨K, P⟩ := wdExp_sound fuel _ (rootL_ok hC) e C0 _ (τ, ar) st hp h
  have hi := P.seg.inv
  have hw := wdExp_root (fuel := fuel) hC hc he
  rw [h] at hw
  obtain ⟨-, -, -, -, T, hF, -, hs⟩ := hw
  have hcnT : CnL T (tysExp false ar) := by
    intro σ hσ
    have : rsb T σ ∈ tysExp false a' := by
      rw [← tysExp_strip, ← hs, tysExp_strip, tysExp_sbD false T (fix_bnd0D hF.fix)]
      exact List.mem_map_of_mem hσ
    exact (nbd_of_derivation (noFreeBndExp_of_checkExp hc) (canonExp_of_checkExp hc) _ this).2
  have hchk := P.chk (th st) hi.sok (absS_self hi.idem) P.ks.dead T ⟨hF.fix, hF.resp respR_rid, hF.abs⟩ hcnT
    (cwExp_nav ar a' C0 (rootL_consOK C0) hs (checkExpS_of_checkExp hc))
  refine ⟨?_, ?_⟩
  · have hS := hchk.1
    rw [ctxRsb_rootD hi.sok.fix] at hS
    refine checkExp_iff.mpr ⟨hS, okNodesExp C0 [] _ fun τ hτ => ?_⟩
    -- the types W records are `Ty.okB`: their images by `T` are the derivation's
    rw [tysExp_sbD false _ (fix_bnd0D hi.sok.fix)] at hτ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
    refine okB_of_rsb hF.fix ?_
    rw [absR_rsb hF.abs]
    have : rsb T σ ∈ tysExp false a' := by
      rw [← tysExp_strip, ← hs, tysExp_strip, tysExp_sbD false T (fix_bnd0D hF.fix)]
      exact List.mem_map_of_mem hσ
    have h2 := tysExp_nodes C0 [] a' _ this
    simp only [NTys, List.mem_flatMap] at h2
    obtain ⟨n, hn, hτn⟩ := h2
    exact okB_of_checkExp hc n hn _ hτn
  · have := congrArg AExp.erase hs
    rw [stripExp_erase, stripExp_erase, rsbExp_eraseD] at this
    rw [rsbExp_eraseD, this, he]

/-- Completeness for F_d (section 7): when a canonical derivation without free `bnd` variables
    exists, `inferExpWD` neither fails nor returns `internal` for any fuel, and for some fuel it
    does not run out. -/
theorem wdCompleteness : WDCompleteness := wdCompleteness_of_ne_internal fun fuel C0 e hC hd => by
  intro hi
  unfold inferExpWD at hi
  simp only at hi
  split at hi
  · rename_i τ ar st hok
    obtain ⟨hc, he⟩ := wdResultChecks hC hok hd
    split at hi
    · simp [hc, he] at hi
    · cases hi
  · cases hi
  · cases hi
  · cases hi

end StandardElm.Stat.Complete
