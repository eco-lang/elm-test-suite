/-
  A Standard Definition of Elm? Mechanisation, part 6.
  Soundness of the evaluator of Eval.lean with respect to the relations of
  Rules.lean: for every fuel n and every choice ch, a result of an evaluator
  function is a result of the corresponding judgement. Proved by induction on
  the fuel, simultaneously for the seventeen evaluator functions.
-/
import StandardElmMech.Eval
namespace StandardElm

theorem pick_mem {ch : Bool} {l : List Val} {v : Val} : pick ch l = some v → v ∈ l := by
  unfold pick; split
  · intro h; exact List.mem_of_getLast? h
  · intro h; exact List.mem_of_head? h

theorem sconTest_true {v : Val} {sc : SCon} : sconTest v sc = some true → v = valof sc := by
  unfold sconTest; split <;> simp_all [valof]

theorem sconTest_false {v : Val} {sc : SCon} : sconTest v sc = some false → v ≠ valof sc := by
  unfold sconTest; split <;> simp_all [valof] <;> (intro h; cases h) <;> simp_all

theorem conIs_true {v : Val} {c : Con} : conIs v c = true → v = .con c [] := by
  unfold conIs; split <;> simp_all

theorem conIs_false {v : Val} {c : Con} : conIs v c = false → v ≠ .con c [] := by
  unfold conIs; split <;> simp_all

theorem conArgs_some {v : Val} {c : Con} {n : Nat} {vs : List Val} :
    conArgs v c n = some vs → v = .con c vs := by
  unfold conArgs; split
  · split <;> simp_all
  · simp

theorem conArgs_none {v : Val} {c : Con} {n : Nat} :
    conArgs v c n = none → ¬ ∃ vs, v = .con c vs ∧ vs.length = n := by
  unfold conArgs; split
  · split <;> simp_all
  · rename_i hn; intro _ ⟨vs, h, _⟩; exact hn c vs h

theorem pick_apply {ch : Bool} {b : BasVal} {vs : List Val} {v : Val} :
    pick ch (applySet b vs) = some v → Apply b vs v := fun h => applySet_sound (pick_mem h)


/-- r:d-atpat-tuple with its first premise v = (v1, v2 [, v3]) discharged. -/
theorem atpat_tuple' {E : Env} {v1 v2 : Val} {v3 : Option Val} {p1 p2 : Pat} {p3 : Option Pat}
    {r1 r2 r3 : VEF} : MatchPat E v1 p1 r1 → MatchPat E v2 p2 r2 → MatchPatOpt E v3 p3 r3 →
    MatchAtPat E (.tuple v1 v2 v3) (.tuple p1 p2 p3) ((r1.plus r2).plus r3) :=
  MatchAtPat.r_d_atpat_tuple _ _ _ _ _ _ _ _ _ _ _ rfl

set_option hygiene false in
/-- Split the evaluator's matches in `h`, then close the goal from the
    rule constructors, the induction hypotheses and the helper lemmas. -/
macro "sound_fin" : tactic => `(tactic| (
  (repeat' (first | (split at h) | (split at *)))
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Bool.not_eq_true] at *)
  all_goals (try subst_vars)
  all_goals (solve_by_elim (maxDepth := 8) [
    EvalAtExp.r_d_atexp_scon, EvalAtExp.r_d_atexp_var, EvalAtExp.r_d_atexp_con,
    EvalAtExp.r_d_atexp_op, EvalAtExp.r_d_atexp_unit, EvalAtExp.r_d_atexp_tuple,
    EvalAtExp.r_d_atexp_nil, EvalAtExp.r_d_atexp_record, EvalAtExp.r_d_atexp_update,
    EvalAtExp.r_d_atexp_paren, EvalAtExp.r_d_atexp_let,
    EvalExpRow.r_d_exprow_field,
    EvalExp.r_d_exp_atexp, EvalExp.r_d_exp_app, EvalExp.r_d_exp_lambda, EvalExp.r_d_exp_case,
    AppVal.r_d_app_closure, AppVal.r_d_app_con, AppVal.r_d_app_basic_partial,
    AppVal.r_d_app_basic_apply,
    EvalMatch.r_d_match_first, EvalMatch.r_d_match_fail, EvalMatch.r_d_match_next,
    EvalMRule.r_d_mrule_match, EvalMRule.r_d_mrule_fail,
    EvalDec.r_d_dec_nonrec, EvalDec.r_d_dec_rec,
    EvalValBind.r_d_valbind_var, EvalValBind.r_d_valbind_pat,
    MatchAtPat.r_d_atpat_wild, MatchAtPat.r_d_atpat_scon, MatchAtPat.r_d_atpat_scon_fail,
    MatchAtPat.r_d_atpat_var, MatchAtPat.r_d_atpat_con, MatchAtPat.r_d_atpat_con_fail,
    MatchAtPat.r_d_atpat_unit, MatchAtPat.r_d_atpat_tuple, MatchAtPat.r_d_atpat_nil,
    MatchAtPat.r_d_atpat_nil_fail, MatchAtPat.r_d_atpat_record, MatchAtPat.r_d_atpat_paren,
    MatchPatRow.r_d_patrow_field,
    MatchPat.r_d_pat_atpat, MatchPat.r_d_pat_con, MatchPat.r_d_pat_con_fail,
    MatchPat.r_d_pat_cons, MatchPat.r_d_pat_cons_fail, MatchPat.r_d_pat_as,
    EvalExpOpt.opt_none, EvalExpOpt.opt_some, EvalExpRowOpt.opt_none, EvalExpRowOpt.opt_some,
    EvalValBindOpt.opt_none, EvalValBindOpt.opt_some, MatchPatOpt.opt_none, MatchPatOpt.opt_some,
    MatchPatRowOpt.opt_none, MatchPatRowOpt.opt_some, MatchAtPats.seq_nil, MatchAtPats.seq_cons,
    atpat_tuple', pick_apply, sconTest_true, sconTest_false, conIs_true, conIs_false, conArgs_some, conArgs_none,
    i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17])))

/-- The soundness statement at fuel n, one conjunct per evaluator function. -/
def SoundAt (ch : Bool) (n : Nat) : Prop :=
  (∀ E a v, evAtExp ch n E a = some v → EvalAtExp E a v) ∧
  (∀ E o r, evExpOpt ch n E o = some r → EvalExpOpt E o r) ∧
  (∀ E row r, evExpRow ch n E row = some r → EvalExpRow E row r) ∧
  (∀ E o r, evExpRowOpt ch n E o = some r → EvalExpRowOpt E o r) ∧
  (∀ E e v, evExp ch n E e = some v → EvalExp E e v) ∧
  (∀ f v r, appVal ch n f v = some r → AppVal f v r) ∧
  (∀ E v m r, evMatch ch n E v m = some r → EvalMatch E v m r) ∧
  (∀ E v mr r, evMRule ch n E v mr = some r → EvalMRule E v mr r) ∧
  (∀ E d VE, evDec ch n E d = some VE → EvalDec E d VE) ∧
  (∀ E vb VE, evValBind ch n E vb = some VE → EvalValBind E vb VE) ∧
  (∀ E o VE, evValBindOpt ch n E o = some VE → EvalValBindOpt E o VE) ∧
  (∀ E v a r, matchAtPat ch n E v a = some r → MatchAtPat E v a r) ∧
  (∀ E v p r, matchPatOpt ch n E v p = some r → MatchPatOpt E v p r) ∧
  (∀ E rc row VE, matchPatRow ch n E rc row = some VE → MatchPatRow E rc row VE) ∧
  (∀ E rc o VE, matchPatRowOpt ch n E rc o = some VE → MatchPatRowOpt E rc o VE) ∧
  (∀ E v p r, matchPat ch n E v p = some r → MatchPat E v p r) ∧
  (∀ E vs as r, matchAtPats ch n E vs as = some r → MatchAtPats E vs as r)

theorem soundAt (ch : Bool) : ∀ n, SoundAt ch n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> simp_all [evAtExp, evExpOpt, evExpRow, evExpRowOpt, evExp, appVal, evMatch,
        evMRule, evDec, evValBind, evValBindOpt, matchAtPat, matchPatOpt, matchPatRow,
        matchPatRowOpt, matchPat, matchAtPats]
  | succ n ih =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro E a v h; cases a <;> simp only [evAtExp] at h <;> sound_fin
    · intro E o r h; cases o <;> simp only [evExpOpt] at h <;> sound_fin
    · intro E row r h; cases row <;> simp only [evExpRow] at h <;> sound_fin
    · intro E o r h; cases o <;> simp only [evExpRowOpt] at h <;> sound_fin
    · intro E e v h; cases e <;> simp only [evExp] at h <;> sound_fin
    · intro f v r h; cases f <;> simp only [appVal] at h <;> sound_fin
    · intro E v m r h; cases m <;> simp only [evMatch] at h <;> sound_fin
    · intro E v mr r h; cases mr <;> simp only [evMRule] at h <;> sound_fin
    · intro E d VE h; cases d <;> simp only [evDec] at h <;> sound_fin
    · intro E vb VE h; cases vb <;> simp only [evValBind] at h <;> sound_fin
    · intro E o VE h; cases o <;> simp only [evValBindOpt] at h <;> sound_fin
    · intro E v a r h; cases a <;> simp only [matchAtPat] at h <;> sound_fin
    · intro E v p r h; cases v <;> cases p <;> simp only [matchPatOpt] at h <;> sound_fin
    · intro E rc row VE h; cases row <;> simp only [matchPatRow] at h <;> sound_fin
    · intro E rc o VE h; cases o <;> simp only [matchPatRowOpt] at h <;> sound_fin
    · intro E v p r h; cases p <;> simp only [matchPat] at h <;> sound_fin
    · intro E vs as r h; cases vs <;> cases as <;> simp only [matchAtPats] at h <;> sound_fin

/-- Main theorem: the evaluator's results are derivable in the definition. -/
theorem evExp_sound {ch : Bool} {n : Nat} {E : Env} {e : Exp} {v : Val} :
    evExp ch n E e = some v → EvalExp E e v :=
  (soundAt ch n).2.2.2.2.1 E e v

theorem evDec_sound {ch : Bool} {n : Nat} {E : Env} {d : Dec} {VE : ValEnv} :
    evDec ch n E d = some VE → EvalDec E d VE :=
  (soundAt ch n).2.2.2.2.2.2.2.2.1 E d VE

end StandardElm
