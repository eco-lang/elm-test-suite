/-
  A Standard Definition of Elm? Mechanisation, part 6.
  Soundness of the evaluator of Eval.lean: for every fuel n, oracle o and index k, a value of an
  evaluator function, with its log, is derivable in the corresponding logged relation of
  RulesL.lean; by `forget` (Forget.lean) the value is derivable in the book's relation of
  Rules.lean. Proved by induction on the fuel, simultaneously for the seventeen evaluator functions.
-/
import StandardElmMech.Eval
import StandardElmMech.Forget
namespace StandardElm

theorem sconTest_true {v : Val} {sc : SCon} : sconTest v sc = true → v = valof sc := by
  unfold sconTest; split <;> simp_all

theorem sconTest_false {v : Val} {sc : SCon} : sconTest v sc = false → v ≠ valof sc := by
  intro h heq; rw [heq] at h; cases sc <;> simp [sconTest, valof] at h

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

theorem applySet_single {b : BasVal} {vs : List Val} {w : Val} :
    applySet b vs = [w] → Apply b vs w := by
  intro h; apply applySet_sound; rw [h]; simp

theorem applySet_first {b : BasVal} {vs ws : List Val} {w w' : Val} :
    applySet b vs = w :: w' :: ws → Apply b vs w := by
  intro h; apply applySet_sound; rw [h]; simp

theorem applySet_second {b : BasVal} {vs ws : List Val} {w w' : Val} :
    applySet b vs = w :: w' :: ws → Apply b vs w' := by
  intro h; apply applySet_sound; rw [h]; simp

/-- r:d-atpat-tuple with its first premise v = (v1, v2 [, v3]) discharged. -/
theorem atpat_tuple_l' {E : Env} {v1 v2 : Val} {v3 : Option Val} {p1 p2 : Pat} {p3 : Option Pat}
    {r1 r2 r3 : VEF} {l1 l2 l3 : Log} : MatchPatL E v1 p1 r1 l1 → MatchPatL E v2 p2 r2 l2 →
    MatchPatOptL E v3 p3 r3 l3 →
    MatchAtPatL E (.tuple v1 v2 v3) (.tuple p1 p2 p3) ((r1.plus r2).plus r3) (l1 ++ l2 ++ l3) :=
  MatchAtPatL.r_d_atpat_tuple_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl

/-- r:d-app-basic-apply at a member chosen by the oracle. -/
theorem app_basic_choice_l {b : BasVal} {vs ws : List Val} {v w w' : Val} (c : Bool) :
    vs.length + 1 = b.arity → applySet b (vs ++ [v]) = w :: w' :: ws →
    AppValL (.basApp b vs) v (if c then w' else w) (logEntry b (vs ++ [v])) := by
  intro h1 h2
  cases c
  · exact AppValL.r_d_app_basic_apply_l _ _ _ _ h1 (applySet_first h2)
  · exact AppValL.r_d_app_basic_apply_l _ _ _ _ h1 (applySet_second h2)

set_option hygiene false in
/-- Split the evaluator's matches in `h`, then close the goal from the logged rule constructors,
    the induction hypotheses and the helper lemmas. -/
macro "sound_fin" : tactic => `(tactic| (
  (repeat' (first | (split at h) | (split at *)))
  all_goals (try simp only [Res.mk.injEq, Outcome.value.injEq, reduceCtorEq, Bool.not_eq_true,
    and_true, true_and] at *)
  all_goals (try obtain ⟨⟨⟩, ⟨⟩, ⟨⟩⟩ := h)
  all_goals (try subst_vars)
  all_goals (solve_by_elim (maxDepth := 8) [
    EvalAtExpL.r_d_atexp_scon_l, EvalAtExpL.r_d_atexp_var_l, EvalAtExpL.r_d_atexp_con_l,
    EvalAtExpL.r_d_atexp_op_l, EvalAtExpL.r_d_atexp_unit_l, EvalAtExpL.r_d_atexp_tuple_l,
    EvalAtExpL.r_d_atexp_nil_l, EvalAtExpL.r_d_atexp_record_l, EvalAtExpL.r_d_atexp_update_l,
    EvalAtExpL.r_d_atexp_paren_l, EvalAtExpL.r_d_atexp_let_l,
    EvalExpRowL.r_d_exprow_field_l,
    EvalExpL.r_d_exp_atexp_l, EvalExpL.r_d_exp_app_l, EvalExpL.r_d_exp_lambda_l, EvalExpL.r_d_exp_case_l,
    AppValL.r_d_app_closure_l, AppValL.r_d_app_con_l, AppValL.r_d_app_basic_partial_l,
    AppValL.r_d_app_basic_apply_l,
    EvalMatchL.r_d_match_first_l, EvalMatchL.r_d_match_fail_l, EvalMatchL.r_d_match_next_l,
    EvalMRuleL.r_d_mrule_match_l, EvalMRuleL.r_d_mrule_fail_l,
    EvalDecL.r_d_dec_nonrec_l, EvalDecL.r_d_dec_rec_l,
    EvalValBindL.r_d_valbind_var_l, EvalValBindL.r_d_valbind_pat_l,
    MatchAtPatL.r_d_atpat_wild_l, MatchAtPatL.r_d_atpat_scon_l, MatchAtPatL.r_d_atpat_scon_fail_l,
    MatchAtPatL.r_d_atpat_var_l, MatchAtPatL.r_d_atpat_con_l, MatchAtPatL.r_d_atpat_con_fail_l,
    MatchAtPatL.r_d_atpat_unit_l, MatchAtPatL.r_d_atpat_tuple_l, MatchAtPatL.r_d_atpat_nil_l,
    MatchAtPatL.r_d_atpat_nil_fail_l, MatchAtPatL.r_d_atpat_record_l, MatchAtPatL.r_d_atpat_paren_l,
    MatchPatRowL.r_d_patrow_field_l,
    MatchPatL.r_d_pat_atpat_l, MatchPatL.r_d_pat_con_l, MatchPatL.r_d_pat_con_fail_l,
    MatchPatL.r_d_pat_cons_l, MatchPatL.r_d_pat_cons_fail_l, MatchPatL.r_d_pat_as_l,
    EvalExpOptL.opt_none_l, EvalExpOptL.opt_some_l, EvalExpRowOptL.opt_none_l,
    EvalExpRowOptL.opt_some_l, EvalValBindOptL.opt_none_l, EvalValBindOptL.opt_some_l,
    MatchPatOptL.opt_none_l, MatchPatOptL.opt_some_l, MatchPatRowOptL.opt_none_l,
    MatchPatRowOptL.opt_some_l, MatchAtPatsL.seq_nil_l, MatchAtPatsL.seq_cons_l,
    atpat_tuple_l', app_basic_choice_l, applySet_single, applySet_first, applySet_second,
    sconTest_true, sconTest_false, conIs_true, conIs_false, conArgs_some, conArgs_none,
    i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17])))

/-- The soundness statement at fuel n, one conjunct per evaluator function. -/
def SoundAt (o : Oracle) (n : Nat) : Prop :=
  (∀ E a k v l k', evAtExp o n E a k = ⟨.value v, l, k'⟩ → EvalAtExpL E a v l) ∧
  (∀ E x k r l k', evExpOpt o n E x k = ⟨.value r, l, k'⟩ → EvalExpOptL E x r l) ∧
  (∀ E row k r l k', evExpRow o n E row k = ⟨.value r, l, k'⟩ → EvalExpRowL E row r l) ∧
  (∀ E x k r l k', evExpRowOpt o n E x k = ⟨.value r, l, k'⟩ → EvalExpRowOptL E x r l) ∧
  (∀ E e k v l k', evExp o n E e k = ⟨.value v, l, k'⟩ → EvalExpL E e v l) ∧
  (∀ f v k r l k', appVal o n f v k = ⟨.value r, l, k'⟩ → AppValL f v r l) ∧
  (∀ E v m k r l k', evMatch o n E v m k = ⟨.value r, l, k'⟩ → EvalMatchL E v m r l) ∧
  (∀ E v mr k r l k', evMRule o n E v mr k = ⟨.value r, l, k'⟩ → EvalMRuleL E v mr r l) ∧
  (∀ E d k VE l k', evDec o n E d k = ⟨.value VE, l, k'⟩ → EvalDecL E d VE l) ∧
  (∀ E vb k VE l k', evValBind o n E vb k = ⟨.value VE, l, k'⟩ → EvalValBindL E vb VE l) ∧
  (∀ E x k VE l k', evValBindOpt o n E x k = ⟨.value VE, l, k'⟩ → EvalValBindOptL E x VE l) ∧
  (∀ E v a k r l k', matchAtPat o n E v a k = ⟨.value r, l, k'⟩ → MatchAtPatL E v a r l) ∧
  (∀ E v p k r l k', matchPatOpt o n E v p k = ⟨.value r, l, k'⟩ → MatchPatOptL E v p r l) ∧
  (∀ E rc row k VE l k', matchPatRow o n E rc row k = ⟨.value VE, l, k'⟩ → MatchPatRowL E rc row VE l) ∧
  (∀ E rc x k VE l k', matchPatRowOpt o n E rc x k = ⟨.value VE, l, k'⟩ → MatchPatRowOptL E rc x VE l) ∧
  (∀ E v p k r l k', matchPat o n E v p k = ⟨.value r, l, k'⟩ → MatchPatL E v p r l) ∧
  (∀ E vs as k r l k', matchAtPats o n E vs as k = ⟨.value r, l, k'⟩ → MatchAtPatsL E vs as r l)

theorem soundAt (o : Oracle) : ∀ n, SoundAt o n := by
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
    · intro E a k v l k' h; cases a <;> simp only [evAtExp] at h <;> sound_fin
    · intro E x k r l k' h; cases x <;> simp only [evExpOpt] at h <;> sound_fin
    · intro E row k r l k' h; cases row <;> simp only [evExpRow] at h <;> sound_fin
    · intro E x k r l k' h; cases x <;> simp only [evExpRowOpt] at h <;> sound_fin
    · intro E e k v l k' h; cases e <;> simp only [evExp] at h <;> sound_fin
    · intro f v k r l k' h; cases f <;> simp only [appVal] at h <;> sound_fin
    · intro E v m k r l k' h; cases m <;> simp only [evMatch] at h <;> sound_fin
    · intro E v mr k r l k' h; cases mr <;> simp only [evMRule] at h <;> sound_fin
    · intro E d k VE l k' h; cases d <;> simp only [evDec] at h <;> sound_fin
    · intro E vb k VE l k' h; cases vb <;> simp only [evValBind] at h <;> sound_fin
    · intro E x k VE l k' h; cases x <;> simp only [evValBindOpt] at h <;> sound_fin
    · intro E v a k r l k' h; cases a <;> simp only [matchAtPat] at h <;> sound_fin
    · intro E v p k r l k' h; cases v <;> cases p <;> simp only [matchPatOpt] at h <;> sound_fin
    · intro E rc row k VE l k' h; cases row <;> simp only [matchPatRow] at h <;> sound_fin
    · intro E rc x k VE l k' h; cases x <;> simp only [matchPatRowOpt] at h <;> sound_fin
    · intro E v p k r l k' h; cases p <;> simp only [matchPat] at h <;> sound_fin
    · intro E vs as k r l k' h; cases vs <;> cases as <;> simp only [matchAtPats] at h <;> sound_fin

/-- Soundness for the logged relation: a value of the evaluator, with its log, is derivable. -/
theorem evExp_sound_l {o : Oracle} {n : Nat} {E : Env} {e : Exp} {k : Nat} {v : Val} {l : Log} {k' : Nat} :
    evExp o n E e k = ⟨.value v, l, k'⟩ → EvalExpL E e v l :=
  (soundAt o n).2.2.2.2.1 E e k v l k'

theorem evDec_sound_l {o : Oracle} {n : Nat} {E : Env} {d : Dec} {k : Nat} {VE : ValEnv} {l : Log} {k' : Nat} :
    evDec o n E d k = ⟨.value VE, l, k'⟩ → EvalDecL E d VE l :=
  (soundAt o n).2.2.2.2.2.2.2.2.1 E d k VE l k'

theorem appVal_sound_l {o : Oracle} {n : Nat} {f v : Val} {k : Nat} {r : Val} {l : Log} {k' : Nat} :
    appVal o n f v k = ⟨.value r, l, k'⟩ → AppValL f v r l :=
  (soundAt o n).2.2.2.2.2.1 f v k r l k'

theorem evValBind_sound_l {o : Oracle} {n : Nat} {E : Env} {vb : ValBind} {k : Nat} {VE : ValEnv} {l : Log} {k' : Nat} :
    evValBind o n E vb k = ⟨.value VE, l, k'⟩ → EvalValBindL E vb VE l :=
  (soundAt o n).2.2.2.2.2.2.2.2.2.1 E vb k VE l k'

/-- Main theorem: the evaluator's values are derivable in the definition. -/
theorem evExp_sound {o : Oracle} {n : Nat} {E : Env} {e : Exp} {k : Nat} {v : Val} :
    (evExp o n E e k).out = .value v → EvalExp E e v := by
  intro h
  rcases hr : evExp o n E e k with ⟨out, l, k'⟩
  rw [hr] at h; simp only at h; subst h
  exact EvalExpL.forget (evExp_sound_l hr)

theorem evDec_sound {o : Oracle} {n : Nat} {E : Env} {d : Dec} {k : Nat} {VE : ValEnv} :
    (evDec o n E d k).out = .value VE → EvalDec E d VE := by
  intro h
  rcases hr : evDec o n E d k with ⟨out, l, k'⟩
  rw [hr] at h; simp only at h; subst h
  exact EvalDecL.forget (evDec_sound_l hr)

end StandardElm
