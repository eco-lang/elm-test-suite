/-
  A Standard Definition of Elm? Mechanisation: statements about every derivation (plan decision D1),
  from `nostuck` (NoStuck.lean).

  * A phrase on which the evaluator is stuck without reading a choice has no value: no derivation of
    the book gives it one (`noValue_of_stuck`). This is how the mechanisation states that a program
    has no meaning (A25, A62), and a `CHECK-NOT` about a single evaluation.
  * A value the evaluator gives without reading a choice is the only value, and its log the only log
    (`evExp_unique`, `evExp_unique_l`).
  * Completeness: every derivation of the book is found by the evaluator with some list of choices
    and fuel (`evExp_complete`), so a phrase has no value exactly when no choices and fuel give it
    one (`noValue_iff`).
-/
import StandardElmMech.NoStuck
import StandardElmMech.Completeness

namespace StandardElm

theorem evExp_unique_l {o : Oracle} {n : Nat} {E : Env} {e : Exp} {k : Nat} {v : Val} {l : Log}
    (h : evExp o n E e k = ⟨.value v, l, k⟩) : ∀ v' l', EvalExpL E e v' l' → v' = v ∧ l' = l := by
  intro v' l' d
  rcases EvalExpL.nostuck d o n k _ h with h1 | h1 | h1
  · simp at h1
  · simp at h1
  · simp only [Res.mk.injEq, Outcome.value.injEq] at h1; exact ⟨h1.1.symm, h1.2.1.symm⟩

theorem evExp_unique {o : Oracle} {n : Nat} {E : Env} {e : Exp} {k : Nat} {v : Val} {l : Log}
    (h : evExp o n E e k = ⟨.value v, l, k⟩) : ∀ v', EvalExp E e v' → v' = v := by
  intro v' d
  obtain ⟨l', d'⟩ := EvalExp.lift d
  exact (evExp_unique_l h v' l' d').1

theorem noValue_of_stuck {o : Oracle} {n : Nat} {E : Env} {e : Exp} {k : Nat} {l : Log}
    (h : evExp o n E e k = ⟨.stuck, l, k⟩) : ¬ ∃ v, EvalExp E e v := by
  rintro ⟨v, d⟩
  obtain ⟨l', d'⟩ := EvalExp.lift d
  rcases EvalExpL.nostuck d' o n k _ h with h1 | h1 | h1 <;> simp at h1

theorem appVal_unique_l {o : Oracle} {n : Nat} {f v : Val} {k : Nat} {w : Val} {l : Log}
    (h : appVal o n f v k = ⟨.value w, l, k⟩) : ∀ w' l', AppValL f v w' l' → w' = w ∧ l' = l := by
  intro w' l' d
  rcases AppValL.nostuck d o n k _ h with h1 | h1 | h1
  · simp at h1
  · simp at h1
  · simp only [Res.mk.injEq, Outcome.value.injEq] at h1; exact ⟨h1.1.symm, h1.2.1.symm⟩

theorem appVal_noValue_of_stuck {o : Oracle} {n : Nat} {f v : Val} {k : Nat} {l : Log}
    (h : appVal o n f v k = ⟨.stuck, l, k⟩) : ¬ ∃ w, AppVal f v w := by
  rintro ⟨w, d⟩
  obtain ⟨l', d'⟩ := AppVal.lift d
  rcases AppValL.nostuck d' o n k _ h with h1 | h1 | h1 <;> simp at h1

theorem evDec_unique_l {o : Oracle} {n : Nat} {E : Env} {d : Dec} {k : Nat} {VE : ValEnv} {l : Log}
    (h : evDec o n E d k = ⟨.value VE, l, k⟩) : ∀ VE' l', EvalDecL E d VE' l' → VE' = VE ∧ l' = l := by
  intro VE' l' dd
  rcases EvalDecL.nostuck dd o n k _ h with h1 | h1 | h1
  · simp at h1
  · simp at h1
  · simp only [Res.mk.injEq, Outcome.value.injEq] at h1; exact ⟨h1.1.symm, h1.2.1.symm⟩

theorem evDec_noValue_of_stuck {o : Oracle} {n : Nat} {E : Env} {d : Dec} {k : Nat} {l : Log}
    (h : evDec o n E d k = ⟨.stuck, l, k⟩) : ¬ ∃ VE, EvalDec E d VE := by
  rintro ⟨VE, dd⟩
  obtain ⟨l', d'⟩ := EvalDec.lift dd
  rcases EvalDecL.nostuck d' o n k _ h with h1 | h1 | h1 <;> simp at h1

theorem agrees_ofList (L : List Bool) : Agrees (Oracle.ofList L) 0 L := by
  intro i h; simp [Oracle.ofList, List.getD, h]

/-- D1's completeness: every derivation of the book is found by some choices and fuel. -/
theorem evExp_complete {E : Env} {e : Exp} {v : Val} (h : EvalExp E e v) :
    ∃ (L : List Bool) (n : Nat), (evExp (Oracle.ofList L) n E e 0).out = .value v := by
  obtain ⟨l, hl⟩ := EvalExp.lift h
  obtain ⟨L, n, c⟩ := EvalExpL.complete hl
  exact ⟨L, n, by rw [c (Oracle.ofList L) 0 n (Nat.le_refl n) (agrees_ofList L)]⟩

/-- Completeness for the logged relation: the derivation's log is the evaluator's. -/
theorem evExp_complete_l {E : Env} {e : Exp} {v : Val} {l : Log} (h : EvalExpL E e v l) :
    ∃ (L : List Bool) (n : Nat), evExp (Oracle.ofList L) n E e 0 = ⟨.value v, l, L.length⟩ := by
  obtain ⟨L, n, c⟩ := EvalExpL.complete h
  exact ⟨L, n, by rw [c (Oracle.ofList L) 0 n (Nat.le_refl n) (agrees_ofList L)]; simp⟩

theorem noValue_iff {E : Env} {e : Exp} :
    (¬ ∃ v, EvalExp E e v) ↔ ∀ (L : List Bool) (n : Nat) (v : Val),
      (evExp (Oracle.ofList L) n E e 0).out ≠ .value v := by
  constructor
  · intro h L n v hv; exact h ⟨v, evExp_sound hv⟩
  · rintro h ⟨v, hv⟩
    obtain ⟨L, n, hc⟩ := evExp_complete hv
    exact h L n v hc

end StandardElm
