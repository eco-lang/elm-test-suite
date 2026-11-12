/-
  A Standard Definition of Elm? Mechanisation: what the evaluator's results say about every
  derivation (plan decision D1).

  * `next_ge`: the index of the next unread choice only grows.
  * `nostuck`: for a derivation of the logged relation with value v and log l, the evaluator, at
    any fuel, oracle and index k, runs out of fuel, or reads a choice (its next index is above k),
    or gives exactly v and l without reading a choice. By induction on the derivation.
  * From these: a phrase on which the evaluator is stuck without reading a choice has no value
    (`noValue_of_stuck`), and a value it gives without reading a choice is the only one, with the
    only log (`evExp_unique`).
-/
import StandardElmMech.Sound
import StandardElmMech.Tactics

namespace StandardElm

/-! ## The index only grows -/

def NextAt (o : Oracle) (n : Nat) : Prop :=
  (∀ {E a k r}, evAtExp o n E a k = r → k ≤ r.next) ∧
  (∀ {E x k r}, evExpOpt o n E x k = r → k ≤ r.next) ∧
  (∀ {E row k r}, evExpRow o n E row k = r → k ≤ r.next) ∧
  (∀ {E x k r}, evExpRowOpt o n E x k = r → k ≤ r.next) ∧
  (∀ {E e k r}, evExp o n E e k = r → k ≤ r.next) ∧
  (∀ {f v k r}, appVal o n f v k = r → k ≤ r.next) ∧
  (∀ {E v m k r}, evMatch o n E v m k = r → k ≤ r.next) ∧
  (∀ {E v mr k r}, evMRule o n E v mr k = r → k ≤ r.next) ∧
  (∀ {E d k r}, evDec o n E d k = r → k ≤ r.next) ∧
  (∀ {E vb k r}, evValBind o n E vb k = r → k ≤ r.next) ∧
  (∀ {E x k r}, evValBindOpt o n E x k = r → k ≤ r.next) ∧
  (∀ {E v a k r}, matchAtPat o n E v a k = r → k ≤ r.next) ∧
  (∀ {E v p k r}, matchPatOpt o n E v p k = r → k ≤ r.next) ∧
  (∀ {E rc row k r}, matchPatRow o n E rc row k = r → k ≤ r.next) ∧
  (∀ {E rc x k r}, matchPatRowOpt o n E rc x k = r → k ≤ r.next) ∧
  (∀ {E v p k r}, matchPat o n E v p k = r → k ≤ r.next) ∧
  (∀ {E vs as k r}, matchAtPats o n E vs as k = r → k ≤ r.next)

set_option hygiene false in
macro "next_fin" : tactic => `(tactic| (
  (repeat' split)
  all_goals (apply_to_eqs [i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17])
  all_goals (try dsimp only at *)
  all_goals (try split at *)
  all_goals (try dsimp only at *)
  all_goals (first | omega | exact i1 rfl | exact i2 rfl | exact i3 rfl | exact i4 rfl | exact i5 rfl | exact i6 rfl | exact i7 rfl | exact i8 rfl | exact i9 rfl | exact i10 rfl | exact i11 rfl | exact i12 rfl | exact i13 rfl | exact i14 rfl | exact i15 rfl | exact i16 rfl | exact i17 rfl)))

theorem nextAt (o : Oracle) : ∀ n, NextAt o n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (intros; subst_vars; simp [evAtExp, evExpOpt, evExpRow, evExpRowOpt, evExp, appVal, evMatch,
        evMRule, evDec, evValBind, evValBindOpt, matchAtPat, matchPatOpt, matchPatRow,
        matchPatRowOpt, matchPat, matchAtPats])
  | succ n ih =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro E a k r h; subst h; cases a <;> simp only [evAtExp] <;> next_fin
    · intro E x k r h; subst h; cases x <;> simp only [evExpOpt] <;> next_fin
    · intro E row k r h; subst h; cases row <;> simp only [evExpRow] <;> next_fin
    · intro E x k r h; subst h; cases x <;> simp only [evExpRowOpt] <;> next_fin
    · intro E e k r h; subst h; cases e <;> simp only [evExp] <;> next_fin
    · intro f v k r h; subst h; cases f <;> simp only [appVal] <;> next_fin
    · intro E v m k r h; subst h; cases m <;> simp only [evMatch] <;> next_fin
    · intro E v mr k r h; subst h; cases mr <;> simp only [evMRule] <;> next_fin
    · intro E d k r h; subst h; cases d <;> simp only [evDec] <;> next_fin
    · intro E vb k r h; subst h; cases vb <;> simp only [evValBind] <;> next_fin
    · intro E x k r h; subst h; cases x <;> simp only [evValBindOpt] <;> next_fin
    · intro E v a k r h; subst h; cases a <;> simp only [matchAtPat] <;> next_fin
    · intro E v p k r h; subst h; cases v <;> cases p <;> simp only [matchPatOpt] <;> next_fin
    · intro E rc row k r h; subst h; cases row <;> simp only [matchPatRow] <;> next_fin
    · intro E rc x k r h; subst h; cases x <;> simp only [matchPatRowOpt] <;> next_fin
    · intro E v p k r h; subst h; cases p <;> simp only [matchPat] <;> next_fin
    · intro E vs as k r h; subst h; cases vs <;> cases as <;> simp only [matchAtPats] <;> next_fin

end StandardElm

namespace StandardElm

section
variable {o : Oracle} {n : Nat}
theorem evAtExp_next {E a k r} (h : evAtExp o n E a k = r) : k ≤ r.next := (nextAt o n).1 h
theorem evExpOpt_next {E x k r} (h : evExpOpt o n E x k = r) : k ≤ r.next := (nextAt o n).2.1 h
theorem evExpRow_next {E row k r} (h : evExpRow o n E row k = r) : k ≤ r.next := (nextAt o n).2.2.1 h
theorem evExpRowOpt_next {E x k r} (h : evExpRowOpt o n E x k = r) : k ≤ r.next := (nextAt o n).2.2.2.1 h
theorem evExp_next {E e k r} (h : evExp o n E e k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.1 h
theorem appVal_next {f v k r} (h : appVal o n f v k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.1 h
theorem evMatch_next {E v m k r} (h : evMatch o n E v m k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.1 h
theorem evMRule_next {E v mr k r} (h : evMRule o n E v mr k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.1 h
theorem evDec_next {E d k r} (h : evDec o n E d k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.1 h
theorem evValBind_next {E vb k r} (h : evValBind o n E vb k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.1 h
theorem evValBindOpt_next {E x k r} (h : evValBindOpt o n E x k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.2.1 h
theorem matchAtPat_next {E v a k r} (h : matchAtPat o n E v a k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.2.2.1 h
theorem matchPatOpt_next {E v p k r} (h : matchPatOpt o n E v p k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.2.2.2.1 h
theorem matchPatRow_next {E rc row k r} (h : matchPatRow o n E rc row k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.2.2.2.2.1 h
theorem matchPatRowOpt_next {E rc x k r} (h : matchPatRowOpt o n E rc x k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h
theorem matchPat_next {E v p k r} (h : matchPat o n E v p k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h
theorem matchAtPats_next {E vs as k r} (h : matchAtPats o n E vs as k = r) : k ≤ r.next := (nextAt o n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h
end

theorem sconTest_iff {v : Val} {sc : SCon} : sconTest v sc = true ↔ v = valof sc :=
  ⟨sconTest_true, fun h => by subst h; cases sc <;> simp [sconTest, valof]⟩

theorem conIs_iff {v : Val} {c : Con} : conIs v c = true ↔ v = .con c [] :=
  ⟨conIs_true, fun h => by subst h; simp [conIs]⟩

theorem conArgs_eq_some {v : Val} {c : Con} {n : Nat} {vs : List Val} :
    conArgs v c n = some vs ↔ v = .con c vs ∧ vs.length = n := by
  unfold conArgs; split
  · simp only [Val.con.injEq]
    constructor
    · intro h; split at h <;> simp_all
    · rintro ⟨⟨rfl, rfl⟩, rfl⟩; simp
  · simp_all

theorem conArgs_eq_none {v : Val} {c : Con} {n : Nat} :
    conArgs v c n = none ↔ ∀ vs, v = .con c vs → vs.length ≠ n := by
  constructor
  · intro h vs hv hl; subst hv; simp [conArgs, hl] at h
  · intro h; cases hc : conArgs v c n with
    | none => rfl
    | some vs => obtain ⟨h1, h2⟩ := conArgs_eq_some.mp hc; exact absurd h2 (h vs h1)

theorem MatchAtPatsL.length_eq : ∀ {E vs as r l}, MatchAtPatsL E vs as r l → vs.length = as.length
  | _, _, _, _, _, .seq_nil_l _ => rfl
  | _, _, _, _, _, .seq_cons_l _ _ _ _ _ _ _ _ _ _ h => by simp [MatchAtPatsL.length_eq h]

/-- What `nostuck` says of one premise: the evaluator `run`, at any index kk, runs out of fuel, reads
    a choice, or gives exactly w and l without reading one. A definition, so that `simp` leaves it
    alone while the tactic `apply_to_eqs` (which unfolds it) uses it. -/
def NS {α : Type} (run : Nat → Res α) (w : α) (l : Log) : Prop :=
  ∀ {kk rr}, run kk = rr → rr.out = .outOfFuel ∨ kk < rr.next ∨ rr = ⟨.value w, l, kk⟩

/-- Closes a case of `nostuck` (NoStuck.lean): split the evaluator's equation `h`, apply the
    premises' facts `ps` and the index lemmas to every equation, split the disjunctions, simplify. -/
syntax "ns_fin" "[" term,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ns_fin [$ps,*]) => `(tactic| (
    (repeat' (split at h))
    all_goals (subst h)
    all_goals (apply_to_eqs [evAtExp_next, evExpOpt_next, evExpRow_next, evExpRowOpt_next,
      evExp_next, appVal_next, evMatch_next, evMRule_next, evDec_next, evValBind_next,
      evValBindOpt_next, matchAtPat_next, matchPatOpt_next, matchPatRow_next, matchPatRowOpt_next,
      matchPat_next, matchAtPats_next])
    iterate 4 (
      all_goals (apply_to_eqs [$ps,*])
      all_goals split_ors
      all_goals (try simp_all [sconTest_iff, conIs_iff, conArgs_eq_some, conArgs_eq_none]))
    all_goals (first | omega | (right; left; omega) | (left; rfl) | (right; right; rfl) | skip)))

/-! ## Agreement of an oracle with a list of choices (for completeness, Completeness.lean) -/

/-- The oracle makes the choices L from index k on. -/
def Agrees (o : Oracle) (k : Nat) (L : List Bool) : Prop :=
  ∀ i (h : i < L.length), o (k + i) = L[i]

theorem agrees_nil {o : Oracle} {k : Nat} : Agrees o k [] := fun i h => absurd h (by simp)

theorem agrees_append {o : Oracle} {k : Nat} {L1 L2 : List Bool} (h : Agrees o k (L1 ++ L2)) :
    Agrees o k L1 ∧ Agrees o (k + L1.length) L2 := by
  constructor
  · intro i hi
    have := h i (by simp; omega)
    rw [this, List.getElem_append_left hi]
  · intro i hi
    have := h (L1.length + i) (by simp; omega)
    rw [show k + L1.length + i = k + (L1.length + i) by omega, this]
    simp

theorem agrees2 {o : Oracle} {k : Nat} {L0 L1 : List Bool} (h : Agrees o k (L0 ++ L1)) :
    Agrees o k L0 ∧ Agrees o (k + L0.length) L1 := agrees_append h

theorem agrees3 {o : Oracle} {k : Nat} {L0 L1 L2 : List Bool} (h : Agrees o k (L0 ++ L1 ++ L2)) :
    Agrees o k L0 ∧ Agrees o (k + L0.length) L1 ∧ Agrees o (k + L0.length + L1.length) L2 := by
  obtain ⟨h01, h2⟩ := agrees_append h
  obtain ⟨h0, h1⟩ := agrees_append h01
  exact ⟨h0, h1, by simpa [Nat.add_assoc] using h2⟩

theorem agrees_single {o : Oracle} {k : Nat} {b : Bool} (h : Agrees o k [b]) : o k = b := by
  simpa using h 0 (by simp)

theorem conArgs_none_of {v : Val} {c : Con} {n : Nat} (h : ¬ ∃ vs, v = .con c vs ∧ vs.length = n) :
    conArgs v c n = none :=
  conArgs_eq_none.mpr (fun vs hv hl => h ⟨vs, hv, hl⟩)

end StandardElm
