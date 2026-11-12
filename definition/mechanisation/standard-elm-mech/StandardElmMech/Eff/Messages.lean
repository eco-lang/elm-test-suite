/-
  A Standard Definition of Elm? Mechanisation: messages (effects.tex, sec:effects-messages, the
  rules r:e-msg-*), plan step 4.

  A leaf command or subscription, receiving an input (the outcome's value at a task leaf, a port's
  boundary value at an incoming port), gives a message: the task leaf the value itself, the port
  leaf its function applied to the decoded value, and a map its function applied to the message of
  its command. `RecvL` is the logged twin (D4); Dec has no log, so the logs are the applications'.
  `recvL` is the executable counterpart, sound, complete and, where it reads no choice, unique.
-/
import StandardElmMech.Eff.EncDec
import StandardElmMech.Eff.Task

namespace StandardElm.Eff
open StandardElm

/-- The input of a leaf: a value (task leaves) or a port name with a boundary value. -/
inductive Input where
  | val (v : Val)
  | port (p : String) (j : BVal)
  deriving Inhabited

/-- c, receiving x, gives the message v. -/
inductive Recv : Val → Input → Val → Prop where
  /-- r:e-msg-task -/
  | r_e_msg_task (tk v : Val) : Recv (.leaf .task tk) (.val v) v
  /-- r:e-msg-port -/
  | r_e_msg_port (p : String) (τ : PTy) (f : Val) (j : BVal) (v' v'' : Val) :
      Dec τ j v' → AppVal f v' v'' → Recv (.leaf (.inn p τ) f) (.port p j) v''
  /-- r:e-msg-map -/
  | r_e_msg_map (f c : Val) (x : Input) (v' v'' : Val) :
      Recv c x v' → AppVal f v' v'' → Recv (.mapE f c) x v''

/-- The logged twin of `Recv` (D4). -/
inductive RecvL : Val → Input → Val → Log → Prop where
  /-- r:e-msg-task -/
  | r_e_msg_task_l (tk v : Val) : RecvL (.leaf .task tk) (.val v) v []
  /-- r:e-msg-port -/
  | r_e_msg_port_l (p : String) (τ : PTy) (f : Val) (j : BVal) (v' v'' : Val) (l : Log) :
      Dec τ j v' → AppValL f v' v'' l → RecvL (.leaf (.inn p τ) f) (.port p j) v'' l
  /-- r:e-msg-map -/
  | r_e_msg_map_l (f c : Val) (x : Input) (v' v'' : Val) (l1 l2 : Log) :
      RecvL c x v' l1 → AppValL f v' v'' l2 → RecvL (.mapE f c) x v'' (l1 ++ l2)

theorem RecvL.forget : ∀ {c x v l}, RecvL c x v l → Recv c x v
  | _, _, _, _, .r_e_msg_task_l _ _ => .r_e_msg_task _ _
  | _, _, _, _, .r_e_msg_port_l _ _ _ _ _ _ _ hd ha => .r_e_msg_port _ _ _ _ _ _ hd ha.forget
  | _, _, _, _, .r_e_msg_map_l _ _ _ _ _ _ _ hr ha => .r_e_msg_map _ _ _ _ _ hr.forget ha.forget

theorem Recv.lift : ∀ {c x v}, Recv c x v → ∃ l, RecvL c x v l
  | _, _, _, .r_e_msg_task _ _ => ⟨[], .r_e_msg_task_l _ _⟩
  | _, _, _, .r_e_msg_port _ _ _ _ _ _ hd ha =>
    let ⟨l, ha'⟩ := AppVal.lift ha; ⟨l, .r_e_msg_port_l _ _ _ _ _ _ _ hd ha'⟩
  | _, _, _, .r_e_msg_map _ _ _ _ _ hr ha =>
    let ⟨l1, hr'⟩ := Recv.lift hr
    let ⟨l2, ha'⟩ := AppVal.lift ha
    ⟨l1 ++ l2, .r_e_msg_map_l _ _ _ _ _ _ _ hr' ha'⟩

/-- The message of c receiving x, by the oracle evaluator. -/
def recvL (o : Oracle) (n : Nat) : Val → Input → Nat → Res Val
  | .leaf .task _, .val v, k => ⟨.value v, [], k⟩
  | .leaf (.inn p τ) f, .port p' j, k =>
    if p = p' then
      match dec τ j with
      | some v' => appVal o n f v' k
      | none => ⟨.stuck, [], k⟩
    else ⟨.stuck, [], k⟩
  | .mapE f c, x, k =>
    match recvL o n c x k with
    | ⟨.value v', l1, k1⟩ =>
      match appVal o n f v' k1 with
      | ⟨.value v'', l2, k2⟩ => ⟨.value v'', l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
  | _, _, k => ⟨.stuck, [], k⟩

/-- A structural test that no rule applies: an out leaf, a task leaf given a port input, a port
    leaf given a value or another port's input, or an undecodable boundary value. -/
def recvNone : Val → Input → Bool
  | .leaf .task _, .val _ => false
  | .leaf (.inn p τ) _, .port p' j => p != p' || (dec τ j).isNone
  | .mapE _ c, x => recvNone c x
  | _, _ => true

theorem recvL_sound {o : Oracle} {n : Nat} : ∀ (c : Val) {x : Input} {k : Nat} {v : Val} {l : Log}
    {k' : Nat}, recvL o n c x k = ⟨.value v, l, k'⟩ → RecvL c x v l
  | .mapE f c, x, k, v, l, k', h => by
    simp only [recvL] at h
    rcases hr : recvL o n c x k with ⟨out, l1, k1⟩
    rw [hr] at h
    cases out with
    | value v' =>
      simp only at h
      rcases ha : appVal o n f v' k1 with ⟨out2, l2, k2⟩
      rw [ha] at h
      cases out2 <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .r_e_msg_map_l _ _ _ _ _ _ _ (recvL_sound c hr) (appVal_sound_l ha)
    | stuck => simp at h
    | outOfFuel => simp at h
  | .leaf m w, x, k, v, l, k', h => by
    cases m with
    | task =>
      cases x with
      | val v0 => simp [recvL] at h; obtain ⟨rfl, rfl, -⟩ := h; exact .r_e_msg_task_l _ _
      | port _ _ => unfold recvL at h; simp at h
    | out _ => unfold recvL at h; cases x <;> simp at h
    | inn p τ =>
      cases x with
      | val _ => unfold recvL at h; simp at h
      | port p' j =>
        simp only [recvL] at h
        split at h
        · rename_i hp; subst hp
          cases hd : dec τ j with
          | none => simp [hd] at h
          | some v' =>
            simp only [hd] at h
            exact .r_e_msg_port_l _ _ _ _ _ _ _ ((dec_iff τ j v').mpr hd) (appVal_sound_l h)
        · cases h
  | .unit, _, _, _, _, _, h | .sv _, _, _, _, _, _, h | .basApp _ _, _, _, _, _, _, h
  | .con _ _, _, _, _, _, _, h | .record _, _, _, _, _, _, h | .tuple _ _ _, _, _, _, _, _, h
  | .closure _ _ _ _, _, _, _, _, _, h | .batch _, _, _, _, _, _, h | .prog _, _, _, _, _, _, h
  | .succeed _, _, _, _, _, _, h | .fail _, _, _, _, _, _, h | .andThen _ _, _, _, _, _, _, h
  | .onError _ _, _, _, _, _, _, h | .prim _ _, _, _, _, _, _, h | .pid _, _, _, _, _, _, h
  | .bv _, _, _, _, _, _, h => by unfold recvL at h; simp at h

theorem recvNone_sound : ∀ {c : Val} {x : Input}, recvNone c x = true → ¬ ∃ v, Recv c x v := by
  intro c x h ⟨v, d⟩
  induction d with
  | r_e_msg_task => simp [recvNone] at h
  | r_e_msg_port p τ f j v' v'' hd _ =>
    simp only [recvNone, bne_self_eq_false, Bool.false_or] at h
    rw [(dec_iff τ j v').mp hd] at h
    simp at h
  | r_e_msg_map f c x v' v'' _ _ ih => exact ih (by simpa [recvNone] using h)

/-- Every logged reception is found by the evaluator, with some choices and fuel. -/
theorem recvL_complete {c : Val} {x : Input} {v : Val} {l : Log} (d : RecvL c x v l) :
    CompleteFor (fun o m k => recvL o m c x k) v l := by
  induction d with
  | r_e_msg_task_l tk v => exact ⟨[], 0, fun o k m _ _ => by simp [recvL]⟩
  | r_e_msg_port_l p τ f j v' v'' l hd ha =>
    obtain ⟨L, n, c⟩ := AppValL.complete ha
    exact ⟨L, n, fun o k m hm hag => by simp [recvL, (dec_iff τ j v').mp hd, c o k m hm hag]⟩
  | r_e_msg_map_l f c x v' v'' l1 l2 hr ha ih =>
    obtain ⟨L1, n1, c1⟩ := ih
    obtain ⟨L2, n2, c2⟩ := AppValL.complete ha
    refine ⟨L1 ++ L2, max n1 n2, fun o k m hm hag => ?_⟩
    obtain ⟨hag1, hag2⟩ := agrees_append hag
    have e1 := c1 o k m (by omega) hag1
    simp only at e1
    have e2 := c2 o (k + L1.length) m (by omega) hag2
    simp only [recvL, e1, e2, List.length_append, Nat.add_assoc]

/-- The index of the next unread choice only grows. -/
theorem recvL_next {o : Oracle} {n : Nat} : ∀ (c : Val) {x : Input} {k : Nat},
    k ≤ (recvL o n c x k).next
  | .mapE f c, x, k => by
    simp only [recvL]
    have h1 := recvL_next (o := o) (n := n) c (x := x) (k := k)
    rcases hr : recvL o n c x k with ⟨out, l1, k1⟩
    rw [hr] at h1; simp only at h1
    cases out with
    | value v' =>
      simp only
      rcases ha : appVal o n f v' k1 with ⟨out2, l2, k2⟩
      have h2 := appVal_next ha; simp only at h2
      cases out2 <;> simp <;> omega
    | stuck => simpa using h1
    | outOfFuel => simpa using h1
  | .leaf m w, x, k => by
    cases m with
    | task => cases x <;> simp [recvL]
    | out _ => unfold recvL; cases x <;> simp
    | inn p τ =>
      cases x with
      | val _ => unfold recvL; simp
      | port p' j =>
        simp only [recvL]
        split
        · cases dec τ j with
          | none => simp
          | some v' => exact appVal_next rfl
        · simp
  | .unit, _, _ | .sv _, _, _ | .basApp _ _, _, _ | .con _ _, _, _ | .record _, _, _
  | .tuple _ _ _, _, _ | .closure _ _ _ _, _, _ | .batch _, _, _ | .prog _, _, _ | .succeed _, _, _
  | .fail _, _, _ | .andThen _ _, _, _ | .onError _ _, _, _ | .prim _ _, _, _ | .pid _, _, _
  | .bv _, _, _ => by unfold recvL; simp

/-- When the evaluator reads no choice, its message and log are the only ones. -/
theorem recvL_unique {o : Oracle} {n : Nat} {c : Val} {x : Input} {k : Nat} {v : Val} {l : Log}
    (h : recvL o n c x k = ⟨.value v, l, k⟩) : ∀ v' l', RecvL c x v' l' → v' = v ∧ l' = l := by
  intro v' l' d
  induction d generalizing v l k with
  | r_e_msg_task_l tk v0 => simp [recvL] at h; exact ⟨h.1, h.2.symm⟩
  | r_e_msg_port_l p τ f j w w' l0 hd ha =>
    simp only [recvL, ite_true, (dec_iff τ j w).mp hd] at h
    exact appVal_unique_l h _ _ ha
  | r_e_msg_map_l f c0 x0 w w' l1 l2 hr ha ih =>
    simp only [recvL] at h
    rcases hr' : recvL o n c0 x0 k with ⟨out, la, ka⟩
    rw [hr'] at h
    cases out with
    | value u =>
      simp only at h
      rcases ha' : appVal o n f u ka with ⟨out2, lb, kb⟩
      rw [ha'] at h
      cases out2 <;> simp at h
      obtain ⟨rfl, rfl, hk⟩ := h
      have h1 := recvL_next (o := o) (n := n) c0 (x := x0) (k := k); rw [hr'] at h1; simp only at h1
      have h2 := appVal_next ha'; simp only at h2
      have hka : ka = k := by omega
      subst hka
      have hkb : kb = ka := by omega
      subst hkb
      obtain ⟨rfl, rfl⟩ := ih hr'
      obtain ⟨rfl, rfl⟩ := appVal_unique_l ha' _ _ ha
      exact ⟨rfl, rfl⟩
    | stuck => simp at h
    | outOfFuel => simp at h

end StandardElm.Eff
