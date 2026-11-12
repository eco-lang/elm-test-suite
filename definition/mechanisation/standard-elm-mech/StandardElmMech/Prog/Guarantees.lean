/-
  A Standard Definition of Elm? Mechanisation: the guarantees of A86 (programs.tex,
  sec:programs-execution, the property after the transition rules), plan step 5.

  `a86_step`: messages are handled one at a time, by r:p-update, in queue order, each update
  applying update to the model of the previous one, and the commands of an update are dispatched
  in its step; every other step keeps the model and only appends to the queue of messages.
  `a86_out_fifo`: the values of each outgoing port are delivered in the order in which they joined
  its queue. "Apart from these ... interleave in every way the rules allow" says there are no
  further guarantees; it is not a theorem (Rulings.lean illustrates it, `a66_batch_order_open`).
-/
import StandardElmMech.Prog.Exec
import StandardElmMech.Mod.Properties

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-- Messages are handled one at a time, by r:p-update, in queue order, each update applying
    update to the model of the previous one; every other step keeps the model and only appends
    to the queue. The commands of an update are dispatched in its step. -/
theorem a86_step {PE : PortEnv} {r : List (String × Val)} {K K' : Config} {a : Option Event}
    (h : Step PE r K a K') :
    (K'.model = K.model ∧ ∃ ms, K'.msgs = K.msgs ++ ms) ∨
    (a = none ∧ ∃ v1 fu v2 cm cs L, K.msgs = v1 :: K'.msgs ∧ field r "update" = some fu ∧
       AppVal fu v1 v2 ∧ AppVal v2 K.model (.tuple K'.model cm none) ∧
       flat cm = some cs ∧ L.Perm cs ∧
       Dispatch K.time K.procs K.outq K.pending L K'.procs K'.outq K'.pending) := by
  cases h with
  | r_p_update s v v1 M P sb Q H fu fs v2 v' cm cs L P' Q' H' sb' h1 _ h3 h4 h5 h6 h7 _ =>
    exact .inr ⟨rfl, v1, fu, v2, cm, cs, L, rfl, h1, h3, h4, h5, h6, h7⟩
  | r_p_proc_message => exact .inl ⟨rfl, _, rfl⟩
  | r_p_in_accept => exact .inl ⟨rfl, _, rfl⟩
  | r_p_platform _ _ _ hp => cases hp
  | r_p_in_reject => exact .inl ⟨rfl, [], by simp⟩
  | _ => exact .inl ⟨rfl, [], by simp⟩

/-! ## Outgoing queues -/

/-- The values delivered on port p along a path, in order. -/
def outsOn (p : String) (π : Path) : List BVal :=
  π.filterMap fun (a, _) => match a with
    | some (.out q j) => if q = p then some j else none
    | _ => none

/-- The final configuration of a path from K. -/
def Path.last (K : Config) (π : Path) : Config := π.foldl (fun _ x => x.2) K

/-- For each step of a path from K not labelled Out(p, _), what it appended to p's queue. -/
def appendedOn (p : String) : Config → Path → List BVal
  | _, [] => []
  | K, (a, K') :: π =>
    (match a with
      | some (.out q _) => if q = p then [] else (K'.outq.get p).drop (K.outq.get p).length
      | _ => (K'.outq.get p).drop (K.outq.get p).length) ++ appendedOn p K' π

theorem OutQ.get_fmPlus_same (Q : OutQ) (p : String) (J : List BVal) :
    OutQ.get (fmPlus Q [(p, J)]) p = J := by
  simp [OutQ.get, Mod.fmLookup_fmPlus, fmLookup]

theorem OutQ.get_fmPlus_other (Q : OutQ) (p q : String) (J : List BVal) (h : q ≠ p) :
    OutQ.get (fmPlus Q [(q, J)]) p = Q.get p := by
  have : (q == p) = false := by simpa using h
  simp [OutQ.get, Mod.fmLookup_fmPlus, fmLookup, this]

/-- Dispatch only appends to a queue. -/
theorem dispatch_outq {s : Time} {P : Procs} {Q : OutQ} {H : Pending} {L : List Val} {P' : Procs}
    {Q' : OutQ} {H' : Pending} (h : Dispatch s P Q H L P' Q' H') (p : String) :
    ∃ new, Q'.get p = Q.get p ++ new := by
  induction h with
  | r_p_disp_empty => exact ⟨[], by simp⟩
  | r_p_disp_task _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | r_p_disp_out P Q H c q j js L P' Q' H' _ hq _ ih =>
    obtain ⟨new, hn⟩ := ih
    by_cases hqp : q = p
    · subst hqp
      refine ⟨j :: new, ?_⟩
      rw [hn, OutQ.get_fmPlus_same]
      simp [OutQ.get, hq]
    · rw [OutQ.get_fmPlus_other _ _ _ _ hqp] at hn
      exact ⟨new, hn⟩
  | r_p_disp_plat _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- Each step either delivers the head of p's queue on p, or delivers nothing on p and only
    appends to p's queue. -/
theorem step_outq {PE : PortEnv} {r : List (String × Val)} {K K' : Config} {a : Option Event}
    (h : Step PE r K a K') (p : String) :
    (a = some (.out p (K.outq.get p).head!) ∧ K.outq.get p = (K.outq.get p).head! :: K'.outq.get p) ∨
    ((∀ j, a ≠ some (.out p j)) ∧ ∃ new, K'.outq.get p = K.outq.get p ++ new) := by
  cases h with
  | r_p_update _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h7 _ =>
    exact .inr ⟨by simp, dispatch_outq h7 p⟩
  | r_p_proc_step _ _ _ _ _ _ _ _ _ _ _ a =>
    exact .inr ⟨by cases a <;> simp, [], by simp⟩
  | r_p_out _ _ _ _ _ Q _ q j J hq =>
    by_cases hqp : q = p
    · subst hqp
      have hg : Q.get q = j :: J := by simp [OutQ.get, hq]
      refine .inl ⟨?_, ?_⟩
      · rw [hg]; rfl
      · rw [hg, OutQ.get_fmPlus_same]; rfl
    · refine .inr ⟨?_, [], ?_⟩
      · intro j' he; simp at he; exact hqp he.1
      · simp [OutQ.get_fmPlus_other _ _ _ _ hqp]
  | r_p_platform _ _ _ hp => cases hp
  | _ => exact .inr ⟨by simp, [], by simp⟩

/-- The values of each outgoing port are delivered in the order in which they joined its queue:
    over any execution, what is delivered on p, followed by what remains queued, is what was
    queued at the start followed by what each step appended, in step order. -/
theorem a86_out_fifo {PE : PortEnv} {r : List (String × Val)} {hst : Host} {K : Config}
    {hs : List BVal} {π : Path} {hs' : List BVal} (h : Exec PE r hst K hs π hs') (p : String) :
    outsOn p π ++ (Path.last K π).outq.get p = K.outq.get p ++ appendedOn p K π := by
  induction h with
  | nil K hs => simp [outsOn, Path.last, appendedOn]
  | cons K hs a K' hs' π hs'' hst' _ _ ih =>
    have hl : Path.last K ((a, K') :: π) = Path.last K' π := rfl
    rw [hl]
    rcases step_outq hst' p with ⟨ha, hq⟩ | ⟨hna, new, hn⟩
    · generalize (K.outq.get p).head! = hd at ha hq
      subst ha
      have ho : outsOn p ((some (.out p hd), K') :: π) = hd :: outsOn p π := by simp [outsOn]
      have hap : appendedOn p K ((some (.out p hd), K') :: π) = appendedOn p K' π := by
        simp [appendedOn]
      rw [ho, hap, List.cons_append, ih, hq]; rfl
    · have hd : (K'.outq.get p).drop (K.outq.get p).length = new := by rw [hn]; simp
      have ⟨ho, hap⟩ : outsOn p ((a, K') :: π) = outsOn p π ∧
          appendedOn p K ((a, K') :: π) = new ++ appendedOn p K' π := by
        rcases a with _ | ⟨q, j⟩ | ⟨q, j⟩ | x | d
        · simp [outsOn, appendedOn, hd]
        · simp [outsOn, appendedOn, hd]
        · by_cases hqp : q = p
          · subst hqp; exact absurd rfl (hna j)
          · simp [outsOn, appendedOn, hqp, hd]
        · simp [outsOn, appendedOn, hd]
        · simp [outsOn, appendedOn, hd]
      rw [ho, hap, ih, hn, List.append_assoc]

end StandardElm.Prog
