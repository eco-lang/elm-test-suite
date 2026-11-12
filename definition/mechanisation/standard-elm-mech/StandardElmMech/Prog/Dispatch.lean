/-
  A Standard Definition of Elm? Mechanisation: dispatch (programs.tex, sec:programs-dispatch, the
  rules r:p-disp-*), plan step 5.

  s, P, Q, H ⊢ L ⇒ (P', Q', H'): the leaves of a command, in the order of an enumeration L of its
  flattening, each start a process (a task leaf), join an outgoing port's queue (an out leaf), or
  are handed to the platform (a leaf of a platform manager; none exist, [params]). Dispatch has no
  application premise, so it has no logged twin. `dispatchFn` dispatches with fresh identifiers in
  order and is sound.
-/
import StandardElmMech.Prog.Objects
import StandardElmMech.Eff.Flat

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-- s, P, Q, H ⊢ L ⇒ (P', Q', H'). `c ∈ Leaf(m, v)` is `leafCore c = some (m, v)`. -/
inductive Dispatch : Time → Procs → OutQ → Pending → List Val → Procs → OutQ → Pending → Prop where
  /-- r:p-disp-empty -/
  | r_p_disp_empty (s : Time) (P : Procs) (Q : OutQ) (H : Pending) : Dispatch s P Q H [] P Q H
  /-- r:p-disp-task -/
  | r_p_disp_task (s : Time) (P : Procs) (Q : OutQ) (H : Pending) (c tk : Val) (n : Nat) (L : List Val)
      (P' : Procs) (Q' : OutQ) (H' : Pending) :
      leafCore c = some (.task, tk) → n ∉ P.dom →
      Dispatch s (P.set n (.live ⟨tk, s, some c⟩)) Q H L P' Q' H' →
      Dispatch s P Q H (c :: L) P' Q' H'
  /-- r:p-disp-out -/
  | r_p_disp_out (s : Time) (P : Procs) (Q : OutQ) (H : Pending) (c : Val) (p : String) (j : BVal)
      (js : List BVal) (L : List Val) (P' : Procs) (Q' : OutQ) (H' : Pending) :
      leafCore c = some (.out p, .bv j) → fmLookup Q p = some js →
      Dispatch s P (fmPlus Q [(p, js ++ [j])]) H L P' Q' H' →
      Dispatch s P Q H (c :: L) P' Q' H'
  /-- r:p-disp-plat: m ∈ Mgr_plat, empty here, so never applicable ([params]) -/
  | r_p_disp_plat (s : Time) (P : Procs) (Q : OutQ) (H : Pending) (c : Val) (m : Mgr) (v : Val)
      (L : List Val) (P' : Procs) (Q' : OutQ) (H' : Pending) :
      leafCore c = some (m, v) → m ∈ platMgrs →
      Dispatch s P Q (H ++ [c]) L P' Q' H' →
      Dispatch s P Q H (c :: L) P' Q' H'

/-- A process identifier never used: one more than the largest in P. -/
def freshPid (P : Procs) : Nat := P.dom.foldl max 0 + 1

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], _ => Nat.le_refl _
  | x :: xs, a => Nat.le_trans (Nat.le_max_left a x) (le_foldl_max xs (max a x))

theorem mem_le_foldl_max : ∀ (l : List Nat) (a n : Nat), n ∈ l → n ≤ l.foldl max a
  | [], _, _, h => by simp at h
  | x :: xs, a, n, h => by
    simp only [List.mem_cons] at h
    simp only [List.foldl_cons]
    rcases h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a n) (le_foldl_max xs _)
    · exact mem_le_foldl_max xs _ n h

theorem freshPid_fresh (P : Procs) : freshPid P ∉ P.dom := by
  intro h
  have := mem_le_foldl_max P.dom 0 _ h
  unfold freshPid at this
  omega

/-- Dispatch a sequence, giving fresh identifiers in order; returns the new identifiers in the
    order created. `none` if a leaf is of no manager this program has (an unknown port). -/
def dispatchFn (s : Time) : Procs → OutQ → List Val → Option (Procs × OutQ × List Nat)
  | P, Q, [] => some (P, Q, [])
  | P, Q, c :: L =>
    match leafCore c with
    | some (.task, tk) =>
      let n := freshPid P
      (dispatchFn s (P.set n (.live ⟨tk, s, some c⟩)) Q L).map fun (P', Q', ns) => (P', Q', n :: ns)
    | some (.out p, .bv j) =>
      match fmLookup Q p with
      | some js => dispatchFn s P (fmPlus Q [(p, js ++ [j])]) L
      | none => none
    | _ => none

theorem dispatchFn_sound {s : Time} {H : Pending} : ∀ {L : List Val} {P : Procs} {Q : OutQ}
    {P' : Procs} {Q' : OutQ} {ns : List Nat},
    dispatchFn s P Q L = some (P', Q', ns) → Dispatch s P Q H L P' Q' H
  | [], P, Q, P', Q', ns, h => by
    simp only [dispatchFn, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact .r_p_disp_empty s P Q H
  | c :: L, P, Q, P', Q', ns, h => by
    simp only [dispatchFn] at h
    split at h
    · rename_i tk hc
      cases hr : dispatchFn s (P.set (freshPid P) (.live ⟨tk, s, some c⟩)) Q L with
      | none => simp [hr] at h
      | some t =>
        obtain ⟨P1, Q1, ns1⟩ := t
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact .r_p_disp_task s P Q H c tk _ L _ _ H hc (freshPid_fresh P) (dispatchFn_sound hr)
    · rename_i p j hc
      split at h
      · rename_i js hq
        exact .r_p_disp_out s P Q H c p j js L _ _ H hc hq (dispatchFn_sound h)
      · cases h
    · cases h

end StandardElm.Prog
