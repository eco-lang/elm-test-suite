/-
  A Standard Definition of Elm? Mechanisation: the statements of section 7 for W on F_b
  (plan step 11, milestone (b)), from the main induction L11 (WComplete.lean, L12).

  * `wRefutation`: `WRefutation` (W fails ⇒ no derivation without free `bnd` variables).
  * `inferExpW_ne_fail`: the first half of completeness (a derivation exists ⇒ W does not fail,
    for every fuel).
  * `inferExpW_instance`: L12 for the result of W: every derivation is the image of W's result by
    a substitution that fixes the rigid variables (the root context's), with the instance lists
    left out. This is the substance of principality; `IsPrincipalB` (node by node) is assembled
    from it in a later file.

  The derivations considered are those without free `bnd` variables (`NoFreeBndExp`, as in
  `IsPrincipalB`): the types at the nodes of the derivation; `tysExp_nodes` reads the types of the
  phrase off its nodes.
-/
import StandardElmMech.Stat.Complete.WComplete

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## The types of a phrase are at its nodes -/

def NTys (ns : List Node) : List Ty := ns.flatMap Node.tys

theorem mem_NTys_append {τ : Ty} {l1 l2 : List Node} : τ ∈ NTys (l1 ++ l2) ↔ τ ∈ NTys l1 ∨ τ ∈ NTys l2 := by
  simp [NTys]

theorem mem_NTys_head {τ : Ty} {n : Node} {l : List Node} (h : τ ∈ n.tys) : τ ∈ NTys (n :: l) := by
  simp only [NTys, List.flatMap_cons, List.mem_append]; exact .inl h

macro "close_nodes " t:term : tactic => `(tactic| (
  have hh := $t
  simp only [NTys] at hh ⊢
  simp [nodesAtPat, nodesPat, nodesPatRowOpt, nodesPatRow, nodesPatOpt, nodesAtPats, nodesAtExp, nodesExp,
    nodesExpRow, nodesExpRowOpt, nodesExpOpt, nodesMatch, nodesMatchOpt, nodesDec, nodesValBind,
    nodesValBindOpt, hh]))

macro "close_head" : tactic => `(tactic| (
  simp [NTys, nodesAtPat, nodesPat, nodesPatRowOpt, nodesPatRow, nodesAtExp, nodesValBind, AAtPat.ty, APatRow.row]))

mutual
theorem tysAtPat_nodes (U : List BVar) (path : List Nat) : ∀ p : AAtPat, ∀ τ ∈ tysAtPat p,
    τ ∈ NTys (nodesAtPat U path p)
  | .wild _, τ, h | .scon _ _, τ, h | .var _ _, τ, h | .con _ _ _, τ, h | .nil _, τ, h => by
    simp only [tysAtPat, List.mem_singleton] at h; subst h; close_head
  | .unit, τ, h => by simp [tysAtPat] at h
  | .tuple p1 p2 p3, τ, h => by
    simp only [tysAtPat, List.mem_append] at h
    rcases h with (h | h) | h
    · close_nodes tysPat_nodes U (path ++ [0]) p1 τ h
    · close_nodes tysPat_nodes U (path ++ [1]) p2 τ h
    · close_nodes tysPatOpt_nodes U (path ++ [2]) p3 τ h
  | .record r τ0, τ, h => by
    simp only [tysAtPat, List.mem_cons] at h
    rcases h with rfl | h
    · close_head
    · close_nodes tysPatRowOpt_nodes U (path ++ [0]) r τ h
  | .paren p, τ, h => by
    simp only [tysAtPat] at h
    close_nodes tysPat_nodes U (path ++ [0]) p τ h
theorem tysPatRowOpt_nodes (U : List BVar) (path : List Nat) : ∀ r : Option APatRow, ∀ τ ∈ tysPatRowOpt r,
    τ ∈ NTys (nodesPatRowOpt U path r)
  | none, τ, h => by simp [tysPatRowOpt] at h
  | some (.field l τ0 rest), τ, h => by
    simp only [tysPatRowOpt, tysPatRow, List.mem_cons] at h
    rcases h with rfl | h
    · close_head
    · close_nodes tysPatRowOpt_nodes U (path ++ [0]) rest τ h
theorem tysPat_nodes (U : List BVar) (path : List Nat) : ∀ p : APat, ∀ τ ∈ tysPat p, τ ∈ NTys (nodesPat U path p)
  | .atpat a, τ, h => by
    simp only [tysPat] at h
    close_nodes tysAtPat_nodes U (path ++ [0]) a τ h
  | .con lc inst args τ0, τ, h => by
    simp only [tysPat, List.mem_cons] at h
    rcases h with rfl | h
    · close_head
    · close_nodes tysAtPats_nodes U path 0 args τ h
  | .cons p1 p2, τ, h => by
    simp only [tysPat, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysPat_nodes U (path ++ [0]) p1 τ h
    · close_nodes tysPat_nodes U (path ++ [1]) p2 τ h
  | .as p x, τ, h => by
    simp only [tysPat] at h
    close_nodes tysPat_nodes U (path ++ [0]) p τ h
theorem tysPatOpt_nodes (U : List BVar) (path : List Nat) : ∀ p : Option APat, ∀ τ ∈ tysPatOpt p,
    τ ∈ NTys (nodesPatOpt U path p)
  | none, τ, h => by simp [tysPatOpt] at h
  | some p, τ, h => by simp only [tysPatOpt] at h; simp only [nodesPatOpt]; exact tysPat_nodes U path p τ h
theorem tysAtPats_nodes (U : List BVar) (path : List Nat) : ∀ (i : Nat) (l : List AAtPat), ∀ τ ∈ tysAtPats l,
    τ ∈ NTys (nodesAtPats U path i l)
  | _, [], τ, h => by simp [tysAtPats] at h
  | i, a :: as, τ, h => by
    simp only [tysAtPats, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysAtPat_nodes U (path ++ [i]) a τ h
    · close_nodes tysAtPats_nodes U path (i + 1) as τ h
end

mutual
theorem tysAtExp_nodes (C : Ctx) (path : List Nat) : ∀ a : AAtExp, ∀ τ ∈ tysAtExp false a,
    τ ∈ NTys (nodesAtExp C path a)
  | .scon _ _, τ, h | .var _ _ _, τ, h | .con _ _ _, τ, h | .op _ _ _, τ, h | .nil _, τ, h => by
    simp only [tysAtExp, List.mem_singleton] at h; subst h; close_head
  | .unit, τ, h => by simp [tysAtExp] at h
  | .tuple e1 e2 e3, τ, h => by
    simp only [tysAtExp, List.mem_append] at h
    rcases h with (h | h) | h
    · close_nodes tysExp_nodes C (path ++ [0]) e1 τ h
    · close_nodes tysExp_nodes C (path ++ [1]) e2 τ h
    · close_nodes tysExpOpt_nodes C (path ++ [2]) e3 τ h
  | .record r, τ, h => by
    simp only [tysAtExp] at h
    close_nodes tysExpRowOpt_nodes C (path ++ [0]) r τ h
  | .update x inst τ0 r, τ, h => by
    simp only [tysAtExp, List.mem_cons] at h
    rcases h with rfl | h
    · close_head
    · close_nodes tysExpRow_nodes C (path ++ [0]) r τ h
  | .letE d e, τ, h => by
    simp only [tysAtExp, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysDec_nodes C (path ++ [0]) d τ h
    · close_nodes tysExp_nodes (C.plusVE (d.result C)) (path ++ [1]) e τ h
  | .paren e, τ, h => by
    simp only [tysAtExp] at h
    close_nodes tysExp_nodes C (path ++ [0]) e τ h
theorem tysExpRow_nodes (C : Ctx) (path : List Nat) : ∀ r : AExpRow, ∀ τ ∈ tysExpRow false r,
    τ ∈ NTys (nodesExpRow C path r)
  | .field l e rest, τ, h => by
    simp only [tysExpRow, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysExp_nodes C (path ++ [0]) e τ h
    · close_nodes tysExpRowOpt_nodes C (path ++ [1]) rest τ h
theorem tysExpRowOpt_nodes (C : Ctx) (path : List Nat) : ∀ r : Option AExpRow, ∀ τ ∈ tysExpRowOpt false r,
    τ ∈ NTys (nodesExpRowOpt C path r)
  | none, τ, h => by simp [tysExpRowOpt] at h
  | some r, τ, h => by simp only [tysExpRowOpt] at h; simp only [nodesExpRowOpt]; exact tysExpRow_nodes C path r τ h
theorem tysExp_nodes (C : Ctx) (path : List Nat) : ∀ e : AExp, ∀ τ ∈ tysExp false e, τ ∈ NTys (nodesExp C path e)
  | .atexp a, τ, h => by
    simp only [tysExp] at h
    close_nodes tysAtExp_nodes C (path ++ [0]) a τ h
  | .app e a, τ, h => by
    simp only [tysExp, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysExp_nodes C (path ++ [0]) e τ h
    · close_nodes tysAtExp_nodes C (path ++ [1]) a τ h
  | .lam p e, τ, h => by
    simp only [tysExp, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysAtPat_nodes C.U (path ++ [0]) p τ h
    · close_nodes tysExp_nodes (C.plusVE p.ve) (path ++ [1]) e τ h
  | .caseE e m, τ, h => by
    simp only [tysExp, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysExp_nodes C (path ++ [0]) e τ h
    · close_nodes tysMatch_nodes C (path ++ [1]) m τ h
theorem tysExpOpt_nodes (C : Ctx) (path : List Nat) : ∀ e : Option AExp, ∀ τ ∈ tysExpOpt false e,
    τ ∈ NTys (nodesExpOpt C path e)
  | none, τ, h => by simp [tysExpOpt] at h
  | some e, τ, h => by simp only [tysExpOpt] at h; simp only [nodesExpOpt]; exact tysExp_nodes C path e τ h
theorem tysMatch_nodes (C : Ctx) (path : List Nat) : ∀ m : AMatch, ∀ τ ∈ tysMatch false m,
    τ ∈ NTys (nodesMatch C path m)
  | .mk (.mk p e) rest, τ, h => by
    simp only [tysMatch, tysMRule, List.mem_append] at h
    rcases h with (h | h) | h
    · close_nodes tysPat_nodes C.U (path ++ [0]) p τ h
    · close_nodes tysExp_nodes (C.plusVE p.ve) (path ++ [1]) e τ h
    · close_nodes tysMatchOpt_nodes C (path ++ [2]) rest τ h
theorem tysMatchOpt_nodes (C : Ctx) (path : List Nat) : ∀ m : Option AMatch, ∀ τ ∈ tysMatchOpt false m,
    τ ∈ NTys (nodesMatchOpt C path m)
  | none, τ, h => by simp [tysMatchOpt] at h
  | some m, τ, h => by simp only [tysMatchOpt] at h; simp only [nodesMatchOpt]; exact tysMatch_nodes C path m τ h
theorem tysDec_nodes (C : Ctx) (path : List Nat) : ∀ d : ADec, ∀ τ ∈ tysDec false d, τ ∈ NTys (nodesDec C path d)
  | .val VE vb, τ, h => by
    simp only [tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h
    close_nodes tysValBind_nodes (C.plusVE VE) (path ++ [0]) vb τ h
theorem tysValBind_nodes (C : Ctx) (path : List Nat) : ∀ vb : AValBind, ∀ τ ∈ tysValBind false vb,
    τ ∈ NTys (nodesValBind C path vb)
  | .var x ann τ0 e rest, τ, h => by
    simp only [tysValBind, List.cons_append, annMark, List.nil_append, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · close_head
    · close_nodes tysExp_nodes (C.plusU (annU ann)) (path ++ [0]) e τ h
    · close_nodes tysValBindOpt_nodes C (path ++ [1]) rest τ h
  | .pat p e, τ, h => by
    simp only [tysValBind, List.mem_append] at h
    rcases h with h | h
    · close_nodes tysAtPat_nodes C.U (path ++ [0]) p τ h
    · close_nodes tysExp_nodes C (path ++ [1]) e τ h
theorem tysValBindOpt_nodes (C : Ctx) (path : List Nat) : ∀ vb : Option AValBind, ∀ τ ∈ tysValBindOpt false vb,
    τ ∈ NTys (nodesValBindOpt C path vb)
  | none, τ, h => by simp [tysValBindOpt] at h
  | some vb, τ, h => by
    simp only [tysValBindOpt] at h; simp only [nodesValBindOpt]; exact tysValBind_nodes C path vb τ h
end

theorem nb_of_noFreeBnd {C0 : Ctx} {a : AExp} (h : NoFreeBndExp C0 a) : NB (tysExp false a) := by
  intro τ hτ v hv
  have := tysExp_nodes C0 [] a τ hτ
  simp only [NTys, List.mem_flatMap] at this
  obtain ⟨n, hn, hτn⟩ := this
  exact h n hn τ hτn v hv

/-! ## The root (L12) -/

theorem root_pre (C0 : Ctx) (hC : RootOK C0) :
    Pre (freshAbove C0) C0 C0 idS ⟨[], freshAbove C0⟩ :=
  ⟨⟨Nat.le_refl _, goodC_nil _ (fun _ h => nomatch h), fun _ h => by cases h⟩, root_ctxW hC,
    root_rel (fun _ _ => rfl), fun _ _ => rfl, absorbs_id idS, respC_id⟩

/-- The main induction at the root: W does not fail when a derivation exists, and every
    derivation is an image of W's result. -/
theorem wExp_root {fuel : Nat} {C0 : Ctx} {e : BExp} {a' : AExp} (hC : RootOK C0) (hc : checkExp C0 a' = true)
    (hnb : NoFreeBndExp C0 a') (he : a'.erase = e) :
    OutP (EPost (freshAbove C0) ⟨[], freshAbove C0⟩ idS a')
      (wExp fuel (rigidFrom (freshAbove C0)) C0 e ⟨[], freshAbove C0⟩) :=
  wExp_complete fuel _ e C0 C0 idS _ a' (root_pre C0 hC) hc he (nb_of_noFreeBnd hnb)

/-- Refutation (section 7): if W fails, no derivation without free `bnd` variables exists. -/
theorem wRefutation : WRefutation := by
  rintro fuel C0 e hC hf ⟨a', hc, hnb, he⟩
  have h := wExp_root (fuel := fuel) hC hc hnb he
  unfold inferExpW at hf
  simp only at hf
  split at hf
  · split at hf <;> cases hf
  · rename_i hw; rw [hw] at h; exact h
  · cases hf
  · cases hf

/-- The first half of completeness: W does not fail, for any fuel. -/
theorem inferExpW_ne_fail {fuel : Nat} {C0 : Ctx} {e : BExp} (hC : RootOK C0)
    (h : ∃ a', checkExp C0 a' = true ∧ NoFreeBndExp C0 a' ∧ a'.erase = e) : inferExpW fuel C0 e ≠ .fail :=
  fun hf => wRefutation fuel C0 e hC hf h

/-- L12: every derivation (without free `bnd` variables) is the image of W's result under a
    substitution fixing every variable of the root context, with the instance lists left out. -/
theorem inferExpW_instance {fuel : Nat} {C0 : Ctx} {e : BExp} {a : AExp} (hC : RootOK C0)
    (h : inferExpW fuel C0 e = .ok a) :
    ∀ a', checkExp C0 a' = true → NoFreeBndExp C0 a' → a'.erase = e →
      ∃ T : FSub, FixesR (rigidFrom (freshAbove C0)) T ∧ stripExp (sbExp T a) = stripExp a' := by
  intro a' hc hnb he
  have hw := wExp_root (fuel := fuel) hC hc hnb he
  unfold inferExpW at h
  simp only at h
  split at h
  · rename_i τ ar st hok
    split at h
    · cases h
      rw [hok] at hw
      obtain ⟨-, -, -, -, T, hF, -, hs⟩ := hw
      refine ⟨T, hF.fix, ?_⟩
      rw [sbExp_sb, comp_of_absorbs hF.abs]; exact hs
    · cases h
  · cases h
  · cases h
  · cases h

end StandardElm.Stat.Complete
