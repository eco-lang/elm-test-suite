/-
  A Standard Definition of Elm? Mechanisation: principality of W for fragment F_c (plan step 11,
  milestone (b), section 7 and L12): `wPrincipality : WPrincipality`.

  From L12 (`inferExpW_instance`, WTheorems.lean) every derivation `a'` without free `bnd`
  variables is `T a` with the instance lists left out, for a `T` fixing the root context's
  variables, moving only variables of class any (`Found.cls`). The nodes of `a` and of `T a`
  correspond one to one, in order (`nodesExp_rel`, WNodeRelExp.lean). Here:

  * the paths of the nodes of a phrase are distinct (`nodesExp_pd`), so a node of `a'` and a node
    of `a` with the same path are corresponding nodes (`f2_pick`);
  * the instance substitution of sec:static-core-principal is `T` restricted to the type variables
    at the nodes of `a` (`mkP`), a finite substitution of step 9 (`ofBnd`): it respects classes
    (it moves only variables of class any), moves no variable of the root context, is defined
    everywhere, and maps each node of `a` to the corresponding node of `a'` (`instanceNodes_of_F2`).

  Since step 9's occurrence nodes no longer carry the instance list, the nodes of a phrase are
  those of the phrase with its instance lists left out (`nodesExp_strip`), so `InstanceOfB` is
  step 9's `InstanceOf` (`instanceOfB_iff`), and W's result is principal in step 9's sense among
  the derivations without free `bnd` variables (`inferExpW_principal`).
-/
import StandardElmMech.Stat.Complete.WNodeRelExp

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Erasure ignores the instance lists -/

mutual
theorem stripAtPat_erase : ∀ p : AAtPat, (stripAtPat p).erase = p.erase
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit | .record _ _ => rfl
  | .tuple p1 p2 p3 => by
    simp only [stripAtPat, AAtPat.erase, stripPat_erase p1, stripPat_erase p2, stripPatOpt_erase p3]
  | .paren p => by simp only [stripAtPat, AAtPat.erase, stripPat_erase p]
theorem stripPat_erase : ∀ p : APat, (stripPat p).erase = p.erase
  | .atpat a => by simp only [stripPat, APat.erase, stripAtPat_erase a]
  | .con _ _ args _ => by simp only [stripPat, APat.erase, stripAtPats_erase args]
  | .cons p1 p2 => by simp only [stripPat, APat.erase, stripPat_erase p1, stripPat_erase p2]
  | .as p _ => by simp only [stripPat, APat.erase, stripPat_erase p]
theorem stripPatOpt_erase : ∀ p : Option APat, APat.eraseOpt (stripPatOpt p) = APat.eraseOpt p
  | none => rfl
  | some p => by simp only [stripPatOpt, APat.eraseOpt, stripPat_erase p]
theorem stripAtPats_erase : ∀ l : List AAtPat, AAtPat.eraseList (stripAtPats l) = AAtPat.eraseList l
  | [] => rfl
  | a :: as => by simp only [stripAtPats, AAtPat.eraseList, stripAtPat_erase a, stripAtPats_erase as]
end

mutual
theorem stripAtExp_erase : ∀ a : AAtExp, (stripAtExp a).erase = a.erase
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [stripAtExp, AAtExp.erase, stripExp_erase e1, stripExp_erase e2, stripExpOpt_erase e3]
  | .record r => by simp only [stripAtExp, AAtExp.erase, stripExpRowOpt_erase r]
  | .update _ _ _ r => by simp only [stripAtExp, AAtExp.erase, stripExpRow_erase r]
  | .letE d e => by simp only [stripAtExp, AAtExp.erase, stripDec_erase d, stripExp_erase e]
  | .paren e => by simp only [stripAtExp, AAtExp.erase, stripExp_erase e]
theorem stripExpRow_erase : ∀ r : AExpRow, (stripExpRow r).erase = r.erase
  | .field _ e rest => by simp only [stripExpRow, AExpRow.erase, stripExp_erase e, stripExpRowOpt_erase rest]
theorem stripExpRowOpt_erase : ∀ r : Option AExpRow, AExpRow.eraseOpt (stripExpRowOpt r) = AExpRow.eraseOpt r
  | none => rfl
  | some r => by simp only [stripExpRowOpt, AExpRow.eraseOpt, stripExpRow_erase r]
theorem stripExp_erase : ∀ e : AExp, (stripExp e).erase = e.erase
  | .atexp a => by simp only [stripExp, AExp.erase, stripAtExp_erase a]
  | .app e a => by simp only [stripExp, AExp.erase, stripExp_erase e, stripAtExp_erase a]
  | .lam p e => by simp only [stripExp, AExp.erase, stripAtPat_erase p, stripExp_erase e]
  | .caseE e m => by simp only [stripExp, AExp.erase, stripExp_erase e, stripMatch_erase m]
theorem stripExpOpt_erase : ∀ e : Option AExp, AExp.eraseOpt (stripExpOpt e) = AExp.eraseOpt e
  | none => rfl
  | some e => by simp only [stripExpOpt, AExp.eraseOpt, stripExp_erase e]
theorem stripMatch_erase : ∀ m : AMatch, (stripMatch m).erase = m.erase
  | .mk mr rest => by simp only [stripMatch, AMatch.erase, stripMRule_erase mr, stripMatchOpt_erase rest]
theorem stripMatchOpt_erase : ∀ m : Option AMatch, AMatch.eraseOpt (stripMatchOpt m) = AMatch.eraseOpt m
  | none => rfl
  | some m => by simp only [stripMatchOpt, AMatch.eraseOpt, stripMatch_erase m]
theorem stripMRule_erase : ∀ mr : AMRule, (stripMRule mr).erase = mr.erase
  | .mk p e => by simp only [stripMRule, AMRule.erase, stripPat_erase p, stripExp_erase e]
theorem stripDec_erase : ∀ d : ADec, (stripDec d).erase = d.erase
  | .val _ vb => by simp only [stripDec, ADec.erase, stripValBind_erase vb]
theorem stripValBind_erase : ∀ vb : AValBind, (stripValBind vb).erase = vb.erase
  | .var _ _ _ e rest => by simp only [stripValBind, AValBind.erase, stripExp_erase e, stripValBindOpt_erase rest]
  | .pat p e => by simp only [stripValBind, AValBind.erase, stripAtPat_erase p, stripExp_erase e]
theorem stripValBindOpt_erase : ∀ vb : Option AValBind, AValBind.eraseOpt (stripValBindOpt vb) = AValBind.eraseOpt vb
  | none => rfl
  | some vb => by simp only [stripValBindOpt, AValBind.eraseOpt, stripValBind_erase vb]
end

/-! ## The paths of the nodes are distinct -/

/-- The paths of the nodes are pairwise distinct. -/
def PD (l : List Node) : Prop := (l.map Node.path).Nodup

/-- The nodes are under `p`, with distinct paths. -/
def PGood (p : List Nat) (l : List Node) : Prop := PD l ∧ ∀ n ∈ l, ∃ s, n.path = p ++ s

/-- The branch below `p` a node is in (`none` for the node at `p`). -/
def pbr (p : List Nat) (n : Node) : Option Nat := (n.path.drop p.length).head?

/-- A node and its first children, below branch `k`. -/
def PG (p : List Nat) (k : Nat) (l : List Node) : Prop := PGood p l ∧ ∀ n ∈ l, ∀ i, pbr p n = some i → i < k

theorem pd_append {l1 l2 : List Node} (h1 : PD l1) (h2 : PD l2)
    (h : ∀ x ∈ l1, ∀ y ∈ l2, x.path ≠ y.path) : PD (l1 ++ l2) := by
  unfold PD at *
  rw [List.map_append, List.nodup_append]
  refine ⟨h1, h2, ?_⟩
  intro a ha b hb e
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  exact h x hx y hy e

theorem pbr_child {p : List Nat} {k : Nat} {n : Node} (h : ∃ s, n.path = p ++ [k] ++ s) : pbr p n = some k := by
  obtain ⟨s, hs⟩ := h
  simp [pbr, hs]

theorem pg_head {p : List Nat} {n : Node} (h : n.path = p) : PG p 0 [n] := by
  refine ⟨⟨by simp [PD], fun m hm => ⟨[], by simp at hm; subst hm; simp [h]⟩⟩, fun m hm i hi => ?_⟩
  simp at hm; subst hm
  simp [pbr, h] at hi

theorem pg_step {p : List Nat} {k : Nat} {L C : List Node} (hL : PG p k L) (hC : PGood (p ++ [k]) C) :
    PG p (k + 1) (L ++ C) := by
  obtain ⟨⟨hpd, hu⟩, hb⟩ := hL
  obtain ⟨hpd', hu'⟩ := hC
  refine ⟨⟨pd_append hpd hpd' fun x hx y hy e => ?_, fun n hn => ?_⟩, fun n hn i hi => ?_⟩
  · have h1 : pbr p y = some k := pbr_child (hu' y hy)
    have h2 : pbr p x = pbr p y := by simp only [pbr, e]
    rw [h1] at h2
    exact absurd (hb x hx k h2) (Nat.lt_irrefl k)
  · rcases List.mem_append.mp hn with hn | hn
    · exact hu n hn
    · obtain ⟨s, hs⟩ := hu' n hn; exact ⟨[k] ++ s, by simp [hs]⟩
  · rcases List.mem_append.mp hn with hn | hn
    · exact Nat.lt_succ_of_lt (hb n hn i hi)
    · rw [pbr_child (hu' n hn)] at hi; cases hi; exact Nat.lt_succ_self _

theorem PG.good {p : List Nat} {k : Nat} {l : List Node} (h : PG p k l) : PGood p l := h.1

theorem pgood_nil (p : List Nat) : PGood p [] := ⟨by simp [PD], fun _ h => by cases h⟩

/-- The nodes of the arguments of a constructor pattern, from branch `i`. -/
def PA (p : List Nat) (i : Nat) (l : List Node) : Prop :=
  PGood p l ∧ ∀ n ∈ l, ∃ j, pbr p n = some j ∧ i ≤ j

theorem pa_cons {p : List Nat} {i : Nat} {A B : List Node} (hA : PGood (p ++ [i]) A) (hB : PA p (i + 1) B) :
    PA p i (A ++ B) := by
  obtain ⟨hpd, hu⟩ := hA
  obtain ⟨⟨hpd', hu'⟩, hb⟩ := hB
  refine ⟨⟨pd_append hpd hpd' fun x hx y hy e => ?_, fun n hn => ?_⟩, fun n hn => ?_⟩
  · have h1 : pbr p x = some i := pbr_child (hu x hx)
    obtain ⟨j, hj, hij⟩ := hb y hy
    have h2 : pbr p x = pbr p y := by simp only [pbr, e]
    rw [h1, hj] at h2; cases h2; omega
  · rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨s, hs⟩ := hu n hn; exact ⟨[i] ++ s, by simp [hs]⟩
    · exact hu' n hn
  · rcases List.mem_append.mp hn with hn | hn
    · exact ⟨i, pbr_child (hu n hn), Nat.le_refl _⟩
    · obtain ⟨j, hj, hij⟩ := hb n hn; exact ⟨j, hj, by omega⟩

theorem pa_nil (p : List Nat) (i : Nat) : PA p i [] := ⟨pgood_nil p, fun _ h => by cases h⟩

theorem pg_args {p : List Nat} {L B : List Node} (hL : PG p 0 L) (hB : PA p 0 B) : PGood p (L ++ B) := by
  obtain ⟨⟨hpd, hu⟩, hb⟩ := hL
  obtain ⟨⟨hpd', hu'⟩, hb'⟩ := hB
  refine ⟨pd_append hpd hpd' fun x hx y hy e => ?_, fun n hn => ?_⟩
  · obtain ⟨j, hj, -⟩ := hb' y hy
    have h2 : pbr p x = pbr p y := by simp only [pbr, e]
    rw [hj] at h2
    exact absurd (hb x hx j h2) (Nat.not_lt_zero _)
  · rcases List.mem_append.mp hn with hn | hn
    · exact hu n hn
    · exact hu' n hn

mutual
theorem nodesAtPat_pd (U : List BVar) : ∀ (x : AAtPat) (path : List Nat), PGood path (nodesAtPat U path x)
  | .wild _, _ | .scon _ _, _ | .var _ _, _ | .con _ _ _, _ | .nil _, _ | .unit, _ => (pg_head rfl).good
  | .tuple p1 p2 p3, path =>
    (pg_step (pg_step (pg_step (pg_head rfl) (nodesPat_pd U p1 _)) (nodesPat_pd U p2 _)) (nodesPatOpt_pd U p3 _)).good
  | .record r _, path => (pg_step (pg_head rfl) (nodesPatRowOpt_pd U r _)).good
  | .paren p, path => (pg_step (pg_head rfl) (nodesPat_pd U p _)).good
theorem nodesPatRowOpt_pd (U : List BVar) : ∀ (r : Option APatRow) (path : List Nat), PGood path (nodesPatRowOpt U path r)
  | none, path => pgood_nil path
  | some (.field _ _ rest), path => (pg_step (pg_head rfl) (nodesPatRowOpt_pd U rest _)).good
theorem nodesPat_pd (U : List BVar) : ∀ (x : APat) (path : List Nat), PGood path (nodesPat U path x)
  | .atpat a, path => (pg_step (pg_head rfl) (nodesAtPat_pd U a _)).good
  | .con _ _ args _, path => pg_args (pg_head rfl) (nodesAtPats_pd U args path 0)
  | .cons p1 p2, path => (pg_step (pg_step (pg_head rfl) (nodesPat_pd U p1 _)) (nodesPat_pd U p2 _)).good
  | .as p _, path => (pg_step (pg_head rfl) (nodesPat_pd U p _)).good
theorem nodesPatOpt_pd (U : List BVar) : ∀ (x : Option APat) (path : List Nat), PGood path (nodesPatOpt U path x)
  | none, path => pgood_nil path
  | some p, path => nodesPat_pd U p path
theorem nodesAtPats_pd (U : List BVar) : ∀ (l : List AAtPat) (path : List Nat) (i : Nat), PA path i (nodesAtPats U path i l)
  | [], path, i => pa_nil path i
  | a :: as, path, i => pa_cons (nodesAtPat_pd U a _) (nodesAtPats_pd U as path (i + 1))
end

mutual
theorem nodesAtExp_pd : ∀ (C : Ctx) (x : AAtExp) (path : List Nat), PGood path (nodesAtExp C path x)
  | _, .scon _ _, _ | _, .var _ _ _, _ | _, .con _ _ _, _ | _, .op _ _ _, _ | _, .unit, _ | _, .nil _, _ =>
    (pg_head rfl).good
  | C, .tuple e1 e2 e3, _ =>
    (pg_step (pg_step (pg_step (pg_head rfl) (nodesExp_pd C e1 _)) (nodesExp_pd C e2 _)) (nodesExpOpt_pd C e3 _)).good
  | C, .record r, _ => (pg_step (pg_head rfl) (nodesExpRowOpt_pd C r _)).good
  | C, .update _ _ _ r, _ => (pg_step (pg_head rfl) (nodesExpRow_pd C r _)).good
  | C, .letE d e, _ => (pg_step (pg_step (pg_head rfl) (nodesDec_pd C d _)) (nodesExp_pd _ e _)).good
  | C, .paren e, _ => (pg_step (pg_head rfl) (nodesExp_pd C e _)).good
theorem nodesExpRow_pd : ∀ (C : Ctx) (r : AExpRow) (path : List Nat), PGood path (nodesExpRow C path r)
  | C, .field _ e rest, _ => (pg_step (pg_step (pg_head rfl) (nodesExp_pd C e _)) (nodesExpRowOpt_pd C rest _)).good
theorem nodesExpRowOpt_pd : ∀ (C : Ctx) (r : Option AExpRow) (path : List Nat), PGood path (nodesExpRowOpt C path r)
  | _, none, path => pgood_nil path
  | C, some r, path => nodesExpRow_pd C r path
theorem nodesExp_pd : ∀ (C : Ctx) (x : AExp) (path : List Nat), PGood path (nodesExp C path x)
  | C, .atexp a, _ => (pg_step (pg_head rfl) (nodesAtExp_pd C a _)).good
  | C, .app e a, _ => (pg_step (pg_step (pg_head rfl) (nodesExp_pd C e _)) (nodesAtExp_pd C a _)).good
  | C, .lam p e, _ => (pg_step (pg_step (pg_head rfl) (nodesAtPat_pd C.U p _)) (nodesExp_pd _ e _)).good
  | C, .caseE e m, _ => (pg_step (pg_step (pg_head rfl) (nodesExp_pd C e _)) (nodesMatch_pd C m _)).good
theorem nodesExpOpt_pd : ∀ (C : Ctx) (x : Option AExp) (path : List Nat), PGood path (nodesExpOpt C path x)
  | _, none, path => pgood_nil path
  | C, some e, path => nodesExp_pd C e path
theorem nodesMatch_pd : ∀ (C : Ctx) (m : AMatch) (path : List Nat), PGood path (nodesMatch C path m)
  | C, .mk (.mk p e) rest, _ =>
    (pg_step (pg_step (pg_step (pg_head rfl) (nodesPat_pd C.U p _)) (nodesExp_pd _ e _)) (nodesMatchOpt_pd C rest _)).good
theorem nodesMatchOpt_pd : ∀ (C : Ctx) (m : Option AMatch) (path : List Nat), PGood path (nodesMatchOpt C path m)
  | _, none, path => pgood_nil path
  | C, some m, path => nodesMatch_pd C m path
theorem nodesDec_pd : ∀ (C : Ctx) (d : ADec) (path : List Nat), PGood path (nodesDec C path d)
  | _, .val _ vb, _ => (pg_step (pg_head rfl) (nodesValBind_pd _ vb _)).good
theorem nodesValBind_pd : ∀ (C : Ctx) (vb : AValBind) (path : List Nat), PGood path (nodesValBind C path vb)
  | C, .var _ _ _ e rest, _ =>
    (pg_step (pg_step (pg_head rfl) (nodesExp_pd _ e _)) (nodesValBindOpt_pd C rest _)).good
  | C, .pat p e, _ => (pg_step (pg_step (pg_head rfl) (nodesAtPat_pd C.U p _)) (nodesExp_pd C e _)).good
theorem nodesValBindOpt_pd : ∀ (C : Ctx) (vb : Option AValBind) (path : List Nat), PGood path (nodesValBindOpt C path vb)
  | _, none, path => pgood_nil path
  | C, some vb, path => nodesValBind_pd C vb path
end

/-! ## Corresponding nodes -/

theorem f2_mem_right {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} (h : F2 R l l') :
    ∀ y ∈ l', ∃ x ∈ l, R x y := by
  induction h with
  | nil => intro y hy; cases hy
  | cons hab _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, .head _, hab⟩
    · obtain ⟨x, hx, hr⟩ := ih y hy; exact ⟨x, .tail _ hx, hr⟩

/-- With distinct paths, nodes of the two lists with the same path are corresponding nodes. -/
theorem f2_pick {T : FSub} {U0 : List BVar} {l l' : List Node} (h : F2 (NRel T U0) l l') (hpd : PD l) :
    ∀ n ∈ l, ∀ n' ∈ l', n.path = n'.path → NRel T U0 n n' := by
  induction h with
  | nil => intro n hn; cases hn
  | @cons a b l l' hab hrest ih =>
    unfold PD at hpd
    simp only [List.map_cons, List.nodup_cons] at hpd
    intro n hn n' hn' e
    rcases List.mem_cons.mp hn with rfl | hn <;> rcases List.mem_cons.mp hn' with rfl | hn'
    · exact hab
    · obtain ⟨m, hm, hr⟩ := f2_mem_right hrest n' hn'
      exact absurd (List.mem_map.mpr ⟨m, hm, (e.trans hr.2.1).symm⟩) hpd.1
    · exact absurd (List.mem_map.mpr ⟨n, hn, e.trans hab.2.1⟩) hpd.1
    · exact ih hpd.2 n hn n' hn' e

/-! ## The instance substitution -/

/-- `T` restricted to the variables of the list it moves. -/
def mkP (T : FSub) : List TyVar → Bnd
  | [] => []
  | a :: L => if T a = .var a then mkP T L else (a, T a) :: mkP T L

theorem lk_mkP (T : FSub) (a : TyVar) : ∀ L : List TyVar, lk (mkP T L) a = if a ∈ L then T a else .var a
  | [] => by simp [mkP, lk_nil]
  | b :: L => by
    have ih := lk_mkP T a L
    by_cases hb : T b = .var b
    · simp only [mkP, hb, ite_true, ih, List.mem_cons]
      by_cases hab : a = b
      · subst hab; simp [hb]
      · simp [hab]
    · simp only [mkP, hb, ite_false, lk_cons, ih, List.mem_cons]
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]

theorem mem_mkP {T : FSub} : ∀ {L : List TyVar} {p : TyVar × Ty}, p ∈ mkP T L → T p.1 ≠ .var p.1 ∧ p.2 = T p.1
  | [], _, h => by cases h
  | b :: L, p, h => by
    simp only [mkP] at h
    split at h
    · exact mem_mkP h
    · rename_i hb
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨hb, rfl⟩
      · exact mem_mkP h

theorem lk_mkP_fix {T : FSub} {L : List TyVar} {a : TyVar} (h : T a = .var a) : lk (mkP T L) a = .var a := by
  rw [lk_mkP]; split <;> simp [h]

theorem mapM_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.mapM_cons, h x (.head _), mapM_some f g l (fun y hy => h y (.tail _ hy))]
    rfl

theorem applyVar_mkP {T : FSub} {L : List TyVar} {v : BVar} (h : ∀ a, v = .ty a → T a = .var a) :
    (ofBnd (mkP T L)).applyVar v = some v := by
  cases v with
  | ty a => simp [Subst.applyVar, apply_ofBnd, sb, lk_mkP_fix (h a rfl)]
  | row e => simp [Subst.applyVar, apply_ofBnd, sb, sbRow]

/-- The node-wise correspondence `F2 (NRel T U0)` with distinct paths is an instance (step 9's
    `InstanceNodes`), for a `T` that moves only variables of class any and fixes the free
    variables of the root context. -/
theorem instanceNodes_of_F2 {T : FSub} {U0 A0 : List BVar} {ns ns' : List Node}
    (hF : F2 (NRel T U0) ns ns') (hpd : PD ns)
    (hcls : RespC T) (hA0 : ∀ a, BVar.ty a ∈ A0 → T a = .var a)
    (hU0 : ∀ a, BVar.ty a ∈ U0 → T a = .var a) : InstanceNodes A0 ns' ns := by
  let L : List TyVar := (ns.flatMap fun n => n.tys ++ n.schemes.map (·.body)).flatMap tvs
  have hagree : ∀ n ∈ ns, ∀ τ, (τ ∈ n.tys ∨ τ ∈ n.schemes.map (·.body)) → sb (lk (mkP T L)) τ = sb T τ := by
    intro n hn τ hτ
    apply sb_congr
    intro a ha
    rw [lk_mkP]
    split
    · rfl
    · rename_i hm
      exact absurd (List.mem_flatMap.mpr ⟨τ, List.mem_flatMap.mpr ⟨n, hn, List.mem_append.mpr hτ⟩, mem_tvs.mpr ha⟩) hm
  refine ⟨ofBnd (mkP T L), fun p hp => ?_, fun v hv hvA => ?_, fun τ _ => ?_, fun n hn n' hn' hp => ?_⟩
  · obtain ⟨h1, h2⟩ := mem_mkP hp
    rw [h2]; exact hcls _
  · simp only [Subst.dom, ofBnd, List.map_nil, List.append_nil, List.mem_map] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact (mem_mkP hp).1 (hA0 _ hvA)
  · rw [apply_ofBnd]; rfl
  · obtain ⟨hU, -, hU', htys, hlen, hgen⟩ := f2_pick hF hpd n hn n' hn' hp
    refine ⟨⟨n.U, ?_, fun x => by rw [hU']⟩, ?_, hlen.symm, fun i hi hi' t hg => ?_⟩
    · have := mapM_some (ofBnd (mkP T L)).applyVar id n.U fun v hv =>
        applyVar_mkP fun a e => hU0 a (by rw [← hU, ← e]; exact hv)
      rwa [List.map_id] at this
    · rw [htys]
      exact mapM_some _ _ n.tys fun τ hτ => by rw [apply_ofBnd, hagree n hn τ (.inl hτ)]
    · refine ⟨⟨n.schemes[i].bound, sb T n.schemes[i].body⟩, ?_, hgen i hi hi' t hg⟩
      simp only [Subst.applyScheme, apply_ofBnd, Option.map_some]
      rw [hagree n hn _ (.inr (List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩))]

/-! ## Principality (section 7, L12) -/

/-- Principality of W for F_c: what W returns is principal among the derivations without free
    `bnd` variables, with the instance relation of sec:static-core-principal (instance lists left
    out). -/
theorem wPrincipality : WPrincipality := by
  intro fuel C0 e a hC h
  obtain ⟨hc, he⟩ := inferExpW_sound h
  refine ⟨hc, fun a' hc' hnb he' => ?_⟩
  have hw := wExp_root (fuel := fuel) hC hc' hnb (he'.trans he)
  unfold inferExpW at h
  simp only at h
  split at h
  · rename_i τ ar st hok
    split at h
    · cases h
      rw [hok] at hw
      obtain ⟨-, hinv, -, hokA, T, hF, -, hs⟩ := hw
      have hTa : sbExp T (sbExp (lk st.θ) ar) = sbExp T ar := by rw [sbExp_sb, comp_of_absorbs hF.abs]
      have hcls : RespC T := hF.resp respC_id
      have hrel : CtxRel (FtvRel T) (rigidFrom (freshAbove C0)) C0 C0 :=
        (root_rel hF.fix).mono fun _ _ _ _ _ h => h.1
      have hok' : OkA st.n (tysExp true (sbExp (lk st.θ) ar)) := by
        rw [tysExp_sb]
        intro τ hτ
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hτ
        exact hinv.ok.okT (hokA x hx)
      have hnbm : NBm T (tysExp false (sbExp (lk st.θ) ar)) := by
        intro τ hτ v hv
        have h1 : sb T τ ∈ tysExp false (sbExp T (sbExp (lk st.θ) ar)) := by
          rw [tysExp_sb]; exact List.mem_map_of_mem hτ
        rw [← tysExp_strip, hTa, hs, tysExp_strip] at h1
        exact nb_of_noFreeBnd hnb _ h1 v hv
      have hF2 := nodesExp_rel T (freshAbove C0) st.n C0.U hF.fix hcls _ C0 C0 [] rfl hc hrel hok' hnbm
      rw [hTa, hs] at hF2
      refine ⟨by rw [stripExp_erase, stripExp_erase]; exact he', instanceNodes_of_F2 hF2
        (nodesExp_pd C0 _ []).1 hcls (fun x hx => hF.fix x (rigid_of_old (old_of_root hx)))
        (fun x hx => hF.fix x (rigid_of_old (old_of_root (List.mem_append_right _ hx))))⟩
    · cases h
  · cases h
  · cases h
  · cases h

/-! ## The nodes of a phrase are those of the phrase without its instance lists -/

theorem stripDec_result (C : Ctx) : ∀ d : ADec, (stripDec d).result C = d.result C
  | .val _ _ => rfl

mutual
theorem nodesAtPat_strip (U : List BVar) : ∀ (x : AAtPat) (path : List Nat),
    nodesAtPat U path (stripAtPat x) = nodesAtPat U path x
  | .wild _, _ | .scon _ _, _ | .var _ _, _ | .con _ _ _, _ | .nil _, _ | .unit, _ | .record _ _, _ => rfl
  | .tuple p1 p2 p3, path => by
    have hv := stripAtPat_ve (.tuple p1 p2 p3)
    simp only [stripAtPat] at hv
    simp only [stripAtPat, nodesAtPat, hv, stripPat_ty, stripPatOpt_ty, nodesPat_strip, nodesPatOpt_strip]
  | .paren p, path => by
    simp only [stripAtPat, nodesAtPat, stripPat_ty, stripPat_ve, nodesPat_strip]
theorem nodesPat_strip (U : List BVar) : ∀ (x : APat) (path : List Nat),
    nodesPat U path (stripPat x) = nodesPat U path x
  | .atpat a, path => by
    simp only [stripPat, nodesPat, stripAtPat_ty, stripAtPat_ve, nodesAtPat_strip]
  | .con lc inst args τ, path => by
    have hv := stripPat_ve (.con lc inst args τ)
    simp only [stripPat] at hv
    simp only [stripPat, nodesPat, hv, nodesAtPats_strip]
  | .cons p1 p2, path => by
    have hv := stripPat_ve (.cons p1 p2)
    simp only [stripPat] at hv
    simp only [stripPat, nodesPat, hv, stripPat_ty, nodesPat_strip]
  | .as p x, path => by
    have hv := stripPat_ve (.as p x)
    simp only [stripPat] at hv
    simp only [stripPat, nodesPat, hv, stripPat_ty, nodesPat_strip]
theorem nodesPatOpt_strip (U : List BVar) : ∀ (x : Option APat) (path : List Nat),
    nodesPatOpt U path (stripPatOpt x) = nodesPatOpt U path x
  | none, _ => rfl
  | some p, path => by simp only [stripPatOpt, nodesPatOpt, nodesPat_strip]
theorem nodesAtPats_strip (U : List BVar) : ∀ (l : List AAtPat) (path : List Nat) (i : Nat),
    nodesAtPats U path i (stripAtPats l) = nodesAtPats U path i l
  | [], _, _ => rfl
  | a :: as, path, i => by simp only [stripAtPats, nodesAtPats, nodesAtPat_strip, nodesAtPats_strip]
end

mutual
theorem nodesAtExp_strip : ∀ (C : Ctx) (x : AAtExp) (path : List Nat), nodesAtExp C path (stripAtExp x) = nodesAtExp C path x
  | _, .scon _ _, _ | _, .var _ _ _, _ | _, .con _ _ _, _ | _, .op _ _ _, _ | _, .unit, _ | _, .nil _, _ => rfl
  | C, .tuple e1 e2 e3, path => by
    have ht := stripAtExp_ty (.tuple e1 e2 e3)
    simp only [stripAtExp] at ht
    simp only [stripAtExp, nodesAtExp, ht, nodesExp_strip, nodesExpOpt_strip]
  | C, .record r, path => by
    have ht := stripAtExp_ty (.record r)
    simp only [stripAtExp] at ht
    simp only [stripAtExp, nodesAtExp, ht, nodesExpRowOpt_strip]
  | C, .update x inst τ r, path => by
    simp only [stripAtExp, nodesAtExp, nodesExpRow_strip]
  | C, .letE d e, path => by
    simp only [stripAtExp, nodesAtExp, stripExp_ty, stripDec_result, nodesDec_strip, nodesExp_strip]
  | C, .paren e, path => by
    simp only [stripAtExp, nodesAtExp, stripExp_ty, nodesExp_strip]
theorem nodesExpRow_strip : ∀ (C : Ctx) (r : AExpRow) (path : List Nat), nodesExpRow C path (stripExpRow r) = nodesExpRow C path r
  | C, .field l e rest, path => by
    have ht := stripExpRow_row (.field l e rest)
    simp only [stripExpRow] at ht
    simp only [stripExpRow, nodesExpRow, ht, nodesExp_strip, nodesExpRowOpt_strip]
theorem nodesExpRowOpt_strip : ∀ (C : Ctx) (r : Option AExpRow) (path : List Nat),
    nodesExpRowOpt C path (stripExpRowOpt r) = nodesExpRowOpt C path r
  | _, none, _ => rfl
  | C, some r, path => by simp only [stripExpRowOpt, nodesExpRowOpt, nodesExpRow_strip]
theorem nodesExp_strip : ∀ (C : Ctx) (x : AExp) (path : List Nat), nodesExp C path (stripExp x) = nodesExp C path x
  | C, .atexp a, path => by
    simp only [stripExp, nodesExp, stripAtExp_ty, nodesAtExp_strip]
  | C, .app e a, path => by
    have ht := stripExp_ty (.app e a)
    simp only [stripExp] at ht
    simp only [stripExp, nodesExp, ht, nodesExp_strip, nodesAtExp_strip]
  | C, .lam p e, path => by
    have ht := stripExp_ty (.lam p e)
    simp only [stripExp] at ht
    simp only [stripExp, nodesExp, ht, stripAtPat_ve, nodesAtPat_strip, nodesExp_strip]
  | C, .caseE e m, path => by
    have ht := stripExp_ty (.caseE e m)
    simp only [stripExp] at ht
    simp only [stripExp, nodesExp, ht, nodesExp_strip, nodesMatch_strip]
theorem nodesExpOpt_strip : ∀ (C : Ctx) (x : Option AExp) (path : List Nat),
    nodesExpOpt C path (stripExpOpt x) = nodesExpOpt C path x
  | _, none, _ => rfl
  | C, some e, path => by simp only [stripExpOpt, nodesExpOpt, nodesExp_strip]
theorem nodesMatch_strip : ∀ (C : Ctx) (m : AMatch) (path : List Nat), nodesMatch C path (stripMatch m) = nodesMatch C path m
  | C, .mk (.mk p e) rest, path => by
    have ht := stripMRule_ty (.mk p e)
    simp only [stripMRule] at ht
    simp only [stripMatch, stripMRule, nodesMatch, ht, stripPat_ve, nodesPat_strip, nodesExp_strip, nodesMatchOpt_strip]
theorem nodesMatchOpt_strip : ∀ (C : Ctx) (m : Option AMatch) (path : List Nat),
    nodesMatchOpt C path (stripMatchOpt m) = nodesMatchOpt C path m
  | _, none, _ => rfl
  | C, some m, path => by simp only [stripMatchOpt, nodesMatchOpt, nodesMatch_strip]
theorem nodesDec_strip : ∀ (C : Ctx) (d : ADec) (path : List Nat), nodesDec C path (stripDec d) = nodesDec C path d
  | C, .val VE vb, path => by simp only [stripDec, nodesDec, nodesValBind_strip]
theorem nodesValBind_strip : ∀ (C : Ctx) (vb : AValBind) (path : List Nat),
    nodesValBind C path (stripValBind vb) = nodesValBind C path vb
  | C, .var x ann τ e rest, path => by
    have hv := stripValBind_ve (.var x ann τ e rest)
    simp only [stripValBind] at hv
    simp only [stripValBind, nodesValBind, hv, nodesExp_strip, nodesValBindOpt_strip]
  | C, .pat p e, path => by
    simp only [stripValBind, nodesValBind, stripAtPat_ty, stripAtPat_ve, nodesAtPat_strip, nodesExp_strip]
theorem nodesValBindOpt_strip : ∀ (C : Ctx) (vb : Option AValBind) (path : List Nat),
    nodesValBindOpt C path (stripValBindOpt vb) = nodesValBindOpt C path vb
  | _, none, _ => rfl
  | C, some vb, path => by simp only [stripValBindOpt, nodesValBindOpt, nodesValBind_strip]
end

/-- With step 9's nodes (no instance list at occurrences), the corrected instance relation is
    step 9's `InstanceOf`. -/
theorem instanceOfB_iff {C0 : Ctx} {a' a : AExp} : InstanceOfB C0 a' a ↔ InstanceOf C0 a' a := by
  unfold InstanceOfB InstanceOf
  rw [stripExp_erase, stripExp_erase, nodesExp_strip, nodesExp_strip]

/-- `IsPrincipalB` is step 9's `IsPrincipal` with the derivations compared restricted to those
    without free `bnd` variables. -/
theorem isPrincipalB_iff {C0 : Ctx} {a : AExp} : IsPrincipalB C0 a ↔
    checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true → NoFreeBndExp C0 a' → a'.erase = a.erase →
      InstanceOf C0 a' a := by
  unfold IsPrincipalB
  simp only [instanceOfB_iff]

/-- Section 7's principality of W for F_c, in step 9's terms: W's result is a derivation of the
    phrase, and every derivation of it without free `bnd` variables is an instance of it
    (`InstanceOf`, sec:static-core-principal). -/
theorem inferExpW_principal {fuel : Nat} {C0 : Ctx} {e : StandardElm.Src.BExp} {a : AExp} (hC : RootOK C0)
    (h : inferExpW fuel C0 e = .ok a) :
    a.erase = e ∧ checkExp C0 a = true ∧
      ∀ a', checkExp C0 a' = true → NoFreeBndExp C0 a' → a'.erase = a.erase → InstanceOf C0 a' a :=
  ⟨(inferExpW_sound h).2, isPrincipalB_iff.mp (wPrincipality fuel C0 e a hC h)⟩

end StandardElm.Stat.Complete
