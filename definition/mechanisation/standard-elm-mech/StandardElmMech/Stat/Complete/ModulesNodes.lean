/-
  A Standard Definition of Elm? Mechanisation: the nodes of a module's value declarations against
  the nodes of their nested `let` (milestone (f) of plan step 11, section 9, node correspondence).

  A top-level group's node and the nodes of its bindings are, up to their paths, the `let`'s
  declaration node and the nodes of the same bindings (`nodesTopDec` against `nodesExp` of
  `toExpA`); a path below a node is the node's path followed by the same relative path in both
  (`sh_*`: nodes below a prefix are the nodes below `[]` with the prefix prepended). So when every
  pair of nodes of two nested `let`s at one path is an instance, so is every pair of nodes of the two
  modules' value declarations at one path (`pi_values`).
-/
import StandardElmMech.Stat.Complete.ModulesPorts
import StandardElmMech.Stat.Complete.WPrincipality

namespace StandardElm.Stat.Complete
namespace MW
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Paths -/

/-- A node moved below a prefix. -/
def Node.pre (r : List Nat) (n : Node) : Node := ⟨r ++ n.path, n.U, n.tys, n.schemes⟩

section
variable (U : List BVar) (r : List Nat)

mutual
theorem shAtPat : ∀ (x : AAtPat) (p : List Nat), nodesAtPat U (r ++ p) x = (nodesAtPat U p x).map (Node.pre r)
  | .tuple p1 p2 p3, p => by
    simp only [nodesAtPat, List.map_append, List.append_assoc, shPat p1, shPat p2, shPatOpt p3]; rfl
  | .record row _, p => by
    simp only [nodesAtPat, List.map_append, List.append_assoc, shPatRowOpt row]; rfl
  | .paren q, p => by simp only [nodesAtPat, List.map_append, List.append_assoc, shPat q]; rfl
  | .wild _, _ | .scon _ _, _ | .var _ _, _ | .con _ _ _, _ | .unit, _ | .nil _, _ => rfl
theorem shPatRow : ∀ (x : APatRow) (p : List Nat), nodesPatRow U (r ++ p) x = (nodesPatRow U p x).map (Node.pre r)
  | .field _ _ rest, p => by
    simp only [nodesPatRow, List.map_append, List.append_assoc, shPatRowOpt rest]; rfl
theorem shPatRowOpt : ∀ (x : Option APatRow) (p : List Nat),
    nodesPatRowOpt U (r ++ p) x = (nodesPatRowOpt U p x).map (Node.pre r)
  | none, _ => rfl
  | some x, p => shPatRow x p
theorem shPat : ∀ (x : APat) (p : List Nat), nodesPat U (r ++ p) x = (nodesPat U p x).map (Node.pre r)
  | .atpat a, p => by simp only [nodesPat, List.map_append, List.append_assoc, shAtPat a]; rfl
  | .con _ _ args _, p => by simp only [nodesPat, List.map_append, shAtPats args p 0]; rfl
  | .cons p1 p2, p => by simp only [nodesPat, List.map_append, List.append_assoc, shPat p1, shPat p2]; rfl
  | .as q _, p => by simp only [nodesPat, List.map_append, List.append_assoc, shPat q]; rfl
theorem shPatOpt : ∀ (x : Option APat) (p : List Nat), nodesPatOpt U (r ++ p) x = (nodesPatOpt U p x).map (Node.pre r)
  | none, _ => rfl
  | some x, p => shPat x p
theorem shAtPats : ∀ (l : List AAtPat) (p : List Nat) (i : Nat),
    nodesAtPats U (r ++ p) i l = (nodesAtPats U p i l).map (Node.pre r)
  | [], _, _ => rfl
  | a :: as, p, i => by
    simp only [nodesAtPats, List.map_append, List.append_assoc, shAtPat a, shAtPats as p (i + 1)]
end

end

mutual
theorem shAtExp (r : List Nat) : ∀ (x : AAtExp) (C D : Ctx) (p : List Nat), CEq C D →
    nodesAtExp C (r ++ p) x = (nodesAtExp D p x).map (Node.pre r)
  | .scon _ _, _, _, _, h | .var _ _ _, _, _, _, h | .con _ _ _, _, _, _, h | .op _ _ _, _, _, _, h
  | .unit, _, _, _, h | .nil _, _, _, _, h => by simp only [nodesAtExp, h.U]; rfl
  | .tuple e1 e2 e3, C, D, p, h => by
    simp only [nodesAtExp, List.map_append, List.append_assoc, shExp r e1 C D _ h, shExp r e2 C D _ h,
      shExpOpt r e3 C D _ h, h.U]; rfl
  | .record row, C, D, p, h => by
    simp only [nodesAtExp, List.map_append, List.append_assoc, shExpRowOpt r row C D _ h, h.U]; rfl
  | .update _ _ _ row, C, D, p, h => by
    simp only [nodesAtExp, List.map_append, List.append_assoc, shExpRow r row C D _ h, h.U]; rfl
  | .letE d e, C, D, p, h => by
    have hr : d.result C = d.result D := by cases d with | val VE vb => exact h.closG VE
    simp only [nodesAtExp, List.map_append, List.append_assoc, shDec r d C D _ h, hr,
      shExp r e (C.plusVE (d.result D)) (D.plusVE (d.result D)) _ (h.plusVE _), h.U]; rfl
  | .paren e, C, D, p, h => by
    simp only [nodesAtExp, List.map_append, List.append_assoc, shExp r e C D _ h, h.U]; rfl
theorem shExpRow (r : List Nat) : ∀ (x : AExpRow) (C D : Ctx) (p : List Nat), CEq C D →
    nodesExpRow C (r ++ p) x = (nodesExpRow D p x).map (Node.pre r)
  | .field _ e rest, C, D, p, h => by
    simp only [nodesExpRow, List.map_append, List.append_assoc, shExp r e C D _ h, shExpRowOpt r rest C D _ h, h.U]
    rfl
theorem shExpRowOpt (r : List Nat) : ∀ (x : Option AExpRow) (C D : Ctx) (p : List Nat), CEq C D →
    nodesExpRowOpt C (r ++ p) x = (nodesExpRowOpt D p x).map (Node.pre r)
  | none, _, _, _, _ => rfl
  | some x, C, D, p, h => shExpRow r x C D p h
theorem shExp (r : List Nat) : ∀ (x : AExp) (C D : Ctx) (p : List Nat), CEq C D →
    nodesExp C (r ++ p) x = (nodesExp D p x).map (Node.pre r)
  | .atexp a, C, D, p, h => by
    simp only [nodesExp, List.map_append, List.append_assoc, shAtExp r a C D _ h, h.U]; rfl
  | .app e a, C, D, p, h => by
    simp only [nodesExp, List.map_append, List.append_assoc, shExp r e C D _ h, shAtExp r a C D _ h, h.U]; rfl
  | .lam q e, C, D, p, h => by
    simp only [nodesExp, List.map_append, List.append_assoc, shAtPat, h.U,
      shExp r e (C.plusVE q.ve) (D.plusVE q.ve) _ (h.plusVE _)]; rfl
  | .caseE e m, C, D, p, h => by
    simp only [nodesExp, List.map_append, List.append_assoc, shExp r e C D _ h, shMatch r m C D _ h, h.U]; rfl
theorem shExpOpt (r : List Nat) : ∀ (x : Option AExp) (C D : Ctx) (p : List Nat), CEq C D →
    nodesExpOpt C (r ++ p) x = (nodesExpOpt D p x).map (Node.pre r)
  | none, _, _, _, _ => rfl
  | some x, C, D, p, h => shExp r x C D p h
theorem shMatch (r : List Nat) : ∀ (x : AMatch) (C D : Ctx) (p : List Nat), CEq C D →
    nodesMatch C (r ++ p) x = (nodesMatch D p x).map (Node.pre r)
  | .mk (.mk q e) rest, C, D, p, h => by
    simp only [nodesMatch, List.map_append, List.append_assoc, shPat, h.U,
      shExp r e (C.plusVE q.ve) (D.plusVE q.ve) _ (h.plusVE _), shMatchOpt r rest C D _ h]; rfl
theorem shMatchOpt (r : List Nat) : ∀ (x : Option AMatch) (C D : Ctx) (p : List Nat), CEq C D →
    nodesMatchOpt C (r ++ p) x = (nodesMatchOpt D p x).map (Node.pre r)
  | none, _, _, _, _ => rfl
  | some x, C, D, p, h => shMatch r x C D p h
theorem shDec (r : List Nat) : ∀ (x : ADec) (C D : Ctx) (p : List Nat), CEq C D →
    nodesDec C (r ++ p) x = (nodesDec D p x).map (Node.pre r)
  | .val VE vb, C, D, p, h => by
    simp only [nodesDec, List.map_append, List.append_assoc, h.closG VE, h.U,
      shValBind r vb (C.plusVE VE) (D.plusVE VE) _ (h.plusVE VE)]; rfl
theorem shValBind (r : List Nat) : ∀ (x : AValBind) (C D : Ctx) (p : List Nat), CEq C D →
    nodesValBind C (r ++ p) x = (nodesValBind D p x).map (Node.pre r)
  | .var _ ann _ e rest, C, D, p, h => by
    simp only [nodesValBind, List.map_append, List.append_assoc, h.U,
      shExp r e (C.plusU (annU ann)) (D.plusU (annU ann)) _ (h.plusU _), shValBindOpt r rest C D _ h]; rfl
  | .pat q e, C, D, p, h => by
    simp only [nodesValBind, List.map_append, List.append_assoc, shAtPat, h.U, shExp r e C D _ h]; rfl
theorem shValBindOpt (r : List Nat) : ∀ (x : Option AValBind) (C D : Ctx) (p : List Nat), CEq C D →
    nodesValBindOpt C (r ++ p) x = (nodesValBindOpt D p x).map (Node.pre r)
  | none, _, _, _, _ => rfl
  | some x, C, D, p, h => shValBind r x C D p h
end

theorem shValBind0 (r : List Nat) (x : AValBind) {C D : Ctx} (h : CEq C D) :
    nodesValBind C r x = (nodesValBind D [] x).map (Node.pre r) := by
  have := shValBind r x C D [] h; rwa [List.append_nil] at this

/-! ## Pairs of nodes at one path -/

/-- Every pair of nodes at one path is an instance by `S`. -/
def PI (S : Subst) (ns ns'' : List Node) : Prop :=
  ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → NodeInstance S n n''

theorem NodeInstance.congr {S : Subst} {n n'' m m'' : Node} (h : NodeInstance S m m'')
    (e1 : n.U = m.U) (e2 : n.tys = m.tys) (e3 : n.schemes = m.schemes)
    (e4 : n''.U = m''.U) (e5 : n''.tys = m''.tys) (e6 : n''.schemes = m''.schemes) : NodeInstance S n n'' := by
  unfold NodeInstance at h ⊢
  rw [e1, e2, e3, e4, e5, e6]; exact h

theorem nodeInstance_empty (S : Subst) (n n'' : Node) (h1 : n.U = []) (h2 : n.tys = []) (h3 : n.schemes = [])
    (h4 : n''.U = []) (h5 : n''.tys = []) (h6 : n''.schemes = []) : NodeInstance S n n'' := by
  unfold NodeInstance
  rw [h1, h2, h3, h4, h5, h6]
  exact ⟨⟨[], rfl, fun _ => Iff.rfl⟩, rfl, rfl, fun i hi => by simp at hi⟩

theorem PI.mono {S : Subst} {ns ns'' ms ms'' : List Node} (h : PI S ns ns'') (h1 : ∀ n ∈ ms, n ∈ ns)
    (h2 : ∀ n ∈ ms'', n ∈ ns'') : PI S ms ms'' := fun n hn n'' hn'' e => h n (h1 n hn) n'' (h2 n'' hn'') e

theorem PI.append {S : Subst} {A A'' B B'' : List Node} (hA : PI S A A'') (hB : PI S B B'')
    (h1 : ∀ a ∈ A, ∀ b ∈ B'', a.path ≠ b.path) (h2 : ∀ b ∈ B, ∀ a ∈ A'', b.path ≠ a.path) :
    PI S (A ++ B) (A'' ++ B'') := by
  intro n hn n'' hn'' e
  rcases List.mem_append.mp hn with hn | hn <;> rcases List.mem_append.mp hn'' with hn'' | hn''
  · exact hA n hn n'' hn'' e
  · exact absurd e (h1 n hn n'' hn'')
  · exact absurd e (h2 n hn n'' hn'')
  · exact hB n hn n'' hn'' e

theorem PI.pre {S : Subst} {ns ns'' : List Node} (r r' : List Nat) (h : PI S (ns.map (Node.pre r')) (ns''.map (Node.pre r'))) :
    PI S (ns.map (Node.pre r)) (ns''.map (Node.pre r)) := by
  intro n hn n'' hn'' e
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
  obtain ⟨m'', hm'', rfl⟩ := List.mem_map.mp hn''
  have e' : m.path = m''.path := by simpa [Node.pre] using e
  have := h (Node.pre r' m) (List.mem_map_of_mem hm) (Node.pre r' m'') (List.mem_map_of_mem hm'')
    (by simp [Node.pre, e'])
  exact NodeInstance.congr this rfl rfl rfl rfl rfl rfl

/-! ## Paths below a top-level declaration -/

theorem topDec_prefix : ∀ (d : ATopDec) (C : Ctx) (q : List Nat), ∀ n ∈ nodesTopDec C q d, ∃ s, n.path = q ++ s
  | .value VE vb, C, q, n, hn => by
    simp only [nodesTopDec, List.cons_append, List.nil_append, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact ⟨[], by simp⟩
    · rw [shValBind0 _ vb (CEq.refl _)] at hn
      obtain ⟨m, -, rfl⟩ := List.mem_map.mp hn
      exact ⟨[0] ++ m.path, by simp [Node.pre]⟩
  | .types _ _ _ _, C, q, n, hn => by
    simp only [nodesTopDec, List.mem_singleton] at hn; subst hn; exact ⟨[], by simp⟩
  | .port x ty U, C, q, n, hn => by
    simp only [nodesTopDec] at hn
    split at hn
    · simp only [List.mem_singleton] at hn; subst hn; exact ⟨[], by simp⟩
    · cases hn
  | .seq a1 a2, C, q, n, hn => by
    simp only [nodesTopDec] at hn
    split at hn
    · rename_i E1 _ _
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hn
      rcases hn with rfl | hn | hn
      · exact ⟨[], by simp⟩
      · obtain ⟨s, hs⟩ := topDec_prefix a1 C (q ++ [0]) n hn; exact ⟨[0] ++ s, by simp [hs]⟩
      · obtain ⟨s, hs⟩ := topDec_prefix a2 _ (q ++ [1]) n hn; exact ⟨[1] ++ s, by simp [hs]⟩
    · cases hn

theorem prefix_ne {q : List Nat} {i j : Nat} (hij : i ≠ j) {s t : List Nat} : q ++ [i] ++ s ≠ q ++ [j] ++ t := by
  intro e
  simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append, List.nil_append,
    List.cons.injEq] at e
  exact hij e.1

theorem prefix_long {q s : List Nat} {i : Nat} : q ≠ q ++ [i] ++ s := by
  intro e
  have := congrArg List.length e
  simp at this

/-- A top-level group's nodes from its `let`'s declaration's. -/
theorem pi_group {S : Subst} {C C'' D D'' : Ctx} (hC : CEq C D) (hC'' : CEq C'' D'')
    {VE VE'' : ValEnv} {vb vb'' : AValBind} (Q P : List Nat)
    (h : PI S (nodesDec D P (.val VE vb)) (nodesDec D'' P (.val VE'' vb''))) :
    PI S (nodesTopDec C Q (.value VE vb)) (nodesTopDec C'' Q (.value VE'' vb'')) := by
  simp only [nodesDec] at h
  simp only [nodesTopDec]
  rw [shValBind0 _ vb (CEq.refl (D.plusVE VE)), shValBind0 _ vb'' (CEq.refl (D''.plusVE VE''))] at h
  rw [shValBind0 _ vb (hC.plusVE VE), shValBind0 _ vb'' (hC''.plusVE VE'')]
  have hg := h _ List.mem_cons_self _ List.mem_cons_self rfl
  refine PI.append (fun n hn n'' hn'' _ => ?_) (PI.pre _ _ (h.mono (fun n hn => List.mem_cons_of_mem _ hn)
    (fun n hn => List.mem_cons_of_mem _ hn))) ?_ ?_
  · simp only [List.mem_singleton] at hn hn''
    subst hn; subst hn''
    exact NodeInstance.congr hg hC.U rfl (by rw [hC.closG]) hC''.U rfl (by rw [hC''.closG])
  · intro a ha b hb
    simp only [List.mem_singleton] at ha; subst ha
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hb
    simp [Node.pre]
  · intro b hb a ha
    simp only [List.mem_singleton] at ha; subst ha
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hb
    intro e
    exact prefix_long (q := Q) (i := 0) (s := m.path) (by simpa [Node.pre] using e.symm)

theorem nodesTopDec_seq {C : Ctx} {q : List Nat} {a1 a2 : ATopDec} {E1 : Env} {PE1 : PortEnv}
    (h : checkTopDec C a1 = some (E1, PE1)) :
    nodesTopDec C q (.seq a1 a2) =
      [⟨q, C.U, [], []⟩] ++ nodesTopDec C (q ++ [0]) a1 ++ nodesTopDec (C.oplusE E1) (q ++ [1]) a2 := by
  simp only [nodesTopDec, h]

theorem nodesExp_let (D : Ctx) (p : List Nat) (d : ADec) (e : AExp) :
    nodesExp D p (.atexp (.letE d e)) =
      [⟨p, D.U, [e.ty], []⟩] ++ ([⟨p ++ [0], D.U, [e.ty], []⟩] ++ nodesDec D (p ++ [0] ++ [0]) d ++
        nodesExp (D.plusVE (d.result D)) (p ++ [0] ++ [1]) e) := by
  simp only [nodesExp, nodesAtExp, AAtExp.ty]

theorem erase_value {ar : ATopDec} {vb : Src.BValBind} (h : Src.BTopDec.value vb = ar.erase) :
    ∃ VE vb'', ar = .value VE vb'' ∧ vb''.erase = vb := by
  cases ar with
  | value VE vb'' => simp only [ATopDec.erase, Src.BTopDec.value.injEq] at h; exact ⟨VE, vb'', rfl, h.symm⟩
  | types _ _ _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at h

theorem erase_port {ar : ATopDec} {x : Var} {ty : Src.BTy} (h : Src.BTopDec.port x ty = ar.erase) :
    ∃ U, ar = .port x ty U := by
  cases ar with
  | port x' ty' U => simp only [ATopDec.erase, Src.BTopDec.port.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨U, rfl⟩
  | value _ _ | types _ _ _ _ | seq _ _ => simp [ATopDec.erase] at h

theorem U_nil_of_closed {C : Ctx} (h : ∀ v, v ∉ C.tyvars) : C.U = [] := by
  cases e : C.U with
  | nil => rfl
  | cons v _ => exact absurd (by simp [Ctx.tyvars, e]) (h v)

/-- A node whose variables a substitution leaves alone is an instance of itself by it. -/
theorem nodeInstance_self {S : Subst} {n : Node} (hU : ∀ v ∈ n.U, v ∉ S.dom)
    (hfix : ∀ τ ∈ n.tys ++ n.schemes.map (·.body), ∀ v ∈ τ.vars, v ∉ S.dom) : NodeInstance S n n := by
  have hvar : ∀ v ∈ n.U, S.applyVar v = some v := by
    intro v hv
    cases v with
    | ty a =>
      simp only [Subst.applyVar]
      rw [apply_fix S (.var a) (fun w hw => by simp [Ty.vars] at hw; subst hw; exact hU _ hv)]
    | row e =>
      simp only [Subst.applyVar]
      rw [apply_fix S (.record [] (some e)) (fun w hw => by simp [Ty.vars, Ty.rowVars] at hw; subst hw; exact hU _ hv)]
  refine ⟨⟨n.U, ?_, fun _ => Iff.rfl⟩, ?_, rfl, fun i hi _ τ hg => ⟨n.schemes[i], ?_, hg⟩⟩
  · have := mapM_some S.applyVar id n.U hvar
    rwa [List.map_id] at this
  · have := mapM_some S.apply id n.tys fun τ hτ => apply_fix S τ (hfix τ (List.mem_append_left _ hτ))
    rwa [List.map_id] at this
  · simp only [Subst.applyScheme]
    rw [apply_fix S _ (hfix _ (List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem hi))))]
    rfl

/-- A port's node is the same in two derivations, and an instance of itself. -/
theorem pi_port {S : Subst} {Cp C C'' : Ctx} (hp : ∀ v, v ∉ Cp.tyvars) (hC : PA Cp C) (hC'' : PA Cp C'')
    {x : Var} {ty : Src.BTy} {U U'' : List BVar} (hk : (checkTopDec C (.port x ty U)).isSome)
    (hk'' : (checkTopDec C'' (.port x ty U'')).isSome) (hS : ∀ v ∈ portsVars Cp (.port x ty U), v ∉ S.dom)
    (q : List Nat) : PI S (nodesTopDec C q (.port x ty U)) (nodesTopDec C'' q (.port x ty U'')) := by
  obtain ⟨⟨E, PE⟩, he⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨⟨E'', PE''⟩, he''⟩ := Option.isSome_iff_exists.mp hk''
  have h1 : elabPort C x ty U = some (E, PE) := he
  have h2 : elabPort C'' x ty U'' = some (E'', PE'') := he''
  have hUU : U'' = U := by rw [elabPort_U h1, elabPort_U h2, hC.U, hC''.U]
  subst hUU
  rw [hC.elabPort hp] at h1
  rw [hC''.elabPort hp, h1] at h2
  cases h2
  have hn : nodesTopDec C q (.port x ty U'') = [⟨q, C.U ++ U'', PE.map (·.2.2), veSchemes E.VE⟩] := by
    simp only [nodesTopDec, hC.elabPort hp, h1]
  have hn'' : nodesTopDec C'' q (.port x ty U'') = [⟨q, C''.U ++ U'', PE.map (·.2.2), veSchemes E.VE⟩] := by
    simp only [nodesTopDec, hC''.elabPort hp, h1]
  simp only [portsVars, h1, portNodeVars] at hS
  rw [hn, hn'', hC.U, hC''.U]
  intro n hn n'' hn'' _
  simp only [List.mem_singleton] at hn hn''
  subst hn; subst hn''
  refine nodeInstance_self (fun v hv => ?_) (fun τ hτ v hv => ?_)
  · rw [U_nil_of_closed hp, List.nil_append] at hv
    exact hS v (List.mem_append_left _ (List.mem_append_left _ hv))
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact hS v (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨τ, hτ, hv⟩)))
    · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
      exact hS v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨σ, hσ, hv⟩))

/-- After a port: the module's context against the `let` body's. -/
theorem port_after {Cp C D : Ctx} (hp : ∀ v, v ∉ Cp.tyvars) (hC : PA Cp C) (h : CEq C D) {x : Var} {ty : Src.BTy}
    {U : List BVar} {E : Env} {PE : PortEnv} {t : AExp} (hk : checkTopDec C (.port x ty U) = some (E, PE))
    (hpo : portOKB Cp x ty (tmplDec t) = true) :
    ∃ d t', t = .atexp (.letE d t') ∧ CEq (C.oplusE E) (D.plusVE (d.result D)) ∧ PA Cp (C.oplusE E) := by
  obtain ⟨VE, U', τ, ts, τ', t', E', PE', rfl, hel, hcl, -⟩ := portOKB_tmpl hpo
  have hk' : elabPort C x ty U = some (E, PE) := hk
  have hUU : U = U' := by rw [elabPort_U hk', elabPort_U hel, hC.U]
  subst hUU
  rw [hC.elabPort hp, hel] at hk'
  cases hk'
  refine ⟨_, t', rfl, ?_, ?_⟩
  · simp only [ADec.result]
    rw [closGroup_nil_of (hC.ofCEq h).cl, hcl, elabPort_ofVE hel]
    exact h.oplus_plus _
  · rw [elabPort_ofVE hel]; exact hC.oplusVE (elabPort_closed hp hel)

theorem pi_root {S : Subst} {C C'' : Ctx} (q : List Nat) (hU : C.U = []) (hU'' : C''.U = []) :
    PI S [⟨q, C.U, [], []⟩] [⟨q, C''.U, [], []⟩] := fun n hn n'' hn'' _ => by
  simp only [List.mem_singleton] at hn hn''; subst hn; subst hn''
  exact nodeInstance_empty S _ _ hU rfl rfl hU'' rfl rfl

/-- The nodes of a `seq`, from those of its first part and of its rest. -/
theorem pi_seq {S : Subst} {C C'' : Ctx} {q : List Nat} {a1 a2 b1 b2 : ATopDec} {C2 C2'' : Ctx}
    (hU : C.U = []) (hU'' : C''.U = [])
    (h1 : PI S (nodesTopDec C (q ++ [0]) a1) (nodesTopDec C'' (q ++ [0]) b1))
    (h2 : PI S (nodesTopDec C2 (q ++ [1]) a2) (nodesTopDec C2'' (q ++ [1]) b2)) :
    PI S ([⟨q, C.U, [], []⟩] ++ nodesTopDec C (q ++ [0]) a1 ++ nodesTopDec C2 (q ++ [1]) a2)
      ([⟨q, C''.U, [], []⟩] ++ nodesTopDec C'' (q ++ [0]) b1 ++ nodesTopDec C2'' (q ++ [1]) b2) := by
  refine PI.append (PI.append (pi_root q hU hU'') h1 ?_ ?_) h2 ?_ ?_
  · intro a ha b hb
    simp only [List.mem_singleton] at ha; subst ha
    obtain ⟨s, hs⟩ := topDec_prefix _ _ _ b hb
    simp only [hs]; exact prefix_long
  · intro b hb a ha
    simp only [List.mem_singleton] at ha; subst ha
    obtain ⟨s, hs⟩ := topDec_prefix _ _ _ b hb
    simp only [hs]; exact fun e => prefix_long e.symm
  · intro a ha b hb
    obtain ⟨s2, hs2⟩ := topDec_prefix _ _ _ b hb
    rcases List.mem_append.mp ha with ha | ha
    · simp only [List.mem_singleton] at ha; subst ha
      simp only [hs2]; exact prefix_long
    · obtain ⟨s1, hs1⟩ := topDec_prefix _ _ _ a ha
      rw [hs1, hs2]; exact prefix_ne (by decide)
  · intro b hb a ha
    obtain ⟨s2, hs2⟩ := topDec_prefix _ _ _ b hb
    rcases List.mem_append.mp ha with ha | ha
    · simp only [List.mem_singleton] at ha; subst ha
      simp only [hs2]; exact fun e => prefix_long e.symm
    · obtain ⟨s1, hs1⟩ := topDec_prefix _ _ _ a ha
      rw [hs1, hs2]; exact prefix_ne (by decide)

theorem isSome_some {α : Type} {o : Option α} (h : o.isSome) : ∃ a, o = some a := Option.isSome_iff_exists.mp h

/-- The nodes of two modules' value declarations and ports at one path are instances by `S` when
    those of their nested `let`s are (the ports' groups taken from one template). -/
theorem pi_values {S : Subst} {Cp : Ctx} (hp : ∀ v, v ∉ Cp.tyvars) :
    ∀ (av ar : ATopDec) (C C'' D D'' : Ctx) (q p : List Nat) (t x x'' : AExp),
    toExpA av t = some x → toExpA ar t = some x'' → av.erase = ar.erase →
    CEq C D → CEq C'' D'' → PA Cp C → PA Cp C'' →
    (checkTopDec C av).isSome → (checkTopDec C'' ar).isSome →
    portsOKB Cp av.erase t = true → (∀ v ∈ portsVars Cp av, v ∉ S.dom) →
    PI S (nodesExp D p x) (nodesExp D'' p x'') → PI S (nodesTopDec C q av) (nodesTopDec C'' q ar)
  | .value VE vb, ar, C, C'', D, D'', q, p, t, x, x'', hx, hx'', he, hC, hC'', _, _, _, _, _, _, h => by
    obtain ⟨VE'', vb'', rfl, -⟩ := erase_value (vb := vb.erase) (by rw [← he]; rfl)
    simp only [toExpA, Option.some.injEq] at hx hx''
    subst hx; subst hx''
    rw [nodesExp_let, nodesExp_let] at h
    exact pi_group hC hC'' q (p ++ [0] ++ [0]) (h.mono
      (fun n hn => List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hn)))
      (fun n hn => List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hn))))
  | .port x0 ty U, ar, C, C'', D, D'', q, p, t, x, x'', _, _, he, _, _, hP, hP'', hk, hk'', _, hS, _ => by
    obtain ⟨U'', rfl⟩ := erase_port (x := x0) (ty := ty) (by rw [← he]; rfl)
    exact pi_port hp hP hP'' hk hk'' hS q
  | .seq a1 av2, ar, C, C'', D, D'', q, p, t, x, x'', hx, hx'', he, hC, hC'', hP, hP'', hk, hk'', hpo, hS, h => by
    have hU := hP.U.trans (U_nil_of_closed hp)
    have hU'' := hP''.U.trans (U_nil_of_closed hp)
    cases ar with
    | seq b1 ar2 =>
      simp only [ATopDec.erase, Src.BTopDec.seq.injEq] at he
      obtain ⟨⟨E, PE⟩, hkk⟩ := isSome_some hk
      obtain ⟨⟨E'', PE''⟩, hkk''⟩ := isSome_some hk''
      obtain ⟨E1, PE1, E2, PE2, hk1, hk2⟩ := checkTopDec_seq hkk
      obtain ⟨E1'', PE1'', E2'', PE2'', hk1'', hk2''⟩ := checkTopDec_seq hkk''
      rw [nodesTopDec_seq hk1, nodesTopDec_seq hk1'']
      cases a1 with
      | value VE vb =>
        cases b1 with
        | value VE'' vb'' =>
          simp only [toExpA] at hx hx''
          obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.mp hx
          obtain ⟨x2'', hx2'', rfl⟩ := Option.map_eq_some_iff.mp hx''
          obtain ⟨-, -, -, rfl⟩ := checkTopDec_value hk1
          obtain ⟨-, -, -, rfl⟩ := checkTopDec_value hk1''
          rw [nodesExp_let, nodesExp_let] at h
          have h2 : CEq (C.oplusE (Env.ofVE (closGroup C.tyvars VE))) (D.plusVE (ADec.result D (.val VE vb))) := by
            simp only [ADec.result]; rw [← hC.closG VE]; exact hC.oplus_plus _
          have h2'' : CEq (C''.oplusE (Env.ofVE (closGroup C''.tyvars VE''))) (D''.plusVE (ADec.result D'' (.val VE'' vb''))) := by
            simp only [ADec.result]; rw [← hC''.closG VE'']; exact hC''.oplus_plus _
          simp only [ATopDec.erase, portsOKB] at hpo
          have ih := pi_values hp av2 ar2 _ _ _ _ (q ++ [1]) (p ++ [0] ++ [1]) (tmplBody t) x2 x2'' hx2 hx2'' he.2 h2 h2''
            (hP.oplusVE (closGroup_closed_of hP.cl VE)) (hP''.oplusVE (closGroup_closed_of hP''.cl VE''))
            (by rw [hk2]; rfl) (by rw [hk2'']; rfl) hpo (fun v hv => hS v (by simpa [portsVars] using hv))
            (h.mono (fun n hn => List.mem_append_right _ (List.mem_append_right _ hn))
              (fun n hn => List.mem_append_right _ (List.mem_append_right _ hn)))
          have hg := pi_group (S := S) hC hC'' (VE := VE) (VE'' := VE'') (vb := vb) (vb'' := vb'') (q ++ [0]) (p ++ [0] ++ [0])
            (h.mono (fun n hn => List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hn)))
              (fun n hn => List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hn))))
          exact pi_seq hU hU'' hg ih
        | types _ _ _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at he
      | port x0 ty U =>
        cases b1 with
        | port x1 ty1 U'' =>
          simp only [ATopDec.erase, Src.BTopDec.port.injEq] at he
          obtain ⟨⟨rfl, rfl⟩, he2⟩ := he
          simp only [ATopDec.erase, portsOKB, Bool.and_eq_true] at hpo
          obtain ⟨d, t', rfl, hce, hPn⟩ := port_after hp hP hC hk1 hpo.1
          obtain ⟨d'', t'', ht'', hce'', hPn''⟩ := port_after hp hP'' hC'' hk1'' hpo.1
          cases ht''
          simp only [toExpA, tmplDec, tmplBody] at hx hx''
          obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.mp hx
          obtain ⟨x2'', hx2'', rfl⟩ := Option.map_eq_some_iff.mp hx''
          rw [nodesExp_let, nodesExp_let] at h
          have ih := pi_values hp av2 ar2 _ _ _ _ (q ++ [1]) (p ++ [0] ++ [1]) t' x2 x2'' hx2 hx2'' he2 hce hce''
            hPn hPn'' (by rw [hk2]; rfl) (by rw [hk2'']; rfl) hpo.2
            (fun v hv => hS v (List.mem_append_right _ hv))
            (h.mono (fun n hn => List.mem_append_right _ (List.mem_append_right _ hn))
              (fun n hn => List.mem_append_right _ (List.mem_append_right _ hn)))
          have hg := pi_port (S := S) hp hP hP'' (by rw [hk1]; rfl) (by rw [hk1'']; rfl)
            (fun v hv => hS v (List.mem_append_left _ hv)) (q ++ [0])
          exact pi_seq hU hU'' hg ih
        | value _ _ | types _ _ _ _ | seq _ _ => simp [ATopDec.erase] at he
      | types _ _ _ _ | seq _ _ => simp [toExpA] at hx
    | value _ _ | types _ _ _ _ | port _ _ _ =>
      cases a1 <;> simp [ATopDec.erase] at he
  | .types _ _ _ _, _, _, _, _, _, _, _, _, _, _, hx, _, _, _, _, _, _, _, _, _, _, _ => by simp [toExpA] at hx

theorem mem_dec_part {D : Ctx} {p : List Nat} {d : ADec} {e : AExp} {n : Node} (h : n ∈ nodesDec D (p ++ [0] ++ [0]) d) :
    n ∈ nodesExp D p (.atexp (.letE d e)) := by
  rw [nodesExp_let]
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_body_part {D : Ctx} {p : List Nat} {d : ADec} {e : AExp} {n : Node}
    (h : n ∈ nodesExp (D.plusVE (d.result D)) (p ++ [0] ++ [1]) e) : n ∈ nodesExp D p (.atexp (.letE d e)) := by
  rw [nodesExp_let]
  exact List.mem_append_right _ (List.mem_append_right _ h)

theorem tys_group {C D : Ctx} (hC : CEq C D) {VE : ValEnv} {vb : AValBind} (Q P : List Nat) :
    ∀ n ∈ nodesTopDec C Q (.value VE vb), ∀ τ ∈ n.tys, ∃ m ∈ nodesDec D P (.val VE vb), τ ∈ m.tys := by
  intro n hn τ hτ
  simp only [nodesTopDec, List.cons_append, List.nil_append, List.mem_cons] at hn
  rcases hn with rfl | hn
  · simp at hτ
  · rw [shValBind0 _ vb (hC.plusVE VE)] at hn
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
    refine ⟨Node.pre (P ++ [0]) g, ?_, hτ⟩
    simp only [nodesDec]
    apply List.mem_append_right
    rw [shValBind0 _ vb (CEq.refl _)]; exact List.mem_map_of_mem hg

/-- The types at a port's node have the port's variables. -/
theorem tys_port {Cp C : Ctx} (hp : ∀ v, v ∉ Cp.tyvars) (hC : PA Cp C) {x : Var} {ty : Src.BTy} {U : List BVar}
    (q : List Nat) : ∀ n ∈ nodesTopDec C q (.port x ty U), ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, v ∈ portsVars Cp (.port x ty U) := by
  intro n hn τ hτ v hv
  cases he : elabPort Cp x ty U with
  | none => simp [nodesTopDec, hC.elabPort hp, he] at hn
  | some pr =>
    obtain ⟨E, PE⟩ := pr
    simp only [nodesTopDec, hC.elabPort hp, he, List.mem_singleton] at hn
    subst hn
    simp only [portsVars, he, portNodeVars]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨τ, hτ, hv⟩))

/-- Every type at a node of a module's value declarations is a type at a node of their nested
    `let`, or has the ports' variables only. -/
theorem tys_values {Cp : Ctx} (hp : ∀ v, v ∉ Cp.tyvars) :
    ∀ (av : ATopDec) (C D : Ctx) (q p : List Nat) (t x : AExp), toExpA av t = some x → CEq C D → PA Cp C →
    (checkTopDec C av).isSome → portsOKB Cp av.erase t = true → ∀ n ∈ nodesTopDec C q av, ∀ τ ∈ n.tys,
      (∃ m ∈ nodesExp D p x, τ ∈ m.tys) ∨ ∀ v ∈ τ.vars, v ∈ portsVars Cp av
  | .value VE vb, C, D, q, p, t, x, hx, hC, _, _, _, n, hn, τ, hτ => by
    simp only [toExpA, Option.some.injEq] at hx; subst hx
    obtain ⟨m, hm, hτm⟩ := tys_group hC q (p ++ [0] ++ [0]) n hn τ hτ
    exact .inl ⟨m, mem_dec_part hm, hτm⟩
  | .port x0 ty U, C, D, q, p, t, x, _, _, hP, _, _, n, hn, τ, hτ => .inr (tys_port hp hP q n hn τ hτ)
  | .seq a1 av2, C, D, q, p, t, x, hx, hC, hP, hk, hpo, n, hn, τ, hτ => by
    obtain ⟨⟨E, PE⟩, hkk⟩ := isSome_some hk
    obtain ⟨E1, PE1, E2, PE2, hk1, hk2⟩ := checkTopDec_seq hkk
    rw [nodesTopDec_seq hk1] at hn
    cases a1 with
    | value VE vb =>
      simp only [toExpA] at hx
      obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.mp hx
      obtain ⟨-, -, -, rfl⟩ := checkTopDec_value hk1
      simp only [ATopDec.erase, portsOKB] at hpo
      have h2 : CEq (C.oplusE (Env.ofVE (closGroup C.tyvars VE))) (D.plusVE (ADec.result D (.val VE vb))) := by
        simp only [ADec.result]; rw [← hC.closG VE]; exact hC.oplus_plus _
      rcases List.mem_append.mp hn with hn | hn
      · rcases List.mem_append.mp hn with hn | hn
        · simp only [List.mem_singleton] at hn; subst hn; simp at hτ
        · obtain ⟨m, hm, hτm⟩ := tys_group hC (q ++ [0]) (p ++ [0] ++ [0]) n hn τ hτ
          exact .inl ⟨m, mem_dec_part hm, hτm⟩
      · rcases tys_values hp av2 _ _ (q ++ [1]) (p ++ [0] ++ [1]) (tmplBody t) x2 hx2 h2
            (hP.oplusVE (closGroup_closed_of hP.cl VE)) (by rw [hk2]; rfl) hpo n hn τ hτ with h | h
        · obtain ⟨m, hm, hτm⟩ := h; exact .inl ⟨m, mem_body_part hm, hτm⟩
        · exact .inr fun v hv => by simpa [portsVars] using h v hv
    | port x0 ty U =>
      simp only [ATopDec.erase, portsOKB, Bool.and_eq_true] at hpo
      obtain ⟨d, t', rfl, hce, hPn⟩ := port_after hp hP hC hk1 hpo.1
      simp only [toExpA, tmplDec, tmplBody] at hx
      obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.mp hx
      rcases List.mem_append.mp hn with hn | hn
      · rcases List.mem_append.mp hn with hn | hn
        · simp only [List.mem_singleton] at hn; subst hn; simp at hτ
        · exact .inr fun v hv => List.mem_append_left _ (tys_port hp hP (q ++ [0]) n hn τ hτ v hv)
      · rcases tys_values hp av2 _ _ (q ++ [1]) (p ++ [0] ++ [1]) t' x2 hx2 hce hPn (by rw [hk2]; rfl) hpo.2
            n hn τ hτ with h | h
        · obtain ⟨m, hm, hτm⟩ := h; exact .inl ⟨m, mem_body_part hm, hτm⟩
        · exact .inr fun v hv => List.mem_append_right _ (h v hv)
    | types _ _ _ _ | seq _ _ => simp [toExpA] at hx
  | .types _ _ _ _, _, _, _, _, _, _, hx, _, _, _, _, _, _, _, _ => by simp [toExpA] at hx

end MW
end StandardElm.Stat.Complete
