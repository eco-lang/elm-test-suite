/-
  A Standard Definition of Elm? Mechanisation: completeness of the functional parts of Chapter 7's
  evaluator, and the statements about every derivation of a module or a program (plan decision D1),
  plan step 2.

  * The relations that evaluate no expression are functions: any derivation gives what the
    evaluator computes (`EvalImports.eq_ev` and the others).
  * `nostuck` for forcing, top-level declarations, modules and programs, from the Core's.
  * `noMeaning_of_stuck`: a program on which the evaluator is stuck without reading a choice has no
    meaning; `evProgram_unique_l`: a value found without reading a choice is the only one.
-/
import StandardElmMech.Mod.Sound
import StandardElmMech.Determinism
import StandardElmMech.Completeness

namespace StandardElm.Mod
open StandardElm StandardElm.Eff

theorem EvalExpItem.eq_ev : ∀ {I it I'}, EvalExpItem I it I' → evExpItem I it = some I'
  | _, _, _, .r_dm_expitem_var I x v h => by simp [evExpItem, h]
  | _, _, _, .r_dm_expitem_op I o => by simp [evExpItem]
  | _, _, _, .r_dm_expitem_alias I t v h1 h2 => by simp [evExpItem, h1, h2]
  | _, _, _, .r_dm_expitem_type I t CE h1 h2 => by subst h2; simp [evExpItem, h1]
  | _, _, _, .r_dm_expitem_open I t VE h => by simp [evExpItem, h]

theorem EvalExpItems.eq_ev : ∀ {I is Is}, EvalExpItems I is Is → evExpItems I is = some Is
  | _, _, _, .seq_nil I => by simp [evExpItems]
  | _, _, _, .seq_cons I it is I1 Is h1 h2 => by simp [evExpItems, h1.eq_ev, h2.eq_ev]

theorem EvalExpList.eq_ev : ∀ {I el I'}, EvalExpList I el I' → evExpList I el = some I'
  | _, _, _, .r_dm_explist_all I => by simp [evExpList]
  | _, _, _, .r_dm_explist_items I is Is hne h => by
    cases is with
    | nil => exact absurd rfl hne
    | cons it rest => simp [evExpList, h.eq_ev]

theorem EvalExpListOpt.eq_ev : ∀ {I el I'}, EvalExpListOpt I el I' → evExpListOpt I el = some I'
  | _, _, _, .opt_none I => by simp [evExpListOpt]
  | _, _, _, .opt_some I el I' h => by simp [evExpListOpt, h.eq_ev]

theorem EvalHeader.eq_ev : ∀ {I h m I'}, EvalHeader I h m I' → evHeader I h = some (m, I')
  | _, _, _, _, .r_dm_header I isPort m el I' h => by simp [evHeader, h.eq_ev]

theorem EvalImports.eq_ev : ∀ {B is E}, EvalImports B is E → evImports B is = some E
  | _, _, _, .r_dm_imports_import B m q el rest I I' E h1 h2 h3 => by
    simp [evImports, h1, h2.eq_ev, h3.eq_ev]
  | _, _, _, .r_dm_imports_empty B => by simp [evImports]

mutual
theorem EvalConBind.eq_ev : ∀ {cb VE}, EvalConBind cb VE → VE = evConBind cb
  | _, _, .r_dm_conbind c rest VE h => by simp [evConBind, ← h.eq_ev]
theorem EvalConBindOpt.eq_ev : ∀ {cb VE}, EvalConBindOpt cb VE → VE = evConBindOpt cb
  | _, _, .opt_none => by simp [evConBindOpt]
  | _, _, .opt_some cb VE h => by simp [evConBindOpt, ← h.eq_ev]
end

mutual
theorem EvalDatBind.eq_ev : ∀ {db CE VE}, EvalDatBind db CE VE → CE = (evDatBind db).1 ∧ VE = (evDatBind db).2
  | _, _, _, .r_dm_datbind t cb rest VE CE' VE' h1 h2 => by
    obtain ⟨e1, e2⟩ := h2.eq_ev
    simp [evDatBind, ← h1.eq_ev, e1, e2]
theorem EvalDatBindOpt.eq_ev : ∀ {db CE VE}, EvalDatBindOpt db CE VE →
    CE = (evDatBindOpt db).1 ∧ VE = (evDatBindOpt db).2
  | _, _, _, .opt_none => by simp [evDatBindOpt]
  | _, _, _, .opt_some db CE VE h => by simpa [evDatBindOpt] using h.eq_ev
end

theorem EvalTypBind.eq_ev : ∀ {tb RA VE}, EvalTypBind tb RA VE → RA = (evTypBind tb).1 ∧ VE = (evTypBind tb).2
  | _, _, _, .r_dm_typbind t ls => ⟨rfl, rfl⟩

/-! ## nostuck -/

theorem evForces_next_ge (o : Oracle) (n : Nat) (E : Env) : ∀ ys k, k ≤ (evForces o n E ys k).next
  | [], k => by simp [evForces]
  | y :: ys, k => by
    simp only [evForces]
    rcases h1 : evExp o n E (forceExp y) k with ⟨out1, l1, k1⟩
    have e1 := evExp_next h1
    simp only at e1
    cases out1 with
    | value v =>
      dsimp only
      rcases h2 : evForces o n E ys k1 with ⟨out2, l2, k2⟩
      have e2 := evForces_next_ge o n E ys k1
      rw [h2] at e2; simp only at e2
      cases out2 <;> simp <;> omega
    | stuck => simp; omega
    | outOfFuel => simp; omega

theorem evForces_next {o : Oracle} {n : Nat} {E : Env} {ys : List Var} {k : Nat} {r : Res (List Val)}
    (h : evForces o n E ys k = r) : k ≤ r.next := by subst h; exact evForces_next_ge o n E ys k

theorem EvalForcesL.nostuck : ∀ {E ys vs l}, EvalForcesL E ys vs l →
    ∀ (o : Oracle) (n k : Nat) r, evForces o n E ys k = r →
      r.out = .outOfFuel ∨ k < r.next ∨ r = ⟨.value vs, l, k⟩
  | _, _, _, _, .seq_nil_l E => by intro o n k r h; subst h; simp [evForces]
  | _, _, _, _, .seq_cons_l E y ys v vs l1 l2 h1 h2 => by
    intro o n k r h
    have p1 : NS (evExp o n E (forceExp y)) v l1 := fun hh => EvalExpL.nostuck h1 o n _ _ hh
    have p2 : NS (evForces o n E ys) vs l2 := fun hh => EvalForcesL.nostuck h2 o n _ _ hh
    simp only [evForces] at h
    (repeat' (split at h))
    all_goals (subst h)
    all_goals (apply_to_eqs [evExp_next, evForces_next])
    iterate 3 (
      all_goals (apply_to_eqs [p1, p2])
      all_goals split_ors
      all_goals (try simp_all))
    all_goals (first | omega | (right; left; omega) | skip)

theorem evTopDec_next_ge (o : Oracle) (n : Nat) : ∀ E td k, k ≤ (evTopDec o n E td k).next
  | E, .val vb, k => by
    simp only [evTopDec]
    split
    · simp
    · rcases h1 : evValBind o n E (thunkGroup vb) k with ⟨out1, l1, k1⟩
      have e1 := evValBind_next h1
      simp only at e1
      cases out1 with
      | value VE =>
        dsimp only
        rcases h2 : evForces o n (E.plusVE (recVE VE)) (vb.map (thunkVar ∘ Prod.fst)) k1 with ⟨out2, l2, k2⟩
        have e2 := evForces_next h2
        simp only at e2
        cases out2 <;> simp <;> omega
      | stuck => simp; omega
      | outOfFuel => simp; omega
  | E, .type db, k => by simp [evTopDec]
  | E, .alias tb, k => by simp [evTopDec]
  | E, .port x .out τ, k => by simp [evTopDec]
  | E, .port x .inn τ, k => by simp [evTopDec]
  | E, .seq t1 t2, k => by
    simp only [evTopDec]
    rcases h1 : evTopDec o n E t1 k with ⟨out1, l1, k1⟩
    have e1 := evTopDec_next_ge o n E t1 k
    rw [h1] at e1; simp only at e1
    cases out1 with
    | value I1 =>
      dsimp only
      rcases h2 : evTopDec o n (E.plusVE I1.VE) t2 k1 with ⟨out2, l2, k2⟩
      have e2 := evTopDec_next_ge o n (E.plusVE I1.VE) t2 k1
      rw [h2] at e2; simp only at e2
      cases out2 <;> simp <;> omega
    | stuck => simp; omega
    | outOfFuel => simp; omega

theorem evTopDec_next {o : Oracle} {n : Nat} {E : Env} {td : TopDec} {k : Nat} {r : Res Interface}
    (h : evTopDec o n E td k = r) : k ≤ r.next := by subst h; exact evTopDec_next_ge o n E td k

theorem evModule_next {o : Oracle} {n : Nat} {B : Basis} {m : Module} {k : Nat} {r : Res (Basis × ValEnv)}
    (h : evModule o n B m k = r) : k ≤ r.next := by
  subst h
  simp only [evModule]
  split
  · rcases h1 : evTopDec o n _ m.body k with ⟨out1, l1, k1⟩
    have e1 := evTopDec_next h1
    simp only at e1
    cases out1 with
    | value I => dsimp only; split <;> simp <;> omega
    | stuck => simp; omega
    | outOfFuel => simp; omega
  · simp

theorem evProgram_next_ge (o : Oracle) (n : Nat) : ∀ B p k, k ≤ (evProgram o n B p k).next
  | B, [], k => by simp [evProgram]
  | B, [m], k => by
    simp only [evProgram]
    rcases h1 : evModule o n B m k with ⟨out1, l1, k1⟩
    have e1 := evModule_next h1
    simp only at e1
    cases out1 with
    | value BV => obtain ⟨B', VE⟩ := BV; dsimp only; split <;> simp <;> omega
    | stuck => simp; omega
    | outOfFuel => simp; omega
  | B, m :: m2 :: p, k => by
    simp only [evProgram]
    rcases h1 : evModule o n B m k with ⟨out1, l1, k1⟩
    have e1 := evModule_next h1
    simp only at e1
    cases out1 with
    | value BV =>
      obtain ⟨B', VE⟩ := BV
      dsimp only
      rcases h2 : evProgram o n (fmPlus B B') (m2 :: p) k1 with ⟨out2, l2, k2⟩
      have e2 := evProgram_next_ge o n (fmPlus B B') (m2 :: p) k1
      rw [h2] at e2; simp only at e2
      cases out2 <;> simp <;> omega
    | stuck => simp; omega
    | outOfFuel => simp; omega

theorem evProgram_next {o : Oracle} {n : Nat} {B : Basis} {p : List Module} {k : Nat} {r : Res Val}
    (h : evProgram o n B p k = r) : k ≤ r.next := by subst h; exact evProgram_next_ge o n B p k

theorem EvalTopDecL.nostuck : ∀ {E td I l}, EvalTopDecL E td I l →
    ∀ (o : Oracle) (n k : Nat) r, evTopDec o n E td k = r →
      r.out = .outOfFuel ∨ k < r.next ∨ r = ⟨.value I, l, k⟩
  | _, _, _, _, .r_dm_topdec_val_l E vb VE vs l1 l2 h0 h1 h2 => by
    intro o n k r h
    have p1 : NS (evValBind o n E (thunkGroup vb)) VE l1 := fun hh => EvalValBindL.nostuck h1 o n _ _ hh
    have p2 : NS (evForces o n (E.plusVE (recVE VE)) (vb.map (thunkVar ∘ Prod.fst))) vs l2 :=
      fun hh => EvalForcesL.nostuck h2 o n _ _ hh
    simp only [evTopDec, h0, ite_false] at h
    (repeat' (split at h))
    all_goals (subst h)
    all_goals (apply_to_eqs [evValBind_next, evForces_next])
    iterate 3 (
      all_goals (apply_to_eqs [p1, p2])
      all_goals split_ors
      all_goals (try simp_all))
    all_goals (first | omega | (right; left; omega) | skip)
  | _, _, _, _, .r_dm_topdec_type_l E db CE VE h1 => by
    intro o n k r h; subst h
    obtain ⟨e1, e2⟩ := h1.eq_ev
    simp [evTopDec, e1, e2]
  | _, _, _, _, .r_dm_topdec_alias_l E tb RA VE h1 => by
    intro o n k r h; subst h
    obtain ⟨e1, e2⟩ := h1.eq_ev
    simp [evTopDec, e1, e2]
  | _, _, _, _, .r_dm_topdec_port_out_l E x τ => by intro o n k r h; subst h; simp [evTopDec]
  | _, _, _, _, .r_dm_topdec_port_in_l E x τ => by intro o n k r h; subst h; simp [evTopDec]
  | _, _, _, _, .r_dm_topdec_seq_l E t1 t2 RA1 CE1 VE1 I2 l1 l2 h1 h2 => by
    intro o n k r h
    have p1 : NS (evTopDec o n E t1) ⟨RA1, CE1, VE1⟩ l1 := fun hh => EvalTopDecL.nostuck h1 o n _ _ hh
    have p2 : NS (evTopDec o n (E.plusVE VE1) t2) I2 l2 := fun hh => EvalTopDecL.nostuck h2 o n _ _ hh
    simp only [evTopDec] at h
    (repeat' (split at h))
    all_goals (subst h)
    all_goals (apply_to_eqs [evTopDec_next])
    iterate 3 (
      all_goals (apply_to_eqs [p1, p2])
      all_goals split_ors
      all_goals (try simp_all))
    all_goals (first | omega | (right; left; omega) | skip)

theorem EvalModuleL.nostuck : ∀ {B m B' VE l}, EvalModuleL B m B' VE l →
    ∀ (o : Oracle) (n k : Nat) r, evModule o n B m k = r →
      r.out = .outOfFuel ∨ k < r.next ∨ r = ⟨.value (B', VE), l, k⟩
  | _, _, _, _, _, .r_dm_module_l B hd is td E I mid I' l1 h1 h2 h3 => by
    intro o n k r h
    have p2 : NS (evTopDec o n (E0base.plusEnv E) td) I l1 := fun hh => EvalTopDecL.nostuck h2 o n _ _ hh
    have e1 := h1.eq_ev
    have e3 := h3.eq_ev
    simp only [evModule, e1] at h
    (repeat' (split at h))
    all_goals (subst h)
    all_goals (apply_to_eqs [evTopDec_next])
    iterate 3 (
      all_goals (apply_to_eqs [p2])
      all_goals split_ors
      all_goals (try simp_all))
    all_goals (first | omega | (right; left; omega) | skip)

theorem EvalProgramL.nostuck : ∀ {B p v l}, EvalProgramL B p v l →
    ∀ (o : Oracle) (n k : Nat) r, evProgram o n B p k = r →
      r.out = .outOfFuel ∨ k < r.next ∨ r = ⟨.value v, l, k⟩
  | _, _, _, _, .r_p_dyn_module_l B m p B' VE v l1 l2 h1 h2 h3 => by
    intro o n k r h
    have p1 : NS (evModule o n B m) (B', VE) l1 := fun hh => EvalModuleL.nostuck h1 o n _ _ hh
    have p2 : NS (evProgram o n (fmPlus B B') p) v l2 := fun hh => EvalProgramL.nostuck h2 o n _ _ hh
    obtain ⟨m2, p', rfl⟩ : ∃ m2 p', p = m2 :: p' := by
      cases p with
      | nil => exact absurd rfl h3
      | cons m2 p' => exact ⟨m2, p', rfl⟩
    simp only [evProgram] at h
    (repeat' (split at h))
    all_goals (subst h)
    all_goals (apply_to_eqs [evModule_next, evProgram_next])
    iterate 3 (
      all_goals (apply_to_eqs [p1, p2])
      all_goals split_ors
      all_goals (try simp_all))
    all_goals (first | omega | (right; left; omega) | skip)
  | _, _, _, _, .r_p_dyn_main_l B m B' VE v l1 h1 h2 => by
    intro o n k r h
    have p1 : NS (evModule o n B m) (B', VE) l1 := fun hh => EvalModuleL.nostuck h1 o n _ _ hh
    simp only [evProgram] at h
    (repeat' (split at h))
    all_goals (subst h)
    all_goals (apply_to_eqs [evModule_next])
    iterate 3 (
      all_goals (apply_to_eqs [p1])
      all_goals split_ors
      all_goals (try simp_all))
    all_goals (first | omega | (right; left; omega) | skip)

/-! ## Statements about every derivation of a program -/

/-- A program on which the evaluator is stuck without reading a choice has no meaning (A25, A62). -/
theorem noMeaning_of_stuck {o : Oracle} {n : Nat} {B : Basis} {p : List Module} {k : Nat} {l : Log}
    (h : evProgram o n B p k = ⟨.stuck, l, k⟩) : ¬ ∃ v, EvalProgram B p v := by
  rintro ⟨v, d⟩
  obtain ⟨l', d'⟩ := EvalProgram.lift d
  rcases EvalProgramL.nostuck d' o n k _ h with h1 | h1 | h1 <;> simp at h1

/-- A program value found without reading a choice is the only one, and its log the only log. -/
theorem evProgram_unique_l {o : Oracle} {n : Nat} {B : Basis} {p : List Module} {k : Nat} {v : Val}
    {l : Log} (h : evProgram o n B p k = ⟨.value v, l, k⟩) :
    ∀ v' l', EvalProgramL B p v' l' → v' = v ∧ l' = l := by
  intro v' l' d
  rcases EvalProgramL.nostuck d o n k _ h with h1 | h1 | h1
  · simp at h1
  · simp at h1
  · simp only [Res.mk.injEq, Outcome.value.injEq] at h1; exact ⟨h1.1.symm, h1.2.1.symm⟩

theorem evModule_unique_l {o : Oracle} {n : Nat} {B : Basis} {m : Module} {k : Nat} {B' : Basis}
    {VE : ValEnv} {l : Log} (h : evModule o n B m k = ⟨.value (B', VE), l, k⟩) :
    ∀ B'' VE' l', EvalModuleL B m B'' VE' l' → B'' = B' ∧ VE' = VE ∧ l' = l := by
  intro B'' VE' l' d
  rcases EvalModuleL.nostuck d o n k _ h with h1 | h1 | h1
  · simp at h1
  · simp at h1
  · simp only [Res.mk.injEq, Outcome.value.injEq, Prod.mk.injEq] at h1
    exact ⟨h1.1.1.symm, h1.1.2.symm, h1.2.1.symm⟩

/-! ## Completeness (D1): every derivation is found by some choices and fuel -/

theorem EvalForcesL.complete : ∀ {E ys vs l}, EvalForcesL E ys vs l →
    ∃ (L : List Bool) (n : Nat), ∀ (o : Oracle) (k m : Nat), n ≤ m → Agrees o k L →
      evForces o m E ys k = ⟨.value vs, l, k + L.length⟩
  | _, _, _, _, .seq_nil_l E => ⟨[], 0, fun o k m _ _ => by simp [evForces]⟩
  | _, _, _, _, .seq_cons_l E y ys v vs l1 l2 h1 h2 => by
    obtain ⟨L1, n1, c1⟩ := EvalExpL.complete h1
    obtain ⟨L2, n2, c2⟩ := EvalForcesL.complete h2
    refine ⟨L1 ++ L2, max n1 n2, ?_⟩
    intro o k m hm hag
    obtain ⟨a1, a2⟩ := agrees2 hag
    simp only [evForces]
    rw [c1 o k m (by omega) a1]
    dsimp only
    rw [c2 o (k + L1.length) m (by omega) a2]
    simp [Nat.add_assoc]

theorem EvalTopDecL.complete : ∀ {E td I l}, EvalTopDecL E td I l →
    ∃ (L : List Bool) (n : Nat), ∀ (o : Oracle) (k m : Nat), n ≤ m → Agrees o k L →
      evTopDec o m E td k = ⟨.value I, l, k + L.length⟩
  | _, _, _, _, .r_dm_topdec_val_l E vb VE vs l1 l2 h0 h1 h2 => by
    obtain ⟨L1, n1, c1⟩ := EvalValBindL.complete h1
    obtain ⟨L2, n2, c2⟩ := EvalForcesL.complete h2
    refine ⟨L1 ++ L2, max n1 n2, ?_⟩
    intro o k m hm hag
    obtain ⟨a1, a2⟩ := agrees2 hag
    simp only [evTopDec, h0, ite_false]
    rw [c1 o k m (by omega) a1]
    dsimp only
    rw [c2 o (k + L1.length) m (by omega) a2]
    simp [Nat.add_assoc]
  | _, _, _, _, .r_dm_topdec_type_l E db CE VE h1 => by
    obtain ⟨e1, e2⟩ := h1.eq_ev
    exact ⟨[], 0, fun o k m _ _ => by simp [evTopDec, e1, e2]⟩
  | _, _, _, _, .r_dm_topdec_alias_l E tb RA VE h1 => by
    obtain ⟨e1, e2⟩ := h1.eq_ev
    exact ⟨[], 0, fun o k m _ _ => by simp [evTopDec, e1, e2]⟩
  | _, _, _, _, .r_dm_topdec_port_out_l E x τ => ⟨[], 0, fun o k m _ _ => by simp [evTopDec]⟩
  | _, _, _, _, .r_dm_topdec_port_in_l E x τ => ⟨[], 0, fun o k m _ _ => by simp [evTopDec]⟩
  | _, _, _, _, .r_dm_topdec_seq_l E t1 t2 RA1 CE1 VE1 I2 l1 l2 h1 h2 => by
    obtain ⟨L1, n1, c1⟩ := EvalTopDecL.complete h1
    obtain ⟨L2, n2, c2⟩ := EvalTopDecL.complete h2
    refine ⟨L1 ++ L2, max n1 n2, ?_⟩
    intro o k m hm hag
    obtain ⟨a1, a2⟩ := agrees2 hag
    simp only [evTopDec]
    rw [c1 o k m (by omega) a1]
    dsimp only
    rw [c2 o (k + L1.length) m (by omega) a2]
    simp [Nat.add_assoc]

theorem EvalModuleL.complete : ∀ {B m B' VE l}, EvalModuleL B m B' VE l →
    ∃ (L : List Bool) (n : Nat), ∀ (o : Oracle) (k m' : Nat), n ≤ m' → Agrees o k L →
      evModule o m' B m k = ⟨.value (B', VE), l, k + L.length⟩
  | _, _, _, _, _, .r_dm_module_l B hd is td E I mid I' l1 h1 h2 h3 => by
    obtain ⟨L, n, c⟩ := EvalTopDecL.complete h2
    refine ⟨L, n, ?_⟩
    intro o k m' hm hag
    simp only [evModule, h1.eq_ev]
    rw [c o k m' hm hag]
    simp [h3.eq_ev]

theorem EvalProgramL.complete : ∀ {B p v l}, EvalProgramL B p v l →
    ∃ (L : List Bool) (n : Nat), ∀ (o : Oracle) (k m : Nat), n ≤ m → Agrees o k L →
      evProgram o m B p k = ⟨.value v, l, k + L.length⟩
  | _, _, _, _, .r_p_dyn_module_l B m p B' VE v l1 l2 h1 h2 h3 => by
    obtain ⟨L1, n1, c1⟩ := EvalModuleL.complete h1
    obtain ⟨L2, n2, c2⟩ := EvalProgramL.complete h2
    obtain ⟨m2, p', rfl⟩ : ∃ m2 p', p = m2 :: p' := by
      cases p with
      | nil => exact absurd rfl h3
      | cons m2 p' => exact ⟨m2, p', rfl⟩
    refine ⟨L1 ++ L2, max n1 n2, ?_⟩
    intro o k m' hm hag
    obtain ⟨a1, a2⟩ := agrees2 hag
    simp only [evProgram]
    rw [c1 o k m' (by omega) a1]
    dsimp only
    rw [c2 o (k + L1.length) m' (by omega) a2]
    simp [Nat.add_assoc]
  | _, _, _, _, .r_p_dyn_main_l B m B' VE v l1 h1 h2 => by
    obtain ⟨L, n, c⟩ := EvalModuleL.complete h1
    refine ⟨L, n, ?_⟩
    intro o k m' hm hag
    simp only [evProgram]
    rw [c o k m' hm hag]
    simp [h2]

/-- D1 for programs: every derivation of a program's meaning is found by some choices and fuel. -/
theorem evProgram_complete {B : Basis} {p : List Module} {v : Val} (h : EvalProgram B p v) :
    ∃ (L : List Bool) (n : Nat), (evProgram (Oracle.ofList L) n B p 0).out = .value v := by
  obtain ⟨l, hl⟩ := EvalProgram.lift h
  obtain ⟨L, n, c⟩ := EvalProgramL.complete hl
  exact ⟨L, n, by rw [c (Oracle.ofList L) 0 n (Nat.le_refl n) (agrees_ofList L)]⟩

/-- A program has no meaning exactly when no choices and fuel give it one. -/
theorem noMeaning_iff {B : Basis} {p : List Module} :
    (¬ ∃ v, EvalProgram B p v) ↔ ∀ (L : List Bool) (n : Nat) (v : Val),
      (evProgram (Oracle.ofList L) n B p 0).out ≠ .value v := by
  constructor
  · intro h L n v hv; exact h ⟨v, evProgram_sound hv⟩
  · rintro h ⟨v, hv⟩
    obtain ⟨L, n, hc⟩ := evProgram_complete hv
    exact h L n v hc

end StandardElm.Mod
