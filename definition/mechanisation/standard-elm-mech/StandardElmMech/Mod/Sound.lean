/-
  A Standard Definition of Elm? Mechanisation: soundness of the evaluator of Chapter 7 (Mod/Eval.lean)
  for the rules (Mod/Rules.lean, Mod/RulesL.lean), plan step 2. The functional parts are sound
  outright; the others, for every oracle and fuel, by induction on syntax with the Core's soundness.
-/
import StandardElmMech.Mod.Eval
import StandardElmMech.Sound

namespace StandardElm.Mod
open StandardElm StandardElm.Eff

theorem evExpItem_sound {I : Interface} {it : ExpItem} {I' : Interface} :
    evExpItem I it = some I' → EvalExpItem I it I' := by
  cases it with
  | var x =>
    simp only [evExpItem, Option.map_eq_some_iff]
    rintro ⟨v, hv, rfl⟩; exact .r_dm_expitem_var I x v hv
  | op o => simp only [evExpItem, Option.some.injEq]; rintro rfl; exact .r_dm_expitem_op I o
  | tycon t =>
    simp only [evExpItem]
    split
    · rename_i hRA
      simp only [Option.map_eq_some_iff]
      rintro ⟨v, hv, rfl⟩; exact .r_dm_expitem_alias I t v hRA hv
    · rename_i hRA
      simp only [Option.some.injEq]; rintro rfl
      exact .r_dm_expitem_type I t _ hRA rfl
  | opened t =>
    simp only [evExpItem, Option.map_eq_some_iff]
    rintro ⟨VE, hVE, rfl⟩; exact .r_dm_expitem_open I t VE hVE

theorem evExpItems_sound {I : Interface} : ∀ {is : List ExpItem} {Is : List Interface},
    evExpItems I is = some Is → EvalExpItems I is Is
  | [], Is, h => by simp only [evExpItems, Option.some.injEq] at h; subst h; exact .seq_nil I
  | it :: is, Is, h => by
    simp only [evExpItems] at h
    split at h
    · rename_i I1 Is' h1 h2
      simp only [Option.some.injEq] at h; subst h
      exact .seq_cons I it is I1 Is' (evExpItem_sound h1) (evExpItems_sound h2)
    · cases h

theorem evExpList_sound {I : Interface} {el : ExpList} {I' : Interface} :
    evExpList I el = some I' → EvalExpList I el I' := by
  cases el with
  | all => simp only [evExpList, Option.some.injEq]; rintro rfl; exact .r_dm_explist_all I
  | items is =>
    cases is with
    | nil => simp [evExpList]
    | cons it rest =>
      simp only [evExpList, Option.map_eq_some_iff]
      rintro ⟨Is, h, rfl⟩
      exact .r_dm_explist_items I (it :: rest) Is (by simp) (evExpItems_sound h)

theorem evExpListOpt_sound {I : Interface} {el : Option ExpList} {I' : Option Interface} :
    evExpListOpt I el = some I' → EvalExpListOpt I el I' := by
  cases el with
  | none => simp only [evExpListOpt, Option.some.injEq]; rintro rfl; exact .opt_none I
  | some el =>
    simp only [evExpListOpt, Option.map_eq_some_iff]
    rintro ⟨I'', h, rfl⟩; exact .opt_some I el I'' (evExpList_sound h)

theorem evHeader_sound {I : Interface} {h : Header} {m : ModId} {I' : Interface} :
    evHeader I h = some (m, I') → EvalHeader I h m I' := by
  obtain ⟨isPort, mid, el⟩ := h
  simp only [evHeader, Option.map_eq_some_iff, Prod.mk.injEq]
  rintro ⟨I'', hl, rfl, rfl⟩
  exact .r_dm_header I isPort mid el I'' (evExpList_sound hl)

theorem evImports_sound {B : Basis} : ∀ {is : List Import} {E : Env},
    evImports B is = some E → EvalImports B is E
  | [], E, h => by simp only [evImports, Option.some.injEq] at h; subst h; exact .r_dm_imports_empty B
  | ⟨m, q, el⟩ :: rest, E, h => by
    simp only [evImports] at h
    split at h
    · rename_i I hI
      split at h
      · rename_i I' E' h1 h2
        simp only [Option.some.injEq] at h; subst h
        exact .r_dm_imports_import B m q el rest I I' E' hI (evExpListOpt_sound h1) (evImports_sound h2)
      · cases h
    · cases h

mutual
theorem evConBind_sound : ∀ (cb : ConBind), EvalConBind cb (evConBind cb)
  | .mk c rest => by
    simp only [evConBind]
    exact .r_dm_conbind c rest _ (evConBindOpt_sound rest)
theorem evConBindOpt_sound : ∀ (cb : Option ConBind), EvalConBindOpt cb (evConBindOpt cb)
  | none => by simp only [evConBindOpt]; exact .opt_none
  | some cb => by simp only [evConBindOpt]; exact .opt_some cb _ (evConBind_sound cb)
end

mutual
theorem evDatBind_sound : ∀ (db : DatBind), EvalDatBind db (evDatBind db).1 (evDatBind db).2
  | .mk t cb rest => by
    simp only [evDatBind]
    exact .r_dm_datbind t cb rest _ _ _ (evConBind_sound cb) (evDatBindOpt_sound rest)
theorem evDatBindOpt_sound : ∀ (db : Option DatBind), EvalDatBindOpt db (evDatBindOpt db).1 (evDatBindOpt db).2
  | none => by simp only [evDatBindOpt]; exact .opt_none
  | some db => by simp only [evDatBindOpt]; exact .opt_some db _ _ (evDatBind_sound db)
end

theorem evTypBind_sound (tb : TypBind) : EvalTypBind tb (evTypBind tb).1 (evTypBind tb).2 := by
  obtain ⟨t, ls⟩ := tb
  exact .r_dm_typbind t ls

theorem evForces_sound_l {o : Oracle} {n : Nat} {E : Env} : ∀ {ys : List Var} {k : Nat} {vs : List Val}
    {l : Log} {k' : Nat}, evForces o n E ys k = ⟨.value vs, l, k'⟩ → EvalForcesL E ys vs l
  | [], k, vs, l, k', h => by
    simp only [evForces, Res.mk.injEq, Outcome.value.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact .seq_nil_l E
  | y :: ys, k, vs, l, k', h => by
    simp only [evForces] at h
    split at h
    · rename_i v l1 k1 h1
      split at h
      · rename_i vs' l2 k2 h2
        simp only [Res.mk.injEq, Outcome.value.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .seq_cons_l E y ys v vs' l1 l2 (evExp_sound_l h1) (evForces_sound_l h2)
      all_goals simp at h
    all_goals simp at h

theorem evTopDec_sound_l {o : Oracle} {n : Nat} : ∀ {E : Env} {td : TopDec} {k : Nat} {I : Interface}
    {l : Log} {k' : Nat}, evTopDec o n E td k = ⟨.value I, l, k'⟩ → EvalTopDecL E td I l
  | E, .val vb, k, I, l, k', h => by
    simp only [evTopDec] at h
    split at h
    · simp at h
    · rename_i hne
      split at h
      · rename_i VE l1 k1 h1
        split at h
        · rename_i vs l2 k2 h2
          simp only [Res.mk.injEq, Outcome.value.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .r_dm_topdec_val_l E vb VE vs l1 l2 hne (evValBind_sound_l h1) (evForces_sound_l h2)
        all_goals simp at h
      all_goals simp at h
  | E, .type db, k, I, l, k', h => by
    simp only [evTopDec, Res.mk.injEq, Outcome.value.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .r_dm_topdec_type_l E db _ _ (evDatBind_sound db)
  | E, .alias tb, k, I, l, k', h => by
    simp only [evTopDec, Res.mk.injEq, Outcome.value.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .r_dm_topdec_alias_l E tb _ _ (evTypBind_sound tb)
  | E, .port x .out τ, k, I, l, k', h => by
    simp only [evTopDec, Res.mk.injEq, Outcome.value.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .r_dm_topdec_port_out_l E x τ
  | E, .port x .inn τ, k, I, l, k', h => by
    simp only [evTopDec, Res.mk.injEq, Outcome.value.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .r_dm_topdec_port_in_l E x τ
  | E, .seq t1 t2, k, I, l, k', h => by
    simp only [evTopDec] at h
    split at h
    · rename_i I1 l1 k1 h1
      split at h
      · rename_i I2 l2 k2 h2
        simp only [Res.mk.injEq, Outcome.value.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have d1 := evTopDec_sound_l h1
        obtain ⟨RA1, CE1, VE1⟩ := I1
        exact .r_dm_topdec_seq_l E t1 t2 RA1 CE1 VE1 I2 l1 l2 d1 (evTopDec_sound_l h2)
      all_goals simp at h
    all_goals simp at h

theorem evModule_sound_l {o : Oracle} {n : Nat} {B : Basis} {m : Module} {k : Nat} {B' : Basis}
    {VE : ValEnv} {l : Log} {k' : Nat} :
    evModule o n B m k = ⟨.value (B', VE), l, k'⟩ → EvalModuleL B m B' VE l := by
  obtain ⟨hd, is, td⟩ := m
  simp only [evModule]
  intro h
  split at h
  · rename_i E hE
    split at h
    · rename_i I l1 k1 h1
      split at h
      · rename_i mid I' hh
        simp only [Res.mk.injEq, Outcome.value.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
        exact .r_dm_module_l B hd is td E I mid I' l1 (evImports_sound hE) (evTopDec_sound_l h1)
          (evHeader_sound hh)
      · simp at h
    all_goals simp at h
  · simp at h

theorem evProgram_sound_l {o : Oracle} {n : Nat} : ∀ {B : Basis} {p : List Module} {k : Nat} {v : Val}
    {l : Log} {k' : Nat}, evProgram o n B p k = ⟨.value v, l, k'⟩ → EvalProgramL B p v l
  | B, [], k, v, l, k', h => by simp [evProgram] at h
  | B, [m], k, v, l, k', h => by
    simp only [evProgram] at h
    split at h
    · rename_i B' VE l1 k1 h1
      split at h
      · rename_i w hw
        simp only [Res.mk.injEq, Outcome.value.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .r_p_dyn_main_l B m B' VE w l1 (evModule_sound_l h1) hw
      · simp at h
    all_goals simp at h
  | B, m :: m2 :: p, k, v, l, k', h => by
    simp only [evProgram] at h
    split at h
    · rename_i B' VE l1 k1 h1
      split at h
      · rename_i w l2 k2 h2
        simp only [Res.mk.injEq, Outcome.value.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .r_p_dyn_module_l B m (m2 :: p) B' VE w l1 l2 (evModule_sound_l h1)
          (evProgram_sound_l h2) (by simp)
      all_goals simp at h
    all_goals simp at h

theorem evProgram_sound {o : Oracle} {n : Nat} {B : Basis} {p : List Module} {k : Nat} {v : Val} :
    (evProgram o n B p k).out = .value v → EvalProgram B p v := by
  intro h
  rcases hr : evProgram o n B p k with ⟨out, l, k'⟩
  rw [hr] at h; simp only at h; subst h
  exact EvalProgramL.forget (evProgram_sound_l hr)

end StandardElm.Mod
