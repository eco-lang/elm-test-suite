/-
  A Standard Definition of Elm? Mechanisation: the induction over the modules of two principal
  program derivations (plan step 10, `reduce_principal_unique`), given the module step
  (`ModuleStep`): two module derivations in one basis, each an instance of the other, give results
  that differ by a bijection of type names that fixes the basis.

  The bases of the two program derivations differ by a bijection of type names (`NRInv`). Module i
  of the second derivation, renamed back, is a derivation in the first one's basis
  (`nr_checkModule`), principal there with the first one's module i, so the two are instances of
  each other (`instanceOfMod_nr`); the module step relates their results, and the renamed-back
  module's value declarations to module i's by mutualInstanceMod_items; composing with the
  bijection relates them to module i of the second derivation (`ItemsRel.thenNames`).
-/
import StandardElmMech.Stat.ItemsCompose

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## Compositions of bijections of type names -/

section
variable {ρ σ ρ' σ' : List (TyName × TyName)}

/-- σ, then ρ. -/
def nrComp (ρ σ : List (TyName × TyName)) : List (TyName × TyName) := tnComp (nr σ) ρ

theorem nrComp_tn (t : TyName) : (nr (nrComp ρ σ)).tnApply t = (nr ρ).tnApply ((nr σ).tnApply t) :=
  thenNames_tn (r := nr σ) t

theorem NRInv.comp (h1 : NRInv ρ ρ') (h2 : NRInv σ σ') : NRInv (nrComp ρ σ) (nrComp σ' ρ') where
  h := ⟨fun t u e => by
          rw [nrComp_tn, nrComp_tn] at e
          exact h2.h.inj _ _ (h1.h.inj _ _ e),
        fun t => by rw [nrComp_tn, h1.h.ar, h2.h.ar],
        fun t ht => by rw [nrComp_tn, h2.h.t0 t ht, h1.h.t0 t ht]⟩
  h' := ⟨fun t u e => by
          rw [nrComp_tn, nrComp_tn] at e
          exact h1.h'.inj _ _ (h2.h'.inj _ _ e),
        fun t => by rw [nrComp_tn, h2.h'.ar, h1.h'.ar],
        fun t ht => by rw [nrComp_tn, h1.h'.t0 t ht, h2.h'.t0 t ht]⟩
  left := fun t => by rw [nrComp_tn, nrComp_tn, h1.left, h2.left]
  right := fun t => by rw [nrComp_tn, nrComp_tn, h2.right, h1.right]

variable {a b c : List (TyName × TyName)}

theorem nr_comp2_ty (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply t) (τ : Ty) :
    (nr a).ty ((nr b).ty τ) = (nr c).ty τ := by
  rw [nr_comp (c := c) (d := []) (by simpa using hc), nr_nil_ty]

theorem nr_comp2_scheme (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply t) (s : Scheme) :
    (nr a).scheme ((nr b).scheme s) = (nr c).scheme s := by
  simp [Renaming.scheme, nr_comp2_ty hc]

theorem nr_comp2_valEnv (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply t) (VE : ValEnv) :
    (nr a).valEnv ((nr b).valEnv VE) = (nr c).valEnv VE := by
  simp [Renaming.valEnv, List.map_map, Function.comp_def, nr_comp2_scheme hc]

theorem nr_comp2_tyEnv (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply t) (TE : TyEnv) :
    (nr a).tyEnv ((nr b).tyEnv TE) = (nr c).tyEnv TE := by
  simp [Renaming.tyEnv, List.map_map, Function.comp_def, Renaming.tyFcn, nr_comp2_ty hc, nr_comp2_valEnv hc]

theorem nr_comp2_iEnv (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply t) (I : IEnv) :
    (nr a).iEnv ((nr b).iEnv I) = (nr c).iEnv I := by
  simp [Renaming.iEnv, nr_comp2_tyEnv hc, nr_comp2_valEnv hc]

theorem nr_comp2_env (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply t) (E : Env) :
    (nr a).env ((nr b).env E) = (nr c).env E := by
  simp [Renaming.env, List.map_map, Function.comp_def, nr_comp2_iEnv hc, nr_comp2_tyEnv hc, nr_comp2_valEnv hc]

theorem nr_comp2_basis (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply t) (B : SBasis) :
    (nr a).basis ((nr b).basis B) = (nr c).basis B := by
  simp [Renaming.basis, Renaming.portEnv, List.map_map, Function.comp_def, hc, nr_comp2_iEnv hc,
    nr_comp2_ty hc]

theorem nr_basis_plus (h : NR a) (B B' : SBasis) :
    (nr a).basis (B.plus B') = ((nr a).basis B).plus ((nr a).basis B') := by
  simp only [SBasis.plus, Renaming.basis, unionL_map_inj _ h.inj, SBasis.mk.injEq, true_and]
  refine ⟨(modify_mapV (fun I => (nr a).iEnv I) B.ME B'.ME).symm, ?_⟩
  exact (modify_mapV (fun p : Dir × Ty => (p.1, (nr a).ty p.2)) B.PE B'.PE).symm

end

/-! ## What specialisation reads of a module and its result, by the erasure -/

def TopItem.portName? : TopItem → Option Var
  | .port x => some x
  | _ => none

def TopItem.typesPart? : TopItem → Option (Option Src.BDatBind × List Src.BTypBind)
  | .types db tbs => some (db, tbs)
  | _ => none

theorem portsOf_eq_names (PE : PortEnv) : ∀ is : List TopItem,
    portsOf PE is = (is.filterMap TopItem.portName?).mapM fun x =>
      match erasePort PE x with
      | some p => Except.ok p
      | none => Except.error SpecError.portType
  | [] => rfl
  | .port x :: rest => by
    simp only [portsOf, List.filterMap_cons, TopItem.portName?, List.mapM_cons, ← portsOf_eq_names PE rest]
    cases erasePort PE x <;> rfl
  | .value _ _ :: rest => by simp only [portsOf, List.filterMap_cons, TopItem.portName?]; exact portsOf_eq_names PE rest
  | .types _ _ :: rest => by simp only [portsOf, List.filterMap_cons, TopItem.portName?]; exact portsOf_eq_names PE rest

theorem eraseTypeDecs_eq_parts : ∀ is : List TopItem,
    eraseTypeDecs is = ((is.filterMap TopItem.typesPart?).map fun p => (eraseDatBind p.1, eraseTypBinds p.2)).foldr
      (fun p acc => (p.1 ++ acc.1, p.2 ++ acc.2)) ([], [])
  | [] => rfl
  | .types db tbs :: rest => by
    simp only [eraseTypeDecs, List.filterMap_cons, TopItem.typesPart?, List.map_cons, List.foldr_cons,
      eraseTypeDecs_eq_parts rest]
  | .value _ _ :: rest => by simp only [eraseTypeDecs, List.filterMap_cons, TopItem.typesPart?]; exact eraseTypeDecs_eq_parts rest
  | .port _ :: rest => by simp only [eraseTypeDecs, List.filterMap_cons, TopItem.typesPart?]; exact eraseTypeDecs_eq_parts rest

/-- The ports and type declarations of a top-level phrase, by its erasure. -/
def bPortNames : Src.BTopDec → List Var
  | .port x _ => [x]
  | .seq a b => bPortNames a ++ bPortNames b
  | _ => []

def bTypesParts : Src.BTopDec → List (Option Src.BDatBind × List Src.BTypBind)
  | .types db tbs => [(db, tbs)]
  | .seq a b => bTypesParts a ++ bTypesParts b
  | _ => []

theorem items_portNames : ∀ d : ATopDec, d.items.filterMap TopItem.portName? = bPortNames d.erase
  | .value _ _ => rfl
  | .types _ _ _ _ => rfl
  | .port _ _ _ => rfl
  | .seq a b => by
    simp [ATopDec.items, ATopDec.erase, bPortNames, List.filterMap_append, items_portNames a,
      items_portNames b]

theorem items_typesParts : ∀ d : ATopDec, d.items.filterMap TopItem.typesPart? = bTypesParts d.erase
  | .value _ _ => rfl
  | .types _ _ _ _ => rfl
  | .port _ _ _ => rfl
  | .seq a b => by
    simp [ATopDec.items, ATopDec.erase, bTypesParts, List.filterMap_append, items_typesParts a,
      items_typesParts b]

theorem module_portNames {m m' : AModule} (he : m'.erase = m.erase) :
    ((m'.body.map ATopDec.items).getD []).filterMap TopItem.portName? =
      ((m.body.map ATopDec.items).getD []).filterMap TopItem.portName? := by
  have hb : m'.body.map ATopDec.erase = m.body.map ATopDec.erase := congrArg Src.BModule.body he
  cases h1 : m.body <;> cases h2 : m'.body <;> rw [h1, h2] at hb <;> simp_all [items_portNames]

theorem module_typesParts {m m' : AModule} (he : m'.erase = m.erase) :
    ((m'.body.map ATopDec.items).getD []).filterMap TopItem.typesPart? =
      ((m.body.map ATopDec.items).getD []).filterMap TopItem.typesPart? := by
  have hb : m'.body.map ATopDec.erase = m.body.map ATopDec.erase := congrArg Src.BModule.body he
  cases h1 : m.body <;> cases h2 : m'.body <;> rw [h1, h2] at hb <;> simp_all [items_typesParts]

theorem erasePort_nr {ρ : List (TyName × TyName)} (h : NR ρ) (PE : PortEnv) (x : Var) :
    erasePort ((nr ρ).portEnv PE) x = erasePort PE x := by
  unfold erasePort
  have e : FMap.find? ((nr ρ).portEnv PE) x = (FMap.find? PE x).map fun q => (q.1, (nr ρ).ty q.2) := by
    induction PE with
    | nil => rfl
    | cons p ps ih =>
      simp only [Renaming.portEnv, List.map_cons, FMap.find?] at ih ⊢
      split <;> simp_all
  rw [e]
  cases FMap.find? PE x with
  | none => rfl
  | some p => simp only [Option.map_some]; rw [toPTy_rename h.wf]

/-! ## The module step and the induction -/

/-- Every type name of a basis's interfaces and ports is in its `T`, `T0` is, and its interfaces
    have no free variables. -/
structure BasisInv (B : SBasis) : Prop where
  t0 : ∀ t ∈ T0, t ∈ B.T
  names : ∀ p ∈ B.ME, ∀ t ∈ p.2.tynames, t ∈ B.T
  pe : ∀ p ∈ B.PE, ∀ t ∈ p.2.2.tynames, t ∈ B.T
  closed : ∀ p ∈ B.ME, p.2.tyvars = []

/-- What the module step gives: a bijection of type names fixing the basis that takes the first
    derivation's result to the second's, and the invariant of the next basis. -/
def StepOut (B : SBasis) (m m2 : AModule) : Prop :=
  ∃ σ σ' R E, NRInv σ σ' ∧ (nr σ).basis B = B ∧ m.result B = some (R, E) ∧
    m2.result B = some ((nr σ).basis R, (nr σ).env E) ∧ BasisInv (B.plus R)

/-- The module step (step 10's lemma on mutual instances, for results), with the hypothesis on the
    module's type declarations it needs, `hyp`. -/
def ModuleStep (hyp : Src.BModule → Prop) : Prop :=
  ∀ (B : SBasis) (m m2 : AModule), BasisInv B → hyp m.erase → checkModule B m = true → checkModule B m2 = true →
    m.NoFreeBnd → m2.NoFreeBnd → InstanceOfMod B m2 m → InstanceOfMod B m m2 → StepOut B m m2

/-- Every module principal in the basis the earlier ones build. -/
def AllPrincipal : SBasis → AProgram → Prop
  | _, [] => True
  | B, m :: ms => IsPrincipalMod B m ∧ ∀ R E, m.result B = some (R, E) → AllPrincipal (B.plus R) ms

theorem allPrincipal_of : ∀ {B : SBasis} {a : AProgram} {Bs : List SBasis}, AProgram.bases B a = some Bs →
    (∀ i (h : i < a.length) (h' : i < Bs.length), IsPrincipalMod Bs[i] a[i]) → AllPrincipal B a
  | _, [], _, _, _ => trivial
  | B, m :: ms, Bs, hb, hp => by
    simp only [AProgram.bases] at hb
    cases hr : m.result B with
    | none => rw [hr] at hb; cases hb
    | some p =>
      obtain ⟨R, E⟩ := p
      rw [hr] at hb
      simp only at hb
      cases hb' : AProgram.bases (B.plus R) ms with
      | none => rw [hb'] at hb; cases hb
      | some Bs' =>
        rw [hb'] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        refine ⟨hp 0 (by simp) (by simp), fun R' E' e => ?_⟩
        rw [hr] at e
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact allPrincipal_of hb' fun i h h' => by
          have := hp (i + 1) (by simp; omega) (by simp; omega)
          simpa using this

theorem mainScheme_cons_cons (x y : SBasis × SBasis × Env) (rest : List (SBasis × SBasis × Env)) :
    mainScheme (x :: y :: rest) = mainScheme (y :: rest) := rfl

section Induction
variable {hyp : Src.BModule → Prop}

theorem prog_rel (hstep : ModuleStep hyp) : ∀ (a a' : AProgram) (B : SBasis) (ρ ρ' : List (TyName × TyName))
    (rs rs' : List (SBasis × SBasis × Env)),
    NRInv ρ ρ' → BasisInv B → (∀ m ∈ a, hyp m.erase) → a'.map AModule.erase = a.map AModule.erase →
    AllPrincipal B a → AllPrincipal ((nr ρ).basis B) a' →
    progResults B a = some rs → progResults ((nr ρ).basis B) a' = some rs' →
    ProgRel a rs a' rs' ∧ (mainScheme rs').bind mainKind = (mainScheme rs).bind mainKind
  | [], [], _, _, _, rs, rs', _, _, _, _, _, _, h1, h2 => by
    simp only [progResults, Option.some.injEq] at h1 h2
    subst h1; subst h2
    exact ⟨trivial, rfl⟩
  | m :: ms, m' :: ms', B, ρ, ρ', rs, rs', hi, hB, hyps, he, hp, hp', h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at he
    obtain ⟨hem, hems⟩ := he
    have h := hi.h
    -- the second module renamed back, and the first renamed
    have hPm := hp.1
    have hPm' := hp'.1
    have hback : (m'.rename (nr ρ')).rename (nr ρ) = m' := nr_inv_module hi.right m'
    have hB' : (nr ρ').basis ((nr ρ).basis B) = B := nr_inv_basis hi.left B
    have hc'' : checkModule B (m'.rename (nr ρ')) = true := by
      rw [← hB', nr_checkModule hi.h', hPm'.1]
    have hn'' : (m'.rename (nr ρ')).NoFreeBnd := nr_noFreeBnd hi.symm hPm'.2.1
    have he'' : (m'.rename (nr ρ')).erase = m.erase := by rw [AModule.erase_rename, hem]
    have hI1 : InstanceOfMod B (m'.rename (nr ρ')) m := hPm.2.2 _ hc'' hn'' he''
    have hcs : checkModule ((nr ρ).basis B) (m.rename (nr ρ)) = true := by rw [nr_checkModule h, hPm.1]
    have hI2' : InstanceOfMod ((nr ρ).basis B) (m.rename (nr ρ)) m' :=
      hPm'.2.2 _ hcs (nr_noFreeBnd hi hPm.2.1) (by rw [AModule.erase_rename, hem])
    have hI2 : InstanceOfMod B m (m'.rename (nr ρ')) := by
      have := instanceOfMod_nr hi.symm hI2'
      rwa [hB', nr_inv_module hi.left] at this
    obtain ⟨σ, σ', R, E, hσ, hfix, hr, hr'', hBn⟩ :=
      hstep B m (m'.rename (nr ρ')) hB (hyps m (List.mem_cons_self ..)) hPm.1 hc'' hPm.2.1 hn'' hI1 hI2
    -- the second derivation's result
    have hr' : m'.result ((nr ρ).basis B) = some ((nr ρ).basis ((nr σ).basis R), (nr ρ).env ((nr σ).env E)) := by
      rw [← hback, nr_result h, hr'']; rfl
    simp only [progResults, hr, hr'] at h1 h2
    cases hrest : progResults (B.plus R) ms with
    | none => rw [hrest] at h1; cases h1
    | some rs0 =>
      rw [hrest] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      have hcomp := fun t => (nrComp_tn (ρ := ρ) (σ := σ) t).symm
      have hBnext : ((nr ρ).basis B).plus ((nr ρ).basis ((nr σ).basis R)) = (nr (nrComp ρ σ)).basis (B.plus R) := by
        rw [nr_basis_plus (hi.comp hσ).h, ← nr_comp2_basis hcomp, ← nr_comp2_basis hcomp, hfix]
      rw [hBnext] at h2
      cases hrest' : progResults ((nr (nrComp ρ σ)).basis (B.plus R)) ms' with
      | none => rw [hrest'] at h2; cases h2
      | some rs0' =>
        rw [hrest'] at h2
        simp only [Option.map_some, Option.some.injEq] at h2
        subst h2
        have hp2 : AllPrincipal (B.plus R) ms := hp.2 R E hr
        have hp2' : AllPrincipal ((nr (nrComp ρ σ)).basis (B.plus R)) ms' := by
          rw [← hBnext]; exact hp'.2 _ _ hr'
        obtain ⟨hrel, hmain⟩ := prog_rel hstep ms ms' (B.plus R) _ _ rs0 rs0' (hi.comp hσ) hBn
          (fun x hx => hyps x (List.mem_cons_of_mem _ hx)) hems hp2 hp2' hrest hrest'
        -- the module's part of ProgRel
        obtain ⟨r0, D, hr0, hit⟩ := mutualInstanceMod_items hB.t0 hPm.1 hc'' hPm.2.1 hn'' hI1 hI2
        have hmod : ModResRel m (B, R, E) m' ((nr ρ).basis B, (nr ρ).basis ((nr σ).basis R), (nr ρ).env ((nr σ).env E)) := by
          refine ⟨congrArg Src.BModule.header hem, congrArg Src.BModule.imports hem, ?_, ?_, ?_, ?_⟩
          · show (elabImports ((nr ρ).basis B) π0 (defaultImports ++ m'.imports)).getD [] = _
            rw [nr_elabImports]
            exact congrArg (fun i => (elabImports B π0 (defaultImports ++ i)).getD []) (congrArg Src.BModule.imports hem)
          · simp only [portsOf_eq_names, module_portNames hem]
            show (List.mapM _ _ : Except SpecError _) = List.mapM _ _
            congr 1
            funext x
            simp only [Renaming.basis]
            rw [erasePort_nr h, erasePort_nr hσ.h]
          · rw [eraseTypeDecs_eq_parts, eraseTypeDecs_eq_parts, module_typesParts hem]
          · refine ⟨r0.thenNames ρ, D, thenNames_wf hr0 h, ?_⟩
            have := ItemsRel.thenNames hr0 h hit
            have hv : ∀ (mm : AModule), valuesOnly (((mm.rename (nr ρ)).body.map ATopDec.items).getD []) =
                (valuesOnly ((mm.body.map ATopDec.items).getD [])).map (TopItem.nrn ρ) := by
              intro mm; rw [nr_rename_body]
              cases mm.body with
              | none => rfl
              | some d => simp only [Option.map_some, Option.getD_some, items_nr]; exact valuesOnly_nr _
            rw [← hback, hv]; exact this
        refine ⟨⟨hmod, hrel⟩, ?_⟩
        cases ms with
        | nil =>
          cases ms' with
          | nil =>
            simp only [progResults, Option.some.injEq] at hrest hrest'
            subst hrest; subst hrest'
            simp only [mainScheme, Renaming.env, nr_valEnv_find]
            cases FMap.find? E.VE "main" with
            | none => rfl
            | some b =>
              obtain ⟨s, st⟩ := b
              cases st with
              | c => rfl
              | v =>
                simp only [Option.map_some, Option.bind_some]
                rw [mainKind_rename h.wf, mainKind_rename hσ.h.wf]
          | cons _ _ => simp at hems
        | cons m2 ms2 =>
          cases ms' with
          | nil => simp at hems
          | cons m2' ms2' =>
            cases rs0 with
            | nil =>
              have := progResults_length hrest; simp at this
            | cons x xs =>
              cases rs0' with
              | nil => have := progResults_length hrest'; simp at this
              | cons y ys => rw [mainScheme_cons_cons, mainScheme_cons_cons]; exact hmain
  | [], _ :: _, _, _, _, _, _, _, _, _, he, _, _, _, _ | _ :: _, [], _, _, _, _, _, _, _, _, he, _, _, _, _ => by
    simp at he

end Induction

end StandardElm.Stat
