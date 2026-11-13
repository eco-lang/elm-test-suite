/-
  A Standard Definition of Elm? Mechanisation: the discharge of D11 (milestone (g) of plan step 11,
  "Discharge"). The per-test theorems of steps 9 and 10 were stated under D11 for the program
  (`InferPrincipalFor`, `D11For`: what step 9's unverified inference returns is principal). Here
  they are proved without it, from the proved inference: module- and program-level W
  (`MW.inferProgramW`) returns a principal derivation of every module in the basis the earlier ones
  build (`MW.inferProgramW_principal`, milestone (f)), so its derivation of the program is the one
  `ElProgram`, `SpecOf` and `ProgramSem` ask for.

  * `wCheck B s q`: W elaborates the program's modules; the derivation's results meet Chapter 9's
    side conditions (ports, the type of `main`: `checksAll`) and the further restrictions of every
    module; and, when `q = some r`, specialisation and erasure give `r`. The kernel decides it per
    test (`decide +kernel`, or `native_decide` where the memory budget is broken).
  * `legal_of_wCheck`: the program is legal (step 9's `legal_X`, without hypothesis).
  * `ident_of_wCheck`, `programSem_of_wCheck`: step 10's `ident_X` and `mean_X` without hypothesis.
  * `a96_number_flags`'s method (`not_legal_of_wMainVar`): when W's principal scheme of `main` is
    that of a worker whose flags type is a type variable, no derivation of the program gives `main`
    a type of Chapter 9: every principal derivation differs from W's by a bijection of type names
    fixing the basis (step 10's module step), which takes a variable to itself, and a variable is
    not a port type.

  The theorems stated under `InferPrincipalFor` (step 9's `legal_of_infer`, step 10's
  `ident_of_spec'`, ...) are kept: they say what the unverified inference gives under D11. No
  per-test theorem uses them any more.
-/
import StandardElmMech.Stat.Complete.ModulesProgram

namespace StandardElm.Stat
open StandardElm.Stat.Complete
open StandardElm.Src (BModule BProgram SProgram)

/-! ## The check -/

/-- The further restrictions of every module of a program derivation, each in the basis the earlier
    ones build. -/
def furtherAllB (B : SBasis) : AProgram → Bool
  | [] => true
  | a :: rest =>
    match a.result B with
    | some (B', E) => furtherModInB B E a && furtherAllB (B.plus B') rest
    | none => false

/-- W's derivation of the program, checked: Chapter 9's side conditions, the further restrictions,
    and (for `some r`) the reduced program. -/
def wCheck (B : SBasis) (s : SProgram) (q : Option Mod.Reduced) : Bool :=
  Src.decSynOK s &&
  match MW.inferProgramW MW.wFuel B (bareOf s).modules with
  | .ok as =>
    match progResults B as with
    | some rs =>
      checksAll rs && furtherAllB B as &&
        match q with
        | none => true
        | some r =>
          match reduceWith B as rs with
          | .ok r' => decide (r' = r)
          | .error _ => false
    | none => false
  | _ => false

theorem furtherAll_mod : ∀ {B : SBasis} {a : AProgram} {Bs : List SBasis}, furtherAllB B a = true →
    AProgram.bases B a = some Bs → ∀ i (h : i < a.length) (h' : i < Bs.length), FurtherMod Bs[i] a[i]
  | _, [], _, _, _, i, h, _ => absurd h (by simp)
  | B, m :: rest, Bs, hf, hb, i, h, h' => by
    simp only [furtherAllB] at hf
    simp only [AProgram.bases] at hb
    cases hm : m.result B with
    | none => rw [hm] at hf; cases hf
    | some p =>
      obtain ⟨B', E⟩ := p
      rw [hm] at hf hb
      simp only [Bool.and_eq_true] at hf
      simp only at hb
      cases hbr : AProgram.bases (B.plus B') rest with
      | none => rw [hbr] at hb; cases hb
      | some Bs' =>
        rw [hbr] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        cases i with
        | zero =>
          show FurtherMod B m
          unfold FurtherMod; rw [hm]; exact furtherModInB_sound hf.1
        | succ j =>
          exact furtherAll_mod hf.2 hbr j (by simpa using h) (by simpa using h')

/-- What a successful check says. -/
theorem wCheck_inv {B : SBasis} {s : SProgram} {q : Option Mod.Reduced} (hB : BasisInv B)
    (h : wCheck B s q = true) :
    Src.SynOK s ∧ ∃ as rs, MW.inferProgramW MW.wFuel B (bareOf s).modules = .ok as ∧
      PrincipalProgDeriv B (bareOf s) as ∧ progResults B as = some rs ∧ checksAll rs = true ∧
      furtherAllB B as = true ∧ ∀ r, q = some r → reduceWith B as rs = .ok r := by
  unfold wCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hsyn, h⟩ := h
  refine ⟨(Src.decSynOK_iff s).mp hsyn, ?_⟩
  split at h
  · rename_i as hw
    split at h
    · rename_i rs hr
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hc, hf⟩, hq⟩ := h
      refine ⟨as, rs, hw, MW.inferProgramW_principal hB hw, hr, hc, hf, fun r hrq => ?_⟩
      subst hrq
      simp only at hq
      split at hq
      · rename_i r' hr'
        simp only [decide_eq_true_eq] at hq
        rw [hr', hq]
      · cases hq
    · cases h
  · cases h

/-! ## Legality, the specialisation of the program, its meaning -/

/-- Step 9's legality, without hypothesis: the program is legal when W's derivation of it passes the
    checks. -/
theorem legal_of_wCheck {B : SBasis} {s : SProgram} {q : Option Mod.Reduced} (hB : BasisInv B)
    (h : wCheck B s q = true) : LegalProgram B s := by
  obtain ⟨hsyn, as, rs, -, ⟨⟨-, he⟩, Bs, hBs, hpr⟩, hr, hc, hf, -⟩ := wCheck_inv hB h
  have hne : as ≠ [] := by
    rintro rfl
    simp [progResults] at hr; subst hr
    simp [checksAll, mainScheme] at hc
  obtain ⟨τ, PE, hel⟩ := elProgram_of_results B as Bs rs hr hBs hpr (furtherAll_mod hf hBs) hc hne
  refine ⟨Src.synOKSet_of_synOK hsyn, τ, PE, ?_⟩
  show ElProgram B (bareOf s).modules τ PE
  rw [← he]; exact hel

/-- The reduced program the check names is a specialisation of the program. -/
theorem specOf_of_wCheck {B : SBasis} {s : SProgram} {r : Mod.Reduced} (hB : BasisInv B)
    (h : wCheck B s (some r) = true) : SpecOf B (bareOf s) r := by
  obtain ⟨-, as, rs, -, hp, hr, -, -, hq⟩ := wCheck_inv hB h
  exact ⟨as, hp, by simp only [reduceProgram, hr]; exact hq r rfl⟩

/-- Every module W elaborates has ordered type declarations. -/
theorem typesOrdered_of_inferProgramW {fuel : Nat} : ∀ (ms : List BModule) (B : SBasis) (as : AProgram),
    BasisInv B → MW.inferProgramW fuel B ms = .ok as → ∀ m ∈ ms, TypesOrdered m
  | [], _, _, _, _, m, hm => absurd hm (by simp)
  | m :: ms, B, as, hB, h, m', hm' => by
    simp only [MW.inferProgramW] at h
    split at h
    · rename_i a hw
      obtain ⟨he, -, R, E, hr, hBn⟩ := MW.step_ok hB hw
      rw [hr] at h
      simp only at h
      rcases List.mem_cons.mp hm' with rfl | hm'
      · obtain ⟨C, hC⟩ := MW.importCtx_of_ok hw
        exact MW.typesOrdered_of_W hw hC
      · cases hrest : MW.inferProgramW fuel (B.plus R) ms with
        | ok as' => exact typesOrdered_of_inferProgramW ms (B.plus R) as' hBn hrest m' hm'
        | fail => rw [hrest] at h; cases h
        | other => rw [hrest] at h; cases h
    · cases h
    · cases h

/-- Step 10's `ident_X`, without hypothesis: the specialisation of the program is unique, and is the
    reduced program the check names. -/
theorem ident_of_wCheck {s : SProgram} {q : Mod.Reduced} (h : wCheck Btest s (some q) = true) :
    ∀ r, SpecOf Btest (bareOf s) r → r = q := by
  obtain ⟨-, as, -, hw, -⟩ := wCheck_inv Btest_inv h
  have hT := typesOrdered_of_inferProgramW _ _ _ Btest_inv hw
  exact fun r hr => specOf_functional MStep.moduleStep Btest_inv hT hr (specOf_of_wCheck Btest_inv h)

/-- Step 10's `mean_X`, without hypothesis: r:p-program with both premises, from the check and a
    value of the reduced modules (Part I's `t_X`). -/
theorem programSem_of_wCheck {s : SProgram} {q : Mod.Reduced} (h : wCheck Btest s (some q) = true)
    (hv : ∃ v, DynOf q v) : ∃ τ PE v, ProgramSem Btest (bareOf s) (τ, PE, v) := by
  obtain ⟨-, τ, PE, hel⟩ := legal_of_wCheck Btest_inv h
  obtain ⟨v, hd⟩ := hv
  exact ⟨τ, PE, v, .r_p_program hel (specOf_of_wCheck Btest_inv h) hd⟩

/-- The per-test forms, in the test basis. -/
theorem legal_of_W {s : SProgram} {q : Option Mod.Reduced} (h : wCheck Btest s q = true) :
    LegalProgram Btest s :=
  legal_of_wCheck Btest_inv h

/-! ## The check with the context of the imports given

In the kernel, the context of a module's imports (`importCtx`: the environment the default imports
and the module's own give) is about half the cost of `wCheck` on a small program, and W, the checker
and `namesB` each ask for it. `wCheckIn B imps C s q` is `wCheck B s q` for a program of one module
whose imports are `imps`, with the context read from `C`; given `importCtx B imps = some C`, proved
once per list of imports (`ctx_<k>_eq`, Certs/Ctx_*.lean), it gives `wCheck` (`wCheck_of_ctx`), so
a per-test theorem is

    theorem wcheck_X : Stat.wCheck Stat.Btest s_X (some g_X.reduced) = true :=
      Stat.wCheck_of_ctx ctx_k_eq (by decide +kernel)

with the statement unchanged. -/

/-- `nodesModule` with the context of the imports given. -/
def nodesModuleIn (C : Ctx) (a : AModule) : List Node :=
  match a.body with
  | some d => nodesTopDec C [] d
  | none => []

/-- `MW.namesB` with the context of the imports given. -/
def namesBIn (B : SBasis) (C : Ctx) (a : AModule) : Bool :=
  let ok : TyName → Bool := fun t => decide (t ∈ B.T) || decide (t ∈ genNames B a)
  (nodesModuleIn C a).all fun n =>
    n.tys.all (fun τ => τ.tynames.all ok) && n.schemes.all fun σ => σ.body.tynames.all ok

/-- `MW.finish` with the context of the imports given. -/
def finishIn (B : SBasis) (C : Ctx) (a : AModule) : MW.MRes :=
  if (a.resultIn B C).isSome && namesBIn B C a then .ok a else .internal

/-- `MW.valuesW` with the context of the imports given. -/
def valuesWIn (fuel : Nat) (B : SBasis) (C : Ctx) (m : BModule) (at? : Option ATopDec) (C1 : Ctx) :
    Option Src.BTopDec → MW.MRes
  | none => finishIn B C ⟨m.header, m.imports, MW.joinBody at? none⟩
  | some r =>
    match MW.bodyExp r with
    | none => .unsupported
    | some e =>
      if MW.rootOKB C1 then
        match WE.inferExpWD fuel C1 e with
        | .ok ae =>
          match MW.unLet r ae with
          | some av =>
            if MW.portsOKB C1 r ae then finishIn B C ⟨m.header, m.imports, MW.joinBody at? (some av)⟩
            else .unsupported
          | none => .internal
        | .fail => if MW.hasPortB r then .unsupported else .fail
        | .unsupported => .unsupported
        | .outOfFuel => .outOfFuel
        | .internal => .internal
      else .unsupported

/-- `MW.inferModuleW` with the context of the imports given. -/
def inferModuleWIn (fuel : Nat) (B : SBasis) (C : Ctx) (m : BModule) : MW.MRes :=
  match m.body with
  | none => finishIn B C ⟨m.header, m.imports, none⟩
  | some d =>
    match MW.typesPart C (MW.splitBody d).1 with
    | none => .unsupported
    | some (at?, C1) => valuesWIn fuel B C m at? C1 (MW.splitBody d).2

/-- `wCheck` for a program of one module whose imports are `imps`, with their context `C` given. -/
def wCheckIn (B : SBasis) (imps : List Src.BImport) (C : Ctx) (s : SProgram) (q : Option Mod.Reduced) : Bool :=
  Src.decSynOK s &&
  match (bareOf s).modules with
  | [m] =>
    decide (m.imports = imps) &&
    match inferModuleWIn MW.wFuel B C m with
    | .ok a =>
      match a.resultIn B C with
      | some (B', E) =>
        checksAll [(B, B', E)] && furtherModInB B E a &&
          match q with
          | none => true
          | some r =>
            match reduceWith B [a] [(B, B', E)] with
            | .ok r' => decide (r' = r)
            | .error _ => false
      | none => false
    | _ => false
  | _ => false

theorem finish_eq_In {B : SBasis} {C : Ctx} {a : AModule} (h : importCtx B a.imports = some C) :
    MW.finish B a = finishIn B C a := by
  have hn : nodesModule B a = nodesModuleIn C a := by
    unfold nodesModule nodesModuleIn; rw [h]; cases a.body <;> rfl
  unfold MW.finish finishIn checkModule MW.namesB namesBIn
  rw [AModule.result_of_ctx h, hn]

theorem inferModuleW_eq_In {fuel : Nat} {B : SBasis} {C : Ctx} {m : BModule} (h : importCtx B m.imports = some C) :
    MW.inferModuleW fuel B m = inferModuleWIn fuel B C m := by
  have hf : ∀ hd body, MW.finish B ⟨hd, m.imports, body⟩ = finishIn B C ⟨hd, m.imports, body⟩ :=
    fun _ _ => finish_eq_In h
  have hv : ∀ at? C1 r, MW.valuesW fuel B m at? C1 r = valuesWIn fuel B C m at? C1 r := by
    intro at? C1 r
    cases r <;> simp only [MW.valuesW, valuesWIn, hf] <;> rfl
  unfold MW.inferModuleW inferModuleWIn
  rw [h]
  simp only [hf, hv]
  all_goals rfl

/-- A check with the context given is the check. -/
theorem wCheck_of_ctx {B : SBasis} {imps : List Src.BImport} {C : Ctx} {s : SProgram} {q : Option Mod.Reduced}
    (hC : importCtx B imps = some C) (h : wCheckIn B imps C s q = true) : wCheck B s q = true := by
  unfold wCheckIn at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hsyn, h⟩ := h
  unfold wCheck
  rw [hsyn, Bool.true_and]
  split at h
  · rename_i m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    rw [hm]
    have hw := inferModuleW_eq_In (fuel := MW.wFuel) hC
    split at h
    · rename_i a ha
      rw [← hw] at ha
      obtain ⟨-, -, -, -, -, haim, -⟩ := MW.inferModuleW_ok_inv ha
      have hCa : importCtx B a.imports = some C := haim ▸ hC
      have hres := AModule.result_of_ctx hCa
      split at h
      · rename_i B' E hr
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hc, hfu⟩, hq⟩ := h
        have hp : MW.inferProgramW MW.wFuel B [m] = .ok [a] := by
          simp only [MW.inferProgramW, ha, hres, hr]
        have hpr : progResults B [a] = some [(B, B', E)] := by
          simp only [progResults, hres, hr, Option.map_some]
        rw [hp]
        simp only [hpr, hc, furtherAllB, hres, hr, hfu, Bool.true_and, Bool.and_true]
        exact hq
      · cases h
    · cases h
  · cases h

/-! ## Lean's pipeline with W

`endToEndW` is step 10's pipeline (`endToEnd`: derived forms, inference, the checker of each module,
Chapter 9's side conditions, specialisation and erasure) with W (`MW.inferProgramW`) in place of
step 9's unverified inference. It lives here, not beside `endToEnd`, because W's definitions come
after step 10's (W's proofs use `SpecOf` and the module step). Its run is part of `wCheck`, so the
per-test theorem `spec_X` (`endToEndW Btest s_X = .ok g_X.reduced`) follows from `wcheck_X` without
running the inference again (`endToEndW_of_wCheck`), and step 10's statements about `endToEnd` hold
of it without D11 (`specOf_of_endToEndW`, `ident_of_endToEndW`). -/

/-- derive (total, step 8), W, check, reduce. -/
def endToEndW (B : SBasis) (s : SProgram) : Except E2EError Mod.Reduced :=
  match MW.inferProgramW MW.wFuel B (bareOf s).modules with
  | .ok as =>
    match progResults B as with
    | none => .error .check
    | some rs => if checksAll rs then (reduceWith B as rs).mapError .spec else .error .check
  | .fail => .error (.infer "W fails")
  | .other => .error (.infer "W gives no derivation")

/-- What a successful run of the pipeline with W gives. -/
theorem endToEndW_ok {B : SBasis} {s : SProgram} {r : Mod.Reduced} (h : endToEndW B s = .ok r) :
    ∃ as rs, MW.inferProgramW MW.wFuel B (bareOf s).modules = .ok as ∧ progResults B as = some rs ∧
      checksAll rs = true ∧ reduceWith B as rs = .ok r := by
  unfold endToEndW at h
  split at h
  · rename_i as hw
    split at h
    · cases h
    · rename_i rs hr
      split at h
      · rename_i hc
        refine ⟨as, rs, hw, hr, hc, ?_⟩
        cases hred : reduceWith B as rs with
        | error e => rw [hred] at h; cases h
        | ok r' => rw [hred] at h; cases h; rfl
      · cases h
  · cases h
  · cases h

/-- A W check that names a reduced program says that the pipeline with W gives it. -/
theorem endToEndW_of_wCheck {B : SBasis} {s : SProgram} {r : Mod.Reduced} (h : wCheck B s (some r) = true) :
    endToEndW B s = .ok r := by
  unfold wCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  unfold endToEndW
  split at h
  · rename_i as hw
    rw [hw]
    split at h
    · rename_i rs hr
      simp only [hr]
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hc, -⟩, hq⟩ := h
      simp only [hc, ↓reduceIte]
      split at hq
      · rename_i r' hr'
        simp only [decide_eq_true_eq] at hq
        rw [hr', hq]; rfl
      · cases hq
    · cases h
  · cases h

/-- Step 10's `specOf_of_endToEnd` for the pipeline with W, without D11: what it gives is a
    specialisation of the program. -/
theorem specOf_of_endToEndW {B : SBasis} {s : SProgram} {r : Mod.Reduced} (hB : BasisInv B)
    (h : endToEndW B s = .ok r) : SpecOf B (bareOf s) r := by
  obtain ⟨as, rs, hw, hr, -, hred⟩ := endToEndW_ok h
  exact ⟨as, MW.inferProgramW_principal hB hw, by simp only [reduceProgram, hr]; exact hred⟩

/-- Step 10's `ident_of_spec'` for the pipeline with W, without D11: the specialisation of the
    program is unique, and is what the pipeline with W gives. -/
theorem ident_of_endToEndW {s : SProgram} {q : Mod.Reduced} (h : endToEndW Btest s = .ok q) :
    ∀ r, SpecOf Btest (bareOf s) r → r = q := by
  obtain ⟨as, -, hw, -⟩ := endToEndW_ok h
  have hT := typesOrdered_of_inferProgramW _ _ _ Btest_inv hw
  exact fun r hr => specOf_functional MStep.moduleStep Btest_inv hT hr (specOf_of_endToEndW Btest_inv h)

/-- Step 10's `programSem_of_legal` for the pipeline with W, without D11. -/
theorem programSem_of_endToEndW {B : SBasis} {s : SProgram} {r : Mod.Reduced} (hB : BasisInv B)
    (h : endToEndW B s = .ok r) (hL : LegalProgram B s) (hv : ∃ v, DynOf r v) :
    ∃ τ PE v, ProgramSem B (bareOf s) (τ, PE, v) := by
  obtain ⟨-, τ, PE, hst⟩ := hL
  obtain ⟨v, hd⟩ := hv
  exact ⟨τ, PE, v, .r_p_program hst (specOf_of_endToEndW hB h) hd⟩

/-! ## A96: flags of a type variable (StandardA96NumberFlagsTest) -/

/-- W's principal scheme of `main`, for a program of one module, is that of a worker whose flags type
    is a type variable (A96: `init = \n -> (n + 1, Cmd.none)` gives flags of class number). -/
def wMainVarB (B : SBasis) (s : SProgram) : Bool :=
  match (bareOf s).modules with
  | [m] =>
    match MW.inferModuleW MW.wFuel B m with
    | .ok a =>
      match a.result B with
      | some (_, E) =>
        match E.VE.find? "main" with
        | some (σ, .v) =>
          match σ.body with
          | .con [.var _, _, _] t => decide (t = tProgram)
          | _ => false
        | _ => false
      | none => false
    | _ => false
  | _ => false

theorem find?_map_snd {V W : Type} (f : V → W) : ∀ (l : List (Var × V)) (k : Var),
    FMap.find? (l.map fun p => (p.1, f p.2)) k = (FMap.find? l k).map f
  | [], _ => rfl
  | (k', v) :: rest, k => by
    simp only [List.map_cons, FMap.find?]
    split <;> simp_all [find?_map_snd f rest k]

theorem applyList_length (S : Subst) : ∀ {as as' : List Ty}, S.applyList as = some as' → as'.length = as.length
  | [], as', h => by simp only [Subst.applyList, Option.some.injEq] at h; subst h; rfl
  | τ :: rest, as', h => by
    simp only [Subst.applyList] at h
    split at h
    · rename_i τ' r' _ h2
      simp only [Option.some.injEq] at h; subst h
      simp [applyList_length S h2]
    · cases h

theorem getD_apply_con (S : Subst) (l : List Ty) (t : TyName) :
    ∃ as, (S.apply (.con l t)).getD (.con l t) = .con as t ∧ as.length = l.length := by
  cases e : S.apply (.con l t) with
  | none => exact ⟨l, rfl, rfl⟩
  | some τ' =>
    simp only [Subst.apply] at e
    split at e
    · rename_i as' hl
      simp only [Option.some.injEq] at e; subst e
      exact ⟨as', rfl, applyList_length _ hl⟩
    · cases e

/-- The default of a scheme whose body is `(τ1, τ2, τ3) t` is a type of three arguments. -/
theorem dflt_con3 {σ : Scheme} {τ1 τ2 τ3 : Ty} {t : TyName} (h : σ.body = .con [τ1, τ2, τ3] t) :
    ∃ as, dflt σ = .con as t ∧ as.length = 3 := by
  unfold dflt
  rw [h]
  exact getD_apply_con _ _ _

/-- A96 (correction 3, and the comment after r:p-stat-main-view): when W's principal scheme of `main`
    gives the flags a type variable, no derivation of the program has a type of Chapter 9 for
    `main`. Every principal derivation of the module is W's up to a bijection of type names fixing
    the basis (step 10's module step), which takes a type variable to itself; a variable is not a port
    type (r:p-stat-main-program), and the default of a `Program` type is not a `Node` type
    (r:p-stat-main-view). -/
theorem not_legal_of_wMainVar {B : SBasis} {s : SProgram} (hB : BasisInv B) (h : wMainVarB B s = true) :
    ¬ LegalProgram B s := by
  rintro ⟨-, τ, PE, hel⟩
  unfold wMainVarB at h
  split at h
  · rename_i m hm
    split at h
    · rename_i a hw
      split at h
      · rename_i R E hr
        split at h
        · rename_i σ hσ
          split at h
          · rename_i α τ2 τ3 t hb
            simp only [decide_eq_true_eq] at h
            subst h
            obtain ⟨hae, hpa⟩ := MW.inferModuleW_principal hB hw
            obtain ⟨C, hC⟩ := MW.importCtx_of_ok hw
            have ho : TypesOrdered a.erase := hae ▸ MW.typesOrdered_of_W hw hC
            -- any principal derivation of the module has `main`'s scheme W's, renamed
            have key : ∀ a' B' E', a'.erase = m → IsPrincipalMod B a' → a'.result B = some (B', E') →
                ∃ σ' x y, E'.VE.find? "main" = some (σ', .v) ∧ σ'.body = .con [.var α, x, y] tProgram := by
              intro a' B' E' he' hpa' hr'
              have hI1 : InstanceOfMod B a' a := hpa.2.2 a' hpa'.1 hpa'.2.1 (he'.trans hae.symm)
              have hI2 : InstanceOfMod B a a' := hpa'.2.2 a hpa.1 hpa.2.1 (hae.trans he'.symm)
              obtain ⟨ρ, ρ', R1, E1, hρ, -, hr1, hr2, -⟩ :=
                MStep.moduleStep B a a' hB ho hpa.1 hpa'.1 hpa.2.1 hpa'.2.1 hI1 hI2
              rw [hr] at hr1
              simp only [Option.some.injEq, Prod.mk.injEq] at hr1
              obtain ⟨rfl, rfl⟩ := hr1
              rw [hr'] at hr2
              simp only [Option.some.injEq, Prod.mk.injEq] at hr2
              obtain ⟨-, rfl⟩ := hr2
              refine ⟨(nr ρ).scheme σ, (nr ρ).ty τ2, (nr ρ).ty τ3, ?_, ?_⟩
              · simp only [Renaming.env, Renaming.valEnv]
                rw [find?_map_snd (fun b => ((nr ρ).scheme b.1, b.2)) E.VE "main", hσ]
                rfl
              · simp only [Renaming.scheme, hb, Renaming.ty, Renaming.tys]
                rw [hρ.h.t0 tProgram (by decide)]
                rfl
            have hel' : ElProgram B [m] τ PE := by rw [← hm]; exact hel
            cases hel' with
            | r_p_stat_module _ _ hne _ => exact hne rfl
            | r_p_stat_main_program hd _ hσ' hb' hP =>
              obtain ⟨a', he', hpa', hr', -⟩ := hd
              obtain ⟨σ0, x0, y0, hf, hb0⟩ := key a' _ _ he' hpa' hr'
              rw [hf] at hσ'
              simp only [Option.some.injEq, Prod.mk.injEq] at hσ'
              obtain ⟨rfl, -⟩ := hσ'
              rw [hb0] at hb'
              simp only [Ty.con.injEq, List.cons.injEq] at hb'
              obtain ⟨⟨rfl, -⟩, -⟩ := hb'
              cases hP
            | r_p_stat_main_view hd _ hσ' hdf =>
              obtain ⟨a', he', hpa', hr', -⟩ := hd
              obtain ⟨σ0, x0, y0, hf, hb0⟩ := key a' _ _ he' hpa' hr'
              rw [hf] at hσ'
              simp only [Option.some.injEq, Prod.mk.injEq] at hσ'
              obtain ⟨rfl, -⟩ := hσ'
              obtain ⟨as, hd3, hl⟩ := dflt_con3 hb0
              rw [hd3] at hdf
              simp only [Ty.con.injEq] at hdf
              rw [hdf.1] at hl
              simp at hl
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- A96's refusal, in the test basis. -/
theorem not_legal_of_wMainVar_test {s : SProgram} (h : wMainVarB Btest s = true) : ¬ LegalProgram Btest s :=
  not_legal_of_wMainVar Btest_inv h


/-! ## General discharge theorems (plan step 11, "Discharge"), as far as W's proved properties go

W's results are principal (`WE.inferExpWD_principal`, `MW.inferModuleW_principal`,
`MW.inferProgramW_principal`), so principal derivations exist wherever W succeeds. The book's
properties (`PrincipalExistsCore`, `PrincipalExistsMod`) ask for them wherever *a* derivation exists;
that needs W to succeed wherever a derivation exists (`WCoversCore`, `WCoversMod`), which is not
proved: milestone (e)'s completeness lacks its `internal` clause (W never stops with `internal` where a
derivation exists), W answers `unsupported` outside its fragment (a pattern binding in a group of
several bindings, an ambiguous context, a type through an alias with a free variable), and W is
stated for root contexts (`RootOKD`) and bases with `BasisInv`, while the properties quantify over
every context and basis. The theorems below state the properties from those coverage hypotheses. -/

/-- W succeeds on every phrase that elaborates (not proved; see above). -/
def WCoversCore : Prop :=
  ∀ (C0 : Ctx) (e : Src.BExp), (∃ τ, ElExp C0 e τ) → RootOKD C0 ∧ ∃ fuel a, WE.inferExpWD fuel C0 e = .ok a

/-- Module-level W succeeds on every module that elaborates (not proved; see above). -/
def WCoversMod : Prop :=
  ∀ (B : SBasis) (m : BModule), (∃ B' E, ElModule B m B' E) → BasisInv B ∧ ∃ fuel a, MW.inferModuleW fuel B m = .ok a

/-- A Core phrase on which W succeeds has a principal derivation. -/
theorem principal_of_inferExpWD {C0 : Ctx} {e : Src.BExp} {fuel : Nat} {a : AExp} (hC : RootOKD C0)
    (h : WE.inferExpWD fuel C0 e = .ok a) : ∃ a, a.erase = e ∧ IsPrincipal C0 a :=
  ⟨a, (WE.inferExpWD_principal hC h).1, (WE.inferExpWD_principal hC h).2.2⟩

/-- sec:static-core-principal, from W's coverage. -/
theorem principalExistsCore_of_covers (h : WCoversCore) : PrincipalExistsCore := by
  intro C0 e he
  obtain ⟨hC, fuel, a, hw⟩ := h C0 e he
  exact principal_of_inferExpWD hC hw

/-- A module on which W succeeds has a principal derivation. -/
theorem principalMod_of_inferModuleW {B : SBasis} {m : BModule} {fuel : Nat} {a : AModule} (hB : BasisInv B)
    (h : MW.inferModuleW fuel B m = .ok a) : ∃ a, a.erase = m ∧ IsPrincipalMod B a :=
  ⟨a, MW.inferModuleW_principal hB h⟩

/-- sec:static-modules-principal, from W's coverage. -/
theorem principalExistsMod_of_covers (h : WCoversMod) : PrincipalExistsMod := by
  intro B m hm
  obtain ⟨hB, fuel, a, hw⟩ := h B m hm
  exact principalMod_of_inferModuleW hB hw

/-- D11 for one program (step 10's `D11For`, about step 9's inference) holds wherever step 9's
    inference returns what W returns. -/
theorem d11For_of_agree {B : SBasis} {p : BProgram} {fuel : Nat} (hB : BasisInv B)
    (h : ∀ a, inferProgram B p = .ok a → MW.inferProgramW fuel B p.modules = .ok a) : D11For B p :=
  fun a hi _ => MW.inferProgramW_principal hB (h a hi)

end StandardElm.Stat
