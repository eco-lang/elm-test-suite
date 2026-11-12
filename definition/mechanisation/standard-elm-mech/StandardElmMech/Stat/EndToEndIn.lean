/-
  A Standard Definition of Elm? Mechanisation: the end-to-end pipeline with the context of the
  first module given, plan step 10 ("Acceptance", item 3: the cost of the per-test theorems).

  `endToEnd` reads the context of each module's imports (`importCtx`) in the inference, the checker
  and the reading of the results. In the kernel, computing that context is most of the cost of a
  small program (2.5 to 3 s: its environment `envOf B.ME π` is built from the whole provider map of
  the default imports and the module's own). Step 9 proves, once for every list of imports the
  tests use, that the imports give a literal context in `Btest` (`ctx_<k>_eq`,
  Certs/Contexts*.lean). `endToEndG B (some (imps, C))` is `endToEnd B` with the first module's
  context read from `C` when that module's imports are `imps` (`endToEnd_eq_G`); it also infers and
  reads the results of each module in one pass, where `endToEnd` checks each certificate twice. The
  later modules of a program elaborate in the basis the earlier ones build, and compute their
  contexts. A per-test theorem:

    theorem spec_X : Stat.endToEnd Stat.Btest s_X = .ok g_X.reduced :=
      Stat.endToEnd_of_ctx ctx_k_eq (by decide +kernel)
-/
import StandardElmMech.Stat.EndToEnd

namespace StandardElm.Stat
open StandardElm (Var Lab ModId)
open StandardElm.Src (BImport BModule BProgram SProgram)

/-! ## Contexts from hints -/

/-- The context of a module's imports: the given one when the imports are the given ones, else
    computed. -/
def ctxOf (B : SBasis) (g : Option (List BImport × Ctx)) (imps : List BImport) : Option Ctx :=
  match g with
  | some (imps0, C0) => if imps = imps0 then some C0 else importCtx B imps
  | none => importCtx B imps

/-- A given context is one its imports give. -/
def GivenOK (B : SBasis) (g : Option (List BImport × Ctx)) : Prop :=
  ∀ imps0 C0, g = some (imps0, C0) → importCtx B imps0 = some C0

theorem givenOK_none (B : SBasis) : GivenOK B none := fun _ _ h => by cases h

theorem ctxOf_eq {B : SBasis} {g : Option (List BImport × Ctx)} (hg : GivenOK B g)
    (imps : List BImport) : ctxOf B g imps = importCtx B imps := by
  unfold ctxOf
  rcases g with _ | ⟨imps0, C0⟩
  · rfl
  · simp only
    split
    · rename_i e; subst e; exact (hg _ _ rfl).symm
    · rfl

/-! ## Inference and the results of the modules, in one pass -/

/-- The modules of a program with their results (r:p-stat-module's B_i, B'_i, E_i), the first
    module's context from `g`. -/
def inferResultsG (B : SBasis) (g : Option (List BImport × Ctx)) :
    List BModule → Except String (AProgram × List (SBasis × SBasis × Env))
  | [] => pure ([], [])
  | m :: ms =>
    match ctxOf B g m.imports with
    | none => throw s!"module {m.header.name}: the imports do not elaborate"
    | some C => do
      let a ← inferModuleIn B C m
      match a.resultIn B C with
      | some (B', E) => do
        let (as, rs) ← inferResultsG (B.plus B') none ms
        pure (a :: as, (B, B', E) :: rs)
      | none => throw s!"module {m.header.name}: the certificate does not check"

theorem inferResultsG_fst : ∀ {B : SBasis} {g : Option (List BImport × Ctx)}, GivenOK B g →
    ∀ (ms : List BModule),
    (inferResultsG B g ms).map (·.1) = inferProgramFrom B ms
  | _, _, _, [] => rfl
  | B, g, hg, m :: ms => by
    rw [inferResultsG, inferProgramFrom.eq_2, ctxOf_eq hg]
    unfold inferModule
    cases hc : importCtx B m.imports with
    | none => rfl
    | some C =>
      simp only
      cases ha : inferModuleIn B C m with
      | error e => rfl
      | ok a =>
        have hca : importCtx B a.imports = some C := (inferModuleIn_imports ha) ▸ hc
        simp only [bind, Except.bind, AModule.result_of_ctx hca]
        cases hr : AModule.resultIn B C a with
        | none => rfl
        | some p =>
          obtain ⟨B', E⟩ := p
          simp only
          have ih := inferResultsG_fst (givenOK_none (B.plus B')) ms
          revert ih
          cases inferResultsG (B.plus B') none ms with
          | error e => intro ih; simp only [Except.map] at ih; rw [← ih]; rfl
          | ok v => intro ih; simp only [Except.map] at ih; rw [← ih]; rfl

theorem inferResultsG_snd : ∀ {B : SBasis} {g : Option (List BImport × Ctx)}, GivenOK B g →
    ∀ (ms : List BModule) (a : AProgram) rs,
    inferResultsG B g ms = .ok (a, rs) → progResults B a = some rs
  | _, _, _, [], a, rs, h => by
    simp only [inferResultsG, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | B, g, hg, m :: ms, a, rs, h => by
    rw [inferResultsG, ctxOf_eq hg] at h
    cases hc : importCtx B m.imports with
    | none => rw [hc] at h; cases h
    | some C =>
      rw [hc] at h
      simp only at h
      cases ha : inferModuleIn B C m with
      | error e => rw [ha] at h; cases h
      | ok a1 =>
        have hca : importCtx B a1.imports = some C := (inferModuleIn_imports ha) ▸ hc
        rw [ha] at h
        simp only [bind, Except.bind] at h
        cases hr : AModule.resultIn B C a1 with
        | none => rw [hr] at h; cases h
        | some p =>
          obtain ⟨B', E⟩ := p
          rw [hr] at h
          simp only at h
          cases hrest : inferResultsG (B.plus B') none ms with
          | error e => rw [hrest] at h; cases h
          | ok v =>
            obtain ⟨as, rs'⟩ := v
            rw [hrest] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ih := inferResultsG_snd (givenOK_none (B.plus B')) ms as rs' hrest
            simp only [progResults, AModule.result_of_ctx hca, hr, ih, Option.map_some]

/-! ## The pipeline -/

/-- `endToEnd`, with the first module's context from `g`. -/
def endToEndG (B : SBasis) (g : Option (List BImport × Ctx)) (s : SProgram) :
    Except E2EError Mod.Reduced := do
  let p := bareOf s
  let (a, rs) ← (inferResultsG B g p.modules).mapError .infer
  unless a.map AModule.erase == p.modules && checksAll rs do throw .check
  (reduceWith B a rs).mapError .spec

theorem endToEnd_eq_G {B : SBasis} {g : Option (List BImport × Ctx)} (hg : GivenOK B g)
    (s : SProgram) : endToEnd B s = endToEndG B g s := by
  have h1 := inferResultsG_fst hg (bareOf s).modules
  have h2 := inferResultsG_snd hg (bareOf s).modules
  unfold endToEnd endToEndG
  simp only [inferProgram]
  rw [← h1]
  revert h2
  cases inferResultsG B g (bareOf s).modules with
  | error e => intro _; rfl
  | ok v =>
    obtain ⟨a, rs⟩ := v
    intro h2
    simp only [Except.map, Except.mapError, bind, Except.bind, h2 a rs rfl]

/-- The per-test form: the kernel runs `endToEndG` with the first module's context a literal. -/
theorem endToEnd_of_ctx {B : SBasis} {imps : List BImport} {C : Ctx} {s : SProgram}
    {x : Except E2EError Mod.Reduced} (hC : importCtx B imps = some C)
    (h : endToEndG B (some (imps, C)) s = x) : endToEnd B s = x :=
  (endToEnd_eq_G (fun _ _ e => by cases e; exact hC) s).trans h

end StandardElm.Stat
