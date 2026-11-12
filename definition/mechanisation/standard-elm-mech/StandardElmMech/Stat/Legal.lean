/-
  A Standard Definition of Elm? Mechanisation: the master theorems of plan step 9 (section
  "Theorems", group 9). A program is legal when the inference's derivation for it checks, meets
  the further restrictions and the conditions of Chapter 9, under the hypothesis that what the
  inference returns is principal (D11, `InferPrincipalFor`).

  Under that hypothesis the derivation the inference returns is itself the principal one, so the
  scheme of `main` and the port environment are read from it: no transfer lemma is needed for
  them (the specification's `mainTransfer` and `CertProgram` cover a weaker hypothesis).

  The per-test theorems run the inference in the kernel, in the context of the module's imports,
  which a shared lemma gives as a literal for every program with the same imports
  (`legal_of_infer1`); programs of several modules use `legal_of_infer`.
-/
import StandardElmMech.Stat.Program
import StandardElmMech.Stat.CheckSound

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BModule BImport BProgram SProgram)

/-! ## The conditions of Chapter 9, decided -/

/-- The view type of a scheme of `main`: Dflt σ = τ Node. -/
def viewTy (σ : Scheme) : Option Ty :=
  match dflt σ with
  | .con [τ] t => if t = tNode then some (.con [τ] tNode) else none
  | _ => none

/-- The type r:p-stat-main-program or r:p-stat-main-view gives `main`, if one applies. -/
def mainTy (E : Env) : Option Ty :=
  match E.VE.find? "main" with
  | some (σ, .v) =>
    match σ.body with
    | .con [τ1, _, _] t => if t = tProgram ∧ portB τ1 = true then some (dflt σ) else viewTy σ
    | _ => viewTy σ
  | _ => none

def portsDisjointB (B B' : SBasis) : Bool :=
  B'.PE.keys.all fun x => !(B.PE.keys.contains x) && !(Src.managersPlat.contains x)

theorem portsDisjointB_sound {B B' : SBasis} (h : portsDisjointB B B' = true) : PortsDisjoint B B' := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · have := List.contains_iff_mem.mpr hm; rw [h1] at this; cases this
  · have := List.contains_iff_mem.mpr hm; rw [h2] at this; cases this

theorem viewTy_sound {σ : Scheme} {τ : Ty} (h : viewTy σ = some τ) : ∃ τ0, dflt σ = .con [τ0] tNode ∧ τ = .con [τ0] tNode := by
  unfold viewTy at h
  split at h
  · rename_i τ0 t hd
    split at h
    · rename_i ht; subst ht; cases h; exact ⟨τ0, hd, rfl⟩
    · cases h
  · cases h

/-- The last step of a program: its main module's derivation gives `main` a type by one of the two
    rules. -/
theorem elProgram_main {B : SBasis} {m : BModule} {B' : SBasis} {E : Env} {τ : Ty}
    (hd : PrincipalModDer B m B' E) (hp : PortsDisjoint B B') (hm : mainTy E = some τ) :
    ElProgram B [m] τ (B.plus B').PE := by
  unfold mainTy at hm
  split at hm
  · rename_i σ hσ
    split at hm
    · rename_i τ1 τ2 τ3 t hb
      split at hm
      · rename_i hc
        obtain ⟨rfl, hpt⟩ := hc
        cases hm
        exact .r_p_stat_main_program hd hp hσ hb (portB_sound _ hpt)
      · obtain ⟨τ0, h1, rfl⟩ := viewTy_sound hm
        exact .r_p_stat_main_view hd hp hσ h1
    · obtain ⟨τ0, h1, rfl⟩ := viewTy_sound hm
      exact .r_p_stat_main_view hd hp hσ h1
  · cases hm

/-! ## One-module programs -/

/-- The check of a one-module program, in the context C of its imports: it meets the syntactic
    restrictions; the inference returns a derivation that checks, meets the further restrictions,
    declares no port the basis or the platform has, and gives `main` a type of Chapter 9. -/
def legal1B (B : SBasis) (imps : List BImport) (C : Ctx) (sp : SProgram) : Bool :=
  Src.decSynOK sp &&
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | [m] =>
    decide (m.imports = imps) &&
    match inferModuleIn B C m with
    | .ok a =>
      match a.resultIn B C with
      | some (B', E) => furtherModInB B E a && portsDisjointB B B' && (mainTy E).isSome
      | none => false
    | .error _ => false
  | _ => false

theorem inferModuleIn_imports {B : SBasis} {C : Ctx} {m : BModule} {a : AModule}
    (h : inferModuleIn B C m = .ok a) : a.imports = m.imports := by
  unfold inferModuleIn at h
  cases hb : m.body with
  | none => simp [hb, pure, Except.pure, bind, Except.bind] at h; subst h; rfl
  | some d =>
    simp only [hb] at h
    cases hi : inferTopDec C (1000 + B.T.length) d with
    | error e => simp [hi, bind, Except.bind] at h
    | ok v => simp [hi, bind, Except.bind, pure, Except.pure] at h; subst h; rfl

theorem legal_of_infer1 {B : SBasis} {imps : List BImport} {C : Ctx} {sp : SProgram}
    (hctx : importCtx B imps = some C) (h : legal1B B imps C sp = true) :
    InferPrincipalFor B (Src.deriveProgram (Src.canonOrder sp)) → LegalProgram B sp := by
  intro H
  unfold legal1B at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hsyn, h⟩ := h
  generalize hp : Src.deriveProgram (Src.canonOrder sp) = p at h H
  have hpm := congrArg BProgram.modules hp
  split at h
  · rename_i m hms
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨himps, h⟩ := h
    split at h
    · rename_i a hinf
      split at h
      · rename_i B' E hres
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hfur, hports⟩, hmain⟩ := h
        obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hmain
        have hctxm : importCtx B m.imports = some C := himps ▸ hctx
        have hctxa : importCtx B a.imports = some C := (inferModuleIn_imports hinf) ▸ hctxm
        have hresult : a.result B = some (B', E) := by rw [AModule.result_of_ctx hctxa]; exact hres
        have hinfp : inferProgram B p = .ok [a] := by
          unfold inferProgram
          rw [hms]
          simp only [inferProgramFrom, bind, Except.bind, pure, Except.pure]
          rw [inferModule_of_ctx hctxm, hinf]
          simp only [hresult]
        have hcheck : checkProgram B [a] = true := by
          simp [checkProgram, AProgram.bases, hresult]
        obtain ⟨⟨_, herase⟩, Bs, hBs, hpr⟩ := H [a] hinfp hcheck
        simp only [AProgram.bases, hresult, Option.map_some] at hBs
        cases hBs
        have hprin : IsPrincipalMod B a := hpr 0 (by simp) (by simp)
        have hea : a.erase = m := by rw [hms] at herase; simpa using herase
        have hfm : FurtherMod B a := by
          unfold FurtherMod; rw [hresult]; exact furtherModInB_sound hfur
        refine ⟨Src.synOKSet_of_synOK (by simpa [Src.decSynOK] using hsyn), τ, (B.plus B').PE, ?_⟩
        rw [hp, hms]
        exact elProgram_main ⟨a, hea, hprin, hresult, hfm⟩ (portsDisjointB_sound hports) hτ
      · cases h
    · cases h
  · cases h

/-! ## Programs of several modules -/

theorem inferProgramFrom_cons {B : SBasis} {m : BModule} {ms : List BModule} {a : AModule} {B' : SBasis}
    {E : Env} (ha : inferModule B m = .ok a) (hr : a.result B = some (B', E)) :
    inferProgramFrom B (m :: ms) = (inferProgramFrom (B.plus B') ms).map (a :: ·) := by
  rw [inferProgramFrom.eq_2]
  simp only [ha, hr, bind, Except.bind, pure, Except.pure]
  cases inferProgramFrom (B.plus B') ms <;> rfl

/-- The check of a program's modules, each in the basis the earlier ones build. -/
def progCheckFrom (B : SBasis) : List BModule → Bool
  | [] => false
  | [m] =>
    match inferModule B m with
    | .ok a =>
      match a.result B with
      | some (B', E) => furtherModInB B E a && portsDisjointB B B' && (mainTy E).isSome
      | none => false
    | .error _ => false
  | m :: m2 :: ms =>
    match inferModule B m with
    | .ok a =>
      match a.result B with
      | some (B', E) => furtherModInB B E a && portsDisjointB B B' && progCheckFrom (B.plus B') (m2 :: ms)
      | none => false
    | .error _ => false

def legalB (B : SBasis) (sp : SProgram) : Bool :=
  Src.decSynOK sp && progCheckFrom B (Src.deriveProgram (Src.canonOrder sp)).modules

theorem progCheck_infer : ∀ (ms : List BModule) (B : SBasis), progCheckFrom B ms = true →
    ∃ as, inferProgramFrom B ms = .ok as ∧ (AProgram.bases B as).isSome
  | [], _, h => by simp [progCheckFrom] at h
  | [m], B, h => by
    simp only [progCheckFrom] at h
    split at h
    · rename_i a ha
      split at h
      · rename_i B' E hr
        refine ⟨[a], ?_, ?_⟩
        · simp [inferProgramFrom, ha, hr, bind, Except.bind, pure, Except.pure]
        · simp [AProgram.bases, hr]
      · cases h
    · cases h
  | m :: m2 :: ms, B, h => by
    simp only [progCheckFrom] at h
    split at h
    · rename_i a ha
      split at h
      · rename_i B' E hr
        simp only [Bool.and_eq_true] at h
        obtain ⟨as, has, hb⟩ := progCheck_infer (m2 :: ms) (B.plus B') h.2
        refine ⟨a :: as, ?_, ?_⟩
        · rw [inferProgramFrom_cons ha hr, has]; rfl
        · obtain ⟨Bs, hBs⟩ := Option.isSome_iff_exists.mp hb
          simp [AProgram.bases, hr, hBs]
      · cases h
    · cases h

theorem progCheck_el : ∀ (ms : List BModule) (B : SBasis) (as : AProgram) (Bs : List SBasis),
    progCheckFrom B ms = true → inferProgramFrom B ms = .ok as → AProgram.bases B as = some Bs →
    (∀ i (h : i < as.length) (h' : i < Bs.length), IsPrincipalMod Bs[i] as[i]) →
    as.map AModule.erase = ms → ∃ τ PE, ElProgram B ms τ PE
  | [], _, _, _, h, _, _, _, _ => by simp [progCheckFrom] at h
  | [m], B, as, Bs, h, hi, hb, hp, he => by
    simp only [progCheckFrom] at h
    split at h
    · rename_i a ha
      split at h
      · rename_i B' E hr
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hfur, hports⟩, hmain⟩ := h
        obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hmain
        simp only [inferProgramFrom, ha, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hi
        subst hi
        simp only [AProgram.bases, hr, Option.map_some, Option.some.injEq] at hb
        subst hb
        have hprin : IsPrincipalMod B a := hp 0 (by simp) (by simp)
        have hea : a.erase = m := by simpa using he
        have hfm : FurtherMod B a := by unfold FurtherMod; rw [hr]; exact furtherModInB_sound hfur
        exact ⟨τ, _, elProgram_main ⟨a, hea, hprin, hr, hfm⟩ (portsDisjointB_sound hports) hτ⟩
      · cases h
    · cases h
  | m :: m2 :: ms, B, as, Bs, h, hi, hb, hp, he => by
    simp only [progCheckFrom] at h
    split at h
    · rename_i a ha
      split at h
      · rename_i B' E hr
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hfur, hports⟩, hrest⟩ := h
        rw [inferProgramFrom_cons ha hr] at hi
        cases hrest' : inferProgramFrom (B.plus B') (m2 :: ms) with
        | error e => rw [hrest'] at hi; cases hi
        | ok rest =>
          rw [hrest'] at hi
          simp only [Except.map, Except.ok.injEq] at hi
          subst hi
          simp only [AProgram.bases, hr] at hb
          cases hbr : AProgram.bases (B.plus B') rest with
          | none => rw [hbr] at hb; cases hb
          | some Bs' =>
            rw [hbr] at hb
            simp only [Option.map_some, Option.some.injEq] at hb
            subst hb
            have hprin : IsPrincipalMod B a := hp 0 (by simp) (by simp)
            simp only [List.map_cons, List.cons.injEq] at he
            have hfm : FurtherMod B a := by unfold FurtherMod; rw [hr]; exact furtherModInB_sound hfur
            obtain ⟨τ, PE, hel⟩ := progCheck_el (m2 :: ms) (B.plus B') rest Bs' hrest hrest' hbr
              (fun i h1 h2 => hp (i + 1) (by simp; omega) (by simp; omega)) he.2
            exact ⟨τ, PE, .r_p_stat_module ⟨a, he.1, hprin, hr, hfm⟩ (portsDisjointB_sound hports)
              (by simp) hel⟩
      · cases h
    · cases h

/-- Legality of a program of any number of modules, everything computed by the kernel. -/
theorem legal_of_infer {B : SBasis} {sp : SProgram} (h : legalB B sp = true) :
    InferPrincipalFor B (Src.deriveProgram (Src.canonOrder sp)) → LegalProgram B sp := by
  intro H
  unfold legalB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hsyn, h⟩ := h
  obtain ⟨as, hinf, hb⟩ := progCheck_infer _ B h
  obtain ⟨Bs, hBs⟩ := Option.isSome_iff_exists.mp hb
  have hck : checkProgram B as = true := by simp [checkProgram, hBs]
  obtain ⟨⟨_, herase⟩, Bs', hBs', hpr⟩ := H as hinf hck
  rw [hBs] at hBs'
  cases hBs'
  obtain ⟨τ, PE, hel⟩ := progCheck_el _ B as Bs h hinf hBs hpr herase
  exact ⟨Src.synOKSet_of_synOK (by simpa [Src.decSynOK] using hsyn), τ, PE, hel⟩

end StandardElm.Stat
