/-
  A Standard Definition of Elm? Mechanisation: the core library values written in Elm, evaluated
  (plans/library-elm-texts.md, decisions L1 to L4, steps 2 and 3).

  The book leaves `List`, `Tuple`, `Maybe` and `Result` with empty or partial dynamic interfaces
  (Appendix D). The tests name 12 of their values (`List.map`, `Tuple.first`, ...), each defined in
  elm/core 1.0.5 by Elm text that names only other Elm text, the book's basic values and
  `List.cons`, the list constructor. The translator writes those texts, the closure of the values the
  tests name, as modules (`Generated/Library.lean`, `libTexts`): elm/core's texts, unchanged but for
  `cons = Elm.Kernel.List.cons`, written `cons = (::)`, and specialised as a program's code is, so
  that `List.sum`, whose scheme quantifies a `number` variable, has its default copy at Float and a
  copy `sum$Int` at Int (L3).

  `libME` is what Chapter 7's rules give those modules: module k is evaluated in ME0 extended, as
  the test basis extends it, by the interfaces of the modules before it (`libME_eval`, from the
  evaluator's soundness). `Btest` is the dynamic test basis with the library (D2 (b)): ME0's
  interfaces of `List`, `Maybe`, `Result` and `Tuple` extended by those values. The view programs'
  theorems (`t_`, and `mean_` through `Stat.DynOf`) are stated in it; the worker theorems keep
  `Mod.Btest []`, since no worker test names a library value (L4).

  Trust: that elm/core's Elm text is the meaning of the library values a program uses, which the
  book does not bind; the theorem of a program that names one is tagged `[library]` (L5).

  A library value's interface entry is computed only when a program looks it up: `libME` is a
  literal list of modules whose interfaces have no record alias and no constructor, and only their
  value environments come from the evaluator, so the kernel evaluates a library module only for a
  program that names a value of it.
-/
import StandardElmMech.Mod.Program
import StandardElmMech.Generated.Library

namespace StandardElm.Lib
open StandardElm StandardElm.Mod

/-- The library modules in module form, in order. -/
def libModules : List Module := libTexts.map ModSrc.toModule

/-- The evaluator's result for a module in B, when it is an interface of one module. -/
def evLibModule (B : Basis) (m : Module) : Option (ModId × Interface × ValEnv) :=
  match evModule (.const false) fuelT B m 0 with
  | ⟨.value ([(mid, I)], VE), _, _⟩ => some (mid, I, VE)
  | _ => none

theorem evLibModule_sound {B : Basis} {m : Module} {mid : ModId} {I : Interface} {VE : ValEnv}
    (h : evLibModule B m = some (mid, I, VE)) : EvalModule B m [(mid, I)] VE := by
  unfold evLibModule at h
  split at h
  · rename_i mid' I' VE' l k hr
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (evModule_sound_l hr).forget
  · simp at h

/-- The value environment of the interface a module has in B. -/
def modVE (B : Basis) (m : Module) : ValEnv :=
  match evLibModule B m with
  | some (_, I, _) => I.VE
  | none => []

/-- The library's interfaces from B on: each module's interface is its value environment (it
    exposes values only), evaluated in B extended by the modules before it (`btestStep`). -/
def libFrom (B : Basis) : List ModSrc → ModEnv
  | [] => []
  | s :: ss =>
    let p : ModId × Interface := (s.name, .ofVE (modVE B s.toModule))
    p :: libFrom (btestStep B p) ss

/-- The library modules' interfaces, evaluated in order in ME0. -/
def libME : ModEnv := libFrom ME0 libTexts

/-- D2: the dynamic test basis with the core library. -/
def Btest : Basis := Mod.Btest libME

/-- Chapter 7's derivations of a sequence of modules, each in the basis of the ones before it
    added as the test basis adds the library (`btestStep`). -/
inductive EvalLib : Basis → List Module → ModEnv → Prop where
  | nil (B : Basis) : EvalLib B [] []
  | cons (B : Basis) (m : Module) (ms : List Module) (mid : ModId) (I : Interface) (VE : ValEnv)
      (rest : ModEnv) :
      EvalModule B m [(mid, I)] VE → EvalLib (btestStep B (mid, I)) ms rest →
      EvalLib B (m :: ms) ((mid, I) :: rest)

/-- The evaluator gives each module, in turn, an interface named as the module and with neither
    record alias nor constructor. -/
def libCheckB (B : Basis) : List ModSrc → Bool
  | [] => true
  | s :: ss =>
    (match evLibModule B s.toModule with
     | some (mid, I, _) => mid == s.name && I.RA.isEmpty && I.CE.isEmpty
     | none => false) &&
    libCheckB (btestStep B (s.name, .ofVE (modVE B s.toModule))) ss

theorem libCheck_sound : ∀ (B : Basis) (ss : List ModSrc), libCheckB B ss = true →
    EvalLib B (ss.map ModSrc.toModule) (libFrom B ss)
  | B, [], _ => .nil B
  | B, s :: ss, h => by
    simp only [libCheckB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := libCheck_sound _ ss h2
    simp only [List.map_cons, libFrom]
    rcases hr : evLibModule B s.toModule with _ | ⟨mid, I, VE⟩
    · rw [hr] at h1; cases h1
    · rw [hr] at h1
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h1
      obtain ⟨⟨rfl, hRA⟩, hCE⟩ := h1
      have hI : Interface.ofVE (modVE B s.toModule) = I := by
        obtain ⟨RA, CE, VE'⟩ := I
        simp only at hRA hCE
        subst hRA; subst hCE
        simp [modVE, hr, Interface.ofVE]
      rw [hI] at ih ⊢
      exact .cons B _ _ _ I VE _ (evLibModule_sound hr) ih

/-- The library modules, evaluated in order in ME0 by Chapter 7's rules (r:dm-module and the rules
    of its premises), have the interfaces `libME` binds: the analogue, for the core library, of
    `elmTexts_eval` and `me0_PlatformCmd_none_eval`. -/
theorem libME_eval : EvalLib ME0 libModules libME :=
  libCheck_sound ME0 libTexts (by decide +kernel)

/-- The modules the library extends, in order. -/
theorem libME_modules : libME.map (·.1) = ["List", "Maybe", "Result", "Tuple"] := rfl

end StandardElm.Lib
