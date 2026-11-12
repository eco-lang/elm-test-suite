/-
  A Standard Definition of Elm? Mechanisation: properties of Chapter 7's derivations, plan step 2.

  * The frame lemma (plan decision D3): a module's derivation reads the basis only at the modules it
    imports, so a partial ME0 (one without Task, Process, ...) gives a program that does not import
    them the same meanings and logs as the book's ME0 would.
  * The Btest lemma (decision D2): the test basis agrees with ME0 on every module but Html and the
    modules of the library parameter.
-/
import StandardElmMech.Mod.Complete
import StandardElmMech.Mod.ME0

namespace StandardElm.Mod
open StandardElm

/-! ## Finite maps -/

theorem fmLookup_append {β : Type} (l1 l2 : List (String × β)) (a : String) :
    fmLookup (l1 ++ l2) a = match fmLookup l1 a with
      | some x => some x
      | none => fmLookup l2 a := by
  induction l1 with
  | nil => simp [fmLookup]
  | cons p l1 ih =>
    obtain ⟨k, x⟩ := p
    simp only [List.cons_append, fmLookup]
    split <;> simp_all

theorem fmLookup_filter {β : Type} (f : List (String × β)) (P : String → Bool) (a : String) :
    fmLookup (f.filter (fun p => P p.1)) a = if P a then fmLookup f a else none := by
  induction f with
  | nil => simp [fmLookup]
  | cons p f ih =>
    obtain ⟨k, x⟩ := p
    simp only [List.filter_cons]
    by_cases hk : k = a
    · subst hk; by_cases hP : P k <;> simp [hP, fmLookup, ih]
    · have hka : (k == a) = false := by simpa using hk
      split <;> simp [fmLookup, hka, ih]

theorem fmLookup_none_iff {β : Type} (g : List (String × β)) (a : String) :
    fmLookup g a = none ↔ (g.any fun q => q.1 == a) = false := by
  induction g with
  | nil => simp [fmLookup]
  | cons p g ih =>
    obtain ⟨k, x⟩ := p
    simp only [fmLookup, List.any_cons]
    split <;> simp_all

theorem fmLookup_fmPlus {β : Type} (f g : List (String × β)) (a : String) :
    fmLookup (fmPlus f g) a = match fmLookup g a with
      | some x => some x
      | none => fmLookup f a := by
  unfold fmPlus
  rw [fmLookup_append]
  cases h : fmLookup g a with
  | some x => rfl
  | none =>
    have hg := (fmLookup_none_iff g a).mp h
    have := fmLookup_filter f (fun k => !(g.any fun q => q.1 == k)) a
    simp only [hg, Bool.not_false, ite_true] at this
    exact this

/-! ## The frame lemma -/

theorem EvalImports.frame {B B' : Basis} : ∀ {is : List Import} {E : Env},
    EvalImports B is E → (∀ md ∈ is.map (·.modid), fmLookup B md = fmLookup B' md) →
    EvalImports B' is E
  | _, _, .r_dm_imports_import _ m q el rest I I' E h1 h2 h3, h => by
    have hm : fmLookup B m = fmLookup B' m := h m (by simp)
    have h1' : fmLookup B' m = some I := by rw [← hm]; exact h1
    exact .r_dm_imports_import B' m q el rest I I' E h1' h2
      (EvalImports.frame h3 (fun md hmd => h md (by simp [hmd])))
  | _, _, .r_dm_imports_empty _, _ => .r_dm_imports_empty B'

/-- The modules a module imports. -/
def Module.imported (m : Module) : List ModId := m.imports.map (·.modid)

/-- A module's derivation reads the basis only at the modules it imports. -/
theorem EvalModuleL.frame {B B' : Basis} : ∀ {m : Module} {B'' : Basis} {VE : ValEnv} {l : Log},
    EvalModuleL B m B'' VE l → (∀ md ∈ m.imported, fmLookup B md = fmLookup B' md) →
    EvalModuleL B' m B'' VE l
  | _, _, _, _, .r_dm_module_l _ hd is td E I mid I' l1 h1 h2 h3, h =>
    .r_dm_module_l B' hd is td E I mid I' l1 (EvalImports.frame h1 h) h2 h3

/-- The modules the modules of a program import. -/
def allImported (p : List Module) : List ModId := p.flatMap Module.imported

/-- A program's derivation reads the basis only at the modules its modules import. -/
theorem EvalProgramL.frame : ∀ {B B' : Basis} {p : List Module} {v : Val} {l : Log},
    EvalProgramL B p v l → (∀ md ∈ allImported p, fmLookup B md = fmLookup B' md) →
    EvalProgramL B' p v l
  | B, B', _, _, _, .r_p_dyn_module_l _ m p B1 VE v l1 l2 h1 h2 h3, h => by
    have hm : ∀ md ∈ m.imported, fmLookup B md = fmLookup B' md :=
      fun md hmd => h md (by simp only [allImported, List.flatMap_cons, List.mem_append]; exact Or.inl hmd)
    refine .r_p_dyn_module_l B' m p B1 VE v l1 l2 (EvalModuleL.frame h1 hm) ?_ h3
    refine EvalProgramL.frame h2 ?_
    intro md hmd
    rw [fmLookup_fmPlus, fmLookup_fmPlus]
    split
    · rfl
    · exact h md (by simp only [allImported, List.flatMap_cons, List.mem_append]; exact Or.inr hmd)
  | B, B', _, _, _, .r_p_dyn_main_l _ m B1 VE v l1 h1 h2, h =>
    .r_p_dyn_main_l B' m B1 VE v l1 (EvalModuleL.frame h1 (fun md hmd => h md (by
      simp only [allImported, List.flatMap_cons, List.flatMap_nil, List.append_nil]; exact hmd))) h2

/-! ## The test basis (D2) -/

/-- One step of Btest's fold changes only the binding of its own module. -/
theorem btestStep_other (B : Basis) (m : ModId) (I : Interface) (md : ModId) (hm : m ≠ md) :
    fmLookup (btestStep B (m, I)) md = fmLookup B md := by
  unfold btestStep
  split <;> (rw [fmLookup_fmPlus]; simp [fmLookup, hm])

theorem foldl_btest_other : ∀ (lib : ModEnv) (B : Basis) (md : ModId), md ∉ fmDom lib →
    fmLookup (lib.foldl btestStep B) md = fmLookup B md
  | [], B, md, _ => rfl
  | (m, I) :: lib, B, md, h => by
    simp only [fmDom, List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [foldl_btest_other lib _ md (by simpa [fmDom] using h.2)]
    exact btestStep_other B m I md (fun e => h.1 e.symm)

/-- D2: the test basis agrees with ME0 on every module but Html and the library's modules. -/
theorem Btest_agrees {lib : ModEnv} {md : ModId} (hHtml : md ≠ "Html") (hlib : md ∉ fmDom lib) :
    fmLookup (Btest lib) md = fmLookup ME0 md := by
  unfold Btest
  rw [foldl_btest_other lib _ md hlib, fmLookup_fmPlus]
  simp [fmLookup, Ne.symm hHtml]

end StandardElm.Mod
