/-
  A Standard Definition of Elm? Mechanisation: the refusal deciders of plan step 9 (milestone 9d),
  in the order `lake exe certify` tries them. Each `<name>B` comes with
  `not_legal_of_<name>B : <name>B B sp = true → ¬ LegalProgram B sp`.
-/
import StandardElmMech.Stat.Refusals
import StandardElmMech.Stat.RefuseScope
import StandardElmMech.Stat.RefuseFurther
import StandardElmMech.Stat.RefuseTypes
import StandardElmMech.Stat.Complete.CoreComplete
import StandardElmMech.Stat.Complete.ModulesProgram

namespace StandardElm.Stat
open StandardElm.Src (SProgram SModule)

/-- `SynOK` reads only the modules of a program. -/
theorem synOK_of_modules {p q : SProgram} (h : q.modules = p.modules) : Src.SynOK q ↔ Src.SynOK p := by
  obtain ⟨_, _, qm⟩ := q
  obtain ⟨_, _, pm⟩ := p
  simp only at h
  subst h
  exact Iff.rfl

/-- A program of one module has one order: if it breaks the restrictions, it is refused (step 8
    refuses such a program in its canonical order only). -/
theorem not_synOKSet_of_one {p : SProgram} (h1 : p.modules.length = 1) (h : ¬ Src.SynOK p) :
    ¬ Src.SynOKSet p := by
  rintro ⟨q, hperm, _, hq⟩
  obtain ⟨m, hm⟩ : ∃ m, p.modules = [m] := by
    match hp : p.modules, h1 with
    | [m], _ => exact ⟨m, rfl⟩
  rw [hm] at hperm
  have hqm : q.modules = [m] := List.perm_singleton.mp hperm
  exact h ((synOK_of_modules (hqm.trans hm.symm)).mp hq)

/-- The refusal of a one-module program step 8 refuses in its canonical order. -/
theorem not_legal_of_syn_one {B : SBasis} {sp : SProgram} (h1 : sp.modules.length = 1)
    (h : ¬ Src.SynOK sp) : ¬ LegalProgram B sp :=
  not_legal_of_syn (not_synOKSet_of_one h1 h)

theorem modulesSynOK_of_synOK {p : SProgram} (h : Src.SynOK p) : Src.ModulesSynOK p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- A text without `main` (a module tested alone) that breaks a restriction other than
    res:program-main, whatever the order of its modules. -/
theorem not_legal_of_modsyn {B : SBasis} {sp : SProgram} (h : ¬ Src.ModulesSynOKSet sp) :
    ¬ LegalProgram B sp := by
  rintro ⟨⟨q, hp, hl, hq⟩, _⟩
  exact h ⟨q, hp, hl, modulesSynOK_of_synOK hq⟩

/-- The same for a text of one module that step 8 refuses in its canonical order. -/
theorem not_legal_of_modsyn_one {B : SBasis} {sp : SProgram} (h1 : sp.modules.length = 1)
    (h : ¬ Src.ModulesSynOK sp) : ¬ LegalProgram B sp := by
  rintro ⟨⟨q, hperm, _, hq⟩, _⟩
  obtain ⟨m, hm⟩ : ∃ m, sp.modules = [m] := by
    match hp : sp.modules, h1 with
    | [m], _ => exact ⟨m, rfl⟩
  rw [hm] at hperm
  have hqm : q.modules = [m] := List.perm_singleton.mp hperm
  obtain ⟨_, _, qm⟩ := q
  obtain ⟨_, _, pm⟩ := sp
  simp only at hqm hm
  subst hqm; subst hm
  exact h (modulesSynOK_of_synOK hq)

end StandardElm.Stat
