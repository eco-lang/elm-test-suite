/-
  A Standard Definition of Elm? Mechanisation: the restrictions of a program as written, the set of
  its modules (sec:programs-syntax), plan step 8. `SynOKSet p`: some sequence of its modules, with
  the same main module, meets the restrictions. A sequence that meets them is a witness
  (`synOKSet_of_synOK`). A program is refused whatever the order of its modules when a module breaks
  a module restriction, when it breaks res:modules-program (both are conditions on the set), when
  a module imports a module that is neither in the basis nor among the program's modules, or when
  two modules import each other (res:program-import-order fails for the one that comes first).
-/
import StandardElmMech.Src.Restrictions

namespace StandardElm.Src

def SynOKSet (p : SProgram) : Prop :=
  ∃ q : SProgram, q.modules.Perm p.modules ∧ q.modules.getLast? = p.modules.getLast? ∧ SynOK q

def ModulesSynOKSet (p : SProgram) : Prop :=
  ∃ q : SProgram, q.modules.Perm p.modules ∧ q.modules.getLast? = p.modules.getLast? ∧ ModulesSynOK q

theorem synOKSet_of_synOK {p : SProgram} (h : SynOK p) : SynOKSet p := ⟨p, List.Perm.refl _, rfl, h⟩

theorem modulesSynOKSet_of {p : SProgram} (h : ModulesSynOK p) : ModulesSynOKSet p :=
  ⟨p, List.Perm.refl _, rfl, h⟩

/-! ## Refusals whatever the order -/

/-- The conditions every sequence must meet that depend only on the set of modules. -/
def SetFails (p : SProgram) : Prop :=
  (∃ m ∈ p.modules, ¬ ModuleOK m) ∨ ¬ (p.modules.flatMap SModule.ports).Nodup ∨
  (∃ m ∈ p.modules, m.header.name ∈ basisModuleIds) ∨
  (∃ m ∈ p.modules, ∃ mod ∈ m.imports.map (·.mod), mod ∉ basisModuleIds ∧ ∀ m' ∈ p.modules, m'.header.name ≠ mod)

/-- Two modules import each other. -/
def TwoCycle (p : SProgram) : Prop :=
  ∃ a ∈ p.modules, ∃ b ∈ p.modules, a.header.name ≠ b.header.name ∧
    b.header.name ∈ a.imports.map (·.mod) ∧ a.header.name ∈ b.imports.map (·.mod) ∧
    a.header.name ∉ basisModuleIds ∧ b.header.name ∉ basisModuleIds

instance : DecidablePred SetFails := fun p => by unfold SetFails; infer_instance
instance : DecidablePred TwoCycle := fun p => by unfold TwoCycle; infer_instance

/-- In a sequence meeting res:program-import-order and res:program-modules-distinct, a module that
    imports a module of the program comes after it. -/
theorem import_before {q : SProgram} (hio : ImportOrder q) {i : Nat}
    (hi : i < q.modules.length) {mod : ModId} (hm : mod ∈ q.modules[i].imports.map (·.mod))
    (hnb : mod ∉ basisModuleIds) : ∃ j < i, (q.modules[j]?.map (·.header.name)) = some mod :=
  ((hio i hi q.modules[i] (by simp [List.getElem?_eq_getElem hi]) mod
    (List.mem_append_right _ hm)).resolve_left hnb)

theorem not_twoCycle {q : SProgram} (hio : ImportOrder q) (hd : ModulesDistinct q) : ¬ TwoCycle q := by
  rintro ⟨a, ha, b, hb, hne, hab, hba, hna, hnb⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have hnames := List.pairwise_iff_getElem.mp hd.1
  -- the module named n is at the index where n stands
  have uniq : ∀ k l (hk : k < q.modules.length) (hl : l < q.modules.length),
      q.modules[k].header.name = q.modules[l].header.name → k = l := by
    intro k l hk hl he
    apply Classical.byContradiction
    intro hkl
    rcases Nat.lt_or_gt_of_ne hkl with h | h
    · exact hnames k l (by simpa using hk) (by simpa using hl) h (by simpa using he)
    · exact hnames l k (by simpa using hl) (by simpa using hk) h (by simpa using he.symm)
  obtain ⟨j', hj', hj'e⟩ := import_before hio hi hab hnb
  obtain ⟨i', hi', hi'e⟩ := import_before hio hj hba hna
  have hj'l : j' < q.modules.length := by omega
  have hi'l : i' < q.modules.length := by omega
  simp only [List.getElem?_eq_getElem hj'l, List.getElem?_eq_getElem hi'l, Option.map_some,
    Option.some.injEq] at hj'e hi'e
  have := uniq _ _ hj'l hj hj'e
  have := uniq _ _ hi'l hi hi'e
  omega

theorem setFails_perm {p q : SProgram} (hp : q.modules.Perm p.modules) (h : SetFails p) : SetFails q := by
  rcases h with ⟨m, hm, h⟩ | h | ⟨m, hm, h⟩ | ⟨m, hm, mod, hmod, h1, h2⟩
  · exact .inl ⟨m, hp.mem_iff.mpr hm, h⟩
  · have hpf : (q.modules.flatMap SModule.ports).Perm (p.modules.flatMap SModule.ports) := by
      have := (hp.map SModule.ports).flatten
      rw [List.flatMap_def, List.flatMap_def]; exact this
    exact .inr (.inl fun h' => h (hpf.nodup_iff.mp h'))
  · exact .inr (.inr (.inl ⟨m, hp.mem_iff.mpr hm, h⟩))
  · exact .inr (.inr (.inr ⟨m, hp.mem_iff.mpr hm, mod, hmod, h1, fun m' hm' => h2 m' (hp.mem_iff.mp hm')⟩))

theorem twoCycle_perm {p q : SProgram} (hp : q.modules.Perm p.modules) (h : TwoCycle p) : TwoCycle q := by
  obtain ⟨a, ha, b, hb, rest⟩ := h
  exact ⟨a, hp.mem_iff.mpr ha, b, hp.mem_iff.mpr hb, rest⟩

/-- A sequence meeting the restrictions fails none of the set conditions. -/
theorem not_setFails_of {q : SProgram} (hm : ∀ m ∈ q.modules, ModuleOK m) (hmp : ModulesProgram q)
    (hd : ModulesDistinct q) (hio : ImportOrder q) : ¬ SetFails q := by
  rintro (⟨m, hm', h⟩ | h | ⟨m, hm', h⟩ | ⟨m, hm', mod, hmod, h1, h2⟩)
  · exact h (hm m hm')
  · exact h hmp.1
  · exact hd.2 m hm' h
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm'
    obtain ⟨j, hj, he⟩ := import_before hio hi hmod h1
    have hjl : j < q.modules.length := by omega
    simp only [List.getElem?_eq_getElem hjl, Option.map_some, Option.some.injEq] at he
    exact h2 _ (List.getElem_mem hjl) he

theorem notSynOKSet_of_setFails {p : SProgram} (h : SetFails p) : ¬ SynOKSet p := by
  rintro ⟨q, hp, _, hm, hmp, hd, hio, _, _⟩
  exact not_setFails_of hm hmp hd hio (setFails_perm hp h)

theorem notSynOKSet_of_twoCycle {p : SProgram} (h : TwoCycle p) : ¬ SynOKSet p := by
  rintro ⟨q, hp, _, _, _, hd, hio, _, _⟩
  exact not_twoCycle hio hd (twoCycle_perm hp h)

theorem notModulesSynOKSet_of_setFails {p : SProgram} (h : SetFails p) : ¬ ModulesSynOKSet p := by
  rintro ⟨q, hp, _, hm, hmp, hd, hio, _⟩
  exact not_setFails_of hm hmp hd hio (setFails_perm hp h)

theorem notModulesSynOKSet_of_twoCycle {p : SProgram} (h : TwoCycle p) : ¬ ModulesSynOKSet p := by
  rintro ⟨q, hp, _, _, _, hd, hio, _⟩
  exact not_twoCycle hio hd (twoCycle_perm hp h)

end StandardElm.Src
