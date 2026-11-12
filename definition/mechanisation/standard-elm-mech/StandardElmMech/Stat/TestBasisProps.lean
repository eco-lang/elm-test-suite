/-
  A Standard Definition of Elm? Mechanisation: the test basis against the initial basis, plan
  step 9 (section "Theorems", group 6, D2, G2-14). By the kernel, on the finite data.
-/
import StandardElmMech.Stat.TestBasis

namespace StandardElm.Stat
open StandardElm (ModId)

/-- Btest agrees with B0 on every module other than Html and the library modules. -/
theorem Btest_agrees : ∀ M ∈ ME0.keys, M ≠ "Html" → M ∉ libModuleIds →
    FMap.find? Btest.ME M = FMap.find? ME0 M := by decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
/-- On a library module, Btest has ME0's type environment and a larger value environment. -/
theorem Btest_lib_extends : ∀ M ∈ libModuleIds, M ∈ ME0.keys →
    (FMap.find? Btest.ME M).map (·.TE) = (FMap.find? ME0 M).map (·.TE) ∧
    ∀ b ∈ ((FMap.find? ME0 M).map (·.VE)).getD [],
      ((FMap.find? Btest.ME M).map fun I => FMap.find? I.VE b.1) = some (some b.2) := by
  decide +kernel

/-- The harness's Html. -/
theorem Btest_html : FMap.find? Btest.ME "Html" = some harnessHtml := by decide +kernel

/-- Every library module is a module of ME0: the library adds no module and no type name. -/
theorem libModules_in_ME0 : ∀ M ∈ libModuleIds, M ∈ ME0.keys := by decide +kernel

/-- The provider maps the default imports give in B0 and in Btest. -/
def πB0 : ProvMap := (elabImports B0stat π0 defaultImports).getD []
def πBtest : ProvMap := (elabImports Btest π0 defaultImports).getD []

/-- Under the default imports alone, Btest changes no unqualified identifier and no identifier that
    B0 provides: it only adds qualified `M.x` for library values, so it makes nothing ambiguous. -/
theorem default_imports_test :
    (elabImports B0stat π0 defaultImports).isSome ∧ (elabImports Btest π0 defaultImports).isSome ∧
      (∀ l ∈ πBtest.keys, l.qual = none → FMap.find? πBtest l = FMap.find? πB0 l) ∧
      (∀ l ∈ πB0.keys, FMap.find? πBtest l = FMap.find? πB0 l) := by
  decide +kernel

end StandardElm.Stat
