/-
  The theorems of the modules StandardElmMech.* whose statement mentions D11's hypothesis
  (`PrincipalExists`, `PrincipalExistsCore`, `PrincipalExistsMod`, `PrincipalExistsFor`,
  `InferPrincipalFor`, `D11For`), split into the per-test theorems (`legal_`, `ident_`, `mean_`,
  `spec_`, `wcheck_`, `refuse_`) and the general ones (plan step 11, "Discharge", last paragraph;
  Acceptance, at (g), item 7). After milestone (g) the per-test list is the programs W does not
  elaborate (listed in `../static-report.json`, `conditional`), and the general list is the lemmas
  of steps 9 to 11 that take the hypothesis as an argument or state it.
  Run from the project folder:  lake env lean scripts/check-hypotheses.lean
-/
import StandardElmMech
open Lean Elab Command

elab "#check_hypotheses" : command => liftTermElabM do
  let env ← getEnv
  let hyps : List Name := [`StandardElm.Stat.PrincipalExists, `StandardElm.Stat.PrincipalExistsCore,
    `StandardElm.Stat.PrincipalExistsMod, `StandardElm.Stat.PrincipalExistsFor,
    `StandardElm.Stat.InferPrincipalFor, `StandardElm.Stat.D11For]
  let perTestPrefixes := ["legal_", "ident_", "mean_", "spec_", "wcheck_", "refuse_"]
  let mut perTest : Array String := #[]
  let mut general : Array String := #[]
  for (n, ci) in env.constants.toList do
    let .thmInfo info := ci | continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`StandardElmMech).isPrefixOf modName do continue
    if n.isInternal then continue
    let used := info.type.getUsedConstants
    let hit := hyps.filter (used.contains ·)
    if hit.isEmpty then continue
    let short := n.componentsRev.head!.toString
    let entry := s!"{n} ({", ".intercalate (hit.map fun h => h.componentsRev.head!.toString)})"
    if n.getPrefix == `StandardElm && perTestPrefixes.any (fun pre => short.startsWith pre) then
      perTest := perTest.push entry
    else general := general.push entry
  let perTestS := perTest.qsort (· < ·)
  let generalS := general.qsort (· < ·)
  logInfo m!"check-hypotheses: {perTestS.size} per-test theorems and {generalS.size} general theorems mention D11's hypothesis\nper-test:\n{"\n".intercalate perTestS.toList}\ngeneral:\n{"\n".intercalate generalS.toList}"

#check_hypotheses
