/-
  Every theorem of the modules StandardElmMech.* depends only on the axioms propext,
  Classical.choice and Quot.sound, and, when its docstring contains `[native]`, also on the axioms
  native_decide introduces (in Lean 4.35 an axiom `<theorem>._native.native_decide.ax_...` per theorem). `sorryAx` is never allowed.
  Run from the project folder:  lake env lean scripts/check-axioms.lean
  (plans/lean-full-definition/conventions.md, "Proofs")
-/
import StandardElmMech
open Lean Elab Command

elab "#check_axioms" : command => liftTermElabM do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  -- native_decide adds an axiom per theorem, named `<theorem>._native.native_decide.ax_...`
  -- (Lean 4.35), or uses Lean.ofReduceBool (earlier toolchains)
  let isNative (a : Name) : Bool :=
    a.components.contains `_native || a == `Lean.ofReduceBool || a == `Lean.trustCompiler
  let mut total : Nat := 0
  let mut nativeCount : Nat := 0
  let mut problems : Array String := #[]
  let mut overstated : Array String := #[]
  for (n, ci) in env.constants.toList do
    let .thmInfo _ := ci | continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`StandardElmMech).isPrefixOf modName do continue
    if n.isInternal then continue
    total := total + 1
    let axs ← Lean.collectAxioms n
    let doc ← findDocString? env n
    let tagged := (doc.getD "").contains "[native]"
    let usesNative := axs.any isNative
    if usesNative then nativeCount := nativeCount + 1
    for a in axs do
      if standard.contains a then continue
      if isNative a && tagged then continue
      problems := problems.push s!"{n} uses {a}"
    if tagged && !usesNative then overstated := overstated.push n.toString
  for w in overstated do logWarning m!"check-axioms: {w} is tagged [native] but uses no native axiom"
  if problems.isEmpty then
    let plain := total - nativeCount
    logInfo m!"check-axioms: {total} theorems ({plain} without native axioms, {nativeCount} native), 0 problems"
  else
    throwError m!"check-axioms: {problems.size} problem(s):\n{"\n".intercalate problems.toList}"

#check_axioms
