/-
  A Standard Definition of Elm? Mechanisation: two small tactics for the proofs about the evaluator
  (Complete.lean), where every case of a rule produces hypotheses `f args = r` about the results
  of the evaluator's recursive calls.

  * `apply_to_eqs [t1, ..., tn]`: for every hypothesis `h` of the local context whose type is an
    equation, and every term `ti` whose type is (after its implicit arguments) a function of an
    equation, adds `ti h` when it type-checks.
  * `split_ors`: repeatedly splits every hypothesis that is a disjunction.

  Only this file and Theorems.lean import `Lean`; the tactics are used at build time only.
-/
import Lean

open Lean Meta Elab Tactic

/-- `apply_to_eqs [t1, ..., tn]` adds `ti h` for every equation `h` of the context that `ti`
    accepts. -/
elab "apply_to_eqs " "[" ts:term,* "]" : tactic => withMainContext do
  let lctx ← getLCtx
  let hyps := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d
  for d in hyps do
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Eq 3 do continue
    for t in ts.getElems do
      let s ← saveState
      try
        let f ← Term.elabTerm t none
        let fty ← inferType f
        let (args, _, body) ← forallMetaTelescopeReducing fty
        if args.size == 0 then
          s.restore
          continue
        let last := args[args.size - 1]!
        let lastTy ← inferType last
        if ← isDefEq lastTy ty then
          let pf ← instantiateMVars (mkAppN f (args.pop.push d.toExpr))
          let pty ← instantiateMVars body
          if pf.hasExprMVar || pty.hasExprMVar then
            s.restore
            continue
          liftMetaTactic fun g => do
            let g' ← g.assert `h_eq pty pf
            let (_, g'') ← g'.intro1P
            return [g'']
        else s.restore
      catch _ => s.restore

/-- Split every disjunction among the hypotheses, repeatedly. -/
elab "split_ors" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let gs ← getGoals
    let mut changed := false
    let mut out : List MVarId := []
    for g in gs do
      let found ← g.withContext do
        let lctx ← getLCtx
        return lctx.findDecl? fun d =>
          if !d.isImplementationDetail && d.type.isAppOfArity ``Or 2 then some d.fvarId else none
      match found with
      | some fv =>
        let subgoals ← g.cases fv
        out := out ++ (subgoals.map (·.mvarId)).toList
        changed := true
      | none => out := out ++ [g]
    setGoals out
    if changed then go (fuel - 1)
  go 64
