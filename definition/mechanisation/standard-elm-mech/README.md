# Standard Elm: mechanisation of the Core dynamic semantics (Lean 4)

A Lean 4 encoding of Chapter 6 of *A Standard Definition of Elm?* (Dynamic
Semantics for the Core, `dynamic-core.tex`) and of the arithmetic, equality,
order and Boolean part of APPLY (Appendix D,
`sec:appendix-dynamic-basis-apply`), with an executable evaluator proved sound
for the rules, and a corpus of examples from the test programs that accompany the book.

## Build and run

Requires Lean 4.35.0 and Lake (`elan` installs both; put `~/.elan/bin` on the
PATH). From this folder:

```
lake build && lake exe run-examples
```

`lake build` checks every definition and proof: the 48 rules, the soundness
theorem, and one `decide +kernel` theorem per kernel-checkable example (the
build prints how many). `lake exe run-examples` evaluates every example with
both choices of a member of APPLY and prints a Markdown table of
implementation value, definition value and status. The first build takes
about a minute.

## Files

| File | Contents |
|------|----------|
| `StandardElmMech/Syntax.lean` | Bare Core syntax after the reduced syntax: AtExp, ExpRow, Exp, Match, MRule, Dec, ValBind, AtPat, PatRow, Pat; special constants typed Int or Float by number specialisation |
| `StandardElmMech/Objects.lean` | SVal, BasVal, Con, Val, Env, ValEnv, Record, VE/FAIL; finite maps; Rec; FV; the Int range parameter (`norm`, eco's 64-bit wrap) |
| `StandardElmMech/Apply.lean` | Eq and cmp as functions; IEEE 754-2019 minimum and maximum (`fMinimum`, `fMaximum`) and clamp at floats built on them (`fClamp`); APPLY as the relation `Apply` (one constructor per line of the book's displays) and as the executable `applySet`, with `applySet_sound` |
| `StandardElmMech/InitialBasis.lean` | The parts of Appendix D the rules read: VE0, VE_K, E_K, the values of the Elm texts of abs, composeL/R, apR/L, identity, always, and the dynamic operator table OT_dyn |
| `StandardElmMech/Rules.lean` | The 48 rules as mutually inductive relations, one constructor per rule, named `r_d_<slug>` after the label `r:d-<slug>` |
| `StandardElmMech/Eval.lean` | Fuel-bounded evaluator, one function per judgement, parameterised by the choice of a member of APPLY |
| `StandardElmMech/Sound.lean` | `soundAt`, `evExp_sound`: every result of the evaluator is derivable by the rules |
| `StandardElmMech/Derived.lean` | Derived forms of Appendix A as functions, including the grouping of a let into components |
| `StandardElmMech/Basis.lean` | E0 for the examples: E0 of Appendix D plus what the default imports add |
| `StandardElmMech/Show.lean` | Prints values as eco's Debug.log output does (test harness only) |
| `StandardElmMech/Examples.lean` | The examples, every one a test program of `tests/`: a corpus of 40, 12 tests of the rulings, 3 tests for rule coverage |
| `StandardElmMech/Theorems.lean` | Theorems that the rules derive the examples' values |
| `Main.lean` | The `run-examples` executable |

## Encoding conventions

* Each rule is one constructor; its label is in its doc comment. The option
  convention (R6) and the sequences of `r:d-pat-con` use small auxiliary
  relations (`EvalExpOpt`, `EvalExpRowOpt`, `EvalValBindOpt`, `MatchPatOpt`,
  `MatchPatRowOpt`, `MatchAtPats`) whose constructors are `opt_none`,
  `opt_some`, `seq_nil` and `seq_cons`; they are not book rules.
* Finite maps are association lists. `f + g` puts `g` first and drops from `f`
  the keys of `g`; lookup takes the first binding.
* A constructor name carries its arity (`Con = name x arity`), since
  `arity(con)` is "the arity of con in the custom type of the value at hand".
* APPLY's set is a list; the evaluator takes its first member (`ch = false`)
  or its last (`ch = true`), so for function equality the two runs give the
  two results.
* Floats are Lean's `Float` (IEEE 754 binary64) for add, sub, mul, fdiv and
  negate, equality, order, min, max and clamp. Float `pow`, the elementary functions and the
  conversions are not encoded.
* Number specialisation is not computed: examples are written after it, with
  `SCon.int` for an integer constant at Int and `SCon.intF` for one at Float.
* Top-level definitions of an example's module are placed in a `let` around
  the logged expression, and its custom types' constructors are bound in the
  environment (Chapter 7 is outside this encoding).
* An operator's value is read from the dynamic operator table OT_dyn
  (rule r:d-atexp-op as revised by audit X1); it is looked up in no
  environment.

## What the theorems say

* `evExp_sound`: if `evExp ch n E e = some v` then `EvalExp E e v`.
* `kc_<n>` (generated): for an example whose value is an Int, a constructor
  without arguments or a string, `∃ v, EvalExp E e v ∧ v` is that value;
  proved by the kernel (`decide +kernel`), no `native_decide`.
* `corpus_derivable`: for every check of the 40 corpus programs,
  `∃ v, EvalExp E e v ∧ showElm v = CHECK value` (by `native_decide`).
* `rulings_derivable`: the same for the ruling programs (but for any check
  listed in `knownDiv`, which is now empty).
* `coverage_derivable`: the same for the coverage programs' checks that
  expect a value. A check that expects no value (the program stops at
  `Debug.todo`) is checked by `run-examples` only: soundness speaks only of
  the values the evaluator gives.
* `a48_float`, `a48_int_max`, `a48_int_min`: APPLY(max) and APPLY(min) are
  IEEE 754-2019 maximum and minimum at floats in either argument order, and
  the comparison at Int.
* `a49_apply_float`, `a49_float_lo_gt_hi`, `a49_float_nan_bound`,
  `a49_float_signed_zero` (`native_decide`, floats compared as printed):
  at floats APPLY(clamp, lo, hi, x) is min (max x lo) hi with those
  operations, so `clamp 10 0 5` is +0, `clamp nan 1 0.5` is NaN and
  `clamp 0 1 -0` is +0. `a49_int_lo_gt_hi` (kernel) and
  `a49_int_apply_singleton`: at Int, `clamp 10 0 5` is 10, the elm/core
  text's result, and APPLY's set has that one member.
* `elmTexts_eval`: each Elm text of the fragment evaluates in E_K, by
  r:d-dec-nonrec, to the closure that InitialBasis.lean binds.
* `a43_*`, `a42_*`, `a51_true`, `a51_false`: the rulings stated directly;
  `a51_true` and `a51_false` show that `(\x -> x) == (\x -> x)` evaluates to
  both True and False.

Soundness only: the encoding does not prove that the evaluator finds every
derivable value. Where the book differs from an implementation (A43, where
eco gives 0), that is shown by the definition deriving the book's value and,
for A43, by APPLY's set having one member, not by a proof that the other
value is underivable.
