# Plan: evaluate the library values written in Elm

**Status (2026-11-14): done. Steps 1 to 6 done; the site's test pages name the library values a program
uses and the generated-theorems page explains `[library]`. All 28 tests are translated,
with `t_`, `spec_`, `ident_` and `mean_` theorems (18 `[native]` because they use `round`, none for
the memory budget); 608 tests end to end. One change from the steps as written: `Stat.DynOf` reads
the basis from the program's kind (`dynBasis`: `Lib.Btest` for a view, `Btest []` for a worker), so
that the worker theorems and the `mean_` theorems built on them are unchanged (L4).** Implements the mechanisation part of
[core-library.md](core-library.md), step 3, in the form decision D2 of
[lean-full-definition.md](lean-full-definition.md) settled. It does not include that plan's site
pages.

## Why

28 `elm-spec` tests that compile are not translated for one reason only. Each uses a library value
that the book leaves outside the definition (Appendix D gives `List`, `Tuple` and the rest empty
dynamic interfaces). The values are:

| Module | Values |
|--------|--------|
| `Tuple` | `first`, `second` |
| `List` | `map`, `foldl`, `foldr`, `sum`, `length`, `head` |
| `Maybe` | `map`, `withDefault`, `andThen` |
| `Result` | `map` |

Each is defined in elm/core 1.0.5 by Elm text. The text calls only other Elm text, the book's basic
values, and `List.cons`, which is the book's `::`. So the book's rules give each one a meaning, and
no new case of APPLY is needed. Lean has done this before: `Eff/TaskTexts.lean` already encodes
`foldl`, `foldr`, `foldrHelper` and `reverse` for `Task.sequence`.

The static side is done already. Since decision D2 (b), the static test basis (`Stat.Btest`,
`Generated/StaticLibrary.lean`) gives these values their elm/core annotations, and the 28 programs
have `legal_` theorems. Only the evaluation is missing.

The tests:

- **LetNumber\* (15):**
  - LetNumberAndThenTest, LetNumberAsPatternTest, LetNumberBoxedSilentMiscompileTest
  - LetNumberContainerDualTest, LetNumberDualUseTest, LetNumberFoldrTest
  - LetNumberIndirectFoldlTest, LetNumberListOfClosuresTest, LetNumberListOfMaybeTest
  - LetNumberListOfRecordsTest, LetNumberMaybeChainTest, LetNumberResultMapTest
  - LetNumberSumMapTest, LetNumberTupleBothTest, LetNumberTupleSecondTest
- **NumberGenericApp (3):** NumberGenericAppList, NumberGenericAppMaybe, NumberGenericAppTuple
- **RecordNarrow (10):**
  - RecordNarrow01CapturesNonEmptyTest to RecordNarrow06RowPolyAnnotationTest
  - RecordNarrow08NoDestructureTest, RecordNarrow09DirectCallTest, RecordNarrow10TripleNestingTest
  - RecordOpenNarrowFieldIndexTest

## Decisions

- **L1. The library is part of the dynamic test basis.** It is not text pasted into each program.
  - `Mod.Btest lib` already takes the library's interfaces (`ME0.lean`: "`lib` holds the core
    library's additions, empty until that plan's steps").
  - `libME` is what Chapter 7's rules give the library modules' texts, evaluated in `ME0`.
  - `Btest libME` extends ME0's interfaces of `List`, `Tuple`, `Maybe` and `Result` with the values.
  - It is the dynamic counterpart of the static `Stat.Btest`, which has had the library since D2 (b).
- **L2. The texts are elm/core 1.0.5's, read from `definition/library/elm-core-1.0.5/`.**
  - The translator writes them into Lean as modules: one per library module, holding the values
    the tests use and the values their texts name, transitively.
  - A text that names `Elm.Kernel.*` is refused, with one exception: `List.cons` is written `::`.
    `cons = Elm.Kernel.List.cons` is the list constructor, which the book has.
  - The modules' texts are not edited.
- **L3. Copies at Int.**
  - A text whose scheme quantifies a `number` variable (`List.sum`) is specialised as the
    program's own code is. Its default copy is at Float, and it has a copy at Int (`sum$Int`).
  - The interface binds both, as ME0 binds `abs` and `abs$Int`.
  - In the translator, an occurrence at Int refers to the copy, as for `abs`.
  - In Lean's pipeline, `List.sum` joins `basisCopies` in `Stat/Specialise.lean`. That list is
    already waiting for it.
- **L4. One test basis for every view program.**
  - The program theorems (`t_`) and the meaning theorems (`mean_`, through `DynOf`) state the
    evaluation in `Btest libME`, with the empty library replaced everywhere.
  - A program that uses no library value evaluates the same either way. The static basis is
    already uniform.
  - The worker theorems (`Prog/`, hand proofs included) keep `Btest []`. No worker test uses a
    library value, and their proofs need not change.
- **L5. A new trust tag, `[library]`.**
  - The theorem of a program whose modules name a library value carries `[library]`. It means
    that elm/core 1.0.5's Elm text is the meaning of the library values the program uses.
  - The book does not bind them; this is D2's harness assumption, extended from the static
    interfaces to the dynamic values.
  - It goes in the trust table of `lean-full-definition.md` and the Lean README, and in the site's
    account of the tags.
- **L6. Out of scope.**
  - Kernel values, even where a model text would do: `List.map2`, so LetNumberMap2Test stays out.
  - `Array`: the book models arrays abstractly, so elm/core's text over `JsArray` would contradict
    Appendix D.
  - `Dict`, `String`, `Bitwise`, `Bytes`, `Json`.
  - core-library.md's site pages.

## Steps

1. **Translator: the library modules.**
   - A table of the library values the translator evaluates (the 12 above).
   - From the vendored files, the closure of their texts. `List.map` needs `foldr`, `foldrHelper`
     and `foldl`; `foldrHelper` needs `reverse`; `length` and `sum` need `foldl`.
   - The closure is written as modules in module form (`Generated/Library.lean`), exposing the
     values and their copies, translated and specialised by the translator's own pipeline.
   - `--check` covers the new file, which is written in the current layout of Generated.
2. **Lean: `libME`.**
   - `Lib.libME : Mod.ModEnv` is the interfaces that `Mod.evModule` gives the library modules,
     evaluated in order in `ME0`.
   - A theorem that each one's evaluation is Chapter 7's derivation, from the evaluator's
     soundness: the analogue of `elmTexts_eval` and `me0_PlatformCmd_none_eval`.
   - `Lib.Btest := Mod.Btest Lib.libME`.
3. **Lean: the test basis.**
   - `#mod_program_theorems` (`Theorems.lean`), `DynOf` (`Stat/Pipeline.lean`) and the lemmas
     that give `mean_` (`Stat/Complete/Discharge.lean`) use `Lib.Btest`.
   - `basisCopies` gains `("List", "sum")`.
   - The theorems' docstrings add `[library]` where the program names a library value.
4. **Translator: the programs.**
   - `Convert.qualifiedValue` (and its unqualified form) accepts the table's values.
   - `Infer` reads their schemes from the annotations it already parses for `StaticLibrary.lean`.
   - The specialiser's `basisOccurrence` handles every number-quantified value of the basis and
     the library (`abs`, `List.sum`), not `abs` alone.
   - The manifest and the docstring record which library values a program uses.
5. **Translate the 28 tests and prove them.**
   - Run the translator and `certify`, then `scripts/verify.sh full`.
   - Each test gains `t_`, `spec_`, `ident_` and `mean_` (`mean_` unless it stops at
     Debug.todo).
   - A test the kernel cannot check within the memory budget is proved by `native_decide` and
     listed, as the conventions say.
   - A test that still does not translate is listed with its reason.
6. **Documents and site.**
   - Update the Lean README, `mechanisation-report.md` (a dated block), the trust table and step
     list of `lean-full-definition.md`, core-library.md's status (step 3 done, in this form), and
     untranslated-tests.md's group D.
   - Regenerate the site data, build the site and run the link audit. The coverage table's
     "uses Tuple.second, which the encoding does not include" rows become translations.

## Acceptance

`scripts/verify.sh full` passes, with these results:

- **Translator:** `--check` is up to date.
- **Static semantics:** `certify` keeps 622 `legal_`, 287 refused and 0 conditional.
- **End to end:** `spec_`, `ident_` and compare-e2e each rise by the number of tests gained.
- **Examples:** run-examples agrees on every check.
- **Axioms:** check-axioms finds 0 problems, and no theorem rests on an axiom it did not before.
- **Nothing lost:** no existing theorem is lost.

The plan's status line and the report say how many of the 28 tests were gained, and why any were
not.
