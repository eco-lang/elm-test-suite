# Plan: widen the part of the basis the Lean mechanisation encodes

**Status (2026-11-09): steps 1 to 5 done** (see Progress); step 6 is outside the basis. This is phase 6 of
[elm-to-lean-translator.md](elm-to-lean-translator.md), "widen the fragment (separate plans), guided
by the manifest's `basis:` and `construct:` counts". Its first step, `Basics.isNaN`, is done (with
`Basics.isInfinite`), and retired the last partial hand translation; this plan orders the rest.

## Where things stand

`definition/mechanisation/translation-manifest.json` (2026-11-09): 941 `elm-spec` tests, 381
translated. Of the 560 refused, 308 expect a compile error (static semantics, not encoded) and 54
use effects (Chapters 8 and 9, not encoded). The rest, by reason:

| Tests | Reason | In the book's initial basis? |
|------:|--------|------------------------------|
| 48 | `basis:Basics.round` | yes (Appendix C, D: conversions) |
| 28 | `basis:Basics.append` (`++`) | yes |
| 14 | `basis:Char.toCode` | yes |
| 10 | `basis:Tuple.second` | no: a library function |
| 6 | `basis:Basics.toFloat` | yes |
| 4 | `basis:Basics.truncate` | yes |
| 2 each | `basis:Basics.floor`, `Basics.ceiling`, `Basics.sqrt`, `Debug.toString`, `Basics.pow@Float` | yes |
| 1 each | `basis:Char.fromCode`, `Basics.sin`, `tan`, `asin`, `acos`, `atan`, `atan2`, `e` | yes |
| 2, 3, 2, 1, 1, 1 | `basis:Tuple.first`, `List.map`, `Maybe.withDefault`, `Maybe.map`, `Maybe.andThen`, `List.map2` | no: library functions |
| 3, 2 | `basis:Result.Ok`, `Result.Err` | yes: constructors of `Result` (corrected 2026-11-09; see [untranslated-tests.md](untranslated-tests.md)) |
| 5 | `construct:record-alias-constructor` | a record alias's constructor (Chapter 7) |
| 5 | `construct:large-program` | tests of a compiler's limits; stay out |
| 15 | `checks:*` | the test's CHECK lines (B.2 of the translator plan) |
| 11 | `import:*` | other modules (Chapter 7) |
| 3, 3, 1 | `construct:main-shape`, `parse`, `construct:large-type` | the test's shape; elm-syntax |

Library functions (`Tuple`, `List`, `Maybe`, and `Result`'s functions but not its constructors) are not in the book's initial basis, so
their tests stay out by design: they test elm/core, not the language. (A later proposal,
[core-library.md](core-library.md), would specify elm/core against the book on the site and bring
these tests in as library checks.)

## Steps, in order of tests gained

Each step: encode the basic values in Lean following Appendix D exactly; bind them in
`InitialBasis.lean`; give them their schemes in the translator's `Translate/Basis.elm` (from
Appendix C) and add them to `basicsValues` in `Translate/Convert.elm`; add a unit test to
`definition/tools/tests/TranslateTest.elm`; run the translator, `lake build` (which re-proves
`applySet_sound` with the new constructors) and `lake exe run-examples`. Done when every new check
agrees, or each disagreement is a recorded finding about the book, and the site data is rebuilt.

1. **Conversions** (`round`, `truncate`, `floor`, `ceiling`, `toFloat`; 62 tests). Appendix D
   defines them with saturation into the Int range (`sat`), `round` rounding half up exactly
   (`x + 1/2` is exact, not a float addition), NaN to 0 and the infinities to the ends of the
   range. Lean: compute `floor` and `ceiling` of a float exactly (`Float.floor` is exact), and
   `round` as `floor x`, plus 1 when `x - floor x >= 1/2` (exact for finite floats), then `sat`;
   `toFloat` is the nearest float. Theorems for the A44 examples (`round 2.5` is 3, `round -2.5` is
   -2, NaN is 0).
2. **`++`** (`append`, 28 tests). At strings, concatenation; at lists, the list of both. A new
   basic value of arity 2; `appendable` and `compappend` in the translator's classes are already
   kept. Check `showElm` on the results of string concatenation with escapes.
3. **`Char.toCode`, `Char.fromCode`** (15 tests). The `code` function of the book's Char model
   (ruling of 2026-11-08: injective, the code of a scalar value is that value, `other(n)` for any
   other n); the encoding needs a qualifier `Char` in E0.
4. **`sqrt` and the elementary functions, `e`, Float `^`** (12 tests). Appendix D defines them as
   the IEEE 754 operations, correctly rounded where IEEE requires it; Lean's `Float` operations
   call the C library, which is not correctly rounded for all of them. Encode only those IEEE
   specifies exactly (`sqrt`) as theorems; for the rest, an encoding is possible but a theorem
   would trust the C library, which must be said on the theorem's page.
5. **`Debug.toString`** (2 tests). A printing function: `showElm` exists; the book's text for it
   must be checked against `showElm` first.
6. **Translator side, not basis**: record alias constructors (5) belong to Chapter 7, which a
   later mechanisation of the module level would bring in; `checks:*` (15) are fixed in the tests
   (an exact `label: value` CHECK line for each logged check), not in the translator.

## Out of scope

Compile-error tests (the static semantics), effects and programs, modules and imports, library
functions outside the book's basis, and tests of a compiler's limits.

## Progress

**2026-11-09: steps 1 to 5 done.** 487 of the 941 `elm-spec` tests translate (from 381); the run
has 1,477 checks, all agreeing, and 1,106 theorems by `decide +kernel` (from 985).

- **Lean.** `BasVal` gains toFloat, round, floor, ceiling, truncate, sqrt, sin, cos, tan, asin,
  acos, atan, atan2, append, charToCode, charFromCode and debugToString; `Apply` a constructor for
  each (and `pow_float`), `applySet` its cases, and `applySet_sound` is re-proved by its automation
  unchanged. The functions (`Apply.lean`) follow Appendix D's displays line by line: `satOfFloat`
  (by `Float.toInt64`, which truncates and saturates into [-2^63, 2^63 - 1] with NaN to 0, so it
  is sat on an integral float or an infinity, and the 0 of NaN), `fRound` (floor x, plus 1 when
  x - floor x >= 1/2, exact for a finite float), `fSqrt`, `fPow` (fig:dynamic-basis-pow),
  `fElem` and `fAtan2` (fig:dynamic-basis-elem), `appendVal`, `charFromCode` (U+FFFD for the
  book's `other(n)`). InitialBasis.lean binds the new names of Basics, `e` and `pi` as their
  floats, and `++` in OT_dyn to `append`; Basis.lean adds `Debug.toString` and a qualifier `Char`
  with `toCode` and `fromCode`.
- **What the kernel cannot do.** `Float.floor`, `Float.ceil`, the elementary functions,
  `Float.pow` and float printing are C library calls the kernel does not reduce (probed). A program
  that uses one of those values, or `^` at Float, is marked `native := true` by the translator
  (`Specialise.nativeValues`; `^` at Float becomes `^@Float` in the translator's representation,
  printed as `^`), and `kernelCheck?` leaves its checks to `derivable_<Shard>` (`native_decide`);
  `run-examples`, the site and the coverage table give the reason `native`. `toFloat`, `sqrt`,
  `++` and the Char functions reduce, so their programs keep their kernel theorems.
- **The C library.** The last line of `fPow` and of `fElem` is the C library's rounding of the
  real function, which the book allows (accuracy is implementation-dependent); the theorems that
  depend on it are the `native_decide` ones, and a native check's page says its value is computed
  by the C library.
- **Theorems.** `a44_conversions` (round, floor, ceiling, truncate at 2.5, -2.5, NaN, the
  infinities and 1e300) and `a44_round_minus_half` (`round -2.5` is -2 from E0), by
  `native_decide`.
- **Findings on the way.** (1) `showFloat` used Lean's `toString`, six significant digits, so the
  first checks of long floats (`e`, `atan2 1 1`) disagreed: floats now print as JavaScript's
  Number::toString, the shortest decimal that reads back as the float, decided exactly with
  integers against the float's rounding interval (no float parsing); 3000 random floats print as
  node prints them. (2) The translator read a literal's text with `String.slice`, in UTF-16 units,
  while elm-syntax counts columns in code points, so an astral character earlier on the line
  shifted the cut (`Pair 1 '𝄞'` after `'😀'`): fixed, with a test. (3) WideRecordGcBitmapTest,
  a GC test that builds lists of 150000 elements, translates now but is beyond the evaluator's fuel
  and the kernel's recursion: refused as `construct:large-computation`.
- **Cost.** The full build's peak memory rose from 3.7 GB to 6.3 GB, and the time to about 1.5
  minutes.
- **Translator tests.** 53 pass (refusals updated; `++` at String and List, conversions,
  `^` at Float and at Int, the Char functions and `Debug.toString`, a literal after an astral
  character).

No book finding: every new check agrees with the book's definitions as written.

The tests still refused, each with what it would take to translate, are assessed in
[untranslated-tests.md](untranslated-tests.md).
