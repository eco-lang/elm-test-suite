# Survey Part 3: Dynamic Semantics and Basic Operations

Scope: pure evaluation and the basic operations of the initial basis (arithmetic, comparison,
equality, Char, String basics, Bitwise). Cmd/Sub/Task/ports are covered elsewhere. Facts are
recorded for two implementations wherever they differ: **Elm-on-JS** (Elm 0.19.1 compiler plus
elm/core 1.0.5 JavaScript kernel) and **eco** (eco native output). eco's JavaScript output keeps
Elm-on-JS behaviour (eco/design_docs/float-semantics.md:10-11), so "eco" below always means the
native path.

## Sources

Path abbreviations used in every cite:

| Abbrev | Path |
|---|---|
| `eco/` | /home/rupert/sc/gitlab/eco-compiler/ |
| `core/` | /home/rupert/.eco/0.2.0/packages/elm/core/1.0.5/src/ (byte-identical to ~/.elm/0.19.1/packages/elm/core/1.0.5/src/: `diff -rq` empty) |
| `kjs/` | core/Elm/Kernel/ (Elm's JavaScript kernel) |
| `jsgen` | eco/compiler/src/Compiler/GenerateJs/Expression.elm (eco's port of Elm's JS generator; the erased path "stays identical to Elm's", eco/THEORY.md:35) |
| `tyopt` | eco/compiler/src/Compiler/LocalOpt/Typed/Expression.elm |
| `intr` | eco/compiler/src/Compiler/IR/Kernel/Intrinsics.elm |
| `arith` | eco/runtime/src/codegen/Passes/EcoToLLVMArith.cpp |
| `ecok/` | eco/elm-kernel-cpp/src/core/ |
| `strops` | eco/runtime/src/allocator/StringOps.hpp |
| `div` | eco/design_docs/elm-divergence.md |
| `fsem` | eco/design_docs/float-semantics.md |
| `ccase` | eco/design_docs/char-case-mapping.md |
| `dlog` | eco/design_docs/debug-log-ordering-policy.md |
| `vrep` | eco/design_docs/theory/value-representation.md |
| `clos` | eco/design_docs/theory/closures-and-calls.md |
| `T/` `TD/` `TC/` `TB/` | eco/test/elm/src/, eco/test/eco-divergence/src/, eco/test/elm-conformance/src/, eco/test/elm-bugs/src/ |

Test suite status: `T/` and `TC/` hold programs whose CHECK lines hold under both Elm-on-JS and
eco (div:27-28; `TC/` CHECKs are recorded from Elm on node, fsem:16-17). `TD/` CHECK lines are
eco's output, with Elm's output in `-- ELM:` lines (div:23-26). `TB/` (synced from
elm-test-suite) records known Elm 0.19.1 bugs: its CHECKs are the *desired* answer, it fails on Elm
0.19.1 and is **not run by eco's E2E harness** (commit 148adc96 message), so eco's result on a `TB/`
test is unverified.

Source-quality notes (the design notes are partly stale; where code and notes disagree the code
wins, eco/THEORY.md:43):
- div:50-58 (Int `^`, float-to-int TODOs), div:105-107 (String case mapping "keeps full mapping")
  and div:154-161 (compare on Float "proposed") are superseded by fsem:24-35, ccase:30-36 and the
  code cited below.
- div:149-150 and div:172 say equality never uses pointer identity; the code does (Equality, below).
- div:425-426 (Char predicates use eco Unicode tables) is wrong: `isUpper`, `isLower`, `isAlpha`,
  `isDigit`, `isOctDigit`, `isHexDigit` are Elm code over ASCII code ranges (core/Char.elm:82-194).

## Evaluation Strategy and Order

| Construct | Strategy | Elm-on-JS order | eco order | Tests | Cite |
|---|---|---|---|---|---|
| Application `f a b` | Call by value: function and arguments evaluated before the body | JS `A2(f, a, b)`: `f`, then `a`, `b` left to right | not pinned by any test | T/PartialApplicationTest:7-9 | kjs (F2/A2 helpers in Utils/JS prelude); clos:96-108 |
| `if c then t else e` | `c`, then only the chosen branch | same | same; no logging expression may be hoisted out of a branch | T/BoolShortCircuitTest:9-10 | dlog:31-35 |
| `case e of ...` | scrutinee once, then only the first matching branch | same | same | T/CaseOrderTest | eco/compiler/src/Compiler/GenerateMlir/Expr.elm:5762-5806 |
| `a && b`, `a \|\| b` (operator) | short-circuit: `a && b` = `if a then b else False`, `a \|\| b` = `if a then True else b` | JS `&&` `\|\|` | rewritten to `if` before codegen | T/BoolShortCircuitTest:9-10, T/BoolShortCircuitParserIdiomTest | jsgen:876-882; tyopt:509-516 |
| `(&&) a b` (prefix, saturated) | see C-DYN-17 | short-circuit (any saturated call of `Basics.and` becomes JS `&&`) | **strict**: only `Can.Binop` is rewritten; a `VarOperator` is an ordinary global, whose kernel intrinsic `eco.bool.and` has both operands evaluated | none | jsgen:682-690, 876-882; tyopt:450-455, 509-516; intr:213-215; arith:1084 |
| `(&&)`, `(\|\|)` as values | strict in both operands | `_Basics_and` gets evaluated arguments | `eco.bool.and` | none | kjs/Basics.js:62-63; intr:213-215 |
| `x \|> f`, `f <\| x` | identical to `f x` | rewritten to a call; JS then evaluates `f` before `x` | rewritten to a call | T/PipelineTest | jsgen:826-830, 963-975; tyopt:518-533 |
| `f << g`, `f >> g` | ordinary curried functions `composeL g f x = g (f x)` | not inlined | ordinary call | T/CompositionTest | core/Basics.elm:849, 860; jsgen:792-793 |
| `let` bindings | strict: every binding evaluated, even if unused; recursive functions not called until applied | bindings regrouped into strongly connected components, dependencies first (same front end); JS `var` per binding in that order | same regrouping; measured: named bindings before `_ =` bindings and not in source order among themselves; a run of `_ =` bindings is in source order | T/DebugLogOrderingTest:6-16, T/DebugLogNoDropTest:14 | eco/compiler/src/Compiler/Canonicalize/Expression.elm:39-47; dlog:18-22, 37-53 |
| Record literal `{ a = e1, b = e2 }` | each field once | field-name order: the canonical record is a Dict keyed by name, emitted as a JS object literal | layout order: unboxed (Int, Float, Char) fields first, then the rest, each group by name | none (T/DebugLogRecordTupleFieldTest is not discriminating) | eco/compiler/src/Compiler/IR/Canonical.elm:218; Optimized.elm:148; GenerateMlir/Expr.elm:528-542; vrep:19 |
| Tuple, list literal | each element once | left to right (JS literal) | not pinned (TC/ListLiteralDebugLogKindTest uses CHECK-DAG) | TC/ListLiteralDebugLogKindTest | vrep:17-18 |
| Top-level value (no parameters) | evaluated at most once in Elm-on-JS | once, at program start, in dependency order, before `main` runs; cyclic values through thunks | a thunk: literals folded at each use; boxed-ABI values memoised on first use; Int/Float/Char values recomputed at every use; a top-level value of function type re-runs its body per call | T/NonEntryMainEvaluatedOnceTest:8-15, TD/EtaExpandLogOrderTest:37-44 | eco/compiler/src/Compiler/GenerateJs/Generate.elm:358-395; eco/compiler/src/Compiler/GenerateMlir/ConstThunks.elm:3-8; eco/design_docs/theory/compiler/mlir-generation.md:112-137; GenerateMlir/Functions.elm:668 |
| `List.map f xs` (basis) | `f` applied once per element | last element first (`map` is `foldr`) | same, except eco may reorder when the callback is proven Debug-free | T/ListMapTemplateOrderTest:13-18 | core/List.elm:124-125, 177-204; dlog:66-80 |
| `List.map2`, `indexedMap` (basis) | `f` once per pair | first element first (kernel loop) | not pinned | none | core/List.elm:134-135, 437-439; kjs/List.js:37-44 |

Observability: Elm is pure, so evaluation order is visible only through `Debug.log` output, through
which of several failing or diverging subexpressions fires first, and through resource exhaustion.
eco states that within a let group the order is "unspecified-but-observable" and not a defect
(dlog:51-53). Under `--optimize` an optimiser may keep either of two failing occurrences (dlog:60-64).

No laziness anywhere: there are no lazy bindings, no call-by-need, and recursion through a
non-function value is accepted only when the self-reference sits inside a lambda
(T/PureRecursiveValueThunkTest:11, T/PureMutualRecursiveValueTest).

## Values

| Value | Meaning | Elm-on-JS representation | eco representation | Cite |
|---|---|---|---|---|
| Int | integer | JS number (IEEE double): see Arithmetic | i64, two's complement, unboxed | div:36-58; vrep:11 |
| Float | IEEE 754 binary64 | JS number | f64, unboxed | vrep:12; fsem:24-35 |
| Char | a character | JS string of 1 or 2 UTF-16 units (DEBUG: `String` object) | one code point 0..0x10FFFF in 32 bits | kjs/Utils.js:145-146; vrep:13, 29; ccase:30 |
| String | sequence of UTF-16 code units | JS string | one of six heap forms; length always in UTF-16 units | strops:1-27 |
| Bool | `type Bool = True \| False` | JS boolean | embedded constants 0x4/0x5 | core/Basics.elm:444; vrep:14, 56 |
| Order | `type Order = LT \| EQ \| GT` | DEBUG/PROD ctor objects; cmp uses -1/0/1 | null-cons words | core/Basics.elm:426; kjs/Utils.js:84-85; ecok/Utils.cpp:23-29 |
| `()` | unit | `0` (PROD) or `{ $: '#0' }` (DEBUG) | constant 0x6 | kjs/Utils.js:136-137; vrep:15 |
| Tuple (2, 3) | product | `{ a, b, c }` | Tuple2/Tuple3 heap object or SSA aggregate | kjs/Utils.js:139-143; vrep:18, 31 |
| List | finite cons list | `{ $, a, b }` cells | Cons cells or chunk views (not part of the value) | ecok/Utils.cpp:211-216 |
| Record | finite map from field names to values | JS object | Record, raw fields first, by name | vrep:19 |
| Custom type value | constructor tag plus fields | `{ $: tag, a, b, ... }` | Custom heap object; nullary ctor embedded | vrep:20-21 |
| Function | closure | JS function (F2..F9 wrappers for arity) | heap Closure with stage arity and captures | clos:18-46 |

## Application and Closures

| Aspect | Semantics | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Currying | every function of n parameters is a function of one parameter returning a function | `F2`..`F9` plus `A2`..`A9` | stages; "staging changes how many intermediate closures are built ... never the result" | T/FunctionChainedPartialApplicationTest, T/PartialAppChainTest | clos:7-9 |
| Partial application | builds a closure holding the given arguments; no body evaluation | `F_n` returns a curried function | `eco_pap_extend_l` copies, never mutates | T/PartialApplicationTest:7-9 | clos:100, 112 |
| Over-application | apply to the stage's arguments, then apply the result to the rest | `A2(f,a,b)` falls back to `f(a)(b)` | generic apply saturates then re-applies | T/CaseReturnFunctionTest, T/HigherOrderReturnLambdaBasedOnConditionTest | clos:96-110 |
| Captures | lexical scope, values captured at closure creation | JS closure over variables (see TCO bug) | captured values copied into the closure | T/ClosureCapture01Test..06 | clos:20, 58 |
| Constructors as functions | an n-ary constructor is an n-ary curried function | yes | yes | T/LssGapCtorAsValue, T/PapEtaCtorProbe | |
| Record alias constructor | `Point 1 2` builds `{ x = 1, y = 2 }` in declared field order | yes | yes | T/TypeAliasCtorTest | |
| Record accessor `.f` | function `\r -> r.f` | yes | yes | T/RecordAccessorFunctionTest | |
| Record update `{ r \| f = e }` | new record; `r` unchanged | `_Utils_update` copies | fresh object | T/RecordUpdateTest:6-7 | kjs/Utils.js:151-166 |
| Self tail calls | constant stack | `while` loop reassigning parameters; closures created in the loop capture the mutable variable (bug: TB/CompilerIssue1813...:13 expects `[1,2,3]`, TB/CompilerIssue2268...:14-15 expects `[3,2,1]`) | loop; capture-in-loop not pinned by a native test | T/TailRecursiveSumTest | TB files cited |
| Closure identity | not part of Elm's meaning | each evaluation of a lambda makes a new JS function | a zero-capture closure is interned: one object per wrapper for every evaluation | TD/FunctionEqualityFalseTest:13-19 | clos:88 |

## Pattern Matching

| Pattern | Matches | Binds | Notes | Cite |
|---|---|---|---|---|
| `_` | anything | nothing | | |
| variable | anything | the value | | |
| `p as x` | what `p` matches | `x` plus `p`'s bindings | | T/CaseAsPatternTest |
| `()` | unit | nothing | | |
| Int literal (incl. negative, hex) | Int equality | nothing | | T/CaseIntTest |
| Char literal | Elm-on-JS: JS string equality; eco: code-point equality | nothing | eco rejects at compile time a Char pattern that is not one code point (compiler crash path) | eco/compiler/src/Compiler/GenerateMlir/Patterns.elm:988-997; T/CaseCharTest, T/AstralCharCasePatternTest |
| String literal | String equality (UTF-16 units) | nothing | | T/CaseStringTest, T/CaseStringEmptyPatternTest |
| `( p1, p2 )`, `( p1, p2, p3 )` | componentwise | union | | T/CaseTupleTest |
| `[]`, `p :: ps`, `[ p1, ..., pn ]` | list shape | union | | T/CaseListConsTest |
| `{ f1, f2 }` | any record with these fields | the named fields | | T/LetDestructRecordTest |
| `C p1 ... pn` | value with tag `C` and matching fields | union | | T/CaseCustomTypeTest |

- Order: branches are tried in source order (first match wins); the decision-tree compilation order
  is not observable because tests are pure.
- No residual failure: incomplete `case`, and refutable patterns in `let`, lambda and function
  parameters, are rejected statically (static survey); eco's decision tree always ends in a
  fallback edge (eco/compiler/src/Compiler/GenerateMlir/Expr.elm:5751-5806), and the Elm-on-JS
  generator emits a default branch. Neither emits a "no match" crash.

## Let and Recursion

| Aspect | Semantics | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Simple binding | evaluate once, bind | JS `var` | SSA value | T/LetBasicTest | |
| Destructuring `( a, b ) = e` | evaluate `e` once, match (irrefutable) | `Opt.Destruct` paths | same | T/LetDestructuringTest | Canonicalize/Expression.elm:41-43 |
| Recursive function | members of an SCC; every member must have parameters | `var` function | `eco.papCreateGroup` allocates the group together | T/LetRecClosureTest, T/LetMutualRecursionBetweenLocalsTest | Canonicalize/Expression.elm:44-47; clos:62, 90 |
| Recursive value | rejected statically unless the self-reference is under a lambda | | | T/PureRecursiveValueThunkTest:11 | Canonicalize/Expression.elm:45-47 |
| Shadowing | not allowed (static) | | | | |
| Top-level value timing | see Evaluation Strategy | eager at init | lazy, memoised or per-use | TD/EtaExpandLogOrderTest:37-44 | mlir-generation.md:116-137 |
| Top-level cyclic value that needs itself while computed | divergence | recursion without end; DEBUG wraps the error as "Some top-level definitions from `M` are causing infinite recursion" | thunk recursion: stack overflow (not tested) | none | eco/compiler/src/Compiler/GenerateJs/Generate.elm:362-395 |

## Equality

`==` and `/=` have type `a -> a -> Bool` (core/Basics.elm:75-76, 349-359); `/=` is `not (==)` in
both implementations (kjs/Utils.js:78; ecok/Utils.cpp:756-758; arith:871 `une` for Float).

| Value kind | Meaning | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Int | numeric | `===`; `-0 === 0` | `icmp eq` | T/EqualityTest | arith:855; intr:344-348 |
| Float | IEEE: NaN unequal to all, `-0 == 0` | `===` (IEEE) except `x == 0` with an Int-literal `0` compiles to `!x`, so `nan == 0` is True and `nan /= 0` False | `oeq` / `une`, every path | T/FloatNegativeZeroTest:6-8, TC/FloatEdgeTest:26-28, TB/CoreIssue1115NanEqualsLiteralZeroTest | jsgen:1079-1102, 1118-1141; arith:855-885; fsem:26 |
| Char | same character | JS string equality (multi-unit Chars from case mapping are possible) | code-point equality | TD/CharAstralRoundTripTest:15-23 | ccase:33 |
| String | same UTF-16 unit sequence | JS `===` | unit-by-unit over any of six forms | T/EqBoxedFastPathTest | strops:1620-1645 |
| Tuple, List, Record, Custom | structural, componentwise; lists also by length | `_Utils_eqHelp` walks object keys; deep values deferred past depth 100 | `eqHelp` by tag, slot kinds, depth bound 100 with deferral | TC/DeepEqualityTest:17-22, T/ContainerEqualityFloatTest:20-39, T/ContainerEqualityCustomFloatTest | kjs/Utils.js:15-75; ecok/Utils.cpp:434-446, 502-697 |
| Same object on both sides | (not defined by Elm's prose) | `x === y` returns True before looking inside | `a == b` returns True before looking inside, in the kernel and in the inline fast path | TB/CompilerIssue2362NanTupleEqualityTest:13-15 (desired: `p == p` False), TB/CoreIssue988NanContainerSelfEqualityTest:17-24 | kjs/Utils.js:29-32; ecok/Utils.cpp:503; eco/runtime/src/codegen/EcoBackend.cpp:2216-2236 |
| Dict, Set | same key/value pairs in key order, whatever the tree shape | converted with `Dict.toList` then compared | `dictEq` walks both trees in order, ignoring colour | TC/DeepEqualityTest:22 | kjs/Utils.js:46-65; ecok/Utils.cpp:625-632, 699-754 |
| Array | same elements | structural on the internal tree (canonical for a given length) | element by element | none | ecok/Utils.cpp:658-675 |
| Function | Elm prose: not comparable | crash 5 "Trying to use `(==)` on functions" unless the same JS object | True iff same closure object, else False, at any depth | TD/FunctionEqualityFalseTest:13-19 | kjs/Utils.js:34-37; kjs/Debug.js:262-263; ecok/Utils.cpp:691-692; div:181-189 |
| Bytes | same bytes | n/a here | `memcmp` | | ecok/Utils.cpp:515-521 |
| Regex, Json values | see other parts | | | | div:362-372 |

## Comparison and Order

`compare : comparable -> comparable -> Order`; `<`, `>`, `<=`, `>=` on `comparable`
(core/Basics.elm:77-80, 368-420). Comparable types: Int, Float, Char, String, and lists and tuples
of comparables (core/Basics.elm:411-414). `min x y = if lt x y then x else y`, `max x y = if gt x y
then x else y` (core/Basics.elm:396-407).

| Type | Order | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Int | numeric | JS `<` or `_Utils_cmp` | signed i64 compare | T/IntCompareTest, T/CompareIntTest | arith:1351 area (int cmp_order); kjs/Utils.js:89-92 |
| Float, `<` `<=` `>` `>=` | IEEE ordered predicates | raw JS operator when either operand is a literal, else `_Utils_cmp(a,b) op 0`, which treats NaN as GT: `one > nan` True, `nan >= nan` True | IEEE on every path (`olt` etc.) | TD/FloatNaNOrderTest:13-64, TB/CoreIssue1050NanGreaterThanNanTest | jsgen:925-934, 940-965; kjs/Utils.js:91; arith:253-312 (float cmp); ecok/Utils.cpp:769-790; fsem:27 |
| Float, `compare` | eco: total order, NaN = NaN > every number, -0 = +0 | `_Utils_cmp`: LT only if `a < b`, EQ if `===`, else GT (NaN always GT; not antisymmetric) | total order | TD/FloatIeeeSemanticsTest:40-52, TD/FloatDivergenceTest:11-24 | kjs/Utils.js:91; arith:1346-1380; ecok/Utils.hpp:82-89; fsem:28 |
| Float inside tuples and lists, `<` etc. | eco: lexicographic by `compare`'s total order | `_Utils_cmp` | total order, so `nan < 1` is False but `( nan, 0 ) < ( 1, 0 )` is also False and `[ nan ] > [ 1 ]` True | TD/FloatIeeeSemanticsTest:53-58 | fsem:29 |
| Char | eco: code point; Elm: UTF-16 string order | JS string `<` | unsigned code point compare | T/CompareCharTest, TD/CharAstralRoundTripTest:22-23 | arith:1177; ecok/Utils.cpp:330-336; vrep:29 |
| String | lexicographic over UTF-16 code units, prefix first | JS string `<` | same, by units | T/CompareStringTest | strops:1647-1660 |
| List | lexicographic, shorter prefix first | cons walk | same | T/CompareEmptyListTest, T/OrderingEmptyListTest | kjs/Utils.js:117-119; ecok/Utils.cpp:374-403 |
| Tuple | lexicographic over components | `a`, `b`, `c` | same | T/CompareTupleWithEmptyListTest | kjs/Utils.js:110-115; ecok/Utils.cpp:340-372 |
| `sort`, `Dict`, `Set` with NaN | needs a total order | inconsistent comparator, behaviour undefined | NaNs sort last and are one key; -0 and +0 are one key | TD/FloatIeeeSemanticsTest:59-65 | fsem:30, 53 |
| `min`/`max` at Float | see Arithmetic | elm/core body | IEEE 754-2019 minimum/maximum | TD/FloatIeeeSemanticsTest:66-84 | eco/compiler/src/Compiler/MonoOpt/FloatMinMax.elm:1-18 |

## Arithmetic

Notation: `trunc`, `floor`, `ceil` on reals; `wrap64(n)` = the unique m in [-2^63, 2^63) with
m = n mod 2^64; `ToInt32` = JS's conversion (truncate, then mod 2^32 into [-2^31, 2^31), NaN and
infinities to 0); `dbl(r)` = r rounded to the nearest double. Elm-on-JS Int results are doubles, so
any Int result above 2^53 is `dbl` of the exact value, and may be a fraction, NaN or an infinity.

| Operation | Type | Mathematical meaning | Edge cases | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|---|---|
| `a + b`, `a - b`, `a * b` | Int | exact sum, difference, product | overflow | `dbl` of exact result (53-bit precision, then Infinity) | `wrap64` of exact result | T/IntAddTest, T/IntMulTest | kjs/Basics.js:10-12; jsgen:843-850; arith:52-87; eco/runtime/src/allocator/IntArith.hpp:23-36 |
| `a + b`, `a - b`, `a * b` | Float | IEEE 754 round-to-nearest | NaN, ±Infinity, -0 | IEEE | IEEE (`addf` etc.) | T/FloatAddTest | arith:267-305 |
| `a / b` | Float | IEEE division | `x / 0` = ±Infinity, `0 / 0` = NaN, `1 / -0` = -Infinity | IEEE | IEEE | T/FloatDivTest, T/FloatNegativeZeroTest:6-8 | kjs/Basics.js:13; arith:309-316; fsem:35 |
| `a // b` | Int | `trunc(a / b)` | `b = 0` gives 0; `minInt // -1`; results outside ±2^31 | `ToInt32(a / b)`: `x // 0` is 0 (Infinity and NaN map to 0); any quotient outside ±2^31 wraps to 32 bits (e.g. `5000000000 // 1` is 705032704) | `trunc`, total: `x // 0` = 0, `x // -1` = `wrap64(-x)` so `minInt // -1` = minInt | T/IntDivTest:10-13, T/IntDivByZeroTest:6-7 | kjs/Basics.js:14; jsgen:855-856; arith:91-123; ecok/Basics.cpp:87-89 |
| `modBy m x` | Int | floored modulus: `x - m * floor(x / m)`, sign of `m` | `m = 0`; `m < 0`; result -0 | JS `%` then sign fix-up; `m = 0` crashes ("Cannot perform mod 0. Division by zero error."); `modBy 4 -4` is -0 | same formula; `m = 0` and `m = -1` give 0 | T/IntModByTest:13-17, TD/ModByZeroKernelPathTest:25-28, TD/IntNegativeZeroTest:14-21 | kjs/Basics.js:20-29; kjs/Debug.js:290-291; arith:125-167; ecok/Basics.cpp:91-102; core/Basics.elm:515-541 |
| `remainderBy d x` | Int | truncated remainder `x - d * trunc(x / d)`, sign of `x` | `d = 0` | JS `x % d`; `d = 0` gives NaN in an Int; `remainderBy 4 -4` is -0 | `srem`; `d = 0` and `d = -1` give 0 | T/IntRemainderByTest:11-14, TD/RemainderByZeroTest:14-23 | kjs/Basics.js:17; jsgen:887-888; arith:169-197; ecok/Basics.cpp:104-106 |
| `b ^ e` | Int | `b` to the power `e` for `e >= 0`; `0 ^ 0 = 1` | `e < 0`; overflow | `Math.pow`: `2 ^ -1` is 0.5, `0 ^ -1` Infinity; overflow loses precision | square-and-multiply mod 2^64; any `e < 0` gives 0 (also `1 ^ -1` and `(-1) ^ -1`) | T/IntPowTest:6-9, TC/FloatEdgeTest:43, TB/CoreIssue960PowNegativeExponentIntTest:12 | kjs/Basics.js:15; arith:238-260; IntArith.hpp:38-54; div:38-39, 50-51 |
| `b ^ e` | Float | IEEE/libm `pow` | `pow(1, ±Infinity)`, `pow(1, NaN)`, `pow(-1, ±Infinity)` | ECMAScript `Math.pow`: NaN for these | LLVM `pow` (C99 Annex F: 1 for these); not pinned by a test | T/FloatPowTest:9-12 | kjs/Basics.js:15; arith:351-358; ecok/Basics.cpp:51-53 |
| `negate n` (and prefix `-`) | Int, Float | `0 - n` (Float: sign flip) | Int minInt; Int 0 | `-n`: `negate 0` is -0 | Int: `wrap64(0 - n)`, one zero; Float: `fneg` | T/IntNegateTest, T/FloatNegateTest:6-8, TD/IntNegativeZeroTest:16 | core/Basics.elm:567-568; jsgen:809-810; arith:199-211, 323-330 |
| `abs n` | Int, Float | `if n < 0 then -n else n` (elm/core body in both) | Int minInt; Float -0, NaN | `abs -0.0` is -0 | Int `abs minInt` = minInt; Float body kept, so `abs -0.0` = -0 | T/IntAbsTest, T/FloatAbsTest:6-8 | core/Basics.elm:581-582 |
| `toFloat n` | Int -> Float | the same number | n beyond 2^53 | identity | `sitofp`, round to nearest | T/ToFloatTest | kjs/Basics.js:47; jsgen:812-813; arith:573 |
| `round x` | Float -> Int | nearest integer, ties toward +Infinity (`round -2.5 = -2`) | NaN, ±Inf, out of Int range; -0 | `Math.round`: NaN or Infinity stored in an Int; `round -0.4` is -0 | `floor(x) + (x - floor(x) >= 0.5 ? 1 : 0)`, then saturate: NaN 0, beyond range the Int bound | T/FloatRoundTest:10-14, TD/FloatIeeeSemanticsTest:91-104, TD/FloatToIntRangeTest:10-19 | kjs/Basics.js:53; arith:586-635; ecok/Basics.cpp:116-137; fsem:33-34 |
| `floor x`, `ceiling x` | Float -> Int | `floor`, `ceil` | as `round`; `ceiling -0.5` | `Math.floor`/`Math.ceil`: NaN/Infinity in an Int; `ceiling -0.5` is -0 | `floor`/`ceil` then saturate | T/FloorToIntTest, T/CeilingToIntTest, TD/FloatIeeeSemanticsTest:97-103, 109-110 | kjs/Basics.js:51-52; ecok/Basics.cpp:123-129 |
| `truncate x` | Float -> Int | `trunc` | beyond ±2^31 | `ToInt32(x)`: `truncate 3e10` is -64771072, NaN and ±Infinity give 0 | saturating `trunc`: 30000000000; NaN 0; `truncate 1e20` maxInt | T/FloatTruncateTest, TD/FloatToIntRangeTest:14, TD/FloatDivergenceTest:17, 24 | kjs/Basics.js:48; jsgen:815-816; arith:681; ecok/Basics.cpp:139-141 |
| `sqrt`, `logBase b x`, `e`, `pi` | Float | sqrt; `log x / log b` (elm/core definition, not a primitive); constants | `sqrt -1` NaN; `logBase 10 1000` = 2.9999999999999996 in Elm | `Math.sqrt`, `Math.log`, `Math.E`, `Math.PI` | `llvm.sqrt`, `llvm.log`; `e`, `pi` folded constants | T/FloatSqrtTest, T/LetNumberLogBaseTest, TB/CoreIssue1048LogBaseTenTest:12-13 (desired 3) | core/Basics.elm:610-630; kjs/Basics.js:34-35, 54-55; intr:196-200, 293-297 |
| `sin cos tan acos asin atan atan2` | Float | the real functions, approximated | precision; NaN | `Math.*` (ECMAScript: implementation-approximated) | `sin`, `cos` LLVM intrinsics; `tan` lowered as `sin x / cos x`; `asin acos atan atan2` libm calls | T/FloatMathTanTest, T/FloatMathAtan2Test, T/FloatMathSin2PlusCos21Test | kjs/Basics.js:36-42; arith:379-516 |
| `isNaN`, `isInfinite` | Float -> Bool | classification | | `isNaN`, `=== ±Infinity` | `fcmp uno`; `abs x == inf` | T/FloatMathIsNaNTest, T/FloatInfinityTest | kjs/Basics.js:49, 56; arith:532-570 |
| `min`, `max` | comparable | elm/core: `if lt x y then x else y` / `if gt x y ...` | Float NaN, ±0 | elm/core body: `max 1 nan` = 1, `max nan 1` = NaN; `max -0 0` and `max 0 -0` depend on order | Float: IEEE 754-2019 maximum/minimum (NaN propagates, -0 < +0); Int and other types: elm/core body | T/IntMinMaxTest, T/FloatMinMaxTest, T/ComparableMinMaxTest, TD/FloatIeeeSemanticsTest:66-84 | core/Basics.elm:396-407; MonoOpt/FloatMinMax.elm:1-18, 70-95; arith:919-945 |
| `clamp lo hi x` | number | elm/core: `if x < lo then lo else if x > hi then hi else x` | NaN; `lo > hi` | elm/core body: `clamp 0 1 nan` = 1 | Float: `min (max x lo) hi`, so NaN in any argument gives NaN and `lo > hi` always gives `hi`; Int: elm/core body | TD/FloatNaNOrderTest:36, TD/FloatIeeeSemanticsTest:85-90, TB/CoreIssue1080ClampNanTest | core/Basics.elm:593-599; MonoOpt/FloatMinMax.elm:75-82 |
| `String.fromInt` | Int -> String | decimal | | `n + ''`: an Int holding 0.5 prints "0.5", 1e21 prints "1e+21" | exact decimal of i64 | T/StringFromNumberIntTest | kjs/String.js:270-273; strops:1272-1280 |
| `String.fromFloat`, `Debug.toString` Float | Float -> String | JS `Number.prototype.toString` | -0, NaN, Infinity, exponent form | native | shortest round-trip digits; fixed for 1e-6 <= abs < 1e21, else exponent; "0" for -0 | TC/DebugToStringTest:47-58, T/StringFromFloatJsFormatTest | kjs/String.js:270-273; strops:1288-1300 |
| `String.toInt` | String -> Maybe Int | optional `+`/`-` then one or more ASCII digits | overflow; long input; "-0" | digit loop in doubles: no overflow check, rounds above 2^53 (`"9007199254740991"` gives ...992), "-0" gives -0 | `Nothing` on 64-bit overflow or input over 64 units; exact otherwise | TC/StringKernelEdgeTest:20, TB/CoreIssue1142StringToIntMaxSafeTest:13-14 | kjs/String.js:278-299; strops:1186-1222; div:199-202 |
| `String.toFloat` | String -> Maybe Float | JS `Number(s)` minus forms with whitespace or `x`, `b`, `o` | "Infinity", overflow | `+s` after the regex filter | replicates: rejects whitespace and x/b/o, accepts signed "Infinity", `strtod` otherwise | none | kjs/String.js:302-312; strops:1224-1270 |
| Int literal | Int | its value | beyond 64 bits | Elm 0.19.1 reads literals into a 64-bit Int and wraps silently (TB/CompilerIssue1246LargeIntLiteralTest:13-14 desires no wrap); some hex literals rejected | 64-bit two's complement, hex at or above 2^63 negative | TD/HexLiteralNegativeI64Test:18-20 | (lexis: other part) |

Basic arithmetic is total in eco by design: "may return a wrong answer (wrapping, `x // 0 == 0`,
NaN), but it never returns a value of a different type and never raises a runtime error" (div:19-21).

## Bitwise

| Operation | Meaning | Elm-on-JS (32-bit) | eco (64-bit) | Tests | Cite |
|---|---|---|---|---|---|
| `and`, `or`, `xor` | bitwise on two's complement | operands `ToInt32`, result signed 32-bit | i64 | T/BitwiseAndTest, T/BitwiseOrTest, T/BitwiseXorTest | kjs/Bitwise.js:6-19; jsgen:758-767; ecok/Bitwise.cpp:5-15 |
| `complement` | `-n - 1` | `~ToInt32(n)` | `~n` on i64 | T/BitwiseComplementTest:6-7 | kjs/Bitwise.js:21-24; ecok/Bitwise.cpp:17 |
| `shiftLeftBy k n` | `n * 2^k` truncated to width | `ToInt32(n) << (k mod 32)`: `shiftLeftBy 32 1` = 1 | `n << (k mod 64)`: `shiftLeftBy 32 1` = 4294967296, `shiftLeftBy 63 1` = minInt | T/BitwiseShiftLeftTest, TD/BitwiseLargeShiftTest:7-8 | kjs/Bitwise.js:26-29; arith:1010-1030; ecok/Bitwise.cpp:21-23 |
| `shiftRightBy k n` | arithmetic shift | `>>`, count mod 32 | `ashr`, count mod 64 | T/BitwiseShiftRightTest:6-8 | kjs/Bitwise.js:31-34; arith:1032-1045 |
| `shiftRightZfBy k n` | logical shift | `>>>`: result is an *unsigned* 32-bit value (`shiftRightZfBy 0 -1` = 4294967295) | `lshr` on 64 bits reinterpreted signed (`shiftRightZfBy 0 -1` = -1) | T/BitwiseShiftRightZfTest | kjs/Bitwise.js:36-39; arith:1049-1060; ecok/Bitwise.cpp:30-32 |
| negative shift count | | `k & 31` | `k & 63` | none | as above |

## Char and String Basics

| Aspect | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|
| What a Char is | JS string of one code point, 1 or 2 UTF-16 units; case mapping can make it longer | exactly one code point in 0..0x10FFFF; a lone surrogate is a Char of its own unit value | TD/CharAstralRoundTripTest:15-23 | ccase:30; vrep:29 |
| `Char.toCode` | first code point; a lone high surrogate reads past its end and gives NaN | the code point | T/CharAstralCodeTest:12-17, TB/CoreIssue1150CharToCodeLoneSurrogateTest | kjs/Char.js:8-16 |
| `Char.fromCode n` | U+FFFD for n < 0 or n > 0x10FFFF, else the code point (surrogates pass through) | same | T/CharAstralCodeTest:16-17, TC/CharFromCodeWideIntTest:17-21 | kjs/Char.js:18-31; arith:1146-1167 |
| `Char.toUpper`/`toLower` | JS full case mapping: 103 code points give multi-code-point "Chars" (`toUpper 'ß'` = "SS") | Unicode 17.0 simple case mapping (`toUpper 'ß'` = 'ß'); `toLower 'İ'` = 'i' | TD/CharSimpleCaseTest, TD/CaseMappingDivergenceTest, TC/CharCaseOrdinaryTest | kjs/Char.js:33-41; ccase:34, 62-77 |
| `toLocaleUpper`/`Lower` | host locale (browser); on node equal to `toUpper` | equal to `toUpper`/`toLower` | TC/CharLocaleCaseTest | ccase:35, 86-88 |
| Char predicates | ASCII code ranges in Elm code (`isUpper` 0x41..0x5A etc.) | same Elm code | T/CharIsAlphaTest, T/CharIsDigitTest | core/Char.elm:82-194 |
| String unit of length and index | UTF-16 code units | UTF-16 code units in every form | T/StringAstralLengthTest:10-11, TC/NonBmpStringTest:13 | kjs/String.js:32-35; strops:15-17 |
| String to Chars (`toList`, `foldl`, `uncons`, `map`, `filter`, `any`, `all`) | combines a high surrogate with *any* next unit (foldr: low with any previous); lone surrogates loop until out of memory | combines only a valid high-low pair; lone surrogate is its own Char; `fromList (toList s) == s` | TC/NonBmpStringTest:13-27, TD/StringLoneSurrogateTest:15-23 | kjs/String.js:15-25, 105-122; vrep:29 |
| `String.reverse` | reverses code points, high surrogate glued to the next unit | reverses code points; valid pairs kept, lone surrogates moved as units | TC/NonBmpStringTest | kjs/String.js:81-103; strops:881-885 |
| `String.slice` | JS `slice` (negative counts from end), in units | units | TC/StringKernelEdgeTest | kjs/String.js:151-153 |
| `String.toUpper`/`toLower` | JS full mapping, Final_Sigma rule (`"ΟΔΟΣ"` to "οδος") | simple mapping per code point, no Final_Sigma ("οδοσ"); length preserved | TC/StringCaseTest | kjs/String.js:180-188; ccase:36, 75-77 |
| `++` | concatenation of units / lists | same (ropes internally) | T/StringConcatTest | kjs/Utils.js:173-193; ecok/Utils.cpp:794-816 |

## Remaining Runtime Failures

| Failure | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|
| `Debug.todo msg` | throws "TODO in module `M` on line N" plus message (crash 8; crash 9 inside a case branch) | prints "Debug.todo: msg" to stderr, exits status 1 | TD/DebugTodoPendingTimerTest:15-17 | kjs/Debug.js:26-41, 269-287; ecok/DebugExports.cpp:43-52 |
| `modBy 0 x` | throws "Cannot perform mod 0. Division by zero error." | 0 | TD/ModByZeroKernelPathTest:25-28 | kjs/Basics.js:23-24; div:66-73 |
| `==` on two different functions | throws crash 5 | False (True for the same object) | TD/FunctionEqualityFalseTest:13-19 | kjs/Utils.js:36; div:181-189 |
| Stack overflow (deep non-tail recursion) | catchable `RangeError` at roughly 10k frames | native stack, larger limit, hard crash (SIGSEGV); separate GC shadow-root stack aborts with "[eco] FATAL: GC shadow root stack overflow" | none (TB/CoreIssue1123NestedCmdBatchStackOverflowTest is a Cmd case) | div:435-440; eco/runtime/src/allocator/RootSet.cpp:36 |
| Out of memory | JS engine heap failure | "eco: out of memory: ..." then `abort()` | none | eco/runtime/src/allocator/ThreadLocalHeap.cpp:424-440 |
| Cyclic top-level value | DEBUG: "causing infinite recursion" error; PROD: stack overflow | stack overflow (thunk) | none | GenerateJs/Generate.elm:362-395 |
| Lone surrogate in `String.toList` etc. | loops until out of memory | well defined | TD/StringLoneSurrogateTest:14 | |
| Ill-typed program accepted by an unsound checker | Elm accepts some unannotated recursive groups and then fails at run time (`str.toUpperCase is not a function`) | rejected statically (`TYPE MISMATCH`) | eco/compiler/tests/SourceIR (TypeCheckFailsCases) | div:262-293 |
| Non-termination | loops | loops | T/BoolShortCircuitTest (used as a bomb) | |
| Pattern-match failure | none (static exhaustiveness) | none | | Pattern Matching above |
| Array index, `List.head` etc. | none: results are `Maybe` | none | | |

## Implementation-Dependent Points

| Point | Elm-on-JS | eco | Cite |
|---|---|---|---|
| Int width | IEEE double: exact to 2^53, then rounded, can reach ±Infinity | i64, wraps mod 2^64 | div:36-49; IntArith.hpp:9-12 |
| Int can hold a non-integer, NaN or Infinity | yes (`2 ^ -1`, `remainderBy 0`, `round (0/0)`, `toCode` of lone surrogate) | never | div:38-41; TD/RemainderByZeroTest:19-23 |
| Int negative zero | `negate 0`, `0 * -1`, `modBy 4 -4`, `remainderBy 4 -4`, `round -0.4`, `ceiling -0.5` are -0 (visible as `1 / toFloat n` = -Infinity) | one zero | TD/IntNegativeZeroTest:14-23; div:75-81 |
| `//` width | quotient through `ToInt32` (32-bit wrap) | full 64-bit truncation | kjs/Basics.js:14; jsgen:855-856; arith:91-123 |
| `x // 0`, `minInt // -1` | 0; n/a | 0; minInt | arith:91-123 |
| `modBy 0`, `remainderBy 0` | crash; NaN | 0; 0 | div:66-73 |
| Int `^` negative exponent | real-valued result in an Int | 0 | div:38-39; IntArith.hpp:38-44 |
| `truncate` | 32-bit (`ToInt32`) | saturating 64-bit | fsem:34, 55 |
| `round`/`floor`/`ceiling` of NaN, ±Inf, out of range | NaN or ±Infinity in an Int | NaN 0; Int bounds | fsem:34, 54 |
| Float `<` `>` `<=` `>=` with NaN | depends on whether an operand is a source literal | IEEE everywhere | fsem:39-47 |
| Float `==` against Int literal `0` | `!x`: `nan == 0` True | IEEE False | jsgen:1079-1102; TB/CoreIssue1115NanEqualsLiteralZeroTest |
| `compare` with NaN | NaN always GT (`compare 1 nan` = GT) | total order (`compare 1 nan` = LT, `compare nan nan` = EQ) | fsem:48; TD/FloatDivergenceTest:12-13, 19-20 |
| `max`/`min`/`clamp` at Float | argument-order dependent with NaN and ±0 | IEEE 754-2019 maximum/minimum; `clamp` = `min (max x lo) hi` | fsem:31-32, 49-52 |
| `clamp lo hi x` at Float with `lo > hi` | `lo` if `x < lo`, else `hi` if `x > hi`, else `x` | always `hi` (undocumented in eco notes) | core/Basics.elm:593-599; MonoOpt/FloatMinMax.elm:75-82 |
| `sort`/`Dict`/`Set` with NaN keys | undefined (inconsistent comparator) | well defined | fsem:53 |
| Float `pow` special cases | ECMAScript: `1 ^ (1/0)` NaN | C99: 1 (unpinned) | kjs/Basics.js:15; arith:351-358 |
| Transcendentals | engine's `Math.*` (implementation-approximated) | libm / LLVM intrinsics; `tan` as `sin/cos` | arith:405-418 |
| Equality on the same object | identity shortcut (True even holding NaN) | identity shortcut, kernel and inline | kjs/Utils.js:29-32; ecok/Utils.cpp:503; EcoBackend.cpp:2222 |
| Function equality | crash unless same object | identity; zero-capture closures interned | div:181-189; clos:88 |
| Char representation | 1-2 UTF-16 units, may become longer by case mapping | one code point | ccase:30, 47-56 |
| Char order | UTF-16 string order | code-point order (differs for U+E000..U+FFFF against astral; String order stays UTF-16, so Char order and String order disagree in eco) | vrep:29; ecok/Utils.cpp:330-336; strops:1647-1650 |
| Char/String case mapping | full mapping, engine Unicode version, Final_Sigma | simple mapping, Unicode 17.0 fixed | ccase:62-77, 92-98 |
| Lone surrogates | `toCode` NaN; `toList` loops | well defined | TD/StringLoneSurrogateTest:14 |
| Bitwise width | 32-bit, `>>>` unsigned | 64-bit, all signed, counts mod 64 | TD/BitwiseLargeShiftTest:6-8 |
| `String.toInt` | no overflow check, rounds above 2^53, "-0" gives -0 | `Nothing` on overflow or more than 64 units | strops:1186-1222 |
| `String.fromInt` of large Int | exponent form at 1e21 | always plain decimal | kjs/String.js:270-273 |
| Top-level value evaluation | once, eagerly at start | lazily; memoised only for boxed values; per use for Int/Float/Char; per call for function-typed | TD/EtaExpandLogOrderTest:37-44; mlir-generation.md:116-137 |
| Record field evaluation order | field-name order | unboxed fields first, then by name | GenerateMlir/Expr.elm:528-542 |
| `(&&) a b` prefix form | short-circuit | strict | jsgen:876-882; tyopt:450-455 |
| Closures made inside a self-tail-call loop | capture the loop's mutable variable | capture values (unpinned) | TB/CompilerIssue1813...:13 |
| Stack depth | about 10k frames, `RangeError` | native stack, SIGSEGV | div:435-440 |
| `Debug.*` under `--optimize` | compile error | allowed, output kept | div:191-197 |
| `Debug.todo` message | "TODO in module ..." | "Debug.todo: msg", exit 1 | TD/DebugTodoPendingTimerTest:15-17 |

## Evidence

| Test | Expression | CHECK (eco) | Elm-on-JS (`-- ELM:` or source) |
|---|---|---|---|
| T/IntDivTest:10-13 | `10 // 3`, `-10 // 3`, `10 // -3`, `-10 // -3` | 3, -3, -3, 3 | same |
| T/IntDivByZeroTest:6-7 | `10 // 0`, `-5 // 0` | 0, 0 | same |
| T/IntModByTest:13-17 | `modBy 4 7`, `modBy 4 -7`, `modBy 5 0` | 3, 1, 0 | same |
| T/IntRemainderByTest:11-14 | `remainderBy 4 7`, `4 -7`, `-4 7`, `-4 -7` | 3, -3, 3, -3 | same |
| T/IntPowTest:6-9 | `2^3`, `5^0`, `2^10`, `(-2)^3` | 8, 1, 1024, -8 | same |
| T/FloatPowTest:9-12 | `2.0 ^ -1.0` | 0.5 | same |
| T/FloatRoundTest:10-14 | `round 2.7, 2.3, -2.7, 2.5, 3.5` | 3, 2, -3, 3, 4 | same |
| TC/FloatEdgeTest:20-25 | `round` of 2.5, -2.5, 0.5, -0.5, 1.5, -1.5 | 3, -2, 1, 0, 2, -1 | same (recorded on node) |
| TC/FloatEdgeTest:26-28, 38-39 | `nan == nan`, `nan /= nan`, `Just nan == Just nan`, `[nan] /= [nan]` | False, True, False, True | same |
| TC/FloatEdgeTest:43 | `3 ^ 33` | 5559060566555523 | same |
| T/FloatNegativeZeroTest:6-8 | `-0 == 0.0`, `1/0`, `1/-0` | True, Infinity, -Infinity | same |
| TD/IntNegativeZeroTest:14-23 | `1 / toFloat (remainderBy 4 -4)` etc. | "0 Infinity" | "0 -Infinity" |
| TD/RemainderByZeroTest:14-23 | `remainderBy 0 7`, `+ 1` | 0, 1 | NaN, NaN |
| TD/ModByZeroKernelPathTest:25-28 | `modBy 0 5`, `List.map2 modBy [0,4] [9,-7]` | 0, [0,1] | crash |
| TD/FloatToIntRangeTest:10-19 | `round nan`, `round inf`, `truncate 3e10` | 0, 9223372036854775807, 30000000000 | NaN, Infinity, -64771072 |
| TD/FloatDivergenceTest:11-24 | `min nan 1`, `compare 1 nan`, `compare nan nan`, `truncate inf` | NaN, LT, EQ, 9223372036854775807 | 1, GT, GT, 0 |
| TD/FloatNaNOrderTest:13-64 | `one > nan` (variables), `max 1 nan`, `clamp 0 1 nan` | False, NaN, NaN | True, 1, 1 |
| TD/FloatIeeeSemanticsTest:53-65 | `compare (nan,1) (1,1)`, `(nan,0) == (nan,0)`, `sort [..nan..]`, `Dict` NaN keys | GT, False, "1,2,3,NaN,NaN", size 2 | (eco only) |
| TD/FloatIeeeSemanticsTest:73-76 | `max -0 0`, `max 0 -0`, `min 0 -0` | +0, +0, -0 | order dependent |
| TD/BitwiseLargeShiftTest:7-8 | `shiftLeftBy 32 1`, `shiftLeftBy 63 1` | 4294967296, -9223372036854775808 | 1, (32-bit) |
| T/BitwiseShiftRightTest:6-8 | `shiftRightBy 4 -1` | -1 | same |
| TD/FunctionEqualityFalseTest:13-19 | `f == f`, `(\x -> x) == (\x -> x + 0)`, `Just f == Just g` | True, False, False | True, crash, crash |
| T/ContainerEqualityFloatTest:20-39 | pairs, triples, lists with NaN, ±0, ±Inf | NaN containers unequal, -0 = 0 | same |
| TC/DeepEqualityTest:17-22 | values nested 120-500 deep | exact answers | same |
| T/CharAstralCodeTest:12-17 | `toCode` of astral; `fromCode -1`, `fromCode 0x110000` | 128512, 65533, 65533 | same |
| TD/CharAstralRoundTripTest:15-23 | `toCode (fromCode 55357)` and astral order | 55357 | NaN |
| TD/StringLoneSurrogateTest:15-23 | lone surrogates through `toList`, `foldr`, `uncons` | defined values | loops to OOM |
| TC/NonBmpStringTest:13-27 | `String.length "a😀b"`, `toList` | 4, [97,128512,98] | same |
| T/BoolShortCircuitTest:9-10 | `False && bomb`, `True \|\| bomb` | False, True | same |
| T/DebugLogOrderingTest:6-16 | five `_ = Debug.log` | source order | same |
| T/ListMapTemplateOrderTest:13-18 | `List.map (Debug.log "m")` on 5 elements | e, d, c, b, a | same |
| TD/EtaExpandLogOrderTest:37-44 | top-level `counted : St Int` with a `Debug.log` | `init` printed per call (3 times) | once |
| T/NonEntryMainEvaluatedOnceTest:8-15 | imported `main` used twice | logged once | same |
| TC/DebugToStringTest:24-82 | `Debug.toString` of each value form | e.g. `{ age = 3, name = "x" }`, `Just -1`, `1e+21`, `0` for -0 | same |
| TD/DebugTodoPendingTimerTest:15-17 | `Debug.todo "boom"` | "Debug.todo: boom", exit 1 | "TODO in module ..." |
| TB/CompilerIssue2362NanTupleEqualityTest:13-15 | `p == p` with `p = (nan, 1)` | desired False (eco unverified; code gives True) | True |
| TB/CompilerIssue2268TcoClosureCaptureTest:14-15 | lambdas made in a tail loop | desired `[3,2,1]` (eco unverified) | `[3,3,3]` |

## Candidate Ambiguities

### C-DYN-1: Int range and overflow
- **Construct:** Int arithmetic `+ - * negate abs ^`
- **Question:** What is the value of an Int operation whose exact result leaves the representable range?
- **Implementation:** eco wraps modulo 2^64 (IntArith.hpp:9-36; arith:52-87).
- **Notes or Elm reference behaviour:** Elm-on-JS computes in doubles: exact to 2^53, then rounded, then ±Infinity (div:36-45). elm/core docs silent.
- **Options:** (a) parametric width W with wraparound, W = 64 in eco and an appendix note for JS; (b) unbounded mathematical integers, overflow implementation-dependent; (c) fix 64-bit wraparound as the definition.
- **Affects:** dynamic | basis

### C-DYN-2: Integer division width and the `minInt // -1` case
- **Construct:** `//`
- **Question:** Is `a // b` = `trunc(a / b)` for all results, and what is `minInt // -1`?
- **Implementation:** eco: total truncated division, `x // 0` = 0, `minInt // -1` = minInt (arith:91-123; ecok/Basics.cpp:87-89).
- **Notes or Elm reference behaviour:** Elm-on-JS computes `ToInt32(a / b)` (kjs/Basics.js:14; jsgen:855-856), so any quotient outside ±2^31 wraps to 32 bits, a point eco's divergence notes do not list; `x // 0` = 0 arises from `ToInt32(±Infinity)` = 0.
- **Options:** (a) `trunc` with wrap to the Int width; (b) define via `ToInt32` as Elm-on-JS does; (c) unspecified outside ±2^31.
- **Affects:** basis

### C-DYN-3: Division by zero for `//`, `modBy`, `remainderBy`
- **Construct:** `x // 0`, `modBy 0 x`, `remainderBy 0 x`
- **Question:** Which defined "wrong answer" does each give?
- **Implementation:** eco: all give 0 (arith:91-197; ecok/Basics.cpp:87-106; TD/ModByZeroKernelPathTest:25-28; TD/RemainderByZeroTest:14-18).
- **Notes or Elm reference behaviour:** Elm-on-JS: `x // 0` = 0, `modBy 0` crashes (kjs/Basics.js:23-24), `remainderBy 0` is NaN in an Int (TD/RemainderByZeroTest:19-23). Author direction fixes `3 // 0 == 0`.
- **Options:** (a) 0 for all three (eco); (b) `modBy 0 x = x` and `remainderBy 0 x = x` (keeps `x = d * (x // d) + remainderBy d x`); (c) leave `modBy 0` as a failure.
- **Affects:** basis

### C-DYN-4: Int `^` with a negative exponent
- **Construct:** `b ^ e` at Int, `e < 0`
- **Question:** What Int is `b ^ e` when `e` is negative?
- **Implementation:** eco: 0 for every base, including 1 and -1 (IntArith.hpp:38-44).
- **Notes or Elm reference behaviour:** Elm-on-JS: `Math.pow`, a fraction or Infinity typed Int (kjs/Basics.js:15; TB/CoreIssue960PowNegativeExponentIntTest:12 requires only "an integer"); `0 ^ -1` undecided in div:50-51.
- **Options:** (a) 0 always (eco); (b) `trunc` of the real result: 1 for base 1, ±1 for base -1, 0 for other bases, 0 for base 0; (c) implementation-dependent.
- **Affects:** basis

### C-DYN-5: Float-to-Int conversion of NaN, infinities and out-of-range values
- **Construct:** `round`, `floor`, `ceiling`, `truncate`
- **Question:** What Int results for NaN, ±Infinity, and values outside the Int range?
- **Implementation:** eco saturates: NaN 0, too large maxInt, too small minInt (arith:586-607; ecok/Basics.cpp:116-121; fsem:34).
- **Notes or Elm reference behaviour:** Elm-on-JS stores NaN or ±Infinity in an Int; `truncate` is `ToInt32` so NaN and ±Infinity give 0 and `truncate 3e10` = -64771072 (TD/FloatToIntRangeTest:15-19).
- **Options:** (a) saturate with NaN to 0 (eco); (b) NaN and ±Inf to 0, out-of-range wrap; (c) implementation-dependent.
- **Affects:** basis

### C-DYN-6: Negative zero in Int
- **Construct:** Int results `negate 0`, `0 * -1`, `modBy 4 -4`, `remainderBy 4 -4`, `round -0.4`, `ceiling -0.5`
- **Question:** Does Int have one zero, or can `toFloat` reveal a negative zero?
- **Implementation:** eco Int has one zero; `1 / toFloat (negate 0)` = Infinity (TD/IntNegativeZeroTest:14-18).
- **Notes or Elm reference behaviour:** Elm-on-JS gives -Infinity (TD/IntNegativeZeroTest:19-22; div:75-81).
- **Options:** (a) Int is the integers, one zero; (b) appendix-only JS artefact.
- **Affects:** basis

### C-DYN-7: `compare` on Float with NaN and signed zeros
- **Construct:** `compare`, and everything built on it (`sort`, `Dict`, `Set`, tuple and list ordering)
- **Question:** What Order does `compare` give when an operand is NaN?
- **Implementation:** eco: total order, NaN equals NaN and is above every number, -0 equals +0 (arith:1346-1380; ecok/Utils.hpp:82-89; TD/FloatIeeeSemanticsTest:40-52).
- **Notes or Elm reference behaviour:** Elm-on-JS: GT whenever NaN is involved, so not antisymmetric (kjs/Utils.js:91; TD/FloatDivergenceTest:19-20); elm/core docs silent.
- **Options:** (a) eco's total order; (b) IEEE totalOrder (-NaN < -Inf, -0 < +0); (c) unspecified when NaN is involved.
- **Affects:** basis

### C-DYN-8: Ordering operators on Float with NaN, and their relation to `compare`
- **Construct:** `<`, `<=`, `>`, `>=` at Float, and at tuples or lists containing Float
- **Question:** Are the order operators IEEE predicates, or derived from `compare`?
- **Implementation:** eco: IEEE at Float (all False with NaN), but lexicographic by `compare`'s total order inside tuples and lists, so `nan < 1` is False and `[ nan ] > [ 1 ]` is True (fsem:27-29; TD/FloatIeeeSemanticsTest:56-57).
- **Notes or Elm reference behaviour:** Elm-on-JS: raw JS operator when an operand is a source literal, else `_Utils_cmp`, so `one > nan` is True but `1 > nan` False (TD/FloatNaNOrderTest:39-58; jsgen:925-934).
- **Options:** (a) eco's split (IEEE at Float, total order in aggregates); (b) all operators defined from `compare`; (c) unspecified with NaN.
- **Affects:** basis

### C-DYN-9: `min`, `max`, `clamp` at Float
- **Construct:** `min`, `max`, `clamp`
- **Question:** Are these the elm/core definitions (`if lt x y then x else y`) or IEEE 754-2019 minimum/maximum?
- **Implementation:** eco replaces the Float specialisations by IEEE minimum/maximum and `clamp lo hi x = min (max x lo) hi`; Int and other types keep elm/core bodies (MonoOpt/FloatMinMax.elm:1-18, 70-95).
- **Notes or Elm reference behaviour:** elm/core defines them in Elm (core/Basics.elm:396-407, 593-599); results with NaN and ±0 depend on argument order (fsem:49-52).
- **Options:** (a) elm/core definitions verbatim; (b) eco's IEEE functions at Float; (c) elm/core definitions with NaN cases unspecified.
- **Affects:** basis

### C-DYN-10: `clamp lo hi x` with `lo > hi`
- **Construct:** `clamp`
- **Question:** What does `clamp 10 0 5` give?
- **Implementation:** eco at Float: `min (max 5 10) 0` = 0 (always `hi` when `lo > hi`); eco at Int: elm/core body gives 10 (MonoOpt/FloatMinMax.elm:75-82; core/Basics.elm:593-599). Not documented in fsem and not tested.
- **Notes or Elm reference behaviour:** elm/core doc gives the three cases assuming `lo <= hi` (core/Basics.elm:586-592); Elm-on-JS returns `lo` when `x < lo`.
- **Options:** (a) elm/core's case analysis (`lo` wins); (b) `hi` wins; (c) unspecified when `lo > hi`.
- **Affects:** basis

### C-DYN-11: Equality and object identity (reflexivity versus IEEE)
- **Construct:** `==` on structured values containing NaN
- **Question:** Is `t == t` True when `t = ( nan, 0 )`, while a separately built `( nan, 0 )` is unequal?
- **Implementation:** eco returns True for the same heap object, in the kernel (ecok/Utils.cpp:503) and the inline fast path (EcoBackend.cpp:2216-2236); whether two occurrences are the same object depends on optimisation (SSA aggregates, interning, constant sharing).
- **Notes or Elm reference behaviour:** Elm-on-JS identical shortcut (kjs/Utils.js:29-32). eco notes claim equality never uses identity (div:149-150, 172; div:464 lists `False`); TB/CompilerIssue2362NanTupleEqualityTest:13-15 and TB/CoreIssue988NanContainerSelfEqualityTest:17-24 want False.
- **Options:** (a) purely structural with IEEE Float equality (identity irrelevant); (b) structural with Float equality reflexive inside containers; (c) unspecified for values containing NaN.
- **Affects:** dynamic | basis

### C-DYN-12: Equality on functions
- **Construct:** `==` where the type contains a function
- **Question:** What does `==` do on functions, given the type system allows it?
- **Implementation:** eco: True iff same closure object, else False, at any depth (ecok/Utils.cpp:503, 691-692; TD/FunctionEqualityFalseTest:13-19); zero-capture closures are interned (clos:88), so two evaluations of one capture-free lambda compare True, and a partial application compares False to an identical one.
- **Notes or Elm reference behaviour:** Elm-on-JS crashes unless the same object (kjs/Utils.js:34-37; kjs/Debug.js:262-263).
- **Options:** (a) a runtime failure (Elm); (b) always False except physical identity, with identity left implementation-dependent; (c) unspecified value of type Bool.
- **Affects:** dynamic

### C-DYN-13: What a Char is
- **Construct:** Char values, `toCode`, `fromCode`, case mapping
- **Question:** Is a Char exactly one Unicode code point (scalar value or any code point including surrogates)?
- **Implementation:** eco: one code point 0..0x10FFFF, surrogate code points allowed as Chars (vrep:29; ccase:30-31).
- **Notes or Elm reference behaviour:** Elm-on-JS: a JS string of 1-2 units; `toUpper 'ß'` is "SS" in a Char; lone surrogates give `toCode` NaN (kjs/Char.js:8-41; ccase:47-56).
- **Options:** (a) code point including surrogates (eco); (b) Unicode scalar value (surrogates excluded, `fromCode` maps them to U+FFFD); (c) abstract character, with the JS model in the appendix.
- **Affects:** basis

### C-DYN-14: Char order versus String order
- **Construct:** `compare`, `<` on Char and on String
- **Question:** Are Chars ordered by code point, and must that agree with String order of one-Char strings?
- **Implementation:** eco: Chars by code point (arith:1177; ecok/Utils.cpp:330-336), Strings by UTF-16 units (strops:1647-1650), so the two disagree for U+E000..U+FFFF against astral Chars.
- **Notes or Elm reference behaviour:** Elm-on-JS orders both by UTF-16 units (kjs/Utils.js:89-92), so they agree.
- **Options:** (a) both by code point; (b) both by UTF-16 units; (c) eco's mix.
- **Affects:** basis

### C-DYN-15: Case mapping
- **Construct:** `Char.toUpper/toLower/toLocale*`, `String.toUpper/toLower`
- **Question:** Simple or full Unicode case mapping, which Unicode version, and is Final_Sigma applied?
- **Implementation:** eco: simple mapping, Unicode 17.0, no Final_Sigma, length preserved (ccase:30-42, 62-77).
- **Notes or Elm reference behaviour:** Elm-on-JS: JS full mapping and Final_Sigma, host Unicode version, locale for `toLocale*` in browsers (ccase:47-56, 75-88).
- **Options:** (a) simple mapping of a named Unicode version; (b) full mapping (needs String results); (c) implementation-dependent.
- **Affects:** basis

### C-DYN-16: Bitwise width and `shiftRightZfBy`
- **Construct:** `Bitwise.*`
- **Question:** On how many bits do the Bitwise functions work, and is `shiftRightZfBy`'s result unsigned?
- **Implementation:** eco: 64 bits, shift counts mod 64, `shiftRightZfBy` result reinterpreted as signed (ecok/Bitwise.cpp:5-32; arith:1010-1060; TD/BitwiseLargeShiftTest:7-8).
- **Notes or Elm reference behaviour:** Elm-on-JS: operands `ToInt32`, counts mod 32, `>>>` gives an unsigned 32-bit result (kjs/Bitwise.js:6-39); div:409-415 suggests matching 32 bits.
- **Options:** (a) the Int width W; (b) fixed 32 bits as Elm-on-JS; (c) implementation-dependent.
- **Affects:** basis

### C-DYN-17: Prefix `(&&) a b` and `(||) a b`
- **Construct:** a saturated prefix use of `&&` or `||`
- **Question:** Does `(&&) False e` evaluate `e`?
- **Implementation:** eco: yes (strict); only `Can.Binop` is rewritten to `if` (tyopt:450-455, 509-516; intr:213-215). Read from the code, not tested.
- **Notes or Elm reference behaviour:** Elm-on-JS: no; any saturated call of `Basics.and`/`or` becomes JS `&&`/`||` (jsgen:682-690, 876-882). elm/core documents only the operator form (core/Basics.elm:73-74, 456-486).
- **Options:** (a) `&&` and `||` are special forms only as infix operators, ordinary strict functions otherwise; (b) short-circuit whenever saturated; (c) unspecified.
- **Affects:** dynamic

### C-DYN-18: Order of evaluation within a `let`
- **Construct:** `let` with several bindings
- **Question:** In what order are the bindings of one `let` evaluated?
- **Implementation:** both front ends regroup bindings into SCCs, dependencies first (Canonicalize/Expression.elm:39-47); eco measured: named bindings before `_ =` bindings, not in source order (dlog:37-53); `_ =` runs are in source order (T/DebugLogOrderingTest:6-16).
- **Notes or Elm reference behaviour:** silent; eco calls it "unspecified-but-observable" (dlog:51-53). Elm-on-JS order among independent bindings not checked here.
- **Options:** (a) source order; (b) any order consistent with dependencies (unspecified); (c) dependency order with source order among independent bindings.
- **Affects:** dynamic

### C-DYN-19: Order of evaluation of record fields and other compound expressions
- **Construct:** record literals, tuples, lists, application arguments
- **Question:** Are sub-expressions evaluated left to right in source order?
- **Implementation:** eco: record fields in layout order, unboxed fields first then by name (GenerateMlir/Expr.elm:528-542); other orders not pinned.
- **Notes or Elm reference behaviour:** Elm-on-JS: record fields by field name (the canonical record is a name-keyed Dict, Canonical.elm:218), tuples, lists and arguments left to right (JS).
- **Options:** (a) source order; (b) unspecified (only Debug.log can tell); (c) field-name order for records, left to right otherwise.
- **Affects:** dynamic

### C-DYN-20: Evaluation time and multiplicity of top-level values
- **Construct:** top-level definitions without parameters
- **Question:** When is a top-level value evaluated, and how many times?
- **Implementation:** eco: thunks; boxed values memoised on first use, Int/Float/Char values recomputed at each use, function-typed values re-run their body per call (mlir-generation.md:112-137; TD/EtaExpandLogOrderTest:37-44).
- **Notes or Elm reference behaviour:** Elm-on-JS: once, eagerly, at start-up, in dependency order (Generate.elm:358-395); a top-level `Debug.todo` value fails at start even if unused at run time.
- **Options:** (a) once, before `main` (Elm); (b) once, on first use; (c) unspecified (observable only through Debug and failure).
- **Affects:** dynamic

### C-DYN-21: Order of callback application in the basis
- **Construct:** `List.map`, `List.filter`, `List.map2`, `List.indexedMap`, folds
- **Question:** Does the book fix the order in which basis functions apply their callbacks?
- **Implementation:** eco follows elm/core: `map`/`filter` via `foldr`, so last element first (T/ListMapTemplateOrderTest:13-18), but may reorder Debug-free callbacks (dlog:66-80).
- **Notes or Elm reference behaviour:** elm/core source fixes it (core/List.elm:124-125, 214-215); `map2` is a forward kernel loop (kjs/List.js:37-44).
- **Options:** (a) define basis functions by their elm/core Elm source (order follows); (b) leave callback order unspecified.
- **Affects:** basis

### C-DYN-22: Resource exhaustion
- **Construct:** deep recursion, large allocation
- **Question:** Is stack overflow or memory exhaustion part of the semantics, and how is it reported?
- **Implementation:** eco: SIGSEGV on native stack overflow; abort with a message on heap or shadow-stack exhaustion (div:435-440; ThreadLocalHeap.cpp:424-440; RootSet.cpp:36).
- **Notes or Elm reference behaviour:** Elm-on-JS: `RangeError` near 10k frames; JS heap failure (div:437-438).
- **Options:** (a) outside the definition (an implementation may fail at any point for lack of resources); (b) a defined abort result; (c) bound recursion depth.
- **Affects:** dynamic

### C-DYN-23: `Debug.todo` and `Debug.log`
- **Construct:** `Debug.todo`, `Debug.log`
- **Question:** Are these part of the defined language, and what do they mean?
- **Implementation:** eco: `Debug.log` writes `label: value` to program output and returns the value; `Debug.todo` prints "Debug.todo: msg" and exits 1; allowed under `--optimize` (dlog:7-16; ecok/DebugExports.cpp:43-52; div:191-197).
- **Notes or Elm reference behaviour:** Elm-on-JS: `console.log`; `Debug.todo` throws "TODO in module ..."; Debug rejected under `--optimize` (kjs/Debug.js:12-41).
- **Options:** (a) `Debug.todo` as a bottom value (abort) and `Debug.log` as an observation outside the pure semantics; (b) omit Debug from the definition; (c) define an output trace.
- **Affects:** dynamic | basis

### C-DYN-24: Closures created in a self tail-call loop
- **Construct:** a lambda created inside a self-tail-recursive function
- **Question:** Does each closure capture the value of its own call (as the substitution semantics says)?
- **Implementation:** eco: loop lowering with captured values; not pinned by a native test (TB tests are not run by eco).
- **Notes or Elm reference behaviour:** Elm-on-JS bug: closures share the reassigned loop variable (TB/CompilerIssue1813TcoClosureCapturesMutatedArgTest:13, TB/CompilerIssue2268TcoClosureCaptureTest:14-15).
- **Options:** (a) the definition's substitution semantics (each call's value), with Elm-on-JS listed as a known bug; (b) appendix note only.
- **Affects:** dynamic

### C-DYN-25: `String.toInt` and `String.fromInt` outside the exact range
- **Construct:** `String.toInt`, `String.fromInt`
- **Question:** What does `String.toInt` return for a numeral outside the Int range or longer than any Int numeral, and how does `fromInt` print large values?
- **Implementation:** eco: `Nothing` on overflow or more than 64 units; `fromInt` exact decimal (strops:1186-1222, 1272-1280).
- **Notes or Elm reference behaviour:** Elm-on-JS: `Just` of a rounded double, no length limit, "-0" gives -0; `fromInt` uses JS number printing, exponent form at 1e21 (kjs/String.js:270-299; TB/CoreIssue1142StringToIntMaxSafeTest:13-14).
- **Options:** (a) `Nothing` outside the Int range, any number of leading zeros accepted; (b) eco's rule including the 64-unit limit; (c) implementation-dependent.
- **Affects:** basis

### C-DYN-26: Float `pow` special cases and transcendental accuracy
- **Construct:** Float `^`, `sin`, `cos`, `tan`, `log`, `logBase`, inverse trig
- **Question:** Does the book define these by IEEE 754 / C99 Annex F, by ECMAScript, or leave accuracy implementation-dependent?
- **Implementation:** eco: LLVM `pow` (C99: `1 ^ (1/0)` = 1), `tan` as `sin/cos`, libm elsewhere (arith:351-516); not tested at special values.
- **Notes or Elm reference behaviour:** Elm-on-JS: `Math.*`, ECMAScript `1 ^ (1/0)` = NaN; `logBase 10 1000` = 2.9999999999999996 (TB/CoreIssue1048LogBaseTenTest:12-13 wants 3).
- **Options:** (a) the real function, rounding implementation-dependent, special values per IEEE 754-2019 recommended operations; (b) follow ECMAScript; (c) implementation-dependent entirely.
- **Affects:** basis
