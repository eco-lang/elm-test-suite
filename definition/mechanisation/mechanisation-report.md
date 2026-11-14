# Mechanisation Report

> **Update, 2026-11-13 (the core library's Elm texts, plans/library-elm-texts.md).** The 28 tests
> that were refused only for a library value (group D of untranslated-tests.md, less
> LetNumberMap2Test, whose `List.map2` is a kernel value) are translated and proved end to end:
> 608 tests now. The book leaves `List`, `Tuple`, `Maybe` and `Result` with empty or partial dynamic
> interfaces. The tests name 12 of their values (`List.foldl`, `foldr`, `head`, `length`, `map`,
> `sum`, `Maybe.andThen`, `map`, `withDefault`, `Result.map`, `Tuple.first`, `second`), each defined
> in elm/core 1.0.5 by Elm text. The translator writes the closure of those texts as four modules
> (`Generated/Library.lean`, through its own pipeline): the texts are unchanged, except that
> `cons = Elm.Kernel.List.cons` is written `cons = (::)`. `List.sum`, whose scheme quantifies a
> `number` variable, gets its default copy at Float and a copy `sum$Int`. Lean evaluates the
> modules in order in ME0 by Chapter 7's rules (`Lib.libME`, with the derivations `libME_eval` from
> the evaluator's soundness). The dynamic test basis with the library, `Lib.Btest = Btest libME`,
> is the basis of every view program's `t_` theorem and of `mean_`'s dynamic premise (`DynOf`,
> through `dynBasis`). Worker theorems keep `Btest []`, since no worker test names a library value.
> A test may name a library value as a value of the basis, at the scheme of its annotation in the
> vendored file. A use of `List.sum` at Int is `List.sum$Int`, in the translator and in Lean's
> specialisation (`basisCopies` gains `("List", "sum")`). The `t_` and `mean_` theorems of a
> program that names a library value are tagged `[library]`, a new entry of the trust table: D2's
> harness assumption, extended from the library's static interfaces to its dynamic values.
> 18 of the 28 are `[native]` because they use `round`; the 10 RecordNarrow tests are checked by the
> kernel; none needed `native_decide` for the memory budget. A library module is evaluated only for
> a program that looks up one of its values. The first build showed that `basisRefs` forced the
> static List interface in every W check (0.4 GB and 1.8 s each, the largest shard at 6.58 GB), so
> its entries no longer depend on the scheme lookup. Counts (`scripts/verify.sh full`, 28 min 7 s
> wall after a rebuild of 189 modules; largest process 6.19 GB, scope peak 8.41 GB):
> - translator: 608 of the 941 `elm-spec` tests translated, 918 source programs written.
> - `legal_`: 622 (11 by `native_decide`), `refuse_`: 287, 0 conditional on D11.
> - 608 `spec_`, 606 `mean_` (two tests stop at Debug.todo), 608 `ident_`.
> - run-examples: 1,748 of 1,748 checks agree; 1,508 by the kernel, 238 by `native_decide`, in 608
>   program theorems.
> - compare-e2e: 608 of 608.
> - check-axioms: 15,665 theorems, 264 using `native_decide`, no axiom problems.
> - No theorem lost: the 28 tests gain `t_`, `wcheck_`, `spec_`, `mean_` and `ident_`, and their
>   `legal_` moves from `Certs/Legal_*.lean` to their end-to-end shard.

> **Update, 2026-11-13 (certificates restructured).** `Certs/` is now in fixed alphabetical
> buckets of `project/Test` (the bounds are in `Certify.lean`), and no test shard imports another, so
> a change to one test rewrites one certificate file. Lake 5 has no job flag; `LEAN_NUM_THREADS=K`
> caps the `lean` processes, and `scripts/verify.sh quick|full` runs the build and every check with
> K = 4 in a 24 GB scope. `spec_X` now states `endToEndW Btest s_X = .ok g_X.reduced`: step 10's
> pipeline with step 11's W in place of step 9's inference. It follows from `wcheck_X`
> (`endToEndW_of_wCheck`), so the kernel runs inference and specialisation once per test.
> compare-e2e checks `endToEndW` and agrees on 580 of 580; step 9's pipeline also still agrees on
> 580. About half of each W check was the kernel recomputing the context of the module's imports;
> W checks now read it from one lemma per list of imports (`Certs/Ctx_<hash>.lean`,
> `wCheck_of_ctx`, proved without hypothesis). That cut an end-to-end shard of 20 tests from 98 s
> to 32 s and brought four programs back within the kernel's memory budget: 11 W checks use
> `native_decide` (was 15), and no `spec_` does (was 5; seven `spec_` theorems rest on a native
> `wcheck_`). A clean certificate build takes 15.2 min wall (93 min serially before) and 47 min of
> CPU. The largest process is 6.19 GB, and the scope peaks at 7.44 GB. The critical path is
> WideRecordDecoder300Test's `native_decide`, 14 min in Lean's interpreter. With nothing changed,
> `verify.sh quick` takes about 1 min 50 s; rebuilding one changed shard takes about 32 s. The
> translator's Generated shards are now fixed alphabetical buckets as well (`viewBounds`, the same
> as `e2eBounds`, and `srcBounds`, in `Translate.elm`), with a Syn file per source shard, and the
> translator removes the files it no longer writes. Before this, adding one test
> (LetCycleThroughLambdaArgumentTest) renamed the contents of 16 of the 24 source shards and
> rebuilt 27 certificate shards in 901 s. Now a test's source bucket is imported by 2 to 7
> certificate shards (3 at the median). For that test the bucket is imported by 6, which took about
> 4.5 min of CPU together in the last clean build. A clean build with these shards: 885 s, 110
> modules, largest process 6.20 GB, scope peak 8.85 GB.

> **Update, 2026-11-13 (plan step 11, milestone (g): D11 discharged).** The hypothesis that the
> inference's derivation is principal (D11, `[principal]`) is gone from every per-test theorem.
> Module-level W now handles ports, as the annotated group `x : ty; x = x`, kept only when its
> closed environment is the port rule's. It returns a derivation for all 622 legal programs. For
> each translated test, a theorem `wcheck_` has the kernel run W, Chapter 9's conditions, the
> further restrictions and the specialisation. `legal_of_W`, `ident_of_wCheck` and
> `programSem_of_wCheck` then give its `legal_`, `ident_` and `mean_` theorems without hypothesis.
> StandardA96NumberFlagsTest is refused by `not_legal_of_wMainVar`: W gives `main` a variable as
> its flags type, every principal derivation keeps that variable, and no port type is a variable.
> So all compile-error tests that reach Lean are refused. CompilerIssue2281LongLineListTest, a list literal of
> 22,000 elements on which compiled W gave no result within two hours, lost its `elm-spec` tag by
> the author's decision. It tests a compiler's column limit, which the book does not speak of, and
> it names only rules its program happens to use; W's failure on it is a known limit. The general
> properties `PrincipalExistsCore` and `PrincipalExistsMod` are proved only from W's coverage.
> Proving them unconditionally needs three things: the `internal` clause of W's completeness
> (milestone (e)); W's coverage of what it answers `unsupported` (pattern bindings in groups,
> ambiguous contexts, aliases with free variables); and bases and contexts outside W's invariants.
> The translator had not translated the two tests of ruling A98. It resolved a built-in type name
> (`String`) before the module's own alias, against A98. It now lets the module's types and aliases
> take the name first, so StandardA98TypeBeforeAliasTest is translated (580 tests), and the core
> refutation refuses its mismatch twin. Counts, after the restructure above:
> - `legal_`: 622, 11 by `native_decide`, none under D11.
> - `refuse_`: 287 (with LetCycleThroughLambdaArgumentTest, added on 2026-11-13 and refused by its
>   restriction core-let-recursion), with no compile-error test left unrefused.
> - 580 `spec_` (0 by `native_decide`), 578 `mean_` and 580 `ident_`.
> - check-axioms: 15,512 theorems, 228 using `native_decide`, no axiom problems.
> - run-examples: 1,709 of 1,709.
> - compare-e2e: 580 of 580.
> - measure-cores: 201 refuted, and none of the 625 compile-success tests.
> - measure-w: W refutes no compile-success test and gives a derivation for all 622 legal programs.
> - `scripts/check-hypotheses.lean`: 13 general lemmas, and no per-test theorem.

> **Update, 2026-11-12 (plan step 11, milestone (f), modules and programs).** Module- and
> program-level W (`MW.inferModuleW`, `MW.inferProgramW`, `Stat/Complete/Modules*.lean`) elaborates
> a module's type declarations whole, as ruling A98 requires, and its top-level groups as one nested
> `let` with milestone (e)'s W. Refutation (`inferModuleW_fail`, `inferProgramW_fail`,
> `Stat.not_legal_of_wRefutes`) and principality (`inferModuleW_principal`,
> `inferProgramW_principal`) are proved without hypotheses; since A98 every module is coherent, so
> section 9's coherence conditions are not needed, and two solutions of the type declarations differ
> by a bijection of type names (`types_bij`). The 15 inference tests the core refutation missed (the
> six rigid-`let` tests, the four row tests, four tests of local type variables and
> CompilerIssue2274) are refused by the kernel: 284 compile-error tests are refused, and only
> StandardA96NumberFlagsTest (milestone (g)) is not. `lake exe measure-w` (`w-report.json`): W
> refutes none of the 624 compile-success tests it can run (CompilerIssue2281LongLineListTest, a
> list of 22,000 elements, is over the memory budget) and returns a derivation for 585 of the 622
> legal programs; the 36 with ports are not yet handled. 14,804 theorems, 0 axiom problems;
> run-examples unchanged (1,708 checks); compare-e2e 579 of 579; the certificates build in 818 s
> with a peak of 6.3 GB.

> **Update, 2026-11-12 (plan step 11, milestones (b) to (d), and step 9's checker made exact).**
> Algorithm W is proved sound, refuting, complete, principal and terminating at expression level for
> Hindley–Milner (milestone (b)), with type classes (c), and with records and rows (d, a separate
> function `inferExpWD`, with a bridge to step 9's `IsPrincipal`). With the stronger constraint
> solving of (b) to (d), the core refutation covers 200 of the 217 compile-error tests that need
> inference (`coreRefutes`), unconditionally, and still none of the 625 that compile; 269
> compile-error tests are refused in all, 16 not yet. Milestone (e), annotations:
> `WE.inferExpWD` is sound, terminating, refuting and principal (`WE.wePrincipality`; its result is
> principal in step 9's sense), and at expression level it refuses the six rigid-`let` tests by the
> escape check; one clause of its completeness (it never stops with an internal error where a
> derivation exists) is not yet proved. Step 9's checker now accepts exactly the book's derivations: every type
> at every node has canonical rows and no free bound variable, and an annotation's new variables
> are exactly those the book gives. This last point is an erratum to `sec:static-core-explicit`: a
> new name stands for a row variable exactly when the annotation uses it as a record extension.
> Before the erratum, `let f : a -> a; f x = x in f` had two incomparable derivations. The
> hypotheses W's theorems carried for these conditions now follow from the checker and are gone.
> No certificate changed: 622 `legal_`, 579 `spec_`, 577 `mean_`, 579 `ident_`; 14,540 theorems,
> 0 axiom problems; run-examples unchanged (1,708 checks); compare-e2e 579 of 579.

> **Update, 2026-11-12 (plan step 11, milestone (a), and the end of step 10).** Step 10 is
> complete: the specialisation of a program is unique (`ident_of_spec'`, under D11 and a
> decidable condition that a module's type names are distinct and its aliases ordered), and each of
> the 579 translated tests has its `ident_` theorem. Getting there corrected the encoding in four
> places, each found as a counterexample checked by the kernel and kept as a regression theorem: a
> module's type declarations are one scope (ruling A98; Elm 0.19.1 to 0.19.3 agree; two new tests);
> the type names a derivation generates are its custom types' (`genNames`), not every name outside
> the basis; a type environment may not keep free variables (an erratum to r:sm-topdec-types); and a
> node of a derivation is the sentence, without the instance at an occurrence, which specialisation
> now reads off the occurrence's type. Before these, D11's hypothesis was false for nearly every
> program, so the theorems under it were vacuous; no program's meaning changed. Step 11, milestone
> (a): unification over the full type language with its refutation theorem and a constraint
> generator proved complete for every derivation refute 176 of the 217 compile-error tests that need
> inference, unconditionally, and none of the 625 that compile; 245 compile-error tests are now
> refused in all. Milestone (b) is under way (the most general unifier, algorithm W sound,
> refuting, principal and terminating for the Hindley–Milner fragment). 10,823 theorems, 0 axiom
> problems; run-examples unchanged (1,708 checks, 579 programs).

> **Update, 2026-11-12 (plan step 10, end to end, done except `ident_`).** Lean computes each
> translated test's reduced program from its source: step 8's derived forms, step 9's inference and
> proved checker, number specialisation (`Stat/Specialise.lean`: copies from the outside in, the
> default copy always made, A93's vacuous variables Float) and type erasure. It agrees with the
> translator on all 579 translated tests (`lake exe compare-e2e`), after two translator changes: it
> keeps identifiers as written (`text`, not `Html.text`, in 431 tests), and orders a group's
> `number` variables by first occurrence (LetNumberFracRecordTest's copy `r$Float$Int`). 579 `spec_`
> theorems (4 by `native_decide`) say so per test, and retire `[elab]` for those tests; 577 `mean_`
> theorems give each program a meaning by r:p-program with both premises, under D11 (two tests stop
> at Debug.todo). The 15 rulings on small programs (A27, A87, A93, polymorphic recursion, copy names,
> exposing items, payload types, kinds of `main`) are theorems, none against the book. Findings:
> (1) as specified, an occurrence outside its group could take a `number` variable from an enclosing
> copy, so two principal derivations gave different reduced programs; fixed in Lean and the
> translator (such a variable is Float), no test changed, the counterexample kept as `ce_equal`;
> (2) for a module whose custom type mentions a local alias spelt like an imported type (finding
> B6), a split derivation of its type declaration is principal too and gives a different
> constructor type, so "the specialisation of the program" is not unique and `ident_` is false as
> the definitions stood (resolved by ruling A98, which removes the split, as Elm does); the
> invariance lemma is proved up to the step across bases (about 4,400 lines). `IsPrincipalMod`
> now ranges over derivations without free `bnd` variables, the derivations of the book.
> 8,800 theorems, 0 axiom problems; run-examples unchanged (1,708 checks, 579 programs).

> **Update, 2026-11-12 (plan step 9, the static semantics, done).** Chapters 4 and 5 and the static
> half of Chapter 9 are in Lean: 45 + 20 + 3 rule constructors (45 + 19 + 3 since ruling A98 removed the split of a type declaration), one per rule label of the book
> (`#check_static_rules`), the objects, substitutions, schemes and closure (A93), Appendix C and the
> test basis (`Btest_agrees`, `default_imports_test`), and `LegalProgram` (a program as written meets
> the syntactic restrictions and elaborates with each module's principal derivation meeting the
> further restrictions). Derivations are annotated phrases decided by a structurally recursive
> checker, proved sound (`checkModule_sound`); the pattern decider is proved correct (`inhabited`,
> A97; `useful_spec`). An inference written in Lean and not proved proposes the derivations. 622
> compile-success tests are legal under D11 (`legal_`, the inference's derivation is principal):
> the kernel runs the inference and the checks, except for 9 large programs (`staticBudgetNative` in `Certify.lean`) whose
> kernel check takes 7 GB to more than 40 GB, proved by `native_decide` (`[native]`); the session
> that first built them died when that build filled the machine's memory, and the certificate
> shards now import one another so that a build checks one at a time (16 shards in 11 minutes,
> at most 4.6 GB). 68 compile-error tests are refused (`refuse_`), each for every derivation and
> with no hypothesis about principality: 31 by step 8's restrictions, 6 by scope, constructor arity
> and imports, 13 by type expressions and ports (for every choice of generated type names, splits
> of a type declaration and sorts of explicit variables), 8 by the type of `main`, 9 by
> exhaustiveness or irredundancy (at every type a derivation can give the patterns). Not proved as
> the specification states them: the adequacy of the checker (`checkExp_adequate`), stability under
> substitution (`check_subst`), `canon_eq_iff`, `gen_trans`, the `iff` forms of the deterministic
> functions and of the further decider, and `elab_basis_mono`; the positive theorems run the
> inference in the kernel instead of reading a written certificate, so `mainTransfer` and
> `CertProgram` are not needed. Step 7's provisional classes hold: every test it classed `further`
> or `static-deterministic` is refused as classed, and every compile-success test it classed with
> basis B0, harness, library or helper is legal. 6,679 theorems, 0 axiom problems; run-examples
> unchanged (1,708 checks, 579 programs). Memory on a clean build (`scripts/measure-build.sh`, now
> run in a copy that can read the book's sources, and robust to processes ending while sampled):
> at most 4.6 GB for one `lean` process, at most 11.7 GB summed over concurrent ones, 13 minutes.
> The site's theorem pages for names with `?` (`find?_cons`) now have slugs a URL can carry (`-q`).

> **Update, 2026-11-12 (plan step 8, source syntax, derived forms, syntactic restrictions, done).**
> Every program elm-syntax parses is written in a source syntax in Lean (916 of 939; 21 do not
> parse, 2 hold lone surrogates). The derived forms of Appendix A are a function from it to a bare
> syntax, generated from the same table as the reduced syntax's, and the book's relational form
> is stated: the canonical grouping is one the book allows (`components_valid`), and so is the
> canonical order of aliases (`aliasOrder_valid`), so the function is one of the book's choices
> (`derive_derivesTo`). On the 579 translated programs the derived forms of the source agree with
> the translator, module by module (`compare-derived`, 0 differ). The 27 restrictions decidable on
> a syntax tree are `Prop`s as the book states them, decided by the kernel: 882 programs meet them
> and 34 do not (the 31 tests classed `syntactic`, and three compile-success tests that import
> modules outside the definition), each refusal proved for every order of the program's modules.
> Findings: 197 tests are modules without `main`, which the book does not accept as programs
> (their statements are about the module); two "recursive main" tests meet `res:program-main` as
> the book states it, and two other tests are refused on the tree. 4,215 theorems, 0 axiom
> problems.

> **Update, 2026-11-11 (plan step 7, measure, classify, extract Appendix C, done).** Appendix C and
> the default imports are extracted into `static-basis.json` by a strict reader of the book's LaTeX
> (`ExtractStaticBasis.elm`): 22 type names, 19 modules, 20 operators, 3 hidden identifiers, 11
> default imports, every row of every figure parsed and validated. The translator's hand-written
> schemes agree with it: 70 compared, 0 differ. Every `elm-spec` test is classified for the static
> semantics (`static-classification.json`): of the 311 compile-error tests, 18 do not parse, 8
> parse although they break a rule left to the parser, 31 break a restriction decidable on a syntax
> tree (step 8), 9 exhaustiveness or irredundancy (step 9), 1 depends on operator grouping, 28 are
> refused without inference (step 9) and 216 need complete inference (step 11); of the 628 that
> compile, 39 need nothing beyond B0, 540 only the harness's `Html.text`, 34 library values, 9
> helper modules, 3 modules outside the definition, and 3 do not parse. "Parses it as Elm does" is
> kept as the `[parse]` trust, not checked.

> **Update, 2026-11-11 (plan step 6, statements about every execution, done).** The three CHECK-NOT
> lines the book supports are theorems about every execution the book allows, with every
> derivation of its steps (`WorkerTest.HoldsNot`): TaskOnErrorSucceedTest never logs `handler
> called`, under every host; PortIncomingRejectTest never logs `received: null` and
> StandardA88PortNonFiniteTest never logs `Just`, under the test runner's echo host (another host
> may send a value whose log has the pattern). Each is proved by an invariant on configurations
> and host states, using the uniqueness of what the evaluator computes when it reads no choice
> (D1) for every application, task step and message. Each test's generated theorem is the
> conjunction of its positive checks and its CHECK-NOT. Finding T1 is a theorem: the book allows
> an execution of StandardA81SleepBeyond32BitsTest that logs `the long sleep ended`
> (`t1_a81_long_sleep_may_end`, by the scheduler with one override, a wait of 3e9 ms). The printer
> of values is defined by well-founded recursion, which the kernel does not unfold, so the fact
> that a printed log entry does not contain the pattern is decided by `native_decide`, and the
> three theorems are tagged `[native]`. 579 of 939 tests; 1,708 checks, all agreeing; 2,751
> theorems, 0 axiom problems.

> **Update, 2026-11-11 (plan step 4 completed).** The round trip of encoding and decoding is a
> theorem (`roundtrip`): a value of a canonical payload type that encodes to j decodes from j to
> itself, records sorted, except where A88 says otherwise (NaN, the infinities, -0, a `Just` whose
> argument encodes as null, an Int outside IntRange, and, an exception the specification did not
> list, a record with a repeated label). It assumes one fact about Lean's floats,
> `FloatRoundTrip` (a finite float other than -0 is the float nearest its own value), as a named
> hypothesis: Lean's Float is opaque to the kernel and no lemma relates a float to its bits. A76
> is complete (`a76_mkObj_perm`, `a76_dec_extra_key`), payload types normalise to canonical ones,
> every port of every translated program is checked canonical (`ports_canon_<Shard>`), and
> well-formed values are defined. 2,493 theorems, 0 axiom problems.

> **Update, 2026-11-11 (plan step 5, Chapter 9, done).** Programs are in Lean: the objects of
> execution, dispatch (4 rules), the start (r:p-init, with A72 and A77), the 12 transitions,
> hosts (the book's, none, and the test runner's echo), executions with their logs (D9), traces
> and `Tr` (closed under prefixes), a default scheduler proved sound (`run_sound`), and worker
> tests: `WorkerTest.Holds` states that some execution the book allows, under the test's host,
> has a log that meets every check, proved by `holds_of_run` from a run. The 35 worker tests of
> the plan are theorems (30 by the kernel; ProcessSpawnKillHalfTest, ProcessSpawnRecursiveTest,
> ProcessYieldThrashingTest, TaskOnErrorCascadeTest and TimerEffectTest by `native_decide`, as
> they use Debug.toString); no override of the scheduler was needed (`worker-choices.json` is
> `{}`). The guarantees of A86 (`a86_step`, `a86_out_fifo`), the rulings A62, A72, A77, A79, A80
> and A81, and `a66_batch_order_open` (one program, two executions delivering a batch in either
> order) are theorems. StandardA81SleepBeyond32BitsTest's CHECK-NOT is not stated (finding T1);
> CoreIssue1123NestedCmdBatchStackOverflowTest is refused for its size
> (`construct:large-computation`, finding T2); no test is refused `effects`. Two harness bugs were
> found and fixed: printed strings now escape a newline, tab, carriage return, vertical tab and
> NUL as Elm/JS's Debug.toString does, and a CHECK line's string reads those escapes back
> (PortEchoStringTest); `BVal.mkObj` sorts by insertion, since the kernel cannot reduce
> `mergeSort` (FlagsRecordTest). 576 of 939 tests; 1,701 checks, all agreeing; 1,493 by the
> kernel and 206 native, in 576 program theorems; 2,354 theorems, 0 axiom problems; the build's
> largest process 3.2 GB (ChecksWorker01 2.3 GB), all together 10.4 GB. No finding about the
> book.

> **Update, 2026-11-11 (plan step 4, Chapter 8, nearly done).** Tasks, commands, subscriptions and
> ports are in Lean: boundary values with exact JSON numbers, the effect values, APPLY of Task,
> Process, the ports and the arrays, the 39 rules of task reduction, encoding, decoding and
> messages, flattening, and the elm/core texts of Task with ME0(Task) and ME0(Process). The book's
> encoding and decoding relations are proved equal to structural functions and to be partial
> functions; the property of task reduction is proved; the executable task step and reception are
> sound and complete; every value of a payload type has a canonical encoding; the rulings A74,
> A76, A88 and A92 are theorems (three about particular floats by `native_decide`, Lean's Float
> being opaque to the kernel). The round trip of encoding and decoding remains. No test is gained
> (every test that needs Chapter 8 is a worker, step 5); 1,585 checks unchanged; 2,129 theorems,
> 0 axiom problems.

> **Update, 2026-11-11 (plan step 2 completed).** The property of interfaces is proved: the
> interfaces of the test basis have it, and every interface a module's derivation puts in the basis
> has it when the module's bound names are distinct (`Mod/Good.lean`). Ruling A25 is proved: the
> module `x = let f _ = x in f ()` has no meaning, nor has any program that begins with it, because
> forcing x's thunk loops (`Mod/A25.lean`). 1,673 theorems, 0 axiom problems.

> **Update, 2026-11-11 (plan step 3, the module form, done).** Every translated test is now stated
> as the program it is: its modules (the helper modules it imports from its project's sources,
> then the test) in the reduced syntax of Chapter 7, evaluated by the rules of Chapters 7 and 9 in
> the test basis, and its CHECK lines, as written, as statements about the log of that evaluation
> (`ViewChecks`): an entry with a label and value, an entry with a label, consecutive entries
> (CHECK-NEXT), or a regular expression the printed log matches. The two tests that stop at
> Debug.todo are theorems that their programs have no meaning (`NoMeaning`). The let form's
> theorems (`LetChecks`, `#program_theorems`) are retired. 43 tests more translate: user modules,
> record alias constructors, port modules, views whose `main` is not `text "literal"`, log checks
> inside functions and pipes, and regular-expression checks (the plan's 42, and
> CompilerIssue2019AliasOfTypeVariableTest, which was refused only because `main` logs a label no
> CHECK line names). 541 of 939 tests; 1,585 checks, all agreeing; 1,411 by the kernel and 172
> native, in 541 program theorems; the comparison with the let form's run
> (`runner/compare-example-run.js`) differs only where the plan allows (the strict tests' checks
> now read "no meaning"). The kernel's reduction of a program that logs many values nests more
> deeply than the default limit, so the generated theorems set `maxRecDepth` to 2048 (1024
> suffices). 1,576 theorems, 0 axiom problems; the build's largest process 3.1 GB, all together
> 10.4 GB. No finding about the book.

> **Update, 2026-11-11 (plan step 2, Chapter 7, in progress).** Chapter 7 is in Lean: its reduced
> syntax, interfaces and the merge, the thunk translation of value groups, the 20 rules and the
> two dynamic rules of Chapter 9 for a program's modules, logged twins, an evaluator proved sound
> and complete, with `noMeaning_of_stuck` and uniqueness for programs, the dynamic ME0 of the
> default-imported modules (with `Ok`, `Err`, `logBase`, `never` and the effect values of
> `Cmd.none` and `Platform.worker`), the harness Html and the test basis, the frame lemmas, and the
> rulings A82, A38 and A28 on programs written by hand. The let form's E0 is now the environment the
> default imports give in that ME0. Seven more tests translate: 498 of 939; 1,500 checks, all
> agreeing; 1,334 by the kernel, 166 native. 1,529 theorems, 0 axiom problems; the build's largest
> process 3.1 GB, all together 9.1 GB. Still open in this step: A25 and the property of interfaces.

> **Update, 2026-11-11 (plan step 1, the Core's foundations).** Done as
> plans/lean-full-definition/step-01-core-foundations.md specifies, with the differences its "Done"
> section records. The evaluator now reads an oracle (a sequence of Booleans, one per choice of
> APPLY) and returns its outcome, its log and the index of the next choice; it is proved sound and
> complete for the rules, and `noValue_of_stuck` and `evExp_unique` turn a run that reads no choice
> into statements about every derivation. Each of the 17 relations has a logged twin, tied to it by
> `forget` and `lift`, and a build-time check keeps the twins in step with the rules. The checks of
> the translated tests are now one theorem per program (491), stating each value structurally
> (`Expect`): 1,487 checks, all agreeing; 1,322 proved by the kernel (1,162 before: the data,
> character and function values and the two checks that expect no value are now stated), 165 by
> `native_decide`, of which 19 are the checks of AppendTypeSplitTest and DeepEqualityTest, moved
> there by the memory budget (14.7 GB and 9.4 GB in the kernel through the logged evaluator). The
> clean build's largest Lean process now needs 3.3 GB and all of them together 7.8 GB. 1,251
> theorems, 77 of them native, all with the expected axioms. No finding about the book.

> **Update, 2026-11-11 (plan step 0, the baseline).** The plan to encode the rest of the definition
> (plans/lean-full-definition.md) is under way. Its step 0 adds the translator option
> `--report-all-refusals` (every refusal of every test, each lifted in turn), the inventory script
> `runner/part1-inventory.js`, and `standard-elm-mech/scripts/measure-build.sh`. Baseline: 491 of 939
> `elm-spec` tests translated; 1,487 checks, all agreeing; 1,162 theorems by `decide +kernel`; the
> largest single Lean process 6.28 GB (shard Elm01, nearly all of it AppendTypeSplitTest) and a peak
> of 10.97 GB summed over the concurrent processes of a clean build. Part I of the plan can bring in
> 87 more tests.

> **Update, 2026-11-11 (CHECK lines tightened).** CustomTypeMultiFieldTest, CustomTypeNestedTest and
> FloatNaNTest had CHECK lines naming only a label, which the translator cannot compare; with their
> values written out they translate, and FloatNaNTest now checks `isNaN (nan + 1.0)`; FloatEdgeTest
> and CoreIssue1080ClampNanTest check each NaN they expect with `isNaN` too. 491 of 939 `elm-spec`
> tests translate; the run has 1,487 checks, all agreeing with the book, and 1,162 theorems by
> `decide +kernel`.

> **Update, 2026-11-10 (review round 3).** After the book's third review and the test changes it
> led to (six tests retagged `elm-unspecced`, LetSeparatedStagingTest given its CHECK line, two tests
> annotated to keep an Int use), 488 of 939 `elm-spec` tests translate. The run has 1,478 checks,
> all agreeing with the book, and 1,157 theorems by `decide +kernel`. No book finding: the rulings
> revised in the review (A27, A94, A96, A97) concern the static semantics and conformance, which the
> encoding does not cover.

> **Update, 2026-11-10 (number defaults to Float).** Ruling A27 is revised: a `number` variable that
> nothing fixes is Float, and the default copy of number specialisation is the copy at Float (`abs`
> is bound to its copy at Float, its copy at Int to `abs$Int`). The translator's default changes
> with it. Checks of a Float value now have kernel theorems too, comparing the float as Elm prints
> it (`Expect.flt`; `showFloat` is computed exactly with integers, which the kernel reduces). The
> run has 1,477 checks, all agreeing, and 1,156 theorems by `decide +kernel` (from 1,106).

> **Update, 2026-11-09 (widening the basis).** Following plans/lean-encoding-widening.md, the
> encoding now has the conversions (`toFloat`, `round`, `floor`, `ceiling`, `truncate`, saturating,
> NaN to 0), `sqrt`, Float `^`, the elementary functions with `e` and `pi`, `append` (`++`),
> `Char.toCode` and `Char.fromCode` (a qualifier `Char` in E0) and `Debug.toString`. 487 of 941
> `elm-spec` tests translate; the run has 1,477 checks, all agreeing, and 1,106 theorems by
> `decide +kernel`. A program that uses a value the kernel cannot compute (`Float.floor`, the C
> library's elementary functions and power, float printing) is marked `native` and its checks are
> proved by `native_decide` only. Floats now print as Elm prints them, the shortest decimal that
> reads back as the float (JavaScript's Number::toString), computed exactly; before, Lean's
> six-digit `toString` agreed only on short values. New theorems `a44_conversions` and
> `a44_round_minus_half`. One newly translatable test, WideRecordGcBitmapTest (lists of 150000
> elements), is refused as `construct:large-computation`: it is beyond the evaluator's fuel.

> **Update, 2026-11-09 (translator).** The examples are now made by a program: the translator
> `definition/tools/src/Translate.elm` (plans/elm-to-lean-translator.md) translates every test tagged
> `elm-spec` that the encoding can express, 381 of 941, into `Generated/`; the others are listed with
> their reasons in `translation-manifest.json`. The run has 1,176 checks, all agreeing, and 985
> theorems are generated by `#kernel_checks`. `isNaN` and `isInfinite` are now encoded. The derived forms of `Derived.lean` are generated from
> the same table as Appendix A. Showing the run's floats as Elm's `Debug.log` does, a zero prints as
> `0` (`showElmSigned` keeps the sign for the theorems on A48 and A49), and `abs` has its copy at
> Float (`abs$Float`). Float `^` is not encoded, so tests using it are refused (since encoded: see
> the update above).

> **Update, 2026-11-09.** Since this report, every example has been made a test program of this
> repository's `tests/`. The examples taken from eco's divergence tests (RemainderByZeroTest,
> ModByZeroKernelPathTest, FunctionEqualityFalseTest, HexLiteralNegativeI64Test,
> FloatIeeeSemanticsTest) were removed. The book's and the survey's examples for A42, A43 and A49 and
> the coverage program became tests (StandardA42ZeroDivisorTest, StandardA43PowNegativeTest,
> StandardA49ClampTest, StandardCoreEvaluationExamplesTest, StandardLetStrictTest,
> StandardApplicationStrictTest), and the suite's own tests of A40, A42, A46, A48 and A51 were
> translated; the Int range example was dropped, StandardA40IntOverflowTest standing for it. The A43
> test states the book's values, so there are no known divergences. The run now has 55 programs and
> 208 checks, all agreeing; 193 theorems are generated by `#kernel_checks`, and `coverage_derivable`
> was added. `example-run.md` is the current run; the counts below are those of the original run.

## Summary

| Item | Value |
|------|-------|
| Tool | Lean 4.35.0 with Lake 5.0.0, project `standard-elm-mech/` |
| Build | `lake build && lake exe run-examples`: builds with no errors and no `sorry` |
| Encoding size | 3,008 lines of Lean in 14 files |
| Scope of this pass | Chapter 6 (Dynamic Semantics for the Core, `dynamic-core.tex`) and, from Appendix D, APPLY for Int arithmetic, Float + - * / and negate, equality, order, min, max and clamp, Booleans, Debug.log and Debug.todo |
| Rules encoded | 48 / 48 of Chapter 6, one Lean constructor per rule, named `r_d_<slug>` after `r:d-<slug>`. Over the six semantics chapters: 48 / 192 (the other 144 are out of this pass's scope, see Not Encoded) |
| APPLY encoded | 43 relation constructors, one per line of the book's displays: Int (14), Float arithmetic (5), equality (3), order (9), min and max (4: IEEE 754-2019 minimum and maximum at floats, the comparison otherwise), clamp (2: min (max x lo) hi with those operations at floats; the three lines of the elm/core text otherwise, merged into one constructor as for min and max), Booleans (5), Debug.log (1); Debug.todo has none, so its set is empty |
| Book version | The chapter and appendix files as revised by the concurrent audit pass (dynamic-core.tex and appendix-dynamic-basis.tex as of 2026-11-07 12:41 and 12:43). The encoding was begun on the earlier text and updated: the only rule that changed is r:d-atexp-op (see F1). Updated again for the author's revised ruling A48 (2026-11-07): min and max are basic values of Appendix D, IEEE 754-2019 minimum and maximum at floats, no longer Elm texts. Updated again for the author's revised ruling A49 (2026-11-07): clamp is a basic value of arity 3, min (max x lo) hi with those operations at floats and the result of its elm/core text at Int; abs stays an Elm text |
| Semantic objects | Val, SVal, BasApp, ConVal, Record, Tuple, Closure, Env, QualEnv, ValEnv, VE/FAIL, v/FAIL, Rec, FV(valbind), the dynamic operator table OT_dyn, E0 and E_K; the Int range fixed to eco's (64-bit, norm = wrap modulo 2^64). The values of the Elm texts used are proved to be what r:d-dec-nonrec gives in E_K (`elmTexts_eval`) |
| Derived forms | Every Core row of Appendix A as a function, including the grouping of a let into components ordered by "refers to" |
| Evaluator | Fuel-bounded, one function per judgement, parameterised by the choice of a member of APPLY. Proved sound: `evExp_sound` (every result it gives is derivable by the 48 rules) |
| Examples run | 262 checks in 53 programs: 40 eco test programs (149 checks), 12 ruling programs (96 checks), 1 coverage program (17 checks) |
| Agreement | 259 agree, 3 diverge. All 149 corpus checks agree. The 3 divergences are the known ruling A43 (3). The 16 clamp checks added for the revised A49 (6 of FloatIeeeSemanticsTest, 1 of CoreIssue1080ClampNanTest, 9 book examples) all agree. The four A48 checks of FloatIeeeSemanticsTest that diverged under the provisional ruling (`max nan 1`, `min nan 1`, `max 0 -0`, `min -0 0`) now agree, as do `max 1 nan`, `min 1 nan`, `max -0 0` and `min 0 -0` |
| Machine-checked | 224 examples proved by the kernel (`decide +kernel`, one theorem each); every agreeing example proved derivable by `corpus_derivable` and `rulings_derivable` (`native_decide`); A48 stated directly by `a48_float` (`native_decide`) and `a48_int_max`, `a48_int_min` (kernel); A49 by `a49_apply_float`, `a49_float_lo_gt_hi` (`clamp 10 0 5` is +0), `a49_float_nan_bound` (`clamp nan 1 0.5` is NaN), `a49_float_signed_zero` (`clamp 0 1 -0` is +0) (`native_decide`, floats compared as printed) and `a49_int_lo_gt_hi` (`clamp 10 0 5` is 10 at Int, kernel), `a49_int_apply_singleton` |
| Rule coverage | 47 / 48 rules exercised by the examples (by inspection); r:d-match-fail is not, see finding F4 |

Implementation results are eco's: the value on each program's `-- CHECK:`
line, which is eco's tested output. The 224 checks taken from eco test files
were compared with those files, 0 mismatches (217 mechanically in the
earlier run; the 7 clamp checks added for A49 by reading
FloatIeeeSemanticsTest.elm lines 85-90 and 278-283 and
CoreIssue1080ClampNanTest.elm). eco was not run in this pass. For A43 and
for the A49 book examples eco has no test; its value is the one the survey
records (ambiguity log A43, eco `IntArith.hpp:38-44`; A49, eco
`MonoOpt/FloatMinMax.elm:75-82`). For the Int range
checks the value is Appendix E's statement of eco's behaviour.

The corpus programs are, from `eco-compiler/test/elm/src/`: IntAdd, IntMul,
IntDiv, IntDivByZero, IntModBy, IntRemainderBy, IntPow, IntNegate, IntAbs,
IntCompare, IntMinMax, BoolAnd, BoolOr, BoolNot, BoolXor, BoolShortCircuit,
CompareChar, CompareEmptyList, CompareTupleWithEmptyList, Equality,
EqualityBoolContainer, EqualityBoolRecord, CaseCustomType, CaseListCons,
CaseNested, CaseTuple, CaseTree, CaseChar, LetDestructuring,
LetDestructRecord, LetRecMultiArg, LetRecClosure, RecordUpdate,
RecordChainedUpdate, RecordAccess, ClosureCapture01, RecursiveFactorial,
MutualRecursion, TailRecursiveSum, PartialAppChain (each `...Test.elm`).
Every CHECK line of these 40 programs is encoded. The ruling programs are
eco-divergence's RemainderByZeroTest, ModByZeroKernelPathTest,
FunctionEqualityFalseTest, HexLiteralNegativeI64Test and
FloatIeeeSemanticsTest, elm-bugs' CompilerIssue2362NanTupleEqualityTest,
CoreIssue988NanContainerSelfEqualityTest and CoreIssue1080ClampNanTest (the
checks of these eight that use no List, Dict, Set, Array or String
functions), and four book examples (A42, A43, A49, the Int range). The full table is
`example-run.md`.

Modelling choices that stand in for chapters outside this pass: a program's
top-level definitions are placed in a `let` around the logged expression
(grouped into components as Appendix A groups both), its custom types'
constructors are bound in the environment, and the default imports'
contribution to the environment (Chapter 7) is added to E0 by hand. Where an eco program writes
`List.length []` to defeat constant folding, the encoding writes `0`.

## Not Encoded

| Rule | Reason |
|------|--------|
| Chapter 6, all 48 rules | None missing: every rule is encoded. Number specialisation (sec:dynamic-core-numbers) is not computed, because it is defined on elaborated programs and needs the static semantics; examples are written after specialisation, with each integer constant typed Int (`SCon.int`) or Float (`SCon.intF`) by hand. The rounding of constants to floats uses Lean's `Float.ofNat` and `Float.ofScientific`, not the book's fl |
| Chapter 4, Static Semantics for the Core (45 rules) | Out of this pass's scope |
| Chapter 5, Static Semantics for Modules (19 rules) | Out of this pass's scope |
| Chapter 7, Dynamic Semantics for Modules (20 rules) | Out of this pass's scope; replaced in the examples by the modelling choices above |
| Chapter 8, Tasks, Commands, Subscriptions and Ports (37 rules) | Out of this pass's scope; EffVal is omitted from Val |
| Chapter 9, Programs (23 rules) | Out of this pass's scope |
| APPLY: Float `pow` (fig:dynamic-basis-pow) | Outside the fragment (Floats limited to + - * / and negate) |
| APPLY: sqrt, cos, sin, tan, acos, asin, atan, atan2, Elm.Kernel.Basics.log, isNaN, isInfinite (fig:dynamic-basis-float, fig:dynamic-basis-elem) | Outside the fragment |
| APPLY: toFloat, round, floor, ceiling, truncate (fig:dynamic-basis-conv) | Outside the fragment |
| APPLY: append on strings and lists | Outside the fragment |
| APPLY: Debug.toString | Outside the fragment; its string is implementation-dependent |
| APPLY: Array.fromList, Array.toList | Outside the fragment (Chapter 8 uses them) |
| APPLY: Task, Process, Platform, Cmd, Sub basic values, Task.command, port values | Effects, out of this pass's scope |
| Eq: process identifiers, JSON values, effect values (clauses 3 and 4) | Their values are not in the encoded Val |
| Float add, sub, mul, fdiv, negate | Encoded with Lean's `Float` (IEEE 754 binary64, round to nearest even), not line by line from fig:dynamic-basis-float; the figure was read against IEEE 754 and agrees with it |
| Values written in Elm: logBase, degrees, radians, turns, fromPolar, toPolar, never; the Elm texts of Task, Cmd and Sub | Outside the fragment. abs, composeL, composeR, apR, apL, identity and always are encoded as closures made from their texts in E_K by r:d-dec-nonrec. abs is not a basic value: the book defines it by its elm/core text, so it is encoded that way and not as an APPLY case (its default copy, at Float, and its copy at Int are both encoded). min, max (A48) and clamp (A49) are basic values, encoded as APPLY cases |

## Findings From Encoding

| Rule | Problem | Disposition |
|------|---------|-------------|
| F1. r:d-atexp-op, with r:dm-imports-import and r:dm-expitem-op (text before the audit revision) | Undefined lookup. The rule's premise was E(opv) = v, with E(opv) meaning E(longvar) for the variable the operator is bound to, e.g. `Basics.add`, "looked up through the qualified environment". But r:dm-imports-import binds the qualifier Basics to the value environment of the interface of Basics, which holds only exposed values, and the operators' variables are not exposed. So E(Basics.add) was undefined in every module, and no infixed operator other than `::` had a value: `10 + 3` had no derivation. Found while building E0. The concurrent audit found the same gap (audit X1, decision 1) and the book now has r:d-atexp-op with no premise and value OT_dyn(opv), the dynamic operator table of Appendix D; the encoding was updated to that rule, and every example gives the same value under it | fix book: stage 04 and 05 (done during this run by the audit's decision 1; nothing further) |
| F2. Appendix D, B0 = ME0 (text before the audit revision) | Ill-typed object. Appendix D gave ME0(modid) = (∅, VE), an Env, where Chapter 7 (fig:dynamic-modules-compound) needs an Interface (RA, CE, VE), since r:dm-imports-import reads B(modid) = I. The revised Appendix D gives ME0(modid) = (RA, CE, VE) (audit X4, decision 2). The encoding uses only the value environments, so it was not affected | fix book: stage 05 (done during this run by the audit's decision 2; nothing further) |
| F3. Rule group Pattern Rows (r:d-patrow-field) | The group's judgement form is written E, r ⊢ patrow ⇒ VE/FAIL, but its one rule gives VE, its Comment says a pattern row never gives FAIL, and r:d-atpat-record's premise expects VE. The encoding uses VE | fix book: stage 04 (write the group's form as ⇒ VE) |
| F4. r:d-match-fail, and the FAIL outcome of r:d-match-next | Never used in the derivation of any well-typed program: a case's match is exhaustive (Comment on r:d-exp-case), so a whole match never gives FAIL. It is the one rule no example exercises, and none can. Not wrong: the judgement stays total over its outcomes | known |
| F5. r:d-patrow-field | The conclusion uses r(lab), a partial operation, with no premise that lab is in Dom r (the Comment says elaboration ensures it). The encoding makes it the premise r(lab) = v | known |
| F6. sec:dynamic-core-simple, Fun in fig:dynamic-basis-eq | ConVal = Con x Val^k carries no arity, but deciding whether a constructor value is a function value (k < arity(con)) and Eq clause 4 (k = arity(con)) need it. The book says arity(con) is that of the custom type of the value at hand; the encoding makes a constructor name a pair (spelling, arity) | known |
| F7. Appendix E, sec:appendix-implementation-equality (A50, eco row) | Appendix E says eco gives True for `p == p` with `p = ( nan, 1 )` (identity shortcut). eco's own tests pin the opposite: CompilerIssue2362NanTupleEqualityTest expects `p == p: False`, and CoreIssue988NanContainerSelfEqualityTest expects False for a record, a custom-type value, a Maybe and shared inner tuples and lists compared with themselves. The definition gives False in every case, agreeing with the tests. The eco row may be out of date | fix book: stage 05 (re-check eco's A50 behaviour and correct the row if eco now conforms) |
| F8. Grouping of a let (sec:appendix-derived-forms-let), A62 | eco's tests read Debug.log output in source order, but the `_ = Debug.log ...` definitions of a let are independent components whose order the definition leaves open, and output lies outside it. Values are unaffected, so no example diverges | known |

## Divergences

| Example | Book Says | Implementation Says | Rules Involved | Disposition |
|---------|-----------|---------------------|----------------|-------------|
| `1 ^ -1` (A43 book example; eco has no test) | 1 | 0 (survey A43, eco IntArith.hpp:38-44) | r:d-exp-app, r:d-atexp-op, r:d-app-basic-partial, r:d-app-basic-apply; APPLY(pow, m, n) for n < 0 and m = 1 (fig:dynamic-basis-int). Kernel-checked: `a43_one`, and `a43_apply_singleton` (the set is {1}) | fix implementation (ruling A43: eco's 0 is recorded as a divergence to fix; Appendix E records it) |
| `(-1) ^ -3` (A43) | -1 | 0 (survey A43) | as above; APPLY(pow) for m = -1. `a43_minus_one_odd` | fix implementation |
| `(-1) ^ -2` (A43) | 1 | 0 (survey A43) | as above. `a43_minus_one_even` | fix implementation |

Agreements worth recording, since they bear on the rulings the orchestrator
named:

* A42: `x // 0`, `modBy 0 x` and `remainderBy 0 x` give 0 in the definition
  and in eco (IntDivByZeroTest, ModByZeroKernelPathTest, RemainderByZeroTest,
  and the book's own `3 // 0`, `modBy 0 3`, `remainderBy 0 3`; theorems
  `a42_*`).
* A51: for `f == f`, `(\x -> x) == (\x -> x + 0)`, `{ h = f } == { h = g }`,
  `{ h = f } == { h = f }` and `Just f == Just g` the definition gives the set
  {True, False}; eco's answers (True for the same reference, False otherwise)
  are each a member, so they agree. `a51_true` and `a51_false` prove that
  `(\x -> x) == (\x -> x)` evaluates to both.
* Int range: 64-bit wrap of constants (`0xFFFFFFFFC0000000` is
  -1073741824), of `max + 1`, `negate min`, `min // -1` and `abs min` agrees
  with eco.
* Float order (A46, A47): all 35 order and equality checks of
  FloatIeeeSemanticsTest that the fragment covers agree, including
  `compare nan nan` = EQ, `[nan] > [1]` = True and `( nan, 0 ) == ( nan, 0 )`
  = False.
* A48 (as revised by the author): the 12 `min` and `max` checks of
  FloatIeeeSemanticsTest agree, among them `max nan 1`, `max 1 nan`,
  `min nan 1` and `min 1 nan` (NaN), `max 0 -0` and `max -0 0` (+0), and
  `min -0 0` and `min 0 -0` (-0), through r:d-app-basic-partial and
  r:d-app-basic-apply with APPLY(max) and APPLY(min) at floats. IntMinMaxTest
  agrees through the comparison case.
* A49 (as revised by the author): the 6 `clamp` checks of
  FloatIeeeSemanticsTest (`clamp 0 1 nan`, `clamp nan 1 0.5` and
  `clamp 0 nan 0.5` are NaN; `clamp 0 1 2` is 1, `clamp 0 1 -1` is +0,
  `clamp 0 1 0.5` is 0.5) and CoreIssue1080ClampNanTest
  (`clamp -100 100 (0 / 0)` is NaN) agree, through APPLY(clamp) at floats.
  The book examples agree with the survey's eco values: at Float,
  `clamp 10 0 5` is +0 (hi), `clamp 0 1 -0` is +0 and `clamp -1 -0 0` is
  -0; at Int, `clamp 10 0 5` is 10 (lo), `clamp 10 0 20` is 0, and
  `clamp 0 10 -5`, `clamp 0 10 15`, `clamp 0 10 7` are 0, 10 and 7.

## Checkpoint record

The author asked for the pipeline to run without stopping, so the checkpoint
after step 6 records a proposed disposition for each item instead of asking.
Proposed: F3 to stage 04, F7 to stage 05, F4, F5, F6 and F8 known (F1 and
F2 were fixed in the book during this run by the audit's decisions 1 and 2); A43 divergences fix implementation. (The A48 divergences of the earlier run are gone: the author revised A48 to eco's IEEE minimum and maximum, and A49 to eco's clamp at Float; the clamp checks added for A49 all agree.) None of
these is yet the human's disposition, so the stage audit's "Dispositions"
check is open until the author confirms them.
