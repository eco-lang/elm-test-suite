The static semantics of the Core ([Chapter 4](/standard/static-core)), of modules ([Chapter 5](/standard/static-modules)) and of programs ([Chapter 9](/standard/programs)); the dynamic semantics of the Core ([Chapter 6](/standard/dynamic-core)), of modules ([Chapter 7](/standard/dynamic-modules)), of tasks, commands, subscriptions and ports ([Chapter 8](/standard/effects)) and of programs (Chapter 9); and the arithmetic, equality, order, Boolean, conversion, append and character part of *APPLY* are encoded in the proof assistant Lean 4 ({{lean}}), one inductive relation per judgement and one constructor per rule, {{rules}} rules in all. A type inference is proved sound and principal for the static semantics. An evaluator is proved sound and complete for the dynamic semantics: whatever value it computes, the rules derive ([`evExp_sound`](/standard/proofs/evExp_sound)), and every derivation is found by it. Every theorem below is checked by Lean each time the project is built, and each has a page with its statement and proof.

The evaluator is run on the test programs of this suite, translated into Lean by a program from their Elm source: {{translated}} of the {{total}} tests tagged elm-spec, with {{checks}} checks, of which {{agree}} agree with the value the test expects{{diverge}}. [{{programs}} further theorems](/standard/proofs/kc) are generated when Lean compiles the project, one for each translated program, proving that the rules give {{generated}} of those checks the value the test expects.

## Which tests are in Lean

The translator, `definition/tools/src/Translate.elm`, puts each of the {{total}} tests tagged elm-spec into Lean in up to two forms. The first is the program as written, in the source syntax the book starts from; the static semantics is proved about it. The second, only for a test whose program compiles, is the reduced program, which Lean's evaluator runs to prove the test's checks.

### Static semantics: is the program legal?

Lean proves {{legal}} programs legal (a theorem `legal_<project>_<Test>`) and {{refused}} not legal (`refuse_<project>_<Test>`), the second for the tests that expect a compile error. Each test's page names its theorem and how it is proved.

<slot name="statics"></slot>

### Evaluation: the reduced program

Of the {{compileSuccess}} tests whose program compiles, {{translated}} are translated into a reduced program the evaluator runs. The rest are not, for one of the reasons below. A test that expects a compile error has no meaning to run, so it has no reduced program. A value or module of the basis that the encoding does not include keeps a test out until the encoding includes it.

<slot name="evaluation"></slot>
