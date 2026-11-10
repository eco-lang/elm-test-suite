# Mechanisation Guide

How to encode the definition in a machine-checked form and test it. The book
is the source of truth: the encoding follows the book, and a mismatch is a
finding about one or the other, never fixed silently in the encoding.

## Common Method

1. **Syntax as data.** Each bare phrase class is an inductive type with one
   constructor per production. Options become separate constructors or option
   types; keep a comment naming the grammar label.
2. **Objects as types.** Finite maps as association lists or finite map
   libraries; disjoint unions as sum types; sets of names as finite sets.
3. **Rules as relations.** Each judgment form is an inductive relation; each
   numbered rule is one constructor named `r<n>_<slug>` (e.g. `r4_let`).
   Side conditions are extra hypotheses.
4. **Conventions made explicit.** The state and exception conventions (or the
   book's own effect conventions) are expanded into explicit rules. Generate
   the implicit exception rules mechanically where the tool allows; record how
   many were generated.
5. **Derived forms as functions** from full syntax to bare syntax, so examples
   can be written in full syntax.
6. **Executable where possible.** To test, the encoding must compute: an
   inductive relation plus a decision procedure or an evaluator proved (or at
   least tested) to agree with it.

## Tools

**Ott (with Lem or a proof-assistant backend).** Write grammar and rules
directly in Ott syntax, close to the book's notation. Ott checks that rules
parse against the grammar and generates LaTeX and prover definitions. Good
first choice: it checks well-formedness with the least effort. Execution
needs a backend (Coq or Isabelle) plus a hand-written evaluator.

**Lean 4.** Inductive types and relations; write an executable interpreter
and type checker as functions, then prove or test that they agree with the
relations. Good when proofs of properties (O7) are wanted later.

**Coq (Rocq).** As Lean. Mature libraries for finite maps; extraction to
OCaml for fast testing.

**PLT Redex.** Grammar and judgment forms in Racket; `judgment-holds` and
random testing (`redex-check`) out of the box. Fastest route to testing
rules against examples; no proofs.

## Derived Forms in the Encoding

The derived-form functions of `Derived.lean` (`bin`, `ifte`, `ifChain`, `andalso`, `orelse`,
`lams`, `neg`, `listE`, `accessor`, `access`, `listP`) are generated from the same table as the
book's Appendix A, `definition/tools/src/DerivedForms/Table.elm`, by
`GenerateDerivedForms.elm`, between the `-- BEGIN GENERATED derived forms` and
`-- END GENERATED derived forms` lines. Change a derived form in the table and run the generator;
the groupings (`components`, `groupBind`, `letDefs`) stay hand-written. After any change, run
`lake exe dump-phrases` before and after and compare: the phrases of the examples must not change
unless the derived form was meant to.

## Example Corpus

Every example is a test program of this repository's `tests/`, as
`../../../shared/run-config.md` "Example corpus" requires, and the examples
are made by the translator, not by hand:

1. `Translate.elm` reads every test tagged `elm-spec`, and either translates
   it (a `Program` in a shard of `StandardElmMech/Generated/`, its checks with
   the kinds of their values, its integer constants at Int or Float by number
   specialisation) or refuses it with a reason (`compile-error`, `effects`,
   `import:<Module>`, `basis:<name>`, `construct:<name>`, `checks:<detail>`,
   `type`, `number`, `parse`), all listed in the manifest. The design is
   `plans/elm-to-lean-translator.md`.
2. The manifest's refusals are the to-do list for widening the encoding: a
   `basis:` reason names a value of the basis the encoding does not include,
   and its count says how many tests it keeps out.
3. For each rule that no translated test exercises, and each example the book
   gives in its Comments, write a test first (in `tests/elm/`, tagged
   `elm-spec` and the rule's label, expected values the book's); the
   translator then translates it. A check whose expression has no value (it
   stops at `Debug.todo`) is a test with `-- EXIT: 1` and
   `-- CHECK-NOT: <label>:`, translated with the expected value `(no value)`.
4. Hand translation is only for a test the translator refuses whose other
   checks the encoding can express: translate those checks in `handPartial`
   (Examples.lean), keeping every label and expected value exactly as the
   test states them, and say in the doc comment which checks are left out.

The translator's own tests are `definition/tools/tests/` (run with
`site/node_modules/.bin/elm-test` from `definition/tools/`); a change to the
translator is tested there and then checked by a full `lake build` and
`lake exe run-examples`.

Record for each example: the program, the implementation's static result
(accepted, rejected and why) and dynamic result (value, exception), and the
encoding's results (example-run.md and example-run.json).

## Report

```
# Mechanisation Report

## Summary
Tool, encoding size, rules encoded / total, examples run, divergences.

## Not Encoded
| Rule | Reason |

## Findings From Encoding
| Rule | Problem (e.g. undefined operation, ill-formed premise) | Disposition |

## Divergences
| Example | Book Says | Implementation Says | Rules Involved | Disposition |
```

Dispositions: `fix book: stage NN`, `fix implementation`, `known`.
