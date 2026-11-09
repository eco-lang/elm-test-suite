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

## Example Corpus

Every example is a test program of this repository's `tests/`, as
`../../../shared/run-config.md` "Example corpus" requires:

1. A corpus of the tests tagged `elm-spec` whose checks the encoded fragment
   can express, enough to exercise every encoded rule.
2. The tests of the rulings the encoded part of the basis bears on (the
   `StandardA<n>...Test` programs, and issue tests such as
   `CoreIssue1080ClampNanTest`).
3. For each rule that no example exercises, and each example the book gives
   in its Comments, a test written for it first (in `tests/elm/`, tagged
   `elm-spec` and the rule's label, expected values the book's), then
   translated. A check whose expression has no value (it stops at
   `Debug.todo`) is a test with `-- EXIT: 1` and `-- CHECK-NOT: <label>:`,
   translated with the expected value `(no value)`.

Translate a test whole where the fragment allows; where some checks use
something the encoding does not cover (a library function outside the encoded
part of the basis), translate the others and say which are left out in the
example's doc comment. Keep the label of every check exactly as the test
logs it, and its expected value exactly as the test's CHECK line states it.

Record for each example: the program, the implementation's static result
(accepted, rejected and why) and dynamic result (value, exception), and the
encoding's results.

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
