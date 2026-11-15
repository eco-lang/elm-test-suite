# Record pattern rows that bind a variable of their own

**Status (2026-11-15): done.** Steps 1 to 5 carried out; `scripts/verify.sh full` passes with 640
of the 955 `elm-spec` tests translated and proved end to end (was 628 of 942), and the four
compilers match the baseline. One finding, in step 1 (Findings, below). The author chose this route (option 2 of the discussion of
2026-11-15) over rewriting copies through a fresh root (option 1) and over a pattern row that only
number specialisation may produce (option 3). An adversarial review of the first draft found five
major and twelve minor problems; all are corrected below ("Review", at the end).

## The problem

A record pattern row is a bare label: `patrow ::= lab ⟨, patrow⟩` (syntax-core.tex:551;
appendix-full-grammar.tex:151). The label does two jobs. It names the field the row reads, and it
is the variable the row binds: rule `r:s-patrow` has the premise `var = lab` ("a field of a record
pattern binds the variable spelt as its label", static-core.tex:745-748), and rule
`r:d-patrow-field` binds `lab` itself (dynamic-core.tex:692-698).

Number specialisation (dynamic-core.tex, sec:dynamic-core-numbers, ruling A87) replaces each
declaration whose bindings quantify `number` variables by copies, "the copies binding distinct new
variables". For a destructuring binding of a `let`

```elm
{ h } = { h = \x -> x - 3 }      -- h : number -> number, used at Int
```

the copy at Int must bind a new variable to field `h` of the copied record. No record pattern can
do that: a row that reads field `h` binds a variable spelt `h`. Renaming the label as well would
change the record's type, and the right-hand side may be any expression whose labels are fixed (a
function's result, a record from flags). The book asks for a copy its own syntax cannot write, so
it gives no meaning to such a program, which Elm 0.19.1 accepts. Lean's specialisation refuses it
(`SpecError.recordPatternCopy`, Stat/Specialise.lean), and so does the translator
(Translate/Specialise.elm, `renamePattern`). Step 10 recorded it as issue 4
(plans/lean-full-definition/step-10-end-to-end.md), and it is why
CovLambdaSetFunctionsDestructuredFromTuplesAndRecordsTest does not translate.

Only `let` destructuring bindings meet it. There is no pattern binding at the top level
(`res:modules-no-top-pattern`), and a record pattern in a lambda, a function's parameters or a
`case` binds a monomorphic variable inside one copy. It arises when such a binding's pattern
contains a record pattern at any depth (`( { h }, g ) = …`) and the program needs a copy other than
the default.

## The design

Follow *The Definition of Standard ML*, as Author Direction 7 ("Otherwise as ML") asks. In SML the
bare pattern row is `lab = pat`, and a row written as an identifier is a derived form (Appendix A
of the Definition: `vid ⟨: ty⟩ ⟨as pat⟩ ⟨, patrow⟩` stands for `vid = vid ⟨: ty⟩ ⟨as pat⟩ ⟨,
patrow⟩`). Here:

1. **Bare syntax.** The pattern row becomes `patrow ::= lab = var ⟨, patrow⟩`: the label names
   the field, and the variable is a variable like any other.
2. **Derived form.** A new row, in a new block for pattern rows in the figure "Derived forms of
   Patterns": `lab ⟨, patrow⟩ ⟹ lab = var ⟨, patrow⟩`, where `var` is the variable spelt as `lab`.
   Elm's `{ h }` is this derived form, with the equivalent form `{ h = h }`.
3. **The field accessor.** Its equivalent form `(\{ lab } -> lab)` (df:field-accessor, in the
   first figure) would use the new row from a later figure, which B4 forbids (every equivalent form
   uses only bare syntax and earlier rows, appendix-derived-forms.tex:31-33). It is written in bare
   syntax instead: `(\{ lab = lab } -> lab)`. The paragraph on it (D5, appendix-derived-forms.tex:
   78-80) and the sentence "the only variable bound by an equivalent form …" (line 113-114) are
   reworded.
4. **Restriction.** Elm has no bare row at all: Elm 0.19.1 rejects `{ n = m }` and also
   `{ n = n }` as a pattern ("UNFINISHED RECORD PATTERN"). The full grammar is the bare grammar plus
   the derived forms (appendix-full-grammar.tex:22-25), and the syntactic restrictions apply to a
   program as written, before derived forms are replaced (syntax-core.tex:582-585). So one new
   restriction among Chapter 2's: *no pattern row of a program has the form `lab = var`*. The
   restrictions become 39 (Chapter 2's become 15). The bare row is then reached only through the
   derived form and through number specialisation.
5. **Why `lab = var` and not SML's `lab = pat`.** Nothing needs a pattern there: no Elm program
   writes one, and a copy needs only to rename. A variable keeps every record pattern
   irrefutable, which the book relies on: "the wildcard `_`, a variable and a record pattern cover
   every inhabitant" (static-core.tex:904) and "a pattern row cannot fail" (dynamic-core.tex:701).
   `lab = pat` would need FAIL rules for rows and new cases in the exhaustiveness and redundancy
   clauses, for no program.
6. **The variable of a pattern row.** Defined once, in Chapter 2: the `var` of `lab = var`, and
   for the derived row `lab`, the variable spelt as `lab`. The definitions of the variables bound by
   a pattern use it: syntax-core.tex:612-614 (on which `res:core-binding-site-distinct`,
   `res:core-no-shadowing` and `res:core-let-recursion` rest, and which are judged on the program
   as written) and appendix-derived-forms.tex:285-287 (the grouping of a `let`, which must hold
   whichever derived forms have been rewritten, lines 106-110). Saying only "the variables of its
   pattern rows" would drop `h` from `{ h }` as written.
7. **Rules.**
   - `r:s-patrow`: drop the premise `var = lab`; the row binds its own variable:
     `C ⊢ lab = var ⟨, patrow⟩ ⇒ ({var ↦ (τ, v)} ⟨+ VE⟩, {lab ↦ τ} ⟨+ ϱ⟩)`. Its comment
     (static-core.tex:748-750) no longer derives `var ∉ Dom VE` from distinct labels: that follows
     from `res:core-binding-site-distinct` in a program, and from fresh names in a copy.
   - `r:d-patrow-field`: `E, r ⊢ lab = var ⟨, patrow⟩ ⇒ {var ↦ r(lab)} ⟨+ VE⟩`, side condition
     `lab ∈ Dom r` as now; the comment "`lab` stands for the variable spelt as the label" goes.
   - The rule names stay, so test tags and site pages keep their addresses; still 194 rules.
8. **Number specialisation.** Its text gains a sentence and an example: a copy renames the
   variables a declaration binds, the variables of its pattern rows included, and never a label;
   the copy at Int of `{ h } = e`, that is of `{ h = h } = e`, is `{ h = h′ } = e′`. It also says
   that copies keep every property the syntactic restrictions give a program, except that a pattern
   row's variable need not be spelt as its label. (Copies are not written, so syntax-core.tex:582
   already does not judge them; the text of dynamic-core.tex:336-339 and 608-610 relies on those
   properties, so the sentence keeps them.) Step 10's issue 3, where copies stand in the bare
   syntax, is a separate point and is not settled here.
9. **Other text tied to the old row.** syntax-core.tex:226-229 (a label in a record pattern "is
   also a variable": true of the derived row only); syntax-core.tex:422-427, 587-590 and
   introduction.tex:101-105 (the lists of derived forms gain record-pattern punning);
   appendix-full-grammar.tex:151 and its header comment (lines 7-12), edited by hand since that
   file has no generated regions; the header comment of appendix-derived-forms.tex;
   appendix-standard-ml.tex, the Records row (pattern rows now follow SML's, with a variable for a
   pattern); static-core.tex:80-81, the notation `var = lab`, kept where it is used.
10. **Ruling.** Ambiguity-log entry **A99** (the log ends at A98), with every field the recent
   entries have: Origin (author decision, 2026-11-15, raised by number specialisation and by step
   10's issue 4); Construct; Question; Example; Implementation (Elm/JS needs no copies; eco lowers a
   destructuring binding to a root variable and field projections before it monomorphises);
   Notes say; Options ((a) a bare row `lab = var` with the label form derived, (b) copies through a
   fresh root and field selection, (c) a row form that only number specialisation produces, (d) no
   generalisation of `number` in destructuring bindings, which rejects programs Elm accepts);
   **Ruling** (a), decided by the author; **Reason** ("Why this is the principled route", below);
   Affects: syntax, static, dynamic.

What does not change: which programs are legal (the restriction removes exactly the alternative
the bare grammar adds), the type and value of every program that needs no copy at a non-default
assignment (with `var = lab` the new rules are the old ones), and every rule name.

## Work

Every step ends with the translator's unit tests, `scripts/verify.sh full` and `npm run test:all`
passing, and the baseline unchanged.

### 1. Tests first

Write the tests, confirm every CHECK value with Elm 0.19.1, run them on the four compilers, then
regenerate the translation (`Translate.elm`; `translate-check` fails otherwise) and run
`verify.sh full`: the tests the translator accepts today are translated and proved now, and the
others are recorded as refused. Names follow the recent rulings (StandardA93…, StandardA97…).

Tags: `elm-spec`, and the rules each program uses: `s-valbind-pat`, `d-valbind-pat`,
`s-atpat-record`, `d-atpat-record`, `s-patrow`, `d-patrow-field`, `s-dec-group`, `s-atexp-scon`,
`d-atexp-scon`, `sec:dynamic-core-numbers`, plus `s-pat-as`/`d-pat-as` and
`s-atpat-tuple`/`d-atpat-tuple` where used; the derived form's label once it exists. Every Float
result has a fractional part, so no CHECK depends on how a whole Float prints.

| Test (`tests/elm/src/`) | Program, in a `let` | Uses | CHECK (Elm 0.19.1) |
|---|---|---|---|
| StandardA99RecordPatternIntTest | `{ n } = { n = 7 }` | `n // 2` | `3`: only the copy at Int is used; the default copy is still made |
| StandardA99RecordPatternFloatTest | `{ n } = { n = 7 }` | `n / 2` | `3.5`: only the default copy |
| StandardA99RecordPatternBothTest | `{ n } = { n = 7 }` | `( n // 2, n / 2 )` | `(3,3.5)` |
| StandardA99RecordPatternTwoVariablesTest | `{ a, b } = { a = 5, b = 3 }` | `( a // 2, b / 2 )` and `( a / 2, b // 2 )` | `(2,1.5)` and `(2.5,1)`: copies at (Int, Float) and (Float, Int) |
| StandardA99RecordPatternSharedVariableTest | `{ a, b } = (\x -> { a = x, b = x }) 5` | `( a // 2, b / 2 )` | `(2,2.5)`: one variable for both fields |
| StandardA99RecordPatternFunctionTest | `{ h } = { h = \x -> x - 3 }`, in `testValue : ( Int, Float )` | `( h 5, h 2.5 )` | `(2,-0.5)`; the annotation fixes `5` at Int, which otherwise defaults to Float |
| StandardA99RecordPatternInTupleTest | `( { p }, q ) = ( { p = 9 }, 4 )` | `( p // q, p / q )` | `(2,2.25)` |
| StandardA99RecordPatternAsTest | `({ n } as r) = { n = 7 }` | `( n // 2, r.n / 2 )` | `(3,3.5)` |
| StandardA99RecordPatternDependentTest | `{ n } = { n = 7 }` and `m = n + 2` | `( m // 2, m / 2 )` | `(4,4.5)`: a second definition, copied too |
| StandardA99RecordPatternInTopCopyTest | top-level `v = let { n } = { n = 6 } in n` | `( v // 4, v / 4 )` | `(1,1.5)`: copies made from the outside in |
| StandardA99RecordPatternLambdaTest | `( f, k ) = ( \{ m } -> m + 1, 2 )` | `( f { m = k // 1 }, f { m = 2.5 } )` | `(3,3.5)`: a record pattern in a lambda of a copied declaration, not renamed |
| StandardA99RecordPatternRowRenameRejectedTest | `{ n = m } = { n = 1 }` | | compile error `UNFINISHED RECORD PATTERN` |
| StandardA99RecordPatternRowPunRejectedTest | `{ n = n } = { n = 1 }` | | the same |

The two rejection tests follow NameClashTwoLetBindingsOfOneNameTest: `-- COMPILE-ERROR:`, `-- CHECK:
-- UNFINISHED RECORD PATTERN -`, the tag `elm19-compile-error` beside `elm-spec`, and the new
restriction's tag. The values of SharedVariable, Lambda and the table's first eight rows were
checked with Elm 0.19.1 by the review; Dependent's is to be checked.

Expected today: the translator refuses Int, Both, TwoVariables, SharedVariable, Function,
InTuple, As, Dependent and InTopCopy (`number`, a record pattern copy); Float and Lambda translate.
Elm and Lamdera should pass every test. Any other outcome is recorded here as a finding before step
2.

### 2. The book

The `.tex` edits of the design: the grammar (syntax-core.tex, fig:core-grammar-patterns), the
variable of a pattern row and the bound variables, the identifier classes, the restriction, the
rules and their comments, the specialisation sentence, the passages of item 9, and A99 in the
ambiguity log. The derived-forms table is not regenerated here: its generator also writes Lean,
which changes in step 3. Lean and the translator are untouched, so verification still passes.

### 3. Lean and the translator: the new row

One step, since the translator's output and the generated Lean must agree.

- **Derived forms.** `DerivedForms.Table` gains the row, in a new pattern-row block
  (`DerivedForms.Term`, `ToLatex`, `ToLean`); `TRecordPat1` prints the bare row
  `{ lab = lab }`. Add the `% BEGIN/END GENERATED derived-forms:<Block>` markers and the block's
  heading to appendix-derived-forms.tex by hand (`Regions.replace` needs them,
  GenerateDerivedForms.elm:55-59), then run `GenerateDerivedForms.elm`, which writes the `.tex`,
  Derived.lean and Src/DerivedRows.lean. DerivedFormsTest's "the book's 14 rows" becomes 15.
- **Core syntax.** `PatRow.field (l : Lab) (rest : Option PatRow)` becomes `PatRow.field (l : Lab)
  (x : Var) (rest : Option PatRow)` (Syntax.lean), `BPatRow` likewise (Src/Bare.lean); `precord`
  (Derived.lean:168-172, hand-written) builds `.field l l rest`; Src/Derive.lean's `patRow` expands
  a label `l` to `.field l l`; `boundPatRow` (Objects.lean) returns `x`.
- **Source syntax unchanged.** `SPat.record` keeps its labels, because the parser (vendored eco,
  Parse/Pattern.elm:191-206) never produces a bare row. The new restriction joins those "trusted to
  the parser" (Src/Restrictions.lean header: ten instead of nine), and the header's counts change.
  `SPat.bound` (Src/Traverse.lean) stays correct: in the source syntax a row's variable is its
  label.
- **Rules and proofs.**
  - By hand: the dynamic rules (Rules.lean, RulesL.lean), Eval, Sound, Twins, SyntaxDecEq.
  - Regenerate rather than edit: Completeness.lean, NoStuck.lean and Forget.lean, with
    `scripts/gen_complete.py`, `gen_nostuck.py` and `gen_forget.py`.
  - The static semantics: Stat/Rules (`r:s-patrow` loses its premise), Infer, Annotated, the W and
    WD proofs under Stat/Complete, the refusal checks, the renaming files (RenameSyntax,
    NameRenCheck, NameRenInst, RenameSpec), CertPrint, CheckSound, MutualWalk, Src/SynSet and
    DerivesTo (`SynOK`).
  - CompareDerived.lean (outside StandardElmMech, so `grep -l PatRow StandardElmMech` misses it):
    `rPRow` and `bPRow` print the variable.
  - RuleCount checks rule labels only and needs no change.
  - About 60 files in all. Most changes are a constructor with one more argument; the real work is
    the static rule and the completeness proofs that use it.
- **Translator.** `Ir.PRecord` carries a label and a variable for each field (with an id);
  `Ir.patternBinders` returns the variables; Convert sets each variable to its label. FrontEnd and
  Classify match eco's `Src.PRecord` and do not change; Source.elm does not change, since `SPat`
  does not. ToLean prints `precord` with label and variable pairs (today `precord [labels]`,
  ToLean.elm:294-295). Then regenerate and verify: nothing is copied yet, so every count is
  unchanged.

### 4. Lean and the translator: copies rename the row's variable

Again together, since compare-e2e checks that the translator's specialisation and Lean's agree.

- Lean (Stat/Specialise.lean): `erPatRow` takes the assignment and renames each row's variable
  to `copyName x a`, keeping the label; `erAtPat` copies a record pattern like any other.
  `SpecError.recordPatternCopy`, `APatRow.firstLabel` and `firstLabel_congr` (RenameSpec.lean:418)
  go. `s_spec_record_pattern_copy` (Stat/SpecExamples.lean:646) states the copy instead of the
  error.
- Translator (Translate/Specialise.elm): `renamePattern` renames the variable of each `PRecord`
  field, and the refusal "a record pattern binding that needs a copy at Float" goes (its wording was
  wrong: the copy it could not make was the one at Int). TranslateTest.elm:270-271 expects that
  refusal; it now expects the translated Lean text, with `h$Int` as the variable of row `h`.
- Regenerate, `verify.sh full`: CovLambdaSetFunctionsDestructuredFromTuplesAndRecordsTest and the
  nine tests refused in step 1 translate and are proved end to end.
- Close step 10's issue 4 (step-10-end-to-end.md:1063-1068, and its table row at line 870) and
  lean-full-definition.md's B7 (lines 387-390) with a note pointing here.

### 5. Results and documents

- `plans/untranslated-tests.md` (also its stale note at lines 71-75 on LetNumberRecordDestructure)
  and the mechanisation report, with the counts.
- README test counts; the site (`runner/definition-data.js`, `site-data.js`,
  `mechanisation-data.js`, build, link audit). Rule pages come from the `.tex`, so `r:s-patrow` and
  `r:d-patrow-field` show the new rules.
- The book's preface counts (preface.tex:209-220: translated, legal, "287 of the 313"), then the
  typeset book: rebuild with the existing pipeline (definition/README.md) and an entry in
  definition/typeset/build-report.md (39 restrictions; pages as they come out).
- `commit.txt` for the user.

## Findings

1. **Step 1: the order of a destructuring binding's `number` variables.** StandardA99RecordPattern
   LambdaTest translated, but Lean's specialisation and the translator's disagreed (compare-e2e,
   and the test's `wcheck_` failed). `( f, k ) = …` quantifies one `number` variable from each of
   `f` and `k`, and the copies are named by an assignment in the declaration's canonical order
   (step 10, Choices, item 2: members in group order). Lean takes a destructuring binding's members
   in the order of its pattern's value environment, `APat.ve`, where `VE₁ + VE₂` lists `VE₂`'s
   first, so `k` before `f`; the translator took them in source order, so the copy Lean named
   `f$Float$Int` was the translator's `f$Int$Float`. No translated test had met it before: it needs
   a destructuring binding with two `number` variables and a copy that is not the default. The
   order only names copies, so neither is wrong; Lean's is the reference and its proofs rest on
   it, so the translator now reverses a pattern's binders (Translate/Infer.elm), its unit test
   that expected source order follows, and Choices, item 2, says so. Then `verify.sh full` passed:
   630 programs end to end, all agreeing.

## Why this is the principled route

- **Renaming acts on variables, never on labels.** A label is part of a type; a variable names a
  value in a scope. Today a record pattern row is both at once, so the Core is not closed under
  renaming its bound variables. Number specialisation needs that closure, as would any definition
  by substitution. Separating the two makes "the copies binding distinct new variables" true of
  every pattern, with no special case.
- **It is how The Definition of Standard ML does it** (Author Direction 7): a bare row pairs a
  label with what it binds, and punning is a derived form. Elm's `{ h }` is the same pun.
- **It changes no program's meaning.** The derived form gives `var = lab`, and then the new rules
  are the old ones; the restriction keeps the language accepted exactly Elm's. Only a specialised
  program, which no one writes, uses the new freedom.
- **It adds no evaluation and needs no equivalence argument.** Option 1 changes the shape of the
  program (a root binding and field selections) and needs an argument that the result means the
  same. Here a copy is the same declaration with new names, as for every other pattern.
- **It is the minimal general form.** A variable rather than SML's pattern keeps record patterns
  irrefutable, so exhaustiveness, redundancy and the FAIL-free pattern-row rule stay as they are.

## Out of scope

eco (its handling of these programs was examined on 2026-11-15 and is the eco project's business);
the Elm/JS divergence of `^` at Int (A43, A87), which the tests avoid; options 1 and 3; step 10's
issue 3.

## Review

An adversarial review of the first draft (2026-11-15) checked its claims against the sources and
ran the test programs on Elm 0.19.1. Corrections made:

1. The restriction let `{ n = n }` through, which Elm rejects; it now forbids every bare row in a
   program as written, and a rejection test covers `{ n = n }`. The hedge about when restrictions
   are judged went: syntax-core.tex:582-585 settles it.
2. The field accessor's equivalent form would have used a later derived form (B4); it is now
   written in bare syntax.
3. "The variables of its pattern rows" would have dropped `{ h }` as written from the bound
   variables; the variable of a pattern row is now defined for both forms.
4. The Function test did not need a copy at Int (`5` defaults to Float); `testValue` is annotated.
5. The steps could not each pass verification: the derived-form generator moved to step 3,
   translation of the new tests into step 1, and the Lean and translator changes are paired.
6. Minor: the comment on `r:s-patrow`; the claim about step 10's issue 3, dropped; the
   restrictions copies keep; the restriction trusted to the parser, with `SPat` unchanged; the
   generated proof files, `precord`, CompareDerived, `erPatRow`, `firstLabel_congr`; the
   translator's real touch points; hand edits to two `.tex` files; more passages and documents;
   rule tags and the compile-error conventions; three more tests (SharedVariable, Lambda,
   Dependent) and the second rejection test; Direction 7, the exact quotation, and A99's Origin
   field.
