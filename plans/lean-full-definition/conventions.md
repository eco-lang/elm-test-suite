# Conventions for every step of the Lean plan

Part of [the plan](../lean-full-definition.md). Paths are relative to the repository root unless
they start with `StandardElmMech/`, which is
`definition/mechanisation/standard-elm-mech/StandardElmMech/`.

## Tools

- Lean 4.35.0 (`lean-toolchain`), Lake, from elan: `export PATH=$HOME/.elan/bin:$PATH`.
- No Lean dependencies (`lake-manifest.json` has `"packages": []`): no Mathlib, no Batteries.
  Core Lean provides `List`, `Array`, `Rat` (reduces under `decide +kernel`), `List.Perm`,
  `String`, `Char`, `Float` (IEEE binary64, reduced by the kernel for `+`, `-`, `*`, `/`,
  comparison; the C library functions `Float.floor`, `sin`, `pow`, ... only by `native_decide`).
- The translator is Elm, run by elm-pages from the repository root:
  `site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm` (writes),
  `... --check` (reports whether the Generated files are up to date). Its unit tests:
  `cd definition/tools && ../../site/node_modules/.bin/elm-test --compiler ../../site/node_modules/.bin/elm`.

## Files and namespaces

The existing files stay where they are. New Lean files go in subdirectories by part of the book,
each with its own namespace under `StandardElm`:

| Directory | Namespace | Contents | Steps |
|-----------|-----------|----------|-------|
| `StandardElmMech/` (top level) | `StandardElm` | Chapter 6, APPLY, the oracle evaluator, the logged Core relations, check statements | 1 |
| `StandardElmMech/Mod/` | `StandardElm.Mod` | Chapter 7, `ME0`, the harness, Chapter 9's `r:p-dyn-*` | 2, 3 |
| `StandardElmMech/Eff/` | `StandardElm.Eff` | Chapter 8: payload types, boundary values, Enc, Dec, task reduction, messages | 4 |
| `StandardElmMech/Prog/` | `StandardElm.Prog` | Chapter 9's executions, the scheduler, the host model, invariants | 5, 6 |
| `StandardElmMech/Src/` | `StandardElm.Src` | Source syntax, derived forms, the syntactic restrictions | 8 |
| `StandardElmMech/Stat/` | `StandardElm.Stat` | Chapters 4, 5 and 9 (static), Appendix C, annotated phrases, the checker, inference, the pattern decider, completeness | 9, 10, 11 |
| `StandardElmMech/Generated/` | `StandardElm` | Written by the translator only | all |
| `StandardElmMech/Certs/` | `StandardElm.Stat` | Written by `lake exe certify` only: the annotated phrases (typing certificates) that step 9's unverified inference produces, which the kernel then checks | 9, 10 |

`StandardElmMech.lean` imports every file. A file that does not need the `Lean` meta library does
not import `Lean` (it costs every importing process about 1.6 GB); only `Theorems.lean` and the
files that define commands such as `#kernel_checks` import it.

## Names

- **Rules.** One constructor per rule of the book, named from its label: `r:dm-module` is
  `r_dm_module`, `r:e-task-prim` is `r_e_task_prim`, `r:s-atexp-scon` is `r_s_atexp_scon`. The
  docstring of the constructor is the label (`/-- r:dm-module -/`). Auxiliary constructors that
  are not rules (options, sequences) are named `opt_none`, `opt_some`, `seq_nil`, `seq_cons`.
- **Logged relations** (decision D4): the book's relation name with `L` appended
  (`EvalExp` and `EvalExpL`), constructors with `_l` appended (`r_d_exp_app_l`).
- **Evaluators:** `ev` plus the judgement (`evExp`, `evModule`, `stepConfig`). **Soundness:**
  `<evaluator>_sound`; **completeness:** `<evaluator>_complete`.
- **Generated theorems.** One theorem per test program, the conjunction of its checks, named
  `t_<project>_<TestName>` (`t_elm_core_FloatNaNTest`), so that a theorem's name does not change
  when another test is added or refused. The positional names `kc_<Shard>_<n>` are retired in
  step 1.
- **Rulings:** a theorem about ruling A*n* has `a<n>` in its name (`a25_no_value`), so the site
  links it to the ruling.

## Proofs

- No `sorry`, no `axiom`. `scripts/check-axioms.lean` (step 1 adds it) runs `#print axioms` on
  every theorem and fails if any uses an axiom other than `propext`, `Classical.choice`,
  `Quot.sound`, and, for theorems marked `[native]`, the axioms `native_decide` introduces
  (`Lean.ofReduceBool`, and `Lean.trustCompiler` where the toolchain adds it).
- Prefer `decide +kernel`. Use `native_decide` only where the kernel cannot reduce (the C
  library's float functions, printing floats, regex matching) or the memory budget is broken, and
  record the test in the step's list of native theorems.
- Evaluators are defined by structural recursion on fuel (`Nat`), never by well-founded
  recursion, which the kernel does not reduce.

## Data the translator writes

- Each translated test is one Lean `def` in a shard `Generated/<Shard><nn>.lean` of at most 40
  programs, with a docstring naming its source file. The shards' checks are in
  `Generated/Checks<Shard><nn>.lean`.
- The manifest `definition/mechanisation/translation-manifest.json` has one entry per `elm-spec`
  test: `project`, `name`, `status` (`translated` or `refused`), `reason` (when refused),
  `shard`, `def`, `checks`, and from step 3 `sources`: a list of `{path, sha256}`, one per module
  of the program, so that a change to a helper module marks the translation out of date.
- From step 0, the option `--report-all-refusals FILE` writes, for every test, every refusal the
  translator meets when it lifts each refusal in turn (step 0's specification).

## Acceptance commands

Run from the repository root, in this order. Each step's specification states the numbers its
outputs must show.

```
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check
(cd definition/tools && ../../site/node_modules/.bin/elm-test --compiler ../../site/node_modules/.bin/elm)
export PATH=$HOME/.elan/bin:$PATH
(cd definition/mechanisation/standard-elm-mech && lake build && lake exe run-examples)
(cd definition/mechanisation/standard-elm-mech && lake env lean scripts/check-axioms.lean)
pnpm test:all && node runner/check-baseline.js
node runner/definition-data.js && node runner/site-data.js && node runner/mechanisation-data.js
(cd site && npm run build)
```

`lake exe run-examples` prints `Total: N checks, N agree, 0 diverge (0 known); K theorems by
decide +kernel.` until step 1, and from step 1, when theorems become one per program, `Total: N
checks, N agree, 0 diverge (0 known); K checks proved by the kernel, M by native_decide.` Neither
N nor K may fall in any step, except where a specification names the checks that change and why.

## Memory budget

Measured on a clean build (`rm -rf .lake/build` in a copy of the project, never in the
repository): no single `lean` process above 6.5 GB of resident set size
(`/usr/bin/time -v lake build`, "Maximum resident set size"), and the sum over concurrent `lean`
processes of the proportional set size (`Pss:` of `/proc/<pid>/smaps_rollup`, sampled every 0.5 s)
under 12 GB. A test that breaks the budget is proved by `native_decide` only, or refused with the
reason `construct:large-*`, and listed in the step's report. Smaller shards do not lower the
single-test peak.

## Reports and the site, after every step

- `definition/mechanisation/mechanisation-report.md`: a dated "Update" block at the top, with the
  counts (tests translated of 939, checks, kernel theorems, native theorems), what the step added,
  and any finding.
- `definition/mechanisation/standard-elm-mech/README.md`: the Files table (one row per new file)
  and "What the theorems say", including the trust tags of the plan.
- `README.md` (the section on the Lean translation): the count "N of the 939 today".
- `definition/tex/preface.tex`: the sentence that counts the translated test programs and names
  what is encoded; then rebuild the PDF (`definition/typeset/build-report.md` has the commands)
  and record the rebuild there.
- `runner/mechanisation-data.js`: rule pages link to constructors by the pattern
  `r_(d|dm|e|p|s|sm)_<slug>` (today it matches `r_d_` only); the rule count covers every rules
  file; new files get a description from the Files table.
- The site: `node runner/definition-data.js && node runner/site-data.js &&
  node runner/mechanisation-data.js && (cd site && npm run build)`, then the link audit, with 0
  problems.
- The plan's status line, and the step's specification marked done with the date.
