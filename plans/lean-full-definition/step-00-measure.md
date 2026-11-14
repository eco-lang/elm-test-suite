# Step 0: measure

Part of [the plan](../lean-full-definition.md). Conventions: [conventions.md](conventions.md).
Size: small. Needs: nothing. Status: **done 2026-11-11** (see "Done" at the end).

## Goal

Replace the hand-made count of the plan's "Test inventory" by a count the translator produces, and
record the baseline that every later step is measured against. Three deliverables:

1. A translator option `--report-all-refusals FILE` that writes, for every `elm-spec` test, every
   refusal the translator meets when it lifts each refusal in turn (not only the one of lowest rank
   that the manifest records today).
2. A script that turns that report, with a short file of hand annotations (needs the translator
   cannot see), into the plan's table "Part I gains", and checks it against the manifest.
3. A script that measures the build's memory as [conventions.md](conventions.md) defines it, and the
   recorded baseline numbers.

No Lean file changes in this step.

## Prerequisites

- The repository as of 2026-11-11: `Translate.elm --check` reports "elm-spec tests: 939,
  translated: 491" and up to date; `lake exe run-examples` prints
  `Total: 1487 checks, 1487 agree, 0 diverge (0 known); 1162 theorems by decide +kernel.`
- The review inputs that motivate this step: finding P1-8 (directive refusals in
  `Translate/Directives.elm` hide every refusal of `Convert.elm`, so lifting Convert's `effects`
  alone measures nothing for FlagsRecordTest and the CHECK-family tests) and F-20 (no option lifts
  refusals; once lifted, `Infer.elm` gives `unknown-type` for `Cmd`, `Task`, `Program`).

## Lean definitions

None.

## Theorems

None.

## Translator changes

### The option

`definition/tools/src/Translate.elm` gains a keyword option beside `--check`:

```
node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm \
    --report-all-refusals definition/mechanisation/refusal-report.json
```

With the option the translator writes only `FILE` (and still prints its summary); it writes no Lean
file and no manifest. Without it nothing changes. The config becomes

```elm
type alias Options = { check : Bool, reportAll : Maybe String }

config : Program.Config Options
config =
    Program.config
        |> Program.add
            (OptionsParser.build Options
                |> OptionsParser.with (Option.flag "check")
                |> OptionsParser.with (Option.optionalKeywordArg "report-all-refusals")
            )
```

### Lifting each refusal in turn

`Translate/Pipeline.elm` gains

```elm
type Stage = StDirectives | StSize | StParse | StConvert | StInfer | StSpecialise

type alias Found = { stage : Stage, reason : String, at : Maybe String, detail : Maybe String }

{-| Every refusal met when each is lifted in turn, in pipeline order; [] for a test that
translates. The first element, if any, is the refusal `translate` reports. -}
translateAll : { project : String, name : String, defName : String } -> String -> Directives -> List Found
```

The stages, in order, and what "lifting" means at each:

| Stage | What it records | How the next stage still runs |
|-------|-----------------|-------------------------------|
| directives | every entry of `Directives.read`'s problem list (today only `List.head problems` is kept: expose the whole list as `refusals : List String`) | continue, except for `compile-error`, where the report stops (those tests are step 7's business) |
| size | `construct:large-program` (source over 20,000 characters), `construct:large-computation` (named tests) | continue |
| parse | `parse` | stop: there is no tree |
| convert | every `Problem` in `st9.problems` of `Convert.convert`, sorted as today by (rank, row, column), not only `best` | `Convert.convertLenient` returns the `TestProgram` it built whatever the problems (ports and effect values dropped, `main` with no checks if its shape is refused) |
| infer | the `Err` of `Infer.infer`: `type` with its message as detail, or `unknown-type:<name>` | stop on error (inference stops at its first error) |
| specialise | `basis:*` or `number` from `Specialise.specialise` | end |

`Convert.elm` gains `convertLenient : String -> Directives -> File -> ( TestProgram, List Problem )`
(the body of `convert` with the final `case best of` replaced by returning both); `convert` becomes
`convertLenient` followed by today's choice of `best`, so its behaviour does not change.

For a refusal of stage convert the reason string is the code exactly as today (`import:Dict`,
`effects`, `basis:Result.Ok`, `checks:unmatched:y`, ...).

### Report format

`definition/mechanisation/refusal-report.json`, written in test order (project, then name):

```json
{
  "generatedBy": "definition/tools/src/Translate.elm --report-all-refusals",
  "toolsSha256": "<sha256 of definition/tools/src, as in the manifest>",
  "tests": [
    { "project": "elm", "name": "AccessorFunctionFieldInListTest", "status": "translated",
      "refusals": [] },
    { "project": "elm", "name": "FlagsRecordTest", "status": "refused",
      "refusals": [
        { "stage": "directives", "reason": "effects" },
        { "stage": "convert", "reason": "effects", "at": "12:1" },
        { "stage": "infer", "reason": "unknown-type:Platform.Program" } ],
      "uses": ["Platform"], "localModules": [], "worker": true, "ports": false },
    ...
  ]
}
```

`uses` lists the module names of every qualified reference and every import other than the default
imports and `Html` (the `uses:` column of the review's inventory). `localModules` lists the imports
that name a file `tests/<project>/src/<Module>.elm`. `worker` is true when `main`'s right-hand side
applies `Platform.worker`; `ports` when the module is a `port module`. These four fields are
computed from the parsed tree, cheaply, by a new function `Convert.facts : File -> Facts`.

### The table script

A new Node script, `runner/part1-inventory.js`:

```
node runner/part1-inventory.js definition/mechanisation/refusal-report.json \
    definition/mechanisation/refusal-annotations.json
```

It reads the report, the manifest and a hand-written file of annotations, checks consistency, and
prints the Markdown of the plan's table "Part I gains" (step, count, names) followed by the list of
tests that stay out, with their reason.

`definition/mechanisation/refusal-annotations.json` holds what the translator cannot see:

```json
{
  "annotations": [
    { "name": "TaskAttemptErrorTest", "needs": ["Ok/Err through the text of Task.attempt (D3)"] },
    { "name": "TaskOnErrorCascadeTest", "needs": ["Ok/Err through the text of Task.attempt (D3)"] },
    { "name": "CoreIssue1123NestedCmdBatchStackOverflowTest", "out": "size: Cmd.batch nested 100000 deep (finding T2)" },
    { "name": "StandardA81SleepBeyond32BitsTest", "partial": "positive check only (finding T1)" },
    { "name": "CompilerIssue2019AliasOfTypeVariableTest", "out": "group A: a check the encoding cannot express" },
    { "name": "PortEchoArrayStringTest", "out": "library: Array.fromList, Array.empty" },
    { "name": "PortEchoJsonValueTest", "out": "library: Json.Encode.encode" },
    { "name": "StandardA92BytesPortTest", "out": "library: Bytes.Encode, Bytes.Decode, List.map, Maybe.withDefault" }
  ]
}
```

Classification (first matching row wins; `R` is the set of reasons of the test's refusals, with
`checks:unmatched:*` read as `checks:unmatched`):

| Step | Rule |
|-----:|------|
| out | annotated `out`, or `R` meets {`parse`, `number`, `construct:large-*`} |
| library | `R` meets `import:<m>` for a module of elm/core outside the default imports and `Html` (Array, Dict, Bitwise, ...), or `basis:<m>.<x>` other than `Result.Ok`, `Result.Err`, `Basics.logBase` |
| 2 | `R` ⊆ {`basis:Result.Ok`, `basis:Result.Err`, `basis:Basics.logBase`} |
| 3 | not a worker, and `R` ⊆ {`import:<local module>`, `construct:record-alias-constructor`, `construct:main-shape`, `effects` (port module), `checks:unmatched`, `checks:unlabelled`, `checks:regex`} |
| 5 | a worker whose checks are all positive (`R` without `checks:check-not` and without `checks:directive:CHECK-NEXT` on a CHECK-NOT test), or annotated `partial` |
| 6 | a worker with a `CHECK-NOT` the book supports |

The script fails (exit 1) when: the report has not 939 entries; a test translated in the manifest
has refusals in the report; the first refusal of a refused test differs from the manifest's
`reason`; a test of the report is not classified; an annotation names no test.

### Translator tests

Add to `definition/tools/tests/TranslateTest.elm`, group "all refusals":

- "a FLAGS directive no longer hides Convert's refusals": a source with `-- FLAGS:` and a port
  module gives `[directives:effects, convert:effects, ...]`.
- "a compile-error test reports only its directive".
- "the first refusal is the one translate reports" (property over the existing refusal examples of
  the file: for each, `List.head (translateAll ...)` equals the `Refused` of `translate`).
- "a translated test reports no refusal".

## Measurement script

`definition/mechanisation/standard-elm-mech/scripts/measure-build.sh`, run from the project folder.
It copies the project to a fresh directory and never deletes inside the repository; every
destructive command uses a literal path or `${COPY:?}`:

```bash
#!/usr/bin/env bash
set -euo pipefail
COPY=$(mktemp -d "${TMPDIR:-/tmp}/sem-measure.XXXXXX")
cp -r . "${COPY:?}/proj"
rm -rf "${COPY:?}/proj/.lake/build"
cd "${COPY:?}/proj"
# sample the summed PSS of all lean processes every 0.5 s while the build runs
( peak=0; while sleep 0.5; do
    s=0; for p in $(pgrep -x lean || true); do
      v=$(awk '/^Pss:/{print $2}' "/proc/$p/smaps_rollup" 2>/dev/null || echo 0); s=$((s+v)); done
    [ "$s" -gt "$peak" ] && peak=$s && echo "$peak" > "${COPY:?}/pss-peak"
  done ) & SAMPLER=$!
/usr/bin/time -v lake build 2> "${COPY:?}/time.txt" >/dev/null
kill "$SAMPLER"
echo "max single-process RSS (KB): $(awk -F': ' '/Maximum resident set size/{print $2}' "${COPY:?}/time.txt")"
echo "peak summed PSS (KB): $(cat "${COPY:?}/pss-peak")"
for f in StandardElmMech/Generated/Checks*.lean; do
  /usr/bin/time -f "$f %M KB %e s" lake env lean "$f" 2>&1 >/dev/null | tail -1
done
```

`/usr/bin/time -v lake build` reports the maximum resident set of the largest child, which is one
`lean` process. The per-shard lines locate a shard that breaks the budget.

## Tests gained

None.

## Acceptance

Run from the repository root:

```
node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --report-all-refusals definition/mechanisation/refusal-report.json
node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check
(cd definition/tools && ../../site/node_modules/.bin/elm-test --compiler ../../site/node_modules/.bin/elm)
node runner/part1-inventory.js definition/mechanisation/refusal-report.json definition/mechanisation/refusal-annotations.json
export PATH=$HOME/.elan/bin:$PATH
(cd definition/mechanisation/standard-elm-mech && bash scripts/measure-build.sh)
(cd definition/mechanisation/standard-elm-mech && lake exe run-examples)
```

Expected:

- The translator prints `elm-spec tests: 939, translated: 491` with the same reason counts as
  today; `--check` says the Lean translations are up to date (the option writes no Lean file).
- The report has 939 entries: 491 translated with `refusals: []`, 311 `compile-error` with one
  refusal each, 137 others.
- The script exits 0 and prints the table of the plan, with these rows (the counts the third review
  established, which this step confirms or corrects):

  | Step | Tests |
  |-----:|------:|
  | 2 | 7 (CaseFanOutShadowTest, CaseResultTest, ResultErrTest, ResultOkTest, StandardA97NeverErrBranchTest, StandardA97SelfOnlyTypeTest, LetNumberLogBaseTest) |
  | 3 | 42: 9 user modules, 5 record aliases, 2 views (HelloTest, CharCasePredicateTest), 15 port views, 9 group E, 2 regex |
  | 5 | 34 workers + StandardA81SleepBeyond32BitsTest's positive check |
  | 6 | 3 (PortIncomingRejectTest, TaskOnErrorSucceedTest, StandardA88PortNonFiniteTest) |
  | library | 29 `basis:*` (the 36 less the 7 of step 2), 5 `import:*` (Array 3, Dict, Bitwise), 3 workers (PortEchoArrayStringTest, PortEchoJsonValueTest, StandardA92BytesPortTest) |
  | out | CompilerIssue2019AliasOfTypeVariableTest, CoreIssue1123NestedCmdBatchStackOverflowTest, 5 `construct:large-program`, 1 `construct:large-computation`, 1 `construct:large-type`, 3 `parse`, 1 `number` |

  Totals: 87 + 1 gains; 137 refused non-compile-error tests in all.
- The measurement prints a maximum single-process RSS of about 6,300,000 KB and a peak summed PSS
  of about 11,100,000 KB (the feasibility review measured 6,297,084 KB and 11.1 GB on a 28-core
  machine; the numbers vary with the machine and are recorded, not required).
- `run-examples` prints `Total: 1487 checks, 1487 agree, 0 diverge (0 known); 1162 theorems by
  decide +kernel.`

Then, per [conventions.md](conventions.md) ("Reports and the site"): replace the plan's table "Part I
gains" and its total by the script's output (with any difference from the table above explained in
the plan's status line), add an "Update" block to `definition/mechanisation/mechanisation-report.md`
with the baseline (tests 491 of 939, checks 1487, kernel theorems 1162, native theorems 13 shard
theorems plus the hand ones, single-process peak, PSS peak), and mark this specification done.

## Risks and fallbacks

- `convertLenient` may build a program that `Infer.infer` cannot read (a port name used as a
  value, a `main` without a `let`). Inference then reports `type` or `unknown-type:*`; that is a
  finding of the report, not a failure of the option. If inference crashes (an Elm runtime error
  in `Debug.todo`), the stage records `infer: crashed` and the report goes on.
- The memory sampler may miss a short peak between samples; 0.5 s is the conventions' figure. The
  single-process figure from `time -v` is exact.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

- **The library count.** The plan's "Test inventory" says the library tests are "36 `basis:*` and
  5 `import:*`". Seven of the 36 `basis:*` refusals (Ok, Err, logBase) are step 2's gains, so 29
  `basis:*` tests remain for [core-library.md](../core-library.md), and three more library tests are
  workers refused today as `effects`. The table this step produces should say so.
- **Workers whose needs come from the basis texts.** TaskAttemptErrorTest and
  TaskOnErrorCascadeTest need `Ok` and `Err` through the text of `Task.attempt`, which no dry run of
  the translator can see. The annotations file records this; after step 2 the need is met.

## Done (2026-11-11)

Implemented as specified, with these differences, each forced by what the code does:

- **A size refusal ends a test's report**, as does a conversion refusal `construct:large-*`. The
  specification let the report continue to parsing and inference; on the programs of a compiler's
  limits (EtaExpandSeventeenArgumentAliasTest, the wide records) the converter's or the
  inference's recursion overflows the JavaScript stack, which elm-pages reports as nothing at all
  (the script ends with status 0 and no file).
- **`Convert.facts` reads the qualified references from the source text** (a regular expression
  over `Module.name`), and the imports and the port header from the tree. The report records
  `uses`, `localModules`, `worker` and `ports` as specified.
- **The inventory script's reasons.** A refusal of inference or specialisation that follows a
  refusal of an earlier stage is a consequence of the lenient conversion and does not count. A
  `basis:<M>.<x>` refusal for a module `M` the test imports from its own sources, and a
  `basis:Basics.<x>` refusal in a test with local modules or ports (a name conversion looked for in
  `Basics` because it could not resolve it), are artefacts of the module form. An import of a
  module whose dynamic interface the book makes empty (`Array`, `Bytes`, `Json.*`, `VirtualDom`)
  is a library need only when the test uses one of its values. The values of `Basics` written in
  Elm (`never` as well as `logBase`) are step 2's (D3): StandardA97NeverErrBranchTest needs `never`.

Results:

- `Translate.elm --report-all-refusals definition/mechanisation/refusal-report.json`: 939
  entries, 491 translated with no refusal, 311 compile-error with one each, 137 others.
- `node runner/part1-inventory.js ...`: exits 0 and prints steps 2: 7, 3: 42, 5: 35 (34 workers
  and StandardA81SleepBeyond32BitsTest's positive check), 6: 3, library 37 (29 `basis:*`, 5
  `import:*`, 3 workers), out 13: Part I gains 87, as the plan's table says.
- Translator unit tests: 67 pass (13 new). `--check`: up to date; the Lean translations are
  unchanged (only the manifest's `toolsSha256` changed).
- `scripts/measure-build.sh`: maximum single-process RSS 6,278,552 KB (shard Elm01: 6,357,412 KB
  checked alone, nearly all of it AppendTypeSplitTest), peak summed PSS 10,968,879 KB, clean build
  1:24.55, on a 28-core machine. Every other shard: 1.8 to 3.8 GB.
- `lake exe run-examples`: `Total: 1487 checks, 1487 agree, 0 diverge (0 known); 1162 theorems by
  decide +kernel.`
