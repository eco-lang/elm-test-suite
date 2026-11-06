# Elm test suite

End-to-end tests for Elm 0.19.x compilers. Each test is a real Elm program. The suite compiles it
with the compiler under test, runs it, and checks what it prints against the expected output
written in the program's comments. Some programs must instead be rejected, with a given error.

It runs the same tests through any number of compilers, one at a time or all together with a
report of where their outcomes differ. Out of the box it installs and runs:

| Name | Compiler |
|---|---|
| `elm-0.19.1` | Elm 0.19.1 (the default) |
| `elm-0.19.2` | Elm 0.19.2 |
| `elm-0.19.3` | Elm 0.19.3 |
| `lamdera-1.5.0` | Lamdera 1.5.0 (built on Elm 0.19.3) |

Adding another compiler (a new Elm release, a release candidate, a fork) is one entry in
`compilers.json`; see [Adding a compiler](#adding-a-compiler).

Most of the tests come from the end-to-end suite of eco, an Elm compiler with a native back end,
and pass under Elm 0.19.1. Two projects expect the correct behaviour where Elm 0.19.1 has a bug,
so they fail under 0.19.1 by design: `elm-bug-fixes` (bugs fixed in a later release; each test
passes from that release) and `elm-bugs` (bugs reported in open issues of the github.com/elm
repositories). eco's tests of the places where it deliberately behaves differently from Elm (64-bit `Int`, IEEE
`Float` comparisons, and so on) are not part of this suite.

## Requirements

- Node.js 20 or later. The case-mapping tests in `elm-conformance` were recorded with Unicode 17.0
  (Node 22.x and later); with an older Node the runner warns, and those tests may fail for that
  reason alone.
- pnpm. With Corepack (`corepack enable`), the version pinned in `package.json` is used.
- Linux (tested) or macOS (untested), on x64 or arm64: the platforms the compiler packages ship
  binaries for.

## Quick start

```sh
pnpm install            # fetches every compiler listed in package.json
pnpm test               # all tests, with the default compiler (Elm 0.19.1)
pnpm test:elm-0.19.3    # all tests, with one compiler
pnpm test:all           # all tests, with every compiler, then the comparison report
pnpm report             # the comparison report again, from the last results
pnpm compilers          # the compilers compilers.json knows
```

`pnpm test` takes under a minute and a half on a 12-core Linux machine. The first run of each compiler
is slower: it downloads the Elm packages the tests use.

The runner takes options after `--`:

```sh
pnpm test -- --compiler elm-0.19.2 --project elm-json      # one project
pnpm test -- --filter Dict,Set                             # tests whose path contains Dict or Set
pnpm test -- --project elm-core --record StringSliceTest   # print a test's output as CHECK lines
pnpm test:all -- --compilers elm-0.19.1,elm-0.19.3         # compare two compilers
```

| Option | Meaning |
|---|---|
| `--compiler <name>` | the compiler, a name from `compilers.json` (default: its `"default"`) |
| `--project <a,b>` | only these projects (directories of `tests/`) |
| `--filter <a,b>` | only tests whose `<project>/<Name>` contains one of these |
| `--jobs <n>` | programs run at once (default 8) |
| `--compile-jobs <n>` | compiles at once (default: the CPU count, at most 8) |
| `--timeout <s>` | seconds a program may run (default 60) |
| `--compile-timeout <s>` | seconds a compile may take (default 60); a compiler that hangs fails the test |
| `--compile-memory <MB>` | memory a compile may use (default 4096; Linux only); a compiler that exceeds it is killed and fails the test |
| `--record <Name>` | run one test (with exactly one `--project`) and print its output as CHECK lines |
| `--json <file>` | also write every test's outcome to a file |

A compiler that crashes can leave `elm-stuff` corrupt, and the next compile in it then reports a
CORRUPT CACHE (Elm 0.19.2, Lamdera) or hangs (Elm 0.19.3). So the runner clears `elm-stuff`
after a compile that crashed or was killed, and tries a compile that hangs, is killed or reports
a corrupt cache once more with an empty `elm-stuff`; the test fails only if the retry fails too.

`run-all.js` (`pnpm test:all`) takes the same options except `--compiler` and `--json`, plus
`--compilers <a,b>`. The exit status of `run.js` is 1 when a test failed.

## What a run does

For each test, the runner:

1. Compiles it in debug mode (the tests print with `Debug.log`) with
   `<command> make src/<Name>.elm --output=...`, in a copy of its project under
   `.work/<compiler>/<project>/`. Each compiler has its own `ELM_HOME`
   (`.work/<compiler>/elm-home`), so compilers never share a package cache. A package missing from
   it is first copied, source only, from another compiler's cache or from `~/.elm` if one has it,
   and the compiler builds its own artifacts; only packages nobody has are downloaded. Outputs are
   kept and reused until the test, its project or the compiler changes.
2. Runs the program in its own process: on Node for a compiler that writes JavaScript, directly for
   one that writes an executable. Most tests are `main = Html.text ...` programs that print with
   `Debug.log` while `main` is evaluated; a minimal DOM (`runner/dom.js`) lets them start on Node.
   Others are `Platform.worker` programs, or `Browser.element` programs whose view changes. Where
   elm/virtual-dom can hit a browser error (a read-only `type` property, an invalid attribute
   name, a node method given something that is not a node), the minimal DOM throws as a browser
   does, so a program that would crash in a browser crashes here too.
3. Passes the test if the program exits on its own within the timeout, with the expected exit
   status, and its output (stdout and stderr together) satisfies the CHECK lines.

Each program's output is kept in `.work/<compiler>/<project>/out/<Name>.log`.

`pnpm test:all` writes each compiler's outcomes to `.work/results/<compiler>.json`, then prints the
report and writes it to `.work/report.md`:

- each compiler's version and totals;
- each project's totals, one column per compiler;
- every test whose outcome is not the same under every compiler, with each compiler's outcome and
  the first line of the reason for each failure.

## The tests

`tests/` holds 13 Elm projects, each with its own `elm.json`:

| Project | Tests | What they cover |
|---|---|---|
| `elm` | 787 | the language and elm/core: every construct, closures, recursion, pattern matching, records, custom types, numbers, strings |
| `elm-core` | 114 | the elm/core modules, function by function |
| `elm-bytes` | 129 | elm/bytes encoders and decoders |
| `elm-json` | 37 | elm/json |
| `elm-parser` | 39 | elm/parser |
| `elm-regex` | 7 | elm/regex |
| `elm-time` | 4 | elm/time |
| `elm-url` | 3 | elm/url |
| `elm-html` | 3 | elm/html |
| `elm-conformance` | 36 | edge cases recorded from Elm on Node: Unicode and case mapping, JSON number and string formats, Float edge values, regex and URL encoding details |
| `elm-compile-errors` | 216 | programs the compiler must reject, checked by the title of the error report |
| `elm-bug-fixes` | 9 | bugs in Elm 0.19.1 fixed in a later official Elm release; each test expects the fixed behaviour and says in its comment which release fixed it |
| `elm-bugs` | 125 | bugs in Elm 0.19.1 and its packages reported in open GitHub issues; each test links its issue and expects the correct behaviour |

### elm-bugs and its issue triage

`tests/elm-bugs/issues.tsv` records a triage of every open issue (883, in November 2026) of the
github.com/elm repositories but `elm-lang.org` and `package.elm-lang.org`, one line each:

| Column | Meaning |
|---|---|
| `likelihood` | that the issue is a real bug in Elm 0.19.1 or its packages: `CERTAIN`, `LIKELY`, `WEAK`, `NOT_BUG` |
| `impact` | `HIGH`, `MEDIUM`, `LOW` |
| `e2e` | whether a test of this suite could show it: `yes`, `maybe`, `no` (needs a browser, network, the REPL, ...) |
| `outcome` | `REPRODUCED` (a test of `elm-bugs`), `FIXED` (a test of `elm-bug-fixes`), `NOT_REPRODUCED` (Elm 0.19.1 behaves correctly), `NOT_E2E`, `NOT_ATTEMPTED` (not a bug, or the correct behaviour is debatable) |
| `test` | the test (or tests, space-separated), for `REPRODUCED` and `FIXED` |
| `fixed_in` | the compilers under which that test passes |
| `note` | why |

A bug counts as fixed once a later official Elm release (not a fork such as Lamdera) fixes it: its
test then moves from `elm-bugs` to `elm-bug-fixes`, its comment says which release fixed it, and
its outcome becomes `FIXED`. A bug fixed only in a fork stays in `elm-bugs`.

Some compiler bugs in `elm-bugs` make the compiler loop while its memory grows: the runner kills a
compile at `--compile-memory` (4096 MB), so they fail within seconds.

A test is a module in `src/` with a top-level `main` (or a `-- COMPILE-ERROR:` line). Modules
without either are helpers that tests import.

### Writing a test

The expected behaviour is written in line comments that start a line:

```elm
module ListReverseTest exposing (main)

{-| List.reverse of a short list. -}

-- CHECK: reversed: [3,2,1]

import Html exposing (text)


main =
    let
        _ =
            Debug.log "reversed" (List.reverse [ 1, 2, 3 ])
    in
    text "done"
```

| Directive | Meaning |
|---|---|
| `-- CHECK: <text>` | the output contains `<text>` |
| `-- CHECK-NOT: <text>` | the output does not contain `<text>` |
| `-- CHECK-NEXT: <text>` | the line after the previous match contains `<text>` |
| `-- CHECK-SAME: <text>` | the line of the previous match contains `<text>` after it |
| `-- CHECK-DAG: <text>`, `-- CHECK-LABEL: <text>` | as `CHECK` |
| `{{regex}}` inside a pattern | a regular expression, e.g. `-- CHECK: zone: "{{Offset (60\|120)}}"` |
| `-- EXIT: <n>` | the expected exit status (default 0), e.g. 1 for a program that crashes |
| `-- STDIN: <text>` | text fed to stdin (`\n`, `\t`, `\\` unescaped; lines concatenate) |
| `-- ENV: NAME=VALUE`, `-- UNSETENV: NAME` | the program's environment |
| `-- FLAGS: <json>` | the flags passed to `init` |
| `-- COMPILE-ERROR: <what>` | the compiler must reject the program; the CHECK lines (the report title, such as `-- CHECK: -- TYPE MISMATCH -`) are matched against its output |
| `-- LINUX-ONLY: <reason>` | skipped on other hosts |

CHECK patterns are matched in any order, each against the whole output. Other lines that look
like directives (`CHECK-MLIR`, `TEXT-MLIR`, `SKIP-AOT`) belong to eco's own harness and are ignored.

To record a new test's expected output from a compiler you trust, give it no CHECK lines, then
`pnpm test -- --project <p> --record <Name>` and paste the printed lines into the file.

A port module with an outgoing port `echoOut` and an incoming port `echoIn` gets each value sent
out through `echoOut` back through `echoIn`, to test ports end to end.

## Adding a compiler

A compiler is an entry of `compilers.json`:

```json
"elm-0.19.3": {
  "description": "Elm 0.19.3, from the npm package elm@0.19.3-0",
  "command": "node_modules/elm-0.19.3/bin/elm",
  "target": "js"
}
```

| Field | Meaning |
|---|---|
| `command` | the compiler executable: a path relative to this directory, an absolute path, or a name on `PATH` |
| `args` | the arguments before the source file (default `["make"]`) |
| `target` | `"js"` if `--output=Name.js` writes JavaScript, `"native"` if `--output=Name` writes an executable |
| `env` | extra environment variables for the compiler (optional) |
| `elmVersion` | the `"elm-version"` written into each test project's `elm.json` (optional; see below) |
| `description` | free text for reports |

The compiler must accept `<args> src/Name.elm --output=<file>` the way `elm make` does, and
`--version`. An application's `elm.json` must name the exact Elm version compiling it, so the runner
writes the compiler's version into its copy of each project's `elm.json`: by default the output of
`--version` when that is an Elm version (`0.19.x`). A compiler that reports a version of its own
(eco says `0.2.0`) leaves `elm.json` as it is, saying `0.19.1`; set `elmVersion` to change that. Then `pnpm test -- --compiler <name>` runs it, and `pnpm test:all` includes it. A
`"test:<name>"` script in `package.json` is a convenient extra.

### A release published on npm (for example Elm 0.19.4)

1. Find the package version: `npm view elm versions` (Elm 0.19.3 is `0.19.3-0`).
2. Add it to `devDependencies` under its own alias, so several versions install side by side:

   ```json
   "elm-0.19.4": "npm:elm@0.19.4-0"
   ```

3. `pnpm install`.
4. Add the entry to `compilers.json`, with `"command": "node_modules/elm-0.19.4/bin/elm"`.

A new Lamdera release is the same, with `npm view lamdera versions` (Lamdera 1.5.0 is
`0.19.3-1.5.0`) and `"command": "node_modules/lamdera-<version>/bin/lamdera"`.

pnpm runs a package's install script only when `pnpm-workspace.yaml` allows it; `elm` and
`lamdera` are allowed. A compiler from a package with another name needs a line there too.

### A release candidate or any other binary

Put the binary anywhere and point `command` at it. For example, for an Elm 0.19.4 release
candidate downloaded to `compilers/elm-0.19.4-rc1/elm` (`compilers/` is a suggestion; it is not
tracked):

```json
"elm-0.19.4-rc1": {
  "description": "Elm 0.19.4 release candidate 1",
  "command": "compilers/elm-0.19.4-rc1/elm",
  "target": "js"
}
```

### eco

eco 0.2.0 compiles to JavaScript for `--output=Name.js` and to
a native executable otherwise, so it can be added twice, once per back end. With `eco` installed on
`PATH`:

```json
"eco-0.2.0-js": {
  "description": "eco 0.2.0, JavaScript back end",
  "command": "eco",
  "target": "js"
},
"eco-0.2.0-native": {
  "description": "eco 0.2.0, native back end",
  "command": "eco",
  "target": "native"
}
```

On a native target, tests that need a JavaScript host (`-- FLAGS:`, or a port module) are
skipped.

## Layout

```
compilers.json        the compilers the runner knows
package.json          the compiler packages (pnpm) and the scripts
pnpm-workspace.yaml   which packages may run install scripts
runner/run.js         runs the suite with one compiler
runner/run-all.js     runs it with several and writes the comparison report
runner/directives.js  reads a test's directives and checks its output
runner/dom.js         the minimal DOM that lets Html programs start on Node
tests/<project>/      the test projects (elm.json and src/)
.work/                compiled programs, logs, package caches and results (not tracked)
```

## License

BSD 3-Clause; see [LICENSE](LICENSE).
