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
and pass under Elm 0.19.1. The tests tagged `elm19-bug-fix` (bugs fixed in a later release; each
test passes from that release) and `elm19-bug` (bugs reported in open issues of the github.com/elm
repositories) expect the correct behaviour where Elm 0.19.1 has a bug, so they fail under 0.19.1 by
design; see [Tags](#tags). eco's tests of the places where it deliberately behaves differently from Elm (64-bit `Int`, IEEE
`Float` comparisons, and so on) are not part of this suite.

## Requirements

- Node.js 20 or later. The case-mapping tests (those with `-- UNICODE: 17.0`) were recorded with
  Unicode 17.0 (Node 22.x and later); with another Node the runner warns, and those tests may fail
  for that reason alone.
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
| `--no-cache` | neither read nor write the result cache |
| `--refresh` | run every test, renew the result cache, and report each result that differs from the cached one |

A compiler that crashes can leave `elm-stuff` corrupt, and the next compile in it then reports a
CORRUPT CACHE (Elm 0.19.2, Lamdera) or hangs (Elm 0.19.3). So the runner clears `elm-stuff`
after a compile that crashed or was killed, and tries a compile that hangs, is killed or reports
a corrupt cache once more with an empty `elm-stuff`; the test fails only if the retry fails too.

`run-all.js` (`pnpm test:all`) takes the same options except `--compiler` and `--json`, plus
`--compilers <a,b>`. The exit status of `run.js` is 1 when a test failed.

### The result cache

A released compiler does not change, nor does a test nobody edits, so the runner keeps each test's
result in `.work/result-cache/<compiler>/<key>.json` and takes it from there on the next run, without
compiling or running the test. The key is a hash of everything the result depends on: the
compiler's executable, the runner (`run.js`, `directives.js`, `dom.js`), Node's version, the
platform and runner image, the time and memory limits, the project's `elm.json`, and the source of
the test and of every module of its project it imports. Edit one test and only it runs again;
edit a helper module and only the tests that import it do.

Every result of a test with `-- NO-CACHE:` or `-- STDIN-DELAY-MS:`, or whose source (or a module it
imports) uses `Time.now`, `Time.every`, `Process.sleep` or `Random.generate`, is never kept. A result
that may be an accident of the moment (a compile that crashed, timed out or ran out of memory, a
program that timed out or was killed) is kept only once two runs in a row give it: the first is
written as a pending entry, which is never used. An entry that is missing, unreadable, of another
format or under the wrong key is a miss: the test runs and the entry is written again, so losing
the cache only makes a run slower. A run of every test of a compiler removes that compiler's
entries it did not use. A result from the cache is marked `cached` (with the time it was produced)
in `.work/results/<compiler>.json`, and its test page says so; the program's `.log` is written only
by a real run. `--refresh` runs everything and lists, in the report, each result that differs
from the cached one: a flaky test, or an input missing from the key. The design is in
[plans/test-result-cache.md](plans/test-result-cache.md).

## What a run does

For each test, the runner:

1. Compiles it in debug mode (the tests print with `Debug.log`) with
   `<command> make src/<Name>.elm --output=...`, in a copy of its project under
   `.work/<compiler>/<project>/`. Each compiler has its own `ELM_HOME`
   (`.work/<compiler>/elm-home`), so compilers never share a package cache. A package missing from
   it is first copied, source only, from another compiler's cache or from `~/.elm` if one has it,
   and the compiler builds its own artifacts; only packages nobody has are downloaded. Outputs are
   kept and reused until the test, its project or the compiler changes. (A test whose result is
   in the result cache, below, is not compiled or run at all.)
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
- each project's totals, one column per compiler, and each tag's;
- every test whose outcome is not the same under every compiler, with each compiler's outcome and
  the first line of the reason for each failure.

## The tests

`tests/` holds 12 Elm projects, each with its own `elm.json`. A test of the language itself is in
`elm`; a test of elm/core, the basis library (the operators of `Basics` included), is in `elm-core`;
any other test of a package is in that package's project. A request for a better error report,
whatever it is about, is in `elm-error-catalogue`. `&&`, `||`, `::` and list literals count as
language, since the book defines them as derived forms or as part of the initial environment. Every
project depends on the latest release of each package it uses.

| Project | Tests | What they cover |
|---|---|---|
| `elm` | 795 | the language: every construct, literals and escapes, closures, recursion, pattern matching, records, custom types, the typing of `number`, ports, flags and `main`, and the programs a compiler must reject |
| `elm-core` | 367 | elm/core, the basis library: arithmetic, equality and order, and every module, function by function |
| `elm-bytes` | 88 | elm/bytes encoders and decoders |
| `elm-parser` | 51 | elm/parser |
| `elm-json` | 42 | elm/json |
| `elm-regex` | 12 | elm/regex |
| `elm-url` | 9 | elm/url |
| `elm-time` | 8 | elm/time |
| `elm-html` | 5 | elm/html |
| `elm-virtual-dom` | 2 | elm/virtual-dom |
| `elm-random` | 1 | elm/random |
| `elm-error-catalogue` | 17 | requests for a better error report (tag `error-message`): what a compiler's report says or how it is laid out, which A Standard Definition of Elm? does not define. Where such a request rests on a program the book rejects, a test in `elm` checks the rejection |

### Tags

A test may carry tags, `-- TAGS: a, b`, which group tests across projects; each test is also tagged
with its own project. The results website shows the tests by project and by tag.

| Tag | Tests | What they are |
|---|---|---|
| `elm-spec` | 934 | tests of `elm` and `elm-core` whose expected outcome A Standard Definition of Elm? determines: its rules and restrictions, derived forms and initial basis |
| `elm19-compile-error` | 221 | programs the compiler must reject, checked by the title of Elm 0.19.1's error report |
| `elm19-bug` | 153 | bugs in Elm 0.19.1 and its packages reported in open GitHub issues, and its divergences from A Standard Definition of Elm?; each test links its issue or ruling and expects the correct behaviour |
| `elm19-bug-fix` | 9 | bugs in Elm 0.19.1 fixed in a later official Elm release; each test expects the fixed behaviour and says in its comment which release fixed it |
| `elm-unspecced` | 14 | tests whose expected outcome A Standard Definition of Elm? leaves open or puts outside the definition: what `Debug.log` prints, the value of an integer constant outside the Int range, the text of a crash, shader blocks; each says why in its comment |
| `elm-spec-contradicts` | 6 | reported bugs whose expected outcome A Standard Definition of Elm? contradicts: the book decides the program the other way, so the report is not a bug against it; each is marked XFAIL and says why in its comment |
| `error-message` | 17 | requests for a better error report: what a compiler's report says or how it is laid out, which A Standard Definition of Elm? does not define; named `ErrorMessages…` or `ErrorMessage…` after their issue, and kept in the project `elm-error-catalogue` |

A tag may also name an item of A Standard Definition of Elm?: a rule or restriction by its name,
as in `-- TAGS: elm-spec, s-dec-group, d-dec-rec, core-let-recursion`; a derived form by `df:` and
its name (`df:if-chain`); an entry of the initial basis by `b:` and its qualified name
(`b:Basics.compare`); a figure by `fig:` and its name (`fig:core-grammar-patterns`), for what the
book defines by a figure, such as its grammar; a section by its label (`sec:syntax-core-layout`).
The test checks that item. Such a tag is not a group of its own: the test's page links to the
item's page in the book (every rule, restriction, derived form, basis entry and figure has one),
or for a section to its place in its chapter; the item's page lists every test that checks it,
and a chapter lists under each figure and section heading the tests of it. A test tagged
`elm-spec` names the items that are its subject, not every rule its program happens to use, and
names at least one: a test that cannot say what in the book it checks is not tagged `elm-spec`. A
test of a derived form also names the rules, and the entries of the basis, that the form's
equivalent form goes through (a test of `&&` names `df:and`, `df:if` and the rules of `case`), for
its outcome is theirs. The names come from the LaTeX sources (`\defnrule[r:<name>]`,
`\citelabel{res:<name>}`, `\citelabel{df:<name>}`, `\citelabel{b:<name>}`, `\label{fig:<name>}`,
`\label{sec:<name>}`), read by `runner/spec-items.js`. Every rule and restriction of the book is
checked by at least one test.

The 34 tests of edge cases recorded from Elm on Node (Unicode and case mapping, JSON number and string
formats, Float edge values, regex and URL encoding details) carry `-- MODE-GUARD:` and
`-- NO-SKIP:`, and the case-mapping ones `-- UNICODE: 17.0`; they share the helper module
`ConformanceHelp`, of which each project that has them holds a copy. Three record what Elm on
Node does where A Standard Definition of Elm? decides nothing, and are tagged `elm-unspecced`:
`ParserLoneLowSurrogateTest` (a parser handed a Char made from a surrogate code point),
`StringWordsUnicodeSpaceTest` (`String.words` of a string that is only whitespace, where the
`elm19-bug` test `CoreIssue1019StringWordsEmptyTest` expects otherwise) and
`ProcessSleepNonFiniteTest` (a sleep of an infinite or NaN delay).

### Bugs and the issue triage

`tests/issues.tsv` records a triage of every open issue (883, in November 2026) of the
github.com/elm repositories but `elm-lang.org` and `package.elm-lang.org`, one line each:

| Column | Meaning |
|---|---|
| `likelihood` | that the issue is a real bug in Elm 0.19.1 or its packages: `CERTAIN`, `LIKELY`, `WEAK`, `NOT_BUG` |
| `impact` | `HIGH`, `MEDIUM`, `LOW` |
| `e2e` | whether a test of this suite could show it: `yes`, `maybe`, `no` (needs a browser, network, the REPL, ...) |
| `outcome` | `REPRODUCED` (a test tagged `elm19-bug`), `FIXED` (a test tagged `elm19-bug-fix`), `NOT_REPRODUCED` (Elm 0.19.1 behaves correctly), `NOT_E2E`, `NOT_ATTEMPTED` (not a bug, or the correct behaviour is debatable) |
| `test` | the test (or tests, space-separated), for `REPRODUCED` and `FIXED` |
| `fixed_in` | the compilers under which that test passes |
| `note` | why |

The tag `elm19-bug` also marks a test, named `Standard<ruling>...Test`, for each point on which Elm 0.19.1
diverges from *A Standard Definition of Elm?* (Appendix E, Known Divergences, of the book), where no
other test covered it. Each links the book's page for its ruling (and the GitHub issue, where there
is one) and expects what the book defines. A test of an Int beyond 32 bits holds for every Int range
the book allows.

A test whose issue's program is invalid under the book is kept as the issue wrote it, with a comment
that says so and names a test that follows the book. Three tests tagged `elm19-bug` use
surrogate escapes such as `"\u{D800}"`, which ruling A8 makes invalid: their counterparts are
`elm`'s `CharLiteralSurrogateEscapeTest` (compiler#2366), `elm-core`'s
`StringToListLoneSurrogateTest` (core#1060) and `elm-url`'s `UrlPercentEncodeLoneSurrogateTest` (url#54), which compute their lone
surrogates with `Char.fromCode`.

A bug counts as fixed once a later official Elm release (not a fork such as Lamdera) fixes it: its
test's tag then changes from `elm19-bug` to `elm19-bug-fix`, its comment says which release fixed
it, and its outcome becomes `FIXED`. A bug fixed only in a fork stays `elm19-bug`.

Some compiler bugs tagged `elm19-bug` make the compiler loop while its memory grows: the runner kills a
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
| `-- NO-SKIP: <reason>` | a skip (on another host, or on a compiler with no JavaScript host for flags and ports) is a failure instead |
| `-- TAGS: <tag>, <tag>` | the test's tags (lower-case letters, digits, `.` and `-`), besides its project; see [Tags](#tags) |
| `-- MODE-GUARD: <reason>` | a Char equality whose answer in debug mode (where `==` on Chars is a prefix test) differs from its answer under `--optimize` throws, so the program fails |
| `-- XFAIL: <reason>` | the test is expected to fail, for the reason given: it runs and passes or fails as any other, but its failure is reported as XFAIL and a pass as XPASS; `check-baseline.js` counts the failure as expected and lists a pass, and the site marks the test |
| `-- UNICODE: <version>` | the Unicode version the expected output was recorded with; under a Node with another, the runner warns |
| `-- NO-CACHE: <reason>` | always compiled and run: its result is never taken from the result cache |
| `-- HELPER: <reason>` | not a test, even with a top-level `main`: a module that tests import |

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

## The results website

`site/` is an [elm-pages](https://elm-pages.com) site built from a run's results: each compiler's
totals, each project's and each tag's totals per compiler with a page listing its tests, the tests
whose outcome differs between compilers, and a page per test with its description, issue link,
tags, source, and per compiler its outcome, failure message and output. To build it after `pnpm test:all`:

```sh
node runner/site-data.js          # writes site/data/ from .work/results/ and tests/
cd site && npm install && npm start      # dev server; or `npm run build` for site/dist/
```

The site is built for the root of its domain: the elm-pages it uses does not route pages under a
base path, so it cannot be served from a GitHub project page (`<owner>.github.io/<repo>/`).
Its address, which link previews and the links back to it use, is `Site.canonicalUrl`: the
environment variable `SITE_URL` at build time (default `https://elm-test-suite.netlify.app`), which
`site/scripts/site-url.mjs` writes into `site/src/SiteUrl.elm` before `npm run build` and
`npm start`. CI sets it to the staging site's address on the staging branch.
Styling is elm-css global snippets in `site/src/Style.elm`, used through `ts-` classes. The site's
own Elm unit tests are in `site/tests/` (`cd site && npm test`).

### Discussions

Each test, project, rule, restriction, derived form, entry of the basis and chapter of the
Definition has a Discussions section, linked to the repository's
[GitHub Discussions](https://github.com/eco-lang/elm-test-suite/discussions): the *Tests*
category for the tests, the *Standard* category for the Definition. A discussion is about an item
when its title holds the item's key in square brackets:

| Key | Item |
|-----|------|
| `[t:elm/CompilerIssue2281LongLineListTest]` | a test |
| `[p:elm]` | a test project |
| `[tag:elm19-bug]` | a tag |
| `[r:d-atexp-var]` | a rule (its label in `definition/tex/`) |
| `[res:...]`, `[df:...]`, `[b:...]`, `[fig:...]` | a restriction, derived form, entry of the basis or figure |
| `[ch:static-core]` | a chapter |

The Discuss link of an item opens GitHub's form for a new discussion with the key in its title and
a link back to the item. The browser reads the discussions from GitHub's REST API, which needs no
token for reading (60 requests an hour for each address): `Shared` fetches the two categories once
per visit, when the first page that shows discussions opens, and each page shows its own. Nothing
is rebuilt when a discussion is posted. `/discussions` and `/standard/discussions` list every
discussion of each category. The code is `site/src/Discuss.elm` (the links), `Discussions.elm`
(fetching, the keys) and `DiscussionsView.elm`; the design is in
[plans/github-discussions.md](plans/github-discussions.md).

## A Standard Definition of Elm?

The site also carries *A Standard Definition of Elm?*, a formal definition of the language, under
`/standard`: its chapters, a page for every rule at an address made from the rule's name
(`/standard/rules/d-atexp-var`), pages likewise for every restriction, derived form and entry of
the initial basis (`/standard/basis/Basics/modBy`), and the PDF. Its LaTeX sources are in `definition/`;
`runner/definition-data.js` turns them into the site's data, rendering the mathematics with KaTeX at
build time, so the pages need no KaTeX JavaScript. See [definition/README.md](definition/README.md).

```sh
node runner/definition-data.js    # writes site/data-standard/ from definition/tex/
```

The book's pages put their content in `View.freeze`, so elm-pages renders it at build time and does
not send the book's data to the browser. The styles are the `sd-` classes in `site/src/Style.elm`.

## Continuous integration

`.github/workflows/ci.yml` runs on Linux for each push to `master` or `standard-elm-suite` and each
pull request: `pnpm test:all`, the comparison report into the job summary, the website and its unit
tests, then `runner/check-baseline.js`, which adds to the job summary every test Elm 0.19.1 fails
that is not tagged `elm19-bug` or `elm19-bug-fix`. The suite reports on compilers already released, so no test
result, of the suite or of the website's unit tests, ever fails the job. The results and the built site are kept as workflow artifacts. With
the repository secrets `NETLIFY_AUTH_TOKEN` and `NETLIFY_SITE_ID` set, a push to `master` publishes
the site to Netlify, and a pull request gets a draft deploy linked in a comment. A push to
`standard-elm-suite` publishes to a separate staging site, with the secrets
`NETLIFY_AUTH_TOKEN_STAGING` and `NETLIFY_SITE_ID_STAGING`.

The result cache is kept between runs with `actions/cache` (the newest one, this branch's or else
`master`'s, is restored before the suite and saved after it even when a later step fails), so a
push that changes no test runs only the tests that never use the cache. GitHub drops a cache
unused for 7 days; the next run is then a full one. Every Monday a scheduled run, and any manual
run with the option *fresh*, runs every test with `--refresh`: the cache is renewed, and a result
that differs from the cached one is listed in the job summary.

## Layout

```
compilers.json        the compilers the runner knows
package.json          the compiler packages (pnpm) and the scripts
pnpm-workspace.yaml   which packages may run install scripts
runner/run.js         runs the suite with one compiler
runner/run-all.js     runs it with several and writes the comparison report
runner/directives.js  reads a test's directives and checks its output
runner/dom.js         the minimal DOM that lets Html programs start on Node
runner/site-data.js   writes the results website's data from the last results
runner/spec-items.js  the names of the book's rules, restrictions, derived forms, basis entries, figures and sections
runner/definition-data.js  writes the website's data for A Standard Definition of Elm?
definition/           the LaTeX sources and PDF of A Standard Definition of Elm?
runner/check-baseline.js  lists the tests Elm 0.19.1 fails that are not tagged elm19-bug, elm19-bug-fix (CI)
site/                 the results website (elm-pages)
plans/                plans for work on the site
.github/workflows/    CI: run the suite, build and publish the website
tests/<project>/      the test projects (elm.json and src/)
tests/issues.tsv      the triage of the open issues of the github.com/elm repositories
.work/                compiled programs, logs, package caches and results (not tracked)
```

## License

The code is BSD 3-Clause; see [LICENSE](LICENSE). The text of *A Standard Definition of Elm?* in
`definition/` is CC BY 4.0; see [definition/LICENSE](definition/LICENSE).
