# Plan: reuse test results that cannot have changed

## Goal

A CI run compiles and runs all 1,289 tests under each of the 4 compilers, about 7.5 of its 10
minutes, even when a push changes only the website or the Definition. A released compiler does not
change, nor does a test that is not edited, so most of those results are already known. Keep each
test's result under a hash of everything it depends on, and on the next run take the result from
there instead of compiling and running the test again. A cache that is lost, partial or corrupt
must only make the run slower, never give a wrong result.

## What exists

- `runner/run.js` skips the *compile* of a test whose output is newer (by file modification time)
  than its source, its project's `elm.json`, its helper modules, the runner and the compiler. Every
  test is still *run*.
- In CI a fresh checkout gives every file a new time and `.work/` is not kept (only the package
  caches are), so every run compiles and runs everything.

## Design

### The key

For each test and compiler, a SHA-256 over a canonical JSON object of every input that can change
the outcome:

| Input | Why |
|-------|-----|
| a format number (`1`) | a change to the cache's shape or rules discards every entry |
| the compiler: name, target, args, env, `elmVersion`, its `--version` line, and the SHA-256 of its executable | the binary is what compiles; its hash catches a reinstall or a different build behind the same version |
| the judge: the contents of `runner/run.js`, `runner/directives.js` and `runner/dom.js` | how a test is compiled, launched and checked |
| the environment: Node's version, the platform and architecture, and on GitHub's runners the image (`ImageOS`, `ImageVersion`) | the js programs run on Node, whose Unicode and Intl behaviour changes between versions |
| the limits: the run and compile timeouts and the compile memory limit | they decide some outcomes |
| the project: its name, its `elm.json` as written for the compiler, and the project's settings in `run.js` (mode guard, skips allowed, Unicode version) | |
| the test's source and the source of every module of its project it imports, directly or not | the only source a compile reads (packages are fixed by `elm.json`, and a package version never changes) |

The executable is hashed once per run of `run.js` (the four binaries take well under a second). A
test's own directives (CHECK lines, EXIT, STDIN, ENV and the rest) are in its source, so they are
covered. Helper modules count only for the tests that import them, so editing one test reruns only
that test.

### The entries

`.work/result-cache/<compiler>/<key>.json`:

```json
{ "format": 1, "key": "<hex>", "project": "elm-bugs", "test": "SomeTest", "ranAt": "2026-11-07T22:56:01Z",
  "pending": false, "result": { "status": "fail", "message": "...", "output": "...", "ms": 31 } }
```

- **Reading.** An entry counts only if it parses, has this format, its `key` is the one looked up,
  and it is not pending. Anything else is a miss: the test is compiled and run, and the entry is
  written again.
- **Writing.** Only after the test finished, to a temporary file renamed into place, so a run that
  is interrupted leaves no half entry.
- **Pruning.** A run of every project and test of a compiler (no `--project`, `--filter` or
  `--record`) removes that compiler's entries that it neither read nor wrote: they belong to sources
  or compilers that no longer exist.

### What is not cached, or not at once

- **Never:** tests whose outcome depends on timing: those with `-- STDIN-DELAY-MS:`, and those whose
  source, or a module it imports, uses `Time.now`, `Time.every`, `Process.sleep` or
  `Random.generate` (19 source files today); tests with a new directive `-- NO-CACHE: <why>`, for
  any other test that must always run; skips (they are decided before the cache is consulted, as
  now), and `--record`.
- **Only once two runs agree:** a compile that crashed, timed out or ran out of memory, and a
  program that timed out or was killed by a signal. Such a result can be an accident of the
  moment (a busy machine, an intermittent crash such as `compiler killed by SIGSEGV`), so the first
  is written as a *pending* entry, which is never used; the next run of the test confirms it when it
  gives the same outcome and the same first line of reason, and otherwise replaces it. (The first
  version of this plan never kept these. Measured, they were most of a run with a full cache: the
  `elm-bugs` tests of compilers that hang or exhaust memory wait out the 60 s compile limit on every
  run, so a warm run took 2 minutes instead of seconds.)

### Options

- `--no-cache`: neither read nor write the cache.
- `--refresh`: run every test, write fresh entries, and report each test whose fresh result differs
  from the entry it replaces (a flaky test, or an input missing from the key). `run-all.js` passes
  both through and lists such differences in its report.
- The output says how many results came from the cache: `compiling 12 (3 up to date), 1180 from
  the cache`.

### The results

A result taken from the cache is the same as the one first written, plus `"cached": "<ranAt>"` in
`.work/results/<compiler>.json`. `runner/site-data.js` passes it on, and a test's page says "from
the cache, ran on <date>" beside the time it took. The program's `.log` file under `.work/` is
written only by a real run.

### CI

- `actions/cache/restore` restores `.work/result-cache` before the suite runs (the newest entry
  whose key starts `results-`; a branch without one gets `master`'s), and `actions/cache/save`
  saves it after the suite, under `results-<run id>-<attempt>`, even when a later step fails.
  GitHub evicts caches unused for 7 days; then the next run is a full one and rebuilds it.
- A weekly scheduled run, and a manual run with the option `fresh`, run the suite with
  `--refresh`: every test runs, the cache is renewed, and any test whose result differs from the
  cache is in the job summary.

## Losing the cache

Every case is a miss, never a wrong result: no cache (first run, evicted, a new branch), a missing
or unreadable entry, an entry of another format, an entry under the wrong name. The run is then
as slow as today and writes the cache again.

## The risk, and the guard

The one way to get a wrong result is an input that changes an outcome but is not in the key. The
key errs wide (the whole judge, the binary's hash, the runner image), and the weekly `--refresh`
run compares every cached result with a fresh one and reports any difference.

## Testing

- A run with an empty cache gives the same results as `--no-cache`.
- A second run takes every cacheable result from the cache, and its results file equals the
  first's apart from `cached`.
- Editing one test reruns only it (under each compiler); editing a helper module reruns only the
  tests that import it; touching `runner/directives.js` reruns everything.
- A corrupt entry, an entry of another format and an entry under the wrong name are misses, and are
  rewritten.
- An interrupted run leaves no partial entry.
- A compile that times out is pending after one run, used after the second, and the third run
  takes it from the cache.
- `--refresh` reports a difference when an entry is edited by hand to another status.
- Pruning removes an entry no test uses, and only on a complete run.
- In CI: the second run on a branch takes its results from the cache.

## Files

| File | Change |
|------|--------|
| `runner/run.js` | the key, the cache's reading, writing and pruning, `--no-cache`, `--refresh` |
| `runner/directives.js` | `uncacheable(content)`: why a test is never cached, or null; `-- NO-CACHE:` |
| `runner/run-all.js` | the differences found by `--refresh` in the report |
| `runner/site-data.js`, `site/src/Data.elm`, `site/app/Route/Projects/Project_/Test_.elm` | the `cached` date |
| `.github/workflows/ci.yml` | restore and save the cache; the weekly and manual `--refresh` runs |
| `README.md` | the cache, its options and the `-- NO-CACHE:` directive |
