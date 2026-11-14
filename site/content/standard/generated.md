Each of these theorems states that a test program, evaluated by the rules of [Chapters 6, 7 and 9](/standard/dynamic-core), logs the value each of its checks expects, or, for a program that stops at Debug.todo, has no meaning. Nothing about them is written by hand: the test programs are translated into Lean by a program, and the theorems are written by Lean from the translations, as follows.

## 1. The translator turns each test into Lean

The translator, `definition/tools/src/Translate.elm`, reads every test tagged elm-spec. It parses the program with elm-syntax, resolves its names, works out the type of every number constant by the book's number specialisation, and prints each module of the program as a Lean syntax tree of the bare Core (the derived forms of Appendix A applied by `Derived.lean`), with its exposing list, imports, custom types and aliases. Each `-- CHECK: label: value` line of the test becomes a check on what the program logs. A test outside what the encoding covers is not translated, and its page says why. For example, the test ClosureCapture01Test

```
unwrapLater w =
    \dummy ->
        case w of
            Wrap x -> x

_ = Debug.log "unwrap1" (unwrapLater (Wrap 42) 0)    -- CHECK: unwrap1: 42
```

becomes

```lean
def g_elm_ClosureCapture01Test : Program := {
  name := "ClosureCapture01Test", source := "tests/elm/src",
  exposing := (.items [.var "main"]), imports := [⟨"Html", "Html", some (.items [.var "text"])⟩],
  types := [("Wrapper", [("Wrap", 1)])],
  defs := [
    .fn "unwrapLater" [pv "w"] (lams [pv "dummy"] (caseOf (v "w") [(pcon "Wrap" [pv "x"], v "x")])),
    .fn "main" [] (letDefs [ ... Debug.log "unwrap1" ... ] ...) ],
  checks := [
    chk .check "unwrap1: 42" .int,
    chk .check "unwrap2: 99" .int ] }
```

Every translated test shows its translation on its own page, under “Lean translation”, beside its Elm source. The translations are generated again whenever the mechanisation is rebuilt, so they follow their tests; a page whose test has changed since says so.

## 2. The translations are gathered in shards

The translated programs are written in files called shards, so that Lean builds them in parallel. A shard is a fixed alphabetical range of test names, so adding a test changes one shard only. There are {{programs}} programs and {{checks}} checks in all:

<slot name="shards"></slot>

## 3. Lean writes one theorem per program

Each shard has a file of theorems, `Generated/Checks<Shard>.lean`, in which the command `#mod_program_theorems`, a metaprogram in Theorems.lean, runs while Lean compiles the file. For each program of the shard it writes the text of one theorem and has Lean elaborate it as if it were in the file:

```lean
theorem t_elm_ClosureCapture01Test :
    Mod.ViewChecks (Mod.Btest []) g_elm_ClosureCapture01Test.modules [checks] :=
  Mod.viewChecks_sound (o := .const false) (by decide +kernel)
```

In words: the program's modules, evaluated by Chapter 7's rules in the test basis, have a derivation whose log meets every check. For a program the test expects to stop at Debug.todo the theorem is instead `Mod.NoMeaning (Mod.Btest []) g.modules`, by `Mod.noMeaning_sound`: no derivation gives it a meaning. Where the book lets an implementation choose (*APPLY* gives a set), the theorem names the choice that meets the checks.

<slot name="source"></slot>

## 4. Lean's kernel proves each one

`decide +kernel` has Lean's kernel itself run the mechanisation's evaluator on the program and check its log against the checks; nothing outside the kernel is trusted for this step. The evaluator is proved sound for the rules ([`evExp_sound`](/standard/proofs/evExp_sound)), and the lemmas named above turn the kernel's computation into a statement about the rules. {{native}} checks belong to programs proved by native_decide instead, tagged [native]: programs that use a value only the C library computes (round, floor, an elementary function, ^ at Float, Debug.toString), or whose proof breaks the memory budget. A program that uses a value of the core library written in Elm (`Tuple.second`, `List.foldl`, ...) evaluates it by its text in elm/core 1.0.5, which the book leaves outside the definition; its theorem is tagged [library].

All of this happens on every build of the Lean project: when a test changes, the translator writes its new translation, its theorem is generated afresh, and if the rules no longer give an expected value, the build fails.

## 5. What they establish, and what they do not

Together the theorems establish that, for each of these {{generated}} checks, the rules with the encoded part of *APPLY* give exactly the value the check expects. A check of what a program logs before it stops at Debug.todo is in no theorem (its program's theorem says only that it has no meaning); the run of the examples compares it. Each theorem is about the Lean translation of its program, which the translator makes; for the translated tests, the end-to-end theorem on the test's page shows that Lean computes the same translation from the source.

## The checks and their theorems

<slot name="checks"></slot>
