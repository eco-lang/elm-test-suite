# Tests to review after the Lean modelling

Candidates found while modelling the book in Lean (plans/lean-full-definition.md). Nothing here has
been changed: each entry says what the test checks today, why it looks off against the book, and a
possible correction, for the author's manual review once the modelling is complete.

## Expectations that accept a compiler crash or hang

These tests expect a compile error, and Elm 0.19.1 to 0.19.3 "pass" them by crashing or hanging.
The book refuses each program with an ordinary type error, so the test could expect that error
instead of any compile failure.

| Test | Elm today | The book | Possible correction |
|------|-----------|----------|---------------------|
| CompilerIssue1639LetAnnotationTypeVarCrashTest | crash, `a [rank = 2]`, Type/Solve.hs:206 (0.19.1, 0.19.2; 0.19.3 also crashes); with an annotation `fanOut : Int -> Int` all three report TYPE MISMATCH | the `let` annotation is too general: its variable would escape into the enclosing function (A20) | expect the "annotation is too general" TYPE MISMATCH, not a crash |
| CompilerIssue1839RigidLetAnnotationCrashTest | crash, `a [rank = 2]` | as above (A20) | as above |
| CompilerIssue2001RankCrashParametricLetAnnotationTest | crash | as above (A20) | as above |
| CompilerIssue2077RankCrashExtensibleLetAnnotationTest | crash, `a [rank = 2]` | as above (A20) | as above |
| CompilerIssue2296LetAnnotationFreeVarCrashTest | crash, `msg [rank = 2]` | as above (A20) | as above |
| CompilerIssue2301InnerSkolemOuterVarCrashTest | crash, `a [rank = 2]` | as above (A20) | as above |
| CompilerIssue1691ContradictoryExtensibleRecordHangTest | hangs, memory unbounded | a type error (the record type would contain itself) | expect a TYPE MISMATCH, not a hang |
| CompilerIssue2027IncompatibleExtensibleRecordsHangTest | hangs or crashes | a type error | as above |
| CompilerIssue2106FoldlExtensibleRecordHangTest | hangs or crashes | a type error (infinite record type) | as above |
| CompilerIssue2108IfBranchExtensibleRecordHangTest | hangs or crashes | a type error | as above |

Other `CompilerIssue*Crash*`/`*Hang*` tests that the Lean refutation already refuses may have the
same shape; check them in the same pass.

## Refused for a different reason than the test intends

| Test | What it means to check | Why Lean refuses it | To decide |
|------|------------------------|---------------------|-----------|
| TypeMismatchTypeUnderAnExposingListTest | TYPE MISMATCH: `x : Int`, `x = Just 1`, with `Maybe` imported by an exposing list | its imports do not elaborate in the test basis (probably `Tuple exposing (first, pair)` names a value Appendix C does not bind; to confirm) | add the value to the test basis (or Appendix C), or change the import, so the test is refused for its type error |

## Elm disagrees with the book

| Test | Elm today | The book |
|------|-----------|----------|
| CompilerIssue2274MutualRecursionTransmuteTest | 0.19.1 infers `f : a -> b -> c`, accepts the program, and `eraseType` turns a String into an Int | `f : a -> b -> b`, so `eraseType : a -> b` is too general: a TYPE MISMATCH (the test expects this; Elm fails it) |

## `elm-spec` tests that leave the basis

Reviewed on 2026-11-14: the `elm-spec` tests that use a module or library function outside the
book's basis, asked whether they could check what they check within it. Seven were resolved then
(see untranslated-tests.md, group H), and the two below were done the same day as far as the basis
allows (group J of that file): PortEchoJsonValueTest as its correction says, with the sample
`[1,2,null]` for the mixed array; StandardA92BytesPortTest kept, beside a new
StandardA92BytesPortDeclarationTest for the static half. The round trip of bytes still needs the
host below.

| Test | What it checks | Why it leaves the basis | Possible correction |
|------|----------------|-------------------------|---------------------|
| PortEchoJsonValueTest | `e-enc-value`, `e-dec-value`: a JSON `Value` crosses a port as it is | builds its Values with `Json.Encode` and prints them with `Json.Encode.encode`. Within the basis a Value comes only from flags or a port, and neither `Debug.log` nor `==` can observe it portably: Elm 0.19.1 prints a Value as `<internals>` (Lean prints JSON text), and its `==` on Values is not the book's (below) | take the Values from flags typed `Value`, send them out on `echoOut : Value -> Cmd msg`, and receive them on an `echoIn` of a concrete type (a record, a tuple), logging the typed result; the mixed array `[1,true,null]` would become a sample that some Elm type decodes |
| StandardA92BytesPortTest | ruling A92: `Port(Bytes)`, and the `e-enc-bytes`/`e-dec-bytes` round trip | builds and reads its bytes with `Bytes.Encode` and `Bytes.Decode`. Within the basis no program can make a `Bytes` value: flags are JSON, and `Dec_Bytes` is undefined at every JSON value | split it: a static test that declares the two ports and logs a constant (in the basis, and still rejected by Elm 0.19.1); and, for the round trip, a host that sends a byte sequence on `echoIn` at start (a new directive in `runner/run.js` and in Lean's echo host), the program logging the value (`<3 bytes>` in both) and `received == sent` |

## Elm's `==` on JSON values is not the book's

Found during that review, with a scratch program on Elm 0.19.1 (no test checks it yet). The book's
equality (Appendix D, Figure "Equality of Values", clause 4) makes two objects of boundary values
equal only when they have the same set of keys. Elm 0.19.1 gives `True` for `{"a":…,"b":"x"} ==
{"a":…,"b":"x","c":1}` (its `_Utils_eqHelp` walks the keys of the left object only), and another
comparison of Values received through a port crashed with a `TypeError` inside `_Utils_eqHelp`. A
test with Values from flags would record this as an `elm19-bug`, if the book's clause is meant to
hold of `Json.Encode.Value`.
