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
