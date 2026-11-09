# Audit Report: A Standard Definition of Elm?

## Summary

- Chapters audited: all 16 in Chapter Order (stage 07, two rounds).
- Round 1: two independent auditors (part X: definitions before use, static and dynamic agreement, cross-chapter seams; part Y: coverage, rulings and directions, voice). 31 findings: 7 Blocker, 9 Major, 15 Minor.
- Fixes: owning stages rerun by five fix agents applying shared design decisions (operator tables, E0 in both semantics, closed types in dynamic interfaces, default copies in number specialisation, Task.perform's hidden bindings, hidden array functions, host and platform defined once, "elaborates" for "well-typed", no implementation named in the body, rulings A88 and A89).
- Round 2: an independent verifier found 28 findings RESOLVED, 3 PARTLY, 0 OPEN, and 5 new problems at the seams the fixes touched (V1 Blocker, V2 to V5 Minor). All fixed in round 2; rulings A87 amended and A90, A91 added.
- Mechanical checks (orchestrator, final build): no LaTeX errors; no undefined or multiply defined references; rules numbered 1 to 192, each exactly once; no em dashes; hedging words only where Hard Constraint 1 allows; every registry macro used except `\jnot`; 3 overfull boxes, at most about 5pt.
- Result: no open Blocker or Major finding. Every chapter is marked `audited` in the checklist.

Detailed findings with evidence are in `drafts/audit-x.md`, `drafts/audit-y.md` and `drafts/audit-v.md` (round 1 verdicts are the first table of `audit-v.md`).

## Findings

| ID | Severity | Check / Rule | Finding | Owner Stage | Disposition |
|----|----------|--------------|---------|-------------|-------------|
| X1 | Blocker | A6, A2, R8 | No operator other than `::` elaborates or evaluates in any module. Static-core defines C(op) as C applied to the long variable the operator is bound to; dyna... | 04 (static-core, dynamic-core), 05 (appendices C, D) | fixed in round 1; verified RESOLVED in round 2 |
| X2 | Blocker | A6 (objects agree), Q6 | Appendix D gives each dynamic interface as ME_0(modid) = (empty, VE), "an environment with an empty qualified environment", but dynamic-modules defines Inter... | 05 (appendix-dynamic-basis) | fixed in round 1; verified RESOLVED in round 2 |
| X3 | Blocker | A6, Q6 | An import item `T(..)` naming a type that its module exposes closed elaborates (r:sm-item-opentype: the closed type keeps its constructors in its type struct... | 04 (dynamic-modules, or static-modules) | fixed in round 1; verified RESOLVED in round 2 |
| X4 | Blocker | A6, Q2 | Statically every module starts with List, `[]` and `::` in scope (pi_0 with TE_List and VE_List in static-modules, which is the E0 of Appendix C in content).... | 04 (dynamic-modules) or 05 (appendix-dynamic-basis) | fixed in round 1; verified RESOLVED in round 2 |
| X5 | Major | A6, R8 | Dynamic-core says "Every operator op is bound ... to the value of a long variable longvar" with no exception, and its DECIDED note names `List.cons`. Static-... | 04 (dynamic-core) | fixed in round 1; verified RESOLVED in round 2 |
| X6 | Blocker | A6, A4 (A27, A87), Q5 | Number specialisation replaces each declaration whose scheme quantifies number variables by one copy per assignment "that the program uses", the copies bindi... | 04 (dynamic-core numbers section, or programs) | fixed in round 1; verified RESOLVED in round 2 |
| X7 | Major | A6, A4 (A59, A87) | A top-level value whose scheme quantifies a number variable and that nothing uses has zero copies after specialisation, so it is never evaluated. Programs sa... | 04 (dynamic-core), 01 if A87 is to be reworded | fixed in round 1; verified RESOLVED in round 2 |
| X8 | Minor | A6, S3, Q5 | Restriction 3 defaults a number variable "free in the type of main", but r:sm-topdec-value closes main's scheme over every variable (U of C is empty at top l... | 04 (static-core) | fixed in round 2 (sentence on main removed from static-core); verified by build |
| X9 | Major | A2, R8 | `APPLY(Task.command, Perform tk)` uses a constructor `Perform` that is defined nowhere: it is in no interface of Appendix C, has no entry or arity in Appendi... | 05 (appendix-dynamic-basis), 04 (effects) | fixed in round 1; verified RESOLVED in round 2 |
| X10 | Major | O4, R8, Q2 | VE_0 is defined twice (static-modules line 172 and Appendix C line 160, same content), and static-modules reuses VE_0 and TE_0 in r:sm-topdec-types for the r... | 04 (static-modules) | fixed in round 1; verified RESOLVED in round 2 |
| X11 | Major | A2, S3, O1, R8 | The Core dynamic objects include EffVal = TaskVal u CmdVal u SubVal u ProcId u ProgVal, all defined only in Chapter 8 (a higher level and later in Chapter Or... | 04 (dynamic-core, dynamic-modules, effects) | fixed in round 1; verified RESOLVED in round 2 |
| X12 | Minor | S3, S4 | Lower levels state content of higher ones: syntax-core forbids rebinding a variable "declared at the top level of the enclosing module", which syntax-modules... | 03 (syntax-core), 04 (static-core, dynamic-core) | accepted as is: decision 4 places number specialisation in sec:dynamic-core-numbers; other S3 items fixed in round 1 |
| X13 | Minor | A6, R8 | Dynamic-modules binds the record alias constructor as `{tycon -> record(...)}` in a ValEnv and tests `tycon in RA`, `(VE of I)(tycon)`, `RA subset Dom VE`, a... | 04 (dynamic-modules) | fixed in round 1; verified RESOLVED in round 2 |
| X14 | Minor | A2, O5 | Dynamic-core says the decorated-metavariable convention is "as defined for the static semantics (Chapter 4)"; static-core never states it; it is in introduct... | 04 (dynamic-core) or 04 (static-core) | fixed in round 1; verified RESOLVED in round 2 |
| X15 | Minor | A4 (A59), Q4 | The thunk translation re-evaluates a group member at each reference within its group. The Comment correctly says the result differs from v_i only through the... | 01 (log), 04 (dynamic-modules) | fixed in round 1; verified RESOLVED in round 2 |
| X16 | Minor | A6, Q7 | Two program-level restrictions are chapter-agent decisions with no ambiguity-log entry ("main is not recursive, even through a delayed occurrence"; "no modul... | 01 (log), 04 (static-modules) | fixed in round 1; verified RESOLVED in round 2 |
| X17 | Minor | R1 | The sentences `B_STAT vdash_STAT program => (tau, PE)`, `B_DYN vdash_DYN program => v` and `B vdash program => (tau, PE, v)` are introduced without saying wh... | 04 (programs) | fixed in round 1; verified RESOLVED in round 2 |
| X18 | Minor | A6 | Appendix A says that `True`, `False`, `negate` and `::` in equivalent forms denote the initial basis's bindings "whatever bindings of these names are in scop... | 03 (appendix-derived-forms) or 04 (static-core, dynamic-core) | fixed in round 1; verified RESOLVED in round 2 |
| Y1 | Blocker | A4 (A4), G6 | Ruling A4 is not in the book. A4 says field access may follow only a value identifier, a record, a record update or a parenthesised form, and that `.x.y` is ... | 03 | fixed in round 1; verified RESOLVED in round 2 |
| Y2 | Blocker | A3 (I2), A6 | The dynamic interfaces of the initial basis have the wrong shape. Appendix D gives each `ME_0(modid) = (emptymap, VE)`, an environment, but Chapter 7 defines... | 05 | fixed in round 1; verified RESOLVED in round 2 |
| Y3 | Major | A3 (I2), D10, A60 | `Task.perform` and `Task.attempt` get no value. Their elm/core texts apply `command` to `Perform (...)`. Appendix D evaluates the texts of `Task` "in an envi... | 05 (Appendix D), 04 (effects) | fixed in round 1; verified RESOLVED in round 2 |
| Y4 | Major | A4 (A60), A3 (I2); open question 3 | Effects says arrays are defined by Elm text, but Appendix D says they are basic values. effects.tex:527-529 (comment on r:e-enc-array) says "Array.toList is ... | 04 | fixed in round 1; verified RESOLVED in round 2 |
| Y5 | Major | A4 (A74, A45), D11; open question 9 | Appendix E does not record Elm/JS's non-conformance at the port boundary for non-finite floats. The body encodes an outgoing NaN or infinity as `null` (r:e-e... | 05 | fixed in round 1; verified RESOLVED in round 2 |
| Y6 | Major | A4 (rulings complete), D11, CLAUDE.md "No silent decisions" | Three decisions about what crosses a port are DECIDED comments with no ambiguity-log entry: an outgoing NaN or infinity encodes as `null`; JSON numbers are d... | 01 | fixed in round 1; verified RESOLVED in round 2 |
| Y7 | Minor | G6, A3; open question 8 | The constructor-pattern arity restriction is not a condition on syntax alone: deciding which declaration a `longcon` denotes needs the imports, qualifiers, r... | 03 | fixed in round 1; verified RESOLVED in round 2 |
| Y8 | Minor | B4 | The list-pattern row is defined by itself (its equivalent form contains a list pattern with one element fewer), which B4 forbids ("No cycles"); the text admi... | 03 | fixed in round 1; verified RESOLVED in round 2 |
| Y9 | Minor | A4 (A65) | Appendices D and E disagree on `sqrt`. Appendix D puts `sqrt` with `+ - * /` among the operations that "allow no such latitude" (correctly rounded). Appendix... | 05 (and 01 if A65 is amended) | fixed in round 1; verified RESOLVED in round 2 |
| Y10 | Minor | A7 (Hard Constraint 3), D8 | The body names an implementation and describes what implementations do: "an extension of eco" (static-modules table), "An eco extension that admits Bytes" (e... | 04 | fixed in round 1; verified RESOLVED in round 2 |
| Y11 | Minor | A7 (Hard Constraints 2 and 5) | "host" is used throughout Chapters 8 and 9 and is never defined. "platform" is defined only in programs.tex:38, after its uses in Chapters 3, 5 and 8. syntax... | 04 (effects, static-modules), 03 (syntax-modules) | fixed: last occurrence retitled in round 2 (V4) |
| Y12 | Minor | A7 (Hard Constraints 2 and 5; Terminology) | "well-typed program/phrase" and "a type error" are used but never defined; the book's term is that a phrase elaborates (dynamic-core.tex:31 already states th... | 04, 05 | fixed in round 1; verified RESOLVED in round 2 |
| Y13 | Minor | D11 | The two "what can and cannot be sent" tables classify `Bytes` differently: Chapter 5 gives it its own row ("not in Standard Elm"), Chapter 8 lists it among "... | 04 | fixed in round 1; verified RESOLVED in round 2 |
| V1 | Blocker | A6, A2 (A87, I2) | The values of Basics written in Elm whose schemes quantify a variable of class number, `abs` and `clamp`, have no binding for their non-default copies. Appen... | 05 (appendix-dynamic-basis) | fixed in round 2 |
| V2 | Minor | A4 (rulings match text), CLAUDE.md "No silent decisions" | The book now makes, for every declaration that quantifies number variables, the default copy (Int for each) whether or not the program uses that instance (de... | 01 (log) | fixed in round 2 (A87 amended; Appendix E row added) |
| V3 | Minor | R8, A6 | The X18 fix makes the meaning of `Basics.True`, `Basics.False` and `Basics.negate` depend on whether the occurrence was introduced by an equivalent form ("fo... | 03 (syntax-modules), 04 (static-core, dynamic-core) | fixed in round 2 (A91 logged; restriction in Chapter 3) |
| V4 | Minor | A7 (Terminology; design decision 7) | The heading "Effect Managers and Programs on a Platform" uses "effect manager", which decision 7 replaces by the registered "manager". | 05 (appendix-implementation) | fixed in round 2 |
| V5 | Minor | O1 (source hygiene) | The DECIDED comment still says "Chapter 8's comment on r:e-enc-array, which calls Array.toList Elm text, needs aligning (reported)", which Y4's fix has made ... | 05 (appendix-dynamic-basis) | fixed in round 2 |

## Carried From Mechanisation

From `../mechanisation/mechanisation-report.md` (Lean 4; all 48 rules of Chapter 6 and APPLY for arithmetic, equality, order, Booleans and Debug; evaluator proved sound; 246 checks, 239 agree, 7 diverge).

| Item | Owner Stage | Disposition |
|------|-------------|-------------|
| F1 operators unreachable through Basics | 04, 05 | fixed by audit round 1 (X1, operator tables); encoding updated |
| F2 basis interfaces had the wrong shape | 05 | fixed by audit round 1 (X2) |
| F3 Pattern Rows box admits FAIL though no rule fails | 04 | fixed (round 3) |
| F4 r:d-match-fail unreachable (exhaustiveness) | none | known |
| F5 pattern-row rule lacks lab in Dom r | 04 | fixed (round 3) |
| F6 constructor arity not carried by constructor values | none | known: arity is that of the constructor's own type (Chapter 6) |
| F7 Appendix E row on `p == p` with NaN | 05 | fixed (round 3) |
| F8 order of Debug.log output unspecified | none | known (A57, A58, A62) |
| Divergence: Int `1 ^ -1`, `(-1) ^ -3`, `(-1) ^ -2` (A43) | eco | fix implementation (definition: 1, -1, 1; eco: 0) |
| Former divergence: `max nan 1`, `min nan 1`, `max 0 -0`, `min -0 0` (A48) | none | resolved: the author changed A48 to IEEE `minimum`/`maximum` at Float; now agree (243 of 246 checks agree) |

## Minor Items Left Open

| Item | Reason |
|------|--------|
| `\jnot` registered but unused | harmless; kept for future use |
| 3 overfull boxes (about 5pt) | cosmetic; see the build report of stage 08 |
