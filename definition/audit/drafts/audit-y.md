# Audit Part Y: Coverage (A3), Rulings (A4), Voice (A7)

Scope: A3 (R3, D1, survey coverage, B4, I2), A4 (A1 to A87, D1 to D11), A7 beyond the scripted checks (prose-style Hard Constraints 2 to 5, Terminology). Open questions 3, 8 and 9 of the brief.

## Findings

| ID | Severity | Chapter:line | Check / Rule | Finding | Owner Stage | Proposed Fix |
|----|----------|--------------|--------------|---------|-------------|--------------|
| Y1 | Blocker | syntax-core.tex:569-577, 258-262; appendix-derived-forms.tex:64-66 | A4 (A4), G6 | Ruling A4 is not in the book. A4 says field access may follow only a value identifier, a record, a record update or a parenthesised form, and that `.x.y` is the application of `.x` to `.y`. The grammar gives `atexp.lab` for every atomic expression, and the lexical rule (a `.` adjacent on both sides is a field selection) makes `.x.y` the selection `(.x).y` and `"s".x` a selection on a string constant. appendix-derived-forms.tex:64-65 says "the atomic expressions that may precede `.lab` are restricted in Section sec:syntax-core-restrictions", but that section has no such restriction. | 03 | Add to the "Records" bullets of sec:syntax-core-restrictions: "In a field selection `atexp.lab`, `atexp` is a `longvar`, a record, a record update, a field selection, or a phrase that begins with `(` (parenthesised expression, tuple, unit, operator value). A field accessor is never followed by a field selection: in `.lab1.lab2` the second `.` begins a second field accessor, so the phrase is the application of `.lab1` to `.lab2`." Cite `% A4`. Adjust the third bullet of sec:syntax-core-lexical (line 258-262) to say a `.` directly after a field accessor begins a field accessor. Keep appendix-derived-forms.tex:64-66 pointing at the new bullet. |
| Y2 | Blocker | appendix-dynamic-basis.tex:29-31, 273-276; dynamic-modules.tex:96, 315-325 | A3 (I2), A6 | The dynamic interfaces of the initial basis have the wrong shape. Appendix D gives each `ME_0(modid) = (emptymap, VE)`, an environment, but Chapter 7 defines a dynamic Interface as `(RA, CE, VE)`, and its rules read the components: rule r:dm-expitem-open needs `(CE of I)(tycon)`, and r:dm-expitem-alias / r:dm-expitem-type test `tycon in RA of I`. The default import `import Maybe exposing (Maybe(..))` (and `Result(..)`) therefore has no evaluation rule, so no module, and no program, evaluates. | 05 | In Appendix D state `ME_0(modid) = (RA, CE, VE)` (Chapter 7's Interface) for every module: `RA = emptyset` everywhere; `CE` binds `Bool`, `Order` (in `Basics`), `Maybe` (in `Maybe`) and `Result` (in `Result`) to the value environments of their constructors (as in Figures fig:dynamic-basis-basics and fig:dynamic-basis-others); `CE = emptymap` for every other module. Replace "(emptymap, emptymap)" at line 275 by "(emptyset, emptymap, emptymap)". Note that the property of sec:dynamic-modules-compound holds for these interfaces. |
| Y3 | Major | appendix-dynamic-basis.tex:417-426; effects.tex:426-430; appendix-static-basis.tex:409-411 | A3 (I2), D10, A60 | `Task.perform` and `Task.attempt` get no value. Their elm/core texts apply `command` to `Perform (...)`. Appendix D evaluates the texts of `Task` "in an environment binding the identifiers of its module, and those it imports, to their values in ME_0", but neither `command` nor the constructor `Perform` (of Task's unexposed type `MyCmd`) is in `ME_0(Task)` (Appendix C 409-411 says `command` is absent; Appendix D line 286 says the basic value `Task.command` is bound to no identifier of the basis). So both texts have free identifiers. effects.tex:429-430 says instead that "the initial basis binds it to the basic value Task.command", which contradicts Appendices C and D. | 05 (Appendix D), 04 (effects) | Appendix D: give the environment of the texts of `Task` explicitly, as `E_K` is given for `Basics`: it binds the identifiers of `ME_0(Task)` and of `Task`'s imports, `command` to the basic value `Task.command`, and the constructor `Perform` (arity 1) to the constructor value `Perform`; neither is in the interface. effects.tex:429-430: replace "the initial basis binds it to the basic value Task.command of the figure" by "the environment in which the text of \kw{Task} is evaluated binds it to the basic value \kw{Task.command} of the figure (Section sec:appendix-dynamic-basis-elm)". |
| Y4 | Major | effects.tex:161-164, 527-529 | A4 (A60), A3 (I2); open question 3 | Effects says arrays are defined by Elm text, but Appendix D says they are basic values. effects.tex:527-529 (comment on r:e-enc-array) says "Array.toList is written in Elm in the basis, and its text defines it (A60)". Appendix D (282-292, 944-965) models arrays as constructor values `array v` and makes `Array.fromList` and `Array.toList` basic values bound to no identifier of the basis; Appendix C gives `Array` no values. effects.tex:161-164 also gives `Array.toList` as an example of "the value to which the initial dynamic basis binds a long identifier of the basis", which it is not. | 04 | effects.tex:527-529: replace the second sentence by "\kw{Array.toList} is the basic value of Section sec:appendix-dynamic-basis-arrays, bound to no identifier of the basis." and drop `% A60` there. effects.tex:161-164: drop "or \kw{Array.toList}" from the example and add "the basic values \kw{Array.fromList} and \kw{Array.toList} of Appendix D, which no identifier of the basis spells, are written likewise". |
| Y5 | Major | appendix-implementation.tex:744-766, 966-988; effects.tex:516-521, 596-601 | A4 (A74, A45), D11; open question 9 | Appendix E does not record Elm/JS's non-conformance at the port boundary for non-finite floats. The body encodes an outgoing NaN or infinity as `null` (r:e-enc-float-null), and an execution's trace then holds `out(p, null)`. The Elm/JS row of "Values at the Boundary" says "NaN and the infinities pass as Floats in both directions" but does not say "Does not conform", and the Known Divergences table "Programs and Ports" has no row for it, although Appendix E claims to list "every known point on which an implementation does not conform". Likewise an incoming `-0` to an `Int` port gives Elm/JS a negative-zero Int, where the body decodes it as `0` (r:e-dec-int comment). The section's requirement list (657-675) states no requirement for the encoding of Float, so the reader cannot see what the row is measured against. | 05 | In "Values at the Boundary", Elm/JS consequences: add "Does not conform: an outgoing NaN or infinity is delivered as a host number, where the definition delivers \kw{null}; an incoming \kw{-0} at an \kw{Int} port gives a negative zero." Add the bullet "A Float that is NaN or an infinity is encoded as JSON null; an incoming JSON number decodes at Int exactly when it is an integer in IntRange, and at Float as the nearest float (Section sec:effects-ports). % A73, A74" to the list at 657-675. Add to Known Divergences "Programs and Ports": `Elm/JS | outgoing Float NaN or infinity | passed as a host number | null | A74`. |
| Y6 | Major | effects.tex:89-92, 520-521, 606-607 | A4 (rulings complete), D11, CLAUDE.md "No silent decisions" | Three decisions about what crosses a port are DECIDED comments with no ambiguity-log entry: an outgoing NaN or infinity encodes as `null`; JSON numbers are decimal rationals, so the sign of a zero is lost at the boundary; an incoming number beyond the finite floats decodes as an infinity. D11 names "what can and cannot be sent over a port" as the key thing to document; A74 rules only that the boundary is the JSON value model and does not settle non-finite floats. | 01 | Add a log entry A88 "Non-finite and signed-zero Floats at the boundary" recording the three choices (provisional, reason: the JSON model of A74 has no NaN, infinity or negative zero; eco writes `null`), then change the three DECIDED comments in effects.tex to cite `% A88`, and cite A88 in Appendix E (see Y5). |
| Y7 | Minor | syntax-core.tex:598-606 | G6, A3; open question 8 | The constructor-pattern arity restriction is not a condition on syntax alone: deciding which declaration a `longcon` denotes needs the imports, qualifiers, replacement and ambiguity rules of Chapter 5 (provider maps, A28, A38). It is also redundant: rule r:s-pat-con requires the instance to be a constructed type after exactly n arguments, and r:s-atpat-con requires a constructed type, so the wrong arity already fails to elaborate (and dynamic-core's comment on r:d-pat-con relies on elaboration, not on this restriction). | 03 | Delete the bullet at syntax-core.tex:598-604 and the DECIDED comment at 605-606. Optionally add to the comment on r:s-pat-con (static-core, owner 04): "Thus a constructed pattern with too few or too many arguments does not elaborate." |
| Y8 | Minor | appendix-derived-forms.tex:33-35, 168-170 | B4 | The list-pattern row is defined by itself (its equivalent form contains a list pattern with one element fewer), which B4 forbids ("No cycles"); the text admits it as "the one exception". The list-expression row already gives a direct form. | 03 | Give the equivalent form directly: `[pat1, ..., patn]` => `( pat1 :: ( pat2 :: ... ( patn :: [ ] ) ... ) )` (n >= 1), each `::` the bare pattern; delete the sentence at 33-35 that states the exception. |
| Y9 | Minor | appendix-dynamic-basis.tex:523-526, 680-682; appendix-implementation.tex:303-306 | A4 (A65) | Appendices D and E disagree on `sqrt`. Appendix D puts `sqrt` with `+ - * /` among the operations that "allow no such latitude" (correctly rounded). Appendix E, restating A65, says every Float operation other than `+ - * /` and the comparisons has implementation-dependent accuracy, which includes `sqrt`. | 05 (and 01 if A65 is amended) | Keep Appendix D (IEEE 754 requires a correctly rounded square root) and change Appendix E 303-306 to "Float operations other than +, -, *, /, \kw{sqrt}, \kw{negate} and the comparisons ...". Record the refinement in A65's ruling text. |
| Y10 | Minor | static-modules.tex:287-288; effects.tex:700-701; programs.tex:164-166, 181-182 | A7 (Hard Constraint 3), D8 | The body names an implementation and describes what implementations do: "an extension of eco" (static-modules table), "An eco extension that admits Bytes" (effects), "An eco extension admits a further type of flags" (programs), and "The implementations detect such a clash only when the program starts" (programs, comment on r:p-stat-module). D8 confines such facts to Appendix E; static-modules.tex:584-588 already shows the neutral form. | 04 | static-modules.tex:287-288: "not in Standard Elm (Appendix E)". effects.tex:700-701: "Extensions of some implementations that admit \kw{Bytes} are recorded in Appendix E." programs.tex:181-182: "Some implementations admit further types of flags (Appendix E)." programs.tex:164-166: delete "The implementations detect such a clash only when the program starts;" and keep "such a program does not elaborate". |
| Y11 | Minor | effects.tex:32-33, 72-74, 80-82; syntax-modules.tex:327; static-modules.tex:582 | A7 (Hard Constraints 2 and 5) | "host" is used throughout Chapters 8 and 9 and is never defined. "platform" is defined only in programs.tex:38, after its uses in Chapters 3, 5 and 8. syntax-modules.tex:327 and static-modules.tex:582 say "effect manager", where the registered name (class Manager, effects.tex:327) is "manager". | 04 (effects, static-modules), 03 (syntax-modules) | In effects.tex sec:effects-simple, at the first use, define both: "A program runs on a \emph{platform}, which performs its commands, and exchanges JSON values with its \emph{host}, the environment outside the program that sends values to its incoming ports and receives those of its outgoing ports." Remove the later \emph{platform} at programs.tex:38 or turn it into a back reference. Replace "effect manager" by "manager of the platform (Chapter ch:effects)" at syntax-modules.tex:327 and static-modules.tex:582. |
| Y12 | Minor | dynamic-core.tex:129, 451, 465, 606; appendix-dynamic-basis.tex:453, 782; appendix-implementation.tex:998 | A7 (Hard Constraints 2 and 5; Terminology) | "well-typed program/phrase" and "a type error" are used but never defined; the book's term is that a phrase elaborates (dynamic-core.tex:31 already states the assumption that way). | 04, 05 | Replace "in a well-typed program" by "in a program that elaborates" (and "only well-typed phrases are evaluated" by "only phrases that elaborate are evaluated"); in the Appendix E divergence table replace "a type error" by "does not elaborate". |
| Y13 | Minor | effects.tex:652; static-modules.tex:284-290 | D11 | The two "what can and cannot be sent" tables classify `Bytes` differently: Chapter 5 gives it its own row ("not in Standard Elm"), Chapter 8 lists it among "any other abstract type" of the basis, but `Bytes` is not a type name of the initial basis (T_0, Appendix C). | 04 | effects.tex:652: remove `\kw{Bytes}` from the abstract-type row and add a row "\kw{Bytes} & no & & (not in Standard Elm; Appendix E)", matching Chapter 5. |

## Rulings and Directions

| Ruling | Status | Where |
|--------|--------|-------|
| A1 | reflected | syntax-core (lexis, adjacency), appendix-implementation |
| A2 | reflected | syntax-core |
| A3 | reflected | syntax-core |
| A4 | MISSING | Y1 |
| A5 | reflected | syntax-core (layout) |
| A6 | reflected | syntax-core (layout, lexis) |
| A7 | reflected | syntax-core, dynamic-core |
| A8 | reflected | syntax-core, appendix-implementation |
| A9 | reflected | syntax-core, dynamic-core, appendix-implementation |
| A10 | reflected | syntax-core, syntax-modules |
| A11 | reflected | syntax-core (kernel syntax out of scope) |
| A12 | reflected | syntax-core (grammar) |
| A13 | reflected | syntax-core, appendix-implementation |
| A14 | reflected | syntax-core, appendix-implementation |
| A15 | reflected | syntax-core |
| A16 | reflected | syntax-core, syntax-modules, appendix-derived-forms, programs |
| A17 | reflected | syntax-core, syntax-modules |
| A18 | reflected | static-modules, effects, appendix-implementation |
| A19 | reflected | static-core, appendix-static-basis |
| A20 | reflected | static-core |
| A21 | reflected | static-core |
| A22 | reflected | static-core |
| A23 | reflected | static-core |
| A24 | reflected | static-core, static-modules |
| A25 | reflected | syntax-modules, dynamic-core, dynamic-modules, programs |
| A26 | reflected | syntax-core, syntax-modules, static-core, dynamic-core, dynamic-modules |
| A27 | reflected | static-core, dynamic-core, programs (consistency of the three is open question 5, not audited here) |
| A28 | reflected | syntax-modules, static-modules, dynamic-modules |
| A29 | reflected | static-modules |
| A30 | reflected | syntax-modules, appendix-derived-forms, programs |
| A31 | reflected | static-core |
| A32 | reflected | static-modules, programs |
| A33 | reflected | static-modules, programs, appendix-implementation |
| A34 | reflected | syntax-core, static-modules, appendix-implementation |
| A35 | reflected | static-core, appendix-static-basis |
| A36 | reflected | static-core |
| A37 | reflected | syntax-core, syntax-modules, appendix-static-basis |
| A38 | reflected | syntax-modules, static-modules, dynamic-modules |
| A39 | reflected | appendix-implementation |
| A40 | reflected | dynamic-core, appendix-dynamic-basis, appendix-implementation |
| A41 | reflected | appendix-dynamic-basis, appendix-implementation |
| A42 | reflected | appendix-dynamic-basis, appendix-implementation |
| A43 | reflected | appendix-dynamic-basis, appendix-implementation |
| A44 | reflected | appendix-dynamic-basis, appendix-implementation |
| A45 | reflected | appendix-dynamic-basis, appendix-implementation (boundary case: Y5) |
| A46 | reflected | appendix-dynamic-basis, appendix-implementation |
| A47 | reflected | appendix-dynamic-basis, appendix-implementation |
| A48 | reflected | appendix-dynamic-basis, appendix-implementation |
| A49 | reflected | appendix-dynamic-basis, appendix-implementation |
| A50 | reflected | dynamic-core, appendix-dynamic-basis, appendix-implementation |
| A51 | reflected | dynamic-core, appendix-dynamic-basis, appendix-implementation |
| A52 | reflected | syntax-core, dynamic-core, appendix-dynamic-basis, appendix-implementation |
| A53 | reflected | appendix-dynamic-basis, appendix-implementation |
| A54 | reflected | appendix-implementation (outside the basis) |
| A55 | reflected | appendix-implementation (outside the basis) |
| A56 | reflected | syntax-core, appendix-derived-forms, dynamic-core, appendix-static-basis, appendix-dynamic-basis |
| A57 | reflected | dynamic-core, appendix-derived-forms |
| A58 | reflected | dynamic-core, dynamic-modules, appendix-derived-forms |
| A59 | reflected | dynamic-modules, programs (correctness of the thunk translation is open question 4, not audited here) |
| A60 | reflected, with exceptions | appendix-dynamic-basis; arrays and `Task.command` departures: Y3, Y4 |
| A61 | reflected | dynamic-core, appendix-implementation |
| A62 | reflected | dynamic-core, appendix-dynamic-basis, appendix-static-basis, programs |
| A63 | reflected | dynamic-core, appendix-implementation |
| A64 | reflected | appendix-implementation (outside the basis) |
| A65 | reflected, inconsistent | appendix-dynamic-basis vs appendix-implementation on `sqrt`: Y9 |
| A66 | reflected | effects, programs, appendix-implementation |
| A67 | reflected | effects, programs, appendix-implementation |
| A68 | reflected | programs, appendix-implementation |
| A69 | reflected | programs, appendix-implementation |
| A70 | reflected | programs, appendix-implementation |
| A71 | reflected | effects, programs, appendix-implementation |
| A72 | reflected | programs, appendix-implementation |
| A73 | reflected | effects, appendix-implementation |
| A74 | reflected | effects, appendix-implementation (non-finite floats unlogged and unrecorded: Y5, Y6) |
| A75 | reflected | effects, appendix-implementation |
| A76 | reflected | effects, appendix-implementation |
| A77 | reflected | effects, programs |
| A78 | reflected | effects, programs, appendix-implementation |
| A79 | reflected | effects, programs, appendix-implementation |
| A80 | reflected | effects, programs, appendix-implementation |
| A81 | reflected | effects, programs, appendix-implementation |
| A82 | reflected | programs, dynamic-modules, appendix-static-basis |
| A83 | reflected | effects, programs, appendix-implementation |
| A84 | reflected | syntax-modules, static-modules, programs |
| A85 | reflected | effects, programs |
| A86 | reflected | programs, appendix-implementation |
| A87 | reflected | dynamic-core (sec:dynamic-core-numbers), appendix-dynamic-basis |
| D1 Form | reflected | whole book; preface, appendix-standard-ml |
| D2 No exceptions | reflected | dynamic-core (sec:dynamic-core-rules), dynamic-modules, effects, programs |
| D3 Total arithmetic | reflected | appendix-dynamic-basis (fig:dynamic-basis-int: `3 // 0` is 0; float, conversion and order figures total) |
| D4 Basic maths in the definition | reflected | appendix-dynamic-basis (APPLY for every basic value, displayed) |
| D5 Row-polymorphic records | reflected | static-core (RecType, substitution, r:s-atexp-update, r:s-atpat-record, r:s-ty-openrecord); appendix-derived-forms (accessor, selection) |
| D6 Simple modules | reflected | static-modules, dynamic-modules |
| D7 Otherwise as ML | reflected | whole book; appendix-standard-ml |
| D8 Implementation details in an appendix | reflected, with lapses | appendix-implementation; body mentions of eco: Y10 |
| D9 Sources | not applicable | a direction for the survey, not for the text |
| D10 Cmd, Sub, Task | reflected | effects (Chapter 8); `Task.perform` gap: Y3 |
| D11 Ports | reflected, with inconsistencies | static-modules sec:static-modules-ports, effects sec:effects-ports, appendix-implementation; Y5, Y6, Y13 |

## Coverage Notes (no finding)

- R3: every production of fig:core-grammar-expressions, fig:core-grammar-patterns, fig:core-grammar-types, fig:grammar-modules and fig:grammar-top-level-declarations has a static rule (or is covered by Expose for a header's exposing list); every production that survives reduced syntax has a dynamic rule. Program has rules in both phases.
- Survey constructs: every construct of the survey's "Phrase Classes" is a bare production, a derived form, or out of scope (GLSL, `infix`, `effect module`, kernel imports), except the A4 restriction (Y1).
- B4: every equivalent form is bare or uses earlier rows, except the list-pattern row (Y8).
- I2: every identifier of the survey's "Initial Basis" (types, Basics values and fixities, Debug, Platform.worker, Cmd/Sub, Task, Process) is in Appendix C and Appendix D, module by module; the shape of the dynamic interfaces is wrong (Y2), and the hidden values `Array.fromList`, `Array.toList`, `Task.command`, `Elm.Kernel.Basics.log` are basic values of Appendix D bound to no identifier, which I2 permits.
- Hard Constraint 4 (pedagogy): no "let us", "recall", exercises or tutorials in the body; "Note that" occurs twice in static-core in the exemplar's manner.
- Terminology: no "type check", "compile", "sugar", "AST", "node", "judgement instance" or "guard" in the body. "Execution" and "runs" for the program loop of Chapter 9 follow the plan (sec:programs-execution) and are not the evaluation phase.

## Open Questions

- 3 (Array.fromList/toList): real; findings Y4 (effects comments contradict Appendix D). Appendix C rightly omits the two values, since they are bound to no identifier.
- 8 (constructor-pattern arity as a syntactic restriction): real; finding Y7.
- 9 (NaN/Infinity as null, JSON numbers as decimal rationals): Chapters 5 and 8 agree with each other (apart from Y13); Appendix E does not record Elm/JS's non-conformance (Y5), and the decisions are unlogged (Y6).
