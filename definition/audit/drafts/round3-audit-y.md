# Audit Part Y (A3 Coverage, A4 Rulings, A7 Voice), 2026-11-10

Scope: uncommitted changes to definition/tex and definition/survey/ambiguity-log.md
(A27 revision and clarification, A56 confirmation, A87, A93 revised; A94 to A97 new),
then a light pass over the rest. Read-only; every finding below was checked against
the source at the line given.

## Findings

| ID | Severity | File:line | Check | Finding |
|----|----------|-----------|-------|---------|
| Y1 | Blocker | appendix-implementation.tex:176-184 | A4 (A27) | Int-era claim now false |
| Y2 | Major | programs.tex:190-195 | A4 (A96, A27) | Example `main` does not elaborate by A96 |
| Y3 | Major | appendix-implementation.tex:34-41, 644-665; programs.tex:564-567, 666-673 | A4 (A94, A56, A87) | Appendix E conformance in terms of "value" disagrees with Chapter 9's trace conformance |
| Y4 | Major | static-core.tex:466-469, 529-532; programs.tex:210-218 | A4 (A96) | "Elaborates" for a program not defined consistently |
| Y5 | Minor | appendix-implementation.tex:637-638, 1103-1105 | A4 (A27, A62) | A27 example relies on implementation-dependent Debug.toString |
| Y6 | Minor | appendix-implementation.tex:129-135; preface.tex:184-186 | A4 (A27, A43) | Power examples not marked "at Int" |
| Y7 | Minor | appendix-implementation.tex:644, 663 | A4 (A87, A27) | "differ only where" and "All three conform" inaccurate |
| Y8 | Minor | dynamic-core.tex:109-115 | A7 (HC3) | Implementation talk in the body |
| Y9 | Minor | static-core.tex:459-461 | A7 (HC1) | "might" twice |
| Y10 | Minor | static-core.tex:482, 485; appendix-implementation.tex:41 (and older: effects.tex:374, appendix-dynamic-basis.tex:459, appendix-implementation.tex:451) | A7 (HC2) | Ruling numbers printed in the text |
| Y11 | Minor | static-core.tex:11; dynamic-core.tex:8; ambiguity-log.md:307; architecture/book-plan.md:113 | A4 hygiene | Stale planning comments and log metadata for A27/A95 |
| Y12 | Minor | static-core.tex:438-440, 459-462, 899-905; dynamic-core.tex:69-72, 109-118; programs.tex:210-218 | A7 (HC4) | New examples outside Comments |

### Y1 (Blocker) Appendix E: "same meaning in every implementation" is false under the Float default

appendix-implementation.tex:176-184:

> A program whose exact Int results, quotients and conversions from Float all lie
> between -2^31 and 2^31-1, and which applies neither modBy 0, remainderBy 0 nor Int ^
> with a negative exponent, has the same meaning in every implementation listed here,
> apart from the sign of a zero seen through toFloat.

Since A27 (revised), a `number` variable that nothing fixes is Float in the definition, while
eco closes it to Int (the book itself says so at appendix-implementation.tex:632-640 and
1103-1105). So `x = if 2 ^ -1 == 0 then 1 else 2` (or `2 ^ 60 + 1`) meets every hypothesis
(the definition applies Float `^`, no Int results) yet eco gives a different value. The
sentence was true only while the default was Int.

Fix: add a hypothesis, for example "and in which every type variable of class number is
fixed (eco closes one that nothing fixes to Int, Section numbers)", or add "except for eco
where a number variable is left for the default" with a reference to
sec:appendix-implementation-numbers.

### Y2 (Major) programs.tex: the A27 example `main` does not elaborate by A96

programs.tex:190-195 (Comment on r:p-stat-main-program):

> with \kw{init = \textbackslash\_ -> (0, Cmd.none)} and no other constraint on the model,
> the model type is $\tFloat$, and the value of \kw{main} is that of its default copy, at
> $\tFloat$

The paragraph added for A96 at programs.tex:210-218 says that an unannotated
`main = Platform.worker { init = \_ -> (0, Cmd.none), ... }`, "whose init ignores its flags,
does not elaborate": the principal scheme leaves the flags a type variable, and
`Port(tau_1)` fails on `Dflt sigma`. The example 20 lines earlier uses the same `init`, so
either `main` is annotated (which the text does not say, and which then would also fix the
model unless written `Program () number msg`), or the example program is illegal.

Fix: write `init = \() -> (0, Cmd.none)` (flags fixed to unit, model still a free `number`).

### Y3 (Major) A94 stated per value; Chapter 9's conformance is per trace

Appendix E introduction (appendix-implementation.tex:34-41), added for A94:

> The requirements concern the programs to which the definition gives a value. Where a
> program elaborates and the definition gives it a value, a conforming implementation's
> result is one of its values; where the definition gives it none ... the definition
> requires nothing ... So Elm/JS, for which (&&) False (Debug.todo "x") is False where the
> definition gives no value (A56), conforms there. % A94

and the A56 row was removed from the divergence table (diff of appendix-implementation.tex,
old lines 1029-1031).

But the body defines conformance for a worker program by traces (programs.tex:666-673:
"for every program that has a meaning ... every trace that the implementation can produce
... is a member of Tr(program, j)"), and when `update` has no result the program keeps its
meaning and simply handles no further message (programs.tex:564-567, Comment on
r:p-update). So a program whose `update`, on some message, evaluates
`(&&) False (Debug.todo "x")` has a meaning; the definition handles no further message,
Elm/JS evaluates the prefix `(&&)` lazily and goes on handling messages and sending port
values. Those traces are not in Tr, so Elm/JS does not conform by Chapter 9, while
Appendix E says it conforms and no longer lists the divergence. The same holds for the
`let` row of the A87 table (appendix-implementation.tex:651-663: "All three conform") when
the `let` is inside `update`.

A94's ruling text ("Where a program elaborates and the definition gives it a value ...")
is phrased for programs as wholes; it does not say how a program whose meaning is a set
of traces is treated when one step has no result.

Fix (needs an author decision, see Q1): either (a) extend the conformance definition in
programs.tex (sec:programs-behaviour) so that, after a step of the definition's execution
that has no result, nothing further is required (and cite A94 there), or (b) narrow the
Appendix E sentence to top-level values and views, and restore an A56 (and A87 `let`)
divergence row for steps inside `update`, `subscriptions` or a task.

### Y4 (Major) What "a program elaborates" means

- static-core.tex:529-532: "A phrase elaborates to A' when some derivation of the sentence
  exists".
- static-core.tex:466-469: "The rules for modules and programs only combine the derivations
  for their declarations, so a principal derivation for a program is made of principal
  derivations for its modules".
- programs.tex:210-218: the unannotated `main` with `init = \_ -> ...` "does not elaborate,
  although a derivation that took the flags to be () would satisfy the rule".

r:p-stat-main-program adds the side condition `Port(tau_1)` on `Dflt sigma`, which a more
general derivation can fail while an instance satisfies it. So the program rules do more
than combine derivations, and for this program a derivation for the program exists (by the
static-core reading it elaborates) while the book says it does not. Read literally, the
static-core Property ("Every ... program that elaborates has a principal derivation") is
then false for it: its program derivations (flags `()`, `Int`, `String`, ...) have no
common generalisation that is itself a program derivation.

The intent (A96) is clear: program elaboration uses the modules' principal derivations.
Fix: in programs.tex, state it as the definition ("A program elaborates when the principal
derivations of its modules satisfy the rules of this section"), and in static-core.tex:466-469
restrict the sentence to modules, saying that for a program the principal derivation is
the combination of its modules' principal derivations, which the program rules then judge.

### Y5 (Minor) The A27 example uses Debug.toString

appendix-implementation.tex:637-638 and 1103-1105 give the definition's result of
`Debug.toString (2 ^ -1)` as `"0.5"`. By appendix-dynamic-basis.tex:1131-1136 and A62 the
string of `Debug.toString` is implementation-dependent, so the definition does not give
`"0.5"`; it gives the float 0.5. Fix: use an observable Bool, for example
`2 ^ -1 == 0` (definition and Elm/JS `False`, eco `True`), or say "the float 0.5".

### Y6 (Minor) Power examples not marked "at Int"

With Float the default, an unannotated `2 ^ -1` or `1 ^ -1` is Float in the definition.
- appendix-implementation.tex:129-130: "Elm/JS & The real power, held as an Int:
  \kw{2 ^ -1} is \kw{0.5}" and :134-135 "eco ... \kw{1 ^ -1} is $0$, not $1$". The
  section is about Int, but the examples read as unannotated expressions (and unannotated,
  Elm/JS's `0.5` now conforms).
- preface.tex:184-186: "on eco, a negative power of \kw{-1} or \kw{1} is \kw{0} where the
  definition gives \kw{1} or \kw{-1}". Not marked Int; also the "respectively" order is
  wrong (the power of 1 is 1; that of -1 is 1 or -1 by parity).
Fix: add "at Int" (or annotate) in each, and reword the preface pairing.

### Y7 (Minor) Wording in the Number Specialisation subsection

- appendix-implementation.tex:644: "The implementations differ only where a copy that the
  program does not need has no value." The table just above records that eco also differs
  wherever a `number` variable is left free. Fix: "On copies, the implementations differ
  from the definition only where ...".
- :663 "All three conform." The three columns are the definition, Elm/JS and eco; the
  definition does not conform to itself. Fix: "Both implementations conform" (subject to Y3).

### Y8 (Minor) Implementation talk in Chapter 6

dynamic-core.tex:109-115: "The default copy computes what an implementation with a single
representation of numbers computes ... as when \kw{x} is evaluated once with floats."
Hard Constraint 3 and audit Y10 (no implementation behaviour described in the body).
Fix: drop the first sentence and the clause "as when x is evaluated once with floats", or
move the observation to Appendix E sec:appendix-implementation-numbers.

### Y9 (Minor) "might"

static-core.tex:459-461: "allows a derivation to give a binding a less general scheme than
it might, as when ... is given the type Int where it might have the scheme ...". It is about
derivations, not the language, but HC1 lists "might". Fix: "than another derivation gives
it, as when ... is given the type Int where another derivation gives it the scheme ...".

### Y10 (Minor) Ruling numbers printed in the text

New: static-core.tex:482 "The labels of a row are distinct (A23)", :485
"(rule~\ruleref{r:s-dec-group}; A24)", appendix-implementation.tex:41 "value (A56),
conforms there". The ambiguity log is not part of the book, so a reader meets an undefined
reference (HC2); the book's convention is `% A<n>` comments. Older instances not raised in
the last audit: effects.tex:374 "(A84)", appendix-dynamic-basis.tex:459 "(A38)",
appendix-implementation.tex:451 "(A50)". Fix: move each to a `%` comment, replacing the
parenthesis by a section reference where one helps (static-core A23: sec on rows;
A24: rule r:s-dec-group alone).

### Y11 (Minor) Stale metadata (not printed)

- static-core.tex:11 header: "defaulting of number (A27)" listed under this chapter's
  evidence; it now lives in dynamic-core (A95). dynamic-core.tex:8 header cites A87, A27
  but not A95.
- ambiguity-log.md:307: A27 "Affects: static"; after the clarification it is applied in the
  dynamic semantics (sec:dynamic-core-numbers): "static, dynamic".
- architecture/book-plan.md:113: "unresolved `number` defaults to Int at top level (A27)"
  and line 5 "rulings (A1 to A86)". Outside the book, but the plan is the stage-04 brief.
- typeset/build-report.md still names core-number-default (generated; regenerates on build).

### Y12 (Minor) Examples outside Comments (HC4)

The new text puts examples in the running prose: static-core.tex:438-440 (`2 ^ -1`),
459-462 (`y = 2 ^ 64 * 4`), 899-905 (`Result Never Int`, `Maybe Never`); dynamic-core.tex:69-72
(`f : number -> number`), 109-118 (`check`); programs.tex:210-218 (unannotated `main`).
The book already does this elsewhere (Appendix D "Thus ..." sentences) and the last audit
did not raise it, so this is recorded for the author's decision rather than as a defect.

## Questions (uncertain; not findings)

- Q1 (A94 scope). Does "a program it gives no value" cover a worker whose `update`,
  `subscriptions` or a task reaches `Debug.todo` at some step (the program has a meaning,
  but its execution stops handling messages)? The answer decides Y3.
- Q2 (Terminology). static-core.tex:446-451 uses "node" for a node of a derivation. The
  Terminology table bans "node" for a phrase; this use is defined in the sentence and is
  about derivations. Acceptable?
- Q3 (HC3). static-core.tex:484-487: "the inference algorithm of Damas and Milner, extended
  in these ways, finds a principal derivation". A pointer to theory, not to a compiler;
  acceptable in the body?
- Q4. static-core.tex:850-851: "every derivation, and every number specialisation of one,
  gives the same answer". Number specialisation is defined on a program (after the default
  on the principal derivation), not on an arbitrary derivation; does "specialisation of one"
  mean "the derivation after the default and copying"?

## Checked and found consistent

- A27 (revised): no remaining text in any chapter or appendix gives Int as the default.
  `res:core-number-default` is gone with no dangling `\ref`/`\citelabel` in tex/. Float is
  used at dynamic-core.tex:57-75, 82, 93, 108; programs.tex:135-146, 190-195, 228-238;
  static-core.tex:430, 452-456; appendix-dynamic-basis.tex:199-203, 520-540, 627
  ("at Int" added); appendix-standard-ml.tex:116-119; Appendix E 609-664, 1103-1105.
  Worked examples recomputed: `inc (7 // 2)` = 4; `abs (3 // -1)` = 3; `abs -1.5` = 1.5;
  `check`/`x` in dynamic-core (Int copy 0, Float copy no value) and in Appendix E (Int copy
  no value, Float copy 0.5, `x + 0.5` = 1); `clamp 10 0 5` = +0 at Float (Appendix D 725)
  and 10 at Int (Appendix E 317-319). The clarification (annotation-bound variables are
  not defaulted, quantifier forall U' of r:s-valbind-var) is at dynamic-core.tex:57-73 with
  the `f : number -> number` example, which is correct.
- A56: infix forms are derived conditionals (appendix-derived-forms.tex:144-148, 55-65);
  prefix values strict (dynamic-core.tex:434-442; appendix-dynamic-basis.tex:1094-1105;
  appendix-static-basis.tex:377-380). The A56 divergence row is removed per A94 (but see Y3).
- A87: default copy at Float, other copies bind new variables, every declaration copied
  (dynamic-core.tex:76-125; dynamic-modules.tex:74-79; Appendix D abs; programs Dflt).
- A93: closure over the group's number variables (static-core.tex:421-430), default Float
  (dynamic-core.tex:89-94).
- A95: principal derivation section (static-core.tex:432-504), defaulting moved to the
  start of number specialisation, r:s-atexp-scon Comment updated.
- A96: static-core intro (29-34), further restrictions (842-856), static-modules.tex:583-588,
  programs.tex:210-218, Appendix F row (appendix-standard-ml.tex:71-78).
- A97: coinductive inhabitants and the Never/V examples (static-core.tex:881-896); Never's
  constructor JustOneMore matches appendix-static-basis.tex:111, 269.
- A4 mechanical: every ruling A1 to A97 has a `% A<n>` citation in a comment after the
  chapter heading (not only in the planning header); no citation of a ruling above A97.
- A3 light: Core static rules cover every bare production (45 rules); dynamic rules cover
  every production surviving the reduced syntax; derived forms appear in an order in which
  each equivalent form is bare or earlier (if before &&, ||); the 88 value identifiers of
  Appendix D are exactly those of Appendix C (the 18 Appendix C-only entries are types).
  Grammar, derived-forms and static-basis files are unchanged since the last audit.
- A7: no `---` and no U+2014 in tex/ or in the ambiguity log; hedging words only "usually"
  about metavariables (introduction.tex:130-131, static-core.tex:512-513) apart from Y9;
  no banned Terminology term in the new text (Q2 aside); no Elm, eco or JavaScript named
  in the changed body text.
