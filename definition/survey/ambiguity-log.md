# Ambiguity Log

Rulings marked **provisional** were made by the agent while running the pipeline without stopping, applying the Author Directions (D1 to D11 in `book-brief.md`). Each records its reason; the authors may overturn any of them, and the stage that owns the affected text then reruns.

Principles applied: Standard Elm is Elm 0.19.1 as intended; eco-only extensions and limits go to the implementation appendix; implementation-dependent points become abstract parameters (D8); nothing in the body fails at run time (D2, D3); platform timing gets the weakest guarantee both implementations meet.

## A1: Whitespace inside `()`
- **Origin:** C-SYN-1
- Construct: unit in expressions, patterns, types.
- Question: Is `( )` (or `({- c -})`) a unit?
- Implementation: patterns accept it (`Pattern.elm:251-262`); expressions take the unit branch only when nothing follows `(` directly, otherwise require an expression (`Expression.elm:246-264,312-313`); types take `()` only with `)` immediately (`Type.elm:99-101`).
- Notes: silent.
- Options: (a) record the inconsistency as is; (b) define unit as `()` with no gap everywhere and treat the pattern case as a parser leniency; (c) allow a gap everywhere.
- **Ruling:** INTENT: unit is the two characters `()` with nothing between, in expressions, patterns and types. A gap inside the parentheses of a pattern is an implementation leniency. (provisional)
- **Reason:** One lexical form everywhere; the leniency adds nothing a program needs.
- **Affects:** syntax

## A2: Reserved words as the last part of a qualified name
- **Origin:** C-SYN-2
- Construct: qualified variables.
- Question: Is `List.if` lexically a qualified identifier?
- Implementation: only unqualified names are checked against reserved words (`Variable.elm:17-19,336-349`); `M.if` parses as `VarQual` and fails later as not found.
- Notes: silent.
- Options: (a) lexical rule excludes reserved words in every position; (b) only unqualified; the qualified case is a scope error.
- **Ruling:** INTENT: reserved words are excluded from every component of a qualified identifier. (provisional)
- **Reason:** The implementation already rejects such programs (as an unbound name); a lexical rule says so directly.
- **Affects:** syntax

## A3: Maximal munch over `-` and `--` in operators
- **Origin:** C-SYN-3
- Construct: operator lexing; negation; comments.
- Question: Does `a*-b`, `2^-1` or `x +--c` lex as one operator?
- Implementation: an operator is the longest run of operator characters, read whole (`Symbol.elm:12-16,126-132`); `--` starts a comment only where a gap is read (`Space.elm:264-274`). So `*-`, `^-`, `+--` are single (unknown) operators.
- Notes: silent.
- Options: (a) record maximal munch exactly; (b) split a trailing `-`/`--` off an operator run.
- **Ruling:** IMPLEMENTATION: an operator symbol is the longest run of symbol characters (maximal munch), and `--` inside such a run does not start a comment. (provisional)
- **Reason:** Matches both implementations and the exemplar's longest-match lexical rule.
- **Affects:** syntax

## A4: Which terms admit `.field`, and `.f.g`
- **Origin:** C-SYN-4
- Construct: field access, accessor.
- Question: Which expressions may be followed by `.f`, and what is `.x.y`?
- Implementation: access follows only a variable, a record/update, or a `(`-form (parens, tuple, unit, even `(op)`) (`Expression.elm:65-81`); an accessor is not followed by access, so `.x.y` parses as the application `(.x) (.y)` and `"s".x` as `"s" (.x)` (`Expression.elm:119-126,591-614`).
- Notes: silent.
- Options: (a) grammar exactly as implemented; (b) access on any atomic expression; (c) `.x.y` as a composed accessor.
- **Ruling:** IMPLEMENTATION: field access may follow only a value identifier, a record expression, a record update or a parenthesised form; `.x.y` is the application of `.x` to `.y`. (provisional)
- **Reason:** Record what the parser accepts; no program needs more.
- **Affects:** syntax

## A5: Layout measures token start columns, not ends of multi-line tokens
- **Origin:** C-SYN-5
- Construct: layout rule with `"""` strings.
- Question: Is a token that continues a construct judged by its own start column even when the previous token ended at a low column on a later line?
- Implementation: every check uses the current column only (`Space.elm:115-131`); `"""` closing in column 1 then `++` in column 5 inside a let definition at column 9 ends the definition and fails at `in`.
- Notes: Elm 0.19.1 rejects the same program; the test treats it as a bug (`test/elm-bugs/src/CompilerIssue1947MultilineStringInLetBinopTest.elm`).
- Options: (a) layout by start column only (implementation and Elm); (b) exempt tokens on the line where a multi-line token ends.
- **Ruling:** IMPLEMENTATION: layout compares the start column of each token only. (provisional)
- **Reason:** Elm 0.19.1 and eco agree.
- **Affects:** syntax

## A6: What a column is
- **Origin:** C-SYN-6
- Construct: layout.
- Question: How are columns counted for non-ASCII, astral characters and CR?
- Implementation: one column per code point (surrogate pair = 1) in identifiers, strings, comments (`Primitives.elm:19-27`, `Identifier.elm:33-36`, `String.elm:149-160`); CR in whitespace counts 0 (`Space.elm:276-277`) but in block comments counts 1 (`Space.elm:380-381`); tabs are illegal in whitespace.
- Notes: silent.
- Options: (a) code points, CR ignored; (b) UTF-16 units; (c) bytes; (d) grapheme clusters.
- **Ruling:** IMPLEMENTATION: a column counts characters (code points) from the start of the line; tab characters may not appear in layout whitespace; a carriage return occupies no column. (provisional)
- **Reason:** Fixes the measure the layout rule needs; byte or UTF-16 counts would make layout depend on encoding.
- **Affects:** syntax

## A7: Negative literal patterns
- **Origin:** C-SYN-7
- Construct: literal patterns.
- Question: Is `-1 -> ...` a legal case branch?
- Implementation: no `-` alternative in pattern terms; a number must start with a digit (`Pattern.elm:80-132`, `Number.elm:12-14`), so it is a syntax error.
- Notes: silent (eco's `Pattern.elm` mirrors upstream's structure; to confirm against elm/compiler `Parse/Pattern.hs`).
- Options: (a) no negative patterns; (b) allow `-` digit in Int patterns.
- **Ruling:** IMPLEMENTATION: there are no negative literal patterns. (provisional)
- **Reason:** Confirmed in Elm 0.19.1's own parser (compiler/src/Parse/Pattern.hs: the pattern term has no `-` alternative).
- **Affects:** syntax

## A8: Surrogate code points in `\u{...}`
- **Origin:** C-SYN-8
- Construct: escapes in Char and String literals.
- Question: Is `'\u{D800}'` a legal Char literal?
- Implementation: only values above `10FFFF` are refused (`String.elm:510-511`); the escape is re-encoded as `\uD800` (`String.elm:17-19`).
- Notes: lone surrogate values are a recorded runtime divergence (`test/eco-divergence/src/StringLoneSurrogateTest.elm`); the lexer is silent.
- Options: (a) allow (implementation); (b) restrict to Unicode scalar values.
- **Ruling:** INTENT: a `\u{...}` escape must denote a Unicode scalar value (surrogates excluded). Acceptance of surrogate escapes is recorded in the implementation appendix. (provisional)
- **Reason:** Characters are abstract in the body (direction D8); a surrogate is not a character.
- **Affects:** syntax

## A9: Int literals beyond 64 bits
- **Origin:** C-SYN-9
- Construct: Int special constant.
- Question: Is an Int literal outside the 64-bit range an error, or reduced modulo 2^64?
- Implementation: reduced modulo 2^64 as two's complement (`Number.elm:86-93`); on the JS host an inexact read is `NumberInexactOnHost` (`Number.elm:160-177`).
- Notes: Elm 0.19.1 also wraps; the test calls that a bug (`test/elm-bugs/src/CompilerIssue1246LargeIntLiteralTest.elm`); eco documents 64-bit Int (`design_docs/elm-divergence.md:12,32-60`).
- Options: (a) modulo 2^64 (implementation); (b) static error outside [-2^63, 2^64).
- **Ruling:** CUSTOM: an integer constant denotes a mathematical integer; its value as an Int is the integer normalised into the implementation's Int range by the same normalisation as Int arithmetic (an implementation parameter, see A40). (provisional)
- **Reason:** Keeps the width out of the body (D8) while giving every constant a value (D3).
- **Affects:** syntax

## A10: Doc comments as tokens
- **Origin:** C-SYN-10
- Construct: `{-| -}`.
- Question: Is a doc comment in an arbitrary position a comment or a syntax error?
- Implementation: a gap stops before `{-|` (`Space.elm:16-18,332-333`), so anywhere other than after the header or before a top-level declaration it is a parse error.
- Notes: silent.
- Options: (a) doc comments are tokens of the module grammar (implementation); (b) treat them as ordinary comments elsewhere.
- **Ruling:** IMPLEMENTATION: doc comments are items of the module grammar, legal only after the module header and before a top-level declaration. (provisional)
- **Reason:** Both implementations treat them so.
- **Affects:** syntax

## A11: Duplicate infix declarations
- **Origin:** C-SYN-11
- Construct: infix declarations (kernel only).
- Question: May one module declare the same operator twice?
- Implementation: collected with `Dict.fromList`, no duplicate check (`Canonicalize/Module.elm:109-111`); the surviving entry depends on list order.
- Notes: silent.
- Options: (a) error; (b) last wins; (c) out of scope with kernel syntax (C-SYN-16).
- **Ruling:** UNSPECIFIED: out of scope with all kernel-only syntax (A16). (provisional)
- **Reason:** User code cannot declare operators.
- **Affects:** syntax

## A12: Tuple arity in the grammar or as a restriction
- **Origin:** C-SYN-12
- Construct: tuples in expressions, patterns, types.
- Question: Should the grammar admit only 2- and 3-tuples, or all n >= 2 with a separate restriction?
- Implementation: parser accepts any n (`Type.elm:31-32`, `Expression.elm:327-361`); canonicaliser rejects n > 3 (`Canonicalize/Expression.elm:443-454`).
- Notes: `design_docs/theory/compiler/front-end.md:7` says eco keeps tuples at three.
- Options: (a) grammar n >= 2 plus restriction; (b) grammar with exactly 2 or 3.
- **Ruling:** INTENT: the grammar admits tuples of exactly two or three components (and unit). (provisional)
- **Reason:** A restriction that is purely about arity reads better as grammar.
- **Affects:** syntax

## A13: eco-only size limits
- **Origin:** C-SYN-13
- Construct: function/lambda parameters, closures, records, constructors.
- Question: Are the heap-layout limits (2047 params, 2047 fields, 2040 constructor fields, 1024 nullary constructors) part of the language?
- Implementation: canonicaliser `TooLarge` errors (`HeapLimits.elm:31-61`, `Canonicalize/Expression.elm:50-57`).
- Notes: documented as divergences from Elm, which has no such limits (`design_docs/elm-divergence.md:214-219`).
- Options: (a) implementation limits outside the Definition; (b) restrictions in the Definition.
- **Ruling:** UNSPECIFIED: size limits are implementation limits, listed in the implementation appendix, not part of the language. (provisional)
- **Reason:** Elm has none; eco's arise from its heap layout.
- **Affects:** syntax

## A14: Unicode version of identifier classes
- **Origin:** C-SYN-14
- Construct: identifiers.
- Question: Which Unicode version fixes Lu/Ll/Lt/Lm/Lo?
- Implementation: Unicode 14.0.0 tables (`Unicode.elm:1-12`).
- Notes: upstream depends on the GHC that built it (`Unicode.elm:8-11`).
- Options: (a) fix 14.0.0; (b) "some Unicode version", implementation-defined.
- **Ruling:** UNSPECIFIED: the Unicode version that classifies letters is an implementation parameter (eco: Unicode 14.0). (provisional)
- **Reason:** Implementation detail (D8).
- **Affects:** syntax

## A15: Closing `"""` among longer quote runs
- **Origin:** C-SYN-15
- Construct: multi-line strings.
- Question: How is `""""` at the end of a multi-line string read?
- Implementation: the first `"""` closes (`String.elm:362-367`); a fourth `"` then opens a new string literal.
- Notes: silent.
- Options: (a) first-match close (implementation); (b) last three quotes of the run close.
- **Ruling:** IMPLEMENTATION: the first `"""` closes a multi-line string. (provisional)
- **Reason:** As implemented in both.
- **Affects:** syntax

## A16: Kernel-only syntax and header-less files
- **Origin:** C-SYN-16
- Construct: `infix` declarations, `effect module`, `Elm.Kernel.*` references, files without a header.
- Question: Which of these belong to Standard Elm?
- Implementation: `infix` and effect modules only in kernel projects (`Module.elm:150-162,212-216,390-399`); kernel references only in kernel packages (`Canonicalize/Expression.elm:28-31`); header-less files are accepted and checked less (`Module.elm:28-29,314-330`) but cannot be imported (`test/elm-compile-errors/src/ErrorMessagesIssue103ImportedModuleWithoutModuleLineTest.elm`).
- Notes: silent.
- Options: (a) core language excludes kernel syntax, with an appendix; (b) include with a "kernel" side condition; (c) header optional only for the main module.
- **Ruling:** CUSTOM: kernel-only syntax (`infix` declarations, `effect module` headers, `Elm.Kernel` references) is outside Standard Elm; the fixities of the initial basis's operators are given in a table. A module without a header is allowed only as the main module and is a derived form of `module Main exposing (..)`. (provisional)
- **Reason:** User programs cannot use kernel syntax; the derived form captures header-less main modules exactly.
- **Amended by the author (2026-11-07):** every module has a header. A file without a `module`, `port module` header is not a module of Standard Elm; the derived form that read it as `module Main exposing (..)` is withdrawn. Both implementations reject such a file under `make` (`MODULE NAME MISSING`), which the earlier ruling overlooked: the survey read the parser, which accepts it, not the build, which does not.
- **Affects:** syntax

## A17: Annotation placement differs between top level and let
- **Origin:** C-SYN-17
- Construct: type annotations.
- Question: Must a top-level definition after its annotation start in column 1 while a let definition must align with its annotation, and may anything but comments come between?
- Implementation: top level `checkFreshLine` (`Declaration.elm:163`); let `checkAligned` (`Expression.elm:1288`); only a gap is read in between.
- Notes: silent.
- Options: (a) state both rules as layout instances (same rule: the definition starts at the annotation's column); (b) separate rules.
- **Ruling:** IMPLEMENTATION: in both places the definition must start in the column of its annotation; state it once as an instance of the layout rule. (provisional)
- **Reason:** One rule covers both.
- **Affects:** syntax

## A18: Bytes as a port payload and in flags
- **Origin:** C-STA-1
- Construct: `port p : Bytes -> Cmd msg`; `main : Program { b : Bytes } m msg`.
- Question: Is `Bytes.Bytes` a legal payload/flags type?
- Implementation: eco accepts `Bytes` in any payload position (C/Canonicalize/Effects.elm:260-263, :295-296); the native target accepts it only as the whole port payload and never in flags (C/LocalOpt/Error.elm:73-79; C/LocalOpt/Typed/Module.elm:167-200).
- Notes or Elm reference behaviour: tests state stock Elm rejects any `Bytes` port payload (T/eco-divergence/src/PortBytesEchoTest.elm:3-4; T/eco-divergence/src/FlagsBytesNativeTest.elm:7). This is not listed in DD/elm-divergence.md section 4.4.
- Options: (a) define Elm 0.19.1's set and treat Bytes as an eco extension; (b) include Bytes; (c) parameterise by target.
- **Superseded by A92** (author, 2026-11-07): Bytes is now a payload type.
- **Ruling:** INTENT: Bytes is not a port or flags payload type in Standard Elm. eco's acceptance is an extension, recorded in the implementation appendix. (provisional)
- **Reason:** Elm 0.19.1 rejects it (compiler/src/Canonicalize/Effects.hs).
- **Affects:** static

## A19: Constrained variables named by prefix
- **Origin:** C-STA-2
- Construct: `f : numberOfItems -> numberOfItems`.
- Question: Is any variable whose name starts with `number`/`comparable`/`appendable`/`compappend` constrained, or only those names followed by digits?
- Implementation: prefix test (C/Core/Name.elm:196-223; C/Type/Type.elm:439-452).
- Notes or Elm reference behaviour: silent in the guide; Elm 0.19.1 believed identical (Guida port, DD/theory/compiler/front-end.md:7).
- Options: (a) prefix rule; (b) exact name plus optional digits.
- **Ruling:** IMPLEMENTATION: a type variable is constrained if its name begins with `number`, `comparable`, `appendable` or `compappend`. (provisional)
- **Reason:** Elm and eco agree; core library documentation relies on names such as `comparableKey`.
- **Affects:** static

## A20: Rigid variable escaping its annotation
- **Origin:** C-STA-3
- Construct: `f x = let g : a -> a; g y = x in g x` (inner annotation variable unified with an outer flexible variable).
- Question: Is this a type error?
- Implementation: unifying a rigid with an outer-rank flexible variable succeeds and lowers the rank (C/Type/Unify.elm:535-570, :575-582); the rigid is then not generalised and the solver crashes with "You ran into a compiler bug" (C/Type/Solve.elm:30-31, :439-440, :459-483).
- Notes or Elm reference behaviour: silent; Elm 0.19.1 has the same check and is believed to crash the same way (unverified).
- Options: (a) specify as a type error (rigid variable escapes); (b) leave as an implementation fault.
- **Ruling:** INTENT: a type error (a rigid type variable may not escape its annotation). (provisional)
- **Reason:** The crash is an implementation fault, not a meaning.
- **Checked against Elm 0.19.1 (2026-11-08):** Elm 0.19.1 fails the same way. `f x = let g : a -> a; g _ = x in g 1` makes it report "You ran into a compiler bug" (`Type/Solve.hs:206`, `a [rank = 2]`). Neither implementation conforms; the divergence table lists both.
- **Affects:** static

## A21: Scoped type variables in nested annotations
- **Origin:** C-STA-4
- Construct: outer `f : a -> List a`, inner `let g : a -> List a`.
- Question: Does the inner `a` denote the outer `a`?
- Implementation: yes; only names not already in scope become new rigid variables (C/Type/Constrain/Typed/Expression.elm:128-143).
- Notes or Elm reference behaviour: silent in Elm docs.
- Options: (a) lexically scoped annotation variables; (b) each annotation closed.
- **Ruling:** IMPLEMENTATION: type variables of an annotation scope over the annotations nested inside its definition. (provisional)
- **Reason:** Both implementations do so.
- **Affects:** static

## A22: Occurs check only at let-bound names
- **Origin:** C-STA-5
- Construct: an expression whose type becomes cyclic without being reachable from any let-bound name.
- Question: When must an infinite type be rejected?
- Implementation: unification has no occurs check; the check runs on the types of the names each `let` binds after its body (C/Type/Solve.elm:33-34, :375-379, :452-454; C/Type/Occurs.elm:15-16).
- Notes or Elm reference behaviour: silent.
- Options: (a) HM occurs check on every unification; (b) the eco/Elm lazy check, defining which programs are rejected.
- **Ruling:** INTENT: types are finite; any program needing an infinite type does not elaborate. (provisional)
- **Reason:** A declarative type system has no infinite types; the lazy occurs check is an implementation strategy.
- **Affects:** static

## A23: Repeated field names through an extension variable
- **Origin:** C-STA-6
- Construct: `f : { r | x : Int } -> r -> Int` applied as `f { x = 1 } { x = "s" }`.
- Question: Can a row's extension be instantiated with a record that has a field of the same name (scoped labels)?
- Implementation: when gathering fields along an extension chain, the outermost occurrence wins (C/Type/Unify.elm:1207-1226), so the duplicate is silently shadowed rather than rejected; not tested.
- Notes or Elm reference behaviour: silent.
- Options: (a) rows have unique labels and the program is rejected; (b) scoped labels, outermost wins.
- **Ruling:** INTENT: a record row has unique labels; a row variable ranges over rows that lack the labels already present, so the example does not elaborate. Confirmed by the author, 2026-11-10.
- **Reason:** Scoped labels are not part of Elm's design and no test relies on them.
- **Affects:** static
- **Note (2026-11-10):** test CompilerIssue2182ExtensibleFunctionAliasCrashTest relied on scoped labels (`type alias Goal a = { a | field : Int } -> a` used as `Goal { field : Int }`, which Elm 0.19.1 accepts, the outer field winning). With the ruling confirmed it expects a compile error; Elm's acceptance is the divergence already recorded in Appendix E.

## A24: Typing of unannotated mutually recursive groups
- **Origin:** C-STA-7
- Construct: `f b = g b` and `g b = ... f False ...` using `f`'s result at two types.
- Question: Are unannotated members monomorphic within their group?
- Implementation: yes (shared variables, C/Type/Constrain/Typed/Expression.elm:184-197).
- Notes or Elm reference behaviour: Elm 0.19.1 generalises earlier members inside later ones and accepts some ill-typed groups that crash at run time (DD/elm-divergence.md:262-293); Elm also miscomputes interface annotations for later members (DD/elm-divergence.md:295-312).
- Options: (a) standard HM (eco); (b) Elm 0.19.1 behaviour (unsound).
- **Ruling:** IMPLEMENTATION (eco): unannotated members of a recursive group are monomorphic within the group (standard Hindley-Milner). (provisional)
- **Reason:** Elm 0.19.1's behaviour is unsound and documented as a bug.
- **Affects:** static

## A25: Top-level value forced through a delayed self-reference
- **Origin:** C-STA-8
- Construct: `x = let f _ = x in f ()`.
- Question: Is this rejected statically?
- Implementation: accepted, since the use of `x` is inside a `let` function body and so delayed (C/Canonicalize/Expression.elm:16-20; C/Canonicalize/Module.elm:400-411); evaluation then needs `x` while initialising `x`.
- Notes or Elm reference behaviour: silent; same rule believed in Elm 0.19.1.
- Options: (a) syntactic direct/delayed rule as implemented; (b) a semantic rule; (c) leave run-time behaviour to the dynamic semantics.
- **Ruling:** IMPLEMENTATION: the static restriction on recursive values is syntactic (direct versus delayed uses); a delayed self-reference that is forced during evaluation has no value (no evaluation rule applies). (provisional)
- **Reason:** Keeps the static rule as both implementations have it; the dynamic semantics says honestly that such a program has no meaning.
- **Affects:** static

## A26: Asymmetry between let and top-level recursion
- **Origin:** C-STA-9
- Construct: `let f = \n -> f n in f 1` versus top-level `f = \n -> f n`.
- Question: Why is the first rejected and the second accepted?
- Implementation: `let` cycles require every member to have parameters (C/Canonicalize/Expression.elm:1362-1394); top level only rejects cycles through direct uses (C/Canonicalize/Module.elm:400-423).
- Notes or Elm reference behaviour: silent.
- Options: (a) record both rules as implemented; (b) unify them.
- **Ruling:** IMPLEMENTATION: record both rules: in a `let`, every member of a recursive group must be a function with parameters; at top level, only cycles through direct uses of parameterless values are rejected. (provisional)
- **Reason:** As implemented in both.
- **Affects:** static

## A27: Unresolved `number`
- **Origin:** C-STA-10
- Construct: `main = text (Debug.toString (2 ^ 62 * 4))` with no constraint fixing `number`.
- Question: What type does an unconstrained `number` have at run time?
- Implementation: the checker leaves `number`; the native back end closes it to `Int` (DD/theory/compiler/front-end.md:54; DD/monomorphization/solver-reuse-evaluation.md:41).
- Notes or Elm reference behaviour: Elm's JS is untyped (numbers are doubles); silent in docs.
- Options: (a) default to Int; (b) default to Float; (c) leave polymorphic and let the dynamic semantics be representation-independent where possible.
- **Ruling:** CUSTOM: a `number` variable that nothing fixes is Float, and the default copy of number specialisation (A87) is the copy at Float. (provisional; revised 2026-11-10, author decision, from Int)
- **Reason:** Elm on JavaScript has one number representation, which behaves as Float, so with Float as the default the definition gives every program whose `number` is left free the value Elm 0.19.1 gives it; with Int, Elm 0.19.1 was non-conforming wherever such a computation took a negative power or passed 2^53 (A43, A87, A93). Every constant whose type is defaulted is an integer constant (a floating-point constant has the type Float itself), and every integer constant may be a Float, so no program loses a meaning. Against it: exact integer arithmetic and reflexive equality are lost for such code (`0 ^ -1` is an infinity, and NaN can arise), and the exemplar defaults overloading to int. eco closes a free `number` to Int and evaluates only the copies used, so it does not conform until its monomorphiser defaults to Float (Appendix E). The suite's checks were measured both ways: 4 of 1,477 differ, all in tests that now annotate at Int or expect the Float answer.
- **Superseded ruling:** an unconstrained `number` remaining in the type of `main` defaults to Int, as the native back end does, and as the exemplar defaults overloading to int.
- **Clarification (2026-11-10, author decision):** a variable bound by an annotation is not defaulted. The rule (static-core, res:core-number-default) had exempted only variables that a closure generalises, but an annotation's explicit variables are bound by the quantifier ∀U' of r:s-valbind-var, and closure never generalises an explicit variable in scope; read literally, the rule defaulted `number` in `twice : number -> number` to Float, which leaves no valid derivation, so programs using `twice` at Int were rejected (never given a wrong value). The rule now exempts variables bound by a closure (r:s-dec-group, r:sm-topdec-value) or by an annotation (r:s-valbind-var). The rule spoke of "a derivation", so a derivation that typed an integer constant at Int directly escaped it; A95 makes it apply to the principal derivation, and moves it from Chapter 4's further restrictions to the start of number specialisation (dynamic-core, sec:dynamic-core-numbers).
- **Affects:** static, dynamic
- **Correction (2026-11-10, review):** the default exempts also a parameter of a type declaration named `number` (bound by a type function, rules r:sm-datbind, r:sm-typbind, r:sm-typbind-record) and the variables closed by r:sm-datbind; only declarations of values are copied by number specialisation. Elm 0.19.1 keeps the class of such a parameter (`type Box number = Box number` rejects `Box "s"`). A93's extra closure variables are kept by scheme equality (static-core, Type Schemes).

## A28: Explicitly exposed type names replace rather than conflict
- **Origin:** C-STA-11
- Construct: `import Foo exposing (Maybe)` where `Foo` defines `Maybe`.
- Question: Is the bare `Maybe` ambiguous with the default import?
- Implementation: an explicitly listed type name or operator replaces the earlier entry; values and `(..)` merge into ambiguity (C/Canonicalize/Environment/Foreign.elm:15-19, :378-445).
- Notes or Elm reference behaviour: silent.
- Options: (a) replacement for explicitly listed types and operators; (b) ambiguity for all kinds.
- **Ruling:** IMPLEMENTATION: an explicitly exposed type name or operator replaces an earlier binding of the same name; values and `(..)` imports merge, and a merged name is ambiguous only when used. (provisional)
- **Reason:** As implemented.
- **Affects:** static

## A29: Private types in exposed signatures
- **Origin:** C-STA-12
- Construct: `module M exposing (f)` with `type Hidden = H` and `f : Hidden -> Int`.
- Question: Is exposing `f` legal?
- Implementation: no check exists (C/Canonicalize/Module.elm:430-530; C/Canonicalize/Error.elm:161-198); the interface keeps the private type's declaration (C/IR/Canonical/Interface.elm:17-19).
- Notes or Elm reference behaviour: silent.
- Options: (a) legal; (b) error.
- **Ruling:** IMPLEMENTATION: legal. (provisional)
- **Reason:** No implementation checks it.
- **Affects:** static

## A30: Module without a header
- **Origin:** C-STA-13
- Construct: a file with no `module` line that declares ports.
- Question: Is a headerless module allowed to declare ports, and what is its name and export list?
- Implementation: accepted without checks; its ports become its effects (C/Parse/Module.elm:29).
- Notes or Elm reference behaviour: silent; an imported module must have a header (CE/ErrorMessagesIssue103ImportedModuleWithoutModuleLineTest.elm).
- Options: (a) record as implemented; (b) require `port module`.
- **Ruling:** INTENT: a header-less module is the main module `module Main exposing (..)` (A16) and cannot declare ports, which require a `port module` header. (provisional)
- **Reason:** Consistent with A16.
- **Amended by the author (2026-11-07):** superseded by the amendment to A16: a module without a header is not a phrase, so the question of its ports does not arise. Neither implementation accepts a header-less file under `make`, so neither diverges here.
- **Affects:** static

## A31: Literal identity in redundancy checking
- **Origin:** C-STA-14
- Construct: `case c of 'A' -> 1; '\u{0041}' -> 2; _ -> 3`.
- Question: Is the second branch redundant?
- Implementation: char and string literals are compared by escaped source text, so it is not reported (C/Nitpick/PatternMatches.elm:94-100; C/Parse/String.elm:13-18). Int literals compare by value.
- Notes or Elm reference behaviour: silent.
- Options: (a) compare denoted values; (b) as implemented.
- **Ruling:** INTENT: literal patterns are compared by the values they denote. (provisional)
- **Reason:** The source spelling of a literal is not a meaning.
- **Affects:** static

## A32: Where `main` is checked and required
- **Origin:** C-STA-15
- Construct: a non-root module defining a `main` of an unsupported type.
- Question: Is `main` checked in every module or only in the entry module, and is it required?
- Implementation: checked in every module that defines it (C/LocalOpt/Erased/Module.elm:392-404); required only for HTML/JS output (B/Reporting/Exit.elm:2219-2280); the entry point is the root's `main` (T/elm/src/EntryMainOfRootModuleTest.elm).
- Notes or Elm reference behaviour: DD/elm-divergence.md:206-208 says Elm's optimiser also reports `BAD MAIN`.
- Options: (a) per-module rule; (b) program-level rule.
- **Ruling:** INTENT: only the main module's `main` is constrained (program level); a `main` in another module is an ordinary value. (provisional)
- **Reason:** Program-level rule; per-module checking is an implementation choice.
- **Affects:** static

## A33: eco System.Environment flags
- **Origin:** C-STA-16
- Construct: `main : Program System.Environment model msg`.
- Question: Part of the language definition?
- Implementation: eco extension, recognised by alias name before dealiasing, flags check skipped (C/IR/Runtime/EcoEnvironment.elm:6-18, :47-56; C/LocalOpt/Erased/Module.elm:423-431).
- Notes or Elm reference behaviour: not in Elm.
- Options: (a) exclude from Standard Elm; (b) appendix.
- **Ruling:** INTENT: excluded from Standard Elm; recorded in the implementation appendix. (provisional)
- **Reason:** eco extension.
- **Affects:** static

## A34: Implementation size limits
- **Origin:** C-STA-17
- Construct: functions over 2047 parameters, records over 2047 fields, constructors over 2040 fields, over 1024 nullary constructors.
- Question: Are limits part of the definition?
- Implementation: rejected in canonicalisation on every target (C/Canonicalize/Error.elm:1073-1130; C/IR/Runtime/HeapLimits.elm:30-61).
- Notes or Elm reference behaviour: Elm has no such limits (DD/elm-divergence.md:214-218).
- Options: (a) implementation-defined limits clause; (b) omit.
- **Ruling:** UNSPECIFIED: implementation limits, appendix (as A13). (provisional)
- **Reason:** Same as A13.
- **Affects:** static

## A35: Equality at every type
- **Origin:** C-STA-18
- Construct: `(\x -> x) == (\x -> x)`, `==` on `Json.Encode.Value` or `Regex`.
- Question: Should the static semantics restrict `==`?
- Implementation: `eq : a -> a -> Bool`, no restriction (core/Basics.elm:348); eco's run-time result differs from Elm's crash (DD/elm-divergence.md:181-189, :362-375).
- Notes or Elm reference behaviour: core/Basics.elm:340-344 says a future compiler will detect it.
- Options: (a) unrestricted, dynamic semantics decides; (b) an equality class excluding functions.
- **Ruling:** IMPLEMENTATION: `==` is unrestricted statically; its value on functions is settled by A51. (provisional)
- **Reason:** Both implementations type it so.
- **Affects:** static

## A36: Constrained name as a record extension variable
- **Origin:** C-STA-19
- Construct: `f : { number | x : Int } -> Int`.
- Question: Is a constrained variable legal as a row extension?
- Implementation: the name makes it a rigid `number`, which can unify with no record structure (C/Type/Type.elm:432-437; C/Type/Unify.elm:575-610), so any use fails with `TYPE MISMATCH`; the declaration itself is accepted.
- Notes or Elm reference behaviour: silent.
- Options: (a) reject the annotation; (b) accept, uninhabited.
- **Ruling:** INTENT: ill formed: a constrained type variable name cannot stand for a row. (provisional)
- **Reason:** Rows and constrained variables are different classes.
- **Affects:** static

## A37: Kernel-package privileges
- **Origin:** C-STA-20
- Construct: `Elm.Kernel.X.f`, `infix` declarations, `effect module`.
- Question: Which packages may use them?
- Implementation: authors `elm`, `elm-explorations` and `eco` (C/Elm/Package.elm:155-160); unannotated kernel references are unconstrained (C/Type/Constrain/Typed/Expression.elm:469-475).
- Notes or Elm reference behaviour: Elm 0.19.1 restricts these to its own core authors (eco adds `eco`).
- Options: (a) exclude kernel features from the definition and specify the basis by signature; (b) model them.
- **Ruling:** INTENT: kernel features are excluded; the initial basis is given by signature and meaning. (provisional)
- **Reason:** As A16.
- **Affects:** static

## A38: Lazy ambiguity and qualified self-reference
- **Origin:** C-STA-21
- Construct: two imports exposing `x`, `x` unused; `M.x` inside module `M`.
- Question: Is an unused ambiguous name an error, and can a module qualify its own names?
- Implementation: ambiguity is an error only on use (C/Canonicalize/Environment.elm:21-25); qualified lookups see only imports, so `M.x` in `M` is `NAMING ERROR` (C/Canonicalize/Environment.elm:96-100; C/Canonicalize/Expression.elm:1643-1676).
- Notes or Elm reference behaviour: silent.
- Options: record as implemented.
- **Ruling:** IMPLEMENTATION: an ambiguous name is an error only when used; a module cannot refer to its own names by qualification. (provisional)
- **Reason:** As implemented.
- **Affects:** static

## A39: Native-only rejections
- **Origin:** C-STA-22
- Construct: polymorphic recursion through annotated functions; GLSL shaders; closures over 2047 slots after specialisation; `Bytes` nested in a port payload; `Debug` with `--optimize`.
- Question: Are these programs Standard Elm?
- Implementation: rejected only by the native back end, or (for `Debug`) accepted only by it (DD/elm-divergence.md:191-197, :220-260; C/LocalOpt/Error.elm:73-79).
- Notes or Elm reference behaviour: Elm compiles the first three; rejects `Debug` under `--optimize`.
- Options: (a) define the language independently of target and list these as implementation restrictions.
- **Ruling:** INTENT: the definition is independent of target; native-only rejections are implementation restrictions listed in the appendix. (provisional)
- **Reason:** Target differences are implementation detail (D8).
- **Affects:** static

## A40: Int range and overflow
- **Origin:** C-DYN-1
- **Construct:** Int arithmetic `+ - * negate abs ^`
- **Question:** What is the value of an Int operation whose exact result leaves the representable range?
- **Implementation:** eco wraps modulo 2^64 (IntArith.hpp:9-36; arith:52-87).
- **Notes or Elm reference behaviour:** Elm-on-JS computes in doubles: exact to 2^53, then rounded, then ±Infinity (div:36-45). elm/core docs silent.
- **Options:** (a) parametric width W with wraparound, W = 64 in eco and an appendix note for JS; (b) unbounded mathematical integers, overflow implementation-dependent; (c) fix 64-bit wraparound as the definition.
- **Ruling:** CUSTOM: Int arithmetic is exact integer arithmetic followed by an implementation-dependent normalisation into the implementation's Int range, which contains at least -2^31 to 2^31-1. eco: 64-bit two's complement wrap; Elm-on-JS: rounding to a double (appendix). (provisional)
- **Reason:** Never fails (D3) and keeps width out of the body (D8).
- **Affects:** dynamic | basis

## A41: Integer division width and the `minInt // -1` case
- **Origin:** C-DYN-2
- **Construct:** `//`
- **Question:** Is `a // b` = `trunc(a / b)` for all results, and what is `minInt // -1`?
- **Implementation:** eco: total truncated division, `x // 0` = 0, `minInt // -1` = minInt (arith:91-123; ecok/Basics.cpp:87-89).
- **Notes or Elm reference behaviour:** Elm-on-JS computes `ToInt32(a / b)` (kjs/Basics.js:14; jsgen:855-856), so any quotient outside ±2^31 wraps to 32 bits, a point eco's divergence notes do not list; `x // 0` = 0 arises from `ToInt32(±Infinity)` = 0.
- **Options:** (a) `trunc` with wrap to the Int width; (b) define via `ToInt32` as Elm-on-JS does; (c) unspecified outside ±2^31.
- **Ruling:** CUSTOM: `a // b` is the normalised truncation of a / b for b /= 0. Elm-on-JS's 32-bit quotient is recorded in the appendix as a divergence. (provisional)
- **Reason:** Mathematical definition; width is the normalisation's business.
- **Affects:** basis

## A42: Division by zero for `//`, `modBy`, `remainderBy`
- **Origin:** C-DYN-3
- **Construct:** `x // 0`, `modBy 0 x`, `remainderBy 0 x`
- **Question:** Which defined "wrong answer" does each give?
- **Implementation:** eco: all give 0 (arith:91-197; ecok/Basics.cpp:87-106; TD/ModByZeroKernelPathTest:25-28; TD/RemainderByZeroTest:14-18).
- **Notes or Elm reference behaviour:** Elm-on-JS: `x // 0` = 0, `modBy 0` crashes (kjs/Basics.js:23-24), `remainderBy 0` is NaN in an Int (TD/RemainderByZeroTest:19-23). Author direction fixes `3 // 0 == 0`.
- **Options:** (a) 0 for all three (eco); (b) `modBy 0 x = x` and `remainderBy 0 x = x` (keeps `x = d * (x // d) + remainderBy d x`); (c) leave `modBy 0` as a failure.
- **Ruling:** IMPLEMENTATION (eco): `x // 0`, `modBy 0 x` and `remainderBy 0 x` are all 0. (provisional)
- **Reason:** Direction D3 (3 // 0 == 0) extended uniformly; eco tests pin all three.
- **Affects:** basis

## A43: Int `^` with a negative exponent
- **Origin:** C-DYN-4
- **Construct:** `b ^ e` at Int, `e < 0`
- **Question:** What Int is `b ^ e` when `e` is negative?
- **Implementation:** eco: 0 for every base, including 1 and -1 (IntArith.hpp:38-44).
- **Notes or Elm reference behaviour:** Elm-on-JS: `Math.pow`, a fraction or Infinity typed Int (kjs/Basics.js:15; TB/CoreIssue960PowNegativeExponentIntTest:12 requires only "an integer"); `0 ^ -1` undecided in div:50-51.
- **Options:** (a) 0 always (eco); (b) `trunc` of the real result: 1 for base 1, ±1 for base -1, 0 for other bases, 0 for base 0; (c) implementation-dependent.
- **Ruling:** CUSTOM: for e < 0, Int `b ^ e` is the truncation of the real result where that is finite: 1 for b = 1, 1 or -1 for b = -1 (by parity of e), 0 otherwise (including b = 0). (confirmed by the author, 2026-11-07: the definition stands and eco is to be changed to match)
- **Reason:** Principled 'wrong answer' (D3) close to the real value. eco returns 0 for every base; this is recorded as an eco divergence to fix.
- **Affects:** basis

## A44: Float-to-Int conversion of NaN, infinities and out-of-range values
- **Origin:** C-DYN-5
- **Construct:** `round`, `floor`, `ceiling`, `truncate`
- **Question:** What Int results for NaN, ±Infinity, and values outside the Int range?
- **Implementation:** eco saturates: NaN 0, too large maxInt, too small minInt (arith:586-607; ecok/Basics.cpp:116-121; fsem:34).
- **Notes or Elm reference behaviour:** Elm-on-JS stores NaN or ±Infinity in an Int; `truncate` is `ToInt32` so NaN and ±Infinity give 0 and `truncate 3e10` = -64771072 (TD/FloatToIntRangeTest:15-19).
- **Options:** (a) saturate with NaN to 0 (eco); (b) NaN and ±Inf to 0, out-of-range wrap; (c) implementation-dependent.
- **Ruling:** IMPLEMENTATION (eco): conversion to Int saturates; NaN gives 0. (provisional)
- **Reason:** Total (D3), pinned by eco tests.
- **Affects:** basis

## A45: Negative zero in Int
- **Origin:** C-DYN-6
- **Construct:** Int results `negate 0`, `0 * -1`, `modBy 4 -4`, `remainderBy 4 -4`, `round -0.4`, `ceiling -0.5`
- **Question:** Does Int have one zero, or can `toFloat` reveal a negative zero?
- **Implementation:** eco Int has one zero; `1 / toFloat (negate 0)` = Infinity (TD/IntNegativeZeroTest:14-18).
- **Notes or Elm reference behaviour:** Elm-on-JS gives -Infinity (TD/IntNegativeZeroTest:19-22; div:75-81).
- **Options:** (a) Int is the integers, one zero; (b) appendix-only JS artefact.
- **Ruling:** INTENT: Int is a set of integers with one zero. (provisional)
- **Reason:** Negative Int zero is a JS artefact (appendix).
- **Affects:** basis

## A46: `compare` on Float with NaN and signed zeros
- **Origin:** C-DYN-7
- **Construct:** `compare`, and everything built on it (`sort`, `Dict`, `Set`, tuple and list ordering)
- **Question:** What Order does `compare` give when an operand is NaN?
- **Implementation:** eco: total order, NaN equals NaN and is above every number, -0 equals +0 (arith:1346-1380; ecok/Utils.hpp:82-89; TD/FloatIeeeSemanticsTest:40-52).
- **Notes or Elm reference behaviour:** Elm-on-JS: GT whenever NaN is involved, so not antisymmetric (kjs/Utils.js:91; TD/FloatDivergenceTest:19-20); elm/core docs silent.
- **Options:** (a) eco's total order; (b) IEEE totalOrder (-NaN < -Inf, -0 < +0); (c) unspecified when NaN is involved.
- **Ruling:** IMPLEMENTATION (eco): `compare` on Float is a total order: -0 and +0 are equal, NaN equals NaN and is greater than every other Float. (provisional)
- **Reason:** A total order makes sorting, Dict and Set well defined.
- **Affects:** basis

## A47: Ordering operators on Float with NaN, and their relation to `compare`
- **Origin:** C-DYN-8
- **Construct:** `<`, `<=`, `>`, `>=` at Float, and at tuples or lists containing Float
- **Question:** Are the order operators IEEE predicates, or derived from `compare`?
- **Implementation:** eco: IEEE at Float (all False with NaN), but lexicographic by `compare`'s total order inside tuples and lists, so `nan < 1` is False and `[ nan ] > [ 1 ]` is True (fsem:27-29; TD/FloatIeeeSemanticsTest:56-57).
- **Notes or Elm reference behaviour:** Elm-on-JS: raw JS operator when an operand is a source literal, else `_Utils_cmp`, so `one > nan` is True but `1 > nan` False (TD/FloatNaNOrderTest:39-58; jsgen:925-934).
- **Options:** (a) eco's split (IEEE at Float, total order in aggregates); (b) all operators defined from `compare`; (c) unspecified with NaN.
- **Ruling:** IMPLEMENTATION (eco): at Float, `<`, `<=`, `>`, `>=` are the IEEE predicates (false when an operand is NaN); on tuples and lists they are the lexicographic order derived from `compare`. (provisional)
- **Reason:** eco's documented float semantics; Elm-on-JS's literal-dependent behaviour is a bug.
- **Affects:** basis

## A48: `min`, `max`, `clamp` at Float
- **Origin:** C-DYN-9
- **Construct:** `min`, `max`, `clamp`
- **Question:** Are these the elm/core definitions (`if lt x y then x else y`) or IEEE 754-2019 minimum/maximum?
- **Implementation:** eco replaces the Float specialisations by IEEE minimum/maximum and `clamp lo hi x = min (max x lo) hi`; Int and other types keep elm/core bodies (MonoOpt/FloatMinMax.elm:1-18, 70-95).
- **Notes or Elm reference behaviour:** elm/core defines them in Elm (core/Basics.elm:396-407, 593-599); results with NaN and ±0 depend on argument order (fsem:49-52).
- **Options:** (a) elm/core definitions verbatim; (b) eco's IEEE functions at Float; (c) elm/core definitions with NaN cases unspecified.
- **Ruling:** IMPLEMENTATION (eco), decided by the author: at Float, `min` and `max` are IEEE 754-2019 `minimum` and `maximum`: NaN if either argument is NaN, and -0 below +0 (so `max 0 -0` is +0, `min -0 0` is -0). At every other comparable type they keep their elm/core definitions. `clamp` at Float is `min (max x lo) hi` with these operations (A49, as amended by the author). (author, 2026-11-07; supersedes the provisional ruling, which took the elm/core text at every type)
- **Reason:** The elm/core text `if x > y then x else y` makes the result at Float depend on argument order (`max nan 1` is 1 but `max 1 nan` is NaN) and treats the two zeros arbitrarily; the author judges this a bug. IEEE `minimum`/`maximum` are symmetric and match eco.
- **Affects:** basis

## A49: `clamp lo hi x` with `lo > hi`
- **Origin:** C-DYN-10
- **Construct:** `clamp`
- **Question:** What does `clamp 10 0 5` give?
- **Implementation:** eco at Float: `min (max 5 10) 0` = 0 (always `hi` when `lo > hi`); eco at Int: elm/core body gives 10 (MonoOpt/FloatMinMax.elm:75-82; core/Basics.elm:593-599). Not documented in fsem and not tested.
- **Notes or Elm reference behaviour:** elm/core doc gives the three cases assuming `lo <= hi` (core/Basics.elm:586-592); Elm-on-JS returns `lo` when `x < lo`.
- **Options:** (a) elm/core's case analysis (`lo` wins); (b) `hi` wins; (c) unspecified when `lo > hi`.
- **Ruling:** IMPLEMENTATION (eco), decided by the author: at Float, `clamp lo hi x` is `min (max x lo) hi` with the IEEE 754-2019 `minimum` and `maximum` of A48: so `clamp 10 0 5` is 0 (hi when lo > hi), a NaN bound or a NaN x gives NaN, and `clamp 0 1 -0` is +0. At every other type `clamp` keeps its elm/core definition (lo when x < lo, else hi when x > hi, else x). (author, 2026-11-07; supersedes the provisional ruling, which followed the elm/core text at every type)
- **Reason:** Consistent with A48: the Float operations built on comparisons follow IEEE rather than the order-dependent elm/core text; matches eco.
- **Affects:** basis

## A50: Equality and object identity (reflexivity versus IEEE)
- **Origin:** C-DYN-11
- **Construct:** `==` on structured values containing NaN
- **Question:** Is `t == t` True when `t = ( nan, 0 )`, while a separately built `( nan, 0 )` is unequal?
- **Implementation:** eco returns True for the same heap object, in the kernel (ecok/Utils.cpp:503) and the inline fast path (EcoBackend.cpp:2216-2236); whether two occurrences are the same object depends on optimisation (SSA aggregates, interning, constant sharing).
- **Notes or Elm reference behaviour:** Elm-on-JS identical shortcut (kjs/Utils.js:29-32). eco notes claim equality never uses identity (div:149-150, 172; div:464 lists `False`); TB/CompilerIssue2362NanTupleEqualityTest:13-15 and TB/CoreIssue988NanContainerSelfEqualityTest:17-24 want False.
- **Options:** (a) purely structural with IEEE Float equality (identity irrelevant); (b) structural with Float equality reflexive inside containers; (c) unspecified for values containing NaN.
- **Ruling:** INTENT: equality is purely structural, with IEEE equality at Float; physical identity plays no part, so a value containing NaN is not equal to itself. (provisional)
- **Reason:** Only meaning that does not depend on optimisation; both implementations' identity shortcut is recorded in the appendix.
- **Affects:** dynamic | basis

## A51: Equality on functions
- **Origin:** C-DYN-12
- **Construct:** `==` where the type contains a function
- **Question:** What does `==` do on functions, given the type system allows it?
- **Implementation:** eco: True iff same closure object, else False, at any depth (ecok/Utils.cpp:503, 691-692; TD/FunctionEqualityFalseTest:13-19); zero-capture closures are interned (clos:88), so two evaluations of one capture-free lambda compare True, and a partial application compares False to an identical one.
- **Notes or Elm reference behaviour:** Elm-on-JS crashes unless the same object (kjs/Utils.js:34-37; kjs/Debug.js:262-263).
- **Options:** (a) a runtime failure (Elm); (b) always False except physical identity, with identity left implementation-dependent; (c) unspecified value of type Bool.
- **Ruling:** CUSTOM: comparing values that contain functions with `==` never fails; when the comparison reaches two function values, the result is an unspecified Bool (named as non-determinism in the rule's Comment). eco's identity comparison and Elm-on-JS's crash are recorded in the appendix. (provisional)
- **Reason:** No runtime errors (D2, D3); identity is not a meaning.
- **Affects:** dynamic

## A52: What a Char is
- **Origin:** C-DYN-13
- **Construct:** Char values, `toCode`, `fromCode`, case mapping
- **Question:** Is a Char exactly one Unicode code point (scalar value or any code point including surrogates)?
- **Implementation:** eco: one code point 0..0x10FFFF, surrogate code points allowed as Chars (vrep:29; ccase:30-31).
- **Notes or Elm reference behaviour:** Elm-on-JS: a JS string of 1-2 units; `toUpper 'ß'` is "SS" in a Char; lone surrogates give `toCode` NaN (kjs/Char.js:8-41; ccase:47-56).
- **Options:** (a) code point including surrogates (eco); (b) Unicode scalar value (surrogates excluded, `fromCode` maps them to U+FFFD); (c) abstract character, with the JS model in the appendix.
- **Ruling:** CUSTOM: Char is an abstract class of characters with an injective `toCode` into the integers; its concrete form is an implementation parameter (eco: one code point; Elm-on-JS: a short UTF-16 string). (provisional)
- **Reason:** Direction D8.
- **Affects:** basis

## A53: Char order versus String order
- **Origin:** C-DYN-14
- **Construct:** `compare`, `<` on Char and on String
- **Question:** Are Chars ordered by code point, and must that agree with String order of one-Char strings?
- **Implementation:** eco: Chars by code point (arith:1177; ecok/Utils.cpp:330-336), Strings by UTF-16 units (strops:1647-1650), so the two disagree for U+E000..U+FFFF against astral Chars.
- **Notes or Elm reference behaviour:** Elm-on-JS orders both by UTF-16 units (kjs/Utils.js:89-92), so they agree.
- **Options:** (a) both by code point; (b) both by UTF-16 units; (c) eco's mix.
- **Ruling:** CUSTOM: Char is ordered by `toCode`; String is ordered lexicographically by its sequence of characters. Implementations whose string order differs (eco's UTF-16 unit order for astral characters) are recorded in the appendix. (provisional)
- **Reason:** One coherent order in the body (D8).
- **Affects:** basis

## A54: Case mapping
- **Origin:** C-DYN-15
- **Construct:** `Char.toUpper/toLower/toLocale*`, `String.toUpper/toLower`
- **Question:** Simple or full Unicode case mapping, which Unicode version, and is Final_Sigma applied?
- **Implementation:** eco: simple mapping, Unicode 17.0, no Final_Sigma, length preserved (ccase:30-42, 62-77).
- **Notes or Elm reference behaviour:** Elm-on-JS: JS full mapping and Final_Sigma, host Unicode version, locale for `toLocale*` in browsers (ccase:47-56, 75-88).
- **Options:** (a) simple mapping of a named Unicode version; (b) full mapping (needs String results); (c) implementation-dependent.
- **Ruling:** UNSPECIFIED: case mapping is outside the initial basis; implementation behaviour in the appendix. (provisional)
- **Reason:** Library, not language.
- **Affects:** basis

## A55: Bitwise width and `shiftRightZfBy`
- **Origin:** C-DYN-16
- **Construct:** `Bitwise.*`
- **Question:** On how many bits do the Bitwise functions work, and is `shiftRightZfBy`'s result unsigned?
- **Implementation:** eco: 64 bits, shift counts mod 64, `shiftRightZfBy` result reinterpreted as signed (ecok/Bitwise.cpp:5-32; arith:1010-1060; TD/BitwiseLargeShiftTest:7-8).
- **Notes or Elm reference behaviour:** Elm-on-JS: operands `ToInt32`, counts mod 32, `>>>` gives an unsigned 32-bit result (kjs/Bitwise.js:6-39); div:409-415 suggests matching 32 bits.
- **Options:** (a) the Int width W; (b) fixed 32 bits as Elm-on-JS; (c) implementation-dependent.
- **Ruling:** UNSPECIFIED: Bitwise is outside the initial basis; width differences in the appendix. (provisional)
- **Reason:** Library, not language; width is implementation detail (D8).
- **Affects:** basis

## A56: Prefix `(&&) a b` and `(||) a b`
- **Origin:** C-DYN-17
- **Construct:** a saturated prefix use of `&&` or `||`
- **Question:** Does `(&&) False e` evaluate `e`?
- **Implementation:** eco: yes (strict); only `Can.Binop` is rewritten to `if` (tyopt:450-455, 509-516; intr:213-215). Read from the code, not tested.
- **Notes or Elm reference behaviour:** Elm-on-JS: no; any saturated call of `Basics.and`/`or` becomes JS `&&`/`||` (jsgen:682-690, 876-882). elm/core documents only the operator form (core/Basics.elm:73-74, 456-486).
- **Options:** (a) `&&` and `||` are special forms only as infix operators, ordinary strict functions otherwise; (b) short-circuit whenever saturated; (c) unspecified.
- **Ruling:** CUSTOM: the infix forms `e1 && e2` and `e1 || e2` are derived forms (conditionals) and short-circuit; the prefix functions `(&&)` and `(||)` are ordinary strict functions. Confirmed by the author, 2026-11-10: a function passed `(&&)` or `(||)` as a value need not know that it is special, so the definition does not ask an implementation to evaluate a prefix use lazily.
- **Reason:** Matches eco; a saturated prefix call is a function application in the definition.
- **Note (A94, 2026-11-10):** Elm on JavaScript, which evaluates the second argument of the prefix forms only when needed, gives `(&&) False (Debug.todo "x")` the value `False` where the definition gives none; by A94 it conforms.
- **Affects:** dynamic
- **Revision (2026-11-10, author decision):** the note above holds only where the program has no meaning. Within a running program, a step that the definition gives no result (an application of `update` that reaches `(&&) False (Debug.todo "x")`) ends the handling of messages (r:p-update), and an implementation that carries on does not conform; the row for Elm/JS's lazy prefix forms in a step of a running program is restored to Appendix E's divergences.

## A57: Order of evaluation within a `let`
- **Origin:** C-DYN-18
- **Construct:** `let` with several bindings
- **Question:** In what order are the bindings of one `let` evaluated?
- **Implementation:** both front ends regroup bindings into SCCs, dependencies first (Canonicalize/Expression.elm:39-47); eco measured: named bindings before `_ =` bindings, not in source order (dlog:37-53); `_ =` runs are in source order (T/DebugLogOrderingTest:6-16).
- **Notes or Elm reference behaviour:** silent; eco calls it "unspecified-but-observable" (dlog:51-53). Elm-on-JS order among independent bindings not checked here.
- **Options:** (a) source order; (b) any order consistent with dependencies (unspecified); (c) dependency order with source order among independent bindings.
- **Ruling:** CUSTOM: the bindings of a `let` are evaluated in an order consistent with their dependencies; the order among independent bindings is not specified and is not observable in the definition. (provisional)
- **Reason:** Elm is pure; only Debug output could tell, and Debug output is outside the definition (A62).
- **Affects:** dynamic

## A58: Order of evaluation of record fields and other compound expressions
- **Origin:** C-DYN-19
- **Construct:** record literals, tuples, lists, application arguments
- **Question:** Are sub-expressions evaluated left to right in source order?
- **Implementation:** eco: record fields in layout order, unboxed fields first then by name (GenerateMlir/Expr.elm:528-542); other orders not pinned.
- **Notes or Elm reference behaviour:** Elm-on-JS: record fields by field name (the canonical record is a name-keyed Dict, Canonical.elm:218), tuples, lists and arguments left to right (JS).
- **Options:** (a) source order; (b) unspecified (only Debug.log can tell); (c) field-name order for records, left to right otherwise.
- **Ruling:** CUSTOM: evaluation order of the parts of a compound expression is not significant (premise order in dynamic rules carries no meaning); implementations may choose. (provisional)
- **Reason:** No state or exceptions, so order is unobservable within the definition.
- **Affects:** dynamic

## A59: Evaluation time and multiplicity of top-level values
- **Origin:** C-DYN-20
- **Construct:** top-level definitions without parameters
- **Question:** When is a top-level value evaluated, and how many times?
- **Implementation:** eco: thunks; boxed values memoised on first use, Int/Float/Char values recomputed at each use, function-typed values re-run their body per call (mlir-generation.md:112-137; TD/EtaExpandLogOrderTest:37-44).
- **Notes or Elm reference behaviour:** Elm-on-JS: once, eagerly, at start-up, in dependency order (Generate.elm:358-395); a top-level `Debug.todo` value fails at start even if unused at run time.
- **Options:** (a) once, before `main` (Elm); (b) once, on first use; (c) unspecified (observable only through Debug and failure).
- **Ruling:** INTENT: each top-level value is evaluated once, when its module is initialised, in dependency order; an implementation may evaluate later or repeatedly provided results agree. (provisional)
- **Reason:** Declarative meaning; eco's lazy and repeated evaluation is unobservable except through Debug.
- **Affects:** dynamic

- **Note (audit X15):** Chapter 7 evaluates top-level groups through a translation in which a reference from inside a value's own recursive group re-evaluates that value; the results are equal except where they contain functions compared with `==` (A51), so "once" holds up to that non-determinism.

## A60: Order of callback application in the basis
- **Origin:** C-DYN-21
- **Construct:** `List.map`, `List.filter`, `List.map2`, `List.indexedMap`, folds
- **Question:** Does the book fix the order in which basis functions apply their callbacks?
- **Implementation:** eco follows elm/core: `map`/`filter` via `foldr`, so last element first (T/ListMapTemplateOrderTest:13-18), but may reorder Debug-free callbacks (dlog:66-80).
- **Notes or Elm reference behaviour:** elm/core source fixes it (core/List.elm:124-125, 214-215); `map2` is a forward kernel loop (kjs/List.js:37-44).
- **Options:** (a) define basis functions by their elm/core Elm source (order follows); (b) leave callback order unspecified.
- **Ruling:** INTENT: a basis function written in Elm in elm/core is defined by that Elm definition. (provisional)
- **Reason:** One source of truth.
- **Affects:** basis

## A61: Resource exhaustion
- **Origin:** C-DYN-22
- **Construct:** deep recursion, large allocation
- **Question:** Is stack overflow or memory exhaustion part of the semantics, and how is it reported?
- **Implementation:** eco: SIGSEGV on native stack overflow; abort with a message on heap or shadow-stack exhaustion (div:435-440; ThreadLocalHeap.cpp:424-440; RootSet.cpp:36).
- **Notes or Elm reference behaviour:** Elm-on-JS: `RangeError` near 10k frames; JS heap failure (div:437-438).
- **Options:** (a) outside the definition (an implementation may fail at any point for lack of resources); (b) a defined abort result; (c) bound recursion depth.
- **Ruling:** UNSPECIFIED: resource exhaustion is outside the definition; an implementation may stop for lack of resources at any point. (provisional)
- **Reason:** As the exemplar leaves implementation limits aside.
- **Affects:** dynamic

## A62: `Debug.todo` and `Debug.log`
- **Origin:** C-DYN-23
- **Construct:** `Debug.todo`, `Debug.log`
- **Question:** Are these part of the defined language, and what do they mean?
- **Implementation:** eco: `Debug.log` writes `label: value` to program output and returns the value; `Debug.todo` prints "Debug.todo: msg" and exits 1; allowed under `--optimize` (dlog:7-16; ecok/DebugExports.cpp:43-52; div:191-197).
- **Notes or Elm reference behaviour:** Elm-on-JS: `console.log`; `Debug.todo` throws "TODO in module ..."; Debug rejected under `--optimize` (kjs/Debug.js:12-41).
- **Options:** (a) `Debug.todo` as a bottom value (abort) and `Debug.log` as an observation outside the pure semantics; (b) omit Debug from the definition; (c) define an output trace.
- **Ruling:** CUSTOM: `Debug.log l v` evaluates to v (any output is outside the definition); `Debug.todo s` has no value: no evaluation rule applies, so evaluation that reaches it has no result; `Debug.toString` yields an implementation-dependent String. (provisional)
- **Reason:** Keeps the pure semantics and says plainly what the escape hatch is.
- **Affects:** dynamic | basis

## A63: Closures created in a self tail-call loop
- **Origin:** C-DYN-24
- **Construct:** a lambda created inside a self-tail-recursive function
- **Question:** Does each closure capture the value of its own call (as the substitution semantics says)?
- **Implementation:** eco: loop lowering with captured values; not pinned by a native test (TB tests are not run by eco).
- **Notes or Elm reference behaviour:** Elm-on-JS bug: closures share the reassigned loop variable (TB/CompilerIssue1813TcoClosureCapturesMutatedArgTest:13, TB/CompilerIssue2268TcoClosureCaptureTest:14-15).
- **Options:** (a) the definition's substitution semantics (each call's value), with Elm-on-JS listed as a known bug; (b) appendix note only.
- **Ruling:** INTENT: each closure captures the values of its own call; Elm-on-JS's sharing is a known bug recorded in the appendix. (provisional)
- **Reason:** Follows from the definition's environment semantics.
- **Affects:** dynamic

## A64: `String.toInt` and `String.fromInt` outside the exact range
- **Origin:** C-DYN-25
- **Construct:** `String.toInt`, `String.fromInt`
- **Question:** What does `String.toInt` return for a numeral outside the Int range or longer than any Int numeral, and how does `fromInt` print large values?
- **Implementation:** eco: `Nothing` on overflow or more than 64 units; `fromInt` exact decimal (strops:1186-1222, 1272-1280).
- **Notes or Elm reference behaviour:** Elm-on-JS: `Just` of a rounded double, no length limit, "-0" gives -0; `fromInt` uses JS number printing, exponent form at 1e21 (kjs/String.js:270-299; TB/CoreIssue1142StringToIntMaxSafeTest:13-14).
- **Options:** (a) `Nothing` outside the Int range, any number of leading zeros accepted; (b) eco's rule including the 64-unit limit; (c) implementation-dependent.
- **Ruling:** UNSPECIFIED: `String.toInt` and `String.fromInt` are outside the initial basis; differences in the appendix. (provisional)
- **Reason:** Library, not language.
- **Affects:** basis

## A65: Float `pow` special cases and transcendental accuracy
- **Origin:** C-DYN-26
- **Construct:** Float `^`, `sin`, `cos`, `tan`, `log`, `logBase`, inverse trig
- **Question:** Does the book define these by IEEE 754 / C99 Annex F, by ECMAScript, or leave accuracy implementation-dependent?
- **Implementation:** eco: LLVM `pow` (C99: `1 ^ (1/0)` = 1), `tan` as `sin/cos`, libm elsewhere (arith:351-516); not tested at special values.
- **Notes or Elm reference behaviour:** Elm-on-JS: `Math.*`, ECMAScript `1 ^ (1/0)` = NaN; `logBase 10 1000` = 2.9999999999999996 (TB/CoreIssue1048LogBaseTenTest:12-13 wants 3).
- **Options:** (a) the real function, rounding implementation-dependent, special values per IEEE 754-2019 recommended operations; (b) follow ECMAScript; (c) implementation-dependent entirely.
- **Ruling:** CUSTOM: `+ - * /`, `sqrt` and negation are correctly rounded (IEEE 754); the power and the transcendental functions denote the real function rounded to a Float, with special values as IEEE 754-2019 recommends; accuracy is implementation-dependent. (provisional)
- **Reason:** D8; neither implementation is exact.
- **Affects:** basis

## A66: Order of commands within one `Cmd.batch`
- **Origin:** C-PLT-1
- Construct: `Cmd.batch [c1, c2]` where both go to the same manager (Task, a port).
- Question: Does the definition fix the order in which they are performed and their messages arrive?
- Implementation (cite): Reverse order: `kjs/Platform.js:319-328` conses; eco reproduces explicitly (`kc/core/TaskEffectManager.cpp:62-68`; `rt/PortRuntime.cpp:168-172`; `CmdBatchOrderTest`).
- Notes or Elm reference behaviour: Docs say "no ordering guarantees about the results" (`core/Platform/Cmd.elm:58-61`).
- Options: (a) unspecified; (b) specify source order; (c) specify reverse order as observed.
- **Ruling:** UNSPECIFIED: the order in which the commands of one batch are performed is not defined. Both implementations' reverse order is recorded in the appendix. (provisional)
- **Reason:** The core documentation promises no order.
- **Affects:** dynamic

## A67: Order across effect managers in one dispatch
- **Origin:** C-PLT-2
- Construct: `Cmd.batch [ port out, Task.perform ... ]`, and incoming vs outgoing port managers.
- Question: Is the relative order of different managers' effects defined?
- Implementation (cite): JS: object key (registration) order `kjs/Platform.js:87, 263`; eco: `std::unordered_map` order `rt/PlatformRuntime.hpp:243, 266`.
- Notes or Elm reference behaviour: elm/core #1110 and #1154 show JS outcomes depending on declaration order (`elm-bugs/src/CoreIssue1110PortDeclarationOrderTest.elm:1-12`).
- Options: (a) unspecified; (b) all subscriptions installed before any command runs; (c) a fixed manager order.
- **Ruling:** UNSPECIFIED: the relative order of effects handled by different managers is not defined. (provisional)
- **Reason:** Implementations differ and the documentation promises none.
- **Affects:** dynamic

## A68: Synchronous or queued delivery of an incoming port value
- **Origin:** C-PLT-3
- Construct: host `send` on an incoming port.
- Question: Does `update` run during `send`, or later; may a send made from inside an outgoing subscriber callback observe the new subscriptions?
- Implementation (cite): JS synchronous `kjs/Platform.js:457-468`; eco queued `rt/PortRuntime.cpp:755-779`, `sched.md:174`.
- Notes or Elm reference behaviour: silent in docs; JS behaviour causes elm/core #1141, #1154.
- Options: (a) host interaction is outside the definition; (b) define delivery as an event queued after the current step.
- **Ruling:** CUSTOM: a value arriving on an incoming port is an event; it is handled after the step in progress completes, never during it. (provisional)
- **Reason:** Removes the reentrancy bugs in elm/core #1110, #1141, #1154; matches eco.
- **Affects:** dynamic

## A69: Outgoing port values sent when no host subscriber exists
- **Origin:** C-PLT-4
- Construct: `port out : P -> Cmd msg` used before (or after) the host subscribes.
- Question: Are such values lost or kept?
- Implementation (cite): JS drops (`kjs/Platform.js:375-383`), with a `sleep 0` before the first delivery so init-time values survive the host's subscribe (`:370-372`); eco buffers until first subscriber (`rt/PortRuntime.cpp:550-566`).
- Notes or Elm reference behaviour: silent.
- Options: (a) host-defined; (b) lost; (c) buffered.
- **Ruling:** UNSPECIFIED: what the host does with outgoing values, and whether it has subscribed, is outside the definition. (provisional)
- **Reason:** Host behaviour.
- **Affects:** dynamic

## A70: Timing of outgoing port delivery
- **Origin:** C-PLT-5
- Construct: an update returning a port command.
- Question: Is delivery to the host synchronous with the update or deferred?
- Implementation (cite): JS deferred by the port manager's `sleep 0` after each batch (`kjs/Platform.js:128-145, 370-386`); eco synchronous (`rt/PortRuntime.cpp:179-197`; `eco/docs/embedding.md:34-35`).
- Notes or Elm reference behaviour: silent.
- Options: (a) unspecified "eventually, in order per port"; (b) synchronous.
- **Ruling:** CUSTOM: outgoing port values are delivered to the host after the step that produced them, in order per port; timing is otherwise not defined. (provisional)
- **Reason:** Weakest guarantee both implementations meet.
- **Affects:** dynamic

## A71: Outcome of an incoming value that does not match the port type
- **Origin:** C-PLT-6
- Construct: host sends `1337` to `port p : (String -> msg) -> Sub msg`.
- Question: Is this a program error, a host error, or ignored? Can it end the program?
- Implementation (cite): JS throws to the caller of `send`, Elm state untouched (`kjs/Platform.js:459-461`); eco returns code 2 with the same message, or aborts the process if detected on the eco thread (`rt/PortRuntime.cpp:755-779, 694-697`); `CoreIssue1043` expects `EXIT: 1`.
- Notes or Elm reference behaviour: no-runtime-errors philosophy (author direction) suggests the Elm program never sees the value.
- Options: (a) rejected at the boundary, program unaffected; (b) program terminates.
- **Ruling:** INTENT: an incoming value that does not match the port's type is rejected at the boundary; the program never sees it and is unaffected. (provisional)
- **Reason:** No runtime errors (D2). eco's process abort in one path is recorded as an eco defect.
- **Affects:** dynamic

## A72: Absent flags
- **Origin:** C-PLT-7
- Construct: `Program (Maybe Int) ...` or `Program Json.Decode.Value ...` started without flags.
- Question: What value do absent flags denote?
- Implementation (cite): JS `undefined` (`kjs/Platform.js:37`), rejected by `null`/`Maybe`; eco `null` (`rt/PlatformRuntime.cpp:776-778`; `eco_embed.cpp:271-275`), so `Maybe` flags give `Nothing`.
- Notes or Elm reference behaviour: silent.
- Options: (a) absent flags are `null`; (b) absent flags are an error unless the flags type is `()`.
- **Ruling:** CUSTOM: a program is started with a flags value from the host; absent flags are taken as the JSON value null. (provisional)
- **Reason:** Total and simple; matches eco.
- **Affects:** dynamic

## A73: Range of Int at the boundary
- **Origin:** C-PLT-8
- Construct: incoming `Int` (port or flags) given `1e300`, `9223372036854775808`, or `-0`; outgoing Int above 2^53.
- Question: Which numbers are valid `Int` values at the boundary?
- Implementation (cite): JS: any finite integral double (`json-kjs:45-55`); eco: signed 64-bit (`kc/json/JsonExports.cpp:2054-2059`; `div.md:330-338`).
- Notes or Elm reference behaviour: follows from Elm's Int representation (JS double); see the numeric part of the survey.
- Options: (a) tie to the definition's Int range; (b) implementation-defined.
- **Ruling:** INTENT: an incoming JSON number is accepted as an Int exactly when it is an integer within the implementation's Int range. (provisional)
- **Reason:** Ties the boundary to the abstract Int range (A40).
- **Affects:** dynamic, basis

## A74: Non-JSON values at the boundary
- **Origin:** C-PLT-9
- Construct: outgoing `Float` NaN or Infinity; incoming NaN into `Float`; `Json.Encode.Value` carrying a JS function, DOM node or `undefined`.
- Question: Is the boundary JSON (values as text) or host values?
- Implementation (cite): JS passes JS values through (`json-kjs:63-71`; `kjs/Platform.js:379`); eco is JSON text: NaN out becomes `null` (`div.md:399-402`), Node addon rejects non-serialisable sends (`eco_node_addon.cpp:425-441`).
- Notes or Elm reference behaviour: silent; the compiler builds codecs from `Json.Encode`/`Json.Decode`.
- Options: (a) define the boundary over the JSON value model; (b) over host values.
- **Ruling:** INTENT: the port boundary is defined over the JSON value model (null, booleans, numbers, strings, arrays, objects); non-JSON host values are outside the definition. (provisional)
- **Reason:** A host-independent model of what crosses a port (D11).
- **Affects:** dynamic, basis

## A75: `Bytes` as a port or flags payload
- **Origin:** C-PLT-10
- Construct: `port out : Bytes -> Cmd msg`, `port out : List Bytes -> Cmd msg`, `Program Bytes ...`.
- Question: Is `Bytes` a payload type of the language?
- Implementation (cite): Elm 0.19.1 rejects (`elmc/compiler/src/Canonicalize/Effects.hs:164-179`); eco accepts (`cs/Canonicalize/Effects.elm:295-296`), native only as whole port payload, never in native flags (`cs/LocalOpt/Typed/Module.elm:194-195, 650-651`).
- Notes or Elm reference behaviour: Elm 0.19.1 rejects.
- Options: (a) exclude (Standard Elm); (b) include as an eco extension in an appendix.
- **Superseded by A92** (author, 2026-11-07): Bytes is now a payload type.
- **Ruling:** INTENT: excluded (as A18). (provisional)
- **Reason:** Elm 0.19.1 rejects.
- **Affects:** static, dynamic

## A76: Field order and error reporting for records at the boundary
- **Origin:** C-PLT-11
- Construct: outgoing record; incoming object missing several fields.
- Question: Is the key order of an outgoing object part of the meaning; which error is reported?
- Implementation (cite): keys emitted alphabetically (`elmc/compiler/src/Optimize/Port.hs:66-75`; `cs/LocalOpt/Erased/Port.elm:111-118`); decoding runs alphabetically-last field first (`cs/LocalOpt/Erased/Port.elm:468-476`); eco's host checker walks the descriptor order (`kc/json/JsonExports.cpp:2022-2040`).
- Notes or Elm reference behaviour: silent.
- Options: (a) objects unordered, error text unspecified; (b) specify.
- **Ruling:** INTENT: objects are unordered; error messages are unspecified. (provisional)
- **Reason:** JSON objects are unordered.
- **Affects:** dynamic

## A77: Unit at the boundary: ports versus flags
- **Origin:** C-PLT-12
- Construct: `port p : (() -> msg) -> Sub msg` versus `Program () model msg`.
- Question: Should `()` accept only `null` (ports) but anything (flags)?
- Implementation (cite): `elmc/compiler/src/Optimize/Port.hs:141-149, 247-250`; `cs/LocalOpt/Erased/Port.elm:245-260, 391-396`.
- Notes or Elm reference behaviour: as implemented, deliberately.
- Options: (a) record the asymmetry; (b) unify.
- **Ruling:** IMPLEMENTATION: unit accepts only null on an incoming port, but any value as flags. (provisional)
- **Reason:** Deliberate in both implementations.
- **Affects:** dynamic

## A78: Pre-emption and interleaving of processes
- **Origin:** C-PLT-13
- Construct: `Process.spawn t1 |> andThen (\_ -> Process.spawn t2)`.
- Question: May a process be paused at an `andThen`, as `Process` documentation says, or only at a primitive that waits?
- Implementation (cite): Both schedulers switch only at a binding or empty receive (`kjs/Scheduler.js:151-195`; `sched.md:46-67`).
- Notes or Elm reference behaviour: doc: "we will pause it at an `andThen` and switch over" (`core/Process.elm:53-57`).
- Options: (a) definition allows switching at any `andThen` (weakest); (b) only at waits.
- **Ruling:** CUSTOM: a process may be suspended at any `andThen`; programs may rely only on that. (provisional)
- **Reason:** Weakest guarantee, as the documentation states.
- **Affects:** dynamic

## A79: Unhandled failure in a spawned process
- **Origin:** C-PLT-14
- Construct: `Process.spawn (Task.fail e)`.
- Question: Is the failure observable at all?
- Implementation (cite): JS silent (`kjs/Scheduler.js:158-165`); eco stderr warning (`rt/Scheduler.cpp:993-1000`; `invariants.csv:708`).
- Notes or Elm reference behaviour: silent; failure is isolated to the process in both.
- Options: (a) the process ends, nothing else happens; (b) implementation may report.
- **Ruling:** INTENT: the failing process ends; nothing else happens. Reporting is an implementation matter. (provisional)
- **Reason:** Isolation of processes.
- **Affects:** dynamic

## A80: `Process.kill` of a finished or already killed process
- **Origin:** C-PLT-15
- Construct: `Process.kill pid` twice.
- Question: No-op or error?
- Implementation (cite): JS TypeError (`kjs/Scheduler.js:105`, elm/core #955); eco no-op (`rt/Scheduler.cpp:556-566`).
- Notes or Elm reference behaviour: JS behaviour is a known bug.
- Options: (a) no-op.
- **Ruling:** INTENT: no effect. (provisional)
- **Reason:** No runtime errors; the JS crash is a known bug.
- **Affects:** dynamic

## A81: `Process.sleep` with zero, negative or non-finite delay
- **Origin:** C-PLT-16
- Construct: `Process.sleep 0`, `Process.sleep -5`, `Process.sleep (0/0)`.
- Question: What does the definition say about delays other than positive finite ones?
- Implementation (cite): JS `setTimeout` rules; eco 0/negative immediate, non-finite 1 ms (`div.md:325-328`; `kc/core/ProcessExports.cpp` sanitizeDelayMs comment).
- Notes or Elm reference behaviour: doc gives only "the given number of milliseconds" (`core/Process.elm:87-90`).
- Options: (a) at least max(0, d) ms, non-finite unspecified; (b) treat as host timer semantics.
- **Ruling:** CUSTOM: `Process.sleep d` waits at least max(0, d) milliseconds; for non-finite d the delay is unspecified. (provisional)
- **Reason:** Weakest guarantee.
- **Affects:** dynamic

## A82: Which `main` types and modules make a program
- **Origin:** C-PLT-17
- Construct: `main` not exposed; `main` in an imported module; `main : Html msg`; `main` with parameters.
- Question: Must `main` be exposed; is a static `main` a program with no update loop; what does a non-root `main` mean?
- Implementation (cite): any top-level `main` checked regardless of exports (`elmc/compiler/src/Optimize/Module.hs:246-272`); non-root `main` is an ordinary value (`NonEntryMainEvaluatedOnceTest`); static main rendered once in JS, only evaluated natively.
- Notes or Elm reference behaviour: "I only know how to handle Html, Svg, and Programs" (`elmc/compiler/src/Reporting/Error/Main.hs:39-52`).
- Options: (a) program = root module with `main : Program f m msg` or `main : Html msg`; (b) restrict the definition to `Program`.
- **Ruling:** INTENT: a program is a main module whose `main` has type `Program flags model msg` or a view type (`Html msg`); the latter is a program with no messages. A `main` in any other module is an ordinary value; `main` need not be exposed. (provisional)
- **Reason:** As both implementations treat it.
- **Affects:** static, dynamic

## A83: Browser programs and managers absent on a platform
- **Origin:** C-PLT-18
- Construct: `Browser.element ...` as `main` natively; `Random.generate` or `Browser.Events.onResize` on the native target.
- Question: Is it a property of the language that every `Program` runs `init`, and every effect is performed by some manager?
- Implementation (cite): eco native returns the record without running it (`kc/browser/BrowserExports.cpp:35-45`) and drops leaves with no registered manager (`rt/PlatformRuntime.cpp:471-473`; `kc/EffectManagerRegistry.cpp:13-22`).
- Notes or Elm reference behaviour: in JS every effect module is a registered manager (`elmc/compiler/src/Generate/JavaScript.hs:440-456`).
- Options: (a) define the platform as a parameter of the definition; (b) treat as non-conformance of a platform.
- **Ruling:** CUSTOM: the set of effect managers (and so the effects available) is a parameter of the platform; the definition specifies the Task manager, ports and the program loop, and the observable contract of the others is left to the platform. eco's native gaps are recorded in the appendix. (provisional)
- **Reason:** Platform effects are not language.
- **Affects:** dynamic, basis

## A84: Duplicate port names and name collisions
- **Origin:** C-PLT-19
- Construct: two modules each declaring `port send`; a port named `Task` or `Time`.
- Question: Static error, or load-time failure?
- Implementation (cite): runtime crash at registration in both (`kjs/Platform.js:335-341`; `rt/PortRuntime.cpp:449-468`; `invariants.csv:603`).
- Notes or Elm reference behaviour: no static check.
- Options: (a) state that port names are global and must be unique per program (static rule); (b) leave as runtime failure.
- **Ruling:** INTENT: port names are global to a program and must be unique, and distinct from the names of the platform's effect managers (static rule). (provisional)
- **Reason:** Turns a load-time crash into a static error (D2).
- **Affects:** static, dynamic

## A85: Effect dispatch when an effect-manager handler waits
- **Origin:** C-PLT-20
- Construct: a user-defined effect module whose `onEffects` returns a task that sleeps.
- Question: Must manager handlers complete without waiting?
- Implementation (cite): JS allows it (the manager process just waits) (`kjs/Platform.js:128-145`); eco requires synchronous handlers or the state update is lost (`sched.md:150-152, 215`; `invariants.csv:703`).
- Notes or Elm reference behaviour: effect modules are restricted to core packages in practice (`core/Platform.elm:17-25`).
- Options: (a) effect modules out of scope of the definition (only the managers' observable behaviour defined); (b) specify handler semantics.
- **Ruling:** INTENT: effect modules are out of scope (A16); only the observable behaviour of the core managers is defined. (provisional)
- **Reason:** Kernel-only feature.
- **Affects:** dynamic, basis

## A86: Where the update loop's ordering guarantees stop
- **Origin:** C-PLT-21
- Construct: messages from different sources (two timers, a task and a port).
- Question: Beyond "one message at a time; each update sees the previous model; effects of an earlier update are dispatched before a later one", what is guaranteed?
- Implementation (cite): `kjs/Platform.js:209-254` (FIFO effects queue); eco same (`rt/PlatformRuntime.cpp:318-341`); eco explicitly lists Task/Cmd/Sub/sleep ordering as possibly different (`div.md:442-447`).
- Notes or Elm reference behaviour: silent beyond the effects-queue comment.
- Options: (a) define only the serialisation guarantees; (b) define a full event order.
- **Ruling:** CUSTOM: the definition guarantees only that messages are handled one at a time, each update sees the model the previous update produced, and the effects of an earlier update are dispatched before those of a later one. (provisional)
- **Reason:** Weakest guarantee both implementations meet.
- **Affects:** dynamic
## A87: Integer constants and `number` polymorphism at run time
- **Origin:** raised while writing Appendix D (stage 05)
- Construct: integer constants whose type is Float or a `number` variable; definitions polymorphic in a `number` variable.
- Question: The dynamic semantics erases types, so an integer constant used at Float (`x : Float` with `x = 2`, then `x ^ -1`) would evaluate as an Int, and a `number`-polymorphic definition built only from integer constants would compute with Int arithmetic even when used at Float. What is the value?
- Implementation: eco monomorphises the whole program, so every constant and every arithmetic operation has a concrete type (survey: "An unresolved number is left as number by the type checker; eco's monomorphiser later closes it"). Elm on JavaScript has a single number representation, so integer constants used at Float behave as floats.
- Notes say: silent.
- Options: (a) runtime coercion when an Int meets a Float (incomplete: fails for purely literal `number` code); (b) number specialisation before evaluation; (c) dictionary passing.
- **Ruling:** CUSTOM: before evaluation, the elaborated program is specialised over its `number` variables: a definition whose type scheme quantifies variables of class number is replaced by its default copy (Float for each of those variables, always made, so every binding is evaluated, A59; Int before the revision of A27 on 2026-11-10) and one further copy for each other assignment of Int or Float at which the program uses it; each occurrence refers to the copy for its instance, and every integer constant then has the type Int or Float; a number variable still free is Float (A27). Because the class number admits only Int and Float, the specialisation is finite (at most 2^k copies of a definition with k number variables), even under polymorphic recursion. An integer constant at Float denotes the nearest Float. (provisional)
- **Consequence (audit V2):** because the default copy is always made and evaluated, a definition used only at Int is also evaluated at Float; if that Float evaluation has no result (for example it reaches `Debug.todo`), the program has no meaning. Elm on JavaScript, which evaluates the definition once with its one kind of number, behaves the same. eco, which evaluates only the copies used, runs such a program, and conforms by A94, since the definition gives the program no value; it differs only in the output of `Debug.log` in an unused copy, which is outside the definition (A62; test StandardA87NumberDefaultCopyTest).
- **Reason:** Gives every program a meaning that agrees with both implementations (eco's monomorphisation, JavaScript's single number type) without runtime coercion; finite because Adm_number has two types.
- **Affects:** static, dynamic, basis

## A88: JSON numbers, non-finite floats and negative zero at a port
- **Origin:** audit finding Y6 (decisions recorded only as comments in Chapter 8)
- Construct: Enc at Float of NaN and infinities; incoming numbers beyond the Float range; `-0` at Int and Float ports; the model of JSON numbers.
- Question: What are JSON numbers in the definition, and what happens to values JSON cannot represent?
- Implementation: eco carries JSON text: an outgoing NaN arrives as null; Elm on JavaScript passes JavaScript numbers through, so NaN, infinities and -0 cross unchanged (survey "Ports at Runtime").
- Notes say: silent.
- Options: (a) JSON numbers are finite decimal rationals; non-finite floats encode as null; too-large incoming numbers round to an infinity as Float constants do; -0 is the number 0; (b) host numbers.
- **Ruling:** CUSTOM: option (a). JSON numbers are finite decimal rationals (every Int and every finite Float is exactly representable); Enc at Float of NaN or an infinity is null; an incoming number too large for a finite Float decodes at Float to the infinity of its sign; -0.0 encodes as 0 and an incoming -0 decodes as 0 at Int and +0.0 at Float. Elm on JavaScript is non-conforming where it passes non-finite values or -0 (Appendix E). (provisional)
- **Reason:** A74 defines the boundary over JSON; this fixes the number model it needs.
- **Affects:** dynamic, basis

## A89: Two program-level restrictions
- **Origin:** audit finding X16 (Chapter 9 restrictions without a ruling)
- Construct: a recursive `main`; a program module named like a module of the initial basis.
- Question: Are these programs rejected?
- Implementation: both implementations report BAD MAIN for a recursive `main` (survey "Programs and main"); a module named like a basis module conflicts with the basis module of the same name.
- Notes say: silent.
- Options: (a) reject both statically; (b) leave unspecified.
- **Ruling:** INTENT: option (a): `main` may not refer to itself, directly or through a delayed occurrence, and no module of a program may have the name of a module of the initial basis. (provisional)
- **Reason:** Records the implementations' behaviour as program restrictions (Chapter 9).
- **Affects:** static

## A90: A process that kills itself
- **Origin:** Chapter 8 decision left as a comment (raised by the effects fix)
- Construct: `Process.kill pid` where pid is the calling process.
- Question: Does the calling process end, or continue?
- Implementation: both implementations continue the calling process (survey "Task and Process").
- Notes say: silent.
- Options: (a) no effect: the process continues with `succeed ()`; (b) the process ends.
- **Ruling:** IMPLEMENTATION: option (a). (provisional)
- **Reason:** Matches both implementations; consistent with A80 (kill never fails).
- **Affects:** dynamic

## A91: The qualifier Basics
- **Origin:** audit findings X18 and V3 (derived forms refer to `Basics.True`, `Basics.False`, `Basics.negate`)
- Construct: `import M as Basics` where M is not the module Basics.
- Question: May a program rebind the qualifier `Basics`, which the equivalent forms of Appendix A use?
- Implementation: not tested; both implementations are believed to accept it (their derived forms do not go through the qualifier).
- Notes say: silent.
- Options: (a) a syntactic restriction: only an import of Basics may provide the qualifier Basics; (b) make the meaning of an identifier depend on whether a derived form introduced it.
- **Ruling:** CUSTOM: option (a), stated in Chapter 3's restrictions; together with A89 (no program module is named Basics), `Basics.True`, `Basics.False` and `Basics.negate` always denote the initial basis's bindings. Programs using `import M as Basics` for another M do not elaborate (Appendix E). (provisional)
- **Reason:** Rules work on phrases; option (b) would make identical phrases mean different things.
- **Affects:** syntax, static

## A92: Bytes over ports and in flags
- **Origin:** author decision, 2026-11-07, revisiting A18 and A75
- Construct: `Bytes.Bytes` (elm/bytes) as, or inside, a port payload type or the flags type of `main`.
- Question: Is `Bytes` a payload type of Standard Elm?
- Implementation: eco accepts it in any payload position on its JavaScript target (carried as a Uint8Array) and, natively, only as the whole payload of a port and never in flags (survey "Ports (Static)", "Eco Differences"); Elm 0.19.1 rejects it. The author reports that Lamdera also supports binary data over its boundary (not surveyed here).
- Notes say: a frequently requested feature that Elm 0.19.x has never provided.
- Options: (a) excluded (the former A18, A75); (b) only as the whole payload; (c) anywhere a payload type may appear, ports and flags alike.
- **Ruling:** CUSTOM, decided by the author: option (c). `Bytes` is a payload type: Port(Bytes) holds, so `Bytes` may appear anywhere a payload type may (alone, in tuples, closed records, `Maybe`, `List`, `Array`), in ports and in flags. The boundary model is extended: a boundary value is a JSON value in which a byte sequence may stand wherever a value may; `Enc` at `Bytes` gives the byte sequence of the value and `Dec` at `Bytes` accepts exactly a byte sequence. Values of type `Json.Encode.Value` remain pure JSON. How a host represents a byte sequence is the host's affair (Appendix E). Supersedes A18 and A75.
- **Reason:** Two of the three implementations (eco, Lamdera) already provide it, it is much requested, and binary data has no faithful JSON encoding. Elm 0.19.1 is non-conforming in rejecting such programs; eco's native target is non-conforming for nested `Bytes` and `Bytes` flags.
- **Affects:** static, dynamic, basis

## A93: A `number` variable of a recursive group that one binding's type does not mention
- **Origin:** author decision, 2026-11-09, raised while planning the Elm-to-Lean translator (plans/elm-to-lean-translator.md, B.8)
- Construct: a group of mutually recursive value bindings in which a type variable of class `number` occurs in the type of one binding and, through a use inside the group, in the derivation of another binding whose type does not mention it.
- Question: Number specialisation (A87) copies a declaration once per assignment of Int or Float to its `number` variables, and makes each occurrence refer to the copy for its instance. An occurrence of a binding whose own scheme does not quantify the variable gives it no assignment. Which copy does the occurrence refer to?
- Example (accepted by Elm 0.19.1, which prints `f 3: 1`):
  ```elm
  f n = if n <= 0 then 0 else if g 1 (n - 1) ^ -1 > 0 then 1 else 0
  g y k = if k <= 0 then y + 1 else let _ = f k in y + 1
  main = let _ = Debug.log "f 3" (f 3) in text "done"
  ```
  `g : b -> number -> b` with `b` of class `number`; `f`'s type does not mention `b`, but its body uses `g` at `b`. With `b` Int, `2 ^ -1` is `0` (A43) and `f 3` is `0`; with `b` Float it is `0.5` and `f 3` is `1`.
- Implementation: Elm on JavaScript has one number representation, so the question does not arise there (it behaves as Float). eco monomorphises; not surveyed for this case.
- Notes say: silent. The Discourse threads "Can an Elm program ever be untyped?" and "Untyped Elm programs (oh no not again!)" (2026) hold that a free `number` may be specialised to Int or Float without changing the program; that holds on JavaScript only.
- Options: (a) the variables an occurrence does not fix are Int; (b) the same, stated as a rule of closure: every binding of a group is closed over all the group's `number` variables, so an occurrence instantiates them freshly and A27 makes them Int; (c) reject such programs; (d) Float, as JavaScript behaves.
- **Ruling:** option (b), decided by the author. Closure of a group of value bindings (r:s-dec-group, r:sm-topdec-value) closes the scheme of each binding also over the `number` variables of the other bindings of the group (static-core, sec:static-core-closure); in number specialisation an occurrence assigns each of them, and one that nothing at the occurrence fixes is Float, by A27 (dynamic-core, sec:dynamic-core-numbers). In the example, `f 3` is `1`. (Until the revision of A27 on 2026-11-10 the variable was Int and `f 3` was `0`.)
- **Reason:** Gives the same answer as A27 gives a `number` variable left free, by a rule of the static semantics rather than a special case of specialisation; a variable that a binding's type does not mention changes no instance of its scheme, so typing is unaffected. With A27's Float default, option (b) agrees with option (d) and with Elm 0.19.1, which answers `1` (test StandardA93MutualNumberDefaultTest); an implementation that makes the variable Int does not conform.
- **Affects:** static, dynamic

## A94: What the definition requires of a program it gives no value
- **Origin:** author decision, 2026-11-10, raised by number specialisation (A87): a copy that a program does not need, and that has no value, leaves the program without a value, while Elm on JavaScript and eco may run it.
- Construct: a program that elaborates but has no value: its evaluation reaches `Debug.todo`, or does not end, possibly in a value or a copy the program does not need.
- Question: Must a conforming implementation fail on such a program?
- Implementation: Elm on JavaScript evaluates every top-level value at start-up but evaluates a `number` value once, as a float, and evaluates `(&&) a b` lazily (A56); eco evaluates a top-level value on first use (A59) and makes only the copies a program uses (A87). Each runs some programs the definition gives no value.
- Notes say: silent.
- Options: (a) a conforming implementation must not give such a program a result; (b) the definition requires nothing of such a program; (c) make the definition give these programs values (copies only for uses that are evaluated, lazy evaluation of unused values).
- **Ruling:** option (b), decided by the author. Where a program elaborates and the definition gives it a value, a conforming implementation's result is one of its values; where it gives the program none, the definition requires nothing of an implementation (Appendix E, its introduction and sec:appendix-implementation-numbers).
- **Reason:** Keeps the definition as it is, simple and independent of which code runs, while recording where implementations differ. The difference is visible only in programs that reach `Debug.todo` or do not end. Consequences: eco's evaluation of top-level values on first use (A59), eco's copies made on demand (A87), and Elm on JavaScript's lazy prefix `&&` and `||` (A56) conform; the A56 and A87 rows leave the list of divergences.
- **Affects:** dynamic
- **Scope (2026-11-10, author decision):** the ruling covers a program that has no meaning (the evaluation of its modules has no value). A program that has a meaning is held to its traces (programs, sec:programs-behaviour): where a step has no result, as when `update` reaches `Debug.todo`, no further message is handled, and an implementation that handles further messages does not conform. A crash where the definition gives a value is non-conforming in either case. Appendix E's introduction says so, and its divergences again list Elm/JS's lazy prefix `(&&)`/`(||)` (A56) and its single evaluation of a `let` whose unneeded copy at Int has no value (A87), each in a step of a running program; eco conforms on both.

## A95: Which derivation gives a program its meaning
- **Origin:** author decision, 2026-11-10, from the review of plans/lean-full-definition.md (Part II, "One derivation is not every derivation").
- Construct: a program with several derivations that differ in the types they give integer constants and occurrences, such as `Debug.toString (2 ^ -1)`, whose constants may be typed at a `number` variable (then defaulted, `"0.5"`) or at Int directly (`"0"`).
- Question: Number specialisation reads types from a derivation, and the defaulting of `number` (A27) applied to "a derivation". Which derivation gives the program its meaning?
- Implementation: both implementations infer principal types (Damas-Milner with classes and rows), so the types they use are those of the principal derivation.
- Notes say: silent.
- Options: (a) the principal derivation, defined in Chapter 4, with defaulting applied to it; (b) any derivation, with a coherence theorem (false here: the two derivations above give different values); (c) an algorithmic definition of elaboration.
- **Ruling:** option (a), decided by the author. Chapter 4 defines an instance of a derivation (one substitution respecting classes and rows maps each type of one to the corresponding type of the other, and each type scheme to one no more general) and a principal derivation (one of which every derivation for the program is an instance), and states the property that every program that elaborates has one, unique up to renaming (static-core, sec:static-core-principal). Defaulting of `number` is no longer a further restriction: it is the first step of number specialisation, applied to the principal derivation (dynamic-core, sec:dynamic-core-numbers). Elaboration is unchanged; legality was left to A96, which judges the further restrictions on the same derivation.
- **Reason:** Makes the meaning of every program unique without changing which programs are legal; defaulting chooses a derivation rather than restricting programs, so it belongs with the dynamic semantics. The property is the Damas-Milner principal type property extended to classes (two classes have a greatest common subclass or none), rows with distinct labels, fixed explicit variables and monomorphic groups; its proof is not given in the book, and the Lean plan proves it as complete inference (step 11). Only `number` variables affect values, so no other class needs a default. Tests that tagged the restriction (`core-number-default`) are tagged `sec:dynamic-core-numbers`.
- **Affects:** static, dynamic

## A96: Which derivation the further restrictions are judged on
- **Origin:** author decision, 2026-11-10, raised by A95 and by problem 12 of plans/lean-full-definition.md ("Inhabitants can be empty, and depend on the instance").
- Construct: a match, lambda pattern or destructuring binding whose type differs between derivations, in a program with an uninhabited type (`type V = V V`, or `Never`); and a `main` whose flags type the program leaves undetermined.
- Question: Chapter 4 said "a phrase that elaborates by the rules but breaks one of them is not legal". Irredundancy and exhaustiveness depend on the type of the match, which depends on the derivation, and Chapter 9's `Port(τ1)` on the scheme of `main`. Is a phrase legal when some derivation meets the restrictions, or only when every derivation does?
- Implementation: both implementations check patterns, and flags, against the types they infer, which are the principal ones. Elm 0.19.1 rejects an unannotated `main = Platform.worker { init = \_ -> ( 0, Cmd.none ), ... }` with "BAD FLAGS ... type variables like `flags` cannot be given as flags".
- Notes say: silent.
- Options: (a) some derivation: then `g r = case r of Ok n -> n` is legal by a derivation that takes the error type to be `V`, which leaves `Err` with no inhabitant, and the `main` above is legal by a derivation that takes the flags to be `()`; Elm rejects both. (b) every derivation: then `h x = case x of _ -> 0` is illegal, since a derivation that takes `x` to be `V` makes `_` redundant, and so is nearly every polymorphic match. (c) the principal derivation (A95).
- **Ruling:** option (c), decided by the author. A Core phrase is legal when it meets the syntactic restrictions, elaborates, and its principal derivation meets the further restrictions (static-core, chapter introduction and sec:static-core-further). Principal derivations are defined for a phrase in a context and for a module or program in a static basis, and the property is stated at each level (sec:static-core-principal). Chapter 5's further restrictions are judged in the same way (static-modules, sec:static-modules-further), and the scheme of `main` in r:p-stat-main-program and r:p-stat-main-view is its principal scheme, so an undetermined flags type is a type variable and not a port type (programs, after the elaboration rules).
- **Reason:** One derivation decides legality, the type of `main`, and the meaning of a program, and it is the one implementations use; options (a) and (b) both differ from Elm. Number specialisation does not change the outcome: it replaces only `number` variables, a variable and Float both have the single inhabitant `_`, and integer patterns elaborate at Int (r:s-atpat-scon). The ruling does not settle the separate question of empty types (`Err e -> never e` on `Result Never Int` breaks irredundancy at the principal type too); that remains a finding of plans/lean-full-definition.md, problem 12. In the Lean plan, a refusal needs only the principal derivation, and a legality theorem needs principality (step 11).
- **Affects:** static
- **Consequence (A97, 2026-11-10):** once every type has inhabitants (A97), the further restrictions of the Core give the same answer in every derivation, so the examples with `type V = V V` under options (a) and (b) no longer arise; the ruling still decides the type of `main` (an undetermined flags type), and makes the Core's statement definite without that argument.
- **Corrections (2026-11-10, review):** (1) a module generates type names, so an instance of a module derivation also renames them by a bijection, and the property is stated for Core phrases (static-core, sec:static-core-principal) and for modules (static-modules, sec:static-modules-principal), not for programs: a program whose flags nothing fixes has derivations with flags (), Int, String, none an instance of another. Chapter 9's rules take each premise about a module from a principal derivation. (2) Section 4.9 moved after the inference rules. (3) Number flags: rule r:p-stat-main-program checks Port on the flags type of the principal scheme before the default, so an unannotated `main` whose `init` is `\n -> (n + 1, Cmd.none)` does not elaborate, as Elm 0.19.1 reports (BAD FLAGS: "type variables like `number` cannot be given as flags"); test StandardA96NumberFlagsTest.

## A97: Types whose every inhabitant is infinite
- **Origin:** author decision, 2026-11-10, from plans/lean-full-definition.md, problem 12 ("Inhabitants can be empty") and "Findings of Part II".
- Construct: a match at a type one of whose parts has no finite inhabitant: `Never`, whose one constructor `JustOneMore` takes a `Never`, and `type V = V V`.
- Question: The inhabitants of a type were finite phrases (static-core, sec:static-core-further), so these types had none. Then `Err e -> never e` on a `Result Never Int` covered no inhabitant and broke irredundancy, and `case m of Nothing -> 0` on a `Maybe Never` was exhaustive. Is that intended?
- Implementation: Elm 0.19.1 (Nitpick/PatternMatches) and eco (compiler/src/Compiler/Nitpick/PatternMatches.elm, `isUseful`, `numAlts`) count the constructors of a type and never ask whether one is inhabited. Elm 0.19.1, tested 2026-11-10: accepts `Ok n -> n ; Err e -> never e` on `Result Never Int`; rejects `Nothing -> 0` on `Maybe Never` and on `Maybe V` (MISSING PATTERNS); accepts `Ok n -> n ; Err (V _) -> 0` on `Result V Int` and `V (V _) -> 0` on `V`. The finite reading gave the opposite answer in all five.
- Notes say: elm/core documents `Never` as a type with no values, and `never` for the branch that handles one.
- Options: (a) inhabitants may be infinite (the clauses read coinductively); (b) treat every type as inhabited, informally; (c) define the restrictions by the pattern-matrix algorithm; (d) keep finite inhabitants and record the divergence from Elm.
- **Ruling:** option (a), decided by the author. The clauses defining inhabitants are read coinductively, so `V` has the one inhabitant `V (V (V ...))` and `Never` the one inhabitant `JustOneMore (JustOneMore ...)`; every type has an inhabitant, and every constructor gives inhabitants of its type at every instance. Inhabitants are not values: no value has type `Never`; an inhabitant describes what a pattern may be asked to match (static-core, sec:static-core-further).
- **Reason:** Agrees with Elm and eco on all five programs, and keeps the restrictions declarative. Where every type a match involves has a finite inhabitant, nothing changes: a pattern examines a finite part of an inhabitant, and an infinite inhabitant cut off below that depth and completed with finite inhabitants is covered by the same patterns. Consequences: the restrictions are the standard check that takes every constructor to be possible, and they give the same answer in every derivation (a part of a match's type that the principal derivation leaves a variable is matched only by patterns that cover everything), which settles A96 for the Core. Tests StandardA97NeverErrBranchTest, StandardA97MaybeNeverMissingJustTest and StandardA97SelfOnlyTypeTest.
- **Affects:** static

## A98: The order of a module's type declarations
- **Origin:** author decision, 2026-11-12, from plans/lean-full-definition/step-10-end-to-end.md, issue 9 (finding B6 at the program level), found while proving that a program's number specialisation is unique.
- Construct: a custom type that mentions a local alias declared after it, spelt like an imported type: `type T = T String` followed by `type alias String = Int`.
- Question: The book elaborated a module's type declarations as one phrase (r:sm-topdec-types), in a context containing all of them, and also let r:sm-topdec-seq split that phrase at a separator, saying the two give the same result. They did not here: as a whole, `String` is the local alias and `T : Int -> T`; split, `type T = T String` was elaborated before the alias existed and `T : String -> T`. The module then had two derivations, neither an instance of the other, and the meaning of a program importing it depended on the derivation. Does the order of type declarations matter?
- Implementation: Elm 0.19.1, 0.19.2 and 0.19.3, tested 2026-11-12: with the type first or the alias first, `T 3` compiles, `T "s"` is a TYPE MISMATCH ("`T` needs ... `M.String`"), `f (T n) = n + 1` compiles and `String.length` on the field is a TYPE MISMATCH. A module's type declarations are one scope; the local name denotes the local type everywhere in the module.
- Options: (a) keep both rules, and judge principality on the split too, so such a module has no principal derivation and is refused; (b) let r:sm-topdec-seq split a type-declaration phrase only where the result is the whole phrase's; (c) r:sm-topdec-seq does not split a type-declaration phrase.
- **Ruling:** option (c), decided by the author. Rule r:sm-topdec-seq has the side condition that its separator is not one of a type-declaration phrase, so a module's type declarations are elaborated together by r:sm-topdec-types, and their order does not matter.
- **Reason:** Agrees with Elm in both orders; (a) refuses a program Elm accepts, and (b) gives the same results as (c) with a rule that never contributes. No legal program tells (b) and (c) apart: a split that succeeds where the whole fails needs aliases that refer to one another, which res:modules-alias-not-recursive refuses. Tests StandardA98TypeBeforeAliasTest and StandardA98TypeBeforeAliasStringMismatchTest.
- **Affects:** static
