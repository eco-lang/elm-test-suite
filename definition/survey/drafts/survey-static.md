# Survey Part 2: Static Semantics

Scope: scoping, canonicalisation, type inference and module-level static checks of Elm 0.19.1 as
implemented by the eco front end. Lexis and grammar, evaluation, and the Cmd/Sub/Task/port runtime
are surveyed elsewhere; the static checks on ports are here.

Background fact used throughout: eco's front end "is forked from Guida, which is a port of the
stock Elm compiler from Haskell to Elm", and keeps "Elm's grammar, scoping rules, type system and
error messages" (DD/theory/compiler/front-end.md:7). Where this survey does not flag a divergence,
Elm 0.19.1 is presumed to behave the same, but that presumption has not been checked against the
Haskell source unless stated.

## Sources

Path abbreviations used in every cite below:

| Prefix | Absolute path |
|---|---|
| `C/` | /home/rupert/sc/gitlab/eco-compiler/compiler/src/Compiler/ |
| `B/` | /home/rupert/sc/gitlab/eco-compiler/compiler/src/Builder/ |
| `CT/` | /home/rupert/sc/gitlab/eco-compiler/compiler/tests/ |
| `T/` | /home/rupert/sc/gitlab/eco-compiler/test/ |
| `CE/` | /home/rupert/sc/gitlab/eco-compiler/test/elm-compile-errors/src/ |
| `DD/` | /home/rupert/sc/gitlab/eco-compiler/design_docs/ |
| `core/` | /home/rupert/.eco/0.2.0/packages/elm/core/1.0.5/src/ |

Files read (principal ones):

| Area | Files |
|---|---|
| Pipeline | C/Compile.elm (phases and error wrapping, :9-32), C/Error.elm:40-74 |
| Scoping | C/Canonicalize/Environment.elm, Environment/Foreign.elm, LocalEnvironment.elm, Expression.elm, Pattern.elm, Module.elm, Dups.elm |
| Types (canonical) | C/Canonicalize/Type.elm, C/IR/Canonical.elm, C/IR/Canonical/Interface.elm |
| Inference | C/Type/Type.elm, Unify.elm, Solve.elm, Occurs.elm, Instantiate.elm, Constrain/Typed/{Expression,Pattern,Module}.elm, C/Core/Name.elm |
| Ports and effects | C/Canonicalize/Effects.elm, C/Parse/Module.elm:330-397, C/Parse/Error.elm:150-185 |
| Exhaustiveness | C/Nitpick/PatternMatches.elm, C/Nitpick/Error.elm |
| `main` | C/LocalOpt/Error.elm, C/LocalOpt/Erased/Module.elm:300-447, C/LocalOpt/Typed/Module.elm:140-200 |
| Error catalogues | C/Canonicalize/Error.elm, C/Type/Error.elm, C/Canonicalize/ImportError.elm, B/Reporting/Exit.elm |
| Initial basis | core/Basics.elm, core/List.elm, core/Platform.elm, C/Parse/DefaultImports.elm |
| Divergences | DD/elm-divergence.md section 4 (:179-312), DD/theory/compiler/front-end.md |
| Tests | CE/*.elm (223 files), T/eco-divergence/src, T/elm/src, CT/SourceIR/*FailsCases.elm |

Phase order (each phase runs only if the previous one succeeded): parse and header checks;
canonicalisation (`BadNames`); type checking (`BadTypes`); pattern checks (`BadPatterns`);
optimisation, which carries the `main` checks (`BadMains`) (C/Compile.elm:9-12, :30-32;
C/Error.elm:57-74). Within canonicalisation: imports, then the module's own types and values, then
top-level values, then effects, then exports; the first failing step ends it (C/Canonicalize/Module.elm:95-99).

## Scoping and Recursion

### Namespaces and environments

| Fact | Cite |
|---|---|
| Values, types and constructors are three separate namespaces, each checked for duplicates on its own; a type and a constructor may share a name. | C/Canonicalize/LocalEnvironment.elm:35-38 |
| Operators are a fourth table, only ever unqualified. | C/Canonicalize/Environment.elm:14-19 |
| Bare names: one table per kind. Qualified names: one table per prefix (import alias, or module name if no alias). | C/Canonicalize/Environment.elm:14-19, :96-124 |
| A bare value is `Local` (bound in an expression), `TopLevel` (module's own), `Foreign` (imported) or `Foreigns` (ambiguous import). | C/Canonicalize/Environment.elm:178-197 |
| Qualified values are always foreign: a module cannot refer to its own top-level value as `M.x`. | C/Canonicalize/Environment.elm:96-100; C/Canonicalize/Expression.elm:1643-1676 |
| Ambiguity is lazy: two imports exposing one name is recorded as `Ambiguous` and is only an error when the name is used (`AMBIGUOUS NAME`). | C/Canonicalize/Environment.elm:21-25; C/Canonicalize/Environment.elm:145-170 (`mergeInfo`) |
| Two entries from the same home merge without ambiguity. | C/Canonicalize/Environment.elm:145-158 |
| The type `List` (arity 1) is in scope before any import. | C/Canonicalize/Environment/Foreign.elm:22, :118-122 |
| A module's own top-level values, ports and effect names replace imported values of the same name (no ambiguity, no error). | C/Canonicalize/LocalEnvironment.elm:105-122 |
| Local types replace imported types; local constructors replace imported constructors. | C/Canonicalize/LocalEnvironment.elm:217-230, :555-560 |
| References to `Debug` values become `VarDebug` (so `--optimize` can find them). | C/Canonicalize/Expression.elm:1606-1630 |
| Kernel references `Elm.Kernel.X.f` / `Eco.Kernel.X.f` resolve only inside a kernel package, and are not checked to exist. | C/Canonicalize/Expression.elm:28-31, :1664-1672 |

### Shadowing

| Fact | Cite |
|---|---|
| Every local binder (function and lambda parameters, case-branch pattern variables, `let` names, record-pattern fields, `as` names) goes through `addLocals`. | C/Canonicalize/Environment.elm:272-295; C/Canonicalize/Module.elm:344, :375; C/Canonicalize/Expression.elm:917-921 |
| A new local whose name is already `Local` or `TopLevel` is a `Shadowing` error. | C/Canonicalize/Environment.elm:302-321 |
| A new local may shadow an imported (`Foreign`/`Foreigns`) value without error. | C/Canonicalize/Environment.elm:310-314 |
| Report title `SHADOWING`; message cites linters as the reason. | C/Canonicalize/Error.elm:1052-1066 |
| Shadowing does not apply to types, type variables or constructors (only `vars` are checked). | C/Canonicalize/Environment.elm:279-295 |

Evidence: CE/ShadowingAnArgumentShadowingATopLevelValueTest.elm, CE/ShadowingShadowingInLambdaTest.elm,
CT/SourceIR/CanonicalizeFailsCases.elm:222-261.

### Duplicates

| Construct | Error | Cite |
|---|---|---|
| Two top-level values (or ports, or effect names) of one name | `DuplicateDecl` (`NAME CLASH`) | C/Canonicalize/LocalEnvironment.elm:131-142 |
| Two types (union or alias) of one name | `DuplicateType` | C/Canonicalize/LocalEnvironment.elm:188-207 |
| Two constructors of one name, across all unions and record-alias constructors of the module | `DuplicateCtor` | C/Canonicalize/LocalEnvironment.elm:539-553 |
| Duplicate field in a record literal, record update or record type | `DuplicateField` | C/Canonicalize/Expression.elm:373, :392; C/Canonicalize/Type.elm:143-152 |
| Duplicate alias / union type parameter | `DuplicateAliasArg` / `DuplicateUnionArg` | C/Canonicalize/LocalEnvironment.elm:433, :468 |
| A name bound twice in one pattern, one parameter list, or one `let` | `DuplicatePattern` (contexts: lambda args, function args, case branch, let binding, destructure) | C/Canonicalize/Error.elm:239-244; C/Canonicalize/Pattern.elm:96-135; C/Canonicalize/Expression.elm:917 |
| Name exported twice | `ExportDuplicate` (`REDUNDANT EXPORT`) | C/Canonicalize/Module.elm:457 |

### Recursion and the cyclic-value check

Uses are classified while canonicalising: a use is _direct_ if evaluated when the enclosing
definition is evaluated, _delayed_ if inside a lambda or inside the body of a `let` definition that
has parameters (C/Canonicalize/Expression.elm:13-24, :128-140).

Top level, two phases (C/Canonicalize/Module.elm:22-39):

| Phase | Rule | Cite |
|---|---|---|
| 1 | Values are grouped into SCCs by every name used (direct or delayed). Acyclic: `Declare`; cyclic: `DeclareRec`, type-checked together. Order is dependency order, not source order, so a top-level value may be used before it is written. | C/Canonicalize/Module.elm:28-32, :178-181, :216-235 |
| 2 | Inside each cyclic group: a definition with parameters has no edges; a zero-parameter definition has edges to the names it uses directly. Any remaining cycle is `RecursiveDecl` (`CYCLIC DEFINITION`). | C/Canonicalize/Module.elm:34-39, :238-260, :400-423 |

So at top level `x = \_ -> x ()` is accepted (use is delayed), while `x = x + 1` and `a = b; b = a`
are rejected.

`let`: the bindings of one `let` form a dependency graph (by all free locals); SCCs become nested
`Let`, `LetDestruct`, `LetRec`. A recursive group is accepted only if every member is a definition
with parameters; any zero-parameter member or any destructuring in the cycle is `RecursiveLet`
(`CYCLIC VALUE`) (C/Canonicalize/Expression.elm:39-47, :1362-1399). Unlike top level, the
direct/delayed distinction is not consulted: `let f = \n -> f n in ...` is rejected
(C/Canonicalize/Expression.elm:1376-1381).

Mutual recursion between `let` functions with parameters is allowed (T/elm/src/LetMutualRecursionBetweenLocalsTest.elm).

`main` may not be in any recursive group: `BadCycle` (`BAD MAIN`), checked in the optimiser, and
before the `main` type check (C/LocalOpt/Erased/Module.elm:311-332; C/LocalOpt/Error.elm:115-123;
CT/SourceIR/MainFailsCases.elm:110-111).

## Types and Inference

### Type language

Canonical types (`Can.Type`): type variable, named type applied to arguments (`TType home name args`),
function, record with optional extension variable (`TRecord fields (Maybe ext)`), unit, 2- or
3-tuple, alias use (`TAlias home name args body`) (C/Canonicalize/Type.elm:92-136). The solver's
types mirror these: `AliasN`, `VarN`, `AppN`, `FunN`, `EmptyRecordN`, `RecordN fields ext`, `UnitN`,
`TupleN a b (Maybe c)` (C/Type/Type.elm:162-187).

| Rule | Cite |
|---|---|
| Every type and alias use must supply exactly its number of parameters (no partial application of type constructors, no higher kinds); otherwise `BadArity` (`TOO FEW ARGS` / `TOO MANY ARGS`). | C/Canonicalize/Type.elm:201-230 |
| Tuples have 2 or 3 components, in types, expressions and patterns; 4+ is `TupleLargerThanThree` (`BAD TUPLE`). Guida's larger tuples are removed. | C/Canonicalize/Type.elm:121-132; C/Canonicalize/Expression.elm:438-454; C/Canonicalize/Pattern.elm:355; DD/theory/compiler/front-end.md:7 |
| Aliases are kept as alias uses (not expanded) in canonical types. | C/Canonicalize/Type.elm:14-18 |
| An extensible record's extension is a type variable name. | C/Canonicalize/Type.elm:113-114 |

Built-in types of the basis: `Int`, `Float`, `Bool(..)`, `Order(..)`, `Never` from `Basics`
(core/Basics.elm:1-15, :121, :144, :426, :444, :948); `List` (built in, see above);
`Char`, `String` (core/Char.elm:62; core/String.elm:93); `Maybe`, `Result`
(core/Maybe.elm:39; core/Result.elm:32); `Program flags model msg`, `Task`, `Cmd msg`, `Sub msg`
(core/Platform.elm:42, :83; core/Platform/Cmd.elm:47; core/Platform/Sub.elm:49).

### Annotations, rigid and flexible variables

| Rule | Cite |
|---|---|
| An annotation is quantified over every type variable it mentions, including record extension variables and variables in alias arguments (implicit quantification). | C/Canonicalize/Type.elm:63-75 |
| Variables named in an annotation become _rigid_; inferred variables are _flexible_. | C/Type/Type.elm:420-437; C/Type/Constrain/Typed/Expression.elm:16-18 |
| Annotation variables are scoped: for an annotated definition, only annotation variables not already in scope (`rtv`) become new rigid variables; a nested annotation that reuses an outer annotation's variable name means the same variable. | C/Type/Constrain/Typed/Expression.elm:88-97, :128-143, :244-252 |
| The body of an annotated definition is checked against the annotation with a `FromAnnotation` expectation; the parameters take their types from the annotation's arrows, seen through aliases. | C/Type/Constrain/Typed/Expression.elm:147-163; C/Canonicalize/Expression.elm:1318-1354 |
| More parameters than arrows in the annotation is `AnnotationTooShort` (`BAD TYPE ANNOTATION`); fewer parameters than arrows (point-free) is fine. | C/Canonicalize/Expression.elm:1328-1330, :1355-1359; C/Canonicalize/Error.elm:352-362 |
| A rigid variable unifies only with a flexible variable, `Error`, or (for a rigid constrained variable) a flexible constrained variable it subsumes; it never unifies with a structure, another rigid variable, or an alias. | C/Type/Unify.elm:22-26, :575-610 |
| An annotation may be less general than the inferred type (body is instantiated); it may not be more general (rigid variables would have to unify with structure). | C/Type/Unify.elm:575-610; CE/TypeMismatchRigidVarAsMaybeTest.elm, CE/TypeMismatchTwoRigidVarsTest.elm |
| Every rigid variable must be generalised at its `let`; one that is not crashes the solver with a "compiler bug" message (no user error). | C/Type/Solve.elm:30-31, :439-440, :459-483 |

### Let-polymorphism and generalisation

| Rule | Cite |
|---|---|
| Algorithm: constraint generation then a rank-based HM solver with union-find; each `let` header solved one rank deeper and generalised; uses instantiate a fresh copy. | C/Type/Solve.elm:3-34; C/Type/Type.elm:16-30, :128-134 |
| Unannotated definition, with or without parameters: its type is generalised in the scope that sees it (`CLet [] vars ...`). There is no value restriction and no monomorphism restriction: `let n = 5` gives `n : number`, usable as `Int` and `Float`. | C/Type/Constrain/Typed/Expression.elm:88-126; T/elm/src/LetNumberDualUseTest.elm |
| Destructuring `let` also generalises its pattern variables (`CLet [] (patternVar :: pvars) ...`). | C/Type/Constrain/Typed/Expression.elm:2223-2242 |
| Lambda and function parameters, and case-branch variables, are monomorphic. | C/Type/Constrain/Typed/Expression.elm:1875-1903 |
| Recursive group: unannotated members share one set of flexible variables for the whole group (monomorphic within the group), generalised together for the body; annotated members are in scope at their annotated (polymorphic) type for the whole group. | C/Type/Constrain/Typed/Expression.elm:168-197, :199-218 |
| Polymorphic recursion is therefore possible only through annotations; a direct self-call at another type inside an annotated body is a `TYPE MISMATCH`. | DD/elm-divergence.md:224-229 |
| Top-level declarations are nested in dependency order (from canonicalisation); the module's types are the environment at the innermost `CSaveTheEnvironment`. | C/Type/Constrain/Typed/Module.elm:15-24, :100-130 |
| Integer literals and negation get a fresh flexible `number` variable; float, char, string and unit literals have fixed types. | C/Type/Constrain/Typed/Expression.elm:483-494, :552-600 |
| An unresolved `number` is left as `number` by the type checker; eco's monomorphiser later closes it (to `Int`). | DD/theory/compiler/front-end.md:54 |

### Occurs check

| Rule | Cite |
|---|---|
| Unification itself does not run an occurs check (except before accepting a `List`/tuple as comparable). | C/Type/Unify.elm:44-45, :806-823 |
| After a `let` body is solved, each name bound by that `let` is checked for an infinite type; a cycle gives `InfiniteType` (`INFINITE TYPE`). Top-level definitions are `let`s in the constraint tree, so they are checked too. | C/Type/Solve.elm:33-34, :375-379, :452-454, :532-555; C/Type/Error.elm:2840 |
| Occurs follows alias arguments only, not alias bodies. | C/Type/Occurs.elm:28-37 |

Evidence: CE/InfiniteTypeSelfAppliedArgumentOnBothSidesTest.elm, CT/SourceIR/TypeCheckFailsCases.elm:799-817, :1273-1283.

### Expression typing summary (constraint generation)

| Form | Constraint | Cite |
|---|---|---|
| `if` | each condition `Bool`; all branches one type | C/Type/Constrain/Typed/Expression.elm:1265-1300, :1270 |
| `case` | subject type = every pattern's type; all branch bodies one type | C/Type/Constrain/Typed/Expression.elm:1741-1874 |
| list literal | all entries one type | C/Type/Constrain/Typed/Expression.elm:1904-1950 |
| operator `a op b` | operator's annotation instantiated (`CForeign`) | C/Type/Constrain/Typed/Expression.elm:424-425, :812-958 |
| call | function type unified with argument types; too many arguments is `TOO MANY ARGS` (`CallArity`) | C/Type/Constrain/Typed/Expression.elm:1007-1220; C/Type/Error.elm:1391-1436 |
| variable | local / top-level: instance of its scheme (`CLocal`); foreign, constructor, operator, Debug: instance of its annotation (`CForeign`) | C/Type/Constrain/Typed/Expression.elm:463-481 |
| kernel reference | annotation from `KernelIntrinsics` if it has a row; otherwise no constraint (kernel packages only) | C/Type/Constrain/Typed/Expression.elm:39-41, :469-475 |

## Constrained Type Variables

### Naming

| Rule | Cite |
|---|---|
| A type variable is constrained by the _prefix_ of its name: `number*`, `comparable*`, `appendable*`, `compappend*` (`String.startsWith`). So `number1`, `comparable2` and also `numberOfThings`, `comparableKey` are constrained. | C/Core/Name.elm:196-223; C/Type/Type.elm:416-452 |
| Distinct names are distinct variables even with the same class (`comparable` vs `comparable2`). | CE/TypeMismatchDifferentlyNamedComparableVarsTest.elm |
| The same name applies to rigid (annotation) and flexible variables. | C/Type/Type.elm:420-437 |
| Class membership after solving is read from the solver root, not the name. | DD/theory/compiler/front-end.md:60 |

### Which types satisfy each class (flexible variable meeting a structure)

From C/Type/Unify.elm:28-34, :718-733, :746-800.

| Type | `number` | `comparable` | `appendable` | `compappend` |
|---|---|---|---|---|
| `Basics.Int`, `Basics.Float` | yes | yes | no | no |
| `String.String` | no | yes | yes | yes |
| `Char.Char` | no | yes | no | no |
| `List t` | no | iff `t` comparable | yes (any `t`) | iff `t` comparable |
| 2- or 3-tuple | no | iff every component comparable | no | no |
| `Bool`, unit, records, functions, `Array`, `Maybe`, custom types | no | no | no | no |
| alias | through its expansion | same | same | same |

Comparable element checks unify each element with a fresh flexible `comparable` at the element's
rank, after an occurs check on the structure (C/Type/Unify.elm:771-823, :825-842).

### Two flexible constrained variables (joins)

From C/Type/Unify.elm:651-701.

| meet | `number` | `comparable` | `appendable` | `compappend` |
|---|---|---|---|---|
| `number` | number | number | mismatch | mismatch |
| `comparable` | number | comparable | compappend | compappend |
| `appendable` | mismatch | compappend | appendable | compappend |
| `compappend` | mismatch | compappend | compappend | compappend |

A plain flexible variable takes the constrained content (C/Type/Unify.elm:535-570, :641-642).

### Rigid constrained variables

A rigid constrained variable (from an annotation) accepts only: a flexible plain variable; a
flexible constrained variable of the same class; a flexible `comparable` if the rigid is `number`;
a flexible `comparable` or `appendable` if the rigid is `compappend` (C/Type/Unify.elm:704-711,
:575-610, :629-634). Everything else mismatches, including a concrete `Int` against a rigid
`number`, a rigid `comparable` used as `number`, and two different rigid variables.

Evidence: CE/TypeMismatchRigidComparableAsNumberTest.elm, CE/TypeMismatchRigidNumberAs*Test.elm (alias,
function, Maybe, record, rigid var, tuple, unit), CE/TypeMismatchRigidCompappendAsIntTest.elm,
CE/TypeMismatchRigidAppendableAddedTest.elm, CE/TypeMismatchCompappendAgainstARigidVarTest.elm.

### Initial basis using classes

| Name | Type | Fixity | Cite |
|---|---|---|---|
| `(+)`, `(-)`, `(*)` | `number -> number -> number` | left 6, left 6, left 7 | core/Basics.elm:82-84, :168-186 |
| `(/)` | `Float -> Float -> Float` | left 7 | core/Basics.elm:85, :203 |
| `(//)` | `Int -> Int -> Int` | left 7 | core/Basics.elm:86, :225 |
| `(^)` | `number -> number -> number` | right 8 | core/Basics.elm:87, :235 |
| `(==)`, `(/=)` | `a -> a -> Bool` | non 4 | core/Basics.elm:75-76, :348-357 |
| `(<)`, `(>)`, `(<=)`, `(>=)` | `comparable -> comparable -> Bool` | non 4 | core/Basics.elm:77-80, :367-385 |
| `max`, `min` / `compare` | `comparable -> comparable -> comparable` / `... -> Order` | | core/Basics.elm:395-418 |
| `(++)` | `appendable -> appendable -> appendable` | right 5 | core/Basics.elm:81, :510 |
| `(&&)`, `(\|\|)` | `Bool -> Bool -> Bool` | right 3, right 2 | core/Basics.elm:73-74 |
| `(<\|)`, `(\|>)` | apL, apR | right 0, left 0 | core/Basics.elm:71-72 |
| `(<<)`, `(>>)` | composition | left 9, right 9 | core/Basics.elm:88-89 |
| `(::)` | `a -> List a -> List a` | right 5 | core/List.elm:41, :106 |
| `negate`, `abs`, `clamp` | over `number` | | core/Basics.elm:566-592 |

`infix` declarations are parsed only in kernel projects (C/Parse/Module.elm:12-14). Two operators of
equal precedence group only if both are left- or both right-associative; anything else (including
`non`) is `Binop` (`INFIX PROBLEM`), so `a == b == c` is rejected (C/Canonicalize/Expression.elm:33-37, :766-780, :848-860).

## Records and Rows

| Rule | Cite |
|---|---|
| Record literal: closed record type (`RecordN fields EmptyRecordN`); duplicate fields are `DuplicateField`. | C/Type/Constrain/Typed/Expression.elm:1951-1976; C/Canonicalize/Expression.elm:384-401 |
| Field access `e.f`: `e : { ext \| f : t }` with fresh `ext`, `t`; result `t`. | C/Type/Constrain/Typed/Expression.elm:1441-1510 |
| Accessor `.f`: `{ ext \| f : t } -> t`. | C/Type/Constrain/Typed/Expression.elm:2193-2215 |
| Record update `{ r \| f1 = e1, ... }`: base `r` must have type `{ ext \| f1 : t1, ... }` and the result has the same type as `r`, so updated fields keep their types and no field can be added. Duplicate updated fields are `DuplicateField`. The base is syntactically a variable. | C/Type/Constrain/Typed/Expression.elm:2024-2085; C/Canonicalize/Expression.elm:365-382; C/IR/Source.elm:379, :410 |
| Record pattern `{ a, b }`: matches `{ ext \| a : ta, b : tb }` (open), binds `a`, `b`. | C/Type/Constrain/Typed/Pattern.elm:208-241 |
| Rows unify field by field after gathering fields along extension chains and through aliases. Shared fields unify; fields only on one side are pushed into the other side's extension as a fresh record; if both sides have own fields they share a fresh extension variable. | C/Type/Unify.elm:54-58, :1047-1110 |
| Closed record vs record with own fields: mismatch unless the fields are empty. | C/Type/Unify.elm:999-1011 |
| When gathering, a field name appearing more than once along a chain: the outermost occurrence wins. | C/Type/Unify.elm:1207-1226 |
| A rigid extension variable cannot absorb extra fields (it is rigid). | CE/TypeMismatchRigidExtensionWhereClosedTest.elm, CE/TypeMismatchSameRigidExtensionTest.elm |
| Record types and record literals limited to 2047 fields (eco). | C/IR/Runtime/HeapLimits.elm:49-51; C/Canonicalize/Type.elm:143-148 |

Record aliases and constructors:

| Rule | Cite |
|---|---|
| An alias whose canonical body is a closed record type `{ ... }` defines a constructor of the same name: a curried function of the fields in declaration order returning the alias applied to its parameters. | C/Canonicalize/LocalEnvironment.elm:578-605, :614-628; C/IR/Canonical.elm:486-507 |
| An alias of an extensible record, or of another alias, or of any non-record, defines no constructor. | C/Canonicalize/LocalEnvironment.elm:597-604; C/Canonicalize/Environment.elm:216-221 |
| The record constructor cannot be used in a pattern (`PatternHasRecordCtor`, `BAD PATTERN`). | C/Canonicalize/Pattern.elm:297; C/Canonicalize/Error.elm:816-817 |
| Importing an alias by name (without `(..)`) also brings its record constructor. | C/Canonicalize/Environment/Foreign.elm:392-403 |
| Extensible record aliases `type alias Named r = { r \| name : String }` must list `r` as a parameter (aliases must bind exactly the variables their body uses). | C/Canonicalize/LocalEnvironment.elm:450-495 |

Evidence: CE/TypeMismatchUpdateValueTest.elm, CE/TypeMismatchUpdateOfAnEmptyRecordTest.elm,
CE/TypeMismatchUpdateOfANearFieldTest.elm, CE/TypeMismatchExtensibleRecordMissingAFieldTest.elm,
CE/TypeMismatchFlexibleRecordWithAnExtraFieldWhereClosedTest.elm, CE/TypeMismatchFieldTypoTest.elm,
T/elm/src/RecordNarrow06RowPolyAnnotationTest.elm.

## Custom Types and Aliases

| Rule | Cite |
|---|---|
| Custom type: parameters must be distinct; every type variable used in a constructor must be a parameter (`TypeVarsUnboundInUnion`, `UNBOUND TYPE VARIABLE(S)`); unused parameters (phantom types) are allowed. | C/Canonicalize/LocalEnvironment.elm:416-447; C/Canonicalize/Error.elm:1149-1150 |
| Type alias: the parameters must be exactly the variables the body uses, including extension variables; unused (phantom) parameters and unbound variables are both errors (`TypeVarsMessedUpInAlias`: `UNUSED TYPE VARIABLE(S)`, `UNBOUND TYPE VARIABLE(S)` or `TYPE VARIABLE PROBLEMS`). | C/Canonicalize/LocalEnvironment.elm:450-495; C/Canonicalize/Error.elm:1152-1304 |
| Recursive aliases are forbidden: aliases are ordered by SCC over the unqualified type names in their bodies; a self-reference or a multi-alias cycle is `RecursiveAlias` (`ALIAS PROBLEM`), whose report suggests a `type`. Recursion through a custom type is fine. | C/Canonicalize/LocalEnvironment.elm:16-21, :240-315, :382-410; C/Canonicalize/Error.elm:1593-1606 |
| Unions are entered before aliases, so an alias may name any local union and any alias declared later. | C/Canonicalize/LocalEnvironment.elm:184-185, :207-209 |
| Custom types may be recursive and mutually recursive (constructors canonicalised with all local types in scope). | C/Canonicalize/LocalEnvironment.elm:539-541 |
| Constructor typing: a constructor's type is a curried function of its argument types returning the type applied to its parameters, generalised over the type's variables. | C/Canonicalize/Expression.elm:1690-1700; C/Canonicalize/Environment.elm:223-232 |
| A local type named like an imported one (`type Maybe a = ...`) is a different type; the bare name means the local one. | CE/TypeMismatchLocalTypeNamedLikeAnImportedOneTest.elm |
| Constructor limits (eco): at most 2040 fields per constructor; a nullary constructor must be among the first 1024 constructors of its type. | C/IR/Runtime/HeapLimits.elm:39-61; C/Canonicalize/LocalEnvironment.elm:671-679 |

Opaque types and visibility (interface): a custom type is _open_ (`T(..)`), _closed_ (`T`) or
_private_ (not exposed); an alias is public or private. Importers see an open type with its
constructors, a closed type with no constructors, nothing of a private type
(C/IR/Canonical/Interface.elm:15-30, :135-150, :298-321). `exposing (..)` makes every type open
and every alias public (C/IR/Canonical/Interface.elm:22-23, :240-244). `Alias(..)` in an export or
import is an error (`ExportOpenAlias` / `ImportOpenAlias`) (C/Canonicalize/Module.elm:511-519;
C/Canonicalize/Environment/Foreign.elm:410-430). Importing a constructor by bare name
(`exposing (Just)`) is `ImportCtorByName` (C/Canonicalize/Environment/Foreign.elm:396-406, :447-470).

## Patterns, Exhaustiveness, Redundancy

### Typing of patterns

| Pattern | Type / binding | Cite |
|---|---|---|
| `_` | any | C/Type/Constrain/Typed/Pattern.elm:150 |
| `x` | any; binds `x` (monomorphic, except in a destructuring `let`) | C/Type/Constrain/Typed/Pattern.elm:153 |
| `p as x` | type of `p`; binds `x` | C/Type/Constrain/Typed/Pattern.elm:156 |
| `()` | unit | C/Type/Constrain/Typed/Pattern.elm:159 |
| tuple | 2- or 3-tuple of component types | C/Type/Constrain/Typed/Pattern.elm:170 |
| constructor `C p1 .. pn` | the type of `C` instantiated; arity must match exactly (`BadArity` pattern context, `TOO FEW/MANY ARGS`) | C/Type/Constrain/Typed/Pattern.elm:173; C/Canonicalize/Pattern.elm:273-297 |
| `[p1, .., pn]`, `p :: ps` | `List t` | C/Type/Constrain/Typed/Pattern.elm:180-207 |
| record `{ f1, .. }` | open record with those fields | C/Type/Constrain/Typed/Pattern.elm:208-241 |
| integer literal | `Int` (not `number`) | C/Type/Constrain/Typed/Pattern.elm:243-252 |
| string literal | `String` | C/Type/Constrain/Typed/Pattern.elm:254-263 |
| char literal | `Char` | C/Type/Constrain/Typed/Pattern.elm:265-274 |
| `True`/`False` of `Basics.Bool` | `Bool` (other types' `True`/`False` constructors are ordinary) | C/Canonicalize/Pattern.elm:15-17; C/Type/Constrain/Typed/Pattern.elm:276-285 |

Float literals are not patterns (parse error; CE/UnexpectedPatternFloatWithExponentTest.elm).

### Exhaustiveness and redundancy

| Rule | Cite |
|---|---|
| Checked matches: each function and lambda parameter (one-row match, context `BadArg`), each `let` destructuring (`BadDestruct`), each `case` (`BadCase`). | C/Nitpick/PatternMatches.elm:12-15, :360-385, :436, :451-455, :511-560 |
| Method: Maranget, "Warnings for Pattern Matching"; unit, tuples, lists, `Bool` become constructors of built-in unions; variables, wildcards and record patterns become `Anything`. | C/Nitpick/PatternMatches.elm:17-29, :75-118 |
| A row is redundant if not useful against the earlier rows. The first redundant row of a match is the only error reported for it (`REDUNDANT PATTERN`), and the match is then not checked for exhaustiveness. | C/Nitpick/PatternMatches.elm:31-35, :539-560, :654-672; C/Nitpick/Error.elm:37-48 |
| Non-exhaustive: `case` gives `MISSING PATTERNS`; argument or destructuring gives `UNSAFE PATTERN`, with example missing patterns. | C/Nitpick/Error.elm:37-41, :62-93; C/Nitpick/PatternMatches.elm:290-305 |
| Literals (`Int`, `Char`, `String`) never cover their type: exhaustive only with a wildcard or variable. | C/Nitpick/PatternMatches.elm:37-38, :94-100, :333-334 |
| Literals are compared as written: `Chr` and `Str` by their escaped source text, `Int` by value. | C/Nitpick/PatternMatches.elm:94-100; C/Parse/String.elm:13-18 |
| The check runs on the type-checked module and relies on it (a mixed literal/constructor column would crash). | C/Nitpick/PatternMatches.elm:39-41 |
| There is no guard syntax; non-exhaustiveness is always an error, never a warning. | C/Compile.elm:30-32 |

Evidence: CE/MissingPatternsAMissingListLengthTest.elm, CE/MissingPatternsAMissingTupleShapeTest.elm,
CE/RedundantPatternABranchAfterAWildcardTest.elm, CE/UnsafePattern*.elm (4 files),
CT/SourceIR/PatternFailsCases.elm:106-530.

## Equality and Comparison

| Rule | Cite |
|---|---|
| `(==)`, `(/=)` have type `a -> a -> Bool` with no class constraint: equality is statically allowed at every type, including functions, `Json.Encode.Value` and `Regex`. Only the two sides must have one type. | core/Basics.elm:325-350; CE/TypeMismatchFloatComparedForEqualityTest.elm |
| Elm documents that `==` on functions and JSON values "will crash if possible" at run time; eco instead returns `False` for distinct closures (runtime divergence, the type checker does not reject it). | core/Basics.elm:332-345; DD/elm-divergence.md:181-189 |
| `(<)`, `(>)`, `(<=)`, `(>=)`, `max`, `min`, `compare` require `comparable` (table above); `Bool`, unit, records, functions and custom types are rejected. | core/Basics.elm:367-418; CE/TypeMismatchBoolsComparedTest.elm, CE/TypeMismatchFunctionLeftOfGreaterThanTest.elm, CE/TypeMismatchRecordLeftOfAtMostTest.elm, CE/TypeMismatchUnitLeftOfAtLeastTest.elm |
| Tuples of comparables are comparable, of 2 or 3 components. | C/Type/Unify.elm:783-797; CE/TypeMismatchComparableAgainstATupleTest.elm |

## Modules

### Header and effects kind

| Rule | Cite |
|---|---|
| Header forms: `module M exposing (...)`, `port module M exposing (...)`, `effect module M where { command = X, subscription = Y } exposing (...)`; a file with no header is accepted. | C/Parse/Module.elm:12-17 |
| Plain `module` may not declare ports (`UNEXPECTED PORTS`; in a package `PACKAGES CANNOT HAVE PORTS`). | C/Parse/Module.elm:24, :345-360; C/Parse/Error.elm:1032-1057, :1077-1086 |
| `port module` is refused in a package; elsewhere it must declare at least one port (`NO PORTS`). | C/Parse/Module.elm:25-26, :362-381; C/Parse/Error.elm:1059-1076, :1087-1108 |
| `effect module` only in a kernel project (author `elm`, `elm-explorations` or `eco`) and may not declare ports (`INVALID EFFECT MODULE`). | C/Parse/Module.elm:27-28, :383-392; C/Elm/Package.elm:155-160; C/Parse/Error.elm:1109-1124 |
| A file with no header is not checked: its ports, if any, become its effects. | C/Parse/Module.elm:29, :320-333 |
| Module name must match the file (`MODULE NAME MISMATCH`), and an imported module must have a header. | C/Parse/Error.elm:989-1031; CE/ErrorMessagesIssue103ImportedModuleWithoutModuleLineTest.elm |

### Exposing lists (exports)

| Item | Meaning | Error | Cite |
|---|---|---|---|
| `(..)` | everything: all values, all types open, all aliases public, all operators | | C/Canonicalize/Module.elm:443-446; C/IR/Canonical/Interface.elm:22-23 |
| `x` | a top-level value or a port | `ExportNotFound` (`UNKNOWN EXPORT`) | C/Canonicalize/Module.elm:492-502 |
| `(op)` | an operator declared `infix` in the module | `ExportNotFound` | C/Canonicalize/Module.elm:504-509 |
| `T(..)` | custom type with constructors | `ExportOpenAlias` (`BAD EXPORT`) if `T` is an alias | C/Canonicalize/Module.elm:511-519 |
| `T` | custom type without constructors (opaque), or alias | `ExportNotFound` | C/Canonicalize/Module.elm:521-529 |
| any item twice | | `ExportDuplicate` (`REDUNDANT EXPORT`) | C/Canonicalize/Module.elm:454-458 |

Interface contents: the module's package; the annotation of each exposed value (inferred if
unannotated); each exposed operator with its function's annotation, associativity and precedence;
every custom type and alias the module declares, each tagged with visibility
(C/IR/Canonical/Interface.elm:12-30, :111-121, :190-262). Values are cut to the exposing list;
types are not cut, only tagged (C/IR/Canonical/Interface.elm:17-19). No check forbids an exposed
value whose type mentions a private type (no such error exists in C/Canonicalize/Error.elm:161-198).

### Imports

| Rule | Cite |
|---|---|
| `import M` makes every public value, type and constructor of `M` available qualified as `M.x`. `import M as A` uses `A` as the prefix instead (and `M.x` is then not available through this import). | C/Canonicalize/Environment/Foreign.elm:7-11, :164-176 |
| `exposing (..)` adds every public name unqualified, operators included, merging (possibly into ambiguity). | C/Canonicalize/Environment/Foreign.elm:217-232 |
| Explicit `exposing`: a lower-case value merges with earlier entries; a type name or operator _replaces_ any earlier entry of that name; `T(..)` adds the constructors, merging. | C/Canonicalize/Environment/Foreign.elm:15-19, :346-445 |
| Exposing a name `M` does not expose is `ImportExposingNotFound` (`BAD IMPORT`); unknown module is `MODULE NOT FOUND`; a module name provided twice is `AMBIGUOUS IMPORT`. | C/Canonicalize/Environment/Foreign.elm:372-374, :406-443; C/Canonicalize/ImportError.elm:6-22, :132-235 |
| Several imports may share a prefix; their names merge under it. | C/Canonicalize/Environment.elm:120-124; C/Canonicalize/Environment/Foreign.elm:250-254 |
| Import cycles between modules are rejected by the build (`IMPORT CYCLE`). | B/Reporting/Exit.elm:2536-2545 |
| Unused imports are not an error (no such error exists). | C/Canonicalize/Error.elm:161-198 |

Default imports, added to every module outside the `elm/core` package (C/Parse/DefaultImports.elm:9-29, :47-60):

```
import Basics exposing (..)
import Debug
import List exposing ((::))
import Maybe exposing (Maybe(..))
import Result exposing (Result(..))
import String exposing (String)
import Char exposing (Char)
import Tuple
import Platform exposing (Program)
import Platform.Cmd as Cmd exposing (Cmd)
import Platform.Sub as Sub exposing (Sub)
```

`List` the type is not exposed by these; it is in scope from the initial environment
(C/Parse/DefaultImports.elm:27-29).

### Module-level static checks summary

Canonicalisation order: imports, then local types, values, constructors, then top-level values,
effects, exports (C/Canonicalize/Module.elm:10-15, :113-139). Effect modules: must define
`init`, `onEffects`, `onSelfMsg`, plus `cmdMap` and/or `subMap`; each effect type must be a local
custom type (`EFFECT PROBLEM`) (C/Canonicalize/Effects.elm:16-20, :84-124, :217-251). Effect modules
are noted only; they are kernel-only.

## Ports (Static)

### Shapes

All aliases are expanded before the shape is read (`deepDealias`, `delambda`) (C/Canonicalize/Effects.elm:134-146).

| Shape | Accepted form | Rejections | Cite |
|---|---|---|---|
| Outgoing | `payload -> Cmd msg`, `msg` a type variable, exactly one argument | `CmdNoArg` ("cannot be just a command"; use `() -> Cmd msg`), `CmdExtraArgs n`, `CmdBadMsg` (Cmd argument not a variable) | C/Canonicalize/Effects.elm:147-174; C/Canonicalize/Error.elm:903-930 |
| Incoming | `(payload -> msg) -> Sub msg`, the same variable `msg` in both places | `SubBad` | C/Canonicalize/Effects.elm:176-203; C/Canonicalize/Error.elm:932-945 |
| Other | anything not ending in `Cmd x` / `Sub x` | `NotCmdOrSub` | C/Canonicalize/Effects.elm:205-209 |

Shape errors are reported as `BAD PORT` (C/Canonicalize/Error.elm:887-891). Port annotations are
mandatory (a port declaration is `port name : type`). The port's annotation variables become rigid
variables of a `CLet` wrapping all declarations; incoming and outgoing are typed alike
(C/Type/Constrain/Typed/Module.elm:19-20, :197-240).

### Payload types (`checkPayload`)

C/Canonicalize/Effects.elm:258-346; error reasons C/Canonicalize/Error.elm:255-259, :830-885.

| Type | Allowed? | Cite |
|---|---|---|
| `Int`, `Float`, `Bool`, `String` | yes | C/Canonicalize/Effects.elm:283-293 |
| `Json.Encode.Value` | yes | C/Canonicalize/Effects.elm:280-281, :378-383 |
| `Bytes.Bytes` | yes in eco (eco extension; Elm 0.19.1 rejects); native target only as the whole payload | C/Canonicalize/Effects.elm:295-296; C/LocalOpt/Typed/Module.elm:167-200; T/eco-divergence/src/PortBytesEchoTest.elm:3-6 |
| `()` | yes | C/Canonicalize/Effects.elm:317-318; T/elm/src/CovPortIncomingUnitTest.elm:31 |
| `List t`, `Maybe t`, `Array t` | iff `t` allowed | C/Canonicalize/Effects.elm:301-312 |
| 2- and 3-tuples | iff every component allowed | C/Canonicalize/Effects.elm:320-330 |
| closed records | iff every field allowed (checked in field-name order) | C/Canonicalize/Effects.elm:341-346 |
| aliases | expanded, then checked | C/Canonicalize/Effects.elm:274-275 |
| `Char` | no (`UnsupportedType`) | C/Canonicalize/Effects.elm:263; CE/PortProblemCharPayloadTest.elm |
| type variables | no (`TypeVariable`) | C/Canonicalize/Effects.elm:332-333 |
| functions | no (`Function`) | C/Canonicalize/Effects.elm:335-336 |
| extensible records | no (`ExtendedRecord`) | C/Canonicalize/Effects.elm:338-339 |
| `Dict`, `Set`, `Result`, any custom type, any other named type | no (`UnsupportedType`) | C/Canonicalize/Effects.elm:298-315 |

Payload errors are reported as `PORT ERROR`, naming the first offending part (C/Canonicalize/Effects.elm:266-268;
C/Canonicalize/Error.elm:830-834). The `PORT ERROR` message lists "Ints, Floats, Bools, Strings,
Maybes, Lists, Arrays, tuples, records, JSON values, and Bytes" (C/Canonicalize/Error.elm:876-880).

Other port facts: ports are top-level values for scoping and duplicates (C/Canonicalize/LocalEnvironment.elm:149-161);
they may be exported by name (C/Canonicalize/Module.elm:497-502); packages may not have ports
(C/Parse/Module.elm:345-366); there is no static error for an unused port (no such constructor in
C/Canonicalize/Error.elm:161-198 or C/Parse/Error.elm:175-183).

## Main

| Rule | Cite |
|---|---|
| Checked in the optimiser, for any module that defines a top-level `main`, exposed or not. | C/LocalOpt/Erased/Module.elm:392-404; C/LocalOpt/Typed/Module.elm:140-146 |
| Annotation optional; the checked type is the inferred or annotated scheme, deep-dealiased. | C/LocalOpt/Erased/Module.elm:404-415 |
| Allowed: `VirtualDom.Node msg` (so `Html msg`, `Svg msg`), static. | C/LocalOpt/Erased/Module.elm:416-421; C/LocalOpt/Error.elm:104-113 |
| Allowed: `Platform.Program flags model msg` where `flags` passes `checkPayload` (same table as ports, including `Bytes` on the JS target). | C/LocalOpt/Erased/Module.elm:433-441 |
| eco extension: `Program System.Environment model msg` (eco/system), flags not checked. | C/LocalOpt/Erased/Module.elm:423-431; C/IR/Runtime/EcoEnvironment.elm:6-18 |
| Any other type is `BadType` (`BAD MAIN TYPE`); bad flags `BadFlags` (`BAD FLAGS`); `main` in a recursive group `BadCycle` (`BAD MAIN`). Native only: `Bytes` anywhere in flags is `NativeBytesInFlags`. | C/LocalOpt/Error.elm:60-86, :104-180 |
| A `main` is required only by the build when producing HTML or JS output (`NO MAIN`). | B/Reporting/Exit.elm:2219-2280 |

Evidence: CE/BadMainType{Alias,Function,Record,ThreeArgumentType,TypeVariable,Unit}MainTest.elm,
CE/BadMainRecursiveMainTest.elm, CE/BadMainRecursiveUnannotatedMainTest.elm,
T/eco-divergence/src/FlagsBytesNativeTest.elm, T/elm/src/EntryMainOfRootModuleTest.elm.

## Static Errors Index

Titles are the report titles a user sees.

| Error (constructor) | Title | Condition | Cite |
|---|---|---|---|
| AnnotationTooShort | BAD TYPE ANNOTATION | more parameters than annotation arrows | C/Canonicalize/Error.elm:352-362 |
| AmbiguousVar/Type/Variant/Binop | AMBIGUOUS NAME | name used that several imports provide | C/Canonicalize/Error.elm:163-166, :387-397, :1497 |
| BadArity (type / pattern) | TOO FEW ARGS / TOO MANY ARGS | wrong argument count for a type or a constructor pattern | C/Canonicalize/Error.elm:399-431 |
| Binop | INFIX PROBLEM | equal-precedence operators that cannot group | C/Canonicalize/Error.elm:453-454 |
| DuplicateDecl/Type/Ctor/Field/AliasArg/UnionArg/Pattern | NAME CLASH | duplicates (see table) | C/Canonicalize/Error.elm:464-504, :1406 |
| EffectNotFound / EffectFunctionNotFound | EFFECT PROBLEM | effect manager incomplete | C/Canonicalize/Error.elm:522-534 |
| ExportDuplicate | REDUNDANT EXPORT | item exposed twice | C/Canonicalize/Error.elm:544-550 |
| ExportNotFound | UNKNOWN EXPORT | exposed name not defined | C/Canonicalize/Error.elm:562-568 |
| ExportOpenAlias | BAD EXPORT | `Alias(..)` exported | C/Canonicalize/Error.elm:611-612 |
| ImportCtorByName / ImportOpenAlias / ImportExposingNotFound | BAD IMPORT | bad exposing item in import | C/Canonicalize/Error.elm:625-678 |
| NotFoundVar/Type/Variant | NAMING ERROR | name not in scope | C/Canonicalize/Error.elm:709-715, :1545 |
| NotFoundBinop | UNKNOWN OPERATOR | operator not in scope | C/Canonicalize/Error.elm:718-787 |
| PatternHasRecordCtor | BAD PATTERN | record-alias constructor in a pattern | C/Canonicalize/Error.elm:816-817 |
| PortPayloadInvalid | PORT ERROR | payload type not allowed | C/Canonicalize/Error.elm:830-834 |
| PortTypeInvalid | BAD PORT | wrong port shape | C/Canonicalize/Error.elm:887-891 |
| RecursiveAlias | ALIAS PROBLEM | alias cycle | C/Canonicalize/Error.elm:955-956, :1593-1606 |
| RecursiveDecl | CYCLIC DEFINITION | top-level value cycle through direct uses | C/Canonicalize/Error.elm:958-1002 |
| RecursiveLet | CYCLIC VALUE | `let` cycle with a parameterless member or a destructuring | C/Canonicalize/Error.elm:1004-1050 |
| Shadowing | SHADOWING | local rebinds a local or top-level name | C/Canonicalize/Error.elm:1052-1061 |
| TooLarge (eco only) | TOO MANY PARAMETERS / CAPTURED VARIABLES / FIELDS / CONSTRUCTORS | heap limits (2047 params, 2047 record fields, 2040 ctor fields, 1024 nullary ctors) | C/Canonicalize/Error.elm:1073-1130; C/IR/Runtime/HeapLimits.elm:30-61 |
| TupleLargerThanThree | BAD TUPLE | 4+ components | C/Canonicalize/Error.elm:1137-1138 |
| TypeVarsUnboundInUnion | UNBOUND TYPE VARIABLE(S) | constructor uses undeclared variable | C/Canonicalize/Error.elm:1149-1150, :1345-1362 |
| TypeVarsMessedUpInAlias | UNUSED TYPE VARIABLE(S) / UNBOUND TYPE VARIABLE(S) / TYPE VARIABLE PROBLEMS | alias parameters differ from body variables | C/Canonicalize/Error.elm:1152-1304 |
| BadExpr / BadPattern (type) | TYPE MISMATCH | unification failure for an expression or pattern | C/Type/Error.elm:114-116, :367, :1197-1271 |
| BadExpr with CallArity | TOO MANY ARGS | function applied to more arguments than its type allows | C/Type/Error.elm:1391-1436 |
| InfiniteType | INFINITE TYPE | occurs check on a let-bound name | C/Type/Error.elm:117, :2840 |
| Redundant | REDUNDANT PATTERN | branch not useful | C/Nitpick/Error.elm:48 |
| Incomplete (case / arg, destruct) | MISSING PATTERNS / UNSAFE PATTERN | non-exhaustive | C/Nitpick/Error.elm:62-93 |
| BadType / BadCycle / BadFlags | BAD MAIN TYPE / BAD MAIN / BAD FLAGS | `main` checks | C/LocalOpt/Error.elm:104-125 |
| NativeBytesInPort / NativeBytesInFlags (eco native) | PORT ERROR / BAD FLAGS | `Bytes` nested in a port payload, or in flags | C/LocalOpt/Error.elm:157-175 |
| UnexpectedPort / NoPorts / NoPortsInPackage / NoPortModulesInPackage / NoEffectsOutsideKernel | UNEXPECTED PORTS / NO PORTS / PACKAGES CANNOT HAVE PORTS / INVALID EFFECT MODULE | header vs. ports | C/Parse/Error.elm:1032-1124 |
| import errors | MODULE NOT FOUND / AMBIGUOUS IMPORT | import names no module / several | C/Canonicalize/ImportError.elm:132-235 |
| build | IMPORT CYCLE / NO MAIN / DEBUG REMNANTS | module cycle; output needs `main`; `Debug` with `--optimize` | B/Reporting/Exit.elm:2219, :2537, :2735-2740; B/Generate.elm:283-294 |
| native monomorphisation (eco only) | MONOMORPHIZATION ERROR / STAGE ARITY LIMIT | polymorphic recursion, shaders, closures over 2047 slots after specialisation | DD/elm-divergence.md:220-260 |

## Evidence

| Rule pinned | Test | Kind |
|---|---|---|
| Shadowing of top-level and in lambdas | CE/ShadowingAnArgumentShadowingATopLevelValueTest.elm, CE/ShadowingShadowingInLambdaTest.elm | reject |
| Duplicates | CE/NameClashARecordFieldGivenTwiceTest.elm, CE/NameClashTwoArgumentsOfOneNameTest.elm, CE/NameClashTwoLetBindingsOfOneNameTest.elm; CT/SourceIR/CanonicalizeFailsCases.elm:108-188 | reject |
| Cyclic values | CE/CyclicDefinitionATopLevelValueDefinedByItselfTest.elm, CE/CyclicValueALetValueDefinedByItselfTest.elm; CT/SourceIR/CanonicalizeFailsCases.elm:313-323 | reject |
| Recursive alias | CE/AliasProblemRecursiveAliasWithCommentedParensTest.elm, CE/AliasProblemQualifiedTypeTest.elm, CE/AliasProblemExtensibleRecordUnitTupleAndFunctionTest.elm | reject |
| Arity | CE/ErrorMessagesIssue203ListWithoutArgumentTest.elm, CE/TooFewArgsAConstructorPatternWithTooFewArgumentsTest.elm, CE/TooManyArgs*Test.elm (8) | reject |
| Constrained variables | CE/TypeMismatch{NumberPlusAppendable,NumberAndCompappendListEntries,CompappendAgainstATuple,AppendableAgainstATuple,ComparableAgainstATuple,TwoComparableVars,DifferentlyNamedComparableVars}Test.elm | reject |
| Rigid variables | CE/TypeMismatchRigid*Test.elm (about 25 files) | reject |
| Inferred `compappend` | T/elm/src/FunctionUnannotatedCompappendTest.elm | accept |
| No value restriction | T/elm/src/LetNumberDualUseTest.elm and T/elm/src/LetNumber*Test.elm | accept |
| Record update cannot change field type or add fields | CE/TypeMismatchUpdateValueTest.elm, CE/TypeMismatchUpdateOfAnEmptyRecordTest.elm | reject |
| Records not comparable | T/elm/src/CompareRecordWithEmptyListFieldTest.elm:3-6; CE/TypeMismatchRecordLeftOfAtMostTest.elm | both |
| Bool/functions not comparable | CE/TypeMismatchBoolsComparedTest.elm, CE/TypeMismatchFunctionLeftOfGreaterThanTest.elm | reject |
| Port payloads | CE/PortProblemCharPayloadTest.elm; T/elm/src/PortEcho*Test.elm, PortAliasEchoTest.elm, CovPortIncoming{Array,JSONValue,Triple,Unit}Test.elm | both |
| Bytes ports (eco) | T/eco-divergence/src/PortBytesEchoTest.elm, PortBytesNestedNativeTest.elm, FlagsBytesNativeTest.elm | both |
| `main` types | CE/BadMainType*Test.elm (6), CT/SourceIR/MainFailsCases.elm:103-111 | reject |
| Patterns | CE/MissingPatterns*, CE/RedundantPatternABranchAfterAWildcardTest.elm, CE/UnsafePattern* | reject |
| Unannotated recursive group (eco rejects, Elm accepts) | T/eco-divergence/src/TypeMismatchResultUsedAtTwoTypesTest.elm; CT/SourceIR/TypeCheckFailsCases.elm:1327 | reject |
| Local type hides imported | CE/TypeMismatchLocalTypeNamedLikeAnImportedOneTest.elm | reject |
| Entry point is the root module's `main` | T/elm/src/EntryMainOfRootModuleTest.elm | accept |

## Candidate Ambiguities

### C-STA-1: Bytes as a port payload and in flags
- Construct: `port p : Bytes -> Cmd msg`; `main : Program { b : Bytes } m msg`.
- Question: Is `Bytes.Bytes` a legal payload/flags type?
- Implementation: eco accepts `Bytes` in any payload position (C/Canonicalize/Effects.elm:260-263, :295-296); the native target accepts it only as the whole port payload and never in flags (C/LocalOpt/Error.elm:73-79; C/LocalOpt/Typed/Module.elm:167-200).
- Notes or Elm reference behaviour: tests state stock Elm rejects any `Bytes` port payload (T/eco-divergence/src/PortBytesEchoTest.elm:3-4; T/eco-divergence/src/FlagsBytesNativeTest.elm:7). This is not listed in DD/elm-divergence.md section 4.4.
- Options: (a) define Elm 0.19.1's set and treat Bytes as an eco extension; (b) include Bytes; (c) parameterise by target.
- Affects: static

### C-STA-2: Constrained variables named by prefix
- Construct: `f : numberOfItems -> numberOfItems`.
- Question: Is any variable whose name starts with `number`/`comparable`/`appendable`/`compappend` constrained, or only those names followed by digits?
- Implementation: prefix test (C/Core/Name.elm:196-223; C/Type/Type.elm:439-452).
- Notes or Elm reference behaviour: silent in the guide; Elm 0.19.1 believed identical (Guida port, DD/theory/compiler/front-end.md:7).
- Options: (a) prefix rule; (b) exact name plus optional digits.
- Affects: static

### C-STA-3: Rigid variable escaping its annotation
- Construct: `f x = let g : a -> a; g y = x in g x` (inner annotation variable unified with an outer flexible variable).
- Question: Is this a type error?
- Implementation: unifying a rigid with an outer-rank flexible variable succeeds and lowers the rank (C/Type/Unify.elm:535-570, :575-582); the rigid is then not generalised and the solver crashes with "You ran into a compiler bug" (C/Type/Solve.elm:30-31, :439-440, :459-483).
- Notes or Elm reference behaviour: silent; Elm 0.19.1 has the same check and is believed to crash the same way (unverified).
- Options: (a) specify as a type error (rigid variable escapes); (b) leave as an implementation fault.
- Affects: static

### C-STA-4: Scoped type variables in nested annotations
- Construct: outer `f : a -> List a`, inner `let g : a -> List a`.
- Question: Does the inner `a` denote the outer `a`?
- Implementation: yes; only names not already in scope become new rigid variables (C/Type/Constrain/Typed/Expression.elm:128-143).
- Notes or Elm reference behaviour: silent in Elm docs.
- Options: (a) lexically scoped annotation variables; (b) each annotation closed.
- Affects: static

### C-STA-5: Occurs check only at let-bound names
- Construct: an expression whose type becomes cyclic without being reachable from any let-bound name.
- Question: When must an infinite type be rejected?
- Implementation: unification has no occurs check; the check runs on the types of the names each `let` binds after its body (C/Type/Solve.elm:33-34, :375-379, :452-454; C/Type/Occurs.elm:15-16).
- Notes or Elm reference behaviour: silent.
- Options: (a) HM occurs check on every unification; (b) the eco/Elm lazy check, defining which programs are rejected.
- Affects: static

### C-STA-6: Repeated field names through an extension variable
- Construct: `f : { r | x : Int } -> r -> Int` applied as `f { x = 1 } { x = "s" }`.
- Question: Can a row's extension be instantiated with a record that has a field of the same name (scoped labels)?
- Implementation: when gathering fields along an extension chain, the outermost occurrence wins (C/Type/Unify.elm:1207-1226), so the duplicate is silently shadowed rather than rejected; not tested.
- Notes or Elm reference behaviour: silent.
- Options: (a) rows have unique labels and the program is rejected; (b) scoped labels, outermost wins.
- Affects: static

### C-STA-7: Typing of unannotated mutually recursive groups
- Construct: `f b = g b` and `g b = ... f False ...` using `f`'s result at two types.
- Question: Are unannotated members monomorphic within their group?
- Implementation: yes (shared variables, C/Type/Constrain/Typed/Expression.elm:184-197).
- Notes or Elm reference behaviour: Elm 0.19.1 generalises earlier members inside later ones and accepts some ill-typed groups that crash at run time (DD/elm-divergence.md:262-293); Elm also miscomputes interface annotations for later members (DD/elm-divergence.md:295-312).
- Options: (a) standard HM (eco); (b) Elm 0.19.1 behaviour (unsound).
- Affects: static

### C-STA-8: Top-level value forced through a delayed self-reference
- Construct: `x = let f _ = x in f ()`.
- Question: Is this rejected statically?
- Implementation: accepted, since the use of `x` is inside a `let` function body and so delayed (C/Canonicalize/Expression.elm:16-20; C/Canonicalize/Module.elm:400-411); evaluation then needs `x` while initialising `x`.
- Notes or Elm reference behaviour: silent; same rule believed in Elm 0.19.1.
- Options: (a) syntactic direct/delayed rule as implemented; (b) a semantic rule; (c) leave run-time behaviour to the dynamic semantics.
- Affects: static

### C-STA-9: Asymmetry between let and top-level recursion
- Construct: `let f = \n -> f n in f 1` versus top-level `f = \n -> f n`.
- Question: Why is the first rejected and the second accepted?
- Implementation: `let` cycles require every member to have parameters (C/Canonicalize/Expression.elm:1362-1394); top level only rejects cycles through direct uses (C/Canonicalize/Module.elm:400-423).
- Notes or Elm reference behaviour: silent.
- Options: (a) record both rules as implemented; (b) unify them.
- Affects: static

### C-STA-10: Unresolved `number`
- Construct: `main = text (Debug.toString (2 ^ 62 * 4))` with no constraint fixing `number`.
- Question: What type does an unconstrained `number` have at run time?
- Implementation: the checker leaves `number`; the native back end closes it to `Int` (DD/theory/compiler/front-end.md:54; DD/monomorphization/solver-reuse-evaluation.md:41).
- Notes or Elm reference behaviour: Elm's JS is untyped (numbers are doubles); silent in docs.
- Options: (a) default to Int; (b) default to Float; (c) leave polymorphic and let the dynamic semantics be representation-independent where possible.
- Affects: static

### C-STA-11: Explicitly exposed type names replace rather than conflict
- Construct: `import Foo exposing (Maybe)` where `Foo` defines `Maybe`.
- Question: Is the bare `Maybe` ambiguous with the default import?
- Implementation: an explicitly listed type name or operator replaces the earlier entry; values and `(..)` merge into ambiguity (C/Canonicalize/Environment/Foreign.elm:15-19, :378-445).
- Notes or Elm reference behaviour: silent.
- Options: (a) replacement for explicitly listed types and operators; (b) ambiguity for all kinds.
- Affects: static

### C-STA-12: Private types in exposed signatures
- Construct: `module M exposing (f)` with `type Hidden = H` and `f : Hidden -> Int`.
- Question: Is exposing `f` legal?
- Implementation: no check exists (C/Canonicalize/Module.elm:430-530; C/Canonicalize/Error.elm:161-198); the interface keeps the private type's declaration (C/IR/Canonical/Interface.elm:17-19).
- Notes or Elm reference behaviour: silent.
- Options: (a) legal; (b) error.
- Affects: static

### C-STA-13: Module without a header
- Construct: a file with no `module` line that declares ports.
- Question: Is a headerless module allowed to declare ports, and what is its name and export list?
- Implementation: accepted without checks; its ports become its effects (C/Parse/Module.elm:29).
- Notes or Elm reference behaviour: silent; an imported module must have a header (CE/ErrorMessagesIssue103ImportedModuleWithoutModuleLineTest.elm).
- Options: (a) record as implemented; (b) require `port module`.
- Affects: static

### C-STA-14: Literal identity in redundancy checking
- Construct: `case c of 'A' -> 1; '\u{0041}' -> 2; _ -> 3`.
- Question: Is the second branch redundant?
- Implementation: char and string literals are compared by escaped source text, so it is not reported (C/Nitpick/PatternMatches.elm:94-100; C/Parse/String.elm:13-18). Int literals compare by value.
- Notes or Elm reference behaviour: silent.
- Options: (a) compare denoted values; (b) as implemented.
- Affects: static

### C-STA-15: Where `main` is checked and required
- Construct: a non-root module defining a `main` of an unsupported type.
- Question: Is `main` checked in every module or only in the entry module, and is it required?
- Implementation: checked in every module that defines it (C/LocalOpt/Erased/Module.elm:392-404); required only for HTML/JS output (B/Reporting/Exit.elm:2219-2280); the entry point is the root's `main` (T/elm/src/EntryMainOfRootModuleTest.elm).
- Notes or Elm reference behaviour: DD/elm-divergence.md:206-208 says Elm's optimiser also reports `BAD MAIN`.
- Options: (a) per-module rule; (b) program-level rule.
- Affects: static

### C-STA-16: eco System.Environment flags
- Construct: `main : Program System.Environment model msg`.
- Question: Part of the language definition?
- Implementation: eco extension, recognised by alias name before dealiasing, flags check skipped (C/IR/Runtime/EcoEnvironment.elm:6-18, :47-56; C/LocalOpt/Erased/Module.elm:423-431).
- Notes or Elm reference behaviour: not in Elm.
- Options: (a) exclude from Standard Elm; (b) appendix.
- Affects: static

### C-STA-17: Implementation size limits
- Construct: functions over 2047 parameters, records over 2047 fields, constructors over 2040 fields, over 1024 nullary constructors.
- Question: Are limits part of the definition?
- Implementation: rejected in canonicalisation on every target (C/Canonicalize/Error.elm:1073-1130; C/IR/Runtime/HeapLimits.elm:30-61).
- Notes or Elm reference behaviour: Elm has no such limits (DD/elm-divergence.md:214-218).
- Options: (a) implementation-defined limits clause; (b) omit.
- Affects: static

### C-STA-18: Equality at every type
- Construct: `(\x -> x) == (\x -> x)`, `==` on `Json.Encode.Value` or `Regex`.
- Question: Should the static semantics restrict `==`?
- Implementation: `eq : a -> a -> Bool`, no restriction (core/Basics.elm:348); eco's run-time result differs from Elm's crash (DD/elm-divergence.md:181-189, :362-375).
- Notes or Elm reference behaviour: core/Basics.elm:340-344 says a future compiler will detect it.
- Options: (a) unrestricted, dynamic semantics decides; (b) an equality class excluding functions.
- Affects: static

### C-STA-19: Constrained name as a record extension variable
- Construct: `f : { number | x : Int } -> Int`.
- Question: Is a constrained variable legal as a row extension?
- Implementation: the name makes it a rigid `number`, which can unify with no record structure (C/Type/Type.elm:432-437; C/Type/Unify.elm:575-610), so any use fails with `TYPE MISMATCH`; the declaration itself is accepted.
- Notes or Elm reference behaviour: silent.
- Options: (a) reject the annotation; (b) accept, uninhabited.
- Affects: static

### C-STA-20: Kernel-package privileges
- Construct: `Elm.Kernel.X.f`, `infix` declarations, `effect module`.
- Question: Which packages may use them?
- Implementation: authors `elm`, `elm-explorations` and `eco` (C/Elm/Package.elm:155-160); unannotated kernel references are unconstrained (C/Type/Constrain/Typed/Expression.elm:469-475).
- Notes or Elm reference behaviour: Elm 0.19.1 restricts these to its own core authors (eco adds `eco`).
- Options: (a) exclude kernel features from the definition and specify the basis by signature; (b) model them.
- Affects: static

### C-STA-21: Lazy ambiguity and qualified self-reference
- Construct: two imports exposing `x`, `x` unused; `M.x` inside module `M`.
- Question: Is an unused ambiguous name an error, and can a module qualify its own names?
- Implementation: ambiguity is an error only on use (C/Canonicalize/Environment.elm:21-25); qualified lookups see only imports, so `M.x` in `M` is `NAMING ERROR` (C/Canonicalize/Environment.elm:96-100; C/Canonicalize/Expression.elm:1643-1676).
- Notes or Elm reference behaviour: silent.
- Options: record as implemented.
- Affects: static

### C-STA-22: Native-only rejections
- Construct: polymorphic recursion through annotated functions; GLSL shaders; closures over 2047 slots after specialisation; `Bytes` nested in a port payload; `Debug` with `--optimize`.
- Question: Are these programs Standard Elm?
- Implementation: rejected only by the native back end, or (for `Debug`) accepted only by it (DD/elm-divergence.md:191-197, :220-260; C/LocalOpt/Error.elm:73-79).
- Notes or Elm reference behaviour: Elm compiles the first three; rejects `Debug` under `--optimize`.
- Options: (a) define the language independently of target and list these as implementation restrictions.
- Affects: static
