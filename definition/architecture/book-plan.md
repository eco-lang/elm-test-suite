# Book Plan: A Standard Definition of Elm?

Decisions at the two architecture checkpoints were made by the agent while
running the whole pipeline without stopping; they are marked **provisional**
where they go beyond the Author Directions (D1 to D11, `../survey/book-brief.md`)
and the rulings (A1 to A97, `../survey/ambiguity-log.md`).

## Grid

| Level | Syntax | Static Semantics | Dynamic Semantics |
|-------|--------|------------------|-------------------|
| Core | syntax-core | static-core | dynamic-core |
| Modules | syntax-modules | static-modules | dynamic-modules |
| Effects | (none: Cmd, Sub, Task are types of the basis) | (port admissibility is in static-modules) | effects |
| Programs | programs (all three phases) | | |

- **Core**: expressions, patterns, types, and `let` value definitions. Everything a single definition's right-hand side can contain.
- **Modules**: module headers, `exposing` lists, imports, and the top-level declarations a module may contain (value definitions, custom types, type aliases, ports). Elm modules are flat: a module exports top-level names only (D6), so this level has no signatures, functors or sharing.
- **Effects**: not a level of syntax but the semantic layer that gives Task, Cmd and Sub values and ports their meaning (D10, D11). It is purely dynamic: it defines task, command and subscription values, the JSON value model at the port boundary, and the encoding and decoding of port values.
- **Programs**: what a program is (a main module and the modules it imports), elaboration of the whole program including the type of `main`, and the execution of a program by the platform as a labelled transition system whose observable behaviour is its traffic on ports.

## Bare and Derived

The bare language is chosen so the rules are as few as possible (ECONOMICAL) while every derived form is a purely syntactic translation (definition-style B2). Rulings cited as A<n>.

### Bare Constructs

| Phrase Class | Construct | Notes |
|--------------|-----------|-------|
| AtExp | special constant `scon` | Int, Float, Char, String constants |
| AtExp | value or constructor identifier `longvar`, `longcon` | qualified or not |
| AtExp | operator value `(op)` | denotes the value the operator is bound to |
| AtExp | unit `()` | A1 |
| AtExp | tuple `( exp1 , exp2 ⟨, exp3⟩ )` | A12 |
| AtExp | empty list `[ ]` | |
| AtExp | record `{ ⟨exprow⟩ }` | |
| AtExp | record update `{ var | exprow }` | base is an unqualified variable |
| AtExp | `( exp )` | |
| AtExp | `let dec in exp` | dec is one dependency group |
| Exp | application `exp atexp` | |
| Exp | lambda `\ atpat -> exp` | one pattern |
| Exp | `case exp of match` | |
| ExpRow | `lab = exp ⟨, exprow⟩` | |
| Match | `mrule ⟨; match⟩` | the `;` is abstract: branches are separated by layout |
| MRule | `pat -> exp` | |
| Dec | `valbind` | one strongly connected group |
| ValBind | `var ⟨: ty⟩ = exp ⟨and valbind⟩` ; `atpat = exp` | `and` is abstract syntax for "and also, in the same group"; annotation carried with its binding |
| AtPat | `_`, `var`, `scon` (no Float), `longcon`, `()`, tuple, `[ ]`, record `{ ⟨patrow⟩ }`, `( pat )` | A7: no negative literals |
| Pat | `longcon atpat1 ... atpatn` (n >= 1), `pat :: pat`, `pat as var` | |
| PatRow | `lab ⟨, patrow⟩` | binds the variable spelt as the label |
| Ty | `tyvar`, `longtycon ty1 ... tyn` (n >= 0), `ty -> ty`, `{ ⟨tyrow⟩ }`, `{ tyvar | tyrow }`, `()`, 2- and 3-tuples, `( ty )` | |
| TyRow | `lab : ty ⟨, tyrow⟩` | |
| Module level | see syntax-modules: header, imports, exposing lists, `type` (custom type group), `type alias`, `port`, value group | |

### Derived Forms

| Phrase Class | Derived Form | Equivalent Form (sketch) | Fresh Names | Survey Ref |
|--------------|--------------|--------------------------|-------------|------------|
| Exp | `exp1 op exp2` (after fixity resolution) | `(op) exp1 exp2` | none | Phrase Classes: operator chain |
| Exp | `exp1 && exp2` | `if exp1 then exp2 else False` (A56) | none | A56 |
| Exp | `exp1 || exp2` | `if exp1 then True else exp2` (A56) | none | A56 |
| Exp | `-atexp` | `Basics.negate atexp` | none | Rewrites: negation |
| Exp | `if exp1 then exp2 else exp3` | `case exp1 of Basics.True -> exp2 ; Basics.False -> exp3` | none | Rewrites |
| Exp | `if e1 then e2 else if ... else en` | nested `if` | none | Rewrites: `else if` |
| AtExp | `[ exp1 , ... , expn ]` (n >= 1) | `exp1 :: [ exp2 , ... , expn ]`, ending in `[ ]` | none | |
| AtPat | `[ pat1 , ... , patn ]` (n >= 1) | `( pat1 :: [ pat2 , ... , patn ] )`, ending in `[ ]` | none | Patterns: list |
| AtExp | `.lab` | `( \ { lab } -> lab )` | none (the label is the bound variable) | |
| AtExp | `atexp.lab` | `( .lab atexp )` | none | |
| Exp | `\ atpat1 ... atpatn -> exp` (n >= 2) | `\ atpat1 -> \ atpat2 -> ... exp` | none | |
| ValBind | `var atpat1 ... atpatn = exp` (n >= 1) | `var = \ atpat1 ... atpatn -> exp` | none | |
| Dec | a `let` with several definitions | nested `let`s, one per strongly connected component of the "refers to" relation, in a dependency order; annotations travel with their definitions | none | Rewrites: `let` block |
| TopDec | the declarations of a module body | types gathered into one custom-type group; aliases in dependency order; value definitions as groups (strongly connected components) in dependency order | none | Rewrites: top-level values |

`True`, `False`, `negate` and `::` in equivalent forms always denote the initial basis's bindings (`Basics.True`, `Basics.False`, `Basics.negate`, `List.(::)`), whatever is in scope, as the exemplar's derived forms use `true`, `false` and `::`.

### Out of Scope

| Construct | Reason |
|-----------|--------|
| `infix` declarations, `effect module`, kernel references | Kernel-only (A11, A16, A37, A85); fixities of the basis operators are given as a table |
| GLSL shader blocks | Extension syntax outside Standard Elm |
| Library modules beyond the initial basis | Library, not language |
| eco extensions (System.Environment flags, size limits) | Appendix E (A13, A33, A34); Bytes payloads are in the language since A92 |

## Chapter Outline

### preface: Preface
- Kind: framing
- Level: none
- Defines: nothing formal; why a formal definition of Elm; the language's character (functional, pure, total, row-polymorphic records, managed effects); the method `B |- P => M`; relation to the Definition of Standard ML (D1, D7); note that rulings were taken where the implementations differ.
- Depends on: everything
- Rulings: D1 to D11
- Exemplar: "Structure and Method"

### introduction: Introduction
- Kind: framing
- Defines: phases (parsing, elaboration, evaluation), levels, the grid table, bare language and derived forms, the appendices, notational conventions; the no-runtime-errors stance (D2, D3) and what the definition leaves to the implementation (Appendix E).
- Depends on: plan
- Exemplar: "Structure and Method"

### syntax-core: Syntax of the Core (Chapter 2)
- Kind: syntax, Level: Core
- Defines: reserved words (the 14 of the survey, A2), special constants (Int decimal and hexadecimal, Float, Char with escapes, String single-line and `"""` multi-line; A8, A9, A15), comments (line, nested block, doc comments A10), identifiers (Var, Con, TyVar, TyCon, Lab, ModId, Op; long identifiers; A2), layout (the three column tests of the survey; A5, A6, A17), lexical analysis (maximal munch A3), infixed operators (resolution by the fixity table of the initial basis; non-associative mixes are errors; whitespace-sensitive negation), grammar figures for the bare Core (expressions, matches, declarations and bindings; patterns; types), syntactic restrictions (tuples are grammar A12, no shadowing, distinct bound names, distinct labels, record update target, constructor arity, recursion restrictions A26: let groups must be functions with parameters).
- Exemplar: "Syntax" rows

### syntax-modules: Syntax of Modules (Chapter 3)
- Kind: syntax, Level: Modules
- Defines: module identifiers; grammar: `module` and `port module` headers, `exposing` lists (`(..)`, values, operators, `T`, `T(..)`), imports (`as`, `exposing`), default imports (as a figure), top-level declarations (`type` custom type groups with `|` constructors, `type alias`, `port var : ty`, value groups); restrictions (ports only in `port module`, every module has a header (A16, A30 as amended), duplicate declarations, constructors unique per module, alias parameters equal the free variables of the body, custom type variables bound, no recursive aliases, `Alias(..)` not allowed, top-level recursion restriction A26, A25, port names unique per program A84 as a program-level restriction, constructor exposure rules).
- Exemplar: "Syntax" rows (module grammar)

### static-core: Static Semantics for the Core (Chapter 4)
- Kind: static, Level: Core
- Defines: simple objects (TyVar with class attribute, RowVar, TyName with arity, Lab, IdStatus {c, v}, Class); compound objects (Type, Row, RecType, FunType, ConsType, TypeFcn, TypeScheme, TyStr, TyEnv, ValEnv, QualEnv, Env, Context); projection, injection, modification; class order and admissible types (Adm_kappa: the "Which types satisfy each class" table of the survey, A19 prefix rule handled syntactically in elaboration of types); substitution respecting classes and rows with unique labels (A23); type functions and alias expansion; type schemes, instances, generalisation and Clos (no value restriction); scope of explicit (annotation) type variables (A21 nested annotations share variables; A20 escape is an error); rules for AtExp, ExpRow, Exp, Match, MRule, Dec, ValBind (annotated and unannotated members, recursive groups A24), AtPat, PatRow, Pat, Ty, TyRow; further restrictions: exhaustiveness of every match and of lambda and let patterns, redundancy (A31 literal values), principal derivations (A95), on which the further restrictions are judged (A96); inhabitants possibly infinite (A97). The default of an unresolved `number`, now Float (A27), is applied by number specialisation in dynamic-core.
- Depends on: syntax-core
- Rulings: A19 to A31, A35, A36, A39, D5
- Exemplar: "Static Semantics" rows

### static-modules: Static Semantics for Modules (Chapter 5)
- Kind: static, Level: Modules
- Defines: Interface, ModEnv, PortSet, static Basis; elaboration of headers, imports (qualified environments, `as`, `exposing`, default imports, replacement rule A28, lazy ambiguity A38), exposing lists and the interface (open, closed, private types; A29 private types in signatures legal), custom type groups (fresh type names, recursion), type aliases (type functions; record alias constructors with status v, A-survey "Records and Rows"), ports (the Port predicate defining admissible port types: Int, Float, Bool, String, `Json.Encode.Value`, unit, List/Maybe/Array of admissible, 2- and 3-tuples and closed records of admissible; not Char, functions, type variables, extensible records, custom types, Bytes A18; D11), value groups at top level; a module elaborates to an interface; module cycles forbidden.
- Depends on: static-core, syntax-modules
- Rulings: A16, A18, A28 to A30, A32, A38, A84, D6, D11
- Exemplar: "Static Semantics" rows (Modules)

### dynamic-core: Dynamic Semantics for the Core (Chapter 6)
- Kind: dynamic, Level: Core
- Defines: reduced syntax (type ascriptions and type phrases removed; annotations dropped); simple objects (SVal, BasVal, Con names, FAIL); compound objects (Val with unit, special values, basic values with partial application, constructor values, records, tuples, closures; Env, ValEnv, QualEnv); the absence of state and exceptions stated plainly (D2), and that premise order carries no meaning (A58); Rec for recursive closures; rules for AtExp, ExpRow, Exp (application of closures, constructors, basic values via APPLY), Match, MRule (FAIL), Dec, ValBind, AtPat, PatRow, Pat; equality and order on values are delegated to APPLY (Appendix D); what has no meaning: `Debug.todo` (A62), a forced delayed self-reference (A25), resource exhaustion (A61).
- Depends on: syntax-core; object names agree with static-core
- Rulings: A25, A40 to A62 (via APPLY), D2, D3
- Exemplar: "Dynamic Semantics" rows

### dynamic-modules: Dynamic Semantics for Modules (Chapter 7)
- Kind: dynamic, Level: Modules
- Defines: reduced module syntax; dynamic interfaces and module environments; evaluation of imports, custom type groups (constructor values), record alias constructors, ports (port values that make commands and subscriptions), value groups in dependency order, each top-level value once at module initialisation (A59).
- Depends on: dynamic-core, static-modules (names)
- Rulings: A59, D6
- Exemplar: "Dynamic Semantics" rows (Modules)

### effects: Tasks, Commands, Subscriptions and Ports (Chapter 8)
- Kind: dynamic, Level: Effects
- Defines: task values (succeed, fail, andThen, onError, and primitive tasks: sleep, spawn, kill, and those of the platform), command values and subscription values (none, batch, map, and leaves for managers: the task manager, outgoing and incoming ports), how the basis functions of Task, Cmd, Sub and Process build these values (D10); processes; the JSON value model (A74); encoding and decoding of values at a port, by type (A67 to A77, D11), with the admissible types from static-modules; what cannot be sent and why; what happens to an incoming value that does not decode (A71).
- Depends on: dynamic-core, static-modules (Port predicate)
- Rulings: A66 to A85, D10, D11
- Exemplar: "Dynamic Semantics" rows (conventions), "Programs"

### programs: Programs (Chapter 9)
- Kind: programs
- Defines: syntax of programs (a main module and the modules it imports, acyclic), elaboration of a program (static basis, the type of `main`: `Program flags model msg` or a view type A82; A27 default; port names unique A84), evaluation of modules, the program loop as a labelled transition system: configurations (model, pending effects, live processes, current subscriptions), events (incoming port values, timers, task completions), steps (one message at a time; A86 ordering guarantees; A66, A67 unspecified orders; A68 incoming values queued; A70 outgoing delivery order per port), flags (A72, A77), observable behaviour (sequences of port inputs and outputs), what a program with `main : Html msg` means.
- Depends on: all earlier chapters
- Rulings: A66 to A86
- Exemplar: "Programs" row

### appendix-derived-forms: Appendix A, Derived Forms
- Kind: appendix (stage 03)
- Defines: the translation tables of "Derived Forms" above, one figure per phrase class; the dependency grouping of `let` and of module bodies stated precisely; the infix resolution reference to Chapter 2.

### appendix-full-grammar: Appendix B, Full Grammar
- Kind: appendix (stage 05)
- Defines: collated grammar of Core and Modules with derived forms marked.

### appendix-static-basis: Appendix C, The Initial Static Basis
- Kind: appendix (stage 05)
- Defines: the initial static basis B0: type names (Int, Float, Char, String, List, unit, tuples, and the abstract types Array, Value, Cmd, Sub, Task, Process.Id, Program, Html), custom types of the basis (Bool, Order, Never, Maybe, Result), and the type schemes and fixities of every value in the survey's "Initial Basis".

### appendix-dynamic-basis: Appendix D, The Initial Dynamic Basis
- Kind: appendix (stage 05)
- Defines: the dynamic basis E0 and the function APPLY on every basic value: arithmetic (D3, D4; A40 to A50), equality (A50, A51), comparison (A46, A47, A53), Debug (A62), and the values of the effects chapter; basis functions written in Elm defined by their elm/core text (A60).

### appendix-implementation: Appendix E, Implementation-Dependent Details
- Kind: appendix (stage 05; definition-style S8)
- Defines: one section per parameter: the Int range and normalisation (A40, A41, A44), characters (A52, A53), Unicode version (A14), Float operations (A65), the order of commands in a batch and across managers (A66, A67), timing at the boundary (A68 to A70), case mapping, bitwise and string conversion (A54, A55, A64), eco extensions and limits (A13, A18, A33, A34, A39), known divergences of Elm 0.19.1 on JavaScript and of eco 0.2.0 from this definition (with the rulings that classify them). One table per section, one row per implementation (Elm 0.19.1 on JavaScript; eco 0.2.0).

### appendix-standard-ml: Appendix F, Elm and Standard ML
- Kind: appendix (stage 05, optional, chosen)
- Defines: a short comparison by construct of this definition with *The Definition of Standard ML (Revised)*: what is the same (D7), and the differences (no exceptions and no state, total arithmetic, row-polymorphic records, constrained type variables, flat modules, managed effects and ports).

## Key Labels

Chapters cross-reference these labels; every chapter defines the ones it owns exactly as written.

| Label | Owner | What |
|-------|-------|------|
| `ch:syntax-core`, `ch:syntax-modules`, `ch:static-core`, `ch:static-modules`, `ch:dynamic-core`, `ch:dynamic-modules`, `ch:effects`, `ch:programs`, `ch:introduction` | each chapter | chapters |
| `ch:appendix-derived-forms`, `ch:appendix-full-grammar`, `ch:appendix-static-basis`, `ch:appendix-dynamic-basis`, `ch:appendix-implementation`, `ch:appendix-standard-ml` | appendices | appendices |
| `sec:syntax-core-layout`, `sec:syntax-core-infix`, `sec:syntax-core-restrictions` | syntax-core | layout rule, infixed operators, restrictions |
| `sec:static-core-classes` | static-core | classes and admissible types |
| `sec:static-core-closure` | static-core | Clos and generalisation |
| `sec:static-core-rules` | static-core | inference rules |
| `sec:static-modules-ports` | static-modules | the Port predicate |
| `sec:dynamic-core-rules` | dynamic-core | inference rules |
| `sec:dynamic-core-apply` | dynamic-core | application of values, `\vdash v_1\,v_2 \Rightarrow v`, used by Chapters 8 and 9 |
| `sec:syntax-core-lexical` | syntax-core | lexical analysis |
| `fig:core-fixities` | syntax-core | fixity table of the basis operators |
| `sec:syntax-modules-grammar`, `sec:syntax-modules-restrictions`, `fig:default-imports` | syntax-modules | module grammar, restrictions, default imports |
| `sec:effects-tasks`, `sec:effects-commands`, `sec:effects-ports` | effects | tasks, commands and subscriptions, port coding |
| `sec:programs-execution` | programs | the program loop |
| `sec:appendix-implementation-int` | appendix-implementation | the Int parameter |
| `sec:appendix-dynamic-basis-apply` | appendix-dynamic-basis | APPLY |

## Chapter Order

1. preface
2. introduction
3. syntax-core
4. syntax-modules
5. static-core
6. static-modules
7. dynamic-core
8. dynamic-modules
9. effects
10. programs
11. appendix-derived-forms
12. appendix-full-grammar
13. appendix-static-basis
14. appendix-dynamic-basis
15. appendix-implementation
16. appendix-standard-ml

## Chapter Checklist

| Chapter | Stage | Status | Rules | Notes |
|---------|-------|--------|-------|-------|
| preface | 05 | audited | - | |
| introduction | 05 | audited | - | states decorated-metavariable convention (static-core lacks it) |
| syntax-core | 03 | audited | - | list patterns added to derived forms |
| syntax-modules | 03 | audited | - | binding order `tycon tyvarseq`; `..` reserved symbol |
| static-core | 04 | audited | 1-45 | requests: \tTuple, \tyrowvar, \names; principal derivations (A95, A96); the A27 default (Float) moved to dynamic-core |
| static-modules | 04 | audited | 46-64 | provider maps for ambiguity; closed types keep constructors in TyStr but not in interface VE; uses \sbtCmd \sbtSub |
| dynamic-core | 04 | audited | 65-112 | requests: \japp, \dcoreFV; lists are constructors [] and :: |
| dynamic-modules | 04 | audited | 113-132 | top-level groups via thunk translation (Rec cannot re-tie closures inside data); dynamic Interface (RA, CE, VE) |
| effects | 04 | audited | 133-171 | Val gains JVal; ports outport/inport; JSON numbers as decimal rationals; NaN encodes null |
| programs | 04 | audited | 172-194 | clock in configurations; main not recursive; basis module names reserved |
| appendix-derived-forms | 03 | audited | - | module types: custom-type group then aliases, elaborated together (Ch 5) |
| appendix-full-grammar | 05 | audited | - | |
| appendix-static-basis | 05 | audited | - | List, [], :: in E0 before imports; operators bound to unexposed Basics variables |
| appendix-dynamic-basis | 05 | audited | - | APPLY for all basic values; A87 number specialisation; Array.fromList/toList hidden |
| appendix-implementation | 05 | audited | - | norm identity on IntRange; very large sleep delays diverge (A81) |
| appendix-standard-ml | 05 | audited | - | |
