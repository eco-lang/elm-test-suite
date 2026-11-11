# Notation Registry: A Standard Definition of Elm?

The single home of every name and symbol in the book. `macros.sty` is generated from this file (with `gen_notation.py`); chapters write registered notation only through its macro. Single-letter metavariables written as plain letters (C, E, T, U, B, D, S) are registered with macro "(plain)".

## Conventions

- Decorated metavariables (primes, subscripts) range over the same class as the undecorated one.
- A sequence x1 ... xk is written x^(k) in the exemplar's style (`x^{(k)}`).
- Static and dynamic semantics reuse the names Env, ValEnv, QualEnv, Interface, ModEnv, Basis for their own classes; Chapter 9 distinguishes them as static and dynamic where both are in play.
- Syntactic metavariables are italic words set with `\mv`; terminals are typewriter, set with `\kw`; classes and semantic domains are roman, set with `\cls`.
- Rows have unique labels: a row variable epsilon in {varrho | epsilon} ranges over rows disjoint from Dom varrho (ruling A23).
- Options: first options with `\opt`, second with `\optt` (defn.sty).

## Syntactic Classes

| Class | Metavariable | Macro | Description | Level |
|---|---|---|---|---|
| SCon | scon | `\scon` | special constants | Core |
| Var | var | `\var` | value variables (lower-case identifiers) | Core |
| Con | con | `\con` | value constructors (upper-case identifiers) | Core |
| TyVar | tyvar | `\tyvar` | type variables | Core |
| TyCon | tycon | `\tycon` | type constructors | Core |
| Lab | lab | `\lab` | record labels (field names) | Core |
| ModId | modid | `\modid` | module identifiers and qualifiers (dotted upper-case names) | Core |
| Op | op | `\opv` | operator symbols | Core |
| LongVar | longvar | `\longvar` | possibly qualified variables `modid.var` | Core |
| LongCon | longcon | `\longcon` | possibly qualified constructors | Core |
| LongTyCon | longtycon | `\longtycon` | possibly qualified type constructors | Core |
| AtExp | atexp | `\atexp` | atomic expressions | Core |
| Exp | exp | `\expm` | expressions (macro has suffix m: `\exp` is the exponential) | Core |
| ExpRow | exprow | `\exprow` | expression rows (record fields) | Core |
| Match | match | `\match` | matches (case branches) | Core |
| MRule | mrule | `\mrule` | match rules | Core |
| Dec | dec | `\dec` | declarations (the definitions of a let) | Core |
| ValBind | valbind | `\valbind` | value bindings | Core |
| AtPat | atpat | `\atpat` | atomic patterns | Core |
| Pat | pat | `\pat` | patterns | Core |
| PatRow | patrow | `\patrow` | pattern rows (record pattern fields) | Core |
| Ty | ty | `\ty` | type expressions | Core |
| TyRow | tyrow | `\tyrow` | type-expression rows | Core |
| TyVarSeq | tyvarseq | `\tyvarseq` | type-variable sequences (parameters of type declarations) | Modules |
| Module | module | `\modm` | modules | Modules |
| Header | header | `\header` | module headers | Modules |
| Imports | imports | `\imports` | import lists | Modules |
| ExpList | explist | `\explist` | exposing lists | Modules |
| ExpItem | item | `\expitem` | exposing items | Modules |
| TopDec | topdec | `\topdec` | top-level declarations | Modules |
| DatBind | datbind | `\datbind` | custom-type bindings | Modules |
| ConBind | conbind | `\conbind` | constructor bindings | Modules |
| TypBind | typbind | `\typbind` | type-alias bindings | Modules |
| Program | program | `\program` | programs | Programs |

## Semantic Classes

| Class | Metavariable | Macro (class) | Macro (var) | Definition | Phase | Level |
|---|---|---|---|---|---|---|
| TyVar | alpha or tyvar | `\TyVar` | (plain) | simple; each has a class attribute | static | Core |
| RowVar | epsilon | `\RowVar` | (plain) | simple: row (extension) variables | static | Core |
| TyName | t | `\TyName` | (plain) | simple; each has an arity | static | Core |
| Class | kappa | `\Class` | (plain) | {any, number, comparable, appendable, compappend} | static | Core |
| IdStatus | is | `\IdStatus` | `\is` | {c, v} | static | Core |
| Type | tau | `\Type` | (plain) | TyVar u RecType u FunType u ConsType | static | Core |
| Row | varrho | `\Row` | (plain) | Lab ->fin Type | static | Core |
| RecType | (varrho, epsilon) written {varrho \| epsilon} or {varrho} | `\RecType` | (plain) | Row x (RowVar u {empty}) | static | Core |
| FunType | tau -> tau' | `\FunType` | (plain) | Type x Type | static | Core |
| ConsType | tau^(k) t | `\ConsType` | (plain) | union over k of Type^k x TyName^(k) | static | Core |
| TypeFcn | theta | `\TypeFcn` | (plain) | union over k of (TyVar u RowVar)^k x Type | static | Core |
| TypeScheme | sigma | `\TypeScheme` | (plain) | union over k of (TyVar u RowVar)^k x Type | static | Core |
| TyStr | (theta, VE) | `\TyStr` | (plain) | TypeFcn x ValEnv | static | Core |
| TyEnv | TE | `\TyEnv` | `\TE` | TyCon ->fin TyStr | static | Core |
| ValEnv | VE | `\ValEnv` | `\VE` | static: (Var u Con) ->fin TypeScheme x IdStatus; dynamic: (Var u Con) ->fin Val | both | Core |
| QualEnv | QE | `\QualEnv` | `\QE` | ModId ->fin Env (the Env in the range has an empty QE) | both | Core |
| Env | E | `\Env` | (plain) | static: QualEnv x TyEnv x ValEnv; dynamic: QualEnv x ValEnv | both | Core |
| Context | C | `\Context` | (plain) | Fin(TyName) x Fin(TyVar u RowVar) x Env, written T, U, E | static | Core |
| Interface | I | `\Interface` | (plain) | static: Env (what a module exposes, with exposure of each type); dynamic: Fin(TyCon) x ConEnv x ValEnv, written (RA, CE, VE): exposed record aliases, constructors of each exposed custom type, exposed values (Chapter 7) | both | Modules |
| ModEnv | ME | `\ModEnv` | `\ME` | ModId ->fin Interface | both | Modules |
| PortEnv | PE | `\PortEnv` | `\PE` | static: Var ->fin Type (port name to declared payload type and direction) | static | Modules |
| Basis | B | `\Basis` | (plain) | static: Fin(TyName) x ModEnv x PortEnv, written T, ME, PE; dynamic: ModEnv | both | Modules |
| SVal | sv | `\SVal` | `\sv` | simple: values of special constants | dynamic | Core |
| BasVal | b | `\BasVal` | (plain) | simple: basic values (names of operations, Appendix D), including the port values outport(p, tau) and inport(p, tau) of Chapter 8 | dynamic | Core |
| Val | v | `\Val` | (plain) | {()} u SVal u BasApp u ConVal u Record u Tuple u Closure u EffVal u JVal (values of type Value are JSON values, Chapter 8) | dynamic | Core |
| BasApp | (b, v1 ... vk) | `\BasApp` | (plain) | BasVal x Val^k, k below the arity of b (partial applications) | dynamic | Core |
| ConVal | con v1 ... vk | `\ConVal` | (plain) | Con x Val^k, k at most the arity of con | dynamic | Core |
| Record | r | `\Record` | (plain) | Lab ->fin Val | dynamic | Core |
| Tuple | (v1, v2) or (v1, v2, v3) | `\Tuple` | (plain) | Val^2 u Val^3 | dynamic | Core |
| Closure | (atpat, exp, E, VE) | `\Closure` | (plain) | AtPat x Exp x Env x ValEnv | dynamic | Core |
| FAIL | FAIL | `\FAILcls` | `\FAIL` | the result of a failed match; not a value | dynamic | Core |
| EffVal | ev | `\EffVal` | `\ev` | TaskVal u CmdVal u SubVal u ProcId u ProgVal | dynamic | Effects |
| TaskVal | tk | `\TaskVal` | `\tk` | task values, Chapter 8 | dynamic | Effects |
| CmdVal | cm | `\CmdVal` | `\cm` | command values, Chapter 8 | dynamic | Effects |
| SubVal | sb | `\SubVal` | `\sbv` | subscription values, Chapter 8 | dynamic | Effects |
| ProcId | pid | `\ProcId` | `\pid` | simple: process identifiers | dynamic | Effects |
| ProgVal | pv | `\ProgVal` | `\pv` | program values: {prog} x Record (prog r, made by Platform.worker and the platform's other program makers), Chapter 8 | dynamic | Effects |
| JVal | j | `\JVal` | (plain) | JSON values: null, Booleans, numbers, strings, arrays, objects | dynamic | Effects |
| Config | K | `\Config` | (plain) | program configurations, Chapter 9 | dynamic | Programs |
| Event | ell | `\Event` | (plain) | labels of program transitions, Chapter 9 | dynamic | Programs |

## Operations

| Operation | Written | Macro | Defined In | Meaning (one line) |
|---|---|---|---|---|
| finite maps | A ->fin B | `\finmap` | static-core | finite maps; Dom and Ran |
| domain | Dom f | `\Dom` | static-core | domain of a finite map |
| range | Ran f | `\Ran` | static-core | range of a finite map |
| finite subsets | Fin A | `\Fin` | static-core | finite subsets |
| projection | E of C | `\of` | static-core | component of a tuple of objects |
| modification | A + B | (plain +) | static-core | right map overrides left |
| context extension | C (+) VE | (plain \oplus) | static-core | extend a context, adding type names |
| class order | kappa <= kappa' | (plain \leq) | static-core | number <= comparable, compappend <= comparable, compappend <= appendable, every class <= any |
| admissible types | Adm_kappa | `\Adm` | static-core | the types a variable of class kappa may stand for |
| class of | cls(alpha) | `\clsof` | static-core | the class attribute of a type variable |
| type variables | tyvars | `\tyvars` | static-core | free type and row variables |
| type names | tynames | `\tynames` | static-core | type names occurring in an object |
| instance | sigma > tau | (plain \succ) | static-core | tau is an instance of sigma |
| generalisation | sigma > sigma' | (plain \succ) | static-core | sigma generalises sigma' |
| closure | Clos_C tau | `\Clos` | static-core | generalise over variables not free in C |
| type function application | theta(tau1 ... tauk) | (plain) | static-core | beta-reduce a type function |
| substitution | S = {tau^(k)/xi^(k)}, written tau{tau^(k)/xi^(k)} or S sigma | (plain) | static-core | replace each xi_i by tau_i; respects classes when each tau_i is in Adm_kappa for kappa the class of xi_i; S ranges over substitutions (A95) |
| derivation | D, D' | (plain) | static-core | a derivation of a sentence by the rules; D ranges over derivations for one phrase in one context (A95) |
| instance of a derivation | D' an instance of D | (plain) | static-core | for some class-respecting S, each type of D' is S applied to the corresponding type of D, each scheme of D' is no more general than S applied to that of D, and S maps U of each context of D onto U of the corresponding context of D' (A95) |
| principal derivation | D principal | (plain) | static-core | every derivation for the phrase in the context is an instance of D; legality is judged on it and evaluation follows it (A95, A96) |
| type-name renaming | rho | (plain) | static-modules | a bijection from the type names one derivation for a module generates to those another generates; instances of module derivations are taken up to rho (A96) |
| row join | {varrho \| epsilon} | `\rec` | static-core | closed record type {varrho} |
| open record | {varrho \| epsilon} | `\orec` | static-core | open record type |
| constructor type | tau t | (plain) | static-core | type construction |
| port payload | Port(tau) | `\Port` | static-modules | tau may cross a port |
| interface of | Exp(E, explist) | `\Expose` | static-modules | interface exposed by an exposing list |
| value of constant | val(scon) | `\valof` | dynamic-core | value denoted by a special constant |
| type of constant | type(scon) | `\typeof` | static-core | type of a special constant |
| apply | APPLY(b, v1 ... vn) | `\APPLY` | appendix-dynamic-basis | the finite set of results of a saturated basic value (a singleton except for equality reaching functions, and empty for Debug.todo) |
| recursive closures | Rec VE | `\Rec` | dynamic-core | tie the knot for a recursive group |
| arity | arity(b), arity(con) | `\arity` | dynamic-core | number of arguments |
| encode | Enc_tau(v) | `\Enc` | effects | value to JSON at a port |
| decode | Dec_tau(j) | `\Dec` | effects | JSON to value at a port; partial |
| Int normalisation | norm(n) | `\norm` | appendix-dynamic-basis | integer into the Int range (Appendix E) |
| Int range | IntRange | `\IntRange` | appendix-dynamic-basis | the implementation's set of Int values (Appendix E) |
| leaf-command sequence | L, c . L | (plain) | programs | L ranges over finite sequences of leaf commands, the input of the dispatch sentences s, P, Q, H \|- L => (P', Q', H') |
| transition | K --ell--> K' | `\step` | programs | program transition with label |
| static operator table | OT_STAT(op) | `\OTstat` | appendix-static-basis | Op ->fin TypeScheme x IdStatus: the scheme and status of each operator of the initial basis, fixed for every program (audit X1) |
| dynamic operator table | OT_DYN(op) | `\OTdyn` | appendix-dynamic-basis | Op ->fin Val: the value of each operator of the initial basis, fixed for every program (audit X1) |

## Judgment Forms

All sentences use the single relation symbol |-, overloaded over phrase classes as in the exemplar (`\jdg{A}{phrase}{A'}` prints A |- phrase => A'; `\jdgv{E}{v}{phrase}{A}` prints E, v |- phrase => A).

| Phase | Level | Phrase Class | Form | Macro | Pronounced |
|---|---|---|---|---|---|
| static | Core | all Core classes | C \|- phrase => A | `\jdg` | phrase elaborates to A in context C |
| static | Core | AtPat, Pat, PatRow | C \|- pat => (VE, tau) | `\jdg` | pat elaborates to VE and tau |
| static | Core | Ty | C \|- ty => tau | `\jdg` | ty denotes tau in C |
| static | Modules | Module classes | B \|- phrase => A | `\jdg` | phrase elaborates to A in basis B |
| dynamic | Core | AtExp, Exp, ExpRow, Dec, ValBind | E \|- phrase => A | `\jdg` | phrase evaluates to A in E |
| dynamic | Core | Match, MRule, AtPat, Pat, PatRow | E, v \|- phrase => A | `\jdgv` | phrase, matched against v, gives A in E |
| dynamic | Modules | Module classes | B \|- phrase => A | `\jdg` | phrase evaluates to A in B |
| static | Programs | Program | B \|-STAT phrase => A | `\jstat` | static judgment used in Chapter 9 |
| dynamic | Programs | Program | B \|-DYN phrase => A | `\jdyn` | dynamic judgment used in Chapter 9 |
| static | any | negation | C \|- phrase =/=> | `\jnot` | phrase does not elaborate |

Per-class judgment boxes (for `\rulegroup`):

| Chapter | Group | Box |
|---|---|---|
| static-core | Atomic Expressions | C \|- atexp => tau |
| static-core | Expression Rows | C \|- exprow => varrho |
| static-core | Expressions | C \|- exp => tau |
| static-core | Matches | C \|- match => tau |
| static-core | Match Rules | C \|- mrule => tau |
| static-core | Declarations | C \|- dec => VE |
| static-core | Value Bindings | C \|- valbind => VE |
| static-core | Atomic Patterns | C \|- atpat => (VE, tau) |
| static-core | Pattern Rows | C \|- patrow => (VE, varrho) |
| static-core | Patterns | C \|- pat => (VE, tau) |
| static-core | Type Expressions | C \|- ty => tau |
| static-core | Type-expression Rows | C \|- tyrow => varrho |
| dynamic-core | Atomic Expressions | E \|- atexp => v |
| dynamic-core | Expression Rows | E \|- exprow => r |
| dynamic-core | Expressions | E \|- exp => v |
| dynamic-core | Matches | E, v \|- match => v'/FAIL |
| dynamic-core | Match Rules | E, v \|- mrule => v'/FAIL |
| dynamic-core | Declarations | E \|- dec => VE |
| dynamic-core | Value Bindings | E \|- valbind => VE |
| dynamic-core | Atomic Patterns | E, v \|- atpat => VE/FAIL |
| dynamic-core | Pattern Rows | E, r \|- patrow => VE/FAIL |
| dynamic-core | Patterns | E, v \|- pat => VE/FAIL |

Modules, effects and programs chapters define their own boxes with `\jdg`, `\jdgv`, `\jstat`, `\jdyn`, and record them by adding rows here (stage 02 owns this file).

## Special Symbols

| Symbol | Macro | Meaning |
|---|---|---|
| \mathrm{any} | `\kany` | the unconstrained class |
| \mathrm{number} | `\knum` | class number |
| \mathrm{comparable} | `\kcomp` | class comparable |
| \mathrm{appendable} | `\kapp` | class appendable |
| \mathrm{compappend} | `\kcapp` | class compappend |
| \mathrm{c} | `\isc` | identifier status: constructor |
| \mathrm{v} | `\isv` | identifier status: value |
| \mathtt{Int} | `\tInt` | built-in type name Int |
| \mathtt{Float} | `\tFloat` | built-in type name Float |
| \mathtt{Char} | `\tChar` | built-in type name Char |
| \mathtt{String} | `\tString` | built-in type name String |
| \mathtt{List} | `\tList` | built-in type name List |
| \mathtt{Bool} | `\tBool` | the type name of Bool (a custom type of the basis) |
| \mathtt{()} | `\tunit` | the unit type |
| \mathtt{Maybe} | `\tMaybe` | the type name of Maybe (a custom type of the basis) |
| \mathtt{Array} | `\tArray` | the abstract type name Array of the basis |
| \mathtt{Bytes} | `\tBytes` | the abstract type name Bytes of the basis (elm/bytes), a port payload type (A92) |
| \mathtt{Value} | `\tValue` | the abstract type name Json.Encode.Value (= Json.Decode.Value) of the basis |
| \{\} | `\emptymap` | the empty map |
| \emptyset | `\emptyrow` | no row variable (closed record type) |

## Chapter Requests

Symbols added by chapter agents through `requests/<chapter>-req.tex`, merged here. The request file is the source of each definition.

| Macro | Definition | Registry Row (from the request) | Requested By |
|---|---|---|---|
| `\dbChr` | `{\cls{Chr}}` | class Chr (simple): the characters of SVal, an implementation parameter (A52) (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbch` | `{\mathit{ch}}` | metavariable of Chr: ch; a character (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbcode` | `{\mathrm{code}}` | operation code(ch): the injective map Chr -> Z, the library's Char.toCode (A52, A53) (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbNaN` | `{\mathrm{NaN}}` | special symbol: NaN, the one not-a-number float of Flt (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbfl` | `{\mathrm{fl}}` | operation fl(r): the real r rounded to a float, to nearest with ties to even, overflowing to an infinity; fl(0) = +0 (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbtrunc` | `{\mathrm{trunc}}` | operation trunc(r): the integer part of the real r, rounding toward zero (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbsat` | `{\mathrm{sat}}` | operation sat(k): k in Z or an infinity, saturated into IntRange (A44) (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbsgn` | `{\mathrm{sgn}}` | operation sgn(x): the sign, +1 or -1, of a float other than NaN (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbFun` | `{\cls{Fun}}` | class Fun: Closure u BasApp u the constructor values awaiting arguments; the function values (A51) (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbEq` | `{\mathrm{Eq}}` | operation Eq(v, v'): the non-empty subset of {True, False} of results of comparing v and v' for equality (A50, A51) (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbcmp` | `{\mathrm{cmp}}` | operation cmp(v, v'): LT, EQ or GT, the order of two comparable values (A46, A47, A53) (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbarr` | `{\mathrm{array}}` | constructor name array, arity 1, spelt by no identifier: array l is the array of the elements of the list l (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbeuler` | `{\mathrm{e}}` | special symbol: the real number e, the base of natural logarithms (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\dbpinum` | `{\pi}` | special symbol: the real number pi, the circle constant (not the primitive metavariable pi of Chapter 8) (appendix-dynamic-basis) | appendix-dynamic-basis |
| `\fgderived` | `{\textsuperscript{$\dagger$}}` | layout mark: dagger after the right-hand label of a derived alternative in the full grammar; marks "derived form, Appendix A"; appendix-full-grammar | appendix-grammar-sml |
| `\sbtOrder` | `{\mathtt{Order}}` | TyName (special symbol): Order, arity 0; the type name of Basics.Order (appendix-static-basis; may be merged with another chapter's type-name macro) | appendix-static-basis |
| `\sbtNever` | `{\mathtt{Never}}` | TyName (special symbol): Never, arity 0; the type name of Basics.Never (appendix-static-basis) | appendix-static-basis |
| `\sbtResult` | `{\mathtt{Result}}` | TyName (special symbol): Result, arity 2; the type name of Result.Result (appendix-static-basis) | appendix-static-basis |
| `\sbtCmd` | `{\mathtt{Cmd}}` | TyName (special symbol): Cmd, arity 1; the type name of Platform.Cmd.Cmd (appendix-static-basis) | appendix-static-basis |
| `\sbtSub` | `{\mathtt{Sub}}` | TyName (special symbol): Sub, arity 1; the type name of Platform.Sub.Sub (appendix-static-basis) | appendix-static-basis |
| `\sbtTask` | `{\mathtt{Task}}` | TyName (special symbol): Task, arity 2; the type name of Platform.Task, also Task.Task (appendix-static-basis) | appendix-static-basis |
| `\sbtProcessId` | `{\mathtt{ProcessId}}` | TyName (special symbol): ProcessId, arity 0; the type name of Platform.ProcessId, also Process.Id (appendix-static-basis) | appendix-static-basis |
| `\sbtProgram` | `{\mathtt{Program}}` | TyName (special symbol): Program, arity 3; the type name of Platform.Program (appendix-static-basis) | appendix-static-basis |
| `\sbtNode` | `{\mathtt{Node}}` | TyName (special symbol): Node, arity 1; the type name of VirtualDom.Node, also Html.Html (appendix-static-basis) | appendix-static-basis |
| `\japp` | `[3]{\vdash #1\,#2 \Rightarrow #3}` | judgment form (dynamic, Core, application of values); written /- v1 v2 => v; v1 applied to v2 gives v (Section sec:dynamic-core-apply) | dynamic-core |
| `\dcoreFV` | `{\mathrm{FV}}` | operation free variables; written FV(valbind); the set of variables occurring free (Appendix A sense) in the right-hand sides of valbind | dynamic-core |
| `\dmConEnv` | `{\cls{ConEnv}}` | class ConEnv (dynamic, Modules): TyCon ->fin ValEnv; constructor environments: the constructors of each custom type, by type | dynamic-modules |
| `\dmCE` | `{\mathit{CE}}` | metavariable of ConEnv: CE (dynamic, Modules) | dynamic-modules |
| `\dmRA` | `{\mathit{RA}}` | metavariable of Fin(TyCon): RA; the record aliases whose constructors an interface exposes (dynamic, Modules) | dynamic-modules |
| `\dmmerge` | `{\mathbin{\boxplus}}` | operation E1 [+] E2 (boxed plus): modification of environments that merges the environments of a qualifier common to both (dynamic, Modules) | dynamic-modules |
| `\dmrecord` | `{\mathrm{record}}` | basic value record(lab1...labn), n >= 1, arity n: the constructor of a record alias; record() stands for the empty record (dynamic, Modules) | dynamic-modules |
| `\dmthunk` | `[1]{#1^{\bullet}}` | operation valbind^bullet, exp^bullet: the translation of a top-level value group in which each member is reached through a function of unit (dynamic, Modules) | dynamic-modules |
| `\BVal` | `{\cls{BVal}}` | class BVal (compound), metavariable j: boundary values, the JSON values in which a byte sequence may stand wherever a value may; JVal is a subset (A92) (effects) | effects-a92 |
| `\effByt` | `{\cls{Byt}}` | class Byt (simple): byte sequences, the finite sequences of integers from 0 to 255, written bytes(o1...ok); not JSON values (A92) (effects) | effects-a92 |
| `\effbytes` | `{\mathrm{bytes}}` | byte sequence bytes(o1...ok), each oi an integer from 0 to 255: a member of Byt (A92) (effects) | effects-a92 |
| `\dbbin` | `{\mathrm{binary}}` | constructor name binary, arity 1, spelt by no identifier: binary l, l a list of Int values from 0 to 255, is the value of type Bytes holding that byte sequence (A92) (appendix-dynamic-basis) | effects-a92 |
| `\effp` | `{\mathit{p}}` | metavariable of Var used for port names: p; a port name (Chapter 8, effects) | effects |
| `\effPrim` | `{\cls{Prim}}` | class Prim (simple), metavariable pi: primitives of tasks, {sleep, spawn, kill} u Prim_plat (effects) | effects |
| `\effPrimPlat` | `{\cls{Prim}_{\mathrm{plat}}}` | class Prim_plat: the platform's further primitives, a parameter of the platform (A83) (effects) | effects |
| `\effMgr` | `{\cls{Manager}}` | class Manager (compound), metavariable m: {task} u ({out} x Var) u ({in} x Var x Type) u Manager_plat (effects) | effects |
| `\effMgrPlat` | `{\cls{Manager}_{\mathrm{plat}}}` | class Manager_plat (simple): the platform's further managers, a parameter of the platform (A83) (effects) | effects |
| `\effm` | `{\mathit{m}}` | metavariable of Manager: m (effects) | effects |
| `\effAction` | `{\cls{Action}}` | class Action (compound): union over k of Prim x Val^k x TaskVal, written pi(v1...vk) ⇓ tk (effects) | effects |
| `\effa` | `{\mathit{a}}` | metavariable of Action: a; the label of a task reduction (effects) | effects |
| `\effJNum` | `{\cls{JNum}}` | class JNum (simple): JSON numbers, the rationals m x 10^e (m, e integers) (effects) | effects |
| `\effStr` | `{\cls{Str}}` | class Str: the strings of SVal, also the JSON strings and the keys of JSON objects (effects) | effects |
| `\effFlt` | `{\cls{Flt}}` | class Flt: the floating-point numbers of SVal (effects) | effects |
| `\effFltFin` | `{\cls{Flt}_{\mathrm{fin}}}` | class Flt_fin: the finite floating-point numbers of SVal (effects) | effects |
| `\effnull` | `{\mathtt{null}}` | special symbol: JSON null (effects) | effects |
| `\efftrue` | `{\mathtt{true}}` | special symbol: JSON true (effects) | effects |
| `\efffalse` | `{\mathtt{false}}` | special symbol: JSON false (effects) | effects |
| `\effJarr` | `[1]{\mathtt{[}#1\mathtt{]}}` | JSON array, written [j1,...,jn] in typewriter brackets: a member of JVal^n (effects) | effects |
| `\effsucceed` | `{\mathrm{succeed}}` | task value succeed v: a task that has succeeded with v (effects) | effects |
| `\efffail` | `{\mathrm{fail}}` | task value fail v: a task that has failed with v (effects) | effects |
| `\effandThen` | `{\mathrm{andThen}}` | task value andThen(v, tk): tk, then v applied to its success value (effects) | effects |
| `\effonError` | `{\mathrm{onError}}` | task value onError(v, tk): tk, then v applied to its failure value (effects) | effects |
| `\effprim` | `{\mathrm{prim}}` | task value prim(pi, v1...vk): a primitive task (effects) | effects |
| `\effsleep` | `{\mathrm{sleep}}` | primitive sleep (Process.sleep) (effects) | effects |
| `\effspawn` | `{\mathrm{spawn}}` | primitive spawn (Process.spawn) (effects) | effects |
| `\effkill` | `{\mathrm{kill}}` | primitive kill (Process.kill) (effects) | effects |
| `\effOut` | `{\mathrm{Out}}` | operation Out(pi, v1...vk): the set of possible outcomes of a primitive (effects) | effects |
| `\effred` | `[1]{\xrightarrow{#1}}` | judgment form tk --a--> tk' (or unlabelled, silent): task reduction (effects) | effects |
| `\effdone` | `[2]{#1\Downarrow #2}` | action pi(v1...vk) ⇓ tk: primitive performed with outcome tk (effects) | effects |
| `\effbatch` | `{\mathrm{batch}}` | command or subscription value batch(cm1...cmn) (effects) | effects |
| `\effnone` | `{\mathrm{none}}` | the command or subscription value batch() with no components (effects) | effects |
| `\effmap` | `{\mathrm{map}}` | command or subscription value map(v, cm) (effects) | effects |
| `\effleaf` | `{\mathrm{leaf}}` | command or subscription value leaf(m, v): a request to manager m (effects) | effects |
| `\effmtask` | `{\mathrm{task}}` | manager name: the task manager (effects) | effects |
| `\effmout` | `{\mathrm{out}}` | manager out p: the outgoing port p (effects) | effects |
| `\effmin` | `{\mathrm{in}}` | manager in(p, tau): the incoming port p of payload type tau (effects) | effects |
| `\effFlat` | `{\mathrm{Flat}}` | operation Flat(cm), Flat(sb): the finite multiset of leaf commands (subscriptions) of a command (subscription) (effects) | effects |
| `\effmset` | `[1]{\{\!/\,#1\,/\!\}}` | finite multiset {/ x1, ..., xn /}; multiset union is \uplus (effects) | effects |
| `\effrecv` | `[3]{\vdash #1 \triangleleft #2 \Rightarrow #3}` | judgment form /- c </ x => v: leaf command c, receiving input x, gives the message v (effects) | effects |
| `\efffloat` | `{\mathrm{float}}` | operation float(j): the floating-point number nearest the JSON number j, rounded as a floating-point constant (effects) | effects |
| `\effprog` | `{\mathrm{prog}}` | program value prog r: ProgVal = {prog} x Record (effects) | effects |
| `\effoutport` | `{\mathrm{outport}}` | basic value outport(p, tau), arity 1: the value of an outgoing port (effects) | effects |
| `\effinport` | `{\mathrm{inport}}` | basic value inport(p, tau), arity 1: the value of an incoming port (effects) | effects |
| `\effc` | `{\mathit{c}}` | metavariable of leaf commands and leaf subscriptions (members of CmdVal u SubVal with no batch): c (effects) | effects |
| `\effx` | `{\mathit{x}}` | metavariable of inputs to a leaf: x, a value or a pair (p, j) of a port name and a JSON value (effects) | effects |
| `\pgStaticBasis` | `{\cls{StaticBasis}}` | class StaticBasis: the class Basis of the static semantics of Modules (Chapter 5), Fin(TyName) x ModEnv x PortEnv, renamed in Chapter 9 (programs) | programs |
| `\pgDynamicBasis` | `{\cls{DynamicBasis}}` | class DynamicBasis: the class Basis of the dynamic semantics of Modules (Chapter 7), ModEnv, renamed in Chapter 9 (programs) | programs |
| `\pgBstat` | `{B_{\mathrm{STAT}}}` | metavariable of StaticBasis: B_STAT; B or (B_STAT, B_DYN) ranges over Basis = StaticBasis x DynamicBasis (programs) | programs |
| `\pgBdyn` | `{B_{\mathrm{DYN}}}` | metavariable of DynamicBasis: B_DYN (programs) | programs |
| `\pgDflt` | `{\mathrm{Dflt}\,}` | operation Dflt sigma: the body of the type scheme sigma with Float for each bound type variable of class number (A27) (programs) | programs |
| `\pgTime` | `{\cls{Time}}` | class Time = {x in R / x >= 0}, metavariables s (instants, milliseconds since the program started) and d (durations) (programs) | programs |
| `\pgProc` | `{\cls{Proc}}` | class Proc: (TaskVal x Time x (CmdVal u {spawned})) u {ended}; the state of a process (programs) | programs |
| `\pgProcMap` | `{\cls{ProcMap}}` | class ProcMap = ProcId ->fin Proc, metavariable P (plain): the processes started so far (programs) | programs |
| `\pgOutQueue` | `{\cls{OutQueue}}` | class OutQueue = Var ->fin JVal^*, metavariable Q (plain): the values awaiting delivery on each outgoing port (programs) | programs |
| `\pgPending` | `{\cls{Pending}}` | class Pending = CmdVal ->fin {1,2,...} (finite multisets), metavariable H (plain): the leaf commands handed to the platform's managers (programs) | programs |
| `\pgorig` | `{\mathit{o}}` | metavariable o of CmdVal u {spawned}: the origin of a process (programs) | programs |
| `\pgspawned` | `{\mathrm{spawned}}` | special symbol: spawned; the origin of a process started by Process.spawn (programs) | programs |
| `\pgended` | `{\mathrm{ended}}` | special symbol: ended; the state of a process that has ended or been killed (programs) | programs |
| `\pgnil` | `{\mathrm{nil}}` | special symbol: nil; the empty finite sequence; sequences are concatenated with \cdot (programs) | programs |
| `\pgLeaf` | `{\mathrm{Leaf}}` | operation Leaf(m, v): the set of leaf commands (or subscriptions) map(v_n, ... map(v_1, leaf(m, v)) ...), n >= 0 (programs) | programs |
| `\pgFlags` | `[1]{\mathrm{Flags}_{#1}}` | operation Flags_tau(j), partial: the flags value of j at tau: () if tau is the unit type (A77), Dec_tau(j) otherwise (programs) | programs |
| `\pgQinit` | `{Q_{\mathrm{init}}}` | object Q_init: the outgoing queues of a program at start, each empty (programs) | programs |
| `\pgEvIn` | `{\mathrm{in}}` | event in(p, j): the host sends j on the incoming port p (programs) | programs |
| `\pgEvOut` | `{\mathrm{out}}` | event out(p, j): the program delivers j on the outgoing port p (programs) | programs |
| `\pgwait` | `{\mathrm{wait}}` | event wait d: d milliseconds pass (programs) | programs |
| `\pgEventPlat` | `{\cls{Event}_{\mathrm{plat}}}` | class Event_plat (simple): the events of the platform's managers, a parameter of the platform (A83) (programs) | programs |
| `\pgplatstep` | `[1]{\xrightarrow{#1}_{\mathrm{plat}}}` | judgment form K --ell-->plat K': a platform step, given by the platform (A83) (programs) | programs |
| `\pgTr` | `{\mathrm{Tr}}` | operation Tr(program, j): the set of traces of program started with flags j (programs) | programs |
| `\tTuple` | `[1]{\mathtt{Tuple}_{#1}}` | TyName (special symbol): Tuple_k; the built-in type name of k-tuples (k = 2, 3), arity k; static-core | static-core |
| `\tyrowvar` | `{\xi}` | metavariable of TyVar u RowVar: xi; a type variable or a row variable (binders of type functions and type schemes); static-core | static-core |
| `\names` | `{\mathrm{names}\,}` | operation: names U; the set of syntactic type variables tyvar that name a member of U (U a set of type and row variables); static-core | static-core |
| `\smProvMap` | `{\cls{ProvMap}}` | class ProvMap (compound), metavariable pi (plain): LongId ->fin (Fin(ModId) \ {emptyset}); provider maps: the modules that provide each identifier to a module (static-modules) | static-modules |
| `\smId` | `{\cls{Id}}` | class Id: (Var u Con) u TyCon, a disjoint union; the unqualified identifiers that an environment binds (static-modules) | static-modules |
| `\smid` | `{\mv{id}}` | metavariable of Id: id (static-modules) | static-modules |
| `\smLongId` | `{\cls{LongId}}` | class LongId: (LongVar u LongCon) u LongTyCon, a disjoint union; long identifiers of the three classes (static-modules) | static-modules |
| `\smlongid` | `{\mv{longid}}` | metavariable of LongId: longid (static-modules) | static-modules |
| `\smmerge` | `{\uplus}` | operation: written pi (+)_modid (N, N'); the provider map pi in which modid replaces the providers of N and joins those of N' (static-modules) | static-modules |
| `\smenv` | `{\mathrm{env}}` | operation: written env(ME, pi); the environment that the provider map pi gives in ME, ambiguous identifiers omitted (static-modules) | static-modules |
| `\smops` | `{\mathrm{ops}}` | operation: written ops(modid); the operators that the module modid declares, empty for every module of a program (static-modules) | static-modules |
| `\smlabs` | `{\mathrm{labs}}` | operation: written labs(ty), partial; the labels of a record alias body in the order written (static-modules) | static-modules |
| `\smdirout` | `{\mathrm{out}}` | special symbol: out; direction of an outgoing port in a PortEnv (static-modules) | static-modules |
| `\smdirin` | `{\mathrm{in}}` | special symbol: in; direction of an incoming port in a PortEnv (static-modules) | static-modules |
