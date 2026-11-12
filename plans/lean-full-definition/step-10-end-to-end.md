# Step 10: end to end (number specialisation and reduction in Lean)

Part of [the plan](../lean-full-definition.md), Part II. Follows [conventions.md](conventions.md).
Status: specified 2026-11-11; done 2026-11-12 except `ident_` (see the last bullet), with
these differences from this specification:

- **Accepted.** `Stat/Specialise.lean`, `Stat/Erase.lean`, `Stat/EndToEnd.lean`,
  `Stat/EndToEndIn.lean`, `Stat/Pipeline.lean`, `Stat/CopyLoop.lean`, `Mod/Reduced.lean` (Part I has
  `Program` and `Prog.WorkerTest`, not `ModProgram`; their reduced parts are defined there),
  `SyntaxDecEq.lean` (decidable equality of the syntaxes, written out, since `deriving` refuses nested
  mutual types), `lake exe compare-e2e`: 579 programs, 579 agree. 579 `spec_` theorems (4 by
  `native_decide`, the programs whose kernel check breaks the budget) and 577 `mean_` theorems (two
  tests have no meaning), written by `lake exe certify` into `Certs/EndToEnd*.lean`, not by the
  translator: certify already knows each test's import context (`spec_` by `endToEnd_of_ctx
  ctx_k_eq`, about 1 s a test instead of 8) and its `legal_` theorem, which `mean_` uses for the
  static premise (`programSem_of_legal`; `endToEnd` does not check the further restrictions). The
  general theorems: copy names, the copy loop (`copyLoop_fuel`, `copyLoop_least`, `copies_le_pow`),
  payload types and `main`, the pipeline. The 15 rulings of `Stat/SpecExamples.lean`, none against
  the book. The site's test pages show each test's `legal_`/`refuse_`, `spec_` and `mean_`.
- **Translator changes.** Items 1 and 2 as specified, item 3 already held; and one this
  specification did not list: the translator wrote `Html.text` where the source has `text` imported
  by an exposing list (431 tests), and now keeps identifiers as written. Items 4, 5 and 7 are done by
  `certify` and the site data instead (no `endToEnd` field in the manifest; the site reads
  `../static-report.json`).
- **Issues found:** item 8 (an occurrence outside its group, fixed in Lean and the translator) and
  item 9 (incoherent modules: `ident_` is false as the definitions stand).
- **`ident_` not delivered.** The invariance lemma is proved up to the step across bases:
  specialisation is invariant under renaming (`specExp_rename`, `reduceWith_rename`), and two module
  derivations that are instances of each other in one basis differ by a renaming of their value
  items (`mutualInstanceMod_items`), in `Stat/Rename*.lean` and `Stat/Mutual*.lean` (about 4,400
  lines). `reduce_principal_unique`, `specOf_functional` and `ident_of_spec` are false as the
  definitions stand (item 9, `Stat/SplitCounterexample.lean`); the remaining work (transport of
  principal derivations across bases, the rest of `ProgRel`, the induction over modules; about 1,700
  lines) waits for the decision item 9 asks for. `IsPrincipalMod` now quantifies over derivations
  without free `bnd` variables (`NoFreeBnd`, `Stat/Principal.lean`), the derivations of the book.

## Goal

Until this step every theorem about a translated test is about a Lean object the translator
wrote: the reduced program, with its number specialisation, its port payload types, its order of
modules and the type of its `main`, all computed by `Translate/Infer.elm` and
`Translate/Specialise.elm` (trust tag `[elab]`). Step 10 computes the same object in Lean from the
source syntax, through the static semantics of step 9, and proves per test that the two agree. It
delivers:

1. **Number specialisation as a Lean function** (`dynamic-core.tex`, Section
   `sec:dynamic-core-numbers`): defaulting, the copies of each declaration of values (`let` and
   top level), the redirection of every occurrence to the copy for its instance (A93's vacuous
   quantifiers included), and the exposing items that stand for copies
   (`dynamic-modules.tex`, Section `sec:dynamic-modules-reduced`). It is defined on the
   program-level object of finding B1: the sequence of principal derivations of the program's
   modules, each in the basis that `r:p-stat-module` (`programs.tex`) builds from the earlier
   ones, represented by step 9's annotated modules.
2. **Type erasure** to Part I's reduced module syntax, with the port payload types (`Port`,
   Figure `fig:static-modules-port`) converted to Part I's `Eff.PTy`, and the kind of `main` from
   `Dflt` (`programs.tex`, before `r:p-stat-module`).
3. **The invariance lemma** (finding B1): specialisation gives the same reduced program for every
   two derivations that differ by a renaming of type and row variables and of generated type
   names, so "the specialisation of the program" is well defined once principal derivations
   exist.
4. **Per test**, for every test that Part I translates: `reduce (infer (derive src))` equals the
   translator's reduced program, by `decide +kernel` where the budget allows and `native_decide`
   otherwise, decided by a measurement on one shard first (feasibility finding F-15).
5. **`r:p-program` with both premises** (`programs.tex`), in the test basis, under the hypothesis
   of decision D11 (see "Issues with the plan", item 1, for what that hypothesis must contain),
   and the identification of the specialisation of the program with the reduced part of the
   translator's program, through which every theorem of Part I about that program becomes a
   theorem about the program the source denotes.

After this step `[elab]` is retired on every page of a test that has its end-to-end theorem;
`[principal]` remains until step 11.

## Prerequisites

Steps 9, 8, 3 and 5 (plan, "Order of work": "10 needs 9, 3 and 5"; step 8 through step 9), and
through them steps 2 and 4. The interfaces this step relies on are listed here with the name used
below. Where the specification of that step names it differently, the name there wins and this
file is corrected; where that specification does not provide it, this step adds it in the file
named in the last column.

### From Part I

[Step 3](step-03-module-form.md) writes each test as `g_<project>_<TestName> : Mod.ModProgram`
(fields `name`, `source`, `native`, `modules : List Mod.Module`, `checks`, `meaning`), whose
modules are already the reduced, grouped modules of `sec:dynamic-modules-reduced`: the translator
prints `Module.ofSource header imports types aliases items`, and that Lean function applies the
grouping of Appendix A (step 8 replaces it by its proved derived form). [Step 5](step-05-programs.md)
adds `ports : Eff.PortEnv`, `flagsType : Eff.PTy` and `kind : Mod.ProgKind` (`view` or `worker`).
(Step 5's example names its program `p_elm_PortEchoTest`; step 3's convention `g_` is used here.)

| Name used here | What it must be | Step | Added here if missing |
|----------------|-----------------|------|-----------------------|
| `Mod.Module`, `Mod.Module.ofSource`, `Mod.ModProgram`, `Mod.ProgKind` | as in steps 3 and 5 | 3, 5 | |
| `Mod.EvalProgram : Mod.Basis → List Mod.Module → Val → Prop`, its logged form | `r:p-dyn-module`, `r:p-dyn-main` (step 3's `EvalProgram`, `EvalProgramL`; step 5's `ProgEval` on a `ModProgram`) | 2, 3, 5 | |
| `Mod.ViewChecks`, `Prog.WorkerTest.Holds`, `t_<project>_<TestName>` | step 3's statement for views (`ViewChecks (Btest []) g.modules cs`) and step 5's for workers (`w.Holds`, `w.prog = g`) | 3, 5 | |
| `Mod.Reduced` and `Mod.ModProgram.reduced : Mod.ModProgram → Mod.Reduced` | the part of a program that the dynamic semantics reads: `modules`, `ports`, `flagsType`, `kind` | | `Stat/EndToEnd.lean` |
| `Prog.workerExec_congr : p.reduced = q.reduced → (WorkerExec p j h l ↔ WorkerExec q j h l)` | step 5's executions read a program only through these fields (`ViewChecks` takes the modules alone) | 5 | `Stat/EndToEnd.lean`, by unfolding |
| `Mod.value_of_viewChecks : ViewChecks B ms cs → ∃ v, EvalProgram B ms v`, `Prog.value_of_holds : w.Holds → ∃ v, EvalProgram B w.prog.modules v` | a check statement includes a value of the program (the logged relation's *forget*, D4; a worker's execution starts from the value of `main`) | 3, 5 | `Stat/EndToEnd.lean` |
| `Eff.PTy`, `Eff.PortDir`, `Eff.PortEnv`, `Eff.PTy.Canon` | payload types and port environments, as in [step 4](step-04-effects.md) (`Eff/PayloadTypes.lean`) | 4 | |
| `Mod.Btest` | the dynamic test basis of D2: [step 2](step-02-modules.md)'s `Mod.Btest (lib : ModEnv := [])`; written `Mod.Btest` here for `Mod.Btest lib` with the core library of the tests' time (`Btest []` until core-library.md lands) | 2 | |
| `Mod.ExpList`, `Mod.ExpItem` | step 2's exposing lists (`var` items, one per copy, `sec:dynamic-modules-reduced`) | 2 | |

`Mod.Btest` must bind, beside `abs` and `abs$Int` (as `InitialBasis.lean` does today,
Appendix D after Figure `fig:dynamic-basis-elm`), the copies of every core-library Elm text whose
scheme quantifies a `number` variable (D2(b); for instance `List.sum` and `List.product` with
`sum$Int` and `product$Int`). See "Issues with the plan", item 6.

### From step 8

[Step 8](step-08-source-syntax.md) gives (namespace `StandardElm.Src`):

| Name | What |
|------|------|
| `Src.SProgram`, `s_<project>_<TestName> : Src.SProgram` | the source syntax the translator writes per test |
| `Src.BProgram`, `Src.BModule`, `Src.BTopDec`, `Src.BValBind`, `Src.BExp`, ... | the bare syntax after the derived forms, with type expressions, annotations, custom types, aliases and ports, constants `SLit` unspecialised (its section 2) |
| `Src.deriveProgram : Src.SProgram → Src.BProgram` | the derived forms (total; meaningful under `Src.SynOK`), including the groupings of `sec:appendix-derived-forms-let` and `sec:appendix-derived-forms-modules` by `Src.Grouping.components` and `Src.Grouping.aliasOrder` |
| `Src.SynOK`, `syn_<project>_<TestName> : Src.SynOK s_<project>_<TestName>` | the syntactic restrictions and their per-test theorem |
| `Src.Grouping.components` | `Derived.lean`'s `components` moved unchanged (least member first); `Derived.lean`'s `letDefs` calls it |

Because Part I's grouping (`Mod.Module.ofSource`, `letDefs`) and step 8's derived forms use the same
`Src.Grouping.components`, the copies that this step emits are grouped the same way on both sides
of the comparison (Choices, item 4). Step 8 also leaves to this step the statement of finding B4's
independence for evaluation (its section 3.3); it is stated below as a proposition, not proved
(Theorems, "Independence of the grouping").

### From step 9

[Step 9](step-09-static-semantics.md) provides these names (its section 14, `Stat/Interface.lean`,
was written to match this specification), in namespace `StandardElm.Stat`:

| Name | What |
|------|------|
| `TyVar` (with its class), `RowVar`, `BVar`, `TyName`, `Ty`, `Scheme`, `Ctx`, `SBasis`, `PortEnv`, `Subst` (`Respects`, `DefinedOn`), `Gen` (`≻`) | the static objects (its sections 1 to 3) |
| `tInt`, `tFloat`, `tProgram`, `tNode`, `dflt`, `Port` (decidable) | Figure `fig:static-core-builtin`, Appendix C, `Dflt`, Figure `fig:static-modules-port` |
| `AExp`, ..., `AValBind`, `AModule`, `AProgram := List AModule` (aliases `AnnExp`, `AnnModule`, ...) | annotated phrases (D10): the type at every node, the instance list at every occurrence, the group's `VE` before closure at every declaration, `U'` at every annotated binding, the type environment of the type declarations |
| `occurrences C a`, `groupNodes C a` | at every occurrence: its path, the scheme used, the instance keyed by the scheme's bound variables; at every group node: its path, `C`, `VE`, each annotated member's `U'` |
| `checkExp`, `checkModule`, `checkProgram : SBasis → AProgram → Bool`, `AModule.result`, `AModule.erase` | the checker (each module in the basis the earlier ones build), with soundness and adequacy |
| `ModDeriv`, `PrincipalMod`, `InstanceOf C0 a' a`, `IsPrincipal`, `InstanceOfMod B a' a`, `IsPrincipalMod`, `principal_unique` | instances and principal derivations (`sec:static-core-principal`, `sec:static-modules-principal`); two principal derivations are instances of each other by definition |
| `PrincipalExists`, `PrincipalExistsFor (p : Src.BProgram)` | D11's hypothesis, and its instance at one program's modules (step 9 states its positive theorems under the latter, because the former is false as the book stands: its "Issues with the plan", item 1) |
| `inferProgram : SBasis → Src.BProgram → Except String AProgram` | the unverified inference |
| `a_<project>_<TestName> : AProgram` | the certificate `lake exe certify` writes for each compile-success test (`Certs/`) |
| `StatProgram B p (τ, PE)` (`ElProgram`), `LegalProgram B sp` | Chapter 9's `r:p-stat-*` with module premises from principal derivations; legality of a source program, on `Src.deriveProgram (Src.canonOrder sp)` |
| `Btest` | the static test basis (D2) |
| `provider B a x` | the module that provides an imported identifier |
| `check_subst` | the checker is stable under a substitution that respects classes and is defined |

## Choices made in this specification

The book leaves these open; each is fixed here, with the reason.

1. **Output form.** Lean's specialisation builds each module with step 3's `Mod.Module.ofSource`
   from its own written items (top-level definitions as `D.Def` with an empty parameter list and
   the bare right-hand side), with the ports, the flags type and the kind, and the comparison is
   made on `Mod.Reduced` (the modules, which are reduced and grouped values, and the other three
   fields). Reason: the translator writes
   `.fn x [p1, p2] e` where the bare syntax has `x = \p1 -> \p2 -> e`; both give the same bare
   phrase after grouping (`Derived.lean`: `Def.rhs (.fn x ps e) = lams ps e`, and
   `lams [] e = e`), so comparing reduced programs makes the theorem independent of how a
   definition was written, and of the fields of `ModProgram` that the semantics does not read
   (`name`, the checks).
2. **Canonical order of the `number` variables of a declaration.** Order of first occurrence in
   the bodies of the bindings' schemes, bindings in their order in the group, each body read left
   to right (arguments of a constructed type in order; domain before range; fields of a record in
   label order). The copy at assignment `a` binds `x$K1$...$Kk` with `Ki` the key (`Int` or
   `Float`) of the `i`th variable, and the default copy binds `x`. Reason: the order is invariant
   under renaming (the invariance lemma needs it), and the names are the translator's today when
   a declaration has one variable (all but three tests). The translator changes to this order
   (Translator changes, item 1).
3. **A93's vacuous variables are Float at every occurrence.** At an occurrence of `x`, a variable
   of the declaration that `x`'s scheme quantifies but its body does not mention is assigned
   Float, whatever the annotated phrase records as its instance. Reason: the instance of a
   vacuous bound variable is not part of any sentence of the derivation (the side condition
   `σ ≻ τ` of `r:s-atexp-longvar` has its witness outside the sentence), so the book's principal
   derivation does not determine it; the book says "a variable that nothing at the occurrence
   fixes is Float" (`sec:dynamic-core-numbers`), and nothing at the occurrence fixes a variable
   the type does not mention. See Issues, item 5.
4. **Copies of one declaration in the bare syntax.** The copies of a group are emitted as
   definitions in the order: default copy first, then the others by the lexicographic order of
   their assignments with Float before Int (which is the string order of their keys); within a
   copy, the members in group order. The `let` (or module body) is then rebuilt by Appendix A's
   grouping of the resulting definitions (`letDefs`, and step 8's module grouping). Reason: the
   book says only that the declaration "is replaced by" its copies; a copy may refer to another
   copy of the same group (polymorphic recursion through an annotation), so the copies cannot in
   general be nested in a fixed order, and regrouping by "refers to" is the reading under which
   Appendix A's independence argument (A57 to A59, finding B4) applies. This is what the
   translator does today. See Issues, item 3.
5. **An occurrence inside its own group.** Each variable of the declaration takes the type the
   enclosing copy gives it unless the scheme used at the occurrence binds it (an annotated
   member's `U'`), in which case it takes the instance's type. Reason: within the group the
   closure has not happened (`r:s-dec-group`: the group elaborates in `C + VE`), so only `U'` is
   bound in the scheme seen there.
6. **Basis values.** A value of the test basis is copied only if it is an Elm text whose scheme
   quantifies a `number` variable (Appendix D: "Of the values of the basis written in Elm, only
   `abs` has a type scheme that quantifies a variable of class number"; plus the core-library
   texts of D2). Basic values (`add`, `clamp`, ...) are never copied (A49). The list is a literal
   table, checked against both bases.
7. **The hypothesis.** The per-test theorems are stated under `D11For Btest p` (defined below):
   the inference returns principal derivations for this program, in the bases `r:p-stat-module`
   builds from `Btest` (which gives the existence part of D11 where the theorems use it). Reason:
   Issues, item 1.
8. **Where inference runs.** In the kernel, inside the per-test theorem, as F-15 proposes; with
   the measurement and fallbacks of "Acceptance", item 3. Step 9 already writes certificates
   (`a_X`, by `lake exe certify`), which makes the first fallback (the kernel checks a written
   certificate and runs only the specialisation) cheap to take (step 9, "Issues with the plan",
   item 6).

## Lean definitions

### Files

| File | Namespace | Contents |
|------|-----------|----------|
| `StandardElmMech/Stat/ProgramDeriv.lean` | `StandardElm.Stat` | `D11For` (over step 9's `InferPrincipalFor`), renamings of annotated programs, `mutualInstanceMod_renaming` |
| `StandardElmMech/Stat/Specialise.lean` | `StandardElm.Stat` | numbers, assignments, copy names, the variables of a group, resolution, scopes, the mutual specialisation, the copy loop, modules, programs, exposing items, the basis table |
| `StandardElmMech/Stat/Erase.lean` | `StandardElm.Stat` | `toPTy`, `mainKind` (with step 9's `dflt`), erasure of type declarations and ports, `defaultNum` |
| `StandardElmMech/Stat/EndToEnd.lean` | `StandardElm.Stat` | `endToEnd`, `SpecOf`, `ProgramSem` (`r:p-program`), the general theorems |
| `StandardElmMech/Stat/SpecExamples.lean` | `StandardElm.Stat` | the unit examples (Tests, below) |
| `StandardElmMech/Generated/EndToEnd<Shard><nn>.lean` | `StandardElm` | per test: `spec_`, `ident_`, `mean_` theorems (written by the translator) |

None of these imports `Lean`. `StandardElmMech.lean` imports all of them.

### The program-level object (finding B1)

```lean
namespace StandardElm.Stat

/-- An annotated program (step 9's `AProgram`): one annotated module per module, main last. -/
abbrev AnnProgram := AProgram

-- `AProgram.bases`, `ProgDeriv`, `PrincipalProgDeriv` and `InferPrincipalFor` are step 9's
-- (`Stat/Principal.lean`, section 8), where the per-test theorems of step 9 first use them.

/-- D11's hypothesis for one program, in the form the theorems of this step need: what the
    inference returns for it is principal. -/
def D11For (B : SBasis) (p : Src.BProgram) : Prop := InferPrincipalFor B p
```

`SBasis.WF` is step 9's well-formedness of a basis (the type names of its interfaces are in its
`T`; its schemes have no free variables). If step 9 has no such predicate, it is added here with
those two clauses.

### Renamings

```lean
/-- A renaming of a derivation: type variables to type variables of the same class, row variables
    to row variables, generated type names to type names of the same arity; finite maps, the
    identity outside their domains. -/
structure Renaming where
  tv : List (TyVar × TyVar)
  rv : List (RowVar × RowVar)
  tn : List (TyName × TyName)

/-- Injective, class-preserving and arity-preserving; the identity on every variable named by
    the syntax (explicit variables are named, sec:static-core-simple) and on every type name of
    `T of B`. -/
def Renaming.WF (B : SBasis) (r : Renaming) : Prop

def Renaming.ty     (r : Renaming) : Ty → Ty
def Renaming.scheme (r : Renaming) : Scheme → Scheme
def AnnModule.rename  (r : Renaming) : AnnModule → AnnModule
def AnnProgram.rename (r : Renaming) (a : AnnProgram) : AnnProgram := a.map (·.rename r)

/-- Equality of annotated programs up to the equality of type schemes (sec:static-core-schemes:
    renaming and reordering bound variables, deleting bound variables that do not occur in the
    body except A93's number variables). -/
def AnnProgram.Equiv : AnnProgram → AnnProgram → Prop
```

### Numbers, assignments, copy names

```lean
/-- The two closed types of Adm(number) (fig:static-core-admissible). -/
inductive Num where
  | int
  | float
  deriving DecidableEq, Repr, Inhabited

def Num.key : Num → String
  | .int => "Int"
  | .float => "Float"

/-- An assignment of Int or Float to the number variables of a declaration, in their
    canonical order (Choices, item 2). -/
abbrev Assignment := List Num

def Assignment.isDefault (a : Assignment) : Bool := a.all (· == .float)
def Assignment.key (a : Assignment) : String := "$".intercalate (a.map Num.key)
def Assignment.default (k : Nat) : Assignment := List.replicate k .float

/-- Lexicographic, Float before Int. On assignments of one length this is the string order of
    their keys, which is the translator's order (Specialise.elm, `List.sortBy`). -/
def Assignment.lt : Assignment → Assignment → Bool

/-- Default first, then by `Assignment.lt`; an insertion sort by structural recursion
    (`List.mergeSort` uses well-founded recursion, which the kernel does not reduce well). -/
def orderAssignments : List Assignment → List Assignment

/-- The variable a copy binds: x itself in the default copy, x$K1$...$Kk otherwise. `$` spells
    no identifier (syntax-core, identifiers), so copy names are new. -/
def copyName (x : Var) (a : Assignment) : Var :=
  if a.isDefault then x else x ++ "$" ++ a.key

/-- Every assignment of length k (2^k of them). -/
def allAssignments : Nat → List Assignment
  | 0 => [[]]
  | k + 1 => (allAssignments k).flatMap fun a => [.float :: a, .int :: a]
```

### The `number` variables of a group

```lean
/-- The type variables of a type in order of first occurrence (Choices, item 2): the arguments
    of a constructed type in order, the domain before the range, the fields of a record in label
    order (the row variable of an open record is not a type variable). Duplicates kept. -/
def Ty.tyVarsSeq : Ty → List TyVar

/-- Keep the first occurrence of each element; structural on the list. -/
def dedupFirst [DecidableEq α] : List α → List α

/-- What specialisation reads at a group node of an annotated phrase. -/
structure GroupView where
  /-- each member: its variable, the body of its scheme in VE (the monotype of an unannotated
      member, the annotation's type of an annotated one), its U' (empty when unannotated) -/
  members : List (Var × Ty × List TyVar)
  /-- the variables that Clos_C VE quantifies: tyvars σ \ tyvars C for each member, and A93's
      number variables of tyvars VE \ (tyvars σ ∪ tyvars C) (sec:static-core-closure); computed
      from C and VE, not read from a stored VE' (so that it is invariant under scheme equality) -/
  closed : List TyVar

def AnnValBind.view (C : Ctx) : AnnValBind → GroupView   -- from step 9's `groupNodes` (C, VE, U')

/-- The number variables of the declaration (sec:dynamic-core-numbers), canonical order. -/
def GroupView.numVars (g : GroupView) : List TyVar :=
  (dedupFirst (g.members.flatMap (·.2.1.tyVarsSeq))).filter fun α =>
    α.cls == .num && (g.closed.contains α || g.members.any (·.2.2.contains α))
```

### Resolution, scopes and occurrences

```lean
/-- The assignments of the copies that enclose a position, innermost first. -/
abbrev NumEnv := List (TyVar × Num)

/-- A type of Adm(number) read under ρ; a number variable that ρ does not assign is Float (the
    default of sec:dynamic-core-numbers, A27). `none` for any other type, which a derivation
    never gives an integer constant or a number variable's instance. -/
def resolve (ρ : NumEnv) : Ty → Option Num
  | .con [] t => if t = tInt then some .int else if t = tFloat then some .float else none
  | .var α => if α.cls = .num then some ((ρ.lookup α).getD .float) else none
  | _ => none

/-- What an occurrence of a variable refers to. `gid` identifies a group: its index in a
    pre-order numbering of all group nodes of the annotated program (modules in order), so that
    it is invariant under renaming. -/
inductive Ref where
  | plain                                                     -- lambda or pattern variable, constructor, basic value, group without number variables
  | group (gid : Nat) (V : List TyVar) (body : Ty) (boundHere : List TyVar)
  | basis (m : ModId) (V : List TyVar) (body : Ty)            -- an Elm text of the test basis in `basisCopies`

/-- Local binders, innermost first; names not found here are resolved through the module's own
    top level and then through `Stat.provider`. -/
structure Scope where
  locals : List (Var × Ref)
  top    : List (Var × Ref)                      -- the current module's top-level groups
  global : ModId × Var → Option Ref              -- top-level groups of earlier modules, and the basis table

inductive SpecError where
  | notANumber | unresolved (x : String) | recordPatternCopy (x : String)
  | missingBasisCopy (m : ModId) (x : Var) | copyFuel | portType | mainShape
  deriving DecidableEq, Repr

/-- The assignment an occurrence selects (Choices, items 3 and 5): v takes the instance's type
    when the scheme used here binds it and its body mentions it; Float when the scheme binds it
    and its body does not (A93); the enclosing copy's type when the scheme does not bind it. -/
def occAssignment (ρ : NumEnv) (V boundHere : List TyVar) (body : Ty)
    (inst : List (TyVar × Ty)) : Except SpecError Assignment :=
  V.mapM fun v =>
    if boundHere.contains v then
      if body.tyVarsSeq.contains v then
        match inst.lookup v >>= resolve ρ with
        | some n => pure n
        | none => throw .notANumber
      else pure .float
    else match resolve ρ (.var v) with
      | some n => pure n
      | none => throw .notANumber
```

For `Ref.group gid V body boundHere`, `boundHere` is `closed ∪ U'_x` restricted to `V` when the
occurrence is outside the group, and `U'_x ∩ V` inside it. An occurrence of `M.x` or `x` that
resolves to a `group` or `basis` reference at assignment `a` is printed `M.copyName x a`
(qualifier kept) or `copyName x a`, and makes the request `(gid, a)` (none for `basis`).

### Specialisation

```lean
abbrev Req := Nat × Assignment          -- a copy of group gid at an assignment

structure Spec (α : Type) where
  out  : α
  reqs : List Req                       -- requests for copies of groups bound outside the phrase

mutual
  def specAtExp  (ρ : NumEnv) (Γ : Scope) : AnnAtExp  → Except SpecError (Spec AtExp)
  def specExpRow (ρ : NumEnv) (Γ : Scope) : AnnExpRow → Except SpecError (Spec ExpRow)
  def specExp    (ρ : NumEnv) (Γ : Scope) : AnnExp    → Except SpecError (Spec Exp)
  def specMatch  (ρ : NumEnv) (Γ : Scope) : AnnMatch  → Except SpecError (Spec Match)
  def specMRule  (ρ : NumEnv) (Γ : Scope) : AnnMRule  → Except SpecError (Spec MRule)
  /-- The copy of one group at assignment a: its members as definitions, each binding
      `copyName x a` (a pattern binding renames the variables of its pattern; a record pattern,
      whose variables are spelt as labels, cannot be renamed: `recordPatternCopy` unless a is
      the default). -/
  def specGroupCopy (ρ : NumEnv) (Γ : Scope) (a : Assignment) : AnnValBind
      → Except SpecError (Spec (List D.Def))
end
```

Cases, by the annotated node (the target is the reduced syntax of `Syntax.lean`):

- integer constant at type `τ`: `.scon (.int n)` if `resolve ρ τ = some .int`, `.scon (.intF n)`
  if `some .float`, else `notANumber`. In a pattern the constant is always `.int n`
  (`r:s-atpat-scon`).
- floating-point, character, string constants: unchanged.
- variable or constructor occurrence: as above (`occAssignment`); constructors and operators
  are `Ref.plain` (only declarations of values are copied, A27 correction 2026-11-10; operators
  stand for basic values or for Elm texts without `number` variables).
- `let d in e`, with `g := d.view C`, `V := g.numVars`, `k := V.length`:
  1. `body ← specExp ρ Γout e`, where `Γout` binds each member `x` to
     `Ref.group gid V τ_x (V ∩ (g.closed ∪ U'_x))`;
  2. split `body.reqs` into those for `gid` and the others;
  3. `(made, out) ← copyLoop gid (fun a => specGroupCopy (V.zip a ++ ρ) Γin a d.vb)
     (2 ^ k + 1) (Assignment.default k :: mine.map (·.2)) [] others`, where `Γin` binds each member to
     `Ref.group gid V τ_x (V ∩ U'_x)`;
  4. the result is `A (letDefs ((orderAssignments (made.map (·.1))).flatMap (made.lookup ·)) body.out)`
     with requests `out`.
- every other node: componentwise, concatenating requests in the order of the node's children.

```lean
/-- The copies one group needs (sec:dynamic-core-numbers, "Copies are made from the outside
    in"): start from the default copy and the requests of the scope; translate each needed
    assignment once; requests of the copies on the group itself join the needed ones; the others
    are passed outwards. Each round makes at least one new copy of at most 2^k, so fuel 2^k + 1
    suffices (theorem `copyLoop_fuel`). Structural on fuel. -/
def copyLoop (gid : Nat) (tr : Assignment → Except SpecError (Spec (List D.Def))) :
    Nat → List Assignment → List (Assignment × List D.Def) → List Req →
    Except SpecError (List (Assignment × List D.Def) × List Req)
  | 0, _, _, _ => .error .copyFuel
  | fuel + 1, pending, made, out => do
    match dedupFirst (pending.filter fun a => !(made.any (·.1 == a))) with
    | [] => pure (made, out)
    | todo => do
      let rs ← todo.mapM fun a => do pure (a, ← tr a)
      let reqs := rs.flatMap (·.2.reqs)
      copyLoop gid tr fuel ((reqs.filter (·.1 == gid)).map (·.2))
        (made ++ rs.map fun (a, s) => (a, s.out)) (out ++ reqs.filter (·.1 != gid))
```

The structural recursion of the mutual block passes `fun a => specGroupCopy ... d.vb` (a call on
the subterm `d.vb` under a lambda) to `copyLoop`, which is defined before the block. If Lean
4.35's structural recursion checker refuses this, the block takes an explicit fuel argument (the
size of the annotated phrase, computed once), decreased at every call; the theorems are then
stated for fuel at least the size.

```lean
/-- A module: its top-level value groups processed last to first (Appendix A puts a group after
    every group it refers to), each by `copyLoop` with the requests of the later groups of the
    module and of the later modules (`incoming`); custom types, aliases and ports erased
    (`Erase.lean`); header and import items expanded. Returns the requests for earlier modules. -/
def specModule (Γg : ModId × Var → Option Ref) (incoming : List Req) (m : AnnModule) :
    Except SpecError (Mod.Module × List Req)

/-- The program: modules last to first, so that every request on module i is known before module
    i is specialised (a module imports only earlier modules, res:program-import-order). -/
def specProgram (a : AnnProgram) : Except SpecError (List Mod.Module)
```

### Exposing items

```lean
/-- The variables the copies of x bind in module m, default first (the order of emission). -/
def copiesOf (made : ModId → Var → List Assignment) (m : ModId) (x : Var) : List Var :=
  (orderAssignments (made m x)).map (copyName x)

/-- sec:dynamic-modules-reduced: an exposing item naming a copied top-level variable stands for
    the items naming the variable and each new variable of its copies; `(..)` is unchanged. Used
    for a module's header (its own copies) and for an import's items (the imported module's
    copies, and `basisCopies` for a basis module: `import Basics exposing (abs)` exposes `abs`
    and `abs$Int`). -/
def expandItems (copies : Var → List Var) : Src.BExpList → Mod.ExpList
```

### The basis table

```lean
/-- The values of the test basis written in Elm whose schemes quantify number variables, with
    those variables in canonical order: ("Basics", "abs") with one variable, and the core-library
    texts of D2 (List.sum, List.product, ...) as core-library.md binds them. -/
def basisCopies : List ((ModId × Var) × List TyVar)
```

### Erasure, payload types, `Dflt`, `main`

```lean
/-- fig:static-modules-port to Part I's payload types; `none` exactly when Port fails. Records
    are produced canonical (fields by label, step 4's PTy.Canon). -/
def toPTy : Ty → Option Eff.PTy

-- `dflt σ` is step 9's Dflt (programs.tex): Float for each bound type variable of class number.

/-- What r:p-stat-main-program and r:p-stat-main-view need of the scheme of main, as Part I
    records it: a worker with its flags type when σ's body is (τ1, τ2, τ3)Program with Port(τ1),
    taken before the default; a view when Dflt σ = τ Node. The flags type of a view is not read
    (step 5); it is `.unit` here and in the translator. -/
def mainKind (σ : Scheme) : Option (Mod.ProgKind × Eff.PTy) :=
  match σ.body with
  | .con [τ1, _, _] t => if t = tProgram then (toPTy τ1).map (.worker, ·) else none
  | _ => match dflt σ with
         | .con [_] t => if t = tNode then some (.view, .unit) else none
         | _ => none

/-- Custom types to their constructors with arities, record aliases to their labels in the order
    written, other aliases to their name; ports to (direction, payload type) from the module's
    port environment (r:sm-topdec-portout, r:sm-topdec-portin). The target constructors are
    step 3's. -/
def eraseTypeDecs : AnnTopDec → Except SpecError (List Mod.TopDec)

/-- The default of sec:dynamic-core-numbers as a function, for the book's two-phase reading:
    Float substituted for every number variable of the derivation bound neither by a closure, nor
    by an annotation's ∀U', nor as a parameter of a type declaration. -/
def defaultNum : AnnProgram → AnnProgram

/-- Specialisation and erasure of a whole program: the reduced modules (each built by
    `Mod.Module.ofSource` from its specialised items), the port environment of the program (the union of the modules' PE, as
    r:p-stat-module accumulates it), the flags type and the kind. -/
def reduceProgram (a : AnnProgram) : Except SpecError Mod.Reduced
```

### The pipeline, `SpecOf` and `r:p-program`

```lean
inductive E2EError where
  | infer (e : InferError) | check | spec (e : SpecError)
  deriving DecidableEq, Repr

/-- The bare program of a source program: step 8's derived forms of its canonical order (the
    program on which step 9 states legality). -/
def bareOf (s : Src.SProgram) : Src.BProgram := Src.deriveProgram (Src.canonOrder s)

/-- derive (total, step 8), infer, check, reduce. -/
def endToEnd (B : SBasis) (s : Src.SProgram) : Except E2EError Mod.Reduced := do
  let p := bareOf s
  let a ← (inferProgram B p).mapError .infer
  unless checkProgram B a && a.map AModule.erase == p.modules && checksAll B p a do throw .check
  (reduceProgram a).mapError .spec

/-- The specialisation of the program: what reduce gives on a principal program derivation. -/
def SpecOf (B : SBasis) (p : Src.BProgram) (r : Mod.Reduced) : Prop :=
  ∃ a, PrincipalProgDeriv B p a ∧ reduceProgram a = .ok r

/-- ⊢_DYN (r:p-dyn-module, r:p-dyn-main) on the reduced part of a program, in Part I's test
    basis. -/
def DynOf (r : Mod.Reduced) (v : Val) : Prop := Mod.EvalProgram Mod.Btest r.modules v

/-- r:p-program (programs.tex), in the reading of finding B1: the dynamic premise is about the
    specialisation of the program. -/
inductive ProgramSem (Bs : SBasis) : Src.BProgram → Ty × PortEnv × Val → Prop
  /-- r:p-program -/
  | r_p_program {p τ PE r v} :
      StatProgram Bs p (τ, PE) → SpecOf Bs p r → DynOf r v → ProgramSem Bs p (τ, PE, v)
```

`checksAll B p a` is the conjunction of the side conditions of `r:p-stat-*` (port names distinct
across modules and from the platform's managers `Src.managersPlat`, `mainKind` of the main
module's `main` defined); step 9's `checkProgram` checks the modules.

### Per-test generated declarations

For each test `X` = `<project>_<TestName>` that Part I translates, the translator writes, in
`Generated/EndToEnd<Shard><nn>.lean` (the shard of its program):

```lean
/-- tests/<project>/src/<TestName>.elm -/
theorem spec_X : Stat.endToEnd Stat.Btest s_X = .ok g_X.reduced := by decide +kernel  -- or native_decide

/-- The specialisation of the program is the reduced part of the translator's program. -/
theorem ident_X (h : Stat.D11For Stat.Btest (Stat.bareOf s_X)) :
    ∀ r, Stat.SpecOf Stat.Btest (Stat.bareOf s_X) r → r = g_X.reduced :=
  Stat.ident_of_spec h spec_X

/-- r:p-program with both premises, in the test basis. -/
theorem mean_X (h : Stat.D11For Stat.Btest (Stat.bareOf s_X)) :
    ∃ τ PE v, Stat.ProgramSem Stat.Btest (Stat.bareOf s_X) (τ, PE, v) :=
  Stat.programSem_of_spec h spec_X (Mod.value_of_viewChecks t_X)   -- Prog.value_of_holds for a worker
```

`ident_X` with Part I's congruence (`ViewChecks` reads only the modules; `Prog.workerExec_congr`)
turns every theorem Part I states about `g_X`, `t_X` among them, into a theorem about every
program whose reduced part is the specialisation of the program `s_X` denotes; that is what
retires `[elab]` for the test. A generic lemma `Stat.transfer` states it once:

```lean
theorem transfer {s q} {Φ : Mod.ModProgram → Prop} (hI : InferPrincipalFor Btest (bareOf s))
    (hΦ : ∀ q q', q.reduced = q'.reduced → (Φ q ↔ Φ q'))
    (h : endToEnd Btest s = .ok q.reduced) (hq : Φ q) :
    ∀ r, SpecOf Btest (bareOf s) r → ∀ q', q'.reduced = r → Φ q'
```

## Theorems

Each statement is in the file of its definitions unless said otherwise. Proof methods name the
lemmas in the order they are used.

### Copy names and the copy loop

```lean
theorem copyName_default (x : Var) (k : Nat) : copyName x (Assignment.default k) = x
theorem copyName_inj {x y : Var} {a b : Assignment} (ha : a.length = b.length) :
    copyName x a = copyName y b → x = y ∧ a = b
theorem allAssignments_length (k : Nat) : (allAssignments k).length = 2 ^ k
```

`copyName_inj` uses that Elm identifiers contain no `$` (Step 8's identifier predicate, or a
hypothesis `'$' ∉ x.toList` threaded from the source syntax) and that keys are `Int` or `Float`.
Method: `String` append injectivity on the prefix before the first `$` (lemmas on
`String.toList`, `List.append_inj`), then induction on the assignments.

```lean
/-- Termination of the loop within its fuel, and its result: the least set of assignments that
    contains the initial ones and is closed under the requests of the copies it contains. -/
theorem copyLoop_fuel {gid k tr init} (hk : ∀ a ∈ init, a.length = k)
    (htr : ∀ a s, a.length = k → tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2.length = k) :
    copyLoop gid tr (2 ^ k + 1) init [] [] ≠ .error .copyFuel ∨ ∃ a e, tr a = .error e

theorem copyLoop_least {gid k tr init made out}
    (h : copyLoop gid tr (2 ^ k + 1) init [] [] = .ok (made, out)) :
    (∀ a ∈ init, a ∈ made.map (·.1)) ∧
    (∀ a ∈ made.map (·.1), ∀ s, tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2 ∈ made.map (·.1)) ∧
    (∀ M : List Assignment, (∀ a ∈ init, a ∈ M) →
       (∀ a ∈ M, ∀ s, tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2 ∈ M) →
       ∀ a ∈ made.map (·.1), a ∈ M)

theorem copies_le_pow {gid k tr init made out}
    (h : copyLoop gid tr (2 ^ k + 1) init [] [] = .ok (made, out)) (hk : ...) :
    made.length ≤ 2 ^ k
```

`copyLoop_least` is the book's "one copy for each other assignment ... at which the program uses
the declaration", with "uses" read as: requested by the scope or by a copy already made, the
default copy always made (A59, A87). `copies_le_pow` is the book's finiteness remark ("at most
`2^k` copies, even when a binding is used recursively at an instance other than its own").
Method for all three: a loop invariant on `(pending, made)` (made assignments distinct, of length
`k`, each made one translated once, the union of made and pending closed under requests of made),
induction on fuel; the number of made assignments increases strictly in every round that does
not stop, and is bounded by `2 ^ k` (`allAssignments_length`, `List.Nodup` of `made.map (·.1)`).

### The variables of a group and the invariance lemma (finding B1)

```lean
theorem tyVarsSeq_rename {B r} (hr : r.WF B) (τ : Ty) :
    (r.ty τ).tyVarsSeq = τ.tyVarsSeq.map r.tvApply
theorem numVars_rename {B r} (hr : r.WF B) (C : Ctx) (vb : AnnValBind) :
    ((vb.rename r).view (r.ctx C)).numVars = (vb.view C).numVars.map r.tvApply
theorem resolve_rename {B r} (hr : r.WF B) (ρ : NumEnv) (τ : Ty) :
    resolve (ρ.map fun (α, n) => (r.tvApply α, n)) (r.ty τ) = resolve ρ τ
theorem toPTy_rename {B r} (hr : r.WF B) (τ : Ty) (h : Port τ) : toPTy (r.ty τ) = toPTy τ
theorem mainKind_rename {B r} (hr : r.WF B) (σ : Scheme) : mainKind (r.scheme σ) = mainKind σ

/-- The invariance lemma of finding B1. -/
theorem reduceProgram_rename {B : SBasis} {r : Renaming} (hr : r.WF B) (a : AnnProgram) :
    reduceProgram (a.rename r) = reduceProgram a

theorem reduceProgram_equiv {a a' : AnnProgram} (h : a.Equiv a') :
    reduceProgram a = reduceProgram a'
```

Method for `reduceProgram_rename`: generalise to the mutual statement

```lean
specExp (ρ.map (fun (α, n) => (r.tvApply α, n))) (Γ.rename r) (e.rename r) = specExp ρ Γ e
```

(and likewise for every function of the mutual block, `copyLoop` by a congruence lemma
`copyLoop_congr`: equal translation functions give equal results) by mutual structural induction
on the annotated phrase. Lemmas in order: `tyVarsSeq_rename` (a renaming maps variables to
variables and preserves label order, so first-occurrence order is preserved); `numVars_rename`
(the closed set is computed from `C` and `VE`, both renamed; class preserved by `r.WF`);
`resolve_rename` (`tInt`, `tFloat` are fixed by `r.tn`, which is the identity on `T of B`;
classes preserved); `occAssignment` congruence (from the three before; the instance list is
renamed pointwise); `copyName` does not mention variables, so names are equal; the group
identifiers `gid` are positions; `toPTy_rename` (a `Port` type has no variables and only type
names of the initial basis, Figure `fig:static-modules-port`, so `r` fixes it); `mainKind_rename`
(the same for the flags; `tProgram`, `tNode` fixed). Then module by module, the requests are equal
by the induction hypothesis. `reduceProgram_equiv` by the same induction: the result reads
schemes only through `GroupView.closed` (computed from `C` and `VE`, unchanged by scheme
equality), through `boundHere` (the same for equal schemes, since `numVars` keeps only variables
occurring in bodies) and through `inst` at variables that occur in the body (Choices, item 3).

```lean
/-- Mutual instances are renamings (step 11's L15, proved here because this step needs it first). -/
theorem mutualInstanceMod_renaming {B a a'} (hB : B.WF)
    (h1 : InstanceOfMod B a' a) (h2 : InstanceOfMod B a a') :
    ∃ r, r.WF B ∧ (AnnModule.rename r a).Equiv a'

/-- Two principal program derivations differ by a renaming, up to scheme equality. -/
theorem principalProg_rename {B p a a'} (hB : B.WF)
    (ha : PrincipalProgDeriv B p a) (ha' : PrincipalProgDeriv B p a') :
    ∃ r, r.WF B ∧ (a.rename r).Equiv a'

theorem reduce_principal_unique {B p a a'} (hB : B.WF)
    (ha : PrincipalProgDeriv B p a) (ha' : PrincipalProgDeriv B p a') :
    reduceProgram a = reduceProgram a'

theorem specOf_functional {B p r r'} (hB : B.WF) :
    SpecOf B p r → SpecOf B p r' → r = r'
```

No hypothesis is needed: two principal derivations are instances of each other by step 9's
definition (`principal_unique`; "any two principal derivations are instances of each other holds
by definition"), and existence is not used. Method for `mutualInstanceMod_renaming`: the
substitution `S` of one instance and `S'` of the other compose to the identity on the types at
the nodes (`S' (S τ) = τ` at every node, by step 9's `InstanceOf` clauses in both directions); so
`S` maps every variable occurring at a node to a variable (if `S α` were not a variable,
`S' (S α)` would not be one), injectively, of the same class (`S α ∈ Adm(cls α)` and
`S' (S α) ∈ Adm(cls (S α))` give `cls (S α) ≤ cls α` and the converse, by the variable case of
`Adm`), and every row variable to `⟨∅ | ε'⟩`; the schemes, each no more general than the other's
image, are equal up to the scheme equality of `sec:static-core-schemes`; the type-name
bijections of `InstanceOfMod` compose likewise. Method for `principalProg_rename`: induction on
the modules. Module 1: `principal_unique` and `mutualInstanceMod_renaming` give `r₁`. The bases
`B₂` and `r₁ B₂` then differ by `r₁`; equivariance of the checker (`checkModule_rename`:
renaming type names outside `T of B` and variables maps derivations to derivations, by induction
on the annotated module) and of `IsPrincipalMod` (`isPrincipalMod_rename`, from
`checkModule_rename` and the definition of `InstanceOfMod`) transport module 2's principal
derivation into `r₁ B₂`, where the same argument gives `r₂`; and so on. `reduce_principal_unique`
from `principalProg_rename`, `reduceProgram_rename`, `reduceProgram_equiv`. `specOf_functional`
from it.

### Defaulting (A27, A95)

```lean
theorem reduce_defaultNum (a : AnnProgram) : reduceProgram (defaultNum a) = reduceProgram a

/-- The book: "Float is substituted for it throughout the derivation, which remains a derivation
    for the program, since Float ∈ Adm(number)". -/
theorem a27_defaultNum_deriv {B p a} (hB : B.WF) (h : ProgDeriv B p a) :
    ProgDeriv B p (defaultNum a)
```

Method for `reduce_defaultNum`: `resolve` already maps every number variable not in `ρ` to Float;
the variables `defaultNum` replaces are exactly those no `ρ` ever contains (they are in no
`numVars`, being bound by no closure or annotation), so every `resolve` call returns the same
`Num`. Induction as for `reduceProgram_rename`. Method for `a27_defaultNum_deriv`: `check_subst`
(step 9) with `S = {Float/α ; α free in a, unbound, cls α = num}`: `S` respects classes
(`Float ∈ Adm(number)`, and `Adm` is monotone: the property of `sec:static-core-types`), is
defined (no row variable is replaced), moves no variable of any `U` (explicit variables are bound
by their annotation) and none of the root context (a module's context has no free type
variables); at every group node the closure is unchanged, since a variable free in `VE` and not in
`C` would be closed and so bound.

### Payload types, `main`, the basis table

```lean
theorem toPTy_isSome_iff (τ : Ty) : (toPTy τ).isSome ↔ Port τ
theorem toPTy_canon {τ π} : toPTy τ = some π → π.Canon
theorem mainKind_worker_iff (σ : Scheme) (π : Eff.PTy) :
    mainKind σ = some (.worker, π) ↔
      ∃ τ1 τ2 τ3, σ.body = .con [τ1, τ2, τ3] tProgram ∧ Port τ1 ∧ toPTy τ1 = some π
theorem mainKind_view_iff (σ : Scheme) (π : Eff.PTy) :
    mainKind σ = some (.view, π) ↔ π = .unit ∧
      (¬ ∃ τ1 τ2 τ3, σ.body = .con [τ1, τ2, τ3] tProgram) ∧ ∃ τ, dflt σ = .con [τ] tNode
theorem basisCopies_complete :
    ∀ m x σ, Mod.Btest.isElmText m x → Stat.Btest.scheme? m x = some σ →
      (σ.bound.any (·.cls == .num)) → (m, x) ∈ basisCopies.map (·.1)
theorem basisCopies_bound :
    ∀ e ∈ basisCopies, ∀ a ∈ allAssignments e.2.length, Mod.Btest.binds e.1.1 (copyName e.1.2 a)
```

Methods: `toPTy_isSome_iff` by induction on `τ` against the clauses of Figure
`fig:static-modules-port` (each clause one case; the record case by induction on the row).
`toPTy_canon`: step 9's rows are sorted by label (if not, `toPTy` applies `PTy.normalise` and the
lemma is `PTy.normalise_canon` of step 4). The two `mainKind` lemmas by unfolding. The last two by
`decide +kernel` over the literal bases (`isElmText` is Part I's predicate that a basis value is
the value of an Elm text; added to `Stat/EndToEnd.lean` as a list of `(ModId, Var)` checked
against `elmTexts` and the core-library texts if Part I has none).

The second sentence of the property of `sec:effects-ports` ("every value that elaboration admits
as a payload of type τ has an encoding"), which [step 4](step-04-effects.md) defers to this step,
is not proved here: it needs a typing of values and type preservation for Chapters 6 to 8. See
Issues, item 7.

### The pipeline

```lean
theorem specOf_of_endToEnd {B s r} (hB : B.WF) (hI : InferPrincipalFor B (bareOf s))
    (h : endToEnd B s = .ok r) : SpecOf B (bareOf s) r

theorem statProgram_of_endToEnd {B s r} (hB : B.WF) (hI : InferPrincipalFor B (bareOf s))
    (h : endToEnd B s = .ok r) : ∃ τ PE, StatProgram B (bareOf s) (τ, PE)

theorem ident_of_spec {s q} (hI : InferPrincipalFor Btest (bareOf s))
    (h : endToEnd Btest s = .ok q.reduced) :
    ∀ r, SpecOf Btest (bareOf s) r → r = q.reduced

theorem programSem_of_spec {s q} (hI : InferPrincipalFor Btest (bareOf s))
    (h : endToEnd Btest s = .ok q.reduced) (hv : ∃ v, Mod.EvalProgram Mod.Btest q.modules v) :
    ∃ τ PE v, ProgramSem Btest (bareOf s) (τ, PE, v)
```

Methods. `specOf_of_endToEnd`: unfold `endToEnd`; step 9's checker soundness gives `ProgDeriv`;
`hI` gives `PrincipalProgDeriv`; `SpecOf` by its definition. `statProgram_of_endToEnd`: from the
same principal program derivation build the `r:p-stat-*` derivation module by module (step 9's
`StatProgram` constructors), the side conditions taken from `checksAll`, `Port`/`Node` from
`mainKind_worker_iff`/`mainKind_view_iff`. `ident_of_spec`: `specOf_of_endToEnd` and
`specOf_functional`. `programSem_of_spec`: `r_p_program` with `statProgram_of_endToEnd`,
`specOf_of_endToEnd` and `DynOf` from `hv`. `transfer`: `ident_of_spec`, then `hΦ`.
`Stat.Btest_wf : Stat.Btest.WF` by `decide +kernel` (once, in `Stat/EndToEnd.lean`).

### Independence of the grouping (finding B4, for evaluation)

Step 8 leaves the statement to this step (its section 3.3). It is stated as a proposition, so that
no theorem rests on an unproved lemma; theorems are about the canonical grouping until it is
proved (plan, B4).

```lean
/-- Any two derivations of a source program by Appendix A with valid numberings (step 8's
    `DerivesTo`, lifted to programs) have the same specialisation, up to the order of independent
    groups, and the same values. -/
def GroupingIndependent : Prop :=
  ∀ (s : Src.SProgram) (p p' : Src.BProgram), Src.SynOK s →
    Src.DerivesToP s p → Src.DerivesToP s p' →
    ∀ r r', SpecOf Btest p r → SpecOf Btest p' r' →
      ∀ v, DynOf r v ↔ DynOf r' v
```

Proof method, when it is taken up (stretch goal of this step, otherwise a later step): step 9's
independence for elaboration (`Stat/Independence.lean`) maps principal derivations of `p` to
principal derivations of `p'` node by node; specialisation commutes with that map (the copies of a
group depend only on the group and on the requests made of it, not on the position of independent
groups); evaluation of two `let` nests that differ by swapping independent adjacent groups gives
the same value (Chapter 6 has neither state nor exceptions, A57, A58), by induction on the nest
with step 1's evaluator completeness.

### Rulings, on small programs (`Stat/SpecExamples.lean`)

Each is a theorem by `decide +kernel` that `reduceProgram` of the annotated program that step 9's
inference gives for a literal source program equals a literal reduced program. Names carry the
ruling (conventions, "Rulings").

| Theorem | Program | What it shows |
|---------|---------|---------------|
| `a27_float_default` | `main = text (Debug.toString (2 ^ -1))` | both constants `.intF` (the free `number` is Float) |
| `a27_annotation_bound` | `f : number -> number`, `f x = let g y = y + x in g 1`, `main` using `f 2 // 1` | copies `f` and `f$Int`; inside `f$Int` the constant `1` of `g` is `.int`: the `number` of `x` is bound by `f`'s annotation, not defaulted (dynamic-core, the `f`/`g` example) |
| `a87_default_copy_made` | `check h = if h == 0 then h else Debug.todo "h"`, `x = check (2 ^ -1)`, used only as `x // 2` | both `x` and `x$Int` emitted, the default copy although unused (the book's example) |
| `a87_vacuous_inner` | `if 2 ^ -1 == 0 then 1 else 2` bound by `y` used at Int | the inner constants Float in every copy of `y` (not a variable of the declaration) |
| `a93_mutual` | A93's example (`f`, `g`, `main`) | `f 3` refers to `f`; no copy of the group at `b = Int`; `f` and `g` default copies only |
| `a93_vacuous_witness` | A93's example with the instance of the vacuous variable at `f 3` set to `Int` by hand in the annotated phrase | the same result: the witness is ignored (Choices, item 3) |
| `spec_polyrec` | `f : number -> Int -> Float`, `f x n = if n <= 0 then 0.5 else f 1.5 (n - 1)`, used at `Int` | `f$Int` requests `f`; both emitted, in that order after regrouping |
| `spec_two_vars_order` | a group whose two `number` variables occur in the order `b`, `a` in its body, used at `b = Int, a = Float` | the copy is named `r$Int$Float` (first occurrence order) |
| `spec_basis_abs` | `abs (3 // -1)`, `Basics.abs 2`, `import Basics exposing (abs)` | `abs$Int` (twice) and `Basics.abs$Int`; the import item expands to `abs, abs$Int` |
| `spec_exposing` | module `A exposing (f)` with `f : number -> number`, module `B` imports `A exposing (f)` and uses `f` at Int | `A`'s header items `f, f$Int`; `B`'s import items `f, f$Int`; `A` gets `f$Int` from `B`'s request |
| `spec_port_payload` | `type alias P = { name : String, id : Int }`, `port send : List P -> Cmd msg` | `(out, list (record [("id", int), ("name", string)]))` |
| `spec_main_kinds` | a view `main`; a worker with flags `()`; one with flags `Int` by annotation | `(view, unit)`, `(worker, unit)`, `(worker, int)` |
| `spec_copy_bound` | a declaration with three `number` variables used at all eight assignments | eight copies, default first |
| `spec_rename_invariant` | the annotated program of `spec_exposing`, renamed by a concrete `r` | equal reductions (an instance of `reduceProgram_rename`) |
| `spec_record_pattern_copy` | `let { x } = { x = 1 } in x // 2` | `.error (.recordPatternCopy "x")` (Issues, item 4) |

## Translator changes

1. **Canonical order of a group's `number` variables** (`Translate/Infer.elm`, `generalise`):
   `groupNumbers` is computed in first-occurrence order over the members' types in group order
   (each type read as `Ty.tyVarsSeq` reads it: constructor arguments in order, domain before
   range, record fields in label order, which is `Dict`'s order), instead of `Set.toList` on the
   variables' numbers. `Specialise.elm`'s `key` and `copyName` already follow the order of
   `groupVars`. Expected to rename copies in the three tests with two-variable copies today:
   CaseNestedRecordAccessTest (`pos$Int$Int`), LetNumberFracRecordTest (`r$Int$Float`, the only
   mixed one) and PapEtaCtorProbe (`init$Int$Int$Int$Int`); the other two keep their names
   (all components equal).
2. **An occurrence inside its own group** (`Specialise.elm`, `occurrence`): a variable of the
   group that the occurrence's instance does not bind takes the enclosing copy's assignment
   (`Dict.get v ctx.rho`) before the default, as Choices, item 5 requires. Today it takes Float,
   which differs from the book when an annotated member of a group with an unannotated member is
   used recursively inside a copy at Int. No translated test is expected to change; the report
   says which do.
3. **The flags type of a view.** The translator writes `flagsType := .unit` for every program
   of kind `view` (step 5 reads `flagsType` only for workers), so that `g_X.reduced` is
   determined; `mainKind` gives the same.
4. **The end-to-end files.** For each translated test, the translator writes the three theorems
   of "Per-test generated declarations" into `Generated/EndToEnd<Shard><nn>.lean`, with
   `decide +kernel` or `native_decide` as the manifest says (item 5), and `Generated/All.lean`
   imports them. `--check` covers the new files.
5. **The manifest** gains, per translated test, `endToEnd`: `"kernel"`, `"native"` or
   `"none"`, and `endToEndReason` when `"none"` (`"differs"`, `"budget"`, `"infer"`, ...). The
   value is read from a hand-maintained table `Translate/EndToEndMethod.elm` (default `"kernel"`),
   filled by the measurement of Acceptance, item 3.
6. **Unit tests** (`definition/tools/tests`): the first-occurrence order on a group of two
   bindings whose variables occur in opposite orders; the in-group occurrence of item 2; the
   printing of an `EndToEnd` shard for one program.
7. **The site** (`runner/mechanisation-data.js`): the trust tags of a test page are computed from
   the manifest: `[elab]` is shown when `endToEnd` is `"none"`, `[principal]` when it is not,
   `[native]` when `endToEnd` is `"native"` or a check theorem is native. The rule page of
   `r:p-program` links to `r_p_program`.

## Tests gained

No test is newly translated: the step changes what the theorems of the translated tests rest on.
For every test Part I translates when this step lands (491 today plus Part I's gains, up to 87:
at most 578), the three theorems `spec_`, `ident_` and `mean_`, except the tests listed in the
report with `endToEnd: "none"` and a reason. Expected exceptions: none from specialisation
(today's translator specialises every translated test); possibly some from the budget (moved to
`native_decide`, not to `"none"`) and any where Lean and the translator disagree, each resolved
before acceptance by fixing one of them or recorded as a finding about the book.

Plus the rulings theorems of `Stat/SpecExamples.lean` (15 examples), the general theorems above,
and the `r:p-program` constructor (rule page link).

Tests to watch, because they exercise specialisation: the `LetNumber*` tests (52 files),
StandardA93MutualNumberDefaultTest, AccessorPlaceholderAccessorOfAFunctionFieldPassedInTailCallsTest
(`inner$Int`), DebugNumberAtFloatTest, the three tests of Translator changes, item 1, and every
test whose program uses `abs` at Int.

## Acceptance

Run the commands of [conventions.md](conventions.md), "Acceptance commands", in order. Expected:

1. The translator writes the new `EndToEnd` shards; `--check` prints `Lean translations are up
   to date.`; the elm-test suite passes with the new unit tests.
2. `lake build` with no `sorry`, no new warnings; `lake exe run-examples` prints its line with
   `N` checks and `K` kernel theorems unchanged from before the step, and a second line:

   ```
   End to end: T programs; T agree with Lean's elaboration (Ek by decide +kernel, En by native_decide); 0 differ.
   ```

   with `T` the number of translated tests, `Ek + En = T` less the `"none"` entries of the
   manifest, each listed in the report. (`run-examples` counts the `spec_` theorems of the
   generated files and reads the manifest; it re-runs nothing.)
3. **Measurement first (F-15).** Before the translator writes every shard, one shard of each
   project is written and measured: `ElmCore03` (typical) and `Elm01` (which holds
   AppendTypeSplitTest, the heaviest check). For each, `/usr/bin/time -v lake env lean
   Generated/EndToEndElmCore03.lean` (maximum resident set size, wall time), and the same per
   theorem (one theorem per scratch file, as the feasibility review measured `#kernel_checks`).
   Decision rule, recorded in the report with the figures:
   - every theorem under 6.5 GB and the shard file under three times the wall time of the same
     shard's `Checks` file: `decide +kernel` for all, and the other shards are written;
   - otherwise the theorems over the budget are `native_decide` (listed); if more than a quarter
     of a shard would be native, the fallback of Risks, "Kernel cost", item 2 (certificates) is
     taken before writing the other shards.
4. `lake env lean scripts/check-axioms.lean`: every `spec_` theorem uses only `propext`,
   `Classical.choice`, `Quot.sound`, and, for those marked native, the axioms of `native_decide`.
   `ident_` and `mean_` use nothing more than their premises.
5. Memory budget of the conventions on a clean build: no `lean` process above 6.5 GB, aggregate
   PSS under 12 GB.
6. `pnpm test:all` and `node runner/check-baseline.js` unchanged.
7. Site data rebuilt, site built, link audit at 0 problems; the test pages show the tags of
   Translator changes, item 7; the rule page of `r:p-program` links to `r_p_program`.
8. Reports: the mechanisation report gets a dated "Step 10" block (counts: translated of 939,
   checks, kernel and native theorems, `T`, `Ek`, `En`, the measurement of item 3, the tests whose
   copy names changed); the README's trust section marks `[elab]` retired (with the date and the
   tests still marked); the plan's trust table, row `[elab]`, says "retired by step 10 for the
   tests with an end-to-end theorem"; the preface sentence names what is encoded; the plan's
   status line and this file's status are updated.

### Trust tags, page by page, after this step

| Page | Before | After |
|------|--------|-------|
| a translated compile-success test with `endToEnd` kernel | `[parse]` `[elab]` `[harness]` `[params]` (`[native]` if a check is native) | `[parse]` `[harness]` `[principal]` `[params]` (`[native]` if a check is native) |
| the same with `endToEnd` native | as above | as above, with `[native]` |
| a translated test with `endToEnd` none | unchanged | unchanged (`[elab]` kept), listed in the report |
| a compile-error test | unchanged by this step | unchanged |
| the rule page of `r:p-program` | no constructor | links `r_p_program`; its theorems carry `[principal]` |
| the mechanisation report and README trust table | `[elab]` until step 10 | `[elab]` retired, with the list of exceptions; `[principal]` until step 11 |

`[parse]`, `[harness]` and `[params]` are unchanged by this step (P2-15: the harness basis stays
an assumption).

## Risks and fallbacks

- **Kernel cost (F-15).** Inference with rows and classes inside `decide +kernel` for about 578
  programs may break the memory budget or take hours. Fallbacks, in order: (1) `native_decide`
  for the theorems over the budget, marked `[native]`; (2) *certificates*, as step 9 already
  writes them (`lake exe certify`, `Certs/`, `a_X`; step 9, "Issues with the plan", item 6):
  `spec_X` becomes `checkAndReduce Stat.Btest (Stat.bareOf s_X) a_X = .ok g_X.reduced` by
  `decide +kernel` (the kernel runs only the checker and the specialisation), and the link that
  `InferPrincipalFor` needs, `inferProgram Stat.Btest (Stat.bareOf s_X) = .ok a_X`, by
  `native_decide`; or, keeping the kernel only, the hypothesis is restated about the certificate
  (`PrincipalProgDeriv Btest p a_X`), which step 11 discharges by comparing `a_X` with its proved
  inference; (3) `native_decide` for everything. Each fallback keeps the statements of `ident_X`
  and `mean_X`.
- **Grouping.** Both sides group through `Src.Grouping.components` (step 8), so the order of
  independent groups agrees provided the copies are listed in the same order before grouping.
  Lean lists them group by group in the bare program's order, the translator in its own
  component order (`Infer.components`); both are the least-member-first order of the source
  definitions, and copies of a later group never come before those of an earlier one, so the
  flat lists group identically (the components of copies of one group are placed before any
  later group's because their least members are smaller). If a difference appears all the same,
  the fallback is to compare under a normal form that sorts independent adjacent groups
  (`Mod.normaliseGroups`), whose preservation of evaluation is `GroupingIndependent`'s dynamic
  half.
- **Lean and the translator disagree.** Each difference is triaged: a translator error (fixed in
  the translator, its unit test added), an error of Lean's inference (fixed in step 9's inference),
  or a question about the book (an entry for the ambiguity log, and the test marked `"none"` with
  reason `"differs"` until it is settled). Expected sources: the in-group occurrence rule
  (Translator changes, item 2), the order of variables, `Infer.elm`'s left-biased row union
  (`Types.elm`, A23).
- **Part I's formats change.** The comparison is through `Mod.ModProgram.reduced`, so changes to the
  written form that keep the reduced program do not break it.
- **Structural recursion.** If the mutual block with `copyLoop` under a lambda is refused, the
  explicit-fuel version (Lean definitions, "Specialisation") is used.
- **Library copies.** If D2's core-library modules do not bind the `$Int` copies of their
  `number` texts, every test that uses one at Int fails `spec_` (`missingBasisCopy`). Fallback:
  this step adds the copies to `Mod.Btest` (each a copy of an Elm text, evaluated as the default
  copy is, as Appendix D does for `abs`).

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **D11's hypothesis is false globally and insufficient for these theorems.** D11 states the
   positive theorems of steps 9 and 10 "under the hypothesis `PrincipalExists` (the two
   properties of the book, stated in Lean)". Two problems. (a) [Step 9](step-09-static-semantics.md)
   ("Issues with the plan", item 1) shows that the module property is false as the book stands
   (`r:sm-topdec-seq` splitting a type-declaration phrase gives a second, incomparable
   derivation when a custom type mentions a later local alias spelt like an imported type), so a
   theorem under the global `PrincipalExists` would be vacuous. Step 9 uses its instance
   `PrincipalExistsFor p` at the program's own modules, but that still quantifies over every
   basis, and a contrived basis whose `Basics` exposes a type named like a local alias that a
   custom type of the module mentions (an ordinary pattern: `type Msg = Got Model` with
   `type alias Model = ...`) makes the same split derivation possible; so `PrincipalExistsFor p`
   is false for many ordinary programs, and this step does not assume it. (b) Existence and
   uniqueness say nothing about the derivation that step 9's unverified inference returns, while
   `SpecOf` and `r:p-stat-*` need the principal derivation itself (its scheme of `main`, its
   interfaces, its instances): from them and a merely sound inference neither "the specialisation
   of the program is `g_X.reduced`" nor `StatProgram` follows (a non-principal derivation may fix
   the flags of `main`, the book's example after `r:p-stat-main-view`, or a `number` variable).
   This specification therefore states the per-test theorems under
   `D11For Btest p := InferPrincipalFor Btest p`: in the test basis and the bases built from it,
   the inference returns principal derivations of this program. It implies the existence part of
   D11 exactly where the theorems use it, it is true for every program whose modules have
   principal derivations in those bases (step 11 proves it for them), and it is false only where
   the book gives the program no principal derivation. The trust table's `[principal]` row should
   read "principal derivations exist for the program in the test basis, and the inference finds
   them". Followed meanwhile: D11's hypothesis in this per-program, per-basis form.
2. **"The order of modules" is not fully retired.** The trust table lists the order of modules
   among the things `[elab]` covers until step 10. After this step the order is Lean's (step 8's
   `canonOrder`, a topological order of the imports with ties by name, shown valid by step 8's
   `synOKSet_iff`), and the translator writes the same order, but the property that every valid
   order has the same meaning (`programs.tex`, the property after `r:p-program`) is proved by no
   step of the plan. The theorems hold for the canonical order. Either a step takes the property (its static half
   needs principality, so step 11; its dynamic half is Part I's), or the trust table says that the
   theorems are about one valid order.
3. **The book does not say how copies stand in the bare syntax** (for the ambiguity log, with
   finding B1). `sec:dynamic-core-numbers` says each declaration "is replaced by" its copies, but
   the bare syntax has one `dec` per `let` and a copy can refer to another copy of its group, so
   no fixed nesting works in general. Read here as: the copies' definitions regrouped by Appendix
   A (Choices, item 4). The book should say so.
4. **A record-pattern binding cannot be copied** (for the ambiguity log). A pattern binding
   `{ x } = e` of a `let` whose group quantifies a `number` variable used at Int needs a copy
   binding "distinct new variables", but a record pattern binds only the variable spelt as its
   label (`r:s-patrow`), so the copy cannot be written. The translator refuses it today; Lean's
   specialisation returns `recordPatternCopy`. The book should allow a copy to bind the label's
   variable under a new name (a new form of pattern row) or exempt such bindings.
5. **The instance of an A93 vacuous variable is not part of a derivation** (for the ambiguity
   log, with A93). `sec:dynamic-core-numbers` refers each occurrence to "the copy for the instance
   at which that occurrence was elaborated", but a vacuous bound variable's image is a witness
   of a side condition, not a type in a sentence, so principal derivations do not determine it.
   The book's next sentence ("a variable that nothing at the occurrence fixes is Float") gives the
   reading used here (Choices, item 3); the book should say that it applies to every variable the
   occurrence's type does not mention.
6. **The dynamic test basis must bind copies of library texts.** D2(b) makes the core library's
   Elm texts entries of `B_test`, but neither D2 nor [core-library.md](../core-library.md) says
   that those whose schemes quantify `number` (`List.sum`, `List.product`, ...) are bound with
   their copies at Int, as Appendix D binds `abs$Int`. Without them a program that uses
   `List.sum` at Int has no reduced program. This step requires them (Prerequisites) and adds
   them if step 2 has not.
7. **Step 4 defers to this step a property this step cannot prove.** [Step 4](step-04-effects.md)
   ("Partial functions") says that "step 10 connects" the dynamic predicate `HasPTy` to
   elaboration, for the property of `sec:effects-ports` that every value elaboration admits as a
   payload has an encoding. That connection is type soundness (a value of an expression
   elaborated at `τ` with `Port τ` satisfies `HasPTy (toPTy τ)`), for Chapters 6 to 8; the plan
   gives it to no step and its size is that of a step. This step proves only the static half
   (`toPTy_isSome_iff`); the property stays stated with `HasPTy` as a hypothesis until a step is
   assigned to type soundness.
8. **Choices, item 5 must be limited to occurrences inside the group** (found 2026-11-12, while
   proving the invariance lemma; `Stat/RenameCounterexample.lean`). As first written, an occurrence
   *outside* its group of a member whose scheme does not bind one of the group's `number` variables
   (A93: `g = f 1 == f 2` in a group with `f : number -> number`) took that variable from the
   enclosing copy's assignment. Annotation variables are named (every annotation's `number` is the
   same variable), so an enclosing declaration can have the same variable, and the result then
   depends on the derivation: two principal derivations of one program, differing by a renaming,
   gave different reduced programs, so `reduce_principal_unique` was false. Fixed in Lean
   (`Member.bOutAll`: outside its group every variable of the declaration is bound at the
   occurrence, so one the member's scheme does not mention is Float, as Choices, item 3 and the
   book's "a variable that nothing at the occurrence fixes is Float" say) and in the translator
   (`Specialise.elm`, `declared`); no translated test changes. Two further statements of this
   specification are false as stated and must change before the invariance lemma is proved:
   `Renaming.WF` cannot fix named variables (the renaming relating two principal derivations may
   move one), and the checker admits free `bnd` variables, which the renaming argument cannot move
   (step 9's checker should reject a `bnd` variable free at a node, as the comment in
   `Stat/Objects.lean` already assumes). `principalProg_rename` needs one renaming per module, with
   one bijection of generated type names across modules; `AnnProgram.Equiv` must ignore the order
   of each U' and the instances at constructor patterns.
9. **Incoherent modules make `ident_` false as the definitions stand** (found 2026-11-12;
   `Stat/SplitCounterexample.lean`, by the kernel). Module `M1` with `type T = T String` and
   `type alias String = Int` has two derivations: the whole type declaration (`T : Int -> T`, the
   inference's) and a split one (`typesSplit`, rule `r_sm_topdec_seq_types`: the custom type first,
   in the basis, so `T : String -> T`). Each is an instance of the other by step 9's `InstanceOfMod`,
   because nodes are compared at equal paths and the split's nodes are at other paths than the
   whole's; so both are principal, and a later module whose `main` reads the constructor gets flags
   Int with one and String with the other (`ce_differ`). This is finding B6 reaching the program
   level. Repairs, each a change to step 9's definitions: (a) give a `typesSplit` node, at its own
   path, the environment it gives, so the two shapes are compared and an incoherent module has no
   principal derivation (what step 11 already assumes); (b) have the checker refuse a split whose
   environment differs from the whole phrase's; (c) drop `typesSplit` from the checker. A second
   risk: `checkTypes` checks a fixed point, so a recursive alias admits many solutions (some with
   junk type names); solving the type declarations in order, as the inference does, would remove it.
   Decision needed before the invariance lemma is finished.
