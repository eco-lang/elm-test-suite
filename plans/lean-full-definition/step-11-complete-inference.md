# Step 11: complete inference and principality

Part of [the plan](../lean-full-definition.md), Part II. Follows [conventions.md](conventions.md).
Status: specified 2026-11-11, not started. Research-sized (plan, "Order of work"): delivered in
milestones, each with its own deliverable, tests and acceptance.

## Goal

Steps 9 and 10 prove that a program elaborates by exhibiting a derivation that a proved checker
accepts, and state legality, number specialisation and `r:p-program` under the hypothesis of
decision D11 that principal derivations exist (and, see [step 10](step-10-end-to-end.md),
"Issues with the plan", item 1, that the inference finds them). Two things remain:

1. **Refusals.** About two hundred compile-error tests are refused by the book because *no*
   derivation exists. A certificate cannot show that; a statement about every derivation is
   needed (step 7's classes `inference`, 216 provisionally, and `fixity-inference`, 1).
2. **Principality.** The book's properties of `sec:static-core-principal` and
   `sec:static-modules-principal` ("every phrase that elaborates has a principal derivation, and
   any two differ only by a renaming"), which the book states without proof, and on which the
   meaning of every program depends (A95, A96; findings B1, B3, B5).

Step 11 writes an inference algorithm in Lean designed for proof (Damas and Milner's algorithm W,
extended with classes, rows with lacks constraints, rigid explicit variables, A93's closure,
modules and their type declarations), proves it sound, complete and principal, and uses it:

- as a refutation procedure for the `inference` and `fixity-inference` tests (its failure shows
  that no derivation exists);
- to discharge D11: the Core's property (`PrincipalExistsCore`) and, for every module that is
  *coherent* (section 9), the module property become theorems; so does step 10's per-program
  hypothesis `D11For Btest p` for every coherent test program; the hypotheses are removed from
  the theorems of steps 9 and 10 for those programs, and `[principal]` is retired. (The book's
  module property is false for incoherent modules, as step 9 found; see "Issues with the plan".)
- for Chapter 9's refusal that only the principal derivation decides: an unannotated `main` whose
  flags type is a variable (A96, StandardA96NumberFlagsTest).

## Prerequisites

- **[Step 9](step-09-static-semantics.md)** (everything below that says `Stat.`): the static
  objects (`TyVar`, `RowVar`, `BVar`, `Cls`, `Ty`, `Scheme`, `Ctx`, `SBasis`, `Subst` with
  `Respects` and `DefinedOn`, `Gen` for `≻`, `Adm`), the `Prop` relations `ElExp`, ...,
  `ElModule`, `ElProgram` of Chapters 4, 5 and 9, annotated phrases `AExp`, ..., `AModule`,
  `AProgram`, the checker `checkExp`, `checkModule`, `checkProgram` with soundness and adequacy,
  the nodes `nodesExp`, `nodesModule`, `InstanceOf C0 a' a` (`a'` an instance of `a`),
  `IsPrincipal`, `InstanceOfMod`, `IsPrincipalMod`, `principal_unique`, `PrincipalExistsCore`,
  `PrincipalExistsMod`, `PrincipalExists`, `PrincipalExistsFor`, `LegalProgram`, the test basis
  `Btest`, the deterministic elaboration of type expressions, imports, exposing lists and headers
  (`Stat/Deterministic.lean`), `check_subst`, the certificates `a_<project>_<TestName>` and the
  conditional theorems `legal_<project>_<TestName>`, and the refusal theorems
  `refuse_<project>_<TestName>` of the classes it proves. Step 9's own inference
  (`Stat/Unify.lean`, `Stat/Infer.lean`) is not proved; this step writes another, for proof.
- **Step 8**: `Src.SProgram`, `Src.BProgram` and the bare phrase types, `Src.deriveProgram`,
  `s_<project>_<TestName>`, `Src.SynOK`.
- **Step 7**: `definition/mechanisation/static-classification.json` with the classes
  `inference` and `fixity-inference`, and the override table `Translate/ClassifyOverrides.elm`.
  This step adds a field `fragment` to the entries of those two classes (Translator changes,
  item 1).
- **[Step 10](step-10-end-to-end.md)**, for milestone (g) only: `InferPrincipalFor`, `D11For`,
  `bareOf`, `endToEnd`, the generated `spec_`, `ident_`, `mean_` theorems,
  `mutualInstanceMod_renaming`, `principalProg_rename`.

Names: everything new is in `StandardElmMech/Stat/Complete/`, namespace
`StandardElm.Stat.Complete`, importing no `Lean`. Where a name of step 9 differs from the one
used here, step 9's wins and this file is corrected.

## Milestones

Each milestone ends with a green build (no `sorry`), its theorems, its per-test refusals and its
own entry in the mechanisation report. A milestone's theorems may carry *fragment hypotheses*
(`InFragment f p`) that a later milestone removes; no theorem carries `sorry` or an axiom.
Counts of compile-error tests are estimates from a scan of the sources (2026-11-11; heuristics
for literals, operators, records, annotations, imports) and are replaced by the milestone's
measured numbers, computed by the selection rules of "Tests gained".

| Milestone | Deliverable | Compile-error tests it proves (estimate) | Size |
|-----------|-------------|-------------------------------------------|------|
| (a) cores | unification over the full type language (classes, rows, rigid variables) with its *refutation* theorem; a weak constraint generator `coreGen` for a module, proved complete for derivations (every derivation solves its constraints); per-test refusals where `unify (coreGen ...)` fails | about 160 of the 217 (lower-bound scan: 170 of 221 type-error tests use no unannotated binding outside its own definition, for which `coreGen` is exact); unconditional: no principality needed | large |
| (b) HM | substitution algebra; the mgu theorem (factorisation) without classes or rows; algorithm W with let-polymorphism, monomorphic annotations; soundness; completeness and principality for fragment F_b | fragment F_b: about 9 in all, about 1 beyond (a) | large |
| (c) classes | meets, the class-propagation table per type name, rigid variables in unification; W for F_c (classes, top-level annotations with variables) | F_c: about 115 in all, about 25 beyond (a) | medium |
| (d) rows | row unification with lacks sets (Rémy-style, derived from the object), occurs check through rows, A23; W for F_d (records, rows, updates, record patterns) | F_d: about 155 in all, about 10 beyond (a) and (c) | large |
| (e) annotations and closure | nested annotations (A21's scoping, A20's escape check), annotated members inside groups, A93's closure; W for F_e (every single-module program) | F_e: about 215 in all, about 13 beyond | large |
| (f) modules | type declarations (`r:sm-topdec-types` fixed point, B5), ports, generated type names, principality up to type-name bijection for coherent modules (section 9: node correspondence with `r:sm-topdec-seq`); programs of several modules | all 217 `inference`/`fixity-inference` but the one of (g): about 2 beyond | large |
| (g) discharge | `PrincipalExistsCore` proved; the module property for *coherent* modules (section 9; the book's property is false otherwise, step 9's finding); `InferPrincipalFor Btest p` (step 10's `D11For`) for every coherent test program; step 9's `legal_` theorems re-proved without hypothesis; `[principal]` retired; Chapter 9's flags refusal | StandardA96NumberFlagsTest; and every compile-success theorem of steps 9 and 10 for a coherent program becomes unconditional (up to the 622 targets of step 9) | medium |

Order: (a) can start as soon as step 9's objects exist; (b) to (f) in order; (g) last, after
step 10. Milestone (a) gives most of the refusals early and unconditionally; (b) to (f) build the
principality proof, whose test yield is the remainder and, at (g), the removal of D11's
hypothesis for every coherent program (section 9).

## The mathematics

### 1. Objects and notation

From `static-core.tex` and step 9. `TyVar` (each `α` with `cls α ∈ {any, num, comp, app, capp}`,
Section `sec:static-core-simple`), `RowVar`, `TyName` (with arity); `V := TyVar ⊎ RowVar`. Types
`τ ::= α | τ → τ | (τ1, ..., τk) t | ⟨ϱ⟩ | ⟨ϱ | ε⟩` with `ϱ` a finite map from labels to types
(Figure `fig:static-core-compound`). `vars X` is the set of type and row variables of an object
`X`; `X` is *well formed* when no record type in it has a label twice (A23).

A *substitution* `S` is a finite map from `V` to types with `S ε` a record type for every row
variable (Section `sec:static-core-types`). `S X` is the book's substitution, applied
simultaneously; it is *defined on* `X` when no record of `X` gains a label it already has. `S`
*respects classes* when `S α ∈ Adm(cls α)` for every type variable in its domain
(Figure `fig:static-core-admissible`). `S` *fixes* a set `R` when `R ∩ dom S = ∅`. `R ∘ S` is
composition (`(R ∘ S) v = R (S v)` for `v ∈ dom S`, `R v` otherwise). `S` is idempotent when
`dom S ∩ vars (ran S) = ∅`.

*Rigid* variables: the explicit variables in scope (`U of C`, Section `sec:static-core-explicit`)
and the free variables of the root context `C0`. A derivation for a phrase in `C0` never
substitutes them (the instance definition of `sec:static-core-principal` excludes the variables
free in `C0`, and maps the variables of `U` to variables), so for the algorithm they are
constants that a flexible variable may be bound to. Explicit variables are *named*: a type
variable of the syntax names one variable (`sec:static-core-simple`), so two annotations writing
`a` in disjoint scopes bind the same variable, each in its own scheme.

*Lacks.* For an object `X`, `lacks_X(ε) = ⋃ { Dom ϱ ; ⟨ϱ | ε⟩ occurs in X }`: the labels that
`ε` must not supply anywhere in `X`. This is the implicit constraint of finding B3 and A23: in
`f : { r | x : Int } -> r -> Int`, `r` names the row variable `ε` (the extension variable, rule
`r:s-ty-openrecord`; written alone it is `⟨∅ | ε⟩`, rule `r:s-ty-rowvar`), and `x ∈ lacks(ε)`.

### 2. The constraint language

A *unification problem* is `P = (E, X, R, n)`: a list `E` of equations `τ ≐ τ'` between types, a
*frame* `X` (a list of types: the rest of the object on which every substitution must be
defined, that is, the context and the types of the derivation built so far), a rigid set `R`,
and a fresh-variable counter `n` above every variable index in `E`, `X`, `R`. Class constraints
are not separate: a variable carries its class, and a requirement "`τ ∈ Adm κ`" arises only when
a variable of class `κ` is bound to `τ`. Lacks constraints are not separate either: they are
`lacks_{X ∪ E}`.

A *unifier* of `P` is a substitution `S` that respects classes, fixes `R`, is defined on
`X ∪ E`, and has `S τ = S τ'` for every equation.

### 3. Meets and class propagation

The order of `sec:static-core-classes` (`num ≤ comp`, `capp ≤ comp`, `capp ≤ app`, all `≤ any`)
has these greatest lower bounds (`none`: no common lower bound):

| `⊓` | any | num | comp | app | capp |
|-----|-----|-----|------|-----|------|
| any | any | num | comp | app | capp |
| num | num | num | num | none | none |
| comp | comp | num | comp | capp | capp |
| app | app | none | capp | app | capp |
| capp | capp | none | capp | capp | capp |

**Meet lemma (K4).** For every `τ`: `τ ∈ Adm κ ∧ τ ∈ Adm κ'` iff `κ ⊓ κ' = some m` and
`τ ∈ Adm m`. (Checked in the review against the figure: `Adm(app) ∩ Adm(comp) = Adm(capp)`,
`Adm(num) ⊆ Adm(comp)`, `Adm(num) ∩ Adm(app) = ∅`.)

**Class propagation (finding B3).** For a class `κ` and a type name `t` of arity `k`,
`D(κ, t) ∈ Option (Class^k)`:

| `κ` | `t` | `D(κ, t)` |
|-----|-----|-----------|
| any | every `t` | `(any, ..., any)` |
| num | `Int`, `Float` | `()` |
| comp | `Int`, `Float`, `Char`, `String` | `()` |
| comp | `List` | `(comp)` |
| comp | `Tuple2`, `Tuple3` | `(comp, comp)`, `(comp, comp, comp)` |
| app | `String` | `()` |
| app | `List` | `(any)` |
| capp | `String` | `()` |
| capp | `List` | `(comp)` |
| any other pair | | `none` |

**Propagation lemma (K5).** `(τ1, ..., τk) t ∈ Adm κ` iff `D(κ, t) = some (κ1, ..., κk)` and
`τi ∈ Adm κi` for every `i`; a function type or a record type is in `Adm κ` iff `κ = any`; a
variable `β` is in `Adm κ` iff `cls β ≤ κ`. By induction on the type against
Figure `fig:static-core-admissible` (`Adm comp` is the least set satisfying its equation, so the
`comp` cases are by induction on the derivation of membership).

**Requirements.** `req κ τ` is the list of pairs `(β, κ')` with `β` a type variable occurring in
`τ` at a position where `κ'` is required, computed structurally: `req any τ = []`;
`req κ β = [(β, κ)]`; `req κ ((τi) t) = ⋃ req κi τi` when `D(κ, t) = some (κi)`, failure when
`none`; failure for a function or record type when `κ ≠ any`. Then `Sτ ∈ Adm κ` iff
`S β ∈ Adm κ'` for every `(β, κ') ∈ req κ τ` (from K5, by induction on `τ`).

### 4. Unification

The state is `(E, A, X, R, n)`: pending equations, the accumulated substitution `A` (idempotent,
already applied to `E` and `X`), frame, rigid set, counter. *Binding* `v ↦ τ` (with `v` flexible,
`v ∉ vars τ`): fail if `v` is a row variable and `Dom(row of τ) ∩ lacks_{X ∪ E}(v) ≠ ∅`;
otherwise `E := E{τ/v}`, `X := X{τ/v}`, `A := {τ/v} ∘ A`. A step takes the first equation
`τ ≐ τ'`:

- **(U0) identical:** drop it.
- **(U1) two type variables `α ≐ β`, `α ≠ β`.** Both flexible: if `cls α ⊓ cls β = none`, fail;
  if it is `cls β`, bind `α ↦ β`; if `cls α`, bind `β ↦ α`; otherwise take a fresh `γ` of class
  `m = cls α ⊓ cls β` (index `n`, `n := n + 1`) and bind `α ↦ γ`, `β ↦ γ`. One rigid, say `α`:
  if `cls α ≤ cls β`, bind `β ↦ α`, else fail. Both rigid: fail.
- **(U2) a type variable and another type `α ≐ τ`** (either order): fail if `α` is rigid; fail if
  `α ∈ vars τ` (the occurs check, through field types and row tails); compute `req (cls α) τ`
  (failure: fail); for each variable `β` with requirements `κ'1, ..., κ'j`: if `β` is rigid,
  fail unless `cls β ≤ κ'i` for all `i`; if flexible, `m := cls β ⊓ κ'1 ⊓ ... ⊓ κ'j` (none:
  fail), and if `m ≠ cls β` bind `β ↦ γ` with `γ` fresh of class `m`; then bind `α` to `τ`
  under those bindings.
- **(U3) constructed types `(τi) t ≐ (τ'i) t'`:** if `t ≠ t'` fail, else replace by the
  equations `τi ≐ τ'i`.
- **(U4) function types:** replace by the two equations of domain and range.
- **(U5) records `⟨ϱ1 | t1⟩ ≐ ⟨ϱ2 | t2⟩`** (`t` a row variable or closed): add `ϱ1(l) ≐ ϱ2(l)`
  for every common label, in label order; let `ϱ1'`, `ϱ2'` be the fields of each side the other
  lacks. Then:
  - both closed: fail unless `ϱ1' = ϱ2' = ∅`;
  - `t1` closed, `t2 = ε2`: fail if `ϱ2' ≠ ∅` or `ε2` rigid; bind `ε2 ↦ ⟨ϱ1'⟩` (and
    symmetrically);
  - `t1 = t2 = ε`: fail unless `ϱ1' = ϱ2' = ∅`;
  - `t1 = ε1 ≠ ε2 = t2`, `ϱ1' = ϱ2' = ∅`: bind the flexible one to `⟨∅ | other⟩` (both rigid:
    fail);
  - `ϱ1' ≠ ∅ = ϱ2'`: fail if `ε2` is rigid or occurs in `ϱ1'`; bind `ε2 ↦ ⟨ϱ1' | ε1⟩` (and
    symmetrically);
  - both non-empty: fail if either is rigid, or `ε1` occurs in `ϱ2'`, or `ε2` in `ϱ1'`; with a
    fresh `ε`, bind `ε1 ↦ ⟨ϱ2' | ε⟩`, then `ε2 ↦ ⟨ϱ1' | ε⟩` (after the first binding).
- **(U6) any other pair** (different heads, a row against a non-record): fail.

When `E` is empty the result is `ok A` with the counter.

**Invariants** of every reachable state, for the original problem `P0 = (E0, X0, R, n0)`:

- (I1) `A` is idempotent, respects classes, fixes `R`, is defined on `X0 ∪ E0`, and
  `dom A ⊆ vars P0 ∪ [n0, n)`; `E` and `X` are `A E0'` and `A X0` for the equations not yet
  removed, and are well formed.
- (I2) *Solution correspondence*: for every substitution `S`, `S` is a unifier of `P0` iff there
  is a unifier `S''` of the current problem `(E, X, R, n)` with `S v = S'' (A v)` for every
  `v ∈ vars P0`.
- (I3) On failure, the current problem has no unifier (and so, by I2, neither has `P0`).

**Termination measure.** `μ = (number of flexible variables occurring in E, size of E)`,
lexicographic, where size counts type constructors, arrows, record nodes and fields. Every
binding step removes at least one flexible variable from `E` (U1 with a fresh `γ` removes two and
adds one; U2's class refinements replace variables one for one and remove `α`; U5's last case
removes two row variables and adds one); U0, U3, U4 and the first three record cases keep the
variables and decrease the size. The executable definition is by *fuel* (`Nat`, structural, one
unit per step) with three outcomes `ok`, `fail`, `outOfFuel`, as step 1's evaluators (conventions,
"Proofs"); the measure is used only in proofs (that some fuel suffices), never in a definition.

**The mgu theorem** (finding B3; class-respect and lacks-respect included). For a well-formed
problem `P0`:

1. if `unify P0 = ok S0` then `S0` is a unifier of `P0`, idempotent, and for every unifier `S`
   there is a substitution `T` that respects classes, fixes `R` and is defined on `S0 X0`, with
   `S v = T (S0 v)` for every `v ∈ vars P0`;
2. if `unify P0 = fail` then `P0` has no unifier;
3. for some fuel the outcome is not `outOfFuel`, and more fuel gives the same outcome.

Proof outline: (I1) to (I3) by induction on the steps, each step by one of the lemmas K1 to K11
below; then at `E = []` every substitution respecting classes, fixing `R` and defined on `X` is a
unifier of the current problem, `S'' = id` gives part 1's first claim, and (I2) gives the
factorisation `T := S''`. Part 3 by well-founded induction on `μ` (a proof, not a definition) and
monotonicity of fuel by induction on fuel.

### 5. Constraint generation without principality (milestone (a))

`coreGen B m` generates, for a module `m` in a basis `B`, one unification problem whose
solutions include every derivation's choice. It follows the rules of `static-core.tex` and
`static-modules.tex` node by node, with one variable per type the rules leave open:

- integer constant: a fresh variable of class `num` (`r:s-atexp-scon`); other constants their
  type; integer constant in a pattern: `Int` (`r:s-atpat-scon`);
- occurrence of a basis value, constructor, operator (`OT_stat`), or of an *annotated* binding:
  its scheme instantiated with fresh variables of the bound variables' classes (exact: every
  derivation uses an instance of that very scheme, since an annotated member's scheme is its
  annotation in every derivation, `r:s-valbind-var` and the comment of `r:s-dec-group`);
- occurrence of a lambda- or pattern-bound variable, or of a member of the group being
  elaborated: that variable's type (exact: such variables have types, not schemes);
- occurrence of an *unannotated* `let`- or top-level-bound variable outside its group: a fresh
  unconstrained variable (an over-approximation: dropping constraints keeps every derivation a
  solution);
- the premises of each rule as equations (application, case, match, update with a fresh row
  variable, record pattern with a fresh row variable, constructor patterns by the arrow shape of
  the instantiated scheme);
- annotated bindings: the explicit variables `U'` (determined by the names, step 9) added to
  the rigid set within the binding, the annotation's type from step 9's deterministic
  elaboration (failure: the test is `static-deterministic`, step 9's), the body's type equated
  with it; the escape condition is dropped (a dropped condition keeps every derivation a
  solution);
- type declarations: step 9's deterministic elaboration with a fixed choice of new type names.

**Completeness of generation.** If `coreGen B m = some P` and `m` has a derivation in `B`, then
`P` has a unifier. Proof: given the annotated derivation `a`, map each generated variable to the
type `a` has at the corresponding node (or instance position), composed with the bijection
between `coreGen`'s new type names and `a`'s (step 9's module determinism up to type names, or
lemma L14 below); class respect from the `σ ≻ τ` side conditions that `check` verifies; rigid
variables fixed because `a` has the explicit variables themselves there; definedness because
`a`'s types are types; each equation by the premise of the rule at that node. Induction on the
annotated module, following `check`'s structure.

So `unify (coreGen B m) = fail` refutes every derivation of `m` in `B`. When `m` is the first
module of its program (or the only one), `B = Stat.Btest` and no principality is involved; that
covers every single-module test and every test whose failing module is a helper that imports no
other helper.

### 6. The inference algorithm W

State: `(A, n, X, R)` (accumulated substitution, counter, frame, rigid set). Outcome per phrase:
`ok (state, type, annotated phrase)`, `fail`, `outOfFuel` (only from `unify`). The annotated
phrase built is not yet substituted; the final annotation applies the final `A`.
`unify (τ ≐ τ')` means: run section 4 on `([τ ≐ τ'], X, R, n)` with fuel, compose its result
into `A`, apply it to `X`. Every type created is appended to `X` (so that lacks are computed on
the whole object).

Expressions (`r:s-atexp-*`, `r:s-exp-*`, `r:s-match`, `r:s-mrule`, `r:s-exprow`):

- integer constant: fresh `γ` of class `num`; float, char, string constants: their type;
- `longvar`, `longcon`, `(opv)`: look up the scheme (`C(longvar)`, `OT_stat(opv)`; absent: fail),
  instantiate each bound type variable with a fresh one of its class and each bound row
  variable with a fresh row variable; record the instance;
- `()`, tuples, `[ ]` (fresh `α`, `α List`), records (closed);
- `{ x | exprow }`: `τ = W(x)`, `ϱ = W(exprow)`, fresh `ε`, `unify (τ ≐ ⟨ϱ | ε⟩)`, result `A τ`
  (`r:s-atexp-update`);
- `let dec in exp`: `VE' = W(dec)` in `C`, then `W(exp)` in `C + VE'`;
- `exp atexp`: `τ1`, `τ2`, fresh `β`, `unify (τ1 ≐ τ2 → β)`, result `β`;
- `\ atpat -> exp`: `(VE, τ) = W(atpat)`, `τ' = W(exp)` in `C + VE`, result `τ → τ'`;
- `case exp of match`: `τ = W(exp)`, `τm = W(match)`, fresh `β`, `unify (τm ≐ τ → β)`;
- match: each rule's `τi → τ'i`, unified pairwise with the first.

Patterns (`r:s-atpat-*`, `r:s-pat-*`, `r:s-patrow`): wildcard and variable a fresh `α`; integer
constant `Int`, char `Char`, string `String`; a constructor's instantiated scheme must be a
constructed type (atomic) or an arrow chain of exactly `n` arguments ending in a constructed
type (`r:s-pat-con`), its status `c`; tuple, `[ ]`, `::` (`unify (τ2 ≐ τ1 List)`), `as`;
a record pattern `{ l1, ..., lk }` gives fresh `αi` and a fresh `ε`, type `⟨{li ↦ αi} | ε⟩`.

Type expressions (`r:s-ty-*`): step 9's deterministic `elabTy`. The new explicit variables of an
annotation `ty` in `C` (`U'` new for `ty` in `C`) are determined: one per name of
`tyvars ty \ names (U of C)`, a row variable if the name is used as the extension variable of a
record type expression in `ty`, a type variable of the class its name gives otherwise (A19, A36:
only a name of class `any` names a row variable, so `{ number | x : Int }` fails in `elabTy`).

Groups (`r:s-dec-group`, `r:s-valbind-var`, `r:s-valbind-pat`; and `r:sm-topdec-value`):

1. For each member `x`: if annotated, `U'_x` as above and `τ_x = elabTy (C + U'_x) ty`, entry
   `x ↦ ∀U'_x. τ_x`; if not, a fresh `α_x` of class `any`, entry `x ↦ α_x`. This is `VE0`.
2. For each member in order, in `C_g = C + VE0`: unannotated, `unify (α_x ≐ W(exp))`;
   annotated, with `R := R ∪ U'_x`, `unify (W(exp) ≐ τ_x)` in `C_g + U'_x` (A21: `U'_x` is in
   scope for annotations nested in `exp`), then `R` restored.
3. Escape (A20): for every annotated member, `U'_x ∩ tyvars (A C_g) = ∅`, else fail.
4. Closure with A93: `VE = A VE0`; each member's scheme is
   `Clos_{A C} σ_x` closed also over the `num` variables of `tyvars VE \ (tyvars σ_x ∪ tyvars (A C))`
   (`sec:static-core-closure`); the group node records `C`, `VE`, the `U'_x`.
5. A pattern binding `atpat = exp` is a group by itself: `(VE, τ) = W(atpat)`,
   `unify (τ ≐ W(exp))`, then step 4.

`inferExpW C0 e` runs W with `R = U of C0 ∪ tyvars C0` (the root context's free variables are
rigid) and applies the final `A` to the annotated phrase.

Modules (milestone (f), `r:sm-module`, `r:sm-topdec-*`, `r:sm-datbind`, `r:sm-conbind`,
`r:sm-typbind`, `r:sm-typbind-record`):

- imports, exposing lists, header: step 9's deterministic functions;
- the type declarations (`r:sm-topdec-types`, finding B5): Appendix A gives one group of custom
  types followed by the aliases in an order where each follows the aliases it mentions
  (`sec:appendix-derived-forms-modules`, step 8's `aliasOrder`). `solveTypes`: (i) a new type
  name `t_i` (arity from its parameter list) for each custom type, above every name of `T of C`;
  (ii) each alias in order, `θ_j = Λ params. elabTy (C ⊕ TE_<j + params) ty_j`, where `TE_<j`
  holds the custom types (type function `t_i`) and the earlier aliases; a record alias also
  gives its constructor; (iii) the constructors, elaborated in `C ⊕ TE` (all of it), closed by
  `Clos_C` (`r:sm-datbind`). This solves the fixed point because type expressions read only the
  type functions of `TE`, and those are fixed by (i) and (ii);
- ports: deterministic (`r:sm-topdec-portout`, `r:sm-topdec-portin`);
- top-level value groups: W's groups in the module's context, which has no free type variables,
  so closure generalises every variable not explicit;
- programs: modules in order, each in the basis that `r:p-stat-module` builds from the earlier
  ones' results.

### 7. Soundness, completeness, principality: the statements

For a well-formed root context `C0` (its `U` unambiguous, its schemes well formed):

- **Soundness.** If `inferExpW n C0 e = ok a` then `checkExp C0 a = true` and `a.erase = e`.
- **Refutation.** If `inferExpW n C0 e = fail` then no derivation of `e` in `C0` exists:
  `¬ ∃ τ, ElExp C0 e τ` (equivalently, by adequacy, no `a'` with `checkExp C0 a' = true` and
  `a'.erase = e`).
- **Completeness.** If some derivation of `e` in `C0` exists, then for every fuel the outcome is
  not `fail`, and for some fuel it is `ok`.
- **Principality.** If `inferExpW n C0 e = ok a` then `IsPrincipal C0 a`: every derivation `a'`
  of `e` in `C0` is an instance of `a` (`InstanceOf C0 a' a`; `sec:static-core-principal`: one substitution respecting
  classes, moving no variable free in `C0`, defined on every type of `a`, mapping each variable
  of `U` at a node to a variable, each type at a node to the corresponding type of `a'`, each
  scheme to one no less general than `a'`'s).
- **Modules** (`sec:static-modules-principal`): for a module coherent in `B` (section 9), the
  same for `inferModuleW n B m` (`IsPrincipalMod B a`), with the instance taken up to a bijection
  on generated type names; refutation for every module.
- **Programs** (finding B1): if `inferProgramW n B p = ok a` and every module is coherent in its
  basis, then `a` is a principal program derivation (step 10's `PrincipalProgDeriv`); if it
  fails, `¬ ∃ τ PE, ElProgram B p.modules τ PE`.

### 8. The proof, lemma by lemma

Unification (K, milestones (a) to (d)):

- **K1 decomposition.** `S((τi) t) = S((τ'i) t')` iff `t = t'` and `S τi = S τ'i` for all `i`;
  the same for arrows; different heads are never equal under any substitution.
- **K2 binding.** If `v ∉ vars τ` then `S v = S τ` iff `S` and `S ∘ {τ/v}` agree on every
  variable; and `{τ/v}` preserves the solution set as (I2) says.
- **K3 occurs check.** If `v ∈ vars τ` and `τ ≠ v` (as a type, or `τ ≠ ⟨∅ | v⟩` for a row
  variable) then `S v ≠ S τ` for every `S` (size).
- **K4 meets**, **K5 propagation**, **requirements**: section 3.
- **K6 class refinement.** Replacing a flexible `β` by a fresh `γ` of class `m = cls β ⊓ κ'...`
  preserves solutions: a unifier `S` with `S β ∈ Adm(cls β)` and `S β ∈ Adm κ'` for every
  requirement extends to `S''` with `S'' γ = S β`, and `S β ∈ Adm m` by K4; if the meet is
  `none`, no `S` satisfies both (K4). A rigid `β` is fixed by every unifier, so its requirements
  hold iff `cls β ≤ κ'` (K5's variable case).
- **K7 rigid variables.** A unifier fixes `R`; so (U1) and (U2) fail exactly when no unifier
  exists.
- **K8 rows.** For `S` defined on both records, `S ⟨ϱ1 | t1⟩ = S ⟨ϱ2 | t2⟩` iff the common
  fields agree and, case by case as in (U5), the remaining fields are supplied by the other
  side's row variable; the factor for the last case is
  `T ε := ⟨(row of S ε1) restricted to the labels outside Dom ϱ2' | tail of S ε1⟩`.
- **K9 definedness and lacks.** For `S` with well-formed range and `X` well formed: `S` is
  defined on `X` iff for every row variable `ε ∈ dom S` occurring in `X`, the labels of `S ε` are
  disjoint from `lacks_X(ε)`. So the lacks check of a binding fails exactly when no unifier is
  defined on the object (A23).
- **K10 composition.** `(T ∘ S) X = T (S X)`; `T ∘ S` is defined on `X` iff `S` is defined on
  `X` and `T` on `S X`.
- **K11 class respect composes.** If `S` and `T` respect classes, so does `T ∘ S` (the property
  of `sec:static-core-types`: `Adm κ` is closed under substitutions that are defined and respect
  classes; with K5 by induction on the type).

Inference (L, milestones (b) to (f)):

- **L1 substitution algebra** for contexts, schemes and annotated phrases (K10 lifted;
  substitution avoids bound variables by choosing fresh ones above the counter).
- **L2 instance transitivity and stability.** `σ ≻ σ'` and `σ' ≻ τ` give `σ ≻ τ`; `σ ≻ τ` gives
  `S σ ≻ S τ` for `S` respecting classes and defined; `InstanceOf` is reflexive and
  transitive (compose the substitutions, K10, K11).
- **L3 generalisation lemma** (with A93). For `T` respecting classes and defined:
  `T (Clos_C σ) ≻ Clos_{T C} (T σ)`, and the same for A93's group closure member by member (the
  extra `num` variables are vacuous: they change no instance). Proof: an instance of the right
  side substitutes variables of `T σ` not in `T C`; those are images of variables of `σ` not in
  `C` (bound on the left) or of no variable of `C`; build the left side's instance.
- **L4 weakening.** If `C'` is at least as general as `C` (`C'(x) ≻ C(x)` for every `x`, same
  `T` and `U`) then every derivation in `C` gives one in `C'` with the same types at its nodes
  and schemes no less general; the escape condition is kept because `tyvars C'(x) ⊆ tyvars C(x)`
  when `C'(x) ≻ C(x)`.
- **L5 stability of the checker under substitution** (step 9's `check_subst`, or proved here):
  `check C a = true` gives `check (S C) (S a) = true` for `S` respecting classes, defined on `a`
  and `C`, fixing `U` at every node.
- **L6 named variables** (A20, A21). In every state of W, a variable named by the syntax occurs
  in `A C` only if it is in `U of C`; hence the escape check after a group is complete: if it
  fails for `A`, it fails for `T ∘ A` for every `T` fixing the explicit variables, so no
  derivation passes it.
- **L7 type expressions.** `elabTy C ty = some τ` iff `ElabTy C ty τ` (step 9's relation), and
  then `τ` is unique; `U'` is unique; both commute with renamings fixing named variables.
- **L8 patterns.** If `W(pat) = ok (VE, τ)` and `S' C ⊢ pat ⇒ (VE', τ')`, then for some `T`,
  `VE' = T VE` and `τ' = T τ` (patterns are linear; every open choice is a fresh variable).
- **L9 mgu**: section 4.
- **L10 soundness of W**, by induction on the phrase: each rule's premises hold of `A_final`
  applied to the annotated phrase (L5 to move earlier parts under later substitutions; L7, L8).
- **L11 completeness and principality of W** (the main induction, Damas and Milner extended):
  for every state satisfying the invariants (I1) and L6, every `S'` respecting classes, fixing
  `R` and defined on `A X`, and every annotated derivation `a'` of `e` in `S' (A C)`: `W` does
  not fail, and if it returns `(A1, τ, a)` then there is `T` respecting classes, fixing `R`,
  defined on `A1 X1`, with `S' ∘ A = T ∘ A1` on the old variables and `a'` an instance of
  `T (A1 a)` node by node. Cases: constants and occurrences (instantiation is most general: L2);
  application, case, update (L9 with the induction hypotheses composed, K10); `let` (L3 then L4
  to move `a'`'s body into the more general context, then the induction hypothesis); groups
  (monomorphic within the group, `r:s-dec-group`; L9 per member; annotated members by L7 and
  L9 with the rigid set enlarged; escape by L6; closure by L3); patterns (L8).
- **L12 the book's statement.** From L11 with `S' = id` and `A = id`: `C0`'s free variables are
  rigid, so `T` moves none of them; this is the instance relation of
  `sec:static-core-principal` (property 1). Refutation is L11's first claim, contraposed.
- **L13 termination of W**: structural on the phrase; each `unify` terminates for some fuel
  (section 4, part 3); take the maximum and use fuel monotonicity.
- **L14 type declarations** (finding B5). `solveTypes` gives a solution of
  `r:sm-topdec-types`'s premises; every solution is its image under a bijection of the new type
  names (by induction along the alias order, each alias's type function determined by the
  earlier ones, L7; then the constructors). *Coherence with `r:sm-topdec-seq`* (section 9): if
  the module is coherent in `C`, a derivation that splits the type declarations with
  `r:sm-topdec-seq` (step 9's `typesSplit`) gives the same environment `E` (up to the bijection)
  and the same types at the nodes of the declarations, since every alias mentions only earlier
  aliases (Appendix A's order) and a constructor mentions no alias of the phrase whose name `C`
  also binds; if it is not coherent, the two shapes give different environments (step 9's
  example).
- **L15 mutual instances are renamings.** If `a'` is an instance of `a` by `T` and `a` of `a'`
  by `T'`, then `T` restricted to the variables of `a` is injective, maps type variables to type
  variables of the same class (from `T α ∈ Adm(cls α)`, `T' (T α) = α` and K5's variable case
  in both directions) and row variables to `⟨∅ | ε'⟩`, and the schemes are equal up to the
  scheme equality of `sec:static-core-schemes`. This is the second half of each property
  ("any two of its principal derivations ... differ only by a renaming").
- **L16 equivariance.** `check` and `checkModule` are invariant under renamings of variables
  and bijections of type names outside `T of B` (by induction on the annotated phrase). Used
  for modules (L14, generated names) and for programs (bases built from earlier modules differ
  by a bijection).

### 9. Node correspondence and coherence of modules (finding B5)

Step 9 fixes the nodes (`nodesModule`: the nodes about the datbind, the typbinds, the conbinds and
the type expressions are kept with their paths, the split parts of `typesSplit` are left out) and
`InstanceOfMod` (up to a bijection on generated type names). With that definition, two
derivations of a module that derive its type declarations in different shapes
(`r:sm-topdec-types` whole, or split by `r:sm-topdec-seq`) have corresponding nodes for every
declaration, in different contexts. Step 9 found ("Issues with the plan", item 1) that the two
shapes can give different results: with `type T = T String` and `type alias String = Int`, the
whole shape gives `T : Int -> T`, the split shape `T : String -> T`, and neither derivation is an
instance of the other, so the module has no principal derivation and the property of
`sec:static-modules-principal` is false for it.

**Coherence.** A module is *coherent in a context `C`* when no constructor argument of its
custom types mentions, unqualified, a type constructor that an alias of the module binds and
that `C` (the context `r:sm-module` builds from the imports) also binds. Decidable
(`coherentIn C m`, on the bare module and `C`'s type environment). For a coherent module the
split shape either fails (the mentioned alias is unbound in `C` at the split) or gives the same
environment and the same types at corresponding nodes (L14); so the module property holds for
coherent modules, and principality is proved for them (milestone (f)). Aliases never cause
incoherence, because Appendix A puts each alias after the aliases it mentions.

A program is coherent when each of its modules is coherent in the context built from the basis
of `r:p-stat-module`. Every test program is checked (`lake exe check-coherence`); an incoherent
compile-success test has no principal derivation by the book, gets no unconditional theorem,
and is listed as evidence for step 9's finding.

## Lean definitions

### Files

| File | Milestone | Contents |
|------|-----------|----------|
| `Stat/Complete/Subst.lean` | (a) | `V`, `Subst`, `apply?`, `DefinedOn`, `RespectsClasses`, `Fixes`, `comp`, `Idem`, `lacks`; K9 to K11 |
| `Stat/Complete/Classes.lean` | (a) | `Class.le`, `Class.meet`, `Class.prop` (the table `D`), `req`; K4, K5 |
| `Stat/Complete/Unify.lean` | (a), (b) to (d) | `UProblem`, `UState`, `UOutcome`, `unifyStep`, `unifyF`; refutation (a); soundness, mgu, termination (b) to (d) |
| `Stat/Complete/Core.lean` | (a) | `coreGen`, its completeness, `refute_of_core` |
| `Stat/Complete/Fragment.lean` | (a) | `Features`, `featuresOf`, `Fragment`, `fragmentOf`, `InFragment` |
| `Stat/Complete/W.lean` | (b) | `WState`, `WOutcome`, the mutual `w*` functions, `inferExpW` |
| `Stat/Complete/WSound.lean` | (b) | L1, L5, L10 |
| `Stat/Complete/WComplete.lean` | (b) to (e) | L2, L3, L4, L6 to L8, L11 to L13 |
| `Stat/Complete/Modules.lean` | (f) | `solveTypes`, `coherentIn`, `coherentProg`, `inferModuleW`, `inferProgramW`; L14, L16, module and program principality |
| `Stat/Complete/Discharge.lean` | (g) | L15, `principalExistsCore`, `principalExistsMod_coherent`, `d11For_of_coherent`, `legal_of_W`, `a96_number_flags` |
| `Stat/Complete/Examples.lean` | each | the unit examples (Tests gained) |
| `Generated/Refuse<nn>.lean` | each | per-test refusal theorems, written by the translator |

### Substitutions, classes, unification

```lean
namespace StandardElm.Stat.Complete
open StandardElm.Stat

inductive V where
  | ty (α : TyVar)
  | row (ε : RowVar)
  deriving DecidableEq, Repr

/-- A substitution: finitely many bindings, each row variable to a record type. If step 9's
    `Stat.Subst` has this shape (and composition), it is used instead and the definitions below
    become lemmas about it. -/
abbrev Subst := List (V × Ty)

/-- The book's simultaneous substitution (sec:static-core-types); `none` when a record would get
    a label twice (A23). Structural on the type. -/
def Subst.apply? (S : Subst) : Ty → Option Ty
def Subst.DefinedOn (S : Subst) (X : List Ty) : Prop := ∀ τ ∈ X, (S.apply? τ).isSome
def Subst.RespectsClasses (S : Subst) : Prop := ∀ α τ, (V.ty α, τ) ∈ S → Adm α.cls τ
def Subst.Fixes (S : Subst) (R : List V) : Prop := ∀ v ∈ R, S.lookup v = none
def Subst.Idem (S : Subst) : Prop := ∀ v ∈ S.map (·.1), ∀ w τ, (w, τ) ∈ S → v ∉ Ty.vars τ
def Subst.comp (T S : Subst) : Subst                       -- T ∘ S
def Subst.var (S : Subst) (v : V) : Ty                      -- S v (v itself, as a type, outside dom S)

/-- lacks_X(ε): the labels ε is extended by anywhere in X. -/
def lacks (X : List Ty) (ε : RowVar) : List Lab

def Class.le : Class → Class → Bool
def Class.meet : Class → Class → Option Class               -- the table of section 3
def Class.prop : Class → TyName → Option (List Class)       -- D(κ, t)
/-- Requirements of section 3; `none` when τ has a head no instance of κ may have. -/
def req : Class → Ty → Option (List (TyVar × Class))

structure UProblem where
  eqs   : List (Ty × Ty)
  frame : List Ty
  rigid : List V
  next  : Nat

def UProblem.vars (P : UProblem) : List V
def UProblem.WF (P : UProblem) : Prop       -- well formed; every variable index below `next`

def IsUnifier (P : UProblem) (S : Subst) : Prop :=
  S.RespectsClasses ∧ S.Fixes P.rigid ∧
  S.DefinedOn (P.frame ++ P.eqs.flatMap fun e => [e.1, e.2]) ∧
  ∀ e ∈ P.eqs, S.apply? e.1 = S.apply? e.2

structure UState where
  eqs : List (Ty × Ty)
  acc : Subst
  frame : List Ty
  rigid : List V
  next : Nat

inductive UOutcome where
  | ok (S : Subst) (next : Nat)
  | fail
  | outOfFuel
  deriving DecidableEq, Repr

/-- One step of section 4 (U0 to U6); `none` = fail; `some st'` = continue. -/
def unifyStep (st : UState) : Option UState

/-- Structural on fuel: one step per unit. -/
def unifyF : Nat → UState → UOutcome
  | 0, _ => .outOfFuel
  | n + 1, st =>
    match st.eqs with
    | [] => .ok st.acc st.next
    | _ => match unifyStep st with
           | none => .fail
           | some st' => unifyF n st'

def UProblem.init (P : UProblem) : UState := ⟨P.eqs, [], P.frame, P.rigid, P.next⟩

/-- Default fuel: a literal the kernel never counts down beyond the steps actually taken. -/
def unifyFuel : Nat := 2 ^ 32
```

### Milestone (a): cores

```lean
/-- The weak constraint generator of section 5 for one module in a basis; `none` when a
    deterministic part (a type expression, an import, a header, a port type) fails, which is
    step 9's business. -/
def coreGen (B : SBasis) (m : Src.BModule) : Option UProblem

/-- Refutation by a core: the first module of a program fails in B. -/
def coreRefutes (B : SBasis) (p : Src.BProgram) : Bool :=
  match p.modules.head?.bind (coreGen B) with
  | some P => unifyF unifyFuel P.init == .fail
  | none => false
```

`coreRefutes` refutes the first module only. A program whose failing module is not the first
(its earlier modules elaborate) is refuted at milestone (f), which knows the principal bases.

### Fragments

```lean
/-- What a program uses, read on the bare program and the schemes it reaches in the basis. -/
structure Features where
  intConst   : Bool   -- an integer constant
  classVar   : Bool   -- a type variable of class ≠ any is created: a constant, an occurrence of a
                      -- value, constructor or operator whose scheme quantifies one, a class-named
                      -- type variable in a type expression or a type parameter
  records    : Bool   -- a record type or row reached, or record syntax (record, update, field
                      -- selection, accessor, record pattern, record type expression)
  annTopPoly : Bool   -- a top-level annotation with type variables, on a member alone in its group
  annOther   : Bool   -- any other annotation with type variables (nested, or on a member of a
                      -- group with other members)
  modules    : Bool   -- more than one module
  deriving DecidableEq, Repr

def featuresOf (B : SBasis) (p : Src.BProgram) : Features

inductive Fragment where
  | b | c | d | e | f
  deriving DecidableEq, Repr, Ord

/-- The least fragment containing the program:
    b: no modules, no annotations with variables, no classes, no records (integer constants count
       as classes);
    c: as b, with classes and with top-level annotations with variables (rigid variables);
    d: as c, with records and rows;
    e: as d, with every annotation (A20, A21) and annotated members in groups;
    f: everything (several modules). -/
def fragmentOf (B : SBasis) (p : Src.BProgram) : Fragment

def InFragment (f : Fragment) (B : SBasis) (p : Src.BProgram) : Prop := fragmentOf B p ≤ f
```

### Milestones (b) to (f): W

```lean
structure WState where
  acc   : Subst
  next  : Nat
  frame : List Ty
  rigid : List V

inductive WFail where
  | unbound | unify | escape (x : Var) | tyExp | pattern | port | module
  deriving DecidableEq, Repr

inductive WOutcome (α : Type) where
  | ok (st : WState) (a : α)
  | fail (why : WFail)
  | outOfFuel

mutual
  def wAtExp  (fuel : Nat) (C : Ctx) : Src.BAtExp  → WState → WOutcome (Ty × AnnAtExp)
  def wExpRow (fuel : Nat) (C : Ctx) : Src.BExpRow → WState → WOutcome (Row × AnnExpRow)
  def wExp    (fuel : Nat) (C : Ctx) : Src.BExp    → WState → WOutcome (Ty × AnnExp)
  def wMatch  (fuel : Nat) (C : Ctx) : Src.BMatch  → WState → WOutcome (Ty × AnnMatch)
  def wMRule  (fuel : Nat) (C : Ctx) : Src.BMRule  → WState → WOutcome (Ty × AnnMRule)
  def wDec    (fuel : Nat) (C : Ctx) : Src.BDec    → WState → WOutcome (VarEnv × AnnDec)
  def wValBind (fuel : Nat) (C : Ctx) : Src.BValBind → WState → WOutcome (VarEnv × AnnValBind)
  def wAtPat  (C : Ctx) : Src.BAtPat  → WState → WOutcome (VarEnv × Ty × AnnAtPat)
  def wPatRow (C : Ctx) : Src.BPatRow → WState → WOutcome (VarEnv × Row × AnnPatRow)
  def wPat    (C : Ctx) : Src.BPat    → WState → WOutcome (VarEnv × Ty × AnnPat)
end

/-- `U'` new for ty in C (sec:static-core-explicit), from the names; `none` if a name is used
    both as a type and as an extension variable. -/
def newExplicit (C : Ctx) (ty : Src.BTy) : Option (List V)

/-- Clos_C VE with A93's extra number variables (sec:static-core-closure). -/
def closure93 (C : Ctx) (VE : VarEnv) : VarEnv

def inferExpW (fuel : Nat) (C0 : Ctx) (e : Src.BExp) : WOutcome AnnExp

/-- r:sm-topdec-types by Appendix A's order (section 6). -/
def solveTypes (C : Ctx) (next : Nat) (db : Option Src.BDatBind) (tbs : List Src.BTypBind) :
    Option (Env × AnnTypes × Nat)

def inferModuleW (fuel : Nat) (B : SBasis) (m : Src.BModule) : WOutcome AnnModule
def inferProgramW (fuel : Nat) (B : SBasis) (p : Src.BProgram) : WOutcome AnnProgram

def wFuel : Nat := 2 ^ 32
```

The recursion is structural on the phrase; fuel is passed unchanged to every call of `unifyF`.
In a group, the members are processed by a local recursion on the `BValBind` chain (a subterm).

At milestone (g), step 9's `Stat.inferProgram` (the unverified inference in step 10's
pipeline) is redefined as `fun B p => (inferProgramW wFuel B p).toExcept`, so that
step 10's `InferPrincipalFor` is about the proved algorithm; the old function is kept as
`Stat.inferProgramFast` if it is faster, and compared on every test by `lake exe
compare-inference` (equal up to renaming, by `reduceProgram` equality and `checkModule`).

## Theorems

All by structural or well-founded induction in proofs; no definition uses well-founded
recursion.

### Unification (milestones (a) to (d))

```lean
/-- (a): the refutation direction, for the full type language. -/
theorem unifyF_fail {n P} (hP : P.WF) (h : unifyF n P.init = .fail) : ∀ S, ¬ IsUnifier P S

/-- (b) to (d): soundness and most general unifier. -/
theorem unifyF_ok {n P S0 n'} (hP : P.WF) (h : unifyF n P.init = .ok S0 n') :
    IsUnifier P S0 ∧ S0.Idem ∧ P.next ≤ n' ∧
    ∀ S, IsUnifier P S → ∃ T, T.RespectsClasses ∧ T.Fixes P.rigid ∧
      T.DefinedOn (P.frame.filterMap S0.apply?) ∧ ∀ v ∈ P.vars, S.var v = (T.comp S0).var v

theorem unifyF_terminates (P : UProblem) (hP : P.WF) : ∃ n, unifyF n P.init ≠ .outOfFuel
theorem unifyF_mono {n m P} (h : unifyF n P.init ≠ .outOfFuel) : unifyF (n + m) P.init = unifyF n P.init
```

Method: the invariants (I1) to (I3) of section 4 as a predicate `Inv P0 st`, preserved by
`unifyStep` (one lemma per case U0 to U6, each from K1 to K11), and `unifyStep st = none →
¬ ∃ S, IsUnifier (st.toProblem) S`. `unifyF_fail` needs only the preservation of "a unifier of
`P0` gives one of the current state" and the failure lemmas (the forward half of (I2)), which is
why it is milestone (a): no factorisation, no idempotence. `unifyF_ok` adds the backward half and
the final step. Termination by `WellFounded.induction` on `μ` (`Prod.Lex` of `Nat`s), with the
lemma `μ (unifyStep st) < μ st`. During (b) and (c), `unifyF_ok` carries the hypothesis
`P.NoRows` (and during (b) `P.NoClasses`); the row and class cases of the case analysis are
closed by contradiction until their milestone.

### Constraint generation (milestone (a))

```lean
theorem coreGen_complete {B m P} (hB : B.WF) (h : coreGen B m = some P) :
    (∃ a : AModule, a.erase = m ∧ checkModule B a = true) → ∃ S, IsUnifier P S

theorem noDeriv_of_core {B p} (hB : B.WF) (h : coreRefutes B p = true) :
    ∀ m, p.modules.head? = some m → ¬ ∃ B' E, ElModule B m B' E

theorem notStat_of_core {B p} (hB : B.WF) (h : coreRefutes B p = true) :
    ¬ ∃ τ PE, ElProgram B p.modules τ PE
```

Methods: `coreGen_complete` by induction on the annotated module following `checkModule`
(section 5), with the variable-to-node map built alongside `coreGen` (its state records, for
each generated variable, the path of the node or instance position it stands for). The type-name
bijection from step 9's module determinism (or L14). `noDeriv_of_core` from it and
`unifyF_fail`, with step 9's `checkModule_adequate` (a derivation gives a checked annotated
module). `notStat_of_core`: the first premise of `r:p-stat-module` (or of
`r:p-stat-main-*` for a single module) is a derivation of the first module in `B`.

### W (milestones (b) to (e))

```lean
/-- The invariant of a state for a context: (I1) for the accumulated substitution, the frame
    contains the context and every type created, L6's named-variable condition. -/
def WState.Inv (st : WState) (C : Ctx) : Prop

theorem wExp_sound {n C e st st' τ a} (hi : st.Inv C) (h : wExp n C e st = .ok st' (τ, a)) :
    st'.Inv C ∧ checkExp (st'.acc.ctx C) (st'.acc.ann a) = true ∧ a.erase = e ∧
    (st'.acc.ann a).ty = st'.acc.applyTy τ

theorem wExp_complete {n C e st S' a'} (hi : st.Inv C)
    (hS' : S'.RespectsClasses ∧ S'.Fixes st.rigid ∧ S'.DefinedOn (st.frame))
    (ha' : checkExp (S'.ctx (st.acc.ctx C)) a' = true) (he : a'.erase = e) :
    (∀ w, wExp n C e st ≠ .fail w) ∧
    ∀ st' τ a, wExp n C e st = .ok st' (τ, a) →
      ∃ T, T.RespectsClasses ∧ T.Fixes st.rigid ∧ T.DefinedOn st'.frame ∧
        (∀ v ∈ st.vars, (S'.comp st.acc).var v = (T.comp st'.acc).var v) ∧
        InstanceNodes (T.ann (st'.acc.ann a)) a'

theorem inferExpW_sound {n C0 e a} (hC : C0.WF) (h : inferExpW n C0 e = .ok _ a) :
    checkExp C0 a = true ∧ a.erase = e
theorem inferExpW_fail {n C0 e w} (hC : C0.WF) (h : inferExpW n C0 e = .fail w) :
    ¬ ∃ τ, ElExp C0 e τ
theorem inferExpW_principal {n C0 e a} (hC : C0.WF) (h : inferExpW n C0 e = .ok _ a) :
    a.erase = e ∧ IsPrincipal C0 a
theorem inferExpW_terminates (C0 : Ctx) (e : Src.BExp) (hC : C0.WF) :
    ∃ n, ∀ m ≥ n, inferExpW m C0 e ≠ .outOfFuel
```

(and the same for every phrase class of the mutual block). `InstanceNodes x y` is the node-wise
relation of `sec:static-core-principal` with the substitution already applied (types equal at
corresponding nodes, `y`'s schemes no more general, `U` mapped to `U`). During (b) to (d) the
statements carry `InFragment f` hypotheses on the phrase (`f = b, c, d`); (e) removes them for
single-module programs.

Method: section 8, lemmas L1 to L13, by mutual structural induction on the phrase, the group
case by an inner induction on the member chain.

### Modules and programs (milestone (f))

```lean
theorem solveTypes_sound {C n db tbs E ann n'} (h : solveTypes C n db tbs = some (E, ann, n')) :
    ElabTopDecTypes C (.types db tbs) E
theorem solveTypes_complete {C n db tbs E'} (h : ElabTopDecTypes C (.types db tbs) E') :
    ∃ E ann n' ρ, solveTypes C n db tbs = some (E, ann, n') ∧ ρ.Bijective ∧ E' = ρ.env E
theorem topdecTypes_seq_coherent {C db tbs E E'}
    (h1 : ElabTopDec C (.types db tbs) E) (h2 : ElabTopDec C (splitSeq db tbs) E') :
    ∃ ρ, ρ.Bijective ∧ E' = ρ.env E

theorem inferModuleW_principal {n B m a} (hB : B.WF) (hc : coherentIn (B.ctxFor m) m)
    (h : inferModuleW n B m = .ok _ a) : a.erase = m ∧ IsPrincipalMod B a
theorem inferModuleW_fail {n B m w} (hB : B.WF) (h : inferModuleW n B m = .fail w) :
    ¬ ∃ B' E, ElModule B m B' E
theorem inferProgramW_principal {n B p a} (hB : B.WF) (hc : coherentProg B p)
    (h : inferProgramW n B p = .ok _ a) : PrincipalProgDeriv B p a
theorem inferProgramW_fail {n B p w} (hB : B.WF) (hc : coherentProg B p)
    (h : inferProgramW n B p = .fail w) : ¬ ∃ τ PE, ElProgram B p.modules τ PE
```

(`B.ctxFor m` is the context of `r:sm-module` built from `m`'s imports; `coherentProg B p` says
each module is coherent in the context its basis gives, decidable along `inferProgramW`. Failure
of the first module needs no coherence: `inferModuleW_fail` holds for every module, since a
derivation of either shape is a derivation W would have to fail on.)

`ElabTopDecTypes` and `ElabTopDec` are step 9's relations for `r:sm-topdec-types` and the
top-level declarations (step 9's `types` and `typesSplit` annotations); `splitSeq` is any
splitting of the type declarations by `r:sm-topdec-seq` that the rules accept; the coherence
lemma `topdecTypes_seq_coherent` carries the hypothesis `coherentIn C m`. Methods: L14 for the
first three; module principality from L11 per value group (closed context) and L14, with step
9's node correspondence (section 9);
programs by induction on the modules, each basis transported by L16 and the uniqueness up to
renaming of the earlier modules' principal derivations (L15). `inferProgramW_fail` for a failing
module `k`: modules before `k` are principal (the induction), any principal derivation of them
differs by a renaming (L15) and gives an isomorphic basis, in which module `k` fails too (L16).

### Discharge (milestone (g))

```lean
/-- The Core's property (sec:static-core-principal), for every phrase and context. -/
theorem principalExistsCore : PrincipalExistsCore

/-- The module property (sec:static-modules-principal), for coherent modules (section 9). -/
theorem principalExistsMod_coherent :
    ∀ B (m : Src.BModule), B.WF → coherentIn (B.ctxFor m) m →
      (∃ B' E, ElModule B m B' E) → ∃ a, a.erase = m ∧ IsPrincipalMod B a

/-- Step 10's hypothesis, for every coherent program, with the pipeline's inference (now
    inferProgramW, Lean definitions, end). -/
theorem d11For_of_coherent {p} (hc : coherentProg Btest p) : D11For Btest p

theorem mutualInstance_renaming {C0 a a'} (h1 : InstanceOf C0 a' a) (h2 : InstanceOf C0 a a') :
    ∃ r : Renaming, r.WF0 C0 ∧ (a.rename r).Equiv a'

/-- Legality without hypothesis, from the proved inference: what step 9's `legal_of_cert` gives
    under `PrincipalExistsFor`. -/
theorem legal_of_W {sp a} (hc : coherentProg Btest (bareOf sp))
    (h : inferProgramW wFuel Btest (bareOf sp) = .ok _ a) (hok : certOK Btest sp a = true) :
    LegalProgram Btest sp

/-- A96's correction 3 and the comment after r:p-stat-main-view: an unannotated main whose
    init is `\n -> (n + 1, Cmd.none)` has flags of class number in its principal scheme, which
    is not a port type. -/
theorem a96_number_flags : ¬ LegalProgram Stat.Btest s_elm_StandardA96NumberFlagsTest
```

Methods: `principalExistsCore`: existence from `inferExpW_terminates` and `inferExpW_fail`
(contraposed: if a derivation exists, `W` does not fail, and for some fuel it is not out of
fuel, so it is `ok`) and `inferExpW_principal`. `principalExistsMod_coherent` the same way with
L14 and L16. `d11For_of_coherent`: unfold `D11For` and the redefined `Stat.inferProgram`;
`inferProgramW_principal`. `mutualInstance_renaming`: L15 (step 10 proves the module version
first, `mutualInstanceMod_renaming`; this is the Core version, by the same argument).
`legal_of_W`: as step 9's `legal_of_cert`, with the principal derivation of each module given by
`inferProgramW_principal` instead of the hypothesis. `a96_number_flags`: the program is coherent
(no aliases) and `inferProgramW wFuel` gives its principal derivation (by `decide +kernel`, the
main scheme's flags type is a variable of class `num`); any principal derivation differs by a
renaming (step 10's `principalProg_rename`), and a renaming of a variable is a variable, which
`Port` excludes (Figure `fig:static-modules-port`); `Dflt σ` is `(Float, ...) Program`, not
`τ Node`; so neither `r:p-stat-main-program` nor `r:p-stat-main-view` applies, and `ElProgram`
has no derivation.

Then, mechanically, for every coherent test program: step 9's conditional `legal_X` is
regenerated as `legal_X : LegalProgram Btest s_X` by `legal_of_W` (with `by decide +kernel` for
`coherentProg`, the inference and `certOK`), and step 10's `ident_X`, `mean_X` are regenerated
without the hypothesis, applying `d11For_of_coherent (by decide +kernel)` (Translator changes,
item 3). `scripts/check-hypotheses.lean` lists the theorems whose statement mentions
`PrincipalExists`, `PrincipalExistsFor`, `InferPrincipalFor` or `D11For`; after (g) the list is
the general lemmas of steps 9 to 11 that take them as arguments and the per-test theorems of the
incoherent programs (expected none among compile-success tests; listed if any).

### Per-test refusal theorems

For each compile-error test `X` selected by a milestone (Tests gained), in
`Generated/Refuse<nn>.lean` (shards of 40):

```lean
/-- tests/<project>/src/<TestName>.elm (class inference, rule r:s-exp-app) -/
theorem refuse_X : ¬ Stat.LegalProgram Stat.Btest s_X :=
  Stat.notLegal_of_noElab (Stat.Complete.notStat_of_core Stat.Btest_wf (by decide +kernel))
  -- milestone (a); from (b) on, for tests (a) does not prove:
  -- Stat.notLegal_of_noElab (Stat.Complete.inferProgramW_fail Stat.Btest_wf
  --   (by decide +kernel) (by decide +kernel))       -- coherence, then the failure
```

`Stat.notLegal_of_noElab : (¬ ∃ τ PE, ElProgram B (bareOf s).modules τ PE) → ¬ LegalProgram B s`
is immediate from step 9's definition of `LegalProgram` (added in `Stat/Complete/Core.lean`).
The name `refuse_<project>_<TestName>` is step 9's for refusals, so that a compile-error test has
one theorem name whichever step proves it. A test proved by (a) keeps its (a) proof; later
milestones add theorems only for tests not yet proved.

## Translator changes

1. **Fragments in the classification.** The classifier of step 7 computes, for every entry of
   class `inference` or `fixity-inference`, the features of `Features` on the elm-syntax tree,
   resolving names by the imports as step 7 does and reading classes and record types from the
   schemes of `static-basis.json` (and of the program's own declarations), and writes a field
   `"fragment": "b" | "c" | "d" | "e" | "f"` and `"features": [...]`. `lake exe check-fragments`
   evaluates Lean's `fragmentOf` on `Src.deriveProgram s_X` for the same tests and prints
   `fragments: N agree, 0 differ`; a difference is resolved before the milestone that uses it.
2. **Refusal files.** A table `Translate/RefuseMethod.elm` maps a compile-error test to its proof
   (`core`, `w`, or none) and to `kernel` or `native`; the translator writes
   `Generated/Refuse<nn>.lean` with the theorems above and `Generated/All.lean` imports them. The
   manifest's entry of a compile-error test gains `refusal: {"step": 11, "milestone": "a",
   "method": "core", "proof": "kernel"}`.
3. **Milestone (g).** For every coherent test program (the list from `lake exe
   check-coherence`), the generated theorems of steps 9 and 10 are written without hypothesis:
   `legal_X : LegalProgram Btest s_X` by `legal_of_W`, and `ident_X`, `mean_X` applying
   `d11For_of_coherent`; an incoherent program keeps its conditional theorems and its
   `[principal]` tag. `--check` covers the change.
4. **The site.** `runner/mechanisation-data.js` shows the refusal theorem on a compile-error
   test's page with its tags (`[parse]`, `[harness]`, and `[native]` if so; the fixity test's page
   says the grouping is the point, step 7's 2.6); after (g), `[principal]` is no longer shown on
   any page, and the trust table's row says "retired by step 11".
5. **Unit tests** in `definition/tools/tests` for the feature computation (one program per
   feature) and the printing of a refusal shard.

## Tests gained

### Selection rules (from step 7's classification)

Let `Inf` be the compile-error tests whose class is `inference` or `fixity-inference`
(provisionally 217: 216 + 1). A test `X ∈ Inf` is proved:

- at **(a)** if `coreRefutes Stat.Btest (Src.deriveProgram s_X) = true` (evaluated for every test
  of `Inf` by `lake exe measure-cores`, which writes the list);
- at **(b)**, **(c)**, **(d)**, **(e)** if it is not proved earlier, its `fragment` is at most
  that milestone's letter, and `inferProgramW wFuel Stat.Btest (Src.deriveProgram s_X)` fails
  (it must, if the classification is right; a test where it succeeds is a finding: the program
  elaborates by the book, and the test or the classification is wrong, reported and moved out of
  `Inf` by the override table);
- at **(f)** every remaining test of `Inf` but StandardA96NumberFlagsTest;
- at **(g)** StandardA96NumberFlagsTest (its class is `inference`, but its refusal needs the
  principal derivation, not the absence of one): `refuse_elm_StandardA96NumberFlagsTest :=
  a96_number_flags`.

The fixity test InfixAssocRightConsAppendTest is proved like any other (its fragment decides the
milestone); its theorem is marked `[parse]` like every theorem, and its page says that the
grouping is the point.

### Estimated yield

From a scan of the 221 compile-error tests whose titles are type errors (a superset of step 7's
216; heuristics for integer literals, class operators, records and rows, annotations with
variables, helper modules): fragments `b` 9, `c` 110, `d` 41, `e` (annotations with variables,
with or without records) 60, `f` 1; and 170 of the 221 reference no unannotated binding outside
its own definition, for which `coreGen` is exact (so (a) refutes them if they are type errors at
all). Hence the estimates of the milestone table: (a) about 160; beyond (a), (b) about 1, (c)
about 25, (d) about 10, (e) about 13, (f) about 2, (g) 1. Each milestone's report replaces these
by the measured lists.

### Unit examples (`Stat/Complete/Examples.lean`, by `decide +kernel`)

- `meet_table`: the 25 entries of section 3 against `Adm` on a set of sample types (each
  `Class.meet κ κ' = some m` with `Adm m` equal to the intersection on the samples).
- `prop_table`: `Class.prop` for every class and every built-in type name of
  Figure `fig:static-core-builtin` plus `Bool`, `Maybe`, `Result`, `Array`.
- unification: `α_comp ≐ β_app` gives `γ_capp`; `α_num ≐ String` fails; `α_comp ≐ (Int, β) Tuple2`
  refines `β` to `comp`; `α_capp ≐ β List` refines `β` to `comp`; `α_app ≐ β List` leaves `β`
  `any`; a rigid `a_comp ≐ β_num` fails and `a_num ≐ β_comp` binds `β`; `α ≐ α → Int` fails
  (occurs); `⟨x : Int | ε⟩ ≐ ⟨y : Bool | ε'⟩` gives one fresh tail; A23:
  `⟨∅ | ε⟩ ≐ ⟨x : String⟩` with `⟨x : Int | ε⟩` in the frame fails (lacks); `⟨a : ⟨∅|ε⟩ | ε'⟩ ≐ ⟨∅|ε⟩`
  fails (occurs through rows).
- W: `\x -> x` gives `α → α`; `let id x = x in (id 1, id "s")` elaborates (let-polymorphism);
  A24's group (`f b = g b`, `g b = ... f False ...` using `f`'s result at two types) fails;
  A20's `f x = let g : a -> a; g y = x in g x` fails with `escape`; A21's nested `a` elaborates;
  `{ number | x : Int }` fails in `elabTy` (A36); A93's example gives `f` a scheme with the extra
  `num` variable; annotated polymorphic recursion `f : number -> Int -> Float` elaborates.
- principality, as theorems about small phrases: `id_principal`, `a93_principal` (every
  derivation of A93's example is an instance of `W`'s), using `inferExpW_principal` once (b),
  (e) land.

## Acceptance

Per milestone, the commands of [conventions.md](conventions.md), "Acceptance commands", with:

1. `lake build` with no `sorry` and no new warnings; `lake env lean scripts/check-axioms.lean`
   clean (refusal theorems by `native_decide` listed).
2. `lake exe run-examples` prints its check line with `N` and `K` unchanged, and the refusal
   line (introduced by step 8 or 9, extended here):

   ```
   Refusals: R of 311 compile-error tests proved (Rk by decide +kernel, Rn by native_decide):
     syntactic 31, further 9, static-deterministic D, inference I, fixity-inference F.
   ```

   with `I + F` growing by the milestone's measured yield; the report lists the tests added.
3. `lake exe measure-cores` (at (a)) and `lake exe check-fragments` print their lists and
   `0 differ`.
4. The memory budget on a clean build (refusal programs are small; any test over budget is
   `native_decide` and listed).
5. Translator `--check` up to date; elm-test passes; `pnpm test:all`, `check-baseline` unchanged;
   site data, site build, link audit at 0 problems.
6. The mechanisation report gets a dated block per milestone (what was proved, the lemmas, the
   counts, the fragment numbers, the estimates replaced by measurements); the plan's status line.

At (g) also:

7. `scripts/check-hypotheses.lean` prints only the expected names (Discharge, last paragraph);
   `lake exe check-coherence` prints the incoherent test programs (expected: none among the
   compile-success tests; each one found is reported as an instance of step 9's finding).
8. Every `inference` and `fixity-inference` test has a refusal theorem (`I + F = 217` or step 7's
   final number), except tests the override table moved, each with its reason.
9. The trust table of the plan, the README and the report mark `[principal]` retired (except
   for incoherent programs, listed); no other test page shows it; the preface sentence says what
   is encoded.

## Risks and fallbacks

- **(a) yields less than estimated.** Strengthen the generator after (b) and (c) give the mgu:
  *ground propagation*: when the constraints of an unannotated group alone have a most general
  unifier that makes a member's type ground, every derivation gives it that type (mgu
  factorisation), so its occurrences may use it exactly. This needs `unifyF_ok`, not
  principality of W.
- **A milestone of (b) to (e) stalls.** Its tests are proved by (a) where possible; the
  remaining ones by hand inversion (per test, `cases` on the static relations through a small
  library of inversion lemmas, one per rule), listed; the milestone's theorems are kept with
  their fragment hypotheses, which is a correct, weaker result.
- **(e) stalls on annotated members inside groups or on A93.** Restrict F_e to programs without
  annotated members in groups of several members (a feature already computed), and state the
  closure lemma L3 without the A93 extras first (they are vacuous for typing; they matter only to
  step 10's specialisation, through the closed set, which is computed from `C` and `VE`).
- **(f) stalls on type declarations or node correspondence.** Single-module programs need only
  L14's soundness and the equivariance L16 for refusals (any choice of names); module
  principality can be stated for modules without type declarations first, which covers the
  compile-success tests with no custom types or aliases.
- **(g) cannot remove the hypothesis everywhere.** Discharge it per fragment: `d11For` for the
  coherent programs of fragment `f` (`d11For_of_frag f`), proved at each milestone from W's
  principality for that fragment, and the generated theorems of the tests in that fragment drop
  the hypothesis; the rest keep `[principal]`, listed. Incoherent programs keep it in any case
  (the book gives them no principal derivation).
- **Kernel cost of W.** Refusal programs are small; the 622 positive programs at (g) run W in
  the kernel inside step 10's `spec_` theorems, which may cost more than step 9's inference.
  Fallbacks of step 10 (native, certificates); or keep `Stat.inferProgramFast` in the pipeline
  and prove per test that its result is a renaming of `inferProgramW`'s (a decidable comparison,
  run natively if needed).
- **Lean core limits.** No Mathlib: finite sets as lists with `Nodup`, `List.Perm` for
  permutations; well-founded induction from `WellFounded` and `Prod.Lex` in core. Mutual
  structural recursion over the bare phrase types (as `Eval.lean` does over the reduced ones).

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **D11's hypothesis cannot be discharged as the plan states it.** The plan says "Step 11
   proves `PrincipalExists` and removes the hypothesis". (a) `PrincipalExists` is false as the
   book stands: step 9 ("Issues with the plan", item 1) exhibits a module with two incomparable
   derivations (`r:sm-topdec-seq` splitting a type-declaration phrase). This step proves the
   Core's property and the module property for coherent modules (section 9), which is the most
   that holds until the book restricts `r:sm-topdec-seq`. (b) Step 9's per-program instance
   `PrincipalExistsFor p` quantifies over every basis, and a contrived basis (one whose `Basics`
   exposes a type named like a local alias that a custom type of the module mentions, an ordinary
   pattern) makes the same split possible; so it is false for many ordinary programs, the
   theorems of step 9 under it are vacuous for them, and this step cannot discharge it. This step
   therefore re-proves step 9's `legal_` theorems without hypothesis from the proved inference
   (`legal_of_W`, in the test basis only), and discharges step 10's `D11For Btest p` (the
   per-basis form; step 10, "Issues with the plan", item 1). Step 9 should state its conditional
   theorems under the per-basis form too (`PrincipalExistsIn Btest p`: principal derivations
   exist in the bases `r:p-stat-module` builds from `Btest`).
2. **Node correspondence for modules** (finding B5): with `r:sm-topdec-seq`, two derivations of
   a module need not have the same nodes, and the contexts at the type declarations differ. Step
   9's `nodesModule` fixes the correspondence; with it, principality holds exactly for coherent
   modules (section 9). The book should both say which nodes correspond and restrict
   `r:sm-topdec-seq` so that the property holds (step 9's proposal).
3. **Explicit variables cannot be "renamed apart".** `sec:static-core-principal` renames the
   variables of one derivation apart from the other's, but explicit variables are named by the
   syntax (`sec:static-core-simple`), so the variables of `U` are the same in both derivations
   and the instance substitution fixes them. Harmless for the property, but the book's sentence
   should exempt the explicit variables (for the ambiguity log).
4. **Step 7's classification has no fragment.** The plan (and this step's brief) count the tests
   of milestone (b) "by step 7's classification", but step 7 classifies by rule and by proof
   class only. This specification adds the field (Translator changes, item 1) with a Lean
   counterpart; if step 7 is still open, the field belongs there.
5. **Most refusals do not need complete inference.** The plan's inventory says the type errors
   "need complete inference (step 11)". By the scan, most are refuted by milestone (a), which
   needs only that constraint generation is complete for derivations and that unification fails
   soundly: no principality, no completeness of W, and no hypothesis. The plan could say that
   step 11 delivers most refusals early, unconditionally.
6. **Milestone (g) depends on step 10.** The plan's dependencies say "11 needs 9". Milestones
   (a) to (f) do; (g) removes step 10's hypotheses and redefines the inference of step 10's
   pipeline, so it needs step 10.
7. **Step 9's substitution does not always refuse a repeated label** (found 2026-11-12, milestone
   (d)). A23 makes a substitution undefined where it would give a record a label twice. Step 9's
   `Subst.apply` merges the bound row into the record with `Row.merge`, which catches a shared label
   only where the two rows meet it head to head; on unsorted rows (which instance lists may hold)
   merging `[a]` into `[c, a]` succeeds and gives `[a, c, a]`. The proofs of milestone (d) carry the
   weaker definedness the encoding has (`MOK`, `Stat/Complete/WDNodeDef.lean`), so no theorem is
   affected; the encoding should check disjointness (or keep rows sorted) to match A23.
   (2026-11-12: step 9's checker now asks every type at every node to have sorted rows, so a
   checked derivation never holds such a row; `Row.merge` itself and instance lists are
   unchanged.)
8. **Status of the milestones (2026-11-12).** (a) done: 200 of the 217 inference tests refuted
   unconditionally (`coreRefutes`), none of the 625 compile-success tests. (b), (c), (d) done at
   expression level: W for Hindley–Milner, with classes, and with records and rows is sound,
   refuting, complete, principal (with a bridge to step 9's `IsPrincipal` over derivations without
   free `bnd` variables and with canonical rows) and terminating; W with records is a separate
   function `inferExpWD`. (e) under way (see item 10). Top-level annotations with type variables, module-level W,
   the per-test refusals that need it, and (g) remain. Every module is coherent since ruling A98, so
   section 9's coherence is not needed.
9. **The kind of an explicit variable is not fixed by the rules** (found 2026-11-12, milestone (e)).
   `sec:static-core-explicit` says that whether a name of `U'` stands for a type or a row variable
   "is fixed by the rules for type expressions, which accept only variables of `U of C`". It is
   fixed only for a name used as the extension variable of a record type (`{ r | ... }`, rule
   `r:s-ty-openrecord`). A name used only as a type (`f : a -> a`) elaborates with `a` a type
   variable (`r:s-ty-tyvar`) and with `a` a row variable (`r:s-ty-rowvar`, `{ | a } -> { | a }`), and
   `f x = x` checks both ways; the two derivations are not instances of each other (an instance maps
   a type variable to a type variable), so `let f : a -> a; f x = x in f` has no principal
   derivation, and the order and repetitions of `U'` are free too (the checker records the list).
   The book should say that a name of `tyvars ty` denotes a row variable exactly when it is used as
   an extension variable in `ty` (A19/A36's convention); a nested annotation that uses an outer
   name as an extension (`f : a -> Int` with an inner `{ a | foo : Int }`) is then refused. W takes
   that reading (`WE.newU`). *Resolved (2026-11-12):* the book now says so (erratum in
   `sec:static-core-explicit`), the relation's `NewFor` asks every name to stand for the variable
   of its kind (`nameVar`), and step 9's checker asks for exactly `newU` (`newForB`); the checker
   also asks every type of a derivation to have canonical rows and no free `bnd` (`okExpB`), so
   the hypotheses `NoFreeBndExp`, `CanonExp` and `WE.CanonAnnExp` follow from `checkExp` and are
   gone from every theorem of milestones (b) to (e) (`noFreeBndExp_of_checkExp`,
   `canonExp_of_checkExp`, `WE.canonAnnExp_of_checkExp`, `Complete/CheckedDeriv.lean`).
10. **Milestone (e) status (2026-11-12).** W for F_e (`WE.inferExpWD`, Stat/Complete/WE*.lean, in
   namespace `WE` beside the (d) chain, which is unchanged): sound by construction, terminating,
   the main induction L11, refutation (`WE.weRefutation`), completeness but for the `internal`
   clause, and L12 (`WE.inferExpWD_instance`). Remaining: (i) principality in the form of
   `WDPrincipality`, by porting WDNodeRelExp/WDNodeOk/WDPrincipality into namespace `WE.WDP`:
   replace `NRelD T U0` (one `U` for every node) by a relation asking only that `T` fix each node's
   `U` (inside an annotated member `U` is `U ∪ U'`); replace `AnnNilV` by "annotated members carry
   W's variables and have types over named variables" (W's result has it: `WE.annMark true`
   marks a type that is not); and prove `SchInstD T (closE A VE σ) (closE A' VE' σ)` for an
   annotated member's scheme `σ` (the declaration node; `WE.closE_relAnn` is the `SchRelD` form,
   used by the `let` case of L11); (ii) the `internal` clause, L10 relative to a derivation: the
   escape condition under the final substitution (the (d) soundness chain's `DeadC` covers only
   fresh variables, and the explicit variables are named). Fragment F_e: 216 of the 217
   inference tests (12 beyond F_d; 17 of them not refuted by milestone (a)); at expression level W
   refuses the six rigid-`let` tests (1639, 1839, 2001, 2077, 2296, 2301) by the escape check
   (`WEExamples.lean`); their per-test refusals need module-level W (milestone (f)).
   *Update (2026-11-12, later):* (i) is done. `WE.wePrincipality : WEPrincipality`, and
   `WE.inferExpWD_principal` gives W's result principal in step 9's sense (`IsPrincipal`, via
   `isPrincipalE_iff`), in WENodeRel.lean, WENodeRelExp.lean and WEPrincipality.lean (namespace
   `WE.WDP`; the (d) chain unchanged). The node relation asks `T` to fix each node's `U` (`NRelE`;
   inside an annotated member `U ∪ U'`, named, hence rigid); annotated members carry W's variables
   over named variables (`AnnOKV`); an annotated member's scheme clause is `closE_instAnn`, from
   `gen_rn_sub` (the derivation's closure generalises fewer of the scheme's variables, since a
   variable free in W's context is free in the derivation's); a `let` body's contexts are related
   by `closE_relAnnE`. (ii), the `internal` clause, remains: the (d) soundness chain does not port,
   because its segment invariant `MovesD (Reach θ C n)` is false for F_e (in `let f : a -> a; f x
   = x in f` W binds the fresh type of `x` to the explicit `a`, which the declaration's context does
   not reach). L10 for F_e needs L6 as an invariant of the soundness induction (named variables in
   the images of returned types are explicit in the context, kept by the escape checks), group
   environments with annotated schemes in the closure commutation, and the escape condition under
   the final substitution relative to a derivation. No test yield depends on it: a refusal needs
   W's `.fail` (refutation, proved) and a positive theorem needs W's `.ok` (soundness and
   principality, proved); the clause only says W never stops with `.internal` where a derivation
   exists.
11. **Milestone (f) status (2026-11-12).** Module- and program-level W (`MW.inferModuleW`,
   `MW.inferProgramW`, Stat/Complete/Modules*.lean) elaborates a module's type declarations whole,
   as ruling A98 requires (`solveTypes`, kept only if step 9's `checkTypes` accepts it and the
   phrase is ordered), and its top-level groups as one nested `let` with milestone (e)'s W.
   Refutation (`inferModuleW_fail`, `inferProgramW_fail`, `Stat.not_legal_of_wRefutes`) and
   principality (`inferModuleW_principal`, `inferProgramW_principal`) are proved without
   hypotheses. Differences from the statements above: no coherence hypotheses (every module is
   coherent since A98, and `typesSplit` is gone, so `coherentIn`, `coherentProg` and
   `topdecTypes_seq_coherent` are dropped); no `solveTypes_sound`/`solveTypes_complete` (soundness
   is by construction through `checkTypes`; L14 is `types_bij`, two solutions differ by a bijection
   of type names fixing the basis, from step 10's `Swap.extend_pairs` and `checkTypes_unique`);
   module failure is stated as `NoDeriv` (no checked derivation). The 15 remaining inference tests
   are refused by the kernel (`decide +kernel`), so 284 compile-error tests are refused and only
   StandardA96NumberFlagsTest (milestone (g)) is not. `lake exe measure-w`
   (`definition/mechanisation/w-report.json`): W refutes none of the 624 compile-success tests it
   can run (CompilerIssue2281LongLineListTest, a list of 22,000 elements, exceeds the memory budget
   even compiled) and returns `.ok` on 585 of the 622 legal programs. The 36 with ports return
   `.unsupported`: ports are not yet in module-level W (to do for (g): a port as an annotated group
   `x : ty; x = x` in the nested `let`, with lemmas that the group's closed scheme is the port
   rule's).
12. **Milestone (g) status (2026-11-13).** Ports are in module-level W as the annotated group
   `x : ty; x = x`, kept only when its closed environment equals the port rule's (the port's node
   is the same in every derivation: contexts at the top of a module are closed and `newForB` fixes
   `U`; `ModulesPorts.lean`); where W fails on a module with a port it answers `.unsupported`, so
   no refutation is claimed there (none is needed). W returns `.ok` on 621 of the 622 legal
   programs; on CompilerIssue2281LongLineListTest (a list literal of 22,000 elements) compiled W
   gave no result within two hours, so that test's `legal_` keeps step 9's form under D11 and is
   the only per-test theorem tagged `[principal]` (`wSkip` in Certify.lean).
   D11 is discharged per test without redefining step 9's inference (W's definitions import
   `Principal`/`Ident`, so that would be an import cycle): `Stat.wCheck B s q` runs W, Chapter 9's
   conditions, the further restrictions and the specialisation, and `legal_of_W`, `ident_of_wCheck`
   and `programSem_of_wCheck` (`Stat/Complete/Discharge.lean`) give `legal_`, `ident_` and `mean_`
   without hypothesis from a per-test `wcheck_X`. `spec_` is unchanged (step 9's pipeline), so
   compare-e2e still agrees on 579. Differences from the statements above: no
   `d11For_of_coherent` (the pipeline is not redefined; `d11For_of_agree` gives D11For wherever
   step 9's inference returns W's result), and `principalExistsCore`/`principalExistsMod` are
   proved only from W's coverage (`principalExistsCore_of_covers`, `principalExistsMod_of_covers`);
   unconditional versions need the `internal` clause of item 10, W's coverage of what it answers
   `.unsupported` (pattern bindings in groups, ambiguous contexts, aliases with free variables),
   and bases and contexts outside `BasisInv`/`RootOKD`. A96's flags refusal:
   `not_legal_of_wMainVar` (W's `main` is a worker whose flags type is a variable; every principal
   derivation is W's up to a bijection of type names, `MStep.moduleStep`, which keeps a variable a
   variable, and `Port` has no case for one; the view rule needs `τ Node`); 285 compile-error tests
   refused, none left. Kernel cost: W costs two to four times step 9's inference, so the 15 W checks
   over 6.3 GB use `native_decide` (`wBudgetNative`), and `spec_elm_WideRecord40Test` joins the
   `spec_` natives (5); CertsAll takes about 1 h 50 min serially, peak 6.11 GB per shard.
   `scripts/check-hypotheses.lean` lists 1 per-test theorem (2281's `legal_`) and 13 general
   lemmas taking D11 as an argument. Afterwards the translator was found not to have written the
   two tests of ruling A98, and to resolve a built-in type name before a module's own alias (against
   A98); with that fixed (`Translate/Infer.elm`): 623 `legal_`, 286 `refuse_` (the A98 mismatch test
   by the core refutation, 201), 580 `spec_`/`ident_`, 578 `mean_`; W gives a derivation for 622 of
   the 623 legal programs.
