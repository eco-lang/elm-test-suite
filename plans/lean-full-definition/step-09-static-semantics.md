# Step 9: the static semantics, by certificate

Part of [the plan](../lean-full-definition.md), Part II. Follows
[conventions.md](conventions.md). Status: specified 2026-11-11; done 2026-11-12, with these
differences from this specification:

- **Accepted.** 9a to 9c: 622 `legal_` theorems (613 of one module, 9 of several), each by the kernel
  running the inference and the checks (`legal_of_infer1`, `legal_of_infer`), not by a written
  certificate `a_X`; under `InferPrincipalFor` the inference's derivation is the principal one, so
  `mainTransfer`, `CertProgram` and `cert_` theorems are not needed. 9 programs break the memory
  budget in the kernel (7 GB to more than 40 GB) and are proved by `native_decide` (`staticBudgetNative` in
  `Certify.lean`). 9d: 68 `refuse_` theorems, all unconditional, by deciders proved sound
  (`Stat/Refuse*.lean`) instead of Group 8's `not_legal_of_scope/shape/main/ports`: 31 syntactic, 1
  imports, 6 scope (`scopeFailB`), 13 type expressions and ports (`typesFailB`), 8 `main`
  (`mainFailB`), 9 further restrictions (`furtherFailB`).
- **Not proved in the form stated here** (none is needed by a theorem above): the adequacy of the
  checker (`checkExp_adequate`, `checkModule_adequate`), `check_subst`, `adm_subst`,
  `canon_eq_iff`, `gen_trans`, `closGroup_extra`, `instance_refl`, `covers_depth`, `extend`,
  `head_forced`, the `iff` forms of Group 7 (only soundness) and of the further decider
  (`further_correct`, `further_invariant`, `furtherMod_correct`, `furtherMod_rename`),
  `elabTypes_complete`, `annotated_main_scheme`, `forcedHead_sound`, `ports_det`, `uses_bound`,
  `elab_basis_mono`, and Group 10 (stretch). Section 14's names (`Stat/Interface.lean`) are left to
  step 10, which adds those it uses.
- **Changed 2026-11-12 (ruling A98, option (c) of step 10's issue 9):** `r:sm-topdec-seq` no longer
  splits a type-declaration phrase, so `r_sm_topdec_seq_types` and `ATopDec.typesSplit` are gone
  (19 constructors for Chapter 5's 19 labels: 45 + 19 + 3); this specification's mentions of them,
  and of 20 constructors, describe the earlier encoding. Issue 1 below is resolved that way.

## Goal

Encode Chapters 4 and 5, the static half of Chapter 9 and Appendix C, and prove legality and
refusals by certificate (decision D10), without principal derivations where the plan allows
(D12) and under the per-program hypothesis `InferPrincipalFor` where it does not (D11):

1. The static objects as Lean types (G2-2): classes, type and row variables, type names with
   arity and generation, types with rows kept canonical, schemes with A93's vacuous `number`
   variables kept, type functions, environments, contexts with `U`, interfaces, provider maps,
   bases.
2. Partial substitution and admissibility, with the book's property (G2-3).
3. The rules as `Prop` relations, one constructor per rule: 45 (Chapter 4), 19 (Chapter 5), 3
   (Chapter 9).
4. Annotated phrases and a checker, proved sound and adequate (D10); instances and principal
   derivations defined on annotated phrases, with node correspondence, for the Core and for
   modules (with the bijection on generated type names); the book's properties
   `PrincipalExistsCore` and `PrincipalExistsMod` as definitions, and D11's hypothesis
   `InferPrincipalFor`.
5. The static half of the test basis `B_test` (D2, G2-14), and the static `ME0` generated from
   step 7's `static-basis.json`.
6. An inference written in Lean, not proved, producing annotated phrases: classes and rows,
   rigid explicit variables (G2-5), generalisation with A93 (G2-6), the fixed point of
   `r:sm-topdec-types` (B5).
7. The pattern decider of D12: literal columns by denotation, `IntRange` as a parameter (B2),
   proved correct against coinductive inhabitants encoded as position maps (G2-12), and the
   principality-free invariance lemma.
8. Refusals without inference (P2-13): names no derivation binds, type-expression errors,
   module-level deterministic failures, and a wrong `main` type fixed by an annotation.
9. Per test: `legal_...` (under `InferPrincipalFor`) for compile-success tests, `refuse_...`
   (unconditional) for the `further` and `static-deterministic` compile-error tests.

Milestones, in order: **9a** the Core alone; **9b** modules and programs of one module;
**9c** programs with helper modules; **9d** the refusals. Each is accepted on its own.

## Prerequisites

- **Step 8**: `Src/Syntax.lean`, `Src/Bare.lean`, `Src/Derive.lean` (`deriveProgram`,
  `canonOrder`), `Src/Restrictions.lean` (`SynOK`, `SynOKSet`, `decSynOK`, `basisModuleIds`,
  `managersPlat`), the Generated source shards `s_<project>_<Test>` and `srcShards`.
- **Step 7**: `static-basis.json` (for the generated static basis) and
  `static-classification.json` (the target sets and the `main`/`mainAnnotated` columns).
- **Step 2** (Part I), the interface this step needs (decision D2):
  - the list of the core library modules and values that `B_test` contains, as a Lean value
    `StandardElm.Mod.libraryValues : List (ModId × List Var)`, and the vendored elm/core 1.0.5
    sources it reads them from (`definition/library/elm-core-1.0.5/`, as
    [core-library.md](../core-library.md) lays it out);
  - the harness's name `text` in `Html` and its intended scheme `∀msg. String -> msg Node`.

  If step 2 has not landed when 9b starts, this step defines `libraryValues` itself in
  `Stat/TestBasis.lean` with at least the 23 values step 7 measured (section 3.2 of
  [step 7](step-07-classify.md)), and step 2 must import it from there; a `#guard` in step 2's
  test file then checks that the dynamic and static lists are equal.
- Existing: `StandardElm.norm`, `intMin`, `intMax` of `Objects.lean` (IntRange as eco's,
  `[params]`).

## Lean definitions

New files in `StandardElmMech/Stat/`, namespace `StandardElm.Stat`, without `import Lean`
except `Stat/Certify.lean`:

| File | Contents | Milestone |
|------|----------|-----------|
| `Stat/FMap.lean` | finite maps as association lists sorted by key | 9a |
| `Stat/Objects.lean` | section 1 | 9a |
| `Stat/Subst.lean` | section 2 | 9a |
| `Stat/Schemes.lean` | `Gen`, canonical forms, `Clos`, explicit variables | 9a |
| `Stat/Rules.lean` | the 45 rules of Chapter 4 | 9a |
| `Stat/Modules.lean` | `Expose`, provider maps, `Port`, the 19 rules of Chapter 5 | 9b |
| `Stat/Program.lean` | `Dflt`, the 3 rules of Chapter 9, `LegalProgram` | 9b |
| `Generated/StaticBasis.lean` | `T0`, `E0`, `ME0`, `OTstat`, `smops`, hidden constructors, default imports (generated) | 9a |
| `Generated/StaticLibrary.lean` | the annotations of the library values (generated) | 9b |
| `Stat/TestBasis.lean` | `B0stat`, the harness, `Btest`, their lemmas | 9b |
| `Stat/Annotated.lean` | annotated phrases, `erase`, the checker | 9a, 9b |
| `Stat/CheckSound.lean`, `Stat/CheckAdequate.lean` | soundness and adequacy | 9a, 9b |
| `Stat/Principal.lean` | nodes, `InstanceOf`, `IsPrincipal`, the book's properties, `ProgDeriv`, `PrincipalProgDeriv`, `InferPrincipalFor` | 9a, 9b |
| `Stat/Patterns.lean` | constructor tables, inhabitants, `Covers`, the decider, its correctness | 9a |
| `Stat/Further.lean` | the further restrictions on annotated phrases, invariance | 9a |
| `Stat/Deterministic.lean` | `elabTy`, `elabImports`, `expose`, `elabTypes`, ports: functions with iff theorems | 9b |
| `Stat/Refusals.lean` | the lemmas of section 8 | 9d |
| `Stat/MainType.lean` | `forcedHead`, `mainTransfer`, annotated `main` | 9b |
| `Stat/Legal.lean` | `legal_of_cert`, `cert_of_check`, the refusal theorems | 9a to 9d |
| `Stat/Unify.lean`, `Stat/Infer.lean` | the unverified inference | 9a, 9b |
| `Stat/Independence.lean` | B4 for elaboration: statement, proof as a stretch goal | 9a |
| `Certify.lean` (package root) | the executable `certify` that writes `StandardElmMech/Certs/` | 9a |
| `StandardElmMech/Certs/<Project><nn>.lean` | certificates and per-test theorems (written by `lake exe certify`) | 9a to 9d |

### 1. Objects (`Stat/Objects.lean`, Sections `sec:static-core-simple` to `sec:static-core-compound` of `static-core.tex`, `sec:static-modules-objects` of `static-modules.tex`)

```lean
namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-- Class (sec:static-core-classes). -/
inductive Cls where | any | num | comp | app | capp
  deriving DecidableEq, Repr
/-- The least partial order with num ≤ comp, capp ≤ comp, capp ≤ app, κ ≤ any. -/
def Cls.le : Cls → Cls → Bool
/-- The greatest common lower bound, if any (num ∧ comp = num, app ∧ comp = capp,
    num ∧ app = none, num ∧ capp = none). -/
def Cls.meet : Cls → Cls → Option Cls
/-- A19: the class a type variable of the syntax names, by its prefix. -/
def classOfName (s : String) : Cls

/-- Type variables. `named s` is the one variable the syntax name `s` names (its class is
    `classOfName s`); `fresh n c` any other free variable; `bnd i c` a bound variable of a
    canonical scheme, never free in a sentence. -/
inductive TyVar where
  | named (s : String)
  | fresh (n : Nat) (c : Cls)
  | bnd (i : Nat) (c : Cls)
  deriving DecidableEq, Repr
def TyVar.cls : TyVar → Cls
/-- Row variables (no class). `named s` exists for every `s`, but the rules name it only when
    `classOfName s = .any` (A36). -/
inductive RowVar where
  | named (s : String) | fresh (n : Nat) | bnd (i : Nat)
  deriving DecidableEq, Repr
/-- tyrowvar: a type or a row variable. -/
inductive BVar where
  | ty (a : TyVar) | row (e : RowVar)
  deriving DecidableEq, Repr

/-- Type names (fig:static-core-simple): an identity and an arity. T0's 22 names have ids 0 to 21
    in the order of fig:static-basis-tynames (Generated/StaticBasis.lean); the type names a
    derivation generates are any others (the inference uses ids from 1000 up). -/
structure TyName where
  id : Nat
  arity : Nat
  deriving DecidableEq, Repr

/-- Types (fig:static-core-compound). A row is a list of fields sorted strictly by label, so that
    equal rows are equal lists (A23: no label twice). -/
inductive Ty where
  | var (a : TyVar)
  | rec (row : List (Lab × Ty)) (tail : Option RowVar)   -- {ρ} when tail = none, {ρ | ε}
  | fn (t1 t2 : Ty)
  | con (args : List Ty) (t : TyName)                    -- τ(k) t, k = t.arity
abbrev Row := List (Lab × Ty)
def labLt (a b : Lab) : Bool                              -- the order of rows
/-- Well formed: every row strictly sorted by `labLt`, recursively; every `con` has as many
    arguments as its name's arity. Every function below maps well-formed objects to well-formed
    objects (lemma per function). -/
def Ty.wf : Ty → Bool
/-- The book's `ρ + ρ'` (modification), sorted. -/
def Row.modify (ρ ρ' : Row) : Row
/-- ρ ⊆ ρ' as finite maps. -/
def Row.Sub (ρ ρ' : Row) : Prop

inductive IdStatus where | c | v
  deriving DecidableEq, Repr

/-- A type scheme ∀tyrowvar(k).τ. Canonical when its bound variables are `bnd 0, bnd 1, ...` in
    order of first occurrence in `body` (preorder, left to right), with the vacuous ones deleted
    except those of class num, which are kept after the others (A93, sec:static-core-schemes). -/
structure Scheme where
  bound : List BVar
  body : Ty
  deriving DecidableEq, Repr
def Scheme.canon : Scheme → Scheme
def mono (τ : Ty) : Scheme := ⟨[], τ⟩

/-- A type function Λtyrowvar(k).τ: parameters in order (application is positional), canonical
    when they are `bnd 0 .. bnd (k-1)`, type parameters of class any ("the class of a bound type
    variable of a type function has no significance"). -/
structure TyFcn where
  params : List BVar
  body : Ty
def TyFcn.canon : TyFcn → TyFcn
def TyName.toFcn (t : TyName) : TyFcn       -- Λα(k).α(k) t

abbrev ValEnv := FMap String (Scheme × IdStatus)      -- Var ∪ Con
abbrev TyStr := TyFcn × ValEnv
abbrev TyEnv := FMap String TyStr
/-- An interface, and every environment in the range of a qualified environment: QE empty. -/
structure IEnv where
  TE : TyEnv
  VE : ValEnv
structure Env where
  QE : FMap ModId IEnv
  TE : TyEnv
  VE : ValEnv
/-- C = T, U, E. U is a list read as a set. -/
structure Ctx where
  T : List TyName
  U : List BVar
  E : Env

abbrev ModEnv := FMap ModId IEnv
inductive Dir where | out | inn
abbrev PortEnv := FMap Var (Dir × Ty)
/-- A static basis B = T, ME, PE. -/
structure SBasis where
  T : List TyName
  ME : ModEnv
  PE : PortEnv
/-- smId and smLongId (sec:static-modules-objects): the value and type name spaces are disjoint. -/
inductive SmId where | val (x : String) | ty (c : String)
structure SmLongId where
  qual : Option ModId
  id : SmId
/-- A provider map: each identifier to its non-empty set of providing modules. -/
abbrev ProvMap := List (SmLongId × List ModId)
```

Operations, all total functions on these types: `Ctx.plusVE`, `Ctx.plusU`, `Ctx.oplusTE`
(`C ⊕ TE`: `T` extended by `tynames TE`), `Ctx.oplusE`, `Env.plus`, `SBasis.plus` (the set
component by union, the maps by modification, `programs.tex`, `sec:programs-elaboration`);
`Ty.tyvars`, `Scheme.tyvars` (free: never a `bnd`), `ValEnv.tyvars`, `Env.tyvars`,
`Ctx.tyvars := C.E.tyvars ++ C.U` (`static-core.tex`, `sec:static-core-compound`);
`tynames` on every object; lookups `Ctx.lookupVal : Ctx → LongId → Option (Scheme × IdStatus)`
and `Ctx.lookupTy : Ctx → LongId → Option TyStr` through `QE` for a qualified identifier
(`sec:static-core-projection`).

Built-in types: `tUnitTy := .con [] tUnit`, `listTy τ := .con [τ] tList`,
`tupleTy τ1 τ2 τ3o`, `tIntTy`, `tFloatTy`, `tCharTy`, `tStringTy`, from the generated names.

### 2. Substitution and admissibility (`Stat/Subst.lean`, `sec:static-core-classes`, `sec:static-core-types`)

```lean
/-- A simultaneous substitution {τ(k)/tyrowvar(k)}: a row variable is mapped to a record type,
    given as its row and tail. -/
structure Subst where
  ty : List (TyVar × Ty)
  row : List (RowVar × (Row × Option RowVar))
def Subst.dom (S : Subst) : List BVar
/-- τ{·}: undefined (none) exactly when, where a row variable is replaced, the row it extends and
    the row it is replaced by share a label (the condition after the table of
    sec:static-core-types). -/
def Subst.apply (S : Subst) : Ty → Option Ty
def Subst.applyScheme (S : Subst) : Scheme → Option Scheme   -- bound variables are bnd, never in dom S
def Subst.applyVE (S : Subst) : ValEnv → Option ValEnv
/-- fig:static-core-admissible. Adm comp is the least set satisfying its equation, hence an
    inductive predicate. -/
inductive Adm : Cls → Ty → Prop
def adm : Cls → Ty → Bool
def Subst.Respects (S : Subst) : Prop := ∀ a τ, (a, τ) ∈ S.ty → Adm a.cls τ
/-- Defined on every type of a list (used by "instance of"). -/
def Subst.DefinedOn (S : Subst) (ts : List Ty) : Prop := ∀ τ ∈ ts, (S.apply τ).isSome
```

### 3. Schemes, closure, explicit variables (`Stat/Schemes.lean`)

```lean
/-- σ ≻ τ (sec:static-core-schemes): τ is σ's body with its bound variables replaced by a list
    of types (record types for row variables) that is defined and respects classes. The list is
    the "instance" the annotated phrases record. -/
def instSubst (σ : Scheme) (ts : List Ty) : Subst
def Gen (σ : Scheme) (τ : Ty) : Prop :=
  ∃ ts, ts.length = σ.bound.length ∧ (instSubst σ ts).Respects ∧ (instSubst σ ts).apply σ.body = some τ
/-- σ ≻ σ'. -/
def GenS (σ σ' : Scheme) : Prop := Gen σ σ'.body ∧ ∀ v ∈ σ'.bound, v ∉ σ.tyvars
/-- type(scon) (sec:static-core-schemes): ∀α.α with α of class num for an integer constant. -/
def typeOf : Src.SLit → Scheme

/-- Clos_A σ (sec:static-core-closure). -/
def closScheme (A : List BVar) (σ : Scheme) : Scheme :=
  Scheme.canon ⟨σ.bound ++ σ.tyvars.diff A, σ.body⟩
def closVE (A : List BVar) (VE : ValEnv) : ValEnv     -- r:sm-datbind, r:sm-typbind-record, ports
/-- The closure of a group of value bindings (r:s-dec-group, r:sm-topdec-value): each scheme is
    closed also over the type variables of class num in tyvars VE \ (tyvars σ ∪ A), which are
    kept although vacuous (A93, G2-6). -/
def closGroup (A : List BVar) (VE : ValEnv) : ValEnv :=
  VE.map fun σis =>
    let extra := (VE.tyvars.diff (σis.1.tyvars ++ A)).filter BVar.isNumTyVar
    (Scheme.canon ⟨σis.1.bound ++ σis.1.tyvars.diff A ++ extra, σis.1.body⟩, σis.2)

/-- names U, unambiguity, "new for ty in C" (sec:static-core-explicit). -/
def namesU (U : List BVar) : List String          -- the s of each named member
def Unambiguous (U : List BVar) : Prop := (namesU U).Nodup
def NewFor (U' : List BVar) (ty : Src.BTy) (C : Ctx) : Prop :=
  (∀ v ∈ U', v.isNamed) ∧
  (∀ s, s ∈ namesU U' ↔ s ∈ ty.tyvars ∧ s ∉ namesU C.U) ∧
  Unambiguous (C.U ++ U')
/-- The scheme an annotated binding gets: ∀U'.τ, canonical. -/
def annScheme (U' : List BVar) (τ : Ty) : Scheme := Scheme.canon ⟨U', τ⟩
```

`Scheme.canon` makes scheme equality the book's (renaming, reordering, deletion of vacuous bound
variables other than A93's): lemma `canon_eq_iff` in section "Theorems". Schemes in every
relation are compared after `canon`; every function producing a scheme returns a canonical one.

### 4. The rules of Chapter 4 (`Stat/Rules.lean`, `static-core.tex`, `sec:static-core-rules`)

Three mutual blocks, in dependency order. Options and sequences are auxiliary relations with
constructors `opt_none`, `opt_some`, `seq_nil`, `seq_cons` (conventions). Free variables of
constructors are implicit.

```lean
mutual
/-- C ⊢ ty ⇒ τ -/
inductive ElTy : Ctx → Src.BTy → Ty → Prop
  /-- r:s-ty-tyvar -/
  | r_s_ty_tyvar : .ty (.named a) ∈ C.U → ElTy C (.tyvar a) (.var (.named a))
  /-- r:s-ty-rowvar -/
  | r_s_ty_rowvar : classOfName a = .any → .row (.named a) ∈ C.U →
      ElTy C (.tyvar a) (.rec [] (some (.named a)))
  /-- r:s-ty-record -/
  | r_s_ty_record : ElTyRowOpt C row ρ → ElTy C (.record row) (.rec ρ none)
  /-- r:s-ty-openrecord -/
  | r_s_ty_openrecord : classOfName r = .any → .row (.named r) ∈ C.U → ElTyRow C row ρ →
      ElTy C (.openRecord r row) (.rec ρ (some (.named r)))
  /-- r:s-ty-unit -/
  | r_s_ty_unit : ElTy C .unit tUnitTy
  /-- r:s-ty-tuple -/
  | r_s_ty_tuple : ElTy C t1 τ1 → ElTy C t2 τ2 → ElTyOpt C t3 τ3 →
      ElTy C (.tuple t1 t2 t3) (tupleTy τ1 τ2 τ3)
  /-- r:s-ty-con -/
  | r_s_ty_con : C.lookupTy c = some (θ, VE) → ElTyList C args τs → θ.apply τs = some τ →
      ElTy C (.con c args) τ
  /-- r:s-ty-fun -/
  | r_s_ty_fun : ElTy C t1 τ1 → ElTy C t2 τ2 → ElTy C (.fn t1 t2) (.fn τ1 τ2)
  /-- r:s-ty-paren -/
  | r_s_ty_paren : ElTy C t τ → ElTy C (.paren t) τ
/-- C ⊢ tyrow ⇒ ρ -/
inductive ElTyRow : Ctx → Src.BTyRow → Row → Prop
  /-- r:s-tyrow -/
  | r_s_tyrow : ElTy C t τ → ElTyRowOpt C rest ρ → ElTyRow C (.field l t rest) (Row.modify [(l, τ)] ρ)
inductive ElTyRowOpt : Ctx → Option Src.BTyRow → Row → Prop   -- opt_none (ρ = []), opt_some
inductive ElTyOpt : Ctx → Option Src.BTy → Option Ty → Prop
inductive ElTyList : Ctx → List Src.BTy → List Ty → Prop        -- seq_nil, seq_cons
end

mutual
/-- C ⊢ atpat ⇒ (VE, τ) -/
inductive ElAtPat : Ctx → Src.BAtPat → ValEnv → Ty → Prop
  | r_s_atpat_wild : ElAtPat C .wild [] τ
  | r_s_atpat_scon : Gen (typeOf sc) τ → τ ∈ [tIntTy, tCharTy, tStringTy] → ElAtPat C (.scon sc) [] τ
  | r_s_atpat_var : ElAtPat C (.var x) [(x, (mono τ, .v))] τ
  | r_s_atpat_con : C.lookupVal lc = some (σ, .c) → Gen σ (.con τs t) → ElAtPat C (.con lc) [] (.con τs t)
  | r_s_atpat_unit : ElAtPat C .unit [] tUnitTy
  | r_s_atpat_tuple : ElPat C p1 VE1 τ1 → ElPat C p2 VE2 τ2 → ElPatOpt C p3 VE3 τ3 →
      ElAtPat C (.tuple p1 p2 p3) (VE1.plus VE2 |>.plus VE3) (tupleTy τ1 τ2 τ3)
  | r_s_atpat_nil : ElAtPat C .nil [] (listTy τ)
  | r_s_atpat_record : ElPatRowOpt C row VE ρ → τ = .rec ρτ tl → Row.Sub ρ ρτ →
      ElAtPat C (.record row) VE τ
  | r_s_atpat_paren : ElPat C p VE τ → ElAtPat C (.paren p) VE τ
/-- C ⊢ patrow ⇒ (VE, ρ); the variable is the one spelt as the label. -/
inductive ElPatRow : Ctx → Src.BPatRow → ValEnv → Row → Prop
  | r_s_patrow : ElPatRowOpt C rest VE ρ →
      ElPatRow C (.field l rest) (FMap.modify [(l, (mono τ, .v))] VE) (Row.modify [(l, τ)] ρ)
/-- C ⊢ pat ⇒ (VE, τ) -/
inductive ElPat : Ctx → Src.BPat → ValEnv → Ty → Prop
  | r_s_pat_atpat : ElAtPat C a VE τ → ElPat C (.atpat a) VE τ
  | r_s_pat_con : C.lookupVal lc = some (σ, .c) → Gen σ (arrows τs (.con τs' t)) →
      ElAtPatList C args VEs τs → ElPat C (.con lc args) (FMap.plusAll VEs) (.con τs' t)
  | r_s_pat_cons : ElPat C p1 VE1 τ → ElPat C p2 VE2 (listTy τ) →
      ElPat C (.cons p1 p2) (VE1.plus VE2) (listTy τ)
  | r_s_pat_as : ElPat C p VE τ → ElPat C (.as p x) (VE.plus [(x, (mono τ, .v))]) τ
-- auxiliary: ElPatOpt, ElPatRowOpt, ElAtPatList
end

mutual
inductive ElAtExp : Ctx → Src.BAtExp → Ty → Prop
  | r_s_atexp_scon : Gen (typeOf sc) τ → ElAtExp C (.scon sc) τ
  | r_s_atexp_longvar : C.lookupVal lv = some (σ, is) → Gen σ τ → ElAtExp C (.var lv) τ
  | r_s_atexp_longcon : C.lookupVal lc = some (σ, is) → Gen σ τ → ElAtExp C (.con lc) τ
  | r_s_atexp_op : OTstat o = some (σ, is) → Gen σ τ → ElAtExp C (.op o) τ
  | r_s_atexp_unit : ElAtExp C .unit tUnitTy
  | r_s_atexp_tuple : ElExp C e1 τ1 → ElExp C e2 τ2 → ElExpOpt C e3 τ3 →
      ElAtExp C (.tuple e1 e2 e3) (tupleTy τ1 τ2 τ3)
  | r_s_atexp_nil : ElAtExp C .nil (listTy τ)
  | r_s_atexp_record : ElExpRowOpt C row ρ → ElAtExp C (.record row) (.rec ρ none)
  | r_s_atexp_update : ElAtExp C (.var ⟨none, x⟩) τ → τ = .rec ρτ tl → ElExpRow C row ρ →
      Row.Sub ρ ρτ → ElAtExp C (.update x row) τ
  | r_s_atexp_let : ElDec C d VE → ElExp (C.plusVE VE) e τ → ElAtExp C (.letE d e) τ
  | r_s_atexp_paren : ElExp C e τ → ElAtExp C (.paren e) τ
inductive ElExpRow : Ctx → Src.BExpRow → Row → Prop
  | r_s_exprow : ElExp C e τ → ElExpRowOpt C rest ρ → ElExpRow C (.field l e rest) (Row.modify [(l, τ)] ρ)
inductive ElExp : Ctx → Src.BExp → Ty → Prop
  | r_s_exp_atexp : ElAtExp C a τ → ElExp C (.atexp a) τ
  | r_s_exp_app : ElExp C e (.fn τ' τ) → ElAtExp C a τ' → ElExp C (.app e a) τ
  | r_s_exp_lambda : ElAtPat C p VE τ → ElExp (C.plusVE VE) e τ' → ElExp C (.lam p e) (.fn τ τ')
  | r_s_exp_case : ElExp C e τ → ElMatch C m (.fn τ τ') → ElExp C (.caseE e m) τ'
inductive ElMatch : Ctx → Src.BMatch → Ty → Prop
  | r_s_match : ElMRule C mr τ → ElMatchOpt C rest τ → ElMatch C (.mk mr rest) τ
inductive ElMRule : Ctx → Src.BMRule → Ty → Prop
  | r_s_mrule : ElPat C p VE τ → ElExp (C.plusVE VE) e τ' → ElMRule C (.mk p e) (.fn τ τ')
inductive ElDec : Ctx → Src.BDec → ValEnv → Prop
  | r_s_dec_group : ElValBind (C.plusVE VE) vb VE → ElDec C (.val vb) (closGroup C.tyvars VE)
inductive ElValBind : Ctx → Src.BValBind → ValEnv → Prop
  | r_s_valbind_var : AnnOK C ann U' τ → ElExp (C.plusU U') e τ → ElValBindOpt C rest VE →
      ElValBind C (.var x ann e rest)
        (FMap.modify [(x, (if ann.isSome then annScheme U' τ else mono τ, .v))] VE)
  | r_s_valbind_pat : ElAtPat C p VE τ → ElExp C e τ → ElValBind C (.pat p e) VE
/-- The first option of r:s-valbind-var. -/
inductive AnnOK : Ctx → Option Src.BTy → List BVar → Ty → Prop
  | opt_none : AnnOK C none [] τ
  | opt_some : NewFor U' ty C → ElTy (C.plusU U') ty τ → (∀ v ∈ U', v ∉ C.tyvars) →
      AnnOK C (some ty) U' τ
-- auxiliary: ElExpOpt, ElExpRowOpt, ElMatchOpt, ElValBindOpt
end
```

Rule count: 9 + 1 (types), 9 + 1 + 4 (patterns), 11 + 1 + 4 + 1 + 1 + 1 + 2 (expressions) = 45
constructors named `r_s_*`; a test in the build (`#guard` over the constructors' names, as for
the dynamic rules) checks the count and that every `\defnrule[r:s-...]` label of
`static-core.tex` has one.

### 5. The rules of Chapter 5 and the static rules of Chapter 9

`Stat/Modules.lean` (`static-modules.tex`):

```lean
/-- Expose(E, explist) (sec:static-modules-interfaces); none when an item is unbound. -/
def expose (E : Env) : Src.BExpList → Option IEnv
/-- π ⊕_modid (N, N') (sec:static-modules-providers, A28). -/
def ProvMap.merge (π : ProvMap) (mid : ModId) (N N' : List SmLongId) : ProvMap
/-- env(ME, π), with TE_List and VE_List taken from E0 (the List special case). -/
def envOf (ME : ModEnv) (π : ProvMap) : Env
def π0 : ProvMap        -- {List ↦ {List}, [] ↦ {List}, :: ↦ {List}}
/-- fig:static-modules-port: the least predicate. -/
inductive Port : Ty → Prop
def portB : Ty → Bool
/-- smlabs (sec:static-modules-rules). -/
def smlabs : Src.BTy → Option (List Lab)
/-- tyvarseq = tyrowvar(k): a row variable for a name used as an extension variable in the phrase. -/
def seqVars (params : List String) (uses : List (String × Bool)) : List BVar

inductive ElImports : SBasis → ProvMap → List Src.BImport → ProvMap → Prop
  | r_sm_imports_import : B.ME.find? i.mod = some I →
      ElExpListOpt (i.mod, I) i.exposing NN' →
      ElImports B (mergeOpt (π.merge i.mod [] (qualified (i.alias.getD i.mod) I)) i.mod NN') is π' →
      ElImports B π (i :: is) π'
  | r_sm_imports_empty : ElImports B π [] π
inductive ElExpList : ModId × IEnv → Src.BExpList → List SmLongId × List SmLongId → Prop
  | r_sm_explist_all : ElExpList (mid, I) .all ([], I.dom)
  | r_sm_explist_items : ElItemList (mid, I) is Ns → ElExpList (mid, I) (.items is) (unionAll Ns)
inductive ElItem : ModId × IEnv → Src.BItem → List SmLongId × List SmLongId → Prop
  | r_sm_item_var : x ∈ I.VE.keys → ElItem (mid, I) (.var x) ([], [⟨none, .val x⟩])
  | r_sm_item_op : o ∈ smops mid → ElItem (mid, I) (.op o) ([], [])
  | r_sm_item_type : I.TE.find? c = some (θ, VE) →
      ElItem (mid, I) (.ty c) ([⟨none, .ty c⟩], (VE.filter (·.2.2 = .v)).keys.map (⟨none, .val ·⟩))
  | r_sm_item_opentype : I.TE.find? c = some (θ, VE) → (∃ k σ, VE.find? k = some (σ, .c)) →
      ElItem (mid, I) (.tyAll c) ([⟨none, .ty c⟩], (VE.keys ∩ I.VE.keys).map (⟨none, .val ·⟩))
inductive ElHeader : Env → Src.BHeader → ModId × IEnv → Prop
  | r_sm_header : expose E h.exposing = some I → ElHeader E h (h.name, I)
inductive ElTopDec : Ctx → Src.BTopDec → Env → PortEnv → Prop
  | r_sm_topdec_value : ElValBind (C.plusVE VE) vb VE →
      ElTopDec C (.value vb) (Env.ofVE (closGroup C.tyvars VE)) []
  | r_sm_topdec_types : TypesOK (C.oplusTE TE) C db tbs TE VE →
      ElTopDec C (.types db tbs) ⟨[], TE, VE⟩ []
  | r_sm_topdec_portout : NewFor U ty C → ElTy (C.plusU U) ty τ → τ = .fn τ' (.con [.var α] tCmd) →
      Port τ' → ElTopDec C (.port x ty) (Env.ofVE [(x, (closScheme C.tyvars (mono τ), .v))]) [(x, (.out, τ'))]
  | r_sm_topdec_portin : NewFor U ty C → ElTy (C.plusU U) ty τ →
      τ = .fn (.fn τ' (.var α)) (.con [.var α] tSub) → Port τ' →
      ElTopDec C (.port x ty) (Env.ofVE [(x, (closScheme C.tyvars (mono τ), .v))]) [(x, (.inn, τ'))]
  | r_sm_topdec_seq : ElTopDec C d1 E1 PE1 → ElTopDec (C.oplusE E1) d2 E2 PE2 →
      ElTopDec C (.seq d1 d2) (E1.plus E2) (PE1.plus PE2)
  /-- r:sm-topdec-seq, applied at a separator inside a type-declaration phrase: the phrase
      `[type datbind ;] type alias tb1 ; ... ; type alias tbl` is one node of the bare syntax,
      and the book lets rule r:sm-topdec-seq split it too (comment on r:sm-topdec-types). -/
  | r_sm_topdec_seq_types : (db.isSome ∨ tbs1 ≠ []) → tbs2 ≠ [] →
      ElTopDec C (.types db tbs1) E1 PE1 → ElTopDec (C.oplusE E1) (.types none tbs2) E2 PE2 →
      ElTopDec C (.types db (tbs1 ++ tbs2)) (E1.plus E2) (PE1.plus PE2)
/-- The premises of r:sm-topdec-types, TE occurring on both sides (the fixed point, B5). -/
inductive TypesOK : Ctx → Ctx → Option Src.BDatBind → List Src.BTypBind → TyEnv → ValEnv → Prop
  | opt_none : ElTypBindList Cte tbs VEs TEs → TypesOK Cte C none tbs (FMap.plusAll TEs) (FMap.plusAll VEs)
  | opt_some : ElDatBind Cte d VE' TE' → (∀ s ∈ TE'.vals, s.1.headName ∉ C.T) →
      ElTypBindList Cte tbs VEs TEs →
      TypesOK Cte C (some d) tbs (TE'.plus (FMap.plusAll TEs)) (VE'.plus (FMap.plusAll VEs))
inductive ElDatBind : Ctx → Src.BDatBind → ValEnv → TyEnv → Prop
  | r_sm_datbind : seqVars ps (useInConbind cb) = vs → ElTyList (C.plusU vs) (ps.map .tyvar) τs →
      ElConBind (C.plusU vs) (.con τs t) cb VE → t.arity = ps.length →
      ElDatBindOpt C rest VE' TE' → (∀ s ∈ TE'.vals, s.1.headName ≠ some t) →
      ElDatBind C ((c, ps, cb) :: rest)
        ((closVE C.tyvars VE).plus VE') (FMap.modify [(c, (t.toFcn, closVE C.tyvars VE))] TE')
inductive ElConBind : Ctx → Ty → Src.BConBind → ValEnv → Prop
  | r_sm_conbind : ElTyList C tys τs → ElConBindOpt C τ rest VE →
      ElConBind C τ ((k, tys) :: rest) (FMap.modify [(k, (mono (arrows τs τ), .c))] VE)
inductive ElTypBind : Ctx → Src.BTypBind → ValEnv → TyEnv → Prop
  | r_sm_typbind : seqVars tb.params (useInTy tb.t) = vs → ElTy (C.plusU vs) tb.t τ →
      smlabs tb.t = none → ElTypBind C tb [] [(tb.c, (TyFcn.canon ⟨vs, τ⟩, []))]
  | r_sm_typbind_record : seqVars tb.params (useInTy tb.t) = vs → ElTy (C.plusU vs) tb.t τ →
      smlabs tb.t = some ls → τ = .rec ρ none → ρ.lookupAll ls = some τs →
      VE = closVE C.tyvars [(tb.c, (mono (arrows τs τ), .v))] →
      ElTypBind C tb VE [(tb.c, (TyFcn.canon ⟨vs, τ⟩, VE))]
inductive ElModule : SBasis → Src.BModule → SBasis → Env → Prop
  | r_sm_module : ElImports B π0 (defaultImports ++ m.imports) π →
      ElTopDecOpt ⟨B.T, [], envOf B.ME π⟩ m.body E PE → ElHeader E m.header (mid, I) →
      mid ∉ B.ME.keys → ElModule B m ⟨E.tynames.diff B.T, [(mid, I)], PE⟩ E
-- auxiliary: ElExpListOpt, ElItemList, ElTopDecOpt, ElDatBindOpt, ElConBindOpt, ElTypBindList
```

Count: 1 + 1 + 2 + 2 + 4 + 5 + 1 + 1 + 2 = 19 constructors named after the rules of
`static-modules.tex`, plus `r_sm_topdec_seq_types`, a second constructor for rule
`r:sm-topdec-seq` (it acts on a different node of the abstract syntax; see "Issues with the
plan", item 1). The build's count test expects 20 constructors for 19 labels and names the
exception.

`Stat/Program.lean` (`programs.tex`, `sec:programs-elaboration`):

```lean
/-- Dflt σ: Float for each bound type variable of class num. -/
def dflt (σ : Scheme) : Ty
/-- The premise "B ⊢ mod ⇒ B', E, inferred by a principal derivation for the module", with the
    further restrictions judged on that derivation (sec:static-modules-further, A96). -/
def PrincipalModDer (B : SBasis) (m : Src.BModule) (B' : SBasis) (E : Env) : Prop :=
  ∃ a : AModule, a.erase = m ∧ IsPrincipalMod B a ∧ a.result B = some (B', E) ∧ FurtherMod B a
inductive ElProgram : SBasis → List Src.BModule → Ty → PortEnv → Prop
  | r_p_stat_module : PrincipalModDer B m B' E →
      Disjoint B'.PE.keys (B.PE.keys ++ managersPlat) → ms ≠ [] →
      ElProgram (B.plus B') ms τ PE → ElProgram B (m :: ms) τ PE
  | r_p_stat_main_program : PrincipalModDer B m B' E →
      Disjoint B'.PE.keys (B.PE.keys ++ managersPlat) →
      E.VE.find? "main" = some (σ, .v) → σ.body = .con [τ1, τ2, τ3] tProgram → Port τ1 →
      ElProgram B [m] (dflt σ) (B.plus B').PE
  | r_p_stat_main_view : PrincipalModDer B m B' E →
      Disjoint B'.PE.keys (B.PE.keys ++ managersPlat) →
      E.VE.find? "main" = some (σ, .v) → dflt σ = .con [τ] tNode →
      ElProgram B [m] (.con [τ] tNode) (B.plus B').PE
/-- A program as written is legal: it meets the syntactic restrictions (as a set of modules) and
    elaborates by Chapter 9's rules, every module by a principal derivation meeting the further
    restrictions. The derived forms are step 8's canonical choice (B4). -/
def LegalProgram (B : SBasis) (sp : Src.SProgram) : Prop :=
  Src.SynOKSet sp ∧ ∃ τ PE, ElProgram B (Src.deriveProgram (Src.canonOrder sp)).modules τ PE
```

Since `σ.body = .con [τ1, τ2, τ3] tProgram` is about a canonical scheme, a `bnd` variable in
`τ1` makes `Port τ1` false (`Port` holds of no variable), as the book wants ("taken from the
scheme before the default, so it contains no type variable").

### 6. Appendix C and the test basis (G2-14)

`Generated/StaticBasis.lean` is written by `ExtractStaticBasis.elm --lean` (an extension of
step 7's script, in `definition/tools`, the translator's directory) from `static-basis.json`:

```lean
namespace StandardElm.Stat
def tInt : TyName := ⟨0, 0⟩      -- ... one def per T0 name, ids in figure order
def tNode : TyName := ⟨21, 1⟩
def T0 : List TyName
def E0 : IEnv                     -- TE_0 = {List ↦ (List, VE_0)}, VE_0 = {[] ↦ ..., :: ↦ ...}
def ME0 : ModEnv                  -- 19 interfaces, schemes written `sch ["comparable"] (...)`
def OTstat : Op → Option (Scheme × IdStatus)
def smops : ModId → List Op
def hiddenCons : List (TyName × List (String × List Ty))   -- Never: JustOneMore
def defaultImports : List Src.BImport                      -- fig:default-imports
```

`sch (vars : List String) (body : Ty) : Scheme` builds the canonical scheme with the named
variables bound; the generator does not compute canonical forms. Checks in the same file:
`theorem ME0_wf : ME0.wfB = true := by decide +kernel` (canonical schemes, sorted maps, arities),
`theorem tynames_ME0 : ME0.tynames ⊆ T0` (Appendix C, `sec:appendix-static-basis-modenv`), and
`example : Src.basisModuleIds = ME0.keys := by decide +kernel` (ties step 8's list to the
appendix).

`Generated/StaticLibrary.lean` is written by the translator from the vendored elm/core files:
for each library module of `libraryValues`, its own type declarations and each value's
annotation, as step 8's source syntax (`Src.STy`), never as a translated type:

```lean
def libModules : List (ModId × List Src.STopDec × List (Var × Src.STy))
```

`Stat/TestBasis.lean`:

```lean
def B0stat : SBasis := ⟨T0, ME0, []⟩
/-- D2(a): ME0(Html) with text added. -/
def harnessHtml : IEnv := { (ME0.find! "Html") with
  VE := [("text", (sch ["msg"] (.fn tStringTy (.con [.var (.named "msg")] tNode)), .v))] }
/-- The interface of a library module: ME0's for that module (if any) with each library value
    added at the scheme its annotation elaborates to: annScheme U' (elabTy C ty), where C is the
    module's own context (its imports, by the default imports, and its type declarations, by
    r:sm-topdec-types with names from 22 up) and U' the named variables of ty. -/
def libInterface (M : ModId) : IEnv
def Tlib : List TyName                 -- the new type names of library modules outside ME0, if any
def Btest : SBasis := ⟨T0 ++ Tlib, ((ME0.modify [("Html", harnessHtml)]).modify libInterfaces), []⟩
```

Statements relating `Btest` to `B0stat` (section "Theorems", group 6): it agrees with `B0stat`
on every module other than `Html` and the library modules; on a library module of `Dom ME0` it
has the same type environment and a larger value environment; `OTstat` and `defaultImports` are
the same objects (definitional); and under the default imports alone the provider maps of the two
bases differ only by qualified identifiers `M.x` of library values, so no unqualified
identifier becomes ambiguous.

### 7. Annotated phrases and the checker (`Stat/Annotated.lean`, D10)

An annotated phrase is the bare phrase with the semantic objects of its derivation's sentence at
every node: the type at every expression and pattern node, the instance (the list of types for
the scheme's bound variables) at every occurrence of a variable, constructor or operator, the
group's value environment before closure at every declaration, `U'` at every annotated binding,
and, in modules, the type environment solving `r:sm-topdec-types` (with its generated type
names), or the split of `r_sm_topdec_seq_types`.

```lean
mutual
inductive AAtExp where
  | scon (sc : Src.SLit) (τ : Ty)
  | var (lv : LongId) (inst : List Ty) (τ : Ty)
  | con (lc : LongId) (inst : List Ty) (τ : Ty)
  | op (o : Op) (inst : List Ty) (τ : Ty)
  | unit
  | tuple (e1 e2 : AExp) (e3 : Option AExp)
  | nil (τ : Ty)                                  -- τ is the list type
  | record (row : Option AExpRow)
  | update (x : Var) (inst : List Ty) (τ : Ty) (row : AExpRow)
  | letE (d : ADec) (e : AExp)
  | paren (e : AExp)
inductive AExpRow where | field (l : Lab) (e : AExp) (rest : Option AExpRow)
inductive AExp where
  | atexp (a : AAtExp) | app (e : AExp) (a : AAtExp) | lam (p : AAtPat) (e : AExp)
  | caseE (e : AExp) (m : AMatch)
inductive AMatch where | mk (mr : AMRule) (rest : Option AMatch)
inductive AMRule where | mk (p : APat) (e : AExp)
inductive ADec where | val (VE : ValEnv) (vb : AValBind)   -- VE: the group's, before closure
inductive AValBind where
  | var (x : Var) (ann : Option (Src.BTy × List BVar)) (τ : Ty) (e : AExp) (rest : Option AValBind)
  | pat (p : AAtPat) (e : AExp)
end
-- AAtPat, APatRow, APat likewise, every node with its τ (and inst at a constructor)

def AExp.erase : AExp → Src.BExp          -- and for every class
def AExp.ty : AExp → Ty                   -- context-free: read from the nodes
def checkExp : Ctx → AExp → Bool          -- and checkAtExp, checkPat, ..., mutually
```

`checkExp C a` checks at each node the premises of the one rule whose conclusion has the node's
form, with the node's objects: for `var lv inst τ`, `C.lookupVal lv = some (σ, _)`,
`inst.length = σ.bound.length`, `(instSubst σ inst).respectsB`, and
`(instSubst σ inst).apply σ.body = some τ`; for `app e a`, `checkExp C e`, `checkAtExp C a` and
`e.ty = .fn a.ty τ`; for `ADec.val VE vb`, that `vb` checks in `C.plusVE VE` and gives exactly
`VE` (computed from `vb`'s nodes), the declaration's result being `closGroup C.tyvars VE`; for an
annotated binding, `NewFor` (decidable), `elabTy (C.plusU U') ty = some τ` and the escape
condition. Every premise is decidable, and the checker is defined by structural recursion on the
annotated phrase, so `decide +kernel` runs it.

Modules:

```lean
inductive ATopDec where
  | value (VE : ValEnv) (vb : AValBind)
  | types (TE : TyEnv) (VE : ValEnv) (db : Option Src.BDatBind) (tbs : List Src.BTypBind)
  | typesSplit (k : Nat) (a1 a2 : ATopDec)      -- r_sm_topdec_seq_types at the k-th separator
  | port (x : Var) (U : List BVar) (τ : Ty)
  | seq (a1 a2 : ATopDec)
structure AModule where
  module : Src.BModule
  body : Option ATopDec
abbrev AProgram := List AModule
def AModule.erase : AModule → Src.BModule
def AModule.result (B : SBasis) (a : AModule) : Option (SBasis × Env)
def checkModule : SBasis → AModule → Bool
def checkProgram : SBasis → AProgram → Bool   -- each module in the basis built by the earlier ones
```

Imports, the header and type expressions carry no annotation: the checker computes them with the
functions of `Stat/Deterministic.lean`, each proved equal to its relation (section "Theorems",
group 8).

### 8. Instances, principal derivations, `InferPrincipalFor` (`Stat/Principal.lean`)

```lean
/-- A node of a derivation: the occurrence it is about (its path in the phrase), the U of its
    context, and the types and type schemes of its sentence. -/
structure Node where
  path : List Nat
  U : List BVar
  tys : List Ty
  schemes : List Scheme
/-- The nodes of the derivation an annotated phrase stands for, in context C, in preorder. A
    node of `typesSplit` that is about no occurrence of the phrase (the split parts) is left out;
    the nodes about the datbind, the typbinds, the conbinds and the type expressions are kept,
    with their paths. -/
def nodesExp (C : Ctx) : AExp → List Node
def nodesModule (B : SBasis) : AModule → List Node

/-- D' is an instance of D (sec:static-core-principal), in context C0. -/
def InstanceOf (C0 : Ctx) (a' a : AExp) : Prop :=
  a'.erase = a.erase ∧
  ∃ S : Subst, S.Respects ∧ (∀ v ∈ S.dom, v ∉ C0.tyvars) ∧
    S.DefinedOn ((nodesExp C0 a).flatMap (·.tys)) ∧
    ∀ n ∈ nodesExp C0 a, ∀ n' ∈ nodesExp C0 a', n.path = n'.path →
      (∃ vs, n.U.mapM S.applyVarToVar = some vs ∧ vs ≈ n'.U) ∧
      some n'.tys = n.tys.mapM S.apply ∧
      List.Forall₂ (fun σ' σ => ∀ τ, Gen σ' τ → ∃ σS, S.applyScheme σ = some σS ∧ Gen σS τ)
        n'.schemes n.schemes
def IsPrincipal (C0 : Ctx) (a : AExp) : Prop :=
  checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true → a'.erase = a.erase → InstanceOf C0 a' a

/-- Modules (sec:static-modules-principal): up to a bijection ρ between the generated type names. -/
def InstanceOfMod (B : SBasis) (a' a : AModule) : Prop :=
  ∃ ρ : List (TyName × TyName), ρ.Bijective (genNames B a) (genNames B a') ∧
    InstanceOfModAux B a' (a.renameTyNames ρ)
def IsPrincipalMod (B : SBasis) (a : AModule) : Prop :=
  checkModule B a = true ∧ ∀ a', checkModule B a' = true → a'.erase = a.erase → InstanceOfMod B a' a

/-- The two properties of the book (sec:static-core-principal, sec:static-modules-principal);
    "any two principal derivations are instances of each other" holds by definition. -/
def PrincipalExistsCore : Prop :=
  ∀ C0 (e : Src.BExp), (∃ τ, ElExp C0 e τ) → ∃ a, a.erase = e ∧ IsPrincipal C0 a
def PrincipalExistsMod : Prop :=
  ∀ B (m : Src.BModule), (∃ B' E, ElModule B m B' E) → ∃ a, a.erase = m ∧ IsPrincipalMod B a
def PrincipalExists : Prop := PrincipalExistsCore ∧ PrincipalExistsMod
/-- Its instance at the modules of one program, in any basis. Defined for reference only: it
    quantifies over every basis, and is false for contrived bases (a basis whose `Basics` exposes
    an alias spelt like a type the program declares makes the B6 split possible), so no theorem
    is stated under it. -/
def PrincipalExistsFor (p : Src.BProgram) : Prop :=
  ∀ B, ∀ m ∈ p.modules, (∃ B' E, ElModule B m B' E) → ∃ a, a.erase = m ∧ IsPrincipalMod B a

/-- The bases of r:p-stat-module: B₁ = B, B_{i+1} = B_i + B'_i, where B'_i is what module i's
    derivation gives (programs.tex, modification of static bases); `none` when a module does
    not check. The same bases `checkProgram` uses. -/
def AProgram.bases (B : SBasis) : AProgram → Option (List SBasis)

/-- a is a derivation for the program p in B: module i of a is a derivation for module i of p
    in the i-th basis. -/
def ProgDeriv (B : SBasis) (p : Src.BProgram) (a : AProgram) : Prop :=
  checkProgram B a = true ∧ a.map AModule.erase = p.modules

/-- Finding B1's reading of "the principal derivation of the program": every module's
    derivation is principal in the basis the earlier ones build. -/
def PrincipalProgDeriv (B : SBasis) (p : Src.BProgram) (a : AProgram) : Prop :=
  ProgDeriv B p a ∧ ∃ Bs, a.bases B = some Bs ∧ ∀ i (h : i < a.length), IsPrincipalMod Bs[i]! a[i]

/-- D11's hypothesis for one program (plan, decision D11): what the inference returns for it is
    principal. Step 11 proves it for every program whose modules are coherent (finding B6). -/
def InferPrincipalFor (B : SBasis) (p : Src.BProgram) : Prop :=
  ∀ a, inferProgram B p = .ok a → checkProgram B a = true → PrincipalProgDeriv B p a
```

### 9. The pattern decider (`Stat/Patterns.lean`, D12, B2, G2-12)

```lean
/-- The constructors of a type name (sec:static-core-further): name and argument types, the
    arguments written over the type's parameters `bnd 0 .. bnd (k-1)`. From the type structures of
    the context's environment and interfaces, every custom type the module declares, the hidden
    constructors of Appendix C (JustOneMore of Never), and List's [] and ::. -/
abbrev ConTable := List (TyName × List (String × List Ty))
def conTable (C : Ctx) : ConTable
/-- A31: what a constant denotes. An integer constant by its value as an Int, norm n ([params]). -/
inductive Den where | int (v : Int) | char (c : Char) | str (s : String)
def denote : Src.SLit → Option Den
/-- exh: the clause "no set of special constants covers every inhabitant of Int, Char or String"
    (res:core-exhaustiveness) is in force; irr: it is not (res:core-irredundancy), so a literal
    column is complete when it lists every value of a finite domain (B2). -/
inductive Mode where | exh | irr

/-- Inhabitants (A97), coinductive, as position maps: a node at each position of a prefix-closed
    set of paths of argument indices. `other` stands for the constants no pattern lists, in mode
    exh only. -/
abbrev Pos := List Nat
inductive INode where
  | den (d : Den) | other | unit | tuple (k : Nat) | con (k : String) (n : Nat) | wild
structure Inh where
  f : Pos → Option INode
def INode.arity : INode → Nat
/-- The type at position p, following the nodes of h from τ. -/
def tyAt (tbl : ConTable) (h : Inh) (τ : Ty) : Pos → Option Ty
/-- The clause of sec:static-core-further that gives the node at a position of type τ. -/
def Clause (tbl : ConTable) (mode : Mode) (τ : Ty) (n : INode) : Prop
def IsInh (tbl : ConTable) (mode : Mode) (τ : Ty) (h : Inh) : Prop :=
  (h.f []).isSome ∧
  (∀ p i, (h.f (p ++ [i])).isSome → (h.f p).isSome) ∧
  ∀ p n, h.f p = some n → ∃ τp, tyAt tbl h τ p = some τp ∧ Clause tbl mode τp n ∧
    ∀ i, (h.f (p ++ [i])).isSome ↔ i < n.arity
/-- Coverage (sec:static-core-further), on bare patterns; constants by denotation (A31). -/
def Covers (C : Ctx) : Src.BPat → Inh → Pos → Prop

/-- Patterns reduced to the matrix form: wildcard (also a variable, a record pattern), constant
    by denotation, constructor with its type name, unit, tuple; `as` and parentheses dropped. -/
inductive PatN where
  | wild | den (d : Den) | con (t : TyName) (k : String) (args : List PatN) | unit | tuple (args : List PatN)
def normalise (C : Ctx) : Src.BPat → PatN
/-- Usefulness (Maranget), by structural recursion on fuel; fuel = 1 + the total size of the
    matrix and the vector suffices (lemma useful_fuel). Literal signatures are complete only in
    mode irr and only when they list every value of the domain: Int has intMax - intMin + 1
    values, Char 1,112,064 (Lean's `Char`), String infinitely many. -/
def useful (mode : Mode) (tbl : ConTable) (fuel : Nat) (P : List (List PatN)) (q : List PatN) : Bool
def exhDec (C : Ctx) (ps : List Src.BPat) : Bool
def irrDec (C : Ctx) (ps : List Src.BPat) : Bool
```

`Stat/Further.lean`: the further restrictions of a phrase are judged at each match, each lambda
and each destructuring binding of its derivation:

```lean
/-- The book's statement (res:core-irredundancy, res:core-exhaustiveness), at the types the
    annotated derivation gives. -/
def FurtherProp (C : Ctx) (a : AExp) : Prop
/-- The decider, on the bare phrase and the module-level context alone (the constructor table
    does not change inside a Core phrase: let and patterns bind only variables). -/
def furtherDec (C : Ctx) (e : Src.BExp) : Bool
def FurtherMod (B : SBasis) (a : AModule) : Prop      -- FurtherProp at every top-level declaration
def furtherModDec (B : SBasis) (a : AModule) : Bool   -- reads only a.erase and the module context
```

### 10. Main type, deterministic parts, refusals (`Stat/Deterministic.lean`, `Stat/MainType.lean`, `Stat/Refusals.lean`)

```lean
def elabTy (C : Ctx) : Src.BTy → Option Ty
def elabImports (B : SBasis) (π : ProvMap) : List Src.BImport → Option ProvMap
/-- The fixed point of r:sm-topdec-types (B5): custom types get the given fresh names; aliases are
    elaborated in Appendix A's order (each after the aliases it mentions), each in C ⊕ (the custom
    types' type functions, which are their names) ⊕ (the earlier aliases); then the constructors
    are elaborated in C ⊕ (all of them). One pass suffices: no alias mentions a later one, and a
    custom type's type function does not depend on its constructors. -/
def elabTypes (C : Ctx) (db : Option Src.BDatBind) (tbs : List Src.BTypBind) (fresh : List TyName) :
    Option (TyEnv × ValEnv)
def elabPort (C : Ctx) (x : Var) (ty : Src.BTy) : Option (Env × PortEnv)
/-- The context every derivation of a module elaborates its declarations in, up to the generated
    names: imports, then the type declarations, then the value groups in order. -/
def moduleCtx (B : SBasis) (m : Src.BModule) (fresh : List TyName) : Option Ctx
/-- A name that no environment of any derivation binds: every free long identifier of every
    expression, pattern and type expression of the module is checked against moduleCtx
    extended by the module's own declarations and, inside a phrase, by its binders. -/
def scopeOK (B : SBasis) (m : Src.BModule) : Bool
/-- Every type expression (annotations, ports, declarations) elaborates in its deterministic
    context, every import and the header elaborate, every port is of an admissible form. -/
def shapeOK (B : SBasis) (m : Src.BModule) : Bool
/-- The head type name of every type a derivation can give `e`, when the head is fixed by the
    basis or by an annotation: a spine `x a1 ... an` with `x` bound by the imports or by an
    annotated top-level declaration (not by a binder of `e`), whose scheme's body has a type-name
    head after n arrows; `[]` and list expressions (List); tuples; unit; records are not heads;
    `let ... in e'` and `( e' )` give the head of `e'`. -/
def forcedHead (C : Ctx) (bound : List Var) : Src.BExp → Option TyName
/-- The Chapter 9 check transferable to the principal derivation without principality:
    `main` annotated (its scheme is the annotation's in every derivation), or a view whose head
    is forced to Node, or a program whose head is forced to Program and whose flags type is fixed
    by an annotation of `init` or by a pattern of `init`'s lambda (`()` forces unit). -/
def mainTransfer (B : SBasis) (p : Src.BProgram) : Bool
def portsDisjointDec (B : SBasis) (p : Src.BProgram) : Bool
```

### 11. The inference (`Stat/Unify.lean`, `Stat/Infer.lean`): not proved

```lean
structure InfState where
  next : Nat                                   -- fresh ids
  tsub : List (Nat × Ty)                       -- bindings of fresh type variables
  rsub : List (Nat × (Row × Option RowVar))    -- bindings of fresh row variables
  lacks : List (Nat × List Lab)                -- labels each fresh row variable may not take (A23)
  rigid : List BVar                            -- the explicit variables in scope (never bound)
def unify (fuel : Nat) (s : InfState) (τ1 τ2 : Ty) : Except String InfState
def inferExp (fuel : Nat) (C : Ctx) (s : InfState) (e : Src.BExp) : Except String (AExp × InfState)
def inferModule (B : SBasis) (m : Src.BModule) : Except String AModule
def inferProgram (B : SBasis) (p : Src.BProgram) : Except String AProgram
```

Written with fuel (structural recursion), so that step 11 can prove it and the kernel could run
it; here only compiled code runs it, inside `lake exe certify`.

**Unification** (classes, rows, rigid variables):

| Case | Action |
|------|--------|
| flexible `α` (class κ) with flexible `β` (class κ') | same variable: nothing; else `κ'' := κ.meet κ'` (none: fail, "no common class"); if `κ'' = κ'` bind `α := β`, if `κ'' = κ` bind `β := α`, else bind both to a fresh variable of class κ'' |
| flexible `α` (κ) with rigid `r` (κ') | bind `α := r` iff `κ'.le κ`; else fail |
| rigid with rigid | equal, or fail ("rigid variable") |
| flexible `α` (κ) with a non-variable `τ` | occurs check (through rows and their tails), then `push κ τ`, then bind |
| `.con as t` with `.con bs t'` | `t = t'`, then the arguments pairwise |
| `.fn` with `.fn` | both sides |
| `.rec ρ1 e1` with `.rec ρ2 e2` | the common labels pairwise; `ρ1 \ ρ2` must go to `e2` and `ρ2 \ ρ1` to `e1`: a closed side (`none`) accepts nothing extra; one open side `e` with extra labels L: bind `e := {L | e'}` for a fresh `e'` with `lacks e' := lacks e ∪ labels`, failing if `L ∩ lacks e ≠ ∅` (A23); both open and distinct: a fresh `e3` with both bindings; the same row variable on both sides: the label sets must be equal; a rigid row variable is never bound |
| anything else | fail |

`push κ τ` (B3: classes pushed into arguments), with refinement of a flexible variable `β`
inside to a fresh variable of class `β.cls.meet κ'` and a rigid one accepted iff its class is
`≤ κ'`:

| κ | Accepted heads and what is pushed |
|---|-----------------------------------|
| any | everything, nothing pushed |
| num | `Int`, `Float` |
| comp | `Int`, `Float`, `Char`, `String`; `τ' List` pushing comp into `τ'`; 2- and 3-tuples pushing comp into each component |
| app | `String`; `τ' List`, nothing pushed |
| capp | `String`; `τ' List` pushing comp into `τ'` |

Records and functions are accepted by `any` only.

**Expressions**: algorithm W over the bare phrase, building the annotated phrase with inference
variables and zonking it (applying the final substitution) at the end. An integer constant gets
a fresh variable of class num; an occurrence of `x` instantiates `σ`'s bound variables with fresh
variables of their classes (row variables with fresh row variables, `.rec [] (some e)`), and the
list is the node's `inst`. `[]` gets `listTy α`. A record update unifies the variable's type with
`.rec ρ (some e)` for the updated fields and a fresh `e`.

**Groups** (`r:s-dec-group`, `r:sm-topdec-value`): every annotated member enters `VE` with
`annScheme U' τ`, `U'` its named variables not already in `U` (a row variable for a name used as
an extension variable in the annotation, a type variable otherwise, G2-5), `τ := elabTy (C +
U') ty`; every unannotated member with a fresh flexible variable (monomorphic in the group). Each
member is inferred in `C + VE` (and `+ U'`, the `U'` variables rigid while it is inferred); an
annotated member's expression is unified with its `τ`; after the member, the escape condition is
checked on the zonked context: `U' ∩ tyvars (zonk C) = ∅` ("rigid variable escapes"). The result
is `closGroup (tyvars (zonk C)) (zonk VE)`; A93's extra variables are thus quantified (G2-6). The
inference does not compare with `Translate/Infer.elm`'s `groupVars`; differences show up as
specialisation differences in step 10.

**Modules**: imports by `elabImports`; type declarations by `elabTypes` with fresh names from
`1000 + (the number of names generated so far)`; value groups and ports in the order of the
derived forms; the header by `expose`; then `Dflt` and the Chapter 9 checks for the main module.

**Output**: an `AProgram`, or an error naming the phrase. The checker decides whether the output
is a derivation; an error, or a certificate the checker rejects, is investigated: an inference
bug, a book finding, or an Elm finding (plan: "A test Elm compiles that does not elaborate is a
finding").

### 12. Parameters (G2-15)

Fixed by choice, named `[params]` on every page that shows a theorem:

| Parameter | Lean | Used by |
|-----------|------|---------|
| IntRange, norm | `StandardElm.intMin`, `intMax`, `norm` (eco: 64-bit, wrapping) | `denote` (A31), the size of the Int domain in mode irr (B2) |
| the platform's managers | `Src.managersPlat : List Var := []` | `r:p-stat-*`'s side condition, `res:modules-program` |
| characters | Lean's `Char` (Unicode scalar values) | `denote`, the size of the Char domain (1,112,064) |

### 13. Certificates and per-test theorems (`Certify.lean`, `StandardElmMech/Certs/`)

`lake exe certify` imports the library, runs `inferProgram Btest (deriveProgram (canonOrder s))`
compiled, for every program of `srcShards` that step 7 classes as a compile-success test with
`basis` in `{B0, harness, library, helper}` (622) or as a `further` or `static-deterministic`
compile-error test, and writes `StandardElmMech/Certs/<Project><nn>.lean` (40 programs each, a new
directory beside `Generated/`, written by this executable only; `--check` compares). Each file
holds, per program, the certificate as a literal term (printed with `Repr`) and the theorem:

```lean
/-- tests/elm/src/HelloTest.elm [parse] [harness] [principal] [params] -/
def a_elm_HelloTest : Stat.AProgram := ...
/-- The certificate is what the inference returns (run compiled, so [native]: the inference is
    too costly for the kernel; the checking below is by the kernel). -/
theorem inf_elm_HelloTest :
    Stat.inferProgram Stat.Btest (Src.deriveProgram (Src.canonOrder s_elm_HelloTest)) =
      .ok a_elm_HelloTest := by native_decide
theorem legal_elm_HelloTest :
    Stat.InferPrincipalFor Stat.Btest (Src.deriveProgram (Src.canonOrder s_elm_HelloTest)) →
    Stat.LegalProgram Stat.Btest s_elm_HelloTest :=
  Stat.legal_of_cert Stat.Btest s_elm_HelloTest a_elm_HelloTest inf_elm_HelloTest
    (by decide +kernel)
```

or, when `mainTransfer` fails, `cert_<project>_<Test> : Stat.CertProgram Stat.Btest s` (section
"Theorems", group 9); for a refusal:

```lean
/-- tests/elm/src/MissingPatternsAMissingTupleShapeTest.elm [parse] [harness] [params] -/
theorem refuse_elm_MissingPatternsAMissingTupleShapeTest :
    ¬ Stat.LegalProgram Stat.Btest s_elm_MissingPatternsAMissingTupleShapeTest :=
  Stat.not_legal_of_further (by decide +kernel)
```

A program whose inference fails gets no theorem and is listed in `certify`'s report. The cert
files import only `StandardElmMech.Stat.Legal` and the Generated source shards (no `Lean` meta
library). Kernel versus native (G2-17): the theorems are by `decide +kernel`, which checks the
certificate and does not run the inference; a program that breaks the memory budget is proved by
`native_decide`, tagged `[native]` in its docstring and listed (the compiler then joins the
trusted base for that theorem, which the plan's trust table records). `certify` measures the
kernel time per program on the first shard and reports it.

### 14. Names provided to step 10

[Step 10](step-10-end-to-end.md) ("From step 9") was specified in parallel and names what it
reads. This step provides those names, as aliases or small functions in `Stat/Interface.lean`,
so that both specifications hold:

```lean
abbrev Class := Cls
abbrev AnnExp := AExp            -- and AnnAtExp, AnnPat, AnnValBind, ... for every class
abbrev AnnModule := AModule
def eraseModule : AnnModule → Src.BModule := AModule.erase
def checkModuleR (B : SBasis) (a : AnnModule) : Option (SBasis × Env) :=
  if checkModule B a then a.result B else none
def ModDeriv (B : SBasis) (m : Src.BModule) (a : AnnModule) : Prop :=
  (checkModuleR B a).isSome ∧ eraseModule a = m
def PrincipalMod (B : SBasis) (m : Src.BModule) (a : AnnModule) : Prop :=
  eraseModule a = m ∧ IsPrincipalMod B a
def StatProgram (B : SBasis) (p : Src.BProgram) (r : Ty × PortEnv) : Prop :=
  ElProgram B p.modules r.1 r.2
abbrev InferError := String
/-- At every occurrence of a variable, constructor or operator: its path, the scheme used (looked
    up in the context the traversal computes) and the instance keyed by the scheme's bound
    variables. -/
def occurrences (C : Ctx) : AnnExp → List (List Nat × Scheme × List (BVar × Ty))
/-- At every group node (r:s-dec-group, r:sm-topdec-value): its path, its context C, the VE of
    the premise, and each annotated member's U'. -/
def groupNodes (C : Ctx) : AnnExp → List (List Nat × Ctx × ValEnv × List (Var × List BVar))
/-- The module that provides an imported identifier, when it is not ambiguous. -/
def provider (B : SBasis) (a : AnnModule) (x : LongId) : Option ModId
```

The certificates store only the instance lists and the group's `VE`; the scheme used and the
context at a node are recomputed by `occurrences` and `groupNodes`, which keeps certificates
small. `inferProgram`'s result type is `Except InferError (List AnnModule)` as step 10 expects.
Step 10's choice to run the inference inside the kernel can instead use the literal certificate
`a_<project>_<Test>` of `Certs/` (section 13), with the same statement; see "Issues with the
plan", item 6.

## Theorems

Grouped by file. Each is stated in Lean, then its proof method.

### Group 1: objects, substitution, schemes

```lean
theorem Cls.meet_spec : Cls.meet k k' = some m ↔ (m.le k ∧ m.le k' ∧ ∀ n, n.le k → n.le k' → n.le m)
theorem Cls.meet_none : Cls.meet k k' = none ↔ ∀ n, ¬ (n.le k ∧ n.le k')
theorem adm_iff : adm k τ = true ↔ Adm k τ
/-- The property of sec:static-core-types. -/
theorem adm_mono : Cls.le k k' = true → Adm k τ → Adm k' τ
theorem adm_subst : Adm k τ → S.Respects → S.apply τ = some τ' → Adm k τ'
theorem subst_wf : τ.wf = true → S.wf → S.apply τ = some τ' → τ'.wf = true
theorem canon_eq_iff (σ σ' : Scheme) (h : σ.wf ∧ σ'.wf) :
    σ.canon = σ'.canon ↔ SchemeEqBook σ σ'
/-- sec:static-core-schemes: if σ ≻ σ' and σ' ≻ τ then σ ≻ τ. -/
theorem gen_trans : GenS σ σ' → Gen σ' τ → Gen σ τ
theorem closGroup_extra (h : (x, (σ', is)) ∈ closGroup A VE) (hx : VE.find? x = some (σ, is)) :
    ∀ τ, Gen σ' τ ↔ Gen (closScheme A σ) τ
```

`SchemeEqBook` is the book's equality written as a relation (a bijective renaming of the
non-vacuous bound variables, sort and class kept, and equal multisets of classes num among the
vacuous ones). Methods: `Cls` lemmas by `decide` over the 25 pairs. `adm_iff` by induction on
`τ` (nested: a motive for lists). `adm_mono` by cases on the class pair, `Adm.comp` by induction.
`adm_subst` by induction on `Adm k τ`; at a variable `α` with `S α = τα` use `S.Respects` and
`adm_mono`. `canon_eq_iff` by the characterisation of `canon` as "first-occurrence numbering",
which is invariant under renaming. `gen_trans` by composing the two substitutions (`instSubst`
of the composed list), with `adm_subst` for respect. `closGroup_extra` (A93: the extra variables
change no instance) since they do not occur in the body.

### Group 2: the checker (D10)

```lean
theorem checkExp_sound : checkExp C a = true → ElExp C a.erase a.ty
theorem checkExp_adequate : ElExp C e τ → ∃ a, a.erase = e ∧ a.ty = τ ∧ checkExp C a = true
theorem checkModule_sound : checkModule B a = true → ∃ B' E, a.result B = some (B', E) ∧ ElModule B a.erase B' E
theorem checkModule_adequate : ElModule B m B' E → ∃ a, a.erase = m ∧ checkModule B a = true ∧ a.result B = some (B', E)
```

```lean
/-- Stability under substitution (used by instances, and by step 10's defaulting): a substitution
    that respects classes, is defined on every type of the derivation, and moves no variable of a
    U nor any free variable of the root context, maps a derivation to a derivation. -/
theorem check_subst (h : checkExp C a = true) (hS : S.Respects) (hdef : S.DefinedOn (a.allTys C))
    (hU : ∀ v ∈ a.allU C, v ∉ S.dom) (hC : ∀ v ∈ C.tyvars, v ∉ S.dom) :
    ∃ a', a'.erase = a.erase ∧ some a'.ty = S.apply a.ty ∧ checkExp C a' = true
```

(and the same for every phrase class, stated mutually.) `check_subst` by induction on the
annotated phrase: at an occurrence the new instance is `S` composed with the old one (`adm_subst`
keeps respect); at a group, `closGroup` commutes with `S` because `S` moves no variable of the
context (the closed variables are bound, `bnd`, and untouched). Soundness: by structural induction on
the annotated phrase, each node's checks giving the rule's premises (the iff lemmas of the
decidable premises: `NewFor`, `respectsB`, `elabTy_iff`, `elabImports_iff`, `expose`). Adequacy:
by mutual induction on the derivation, building the annotated phrase from the premises: a `Gen`
premise gives the instance list, `r:s-dec-group` gives `VE`, `r:sm-topdec-types` gives `TE`,
`r_sm_topdec_seq_types` gives a `typesSplit`.

### Group 3: principal derivations

```lean
theorem principal_unique : IsPrincipal C a → IsPrincipal C a' → a.erase = a'.erase →
    InstanceOf C a a' ∧ InstanceOf C a' a
theorem instance_refl : checkExp C a = true → InstanceOf C a a
```

By unfolding (the first two are the remark that uniqueness is part of the definition); the third
by the identity substitution.

### Group 4: patterns (D12, B2, A97, G2-12)

```lean
/-- A97: every type has an inhabitant, in both modes. -/
theorem inhabited (htbl : tbl.WF) (mode) (τ : Ty) (hτ : τ.wf) : ∃ h, IsInh tbl mode τ h
/-- Cut-off: coverage reads h only at positions shorter than the pattern's depth. -/
theorem covers_depth : Covers C p h [] ↔ Covers C p (h.cut p.depth) []
/-- Extension: a partial inhabitant, defined and consistent up to depth d, extends to an
    inhabitant agreeing with it there. -/
theorem extend (htbl : tbl.WF) : PartialInh tbl mode τ d g → ∃ h, IsInh tbl mode τ h ∧ h.agrees d g
/-- Head forcing (the principality-free core of D12): a pattern other than a wildcard, a variable,
    a record pattern, or these under `as` and parentheses, fixes the head of its type. -/
theorem head_forced (h : ElPat C p VE τ) (hp : (normalise C p).isRefutable) : τ.headOf? = (normalise C p).head?
theorem useful_fuel : fuel ≥ 1 + size P q → useful mode tbl fuel P q = useful mode tbl (size P q + 1) P q
theorem useful_iff (hcols : ColumnsElaborate C P q τs) :
    useful mode (conTable C) fuel P q = true ↔
    ∃ hs, (∀ i, IsInh (conTable C) mode τs[i] hs[i]) ∧ MatchesRow C q hs ∧ ∀ r ∈ P, ¬ MatchesRow C r hs
theorem exhDec_correct (hps : ∀ p ∈ ps, ∃ VE, ElPat C p VE τ) :
    exhDec C ps = true ↔ ∀ h, IsInh (conTable C) .exh τ h → ∃ p ∈ ps, Covers C p h []
theorem irrDec_correct (hps : ∀ p ∈ ps, ∃ VE, ElPat C p VE τ) :
    irrDec C ps = true ↔ ∀ j (hj : j < ps.length), ∃ h, IsInh (conTable C) .irr τ h ∧
      Covers C ps[j] h [] ∧ ∀ i < j, ¬ Covers C ps[i] h []
```

Methods. `inhabited`: define `h.f` by recursion on the position, choosing at each position the
first constructor of the type there (the type is computed along the path, so no recursion on
types is needed: this is why position maps make A97 a theorem, P2-14); for Int/Char/String the
constant `0`, `'\u{0}'`, `""`. `covers_depth` by induction on the pattern. `extend` by filling
each frontier position with `inhabited` at its type. `head_forced` by inversion on the pattern
rules (`r:s-atpat-scon` forces Int/Char/String, `r:s-atpat-con` and `r:s-pat-con` the
constructor's type name, `r:s-atpat-unit`, `-tuple`, `-nil`, `r:s-pat-cons` their names).
`useful_iff`: Maranget's proof, by induction on fuel, with `ColumnsElaborate` (each column's
patterns elaborate at that column's type) as invariant: specialisation by a constructor keeps it
(the argument patterns elaborate at the instantiated argument types, from `r:s-pat-con`'s
premises), the default matrix keeps it; at a column whose type is a variable, a function or a
record type, `head_forced` shows that only wildcards occur, so the signature is empty and the
inhabitant there is `wild`; a complete literal signature in mode irr is the whole finite domain
(B2), never in mode exh (the `other` inhabitant); the witnesses are completed by `extend`.
`exhDec_correct` and `irrDec_correct` from `useful_iff` with one column.

### Group 5: the further restrictions without principality (D12)

```lean
theorem further_correct (h : checkExp C a = true) : furtherDec C a.erase = true ↔ FurtherProp C a
/-- The principality-free invariance lemma: every derivation of a phrase gives the same answer. -/
theorem further_invariant (h : checkExp C a = true) (h' : checkExp C a' = true) (he : a.erase = a'.erase) :
    FurtherProp C a ↔ FurtherProp C a'
theorem furtherMod_correct (h : checkModule B a = true) : furtherModDec B a = true ↔ FurtherMod B a
theorem furtherMod_rename : FurtherMod B a ↔ FurtherMod B (a.renameTyNames ρ)   -- ρ bijective on generated names
```

`further_correct` by induction on the annotated phrase, `exhDec_correct`/`irrDec_correct` at
each match, lambda and destructuring binding (their patterns elaborate at the node's type by the
checked premises). `further_invariant` is a corollary: `furtherDec` reads only the bare phrase
and `C`. `furtherMod_rename`: the constructor table is renamed with the names.

### Group 6: the test basis (D2, G2-14)

```lean
theorem Btest_agrees : ∀ M ∈ ME0.keys, M ≠ "Html" → M ∉ libModuleIds → Btest.ME.find? M = ME0.find? M
theorem Btest_lib_extends : ∀ M ∈ libModuleIds, M ∈ ME0.keys →
    (Btest.ME.find! M).TE = (ME0.find! M).TE ∧ (ME0.find! M).VE ⊆ (Btest.ME.find! M).VE
theorem Btest_html : Btest.ME.find? "Html" = some harnessHtml
theorem default_imports_test :
    ∃ π π', elabImports B0stat π0 defaultImports = some π ∧ elabImports Btest π0 defaultImports = some π' ∧
      (∀ x : SmId, π'.find? ⟨none, x⟩ = π.find? ⟨none, x⟩) ∧
      (∀ l ∈ π.keys, π'.find? l = π.find? l)
```

All by `decide +kernel` (finite data), or `rfl` for definitional ones. The last says: under the
default imports alone, `Btest` changes no unqualified identifier and no qualified identifier that
`B0` provides, so it makes nothing ambiguous; it only adds qualified `M.x` for library values.

### Group 7: deterministic parts (P2-13)

```lean
theorem elabTy_iff : ElTy C ty τ ↔ elabTy C ty = some τ
theorem elabImports_iff : ElImports B π is π' ↔ elabImports B π is = some π'
theorem header_iff : ElHeader E h r ↔ (expose E h.exposing).map (h.name, ·) = some r
theorem elabTypes_complete (hd : ElTopDec C (.types db tbs) E PE) :
    ∃ fresh ρ, (∀ t ∈ fresh, t ∉ C.T) ∧ elabTypes C db tbs fresh = some (E.TE.rename ρ, E.VE.rename ρ) ∧ PE = []
theorem elabTypes_sound (h : elabTypes C db tbs fresh = some (TE, VE)) (hf : ∀ t ∈ fresh, t ∉ C.T) (hnd : fresh.Nodup) :
    ElTopDec C (.types db tbs) ⟨[], TE, VE⟩ []
theorem annotated_main_scheme (hm : ElModule B m B' E) (hann : m.mainAnnotation = some ty) :
    ∃ U' τ, E.VE.find? "main" = some (annScheme U' τ, .v) ∧ elabTy (mainCtx B m) ty = some τ
theorem forcedHead_sound (h : forcedHead C bound e = some t) (hb : ∀ x ∈ bound, ...) :
    ElExp C' e τ → C' agrees with C off `bound` → ∃ τs, τ = .con τs t
theorem ports_det (h1 : ElModule B m B1 E1) (h2 : ElModule B m B2 E2) : B1.PE = B2.PE
```

`elabTy_iff` by induction on `ty`, using unambiguity of `U` (at most one of `r_s_ty_tyvar`,
`r_s_ty_rowvar` applies). `elabImports_iff` by induction on the list. `elabTypes_complete`: the
book's property (`static-modules.tex`, "TE is determined by C and the phrase, up to the choice of
the type names") for `r_sm_topdec_types`; by induction on the aliases in Appendix A's order
(each alias's type function is fixed by the earlier ones and the custom types' names). For a
derivation that uses `r_sm_topdec_seq_types` the statement is false in general (item 1 of
"Issues with the plan"); the lemma is stated for derivations without it, and the theorems that
use it (`not_legal_of_shape`) quantify over both: a `typesSplit` derivation elaborates each part
in a context computed the same way, and `shapeOK` checks every alias and constructor in every
context a split can give it (finitely many: one per separator). `annotated_main_scheme` by
inversion through `r:sm-topdec-value` and `r:s-valbind-var` (the closure leaves an annotated
member's scheme unchanged, `static-core.tex`, comment on `r:s-dec-group`). `forcedHead_sound` by
induction on `e` along the spine. `ports_det` from `elabTy_iff` and the port rules.

### Group 8: refusals without inference

```lean
theorem uses_bound : ElExp C e τ → ∀ lv ∈ e.freeLongVars, (C.lookupVal lv).isSome
theorem not_elab_of_scope : scopeOK B m = false → ¬ ∃ B' E, ElModule B m B' E
theorem not_elab_of_shape : shapeOK B m = false → ¬ ∃ B' E, ElModule B m B' E
theorem not_legal_of_syn : ¬ Src.SynOKSet sp → ¬ LegalProgram B sp
theorem not_legal_of_scope (h : progScopeOK B (Src.deriveProgram (Src.canonOrder sp)) = false) : ¬ LegalProgram B sp
theorem not_legal_of_shape (h : progShapeOK B (Src.deriveProgram (Src.canonOrder sp)) = false) : ¬ LegalProgram B sp
theorem not_legal_of_further (h : progFurtherDec B (Src.deriveProgram (Src.canonOrder sp)) = false) : ¬ LegalProgram B sp
theorem not_legal_of_main (h : progMainWrong B (Src.deriveProgram (Src.canonOrder sp)) = true) : ¬ LegalProgram B sp
theorem not_legal_of_ports (h : portsDisjointDec B (Src.deriveProgram (Src.canonOrder sp)) = false) : ¬ LegalProgram B sp
```

`uses_bound` by mutual induction on the derivation, with `ElPat C p VE τ → VE.keys = p.boundVars`
(patterns bind exactly their variables) and the same for constructors and type constructors.
`not_elab_of_scope`: every derivation of the module elaborates each declaration in a context
contained in `moduleCtx` plus the module's declarations (r:sm-module, r:sm-topdec-seq), so an
identifier bound there is bound in no derivation. The program-level versions: `ElProgram` needs
`ElModule` for each module (via `PrincipalModDer` and `checkModule_sound`); for a module after
the first, the basis is built from principal derivations of the earlier ones, which these
deciders do not need, because they read only `T`, `ME` up to type names, and the names the
interfaces bind, which every derivation of the earlier modules gives alike (`elabTypes_complete`,
`annotated` schemes, and the interface's domain, which `expose` fixes). `not_legal_of_further` by
`further_correct` at every derivation (in particular the principal one, if there is one).
`not_legal_of_main`: `progMainWrong` holds when `main` is annotated with a type that is neither a
`Node` nor a `Program` type with a port flags type, or when `forcedHead` gives a head other than
`Node` and `Program` (BadMainTypeTypeVariableMainTest: `main = []`, head `List`).

### Group 9: the master theorems

```lean
def certOK (B : SBasis) (sp : Src.SProgram) (a : AProgram) : Bool :=
  let p := Src.deriveProgram (Src.canonOrder sp)
  Src.decSynOK (Src.canonOrder sp) && checkProgramFor B p a && progFurtherDec B p &&
    mainTransfer B p && portsDisjointDec B p
theorem legal_of_cert (B sp a)
    (hinf : inferProgram B (Src.deriveProgram (Src.canonOrder sp)) = .ok a)
    (h : certOK B sp a = true) :
    InferPrincipalFor B (Src.deriveProgram (Src.canonOrder sp)) → LegalProgram B sp
/-- The weaker statement when mainTransfer fails: the program elaborates, by a derivation that
    meets the further restrictions (and so every derivation does). -/
def CertProgram (B : SBasis) (sp : Src.SProgram) : Prop :=
  Src.SynOKSet sp ∧ ∃ a, checkProgramFor B (Src.deriveProgram (Src.canonOrder sp)) a = true ∧
    ∀ am ∈ a, FurtherModAt B a am
theorem cert_of_check (B sp a) (h : certOKWeak B sp a = true) : CertProgram B sp
```

Proof of `legal_of_cert`, for a program of one module `m` in `B`: `checkModule_sound` gives a
derivation, so the hypothesis gives a principal `P`; `furtherMod_correct` and the decider give
`FurtherMod B P`; `mainTransfer` gives the Chapter 9 condition for `P`'s scheme of `main`
(annotated: `annotated_main_scheme`, the same in every derivation; view: `forcedHead_sound` in
`P`, so `P`'s type of `main` has head `Node`, and `dflt` keeps the head; program: head and flags
likewise, `Port` decided); `ports_det` gives `P`'s port environment, so `portsDisjointDec`
gives the side condition; then `r_p_stat_main_view` or `r_p_stat_main_program`. For more modules
(milestone 9c), the same for each, with the basis of each later module built from principal
derivations of the earlier ones; the certificate was checked in the basis built from the
certificate's own derivations, and the lemma

```lean
theorem elab_basis_mono (hle : B ≤ᵢ B') : ElModule B m B1 E1 → ∃ B1' E1', ElModule B' m B1' E1'
```

(`≤ᵢ`: the same type names up to a bijection, interfaces with the same domains, and each scheme
of `B'` at least as general, `GenS`) carries the elaboration over; the principal interfaces of the
earlier modules are at least as general as the certificate's by `InstanceOfMod`. Proof of
`elab_basis_mono`: by induction on the derivation, replacing each `Gen σ τ` premise at a basis
binding by `gen_trans`. If `elab_basis_mono` is not done when 9c is accepted, the 9 helper tests
get `cert_` theorems instead.

### Group 10: B4 for elaboration (stretch, `Stat/Independence.lean`)

```lean
def GroupingIndependentElab : Prop :=
  ∀ C (ds : List Src.SDef) body cs cs', Src.Grouping.ValidNumbering ds.length (Src.letRefers ds) cs →
    Src.Grouping.ValidNumbering ds.length (Src.letRefers ds) cs' →
    ∀ τ, ElExp C (Src.letsOf ds cs body) τ ↔ ElExp C (Src.letsOf ds cs' body) τ
```

Proof sketch (not required for acceptance): adjacent independent components commute, by
weakening (`C + VE` with variables not free in the phrase) and exchange lemmas for the rules, and
`closGroup` adds no free variable to the context (Appendix A's argument). Until proved, the
theorems hold for the canonical choice (plan, B4).

## Translator changes

- `ExtractStaticBasis.elm` gains `--lean`: it writes `Generated/StaticBasis.lean` from
  `static-basis.json` (format of section 6), and `--check` compares it too.
- `Translate.elm` writes `Generated/StaticLibrary.lean`: for each module of `libraryValues`, the
  vendored file is parsed with elm-syntax and its type declarations and the annotations of the
  listed values are written with `Translate.Source` (step 8) as `Src.STopDec` and `Src.STy` terms.
  A value without an annotation in elm/core is an error. `--check` covers the file.
- No change to Part I's path.

Data format of `Generated/StaticLibrary.lean`:

```lean
/-- From definition/library/elm-core-1.0.5/src/List.elm (elm/core 1.0.5). -/
def lib_List : ModId × List Src.STopDec × List (Var × Src.STy) :=
  ("List", [], [("map", Src.tfn (Src.tfn (Src.tv "a") (Src.tv "b")) (Src.tfn (Src.tcon "List" [Src.tv "a"]) (Src.tcon "List" [Src.tv "b"]))), ...])
def libModules : List (ModId × List Src.STopDec × List (Var × Src.STy)) := [lib_List, lib_Tuple, lib_Maybe, ...]
```

## Tests gained

Milestone **9a (Core)**: for each of the 381 programs translated today whose source has no
`type` declaration (manifest status `translated`, no line beginning `type`), and any other
compile-success test with no type declaration, no port, no helper and `basis` in
`{B0, harness, library}`, a theorem

```lean
theorem core_<project>_<Test> : ∃ τ, Stat.ElExp (Stat.coreCtx Stat.Btest s) (Stat.coreOf s) τ ∧ ...
```

where `coreOf s` is the main module's top-level value groups as nested `let`s around `main`'s
expression and `coreCtx` the context of the default and written imports, computed by
`elabImports` (both milestone scaffolding, replaced by `r:sm-module` in 9b), together with
`FurtherProp` at the certificate. Expected: at least 381.

Milestone **9b (one-module programs)**: `legal_` or `cert_` for every compile-success test of one
module with `basis` in `{B0, harness, library}`: 613 (40 + 540 + 33). The split between `legal_`
and `cert_` is measured (`mainTransfer`); every `cert_` is listed with the reason.

Milestone **9c (helpers)**: the 9 `helper` tests (step 7, section 3.2): 622 positive in all.

Milestone **9d (refusals)**: `refuse_` for the 9 `further` tests (exhaustiveness 7,
irredundancy 2, named in [step 7](step-07-classify.md), section 2.5) and the
`static-deterministic` tests (28 provisional: scope 1, type-expression 13, module 6, main 6,
arity 2, named in step 7, section 2.4). The 31 `syntactic` tests also get `refuse_` from step 8's
theorems by `not_legal_of_syn`. Expected: 37 + 31 = 68 `refuse_` theorems.

Every positive theorem is under `InferPrincipalFor` (D11) and names `[parse] [harness]
[principal] [params]`; every refusal is unconditional and names `[parse] [harness] [params]`.

## Acceptance

```
site/node_modules/.bin/elm-pages run definition/tools/src/ExtractStaticBasis.elm --lean
node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm
node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check
export PATH=$HOME/.elan/bin:$PATH
(cd definition/mechanisation/standard-elm-mech && lake build)
(cd definition/mechanisation/standard-elm-mech && lake exe certify && lake build && lake exe certify --check)
(cd definition/mechanisation/standard-elm-mech && lake exe run-examples)
(cd definition/mechanisation/standard-elm-mech && lake env lean scripts/check-axioms.lean)
```

Expected, per milestone:

1. **9a**: `lake build` with no `sorry`; the rule-count test passes (45 `r_s_*`); `certify`
   prints `core: N programs, N certified, 0 failed` with N ≥ 381, and the kernel time and peak
   memory of the first shard; `check-axioms` clean.
2. **9b**: the rule-count test passes (20 constructors for the 19 labels of Chapter 5, 3 for
   Chapter 9); `certify` prints `legal: L, cert: K, failed: 0` with `L + K = 613`, every failure
   investigated and recorded as a finding before acceptance; `default_imports_test`,
   `Btest_agrees` proved.
3. **9c**: `L + K = 622`.
4. **9d**: `refused: 37 (further 9, static-deterministic 28), 0 failed`; with step 8's 31, 68
   `refuse_` theorems.
5. `run-examples` totals unchanged (this step adds no dynamic check); the memory budget holds on
   a clean build, the per-shard peak of `Certs/` recorded; `native_decide` theorems listed.
6. Reports: the mechanisation report's dated block gives the counts (`legal`, `cert`, `refuse`,
   native), the README's Files table gets one row per new file and the trust tags, and
   `runner/mechanisation-data.js` links each static rule page to its constructor (pattern
   `r_(s|sm|p)_<slug>`, already in the conventions).

## Risks and fallbacks

- **Certificate size and kernel time.** Types at every node may make certificates five to twenty
  times the program's size. Fallback, with the same theorem statements: store types only at
  leaves (constants, occurrences, `[]`) and binders (pattern variables, lambda parameters, `let`
  groups), and let the checker synthesise the others bottom-up. Second fallback: `native_decide`
  for the programs over budget, listed.
- **The inference fails on a program Elm accepts.** Expected for some; each is diagnosed. A
  failure of the book (a rule too strict) goes to the ambiguity log; the test's theorem waits.
- **`mainTransfer` covers too few programs.** Then more tests get `cert_` and wait for step 11;
  `forcedHead` can be extended (more spine shapes) without changing any statement.
- **The book's module property is false** as the book stands (item 1 below, plan finding B6).
  Theorems are stated under `InferPrincipalFor` of their own program, so a false instance can only
  affect the program it is false for; step 11 proves it for every coherent program (every test).
- **Nested inductives** as in step 8: mutual fallback.
- **Size of the step.** The milestones are independent enough that 9a can be accepted before
  Chapter 5 is started; 9d needs only the deterministic functions and the decider.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **`r:sm-topdec-seq` on type declarations gives different results (book finding, extends B5).**
   The book says of `r:sm-topdec-types`: "Rule r:sm-topdec-seq also applies to such a phrase,
   splitting it at one of its separators. Where both rules apply they give the same result."
   They do not when a custom type mentions a later local alias that has the name of an imported
   type constructor. For

   ```elm
   module M exposing (..)
   type T = T String
   type alias String = Int
   ```

   `r:sm-topdec-types` elaborates `T`'s constructor in `C ⊕ TE`, where `String` is the local alias,
   giving `T : Int -> T`; splitting at the separator elaborates `type T = T String` in `C`, where
   `String` is the basis type, giving `T : String -> T`. Both are derivations of the module, with
   different environments and no variables, so neither is an instance of the other, and the module
   has no principal derivation: the property of `sec:static-modules-principal` fails for it, and
   with it the plan's global hypothesis `PrincipalExists`. A theorem stated under a false global
   hypothesis is vacuous for every program. This specification therefore states every positive
   theorem under a hypothesis about its own program. **Resolved in the plan (2026-11-11):** D11
   now uses `InferPrincipalFor B p`, defined above, and the plan records this as finding B6. The book should restrict `r:sm-topdec-seq` to separators outside a
   type-declaration phrase, or drop the sentence. (Ambiguity log; Appendix A's ordering prevents
   the same problem between aliases, but the custom types always come first.)
2. **D11 does not by itself give `main`'s type.** Under `PrincipalExists` the principal derivation
   exists, but a certificate that is not principal says nothing about the principal scheme of an
   unannotated `main` (`main = Debug.todo "x"` checks at `Node`-typed instances, while its
   principal scheme is a variable). The specification adds principality-free transfer lemmas
   (`annotated_main_scheme`, `forcedHead_sound`) and states the weaker `CertProgram` where they do
   not apply; those tests reach `LegalProgram` in step 11.
3. **Programs with helper modules** need `elab_basis_mono` (the later module elaborates in the basis
   of the principal derivations of the earlier ones). The plan does not mention it; it is milestone
   9c here, with `cert_` as fallback.
4. **Where certificates are written.** The conventions reserve `Generated/` for the translator.
   Certificates are produced by the Lean inference, so this specification adds
   `StandardElmMech/Certs/`, written only by `lake exe certify` (with `--check`). The conventions'
   file table should list it.
5. **Rule count.** "45 + 19 + 3" constructors becomes 45 + 20 + 3: the bare syntax of step 8 has
   one node for a type-declaration phrase, and `r:sm-topdec-seq` needs a second constructor there
   (item 1 shows it cannot be dropped without changing the book).
6. **Coordination with step 10.** Step 10's specification runs the inference inside the kernel
   in each per-test theorem (its choice 8). This specification runs it compiled, in `lake exe
   certify`, and has the kernel check only the written certificate, which is cheaper and trusts
   no more (the inference is unverified either way). Step 10 can use `a_<project>_<Test>`
   unchanged; if it keeps its choice, nothing here changes. Step 10 also states its theorems under
   `InferPrincipal`, which agrees with item 2 above: without principality of the found derivation,
   the scheme of an unannotated `main` cannot be transferred.
7. **B2 is followed literally.** The decider implements the book's text (the "no set of constants"
   clause for exhaustiveness only; complete finite literal domains in irredundancy). The finding
   stays open; the decider changes in one place (`useful`'s literal completeness) if the book
   changes.
