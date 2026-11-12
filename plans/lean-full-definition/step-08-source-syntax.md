# Step 8: source syntax, derived forms, syntactic restrictions

Part of [the plan](../lean-full-definition.md), Part II. Follows
[conventions.md](conventions.md). Status: specified 2026-11-11, not started.

## Goal

1. **The source syntax in Lean** (gap G2-8): every program elm-syntax parses, as written, with
   operator chains as elm-syntax groups them (the `[parse]` trust), type expressions,
   annotations, custom types, aliases, ports, headers and imports.
2. **The bare syntax** (G2-9) between source and reduced: the phrase classes of Chapters 2 and 3
   after the derived forms, with type expressions, annotations and unspecialised constants. The
   static rules of step 9 are stated on it.
3. **The derived forms of Appendix A as a Lean function** from source to bare (G2-10, finding B4),
   with one canonical choice for the two groupings, generated from the same table as
   `Derived.lean`, and checked to agree with `Derived.lean` on the 491 programs translated today.
4. **The 27 syntactic restrictions decidable on a syntax tree** (G2-11, P2-4), each a `Prop` as the
   book states it, with a decider and a theorem `decide_R p = true ↔ R p`; the nine restrictions
   about characters, tokens and layout are listed as trusted to the parser.
5. **A new translator path** (G2-13) that writes the source syntax of every program elm-syntax
   parses, compile-error tests included.
6. **Gains**: a theorem `¬ SynOKSet` for each of the 31 tests step 7 classed `syntactic`, and a
   theorem `SynOK` ("meets the AST-decidable restrictions") for every written compile-success
   test.

## Prerequisites

- Step 7: `static-classification.json` (the class `syntactic` and its 31 tests, the parse
  column) and `static-basis.json` (only for the 19 module identifiers of `Dom ME0`, used by
  `res:program-modules-distinct` and `res:program-import-order`).
- Existing: `StandardElmMech/Syntax.lean` (`LongId`, `Op`, `Var`, `Lab`, `ModId`), `Derived.lean`
  and its generator `definition/tools/src/GenerateDerivedForms.elm` with
  `DerivedForms/{Table,Term,ToLean,ToLatex}.elm`.
- Coordination with Part I step 3 (plan, "Order of work"): step 3 adds a module-aware translator
  path whose grouping of a module's declarations step 8 supersedes. Step 8 does not delete
  step 3's path; it moves the grouping functions (`reach`, `components`) to
  `Src/Grouping.lean`, and step 3's code (or today's `Derived.lean`) calls them, so that both
  paths use one grouping. If step 3 has not landed, the same holds for `Derived.lean` alone.

## Lean definitions

All new files are in `StandardElmMech/Src/`, namespace `StandardElm.Src`, and import no `Lean`
meta library, except `Src/SynCommand.lean`.

| File | Contents |
|------|----------|
| `Src/Syntax.lean` | the source syntax (section 1) |
| `Src/Bare.lean` | the bare syntax (section 2) |
| `Src/Notation.lean` | short constructors used by the Generated files |
| `Src/DerivedRows.lean` | generated: the row functions of Appendix A over the bare types (section 3.1) |
| `Src/Graph.lean` | reachability on `Fin n`-indexed graphs, its decider and its correctness (section 4) |
| `Src/Grouping.lean` | the canonical numbering of components and of aliases, the book's relation, validity (section 3.3) |
| `Src/Derive.lean` | the derived-forms function, source to bare (section 3.2) |
| `Src/Traverse.lean` | occurrences, binding sites, free and direct occurrences (section 5.1) |
| `Src/Restrictions.lean` | the 27 restrictions, their deciders, the iff theorems, `SynOK` (section 5) |
| `Src/SynCommand.lean` | the command `#syn_theorems` (imports `Lean`) |
| `CompareDerived.lean` (package root) | the executable `compare-derived` (section 3.4) |

### 1. Source syntax (`Src/Syntax.lean`)

Lists are used for sequences (nested inductives). Every function over these types is written by
structural recursion (`termination_by structural`), so that the kernel reduces it; see "Risks"
for the fallback.

```lean
namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)

/-- A special constant as written (Chapter 2, sec:syntax-core-constants), before number
    specialisation. `int n`: a decimal or hexadecimal integer constant denoting the
    non-negative integer `n` (unbounded; its value as an Int is `norm n`, which A31 uses).
    `float m e`: the floating point constant m × 10^e, exactly as written. `char c` and `str s`
    after escapes. -/
inductive SLit where
  | int (n : Nat)
  | float (m : Nat) (e : Int)
  | char (c : Char)
  | str (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- Type expressions as written (Figure fig:core-grammar-types). elm-syntax drops parentheses
    in types, so there is no `paren`. `tuple` has 2 or 3 components by the grammar; `ext r fs`
    is `{ r | fs }`, whose `fs` may be empty only in a text that breaks
    res:core-record-update-form. -/
inductive STy where
  | var (a : String)
  | con (c : LongId) (args : List STy)
  | unit
  | tuple (ts : List STy)
  | record (fs : List (Lab × STy))
  | ext (r : String) (fs : List (Lab × STy))
  | fn (a b : STy)

/-- Patterns as written (Figure fig:core-grammar-patterns, with the derived list pattern). A
    float constant is representable so that res:core-no-float-pattern can be stated. -/
inductive SPat where
  | wild
  | lit (l : SLit)
  | var (x : Var)
  | unit
  | con (k : LongId) (args : List SPat)       -- longcon atpat1 ... atpatn, n ≥ 0
  | tuple (ps : List SPat)                    -- 2 or 3
  | list (ps : List SPat)                     -- [p1, ..., pn], n ≥ 0; [] is n = 0
  | record (ls : List Lab)                    -- { l1, ..., ln }
  | cons (p1 p2 : SPat)
  | as (p : SPat) (x : Var)
  | paren (p : SPat)

mutual
/-- Expressions as written. Operator applications are as elm-syntax groups them, by the
    fixities of Figure fig:core-fixities ([parse]); `&&` and `||` are `binop` like the others. -/
inductive SExp where
  | lit (l : SLit)
  | var (x : LongId)
  | con (k : LongId)                          -- includes a record alias's constructor
  | opVal (o : Op)                            -- (opv)
  | unit
  | tuple (es : List SExp)                    -- 2 or 3
  | list (es : List SExp)                     -- [e1, ..., en], n ≥ 0
  | record (fs : List (Lab × SExp))
  | update (x : Var) (fs : List (Lab × SExp)) -- { x | fs }; fs = [] breaks res:core-record-update-form
  | accessor (l : Lab)                        -- .lab
  | access (e : SExp) (l : Lab)               -- atexp.lab
  | neg (e : SExp)                            -- -atexp
  | paren (e : SExp)
  | app (f : SExp) (args : List SExp)         -- f a1 ... an, n ≥ 1
  | binop (o : Op) (l r : SExp)
  | ifte (arms : List (SExp × SExp)) (els : SExp)
      -- if c1 then e1 else if c2 then e2 ... else e: the maximal chain whose else-branches are
      -- `if` without parentheses; arms ≠ []
  | lam (ps : List SPat) (body : SExp)        -- \p1 ... pn -> e, n ≥ 1
  | caseE (e : SExp) (rules : List (SPat × SExp))
  | letE (defs : List SDef) (body : SExp)
/-- A definition: `var [: ty] atpat1 ... atpatm = exp` (m ≥ 0) or `atpat = exp`. -/
inductive SDef where
  | fn (x : Var) (ann : Option STy) (ps : List SPat) (e : SExp)
  | pat (p : SPat) (e : SExp)
end

inductive SItem where
  | var (x : Var) | op (o : Op) | ty (c : String) | tyAll (c : String)
inductive SExposing where
  | all
  | items (is : List SItem)
structure SImport where
  mod : ModId                -- dotted, "Platform.Cmd"
  alias : Option ModId       -- as written; res:modules-import-alias requires no dot
  exposing : Option SExposing
inductive STopDec where
  | custom (c : String) (params : List String) (ctors : List (String × List STy))
  | alias (c : String) (params : List String) (t : STy)
  | port (x : Var) (t : STy)
  | value (d : SDef)          -- `.pat` only in a text that breaks res:modules-no-top-pattern
structure SHeader where
  isPort : Bool
  name : ModId
  exposing : SExposing
structure SModule where
  header : SHeader
  imports : List SImport      -- as written, without the default imports
  decls : List STopDec        -- in the order written
/-- A program: its modules, the main module last (Chapter 9, sec:programs-syntax). -/
structure SProgram where
  project : String
  name : String
  modules : List SModule
```

No source positions are kept: no theorem names the offending phrase (the translator's manifest
and the step-7 JSON say where it is, for the reader). Constants are kept as decoded, which is all
A31 and `res:core-no-float-pattern` need: an integer by its value before `norm` (so `0x10` and
`16` are equal, as A31 wants), a character by its code point (`'A'` and `'\u{0041}'` equal), a
string by its characters.

### 2. Bare syntax (`Src/Bare.lean`)

The bare grammar of Chapters 2 and 3, with type expressions and annotations kept and constants
unspecialised. It is the reduced syntax of `Syntax.lean` (Chapter 6,
`sec:dynamic-core-reduced`) before number specialisation and type erasure. The constructor
names are those of `Syntax.lean`, on purpose: the generated row functions (3.1) are then the same
text over either set of types.

```lean
mutual
inductive BTy where
  | tyvar (a : String)
  | record (row : Option BTyRow)              -- { [tyrow] }
  | openRecord (r : String) (row : BTyRow)    -- { tyvar | tyrow }
  | unit
  | tuple (t1 t2 : BTy) (t3 : Option BTy)
  | con (c : LongId) (args : List BTy)        -- longtycon ty1 ... tyk
  | fn (t1 t2 : BTy)
  | paren (t : BTy)
inductive BTyRow where
  | field (l : Lab) (t : BTy) (rest : Option BTyRow)
end

mutual
inductive BAtPat where
  | wild | scon (sc : SLit) | var (x : Var) | con (lc : LongId) | unit
  | tuple (p1 p2 : BPat) (p3 : Option BPat) | nil | record (row : Option BPatRow)
  | paren (p : BPat)
inductive BPatRow where
  | field (l : Lab) (rest : Option BPatRow)
inductive BPat where
  | atpat (a : BAtPat) | con (lc : LongId) (args : List BAtPat)
  | cons (p1 p2 : BPat) | as (p : BPat) (x : Var)
end

mutual
inductive BAtExp where
  | scon (sc : SLit) | var (lv : LongId) | con (lc : LongId) | op (o : Op) | unit
  | tuple (e1 e2 : BExp) (e3 : Option BExp) | nil | record (row : Option BExpRow)
  | update (x : Var) (row : BExpRow) | letE (d : BDec) (e : BExp) | paren (e : BExp)
inductive BExpRow where
  | field (l : Lab) (e : BExp) (rest : Option BExpRow)
inductive BExp where
  | atexp (a : BAtExp) | app (e : BExp) (a : BAtExp) | lam (p : BAtPat) (e : BExp)
  | caseE (e : BExp) (m : BMatch)
inductive BMatch where
  | mk (mr : BMRule) (rest : Option BMatch)
inductive BMRule where
  | mk (p : BPat) (e : BExp)
inductive BDec where
  | val (vb : BValBind)
/-- `var [: ty] = exp [and valbind]` or `atpat = exp` (r:s-valbind-var, r:s-valbind-pat). -/
inductive BValBind where
  | var (x : Var) (ann : Option BTy) (e : BExp) (rest : Option BValBind)
  | pat (p : BAtPat) (e : BExp)
end

/-- Modules (Figures fig:grammar-modules and fig:grammar-top-level-declarations). -/
inductive BItem where | var (x : Var) | op (o : Op) | ty (c : String) | tyAll (c : String)
inductive BExpList where | all | items (is : List BItem)
structure BImport where
  mod : ModId
  alias : Option ModId
  exposing : Option BExpList
/-- conbind: `con ty1 ... tyn [| conbind]`, as a list. -/
abbrev BConBind := List (String × List BTy)
/-- datbind: `tycon tyvarseq = conbind [and datbind]`, as a list. -/
abbrev BDatBind := List (String × List String × BConBind)
/-- typbind: `tycon tyvarseq = ty`. -/
structure BTypBind where
  c : String
  params : List String
  t : BTy
inductive BTopDec where
  | value (vb : BValBind)                            -- r:sm-topdec-value
  | types (db : Option BDatBind) (tbs : List BTypBind)
      -- `[type datbind ;] type alias typbind1 ; ... ; type alias typbindl` (r:sm-topdec-types);
      -- l ≥ 1 when db = none
  | port (x : Var) (t : BTy)                         -- r:sm-topdec-portout / -portin
  | seq (d1 d2 : BTopDec)                            -- r:sm-topdec-seq
structure BHeader where
  isPort : Bool
  name : ModId
  exposing : BExpList
structure BModule where
  header : BHeader
  imports : List BImport        -- as written; the default imports are added by r:sm-module
  body : Option BTopDec         -- none: a module with no declarations
structure BProgram where
  modules : List BModule
```

**How Part I's reduced syntax is computed from it** (G2-9; done in step 10, recorded here so the
types are fit for it): number specialisation reads the annotated derivation of step 9 and maps
each `SLit.int n` occurrence to `SCon.int n` or `SCon.intF n` of `Syntax.lean` and makes the
copies of Section `sec:dynamic-core-numbers`; type erasure drops `ann`, every `BTy` and the type
declarations; a port's payload type is the `τ'` that `r:sm-topdec-portout`/`-portin` gives, read
from the annotated derivation, mapped to Part I's payload-type inductive by the function and
lemma step 10 specifies (P2-15).

### 3. The derived forms

#### 3.1 Row functions, generated (`Src/DerivedRows.lean`)

`DerivedForms/ToLean.elm` gets a target record:

```elm
type alias Target =
    { exp : String, atExp : String, pat : String, atPat : String, namespace : String }

reduced : Target   -- { exp = "Exp", atExp = "AtExp", pat = "Pat", atPat = "AtPat", namespace = "StandardElm.D" }
bare : Target      -- { exp = "BExp", atExp = "BAtExp", pat = "BPat", atPat = "BAtPat", namespace = "StandardElm.Src.D" }
```

and `ToLean.definitions : Target -> List Row -> Result String String` prints the signatures with
the target's type names; the bodies are unchanged (they use only constructor names, which the two
syntaxes share). `GenerateDerivedForms.elm` writes a third region, between
`-- BEGIN GENERATED derived forms` and `-- END GENERATED derived forms` in
`Src/DerivedRows.lean`. The region holds, over the bare types, exactly the functions of
`Derived.lean`'s region: `bin`, `ifte`, `lams`, `neg`, `accessor`, `listP`, `ifChain`,
`andalso`, `orelse`, `listE`, `access`. The rows `df:function-binding`, `df:let-grouping` and
`df:module-grouping` stay hand-written (their `lean` field is `HandWritten`), now in
`Src/Derive.lean` and `Src/Grouping.lean`.

#### 3.2 The function (`Src/Derive.lean`)

```lean
namespace StandardElm.Src

def deriveTy : STy → BTy
def deriveAtPat : SPat → BAtPat        -- an atomic pattern; a non-atomic one is put in `.paren`
def derivePat : SPat → BPat
def deriveAtExp : SExp → BAtExp        -- an atomic expression; a non-atomic one in `.paren`
def deriveExp : SExp → BExp
/-- df:function-binding: `x [: ty] p1 ... pm = e` gives `x [: ty] = \p1 ... pm -> e`
    (via df:lambda-params when m ≥ 2, the bare lambda when m = 1, `e` when m = 0). -/
def deriveDef : SDef → BValBind         -- a binding without `and`
/-- df:let-grouping (n ≥ 2), and the bare `let valbind in exp` (n = 1). -/
def deriveLet (ds : List SDef) (body : BExp) : BExp
/-- df:module-grouping. -/
def deriveTopDecs (ds : List STopDec) : Option BTopDec
def deriveModule (m : SModule) : BModule
def deriveProgram (p : SProgram) : BProgram
```

The clauses, row by row (labels are those of `appendix-derived-forms.tex`):

| Source | Bare | Row |
|--------|------|-----|
| `lit l`, `var x`, `con k`, `opVal o`, `unit` | `.atexp (.scon l)`, `.atexp (.var x)`, `.atexp (.con k)`, `.atexp (.op o)`, `.atexp .unit` | bare |
| `tuple [a, b]`, `tuple [a, b, c]` | `.atexp (.tuple (dE a) (dE b) none)`, `... (some (dE c))` | bare |
| `list []` | `.atexp .nil` | bare |
| `list es`, `es ≠ []` | `D.listE (es.map dE)` | `df:list` |
| `record fs`, `update x fs` | `.atexp (.record (row fs))`, `.atexp (.update x (row' fs))` | bare |
| `accessor l` | `.atexp (D.accessor l)` | `df:field-accessor` |
| `access e l` | `.atexp (D.access (dA e) l)` | `df:field-selection` |
| `neg e` | `.atexp (D.neg (dA e))` | `df:negation` |
| `paren e` | `.atexp (.paren (dE e))` | bare |
| `app f [a1, ..., an]` | `(... (.app (dE f) (dA a1)) ...) (dA an)` | bare |
| `binop "&&" l r`, `binop "\|\|" l r` | `D.andalso (dE l) (dE r)`, `D.orelse (dE l) (dE r)` | `df:and`, `df:or` |
| `binop o l r` | `D.bin o (dE l) (dE r)` | `df:infix` |
| `ifte [(c, t)] e` | `D.ifte (dE c) (dE t) (dE e)` | `df:if` |
| `ifte arms e`, `arms.length ≥ 2` | `D.ifChain (arms.map ...) (dE e)` | `df:if-chain` |
| `lam [p] b` | `.lam (dAP p) (dE b)` | bare |
| `lam ps b`, `ps.length ≥ 2` | `D.lams (ps.map dAP) (dE b)` | `df:lambda-params` |
| `caseE e rules` | `.caseE (dE e) (match rules)` | bare |
| `letE ds b` | `deriveLet ds (dE b)` | `df:let-grouping` |
| `SPat.list []`, `SPat.list ps` | `.nil`, `D.listP (ps.map dP)` | bare, `df:list-pattern` |

`dA e` is `deriveAtExp e`: for the forms that are atomic in the book (`lit`, `var`, `con`,
`opVal`, `unit`, `tuple`, `list`, `record`, `update`, `accessor`, `access`, `neg`, `paren`,
`letE`) the atomic phrase itself; for any other form, `.paren (deriveExp e)`. This is
`Derived.lean`'s `D.A`. The function is total: on a tree that breaks a syntactic restriction or
the grammar (a 4-tuple, an `ext` with no field, a top-level `.pat`), it returns a fixed phrase
(`.atexp .unit`, a one-field row, a `_ = ()` binding); every theorem about `derive` that matters
has `SynOK` among its hypotheses, and `Legal` (step 9) contains `SynOK` as a conjunct.

`deriveLet ds body`: when `ds = [d]`, `.atexp (.letE (.val (deriveDef d)) body)`; otherwise, with
`cs := Grouping.components ds.length (letRefers ds)`, the nest
`.atexp (.letE (.val (group cs_1)) (.atexp (.letE ... body)))` where `group [i1, ..., ip]` is
`deriveDef ds[i1] and ... and deriveDef ds[ip]` (members in increasing index, annotations kept,
section `sec:appendix-derived-forms-let`). A destructuring definition is never in a recursive
component of a legal program (`res:core-let-recursion`), so `group` of a component with a `.pat`
member and other members is junk, as for `Derived.lean`'s `groupBind`.

`deriveTopDecs ds` (section `sec:appendix-derived-forms-modules`): with `customs` the custom
types in order written, `aliases` the aliases, `vals` the ports and definitions,

1. `db := if customs = [] then none else some (customs.map toDatBind)`;
2. `tbs := (Grouping.aliasOrder aliases).map toTypBind` (each after every alias it mentions,
   section 3.3);
3. `vs := (Grouping.components vals.length (topRefers vals)).map toTopDec'`, a port alone in its
   component, a value component as one `BTopDec.value` group;
4. the result is the `seq` chain, right-nested, of `types db tbs` (omitted when `db = none` and
   `tbs = []`) followed by the `vs`, or `none` when there is nothing.

Refers-to is computed on the source, by free occurrences (`Src/Traverse.lean`): Appendix A says
"No equivalent form adds or removes a free occurrence of a variable", so the grouping is the same
before and after the other rows.

#### 3.3 The canonical choice (`Src/Grouping.lean`, finding B4)

```lean
namespace StandardElm.Src.Grouping

/-- The components of the graph on `0 .. n-1` whose edges are `refers`, each as its members in
    increasing order, listed so that a component comes after every component it refers to; among
    the components that may be placed next, the one with the least member comes first. This is
    `Derived.lean`'s `components`, moved here unchanged in its result. -/
def components (n : Nat) (refers : Nat → Nat → Bool) : List (List Nat)

/-- The aliases ordered so that each comes after every alias it mentions; among those that may
    come next, the one written first. -/
def aliasOrder (as : List STopDec) : List STopDec

/-- The book's relation (sec:appendix-derived-forms-let): `cs` partitions `0 .. n-1` into the
    classes of mutual reachability, each class sorted, and whenever a member of `cs[a]` refers to
    a member of `cs[b]` with `b ≠ a`, then `b < a`. -/
def ValidNumbering (n : Nat) (refers : Nat → Nat → Bool) (cs : List (List Nat)) : Prop :=
  (cs.flatten.Perm (List.range n)) ∧
  (∀ c ∈ cs, c.Pairwise (· < ·) ∧ c ≠ []) ∧
  (∀ c ∈ cs, ∀ i ∈ c, ∀ j < n, (Graph.Reach n refers i j ∧ Graph.Reach n refers j i) ↔ j ∈ c) ∧
  (∀ a b (ha : a < cs.length) (hb : b < cs.length), a ≠ b →
      (∃ i ∈ cs[a], ∃ j ∈ cs[b], refers i j = true) → b < a)

/-- The book's relation for aliases: a permutation in which each alias comes after the aliases
    it mentions. -/
def ValidAliasOrder (as order : List STopDec) : Prop
```

`Derived.lean`'s `reach` and `components` become `Grouping.reachB` and `Grouping.components`;
its `letDefs` calls `Grouping.components ds.length (refers ds)`. The phrases of the 491 programs
do not change (acceptance 4: `lake exe dump-phrases` gives the same output before and after).

The independence of the choice (A57 to A59, finding B4) cannot be stated in step 8, which has
neither elaboration nor evaluation. Step 8 states the relational form of the derived forms:

```lean
/-- `src` derives to `b` by Appendix A with some valid numbering of every let and of the
    module's ports and definitions, and some valid order of its aliases. -/
inductive DerivesTo : SModule → BModule → Prop
```

(one constructor per production, the let and module cases taking any `ValidNumbering` and
`ValidAliasOrder`). Step 9 states and, as a milestone, proves the independence for elaboration
(`Stat/Independence.lean`); step 10 states it for evaluation. Until each is proved, theorems
are about `deriveModule`, the canonical choice, as the plan says.

#### 3.4 Agreement with `Derived.lean` on the 491 programs (`lake exe compare-derived`)

For each test `T` translated today (manifest status `translated`) whose source is written by the
new path, the executable compares, check by check, the phrase the current translation builds
(`p.phrase ck` of `Examples.lean`, or step 3's module form if it has landed) with the phrase built
from `s_<project>_T` the same way: the canonical groups of the main module's top-level
definitions other than `main`, around the canonical groups of `main`'s `let` definitions other
than the `_ = Debug.log "label" e` checks, around `Debug.log "label" (e)`. Both are mapped into a
neutral syntax by:

- dropping annotations (the bare side has them, the reduced side does not);
- mapping `SLit.int n`, `SCon.int n` and `SCon.intF n` to one form `num n` (specialisation is
  step 10's business);
- removing the suffix `$...` that the translator gives to specialisation copies, and then
  removing, from each `let` chain, a binding of a name already bound by an earlier binding of
  that chain whose normalised right-hand side is equal (the copies collapse to the default
  copy).

Expected output: `491 programs, 1487 checks compared, 0 differ.` (the check count is
`run-examples`' total at the time; a difference is listed with both phrases and fails the
acceptance unless it is explained by a specialisation copy the collapse does not handle, in which
case the collapse is extended).

### 4. Reachability (`Src/Graph.lean`)

```lean
namespace StandardElm.Src.Graph

/-- One or more steps of `r` among `0 .. n-1`. -/
inductive Plus (n : Nat) (r : Nat → Nat → Bool) : Nat → Nat → Prop
  | step : i < n → j < n → r i j = true → Plus n r i j
  | trans : Plus n r i j → Plus n r j k → Plus n r i k

/-- Zero or more steps. -/
def Reach (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Prop := i = j ∨ Plus n r i j

/-- The targets reachable from `i` in at most `k` steps, by iteration. -/
def reachIn (n : Nat) (r : Nat → Nat → Bool) : Nat → Nat → List Nat
def plusB (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Bool   -- j ∈ step from reachIn n r n i
def reachB (n : Nat) (r : Nat → Nat → Bool) (i j : Nat) : Bool := i == j || plusB n r i j
def onCycleB (n : Nat) (r : Nat → Nat → Bool) (i : Nat) : Bool := plusB n r i i
```

## Theorems

### Grouping and reachability

```lean
theorem Graph.plusB_iff (n r i j) (hi : i < n) (hj : j < n) : plusB n r i j = true ↔ Plus n r i j
theorem Graph.reachB_iff (n r i j) (hi : i < n) (hj : j < n) : reachB n r i j = true ↔ Reach n r i j
theorem Grouping.components_valid (n r) : ValidNumbering n r (components n r)
theorem Grouping.aliasOrder_valid (as) (h : ∀ i, ¬ Graph.Plus as.length (mentions as) i i) :
    ValidAliasOrder as (aliasOrder as)
theorem derive_derivesTo (m : SModule) (h : ModuleOK m) : DerivesTo m (deriveModule m)
```

Proof methods. `plusB_iff`: `→` by induction on the iteration count (each element of `reachIn`
has a path); `←` by the path-shortening lemma: a `Plus` path between nodes `< n` has a sub-path of
at most `n` steps without a repeated node (induction on the path's length, cutting at the first
repeated node with `List.Nodup` and a length bound). `components_valid`: partition and
mutual-reachability by `reachB_iff`; the order by strong induction on the number of components
left to place, with the lemma that among the unplaced components one refers only to placed
components or itself (the condensation of a finite graph is acyclic: a cycle of components would
merge them). `aliasOrder_valid` the same, on the acyclic "mentions" graph (`res:modules-alias-
not-recursive`, which `ModuleOK` includes). `derive_derivesTo` by structural induction, using the
two validity theorems at the let and module cases.

### The syntactic restrictions

For each restriction `R` of the table in section 5, in `Src/Restrictions.lean`:

```lean
def R : SModule → Prop            -- or SProgram → Prop for the five program restrictions
def decR : SModule → Bool         -- or SProgram → Bool
theorem decR_iff (m : SModule) : decR m = true ↔ R m
instance : DecidablePred R := fun m => decidable_of_iff _ (decR_iff m)
```

and

```lean
def ModuleOK (m : SModule) : Prop := RowLabelsDistinct m ∧ RecordUpdateForm m ∧ ... (22 conjuncts)
def ProgramOK (p : SProgram) : Prop := ModulesProgram p ∧ ModulesDistinct p ∧ ImportOrder p ∧
  ModulesReachable p ∧ ProgramMain p
def SynOK (p : SProgram) : Prop := (∀ m ∈ p.modules, ModuleOK m) ∧ ProgramOK p
/-- The program as written is the set of its modules (sec:programs-syntax): some sequence of
    them, with the same main module, meets the restrictions. -/
def SynOKSet (p : SProgram) : Prop :=
  ∃ q : SProgram, q.modules.Perm p.modules ∧ q.modules.getLast? = p.modules.getLast? ∧ SynOK q
def decSynOK (p : SProgram) : Bool
theorem decSynOK_iff (p : SProgram) : decSynOK p = true ↔ SynOK p
/-- The canonical order: modules in a topological order of imports (ties by module name), the
    given main module last. -/
def canonOrder (p : SProgram) : SProgram
theorem synOKSet_iff (p : SProgram) : SynOKSet p ↔ SynOK (canonOrder p)
theorem synOK_of_dec {p} (h : decSynOK p = true) : SynOK p
theorem notSynOKSet_of_dec {p} (h : decSynOK (canonOrder p) = false) : ¬ SynOKSet p
```

Proof methods. Each `decR_iff` unfolds both sides: the restrictions that are list conditions
(`Nodup`, `∀ x ∈ l`) by `simp` with `List.all_eq_true`, `List.nodup_iff`-style lemmas of core
(`List.Nodup` has a decidable instance in core); the ones defined by traversals (binding sites,
occurrences) by structural induction on `SExp`, with the motive stated for `SExp`, `SDef` and their
lists at once; the four cycle restrictions (`LetRecursion`, `AliasNotRecursive`,
`ValueRecursion`, `ModulesReachable`) through `Graph.plusB_iff`/`reachB_iff`. `synOKSet_iff`:
every restriction but `ImportOrder` is invariant under a permutation of the modules that keeps
the last one (each is a conjunction over modules, or a `Nodup` over all modules), and a
permutation meets `ImportOrder` exactly when the import graph among the program's modules is
acyclic, in which case `canonOrder` (Kahn's algorithm) meets it (lemma `kahn_topological`).

### Per test (written by `#syn_theorems`)

```lean
theorem syn_<project>_<Test> : Src.SynOK s_<project>_<Test> := Src.synOK_of_dec (by decide +kernel)
theorem nosyn_<project>_<Test> : ¬ Src.SynOKSet s_<project>_<Test> :=
  Src.notSynOKSet_of_dec (by decide +kernel)
theorem nosyn_<project>_<Test>_<slug> : ¬ Src.Holds Src.<R> s_<project>_<Test> :=
  fun h => absurd ((Src.decHolds_iff _ _).2 h) (by decide +kernel)
```

`Holds R p := ∀ m ∈ p.modules, R m` for a module restriction, `R p` for a program one; `<slug>`
is the label without `res:` and with `-` as `_` (`core_no_shadowing`). One `nosyn_..._<slug>` is
written for each restriction the program breaks. A theorem that the kernel cannot decide within
the memory budget is proved by `native_decide` and listed in the report.

## Section 5: the 27 restrictions

### 5.1 Traversals (`Src/Traverse.lean`)

```lean
/-- Every expression occurrence of a module (all subexpressions of every definition, port and
    `let`, preorder), every pattern occurrence (all subpatterns of every lambda parameter,
    function parameter, match rule and destructuring binding), every type-expression occurrence
    (all subterms of every annotation, port type, constructor argument and alias body), every
    `let`'s definition list. -/
def SModule.exps : SModule → List SExp
def SModule.pats : SModule → List SPat
def SModule.tys  : SModule → List STy
def SModule.lets : SModule → List (List SDef)
/-- The variables a pattern binds: its variable patterns, the labels of its record patterns, the
    variables after `as` (sec:syntax-core-restrictions, "Patterns and bound variables"). With
    multiplicity, in order. -/
def SPat.bound : SPat → List Var
def SDef.bound : SDef → List Var        -- [x] for `.fn x ...`, `p.bound` for `.pat p _`
/-- `x` occurs in `e` as an unqualified variable (`var ⟨none, x⟩`, or the variable of an update
    `{ x | ... }`), anywhere, binders not counted. -/
def occurs (x : Var) : SExp → Bool
/-- `x` occurs in a definition: in its right-hand side (its patterns and annotation hold no
    variable occurrence). -/
def occursDef (x : Var) : SDef → Bool
/-- Free occurrence: unqualified, not within the scope of a binding of `x` made inside `e`
    (appendix-derived-forms.tex, before the tables). -/
def occursFree (x : Var) : SExp → Bool
/-- Direct occurrence (res:modules-value-recursion): free, and not within a lambda expression,
    nor within the right-hand side of a `let` definition with parameters (whose equivalent form is
    a lambda, Appendix A). -/
def occursDirect (x : Var) : SExp → Bool
/-- A binding site with the variables it binds (with multiplicity) and the variables bound by the
    binding sites in whose scope it lies. -/
structure Site where
  binds : List Var
  outer : List Var
def SModule.sites : SModule → List Site
```

The binding sites and scopes are those of `syntax-core.tex`, `sec:syntax-core-restrictions`:
the parameters of a lambda (scope: its body); the parameters of a function binding, of a `let` or
of the top level (scope: its right-hand side); the pattern of a match rule (scope: its
expression); the definitions of one `let` taken together, binding the variables they define and
those their destructuring patterns bind (scope: the definitions and the body). The top-level
declarations are not a binding site of Chapter 2 (their shadowing is
`res:modules-no-shadowing`). A destructuring definition of a `let` is part of the `let`'s site
and not a second site (see "Issues with the plan", item 3).

### 5.2 The restrictions decided on the tree

`m` is a module, `p` a program; `vals m` the variables of its value declarations, `ports m` of its
port declarations, `customs m`, `aliases m` the type constructors of its custom types and
aliases, `ctors m` the constructors of its custom types, `recAliases m` the aliases whose body is
a record type without extension variable; `last p` the main module; `basisModuleIds` the 19
module identifiers of `Dom ME0` (Appendix C, `sec:appendix-static-basis-modenv`; a `def` checked
against `static-basis.json` by a test in step 9); `allImports m` the default imports of Figure
`fig:default-imports` followed by `m.imports`; `managersPlat : List Var := []` (the empty
platform, `[params]`).

| # | Label | Lean name | Statement (as the book states it) |
|--:|-------|-----------|-----------------------------------|
| 1 | `res:core-row-labels-distinct` | `RowLabelsDistinct m` | every `record fs` and `update x fs` in `m.exps` has `(fs.map (·.1)).Nodup`; every `record ls` in `m.pats` has `ls.Nodup`; every `record fs`, `ext r fs` in `m.tys` has `(fs.map (·.1)).Nodup` |
| 2 | `res:core-record-update-form` | `RecordUpdateForm m` | every `update x fs` in `m.exps` has `fs ≠ []`; every `ext r fs` in `m.tys` has `fs ≠ []` (the variable before `\|` is unqualified by the type of `update`) |
| 3 | `res:core-binding-site-distinct` | `BindingSiteDistinct m` | `∀ s ∈ m.sites, s.binds.Nodup` |
| 4 | `res:core-no-shadowing` | `NoShadowing m` | `∀ s ∈ m.sites, ∀ x ∈ s.binds, x ∉ s.outer` |
| 5 | `res:core-no-float-pattern` | `NoFloatPattern m` | `∀ q ∈ m.pats, ∀ a b, q ≠ .lit (.float a b)` |
| 6 | `res:core-let-recursion` | `LetRecursion m` | `∀ ds ∈ m.lets, ∀ i < ds.length, Graph.Plus ds.length (letRefersOcc ds) i i → ∃ x a q qs e, ds[i] = .fn x a (q :: qs) e`, where `letRefersOcc ds i j := (ds[j].bound).any (fun x => occursDef x ds[i])` ("a variable that the second binds occurs in the first") |
| 7 | `res:modules-ports` | `PortsInPortModule m` | `(∃ x t, .port x t ∈ m.decls) ↔ m.header.isPort` |
| 8 | `res:modules-import-alias` | `ImportAlias m` | `∀ i ∈ m.imports, ∀ a, i.alias = some a → '.' ∉ a.toList` |
| 9 | `res:modules-basics-qualifier` | `BasicsQualifier m` | `∀ i ∈ m.imports, i.alias = some "Basics" → i.mod = "Basics"` |
| 10 | `res:modules-no-operator-exposing` | `NoOperatorExposing m` | `∀ is, m.header.exposing = .items is → ∀ o, .op o ∉ is` |
| 11 | `res:modules-header-exposing` | `HeaderExposing m` | for `m.header.exposing = .items is`: `.var x ∈ is → x ∈ vals m ++ ports m`; `.ty c ∈ is → c ∈ customs m ++ aliases m`; `.tyAll c ∈ is → c ∈ customs m` |
| 12 | `res:modules-exposing-distinct` | `ExposingDistinct m` | the identifiers of the header's items are `Nodup` (`ty c` and `tyAll c` both have identifier `c`) |
| 13 | `res:modules-no-top-pattern` | `NoTopPattern m` | `∀ q e, .value (.pat q e) ∉ m.decls` |
| 14 | `res:modules-values-distinct` | `ValuesDistinct m` | `(vals m ++ ports m).Nodup` |
| 15 | `res:modules-types-distinct` | `TypesDistinct m` | `(customs m ++ aliases m).Nodup` |
| 16 | `res:modules-constructors-distinct` | `ConstructorsDistinct m` | `(ctors m ++ recAliases m).Nodup` |
| 17 | `res:modules-no-shadowing` | `TopNoShadowing m` | every variable bound within an expression of `m` (a lambda or function parameter, a variable of a pattern, a variable defined in a `let`) is not in `vals m ++ ports m` |
| 18 | `res:modules-tyvarseq-distinct` | `TyVarSeqDistinct m` | `∀ c ps, (.custom c ps _ ∈ m.decls ∨ .alias c ps _ ∈ m.decls) → ps.Nodup` |
| 19 | `res:modules-custom-type-tyvars` | `CustomTypeTyVars m` | for every `.custom c ps ctors`, every type variable (extension variables included) of every argument type is in `ps` |
| 20 | `res:modules-alias-tyvars` | `AliasTyVars m` | for every `.alias c ps t`, `∀ a, a ∈ ps ↔ a ∈ STy.tyvars t` |
| 21 | `res:modules-alias-not-recursive` | `AliasNotRecursive m` | `∀ i, ¬ Graph.Plus n (aliasRefers m) i i`, where alias `i` refers to alias `j` if `j`'s type constructor occurs, unqualified, in `i`'s body |
| 22 | `res:modules-value-recursion` | `ValueRecursion m` | `∀ i, ¬ Graph.Plus n (direct m) i i` over the value declarations, where `direct m i j` holds if declaration `i` is `.fn x _ [] e` (no parameters: with parameters every occurrence is delayed) and `occursDirect (the variable of j) e` |
| 23 | `res:modules-program` | `ModulesProgram p` | the port names of all modules are `Nodup` and none is in `managersPlat`; no module identifier is in `basisModuleIds`; `main` does not occur free in the expression of the main module's declaration of `main` |
| 24 | `res:program-modules-distinct` | `ModulesDistinct p` | `(p.modules.map (·.header.name)).Nodup ∧ ∀ m ∈ p.modules, m.header.name ∉ basisModuleIds` |
| 25 | `res:program-import-order` | `ImportOrder p` | `∀ i < p.modules.length, ∀ imp ∈ allImports p.modules[i], imp.mod ∈ basisModuleIds ∨ ∃ j < i, p.modules[j].header.name = imp.mod` |
| 26 | `res:program-modules-reachable` | `ModulesReachable p` | every module but the last is reachable from the last by the relation "imports" |
| 27 | `res:program-main` | `ProgramMain p` | the main module has exactly one top-level value declaration binding `main`, of the form `.fn "main" ann ps e`, and `occursFree "main" e = false` (see "Issues with the plan", item 4, for `ps`) |

### 5.3 The nine restrictions trusted to the parser

Not stated in Lean (plan, "Out of scope"): `res:core-escape-unicode`,
`res:core-identifier-characters`, `res:core-constant-separated`, `res:core-adjacent-items`,
`res:core-layout-rule`, `res:core-operator-chain`, `res:core-field-selection`,
`res:core-annotation-placement` (elm-syntax attaches each signature to its definition, so a tree
cannot even express a violation), `res:modules-header` (a text without a header has no tree).
Every Part II theorem carries `[parse]` for them.

## Translator changes

### New module `definition/tools/src/Translate/Source.elm`

```elm
module Translate.Source exposing (Problem, program)

type alias Problem = { reason : String, at : String }

{-| The Lean text of a program's source syntax: the test module and its helper modules (as
step 7 finds them), or why it cannot be written. -}
program : { project : String, name : String, defName : String }
    -> List { path : String, source : String, file : Elm.Syntax.File.File }
    -> Result Problem String
```

It maps the elm-syntax tree directly (no `Convert`, no inference, no specialisation), so it
runs for compile-error tests too:

- `Integer`/`Hex` expressions and `IntPattern`/`HexPattern`: the integer is read from the source
  text at the node's range (`Translate.Literal.textAt`, `decimalOfHex`), never from elm-syntax's
  `Int` (a JavaScript double, inexact beyond 2^53). `Floatable`/`FloatPattern`: mantissa and
  exponent from the text (`Translate.Literal`'s float reading). `CharLiteral`, `Literal`: decoded
  by elm-syntax; a lone surrogate (U+D800 to U+DFFF), which Lean's `Char` cannot hold, refuses the
  program with reason `source:surrogate`.
- `IfBlock c t f` with `f` itself an `IfBlock` (not parenthesised) extends the chain `arms`.
- `Negation e` is `neg`; a negative literal is a negation (as today).
- `OperatorApplication o _ l r` is `binop o`; `PrefixOperator o` is `opVal o`.
- `RecordAccess e l` is `access`, `RecordAccessFunction l` is `accessor` (without the dot).
- `LetFunction` with a signature is `SDef.fn x (some ty) ps e`; `LetDestructuring p e` is
  `SDef.pat`. Top-level `FunctionDeclaration` likewise; `Destructuring` is `.value (.pat p e)`;
  `CustomTypeDeclaration`, `AliasDeclaration`, `PortDeclaration` map to `custom`, `alias`, `port`.
- Module headers: `NormalModule` (isPort false), `PortModule` (true); `EffectModule` refuses with
  `source:effect-module`. `InfixDeclaration` refuses with `source:infix-declaration`;
  `GLSLExpression` with `source:glsl`; a negative integer pattern (outside the book's grammar,
  whose constants are unsigned) with `source:negative-pattern`; a tuple of 0, 1 or more than 3
  components, in an expression, pattern or type, with `source:tuple-arity`.
- Modules are written in the order of a topological sort of their imports (ties by name), the
  test module last; the Lean term is wrapped in `Src.canonOrder`, which recomputes that order, so
  that the theorem about the set (`SynOKSet`) and the one about the sequence agree.

The output uses the short constructors of `Src/Notation.lean`, for size:

```lean
/-- tests/elm/src/HelloTest.elm -/
def s_elm_HelloTest : Src.SProgram := Src.canonOrder <| Src.prog "elm" "HelloTest" [
  Src.mdl (Src.hdr false "HelloTest" (.items [.var "main"]))
    [Src.imp "Html" none (some (.items [.var "text"]))]
    [Src.val "main" none [] (Src.app (Src.v "text") [Src.str "Hello"])] ]
```

### Output files and the manifest

- `StandardElmMech/Generated/Src<Project><nn>.lean`, at most 40 programs each, in project then
  name order, for every `elm-spec` test whose program parses and is written (compile-error tests
  included); `Generated/SrcAll.lean` imports them and defines
  `srcShards : List (String × List (String × Src.SProgram))` (test name, program).
- `StandardElmMech/Generated/SynAll.lean`: `import StandardElmMech.Generated.SrcAll`,
  `import StandardElmMech.Src.SynCommand`, then one line `#syn_theorems srcShards`. The command
  evaluates `decSynOK` and each `decR` for every program with the interpreter, and adds the
  theorems of "Per test" above, `syn_` or `nosyn_` according to the result; the kernel checks
  each. One file, so one process pays the 1.6 GB of `import Lean`; if it exceeds the 6.5 GB budget
  or 10 minutes, it is split by project (`SynElm.lean`, `SynElmCore.lean`).
- The manifest entry of every test gains an object `src`:
  `{"status": "written", "shard": "SrcElm03", "def": "s_elm_HelloTest", "modules": [{"path": ..., "sha256": ...}]}`
  or `{"status": "refused", "reason": "parse" | "source:surrogate" | "source:effect-module" |
  "source:infix-declaration" | "source:glsl" | "source:negative-pattern" | "source:tuple-arity",
  "at": "<path>:<row>:<col>"}`. The existing `status` (Part I's path) is unchanged.
- `lake exe syn-report` (new executable, root `SynReport.lean`) writes
  `definition/mechanisation/syntactic-report.json`: for every written test, `{"project", "name",
  "synOK": true|false, "breaks": ["res:..."]}`, for the site and for acceptance.

### Unit tests (`definition/tools/tests/SourceTest.elm`)

1. `0x10` and `16` give `SLit.int 16`; `9007199254740993` is written exactly.
2. `'\u{0041}'` gives `SLit.char 'A'`; a lone surrogate refuses with `source:surrogate`.
3. `if a then b else if c then d else e` is one `ifte` with two arms; with parentheses around the
   inner `if`, two nested `ifte`.
4. `a + b * c` is `binop "+" a (binop "*" b c)` (elm-syntax's grouping); `a && b` is `binop "&&"`.
5. `f : Int -> Int` followed by `f x = x` gives `SDef.fn "f" (some ...) [var "x"] ...`.
6. `{ r | x = 1 }` gives `update "r" [("x", ...)]`; `.x` gives `accessor "x"`.
7. A port module with one port gives `isPort := true` and `STopDec.port`.
8. A test with a helper writes the helper first.
9. `(a, b, c, d)` in a type refuses with `source:tuple-arity` (if elm-syntax parses it).
10. A `Destructuring` at top level is written as `.value (.pat ...)`.

## Tests gained

- **Refusals, 31**: the tests step 7 classes `syntactic` (listed by name in
  [step 7](step-07-classify.md), section 2.5), each with `nosyn_elm_<Test> : ¬ Src.SynOKSet ...`
  and one `nosyn_elm_<Test>_<slug>` for the restriction it is classed under (and any other it
  breaks).
- **Compile-success**: `syn_<project>_<Test> : Src.SynOK ...` for every compile-success test whose
  source is written: 625 expected (628 less the three `Container*` tests elm-syntax cannot parse).
- **Compile-error tests refused later**: `syn_...` for each written compile-error test that breaks
  no AST-decidable restriction (the static and further classes, refused by steps 9 and 11);
  expected 260 = 311 − 18 (parse-fail) − 2 (`source:surrogate`: CharLiteralSurrogateEscapeTest,
  StandardA8SurrogateEscapeTest) − 31.

So `SynAll.lean` holds 916 per-test theorems: 885 `syn_` and 31 `nosyn_` (plus the
per-restriction `nosyn_..._<slug>`).

## Acceptance

```
site/node_modules/.bin/elm-pages run definition/tools/src/GenerateDerivedForms.elm
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check
(cd definition/tools && ../../site/node_modules/.bin/elm-test --compiler ../../site/node_modules/.bin/elm)
export PATH=$HOME/.elan/bin:$PATH
(cd definition/mechanisation/standard-elm-mech && lake build && lake exe run-examples)
(cd definition/mechanisation/standard-elm-mech && lake exe dump-phrases > /tmp/after.txt)   # compare with the output before the step
(cd definition/mechanisation/standard-elm-mech && lake exe compare-derived)
(cd definition/mechanisation/standard-elm-mech && lake exe syn-report)
(cd definition/mechanisation/standard-elm-mech && lake env lean scripts/check-axioms.lean)
```

(`/tmp/after.txt` stands for a file in the implementer's scratch directory.) Expected:

1. `GenerateDerivedForms.elm` reports `Derived.lean: unchanged`, the appendix unchanged, and
   `Src/DerivedRows.lean: written` the first time, `unchanged` after.
2. The translator's summary: `elm-spec tests: 939, translated: 491` and the refusal counts as
   before (Part I's path is unchanged), plus a line `source syntax: 916 written, 23 refused
   (parse 21, source:surrogate 2)`. Any other refusal is listed and explained in the report.
   `--check`: up to date.
3. elm-test: the previous tests and the 10 of `SourceTest.elm` pass.
4. `lake build` with no `sorry` and no new warning; `run-examples` prints the same totals as
   before (`Total: 1487 checks, 1487 agree, 0 diverge (0 known); 1162 theorems by decide +kernel.`
   at the time of writing, or the numbers of the latest step); `dump-phrases` output identical to
   the output before the step (the grouping moved, not changed).
5. `compare-derived`: `491 programs, N checks compared, 0 differ.`, N the `run-examples` total.
6. `syn-report`: `916 programs: 885 meet the AST-decidable restrictions, 31 do not.` The 31 are
   exactly step 7's `syntactic` set; each breaks (at least) its classed restriction. A
   compile-success test that does not meet them, or a test outside the set that does not, is a
   finding: about the book, elm-syntax, or the classification, and is recorded before the step
   is accepted.
7. `check-axioms`: the new theorems use only `propext`, `Classical.choice`, `Quot.sound` (and the
   native axioms for those listed as `native_decide`).
8. Memory budget of [conventions.md](conventions.md) on a clean build; `SynAll.lean`'s peak
   recorded in the report.
9. Reports and site as the conventions say; `runner/mechanisation-data.js` links each
   `res:` restriction page to its Lean `Prop` and decider (pattern `Src\.[A-Z][A-Za-z]+`).

## Risks and fallbacks

- **Nested inductives and the kernel.** Lean 4.35 supports nested inductives through `List` and
  `Prod`, structural recursion on them, and their reduction in the kernel; the first commit of the
  step is a 20-line smoke test (`decide +kernel` on a structurally recursive function over a
  nested `SExp` value). If it fails, the source and bare types are rewritten as explicit mutual
  families (`SExpList`, `SFieldList`, ...), as `Syntax.lean` does with `Option` chains; nothing
  else in the specification changes.
- **`deriving DecidableEq` on nested types** may not be available; no theorem needs it (the
  deciders compare strings and numbers), and `compare-derived` uses a `BEq` written by hand.
- **The `#syn_theorems` command** needs the interpreter to run `decSynOK` at elaboration time; if
  that is slow, the command evaluates only `decSynOK` and the per-restriction theorems are
  written only for the 31.
- **Large programs.** The five `construct:large-program` tests are written; their `Nodup` checks
  are quadratic in the number of fields. If the kernel exceeds the budget, they use
  `native_decide` and are listed.
- **A compile-success test that breaks a restriction** would be a real finding; the step stops
  until it is classified (book, elm-syntax or Elm).

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **Count.** The plan's gain "the ~37 syntactic refusals" is 31 measured (step 7, Issues 1).
   Followed: 31.
2. **Independence of the grouping (B4).** The plan says step 8 "states the independence as a lemma
   for elaboration and evaluation"; neither relation exists in step 8. This specification states
   in step 8 the book's relational form (`DerivesTo`, `ValidNumbering`) and proves the canonical
   choice valid; the independence statements are made in step 9 (elaboration) and step 10
   (evaluation). Theorems hold for the canonical choice meanwhile, as the plan says.
3. **Binding sites (book).** `syntax-core.tex` lists "the pattern of a destructuring binding" as a
   binding site whose scope is the definitions of its `let` and its body, and also "the
   definitions of one let, taken together", binding the same variables, with the same scope. Read
   literally each lies in the scope of the other and every destructuring `let` breaks
   `res:core-no-shadowing`. This specification reads the destructuring pattern as part of the
   `let`'s site (the only reading under which Elm's programs are legal). The book should drop
   the separate entry or say that a site is not in its own scope. (Ambiguity log.)
4. **`res:program-main` and parameters (book).** The restriction says the declaration "has the
   form `main [: ty] = exp`". Read on the source, `main a b = a` breaks it, but the book's comment
   on `r:p-stat-main-view` ("a main with parameters does not elaborate") and the test
   BadMainTypeFunctionMainTest (tagged `p-stat-main-program`) treat such a `main` as legal
   syntax refused by the static rule. This specification follows the comment: `ProgramMain`
   allows parameters, and the refusal is step 9's. Likewise `res:modules-no-top-pattern` ("a
   binding other than one of the form `var [: ty] = exp`") is read as "no destructuring binding",
   since top-level function definitions are derived forms of that form. (Ambiguity log.)
5. **Rule `r:sm-topdec-seq` on type declarations** is a step 9 matter, recorded there (its
   Issues, item 1), because the bare syntax of this step has to choose a representation for it:
   `BTopDec.types` is one node, and step 9 gives it both rules.

## Progress

**2026-11-11: in progress.**

Done:
- `Src/Syntax.lean`, `Src/Notation.lean` (with `canonOrder`, Kahn's order by imports, ties by
  name, the main module last), `Src/Bare.lean`, `Src/DerivedRows.lean` (generated: the region is
  `ToLean.bareDefinitions`, the bodies of `Derived.lean` over the bare types; `Derived.lean` and the
  appendix unchanged), `Src/Graph.lean` (`Plus`, `Reach`, `plusB`, `reachB`, `plusB_iff`,
  `reachB_iff`: the set of targets grows until it no longer grows, and a set of `range n` that
  grows n times is all of it), `Src/Grouping.lean` (`components`, moved from `Derived.lean`
  unchanged in its result: `dump-phrases` is byte-identical before and after; `ValidNumbering`),
  `Src/Derive.lean` (the derived forms, source to bare, total), `Src/Traverse.lean`,
  `Src/Restrictions.lean` (the 27 restrictions, each a `Prop` stated as the book states it and
  decidable by instances the kernel reduces, so `decR` is `decide` and `decR_iff` is
  `decide_eq_true_iff`; `ModuleOK`, `ProgramOK`, `SynOK`, `ModulesSynOK`), `Src/SynCommand.lean`
  (`#syn_theorems`).
- Translator: `Translate/Source.elm`; `Generated/Src<Project><nn>.lean`, `SrcAll.lean`,
  `SynAll.lean`; manifest object `src`; `source syntax: 916 written, 23 refused (parse 21,
  source:surrogate 2)`, as specified. 136 unit tests (`SourceTest.elm` among them: elm-syntax 7.3.9
  does not parse a tuple type of four nor a top-level destructuring, so those two tests check that
  they are never written).
- `SynAll.lean`: `916 programs: 882 meet the AST-decidable restrictions, 34 do not` (2 min 11 s);
  `lake exe syn-report` writes `syntactic-report.json`. The 34 are the 31 `syntactic` tests and the
  three compile-success tests whose programs import a module outside Dom ME0 (Dict, Bitwise,
  Bytes.Encode, Bytes.Decode), which break `res:program-import-order` as the book states it: their
  modules lie outside the definition (step 7 classes them `outside`).
- `lake exe compare-derived`: `579 programs, 589 modules compared, 0 differ.` (module form; long
  identifiers compared without their qualifiers, since the translator resolves an exposed name to
  its qualified form, which is elaboration, not a derived form).
- run-examples unchanged; 4,106 theorems, 0 axiom problems.

Findings:
- 197 of the written programs are modules without `main` (188 compile-error tests and others): a
  test of a module's error, not a program. `res:program-main` refuses every such text as a program
  whatever its intended error; their theorems are stated with `ModulesSynOK` (every restriction
  but `res:program-main`), and steps 9 to 11 state theirs for the module.
- BadMainRecursiveMainTest and BadMainRecursiveUnannotatedMainTest meet `res:program-main` as the
  book states it (`main` reaches itself only through `f`; it does not occur free in its own
  expression): reclassified `static-deterministic` (`main`).
- QualifiedTypeNotExposedTest also breaks `res:modules-value-recursion` (`foo = foo`), and
  StandardA84DuplicatePortNameTest is decided by `res:modules-program`: both reclassified
  `syntactic`. The counts of step 7 are unchanged (31 and 28).
- The five tests of a compiler's limits (`construct:large-program`) are proved by `native_decide`
  (`synNative`): the kernel overflowed its recursion depth on them.

**2026-11-12: done.**

- `Src/GroupingProof.lean`: `components_valid : ValidNumbering n r (components n r)`, for every
  graph. The classes are the equivalence classes of mutual reachability (computed once through
  `reachTable`), covering `range n` without overlap; among the classes not yet placed one is
  always ready, since a node whose count of reachable unplaced nodes is least lies in a ready class.
- `Src/AliasOrderProof.lean`: `aliasOrder_valid`, under the hypotheses that the alias names are
  distinct and no alias mentions itself through others, by the same counting argument.
- `Src/DerivesTo.lean`: `DerivesE` (one constructor per production; the `let` case with any valid
  numbering), `DerivesTo` for modules (any valid numbering of the ports and definitions, any valid
  order of the aliases), `deriveExp_derives` (unconditional) and `derive_derivesTo` (under
  `ModuleOK`, which supplies `res:modules-types-distinct` and `res:modules-alias-not-recursive`).
  `deriveTopDecs` is now `assemble` applied to the canonical choices; `compare-derived` unchanged.
- `Src/SynSet.lean`: `SynOKSet`, `ModulesSynOKSet`, `synOKSet_of_synOK`, and the refusals of every
  order of a program's modules (`notSynOKSet_of_setFails`: a module restriction,
  res:modules-program's ports and names, an import of no module; `notSynOKSet_of_twoCycle`: two
  modules importing each other). Every one of the 34 refusals is stated for the set of modules;
  none is stated only for the canonical sequence. The per-test theorems are `syn_... : SynOKSet`
  and `nosyn_... : ¬ SynOKSet` (or the `Modules` forms).
- Memory: one file of theorems for all 916 programs peaked at 6.46 GB, so they are split into
  `Syn01.lean` to `Syn06.lean` (four source shards each, 2.6 to 3.1 GB each); the clean build's
  largest process is 3.1 GB and all together 9.5 GB, in 1 min 44 s.
- The site's restriction pages show their Lean `Prop` and the programs that break them
  (`mechanisation/restrictions.json`); link audit 0 problems.
- 4,215 theorems, 0 axiom problems; run-examples unchanged; 136 unit tests.

Differences from this specification:
- `synOKSet_iff` (the general equivalence with the canonical order, through the correctness of
  Kahn's algorithm) is not proved; the theorems the tests need are proved instead: a sequence that
  meets the restrictions is a witness of the set, and each refusal is proved for every order by the
  lemmas above.
- The restrictions are decided by `decide` on instances (each `decR_iff` is
  `decide_eq_true_iff`); no hand-written deciders.
