# Step 3: module form, and every check as a log statement

Part of [the plan](../lean-full-definition.md) (decisions D2, D4, D9). Conventions:
[conventions.md](conventions.md). Size: large (most of it translator work that step 8 later
replaces). Needs: step 2. Status: done (2026-11-11; see Progress).

## Goal

Translate every test as the program it is, a sequence of modules in the reduced syntax of
Chapter 7, and state every check once, as a statement about the log of the book's evaluation of
the program (`r:p-dyn-module`, `r:p-dyn-main`) in the test basis `Btest`:

- the translator resolves a test's imports among `tests/<project>/src`, orders the modules, and
  writes each in reduced syntax; it types several modules at once (qualified type names, imported
  schemes, `Html.text` from the harness, ports and their payload types) and specialises numbers
  across modules (an exposing item stands for its copies);
- the Lean side gains `ModProgram`, the grouping of a module's declarations, the statements
  `ViewChecks` and `NoMeaning`, and a generator command for the per-program theorems;
- every existing check migrates once from the let form to a log statement (D9); the two strict
  tests become theorems that the program has no meaning (D1), their logs reported by
  `run-examples` only;
- 42 tests are gained: user modules, record alias constructors, two views, the port views, group E
  and the two regular-expression checks.

Acceptance is mechanical: every `(program, label)` value of `example-run.json` is unchanged except
those of the two strict tests.

## Prerequisites

- Step 2 done: Chapter 7 and `r:p-dyn-*` in Lean with `evProgram`, its soundness, completeness and
  `noMeaning_of_stuck`; `ME0` with the empty-interface modules `Array`, `Bytes`, `Json.*`,
  `VirtualDom`; `Btest`; `PTy`.
- Step 1's `LogCheck`, `Expect`, `Shape`, `Expect.parse`, `Rx`, deciders and their soundness.
- The book: `dynamic-modules.tex`, lines 38 to 89 (reduced syntax: ports as `(out, τ)` or `(in, τ)`,
  record aliases as label lists in the order written, an exposing item standing for its copies,
  `import M` read as `import M as M`, the default imports first); `appendix-derived-forms.tex`,
  Section `sec:appendix-derived-forms-modules` (lines 331 to 415, the order of a module's
  declarations); `programs.tex`, Section `sec:programs-syntax` (lines 50 to 89: a program is its
  main module and every module it imports, each after the modules it imports) and Section
  `sec:programs-evaluation` (lines 229 to 272); `static-modules.tex`, Section
  `sec:static-modules-ports` (lines 228 to 270, the port types); `dynamic-core.tex`, Section
  `sec:dynamic-core-numbers` (number specialisation, its copies and their names).
- The runner's CHECK semantics, `runner/directives.js` (`extractCheckPatterns`, `verifyPatterns`):
  a CHECK pattern is a substring of the whole output, `{{...}}` parts are regular expressions,
  CHECK-DAG is a CHECK, CHECK-NEXT and CHECK-SAME constrain lines.

## Lean definitions

New file `StandardElmMech/Mod/Program.lean` (namespace `StandardElm.Mod`), and changes to
`Theorems.lean`, `Main.lean`, `DumpPhrases.lean`.

### A module as the translator writes it

The translator writes a module's declarations as written (after number specialisation); a Lean
function applies the derived form of Appendix A (`sec:appendix-derived-forms-modules`), as
`letDefs` does for a `let`. Step 8 replaces this function by the derived form it proves.

```lean
/-- A port or a definition `var atpat1 ... atpatm = exp` of a module body (a module has no
    pattern bindings at the top level). -/
inductive TopItem where
  | defn (d : D.Def)                  -- only `.fn`; the translator refuses top-level patterns
  | port (x : Var) (d : Dir) (τ : PTy)

/-- The item as a definition for computing "refers to": a port binds its name and refers to
    nothing (its stand-in right-hand side is `()`), so it is alone in its component. -/
def TopItem.asDef : TopItem → D.Def
  | .defn d => d
  | .port x _ _ => .fn x [] (.atexp .unit)

/-- `topdec1 ; ... ; topdecn`, nested to the right; n ≥ 1. -/
def TopDec.seqOf : List TopDec → Option TopDec
  | [] => none
  | [t] => some t
  | t :: ts => (TopDec.seqOf ts).map (.seq t)

/-- Appendix A's row for modules: the custom types as one group (in the order given), then the
    aliases (in the order given, which the translator makes "after every alias it mentions"), then
    the ports and definitions in components ordered by "refers to" (`D.components`), a port alone,
    a group of definitions as one value declaration. -/
def Module.ofSource (h : Header) (written : List Import) (types : List (TyCon × List Con))
    (aliases : List TypBind) (items : List TopItem) : Option Module :=
  let typeDec : List TopDec := match types with
    | [] => []
    | (t, cs) :: rest => [.type (datBindOf ((t, cs) :: rest))]
  let aliasDecs := aliases.map TopDec.alias
  let ds := items.map TopItem.asDef
  let itemDecs := (D.components ds).map fun comp =>
    match comp with
    | [i] => match items[i]! with
      | .port x d τ => TopDec.port x d τ
      | .defn (.fn x ps e) => .val [(x, D.lams ps e)]
      | .defn (.pat _ _) => .val []                         -- not produced
    | is => .val (is.map fun i => match items[i]! with
      | .defn (.fn x ps e) => (x, D.lams ps e)
      | _ => ("", .atexp .unit))                             -- not produced
  (TopDec.seqOf (typeDec ++ aliasDecs ++ itemDecs)).map (.withDefaults h written)

def datBindOf : List (TyCon × List Con) → DatBind    -- t1 = c11 | ... and t2 = ... ; constructors non-empty
```

No theorem about the grouping is proved in this step. The grouping is part of the translator's
reduced syntax, which the trust model covers by `[elab]` until step 10, and step 8 replaces
`Module.ofSource` by the derived form of Appendix A proved in Lean (with the independence of the
choice of order, finding B4). Choice made because a proof here would be thrown away by step 8.
`Module` gets an `Inhabited` instance (a one-alias module) so that the generated `(...).get!` is
well-typed; the translator never writes a module for which `Module.ofSource` is `none`.

### Programs and checks

```lean
/-- The CHECK lines of a test, in the order written, with the shape of the logged value the
    translator inferred for the label (`Shape.any` when it found none or several). -/
inductive CheckLine where
  | check (text : String) (shape : Shape)    -- -- CHECK: and -- CHECK-DAG: (D9: DAG is CHECK)
  | next (text : String) (shape : Shape)     -- -- CHECK-NEXT:
  | same (text : String)                     -- -- CHECK-SAME:
  | not_ (text : String)                     -- -- CHECK-NOT: (here only with EXIT 1)
  deriving Repr

/-- A test program in module form. -/
structure ModProgram where
  name : String
  source : String := "tests/elm/src"
  native : Bool := false        -- uses a value only the C library computes (as Program.native)
  modules : List Module         -- program order, the main module last
  checks : List CheckLine
  meaning : Bool := true        -- false: the test expects the program to stop (EXIT 1)
```

### The statements (D9)

```lean
/-- A view program: some derivation of the book's evaluation of the program, in basis B, has a
    log that meets every check. -/
def ViewChecks (B : Basis) (p : List Module) (cs : List LogCheck) : Prop :=
  ∃ v l, EvalProgramL B p v l ∧ ∀ c ∈ cs, c.Holds l

/-- The program has no meaning (r:p-dyn-main's comment: a top-level value with no value). -/
def NoMeaning (B : Basis) (p : List Module) : Prop := ¬ ∃ v, EvalProgram B p v

def viewChecksB (o : Oracle) (B : Basis) (p : List Module) (cs : List LogCheck) : Bool :=
  match evProgram o fuelT B p 0 with
  | ⟨.value _, l, _⟩ => cs.all (·.check l)
  | _ => false

def stuckB (B : Basis) (p : List Module) : Bool :=
  match evProgram (.const false) fuelT B p 0 with
  | ⟨.stuck, _, 0⟩ => true
  | _ => false
```

`toLogChecks : List CheckLine → Except String (List LogCheck)` (a `partial def`, run only at
generation) turns lines into statements:

| Lines | Statement |
|-------|-----------|
| `check "label: value" s` (first `": "` splits, as `Directives.elm` does) | `.has (.entry label (Expect.parse s value))` |
| `check "text" _`, no `": "` | `.has (.label text)` |
| `check t _` followed by `next t1 s1`, ..., `next tk sk` | `.run [pat t, pat t1, ..., pat tk]` with `pat` as the two rows above |
| a line whose text contains `{{` | `.printed (Rx.parse (pattern as JavaScript reads it))` |
| `check t _` followed by `same u` | `.printed (lit t ++ [^\n]* ++ lit u)` |
| `not_ t` | no statement here (the program has no meaning; step 6 states CHECK-NOT) |

### The generator command

`Theorems.lean` gains, beside step 1's `#program_theorems` (which goes away with the let form at the
end of this step):

```lean
/-- `#mod_program_theorems shard` emits, for each `g : ModProgram` of the list `shard`:
    * if `g.meaning = false`:
        theorem t_<project>_<Name> : NoMeaning (Btest []) g.modules := noMeaning_sound (by decide +kernel)
    * otherwise, with cs := toLogChecks g.checks (shown literally in the statement):
        theorem t_<project>_<Name> : ViewChecks (Btest []) g.modules cs :=
          viewChecks_sound (o := ⟨oracle⟩) (by decide +kernel)
      by `native_decide` instead when `g.native`, when `budgetNative` names it, or when some
      statement is `.printed` (D9). -/
elab "#mod_program_theorems " ps:ident : command
```

The oracle: the command runs the compiled evaluator (`evalExpr`) with `Oracle.const false`, then
`Oracle.const true`; if neither meets every check, it reads the number `j` of choices the run made
and tries the `2^j` lists for `j ≤ 12`, writing the first that works as `Oracle.ofList [...]`; else
it fails with the program's name. (Today no check depends on the choice: no row of
`example-run.json` has two values.) The docstring of each theorem is the list of the program's
source files followed by its trust tags: `[parse] [elab] [harness] [params]`, and `[native]` when
proved by `native_decide`.

Example of the output for ImportExposingItemsTest:

```lean
/-- tests/elm/src/ImportExposingItemsTest.elm, tests/elm/src/ModuleExposingHelper.elm
    [parse] [elab] [harness] [params] -/
theorem t_elm_ImportExposingItemsTest :
    ViewChecks (Btest []) g_elm_ImportExposingItemsTest.modules
      [.has (.entry "double" (.int 42)), .has (.entry "open" (.list [.int 0, .int 7])),
       .has (.entry "point" (.int 3)), .has (.entry "closed" (.int 5)),
       .has (.entry "qualified" (.int 101))] :=
  viewChecks_sound (o := .const false) (by decide +kernel)
```

### run-examples and the phrases

`Main.lean` runs `evProgram` with both constant oracles for each `ModProgram`. Rows, one per CHECK
line as today:

| Field | Value |
|-------|-------|
| `label`, `expected` | the text before and after the first `": "` (for a label-only line, the text and `""`; for a regex line, the whole pattern and `""`) |
| `definition` | the distinct `showElm` values of the log entries with that label, oracle false first, then oracle true, in order of first appearance; `["(no meaning)"]` if the program has none |
| `status` | `agree` if `expected` is among them (label-only: the label occurs; regex: `Rx.search` on `renderLog`); for a program without meaning, `agree (partial log)` for a CHECK met by the partial log at `stuck`, and `agree (no meaning)` for a CHECK-NOT |
| `theorem` | `t_<project>_<Name>`; `null` with `skipped: "partial-log"` for the CHECK rows of a program without meaning |
| `proof` | `kernel` or `native` |

The summary line is step 1's. `DumpPhrases.lean` dumps each program's modules (`repr`), so that a
change to the derived forms can still be shown to change no phrase.

## Theorems

```lean
theorem viewChecks_sound {o B p cs} : viewChecksB o B p cs = true → ViewChecks B p cs
theorem noMeaning_sound {B p} : stuckB B p = true → NoMeaning B p
/-- When the evaluator reads no choice, the checks hold of every derivation's log, not only of
    some (from evProgram_unique_l): the existential of D9 is then also universal. -/
theorem viewChecks_every {o B p cs v l} (h : evProgram o fuelT B p 0 = ⟨.value v, l, 0⟩)
    (hc : cs.all (·.check l) = true) :
    ∀ v' l', EvalProgramL B p v' l' → ∀ c ∈ cs, c.Holds l'
```

Methods: `viewChecks_sound` from `evProgram_sound_l` and `LogCheck.check_sound`; `noMeaning_sound`
from `noMeaning_of_stuck`; `viewChecks_every` from `evProgram_unique_l`.

Generated: one theorem per program, `t_<project>_<Name>`, 540 in all (538 `ViewChecks`, 2
`NoMeaning`).

The strict tests (D1 and finding P1-10 of the third review):

```lean
/-- tests/elm/src/StandardLetStrictTest.elm [parse] [elab] [harness] [params] -/
theorem t_elm_StandardLetStrictTest : NoMeaning (Btest []) g_elm_StandardLetStrictTest.modules :=
  noMeaning_sound (by decide +kernel)
/-- tests/elm/src/StandardApplicationStrictTest.elm [parse] [elab] [harness] [params] -/
theorem t_elm_StandardApplicationStrictTest : NoMeaning (Btest []) g_elm_StandardApplicationStrictTest.modules :=
  noMeaning_sound (by decide +kernel)
```

Their `CHECK: before: ()` is reported by `run-examples` from the partial log (`before` is logged,
then `Debug.todo` is reached, in the logged rules' order) and is not a theorem: the book has no
derivation for the program to be about, and the partial log is one order of evaluation among
those the book leaves open (A57).

## Translator changes

The translator keeps its pipeline (directives, parse, convert, infer, specialise, print) and its
refusal ranks, but every stage works on a program of modules. Existing behaviour that does not
concern modules (literals, derived forms, number specialisation within a module) is unchanged.

### Resolving the modules (`Translate.elm`, new `Translate/Modules.elm`)

For a test `tests/<project>/src/<Name>.elm`:

1. Parse the test. For each written import `M` that is not a module of the basis
   (`basisModules` = `Basics`, `List`, `Maybe`, `Result`, `String`, `Char`, `Tuple`, `Debug`,
   `Platform`, `Platform.Cmd`, `Platform.Sub`, `Array`, `Bytes`, `Json.Encode`, `Json.Decode`,
   `VirtualDom`, `Html`), read `tests/<project>/src/<M with . as />.elm` (a `BackendTask`); if there
   is none, refuse `import:<M>` as today (library modules such as `Dict`, `Bitwise`, and effect
   modules such as `Task`, `Process`, keep their refusals: `import:*`, `effects`).
2. Recurse on the helper's imports. An import cycle is refused `import:cycle`.
3. Order: depth-first post-order from the test, following each module's imports in the order
   written, a module emitted after its imports and once; the test (the main module) last. This is
   a sequence meeting `res:program-import-order` (`programs.tex`, lines 70 to 72); every such
   sequence has the same meaning (the property at lines 286 to 296).

Helper files are tests' helpers (`-- HELPER:`), skipped as tests today; they are read only through
an importing test.

### The representation (`Translate/Ir.elm`)

```elm
type alias ModuleIr =
    { name : String                  -- the module identifier
    , path : String                  -- tests/elm/src/ModuleExposingHelper.elm
    , isPort : Bool
    , exposing : ExposingIr          -- All | Items (List ItemIr)
    , imports : List ImportIr        -- written imports only, in order
    , types : List TypeIr            -- custom types, source order: name, params, constructors with argument annotations
    , aliases : List AliasIr         -- name, params, annotation; recordLabels : Maybe (List String) (closed record, order written)
    , ports : List PortIr            -- name, binder, annotation; filled by Infer: direction, payload
    , decls : List Decl              -- definitions in source order, main included
    }

type ItemIr = IVar String | IOp String | IType String | IOpen String
type alias ImportIr = { modid : String, alias : Maybe String, exposing : Maybe ExposingIr }

type alias CheckLineIr = { kind : CheckKindIr, text : String }   -- Check | Dag | Next | Same | Not

type alias ProgramIr =
    { modules : List ModuleIr        -- program order, main last
    , checks : List CheckLineIr
    , meaning : Bool                 -- False when EXIT: 1 with CHECK-NOT lines
    }
```

`TestProgram` (the let form: `defs`, `locals`, `checks`) is retired. `Name` gains a variant for
values of user modules, which keeps the spelling written so that the Lean phrase resolves through
the module's imports as the book's rules do:

```elm
type Name
    = Local Int String                                  -- bound in this module (binder id, name)
    | Global String String                              -- a value of the basis (module, name); "" = unqualified
    | Foreign { binder : Int, qual : Maybe String, name : String }   -- a user module's value, as written
    | UserCon { qual : Maybe String, name : String }    -- a constructor of a user module, as written
```

Binder ids are unique across the program (one `St.next` threaded through all modules).

### Conversion (`Translate/Convert.elm`)

- Converts each module in program order. A module's import environment (`Imports`) maps
  qualifiers and unqualified names to basis modules or to the export tables of earlier user
  modules (`ExportTable = { values : Dict String Int, constructors : Dict String Int,
  types : Dict String TypeExport }`), built from each module's header after its conversion.
- No longer refused: `port module` and port declarations (converted to `PortIr`); imports of the
  basis modules of the table above; a `main` that is not `let ... in text "literal"` (Infer
  decides whether it is a view); record alias constructors.
- Still refused: top-level destructuring (`construct:top-level-pattern`, not in Elm 0.19.1
  anyway); infix declarations; effect values in expressions (`Platform.*`, `Cmd.*`, `Sub.*`,
  `Task.*`, `Process.*`: `effects`, until step 5); library values (`basis:*`); size.
- Checks are not extracted from `main`: `main` is translated whole. The CHECK lines come from the
  directives (all of them, in order). For each CHECK line with a label, the label must be the
  literal first argument of some `Debug.log` application in some module of the program (in any
  position, pipes included); otherwise `checks:unmatched:<label>` as today. This admits group E.

### Directives (`Translate/Directives.elm`)

`read` returns every CHECK-family line in order (`checkLines : List CheckLineIr`). Refusals that
remain: `compile-error`, `FLAGS`, `STDIN*`, `ENV`, `UNSETENV` (`effects`), `CHECK-LABEL`, an exit
status other than 0 or 1, a CHECK-NOT without `EXIT: 1` (`checks:check-not`, step 6). No longer
refusals: CHECK-DAG, CHECK-NEXT, CHECK-SAME, `{{regex}}`, unlabelled CHECK.

### Inference (`Translate/Infer.elm`, `Translate/Basis.elm`, `Translate/Types.elm`)

- Programs are inferred module by module in program order, with one substitution; each module's
  declarations by components as today. After a module, its exposed values' schemes are generalised
  and put in its export table.
- Type names of user modules are qualified: `TCon "ModuleExposingHelper.Open" []`. Builtin types
  keep their short names (`Int`, `Maybe`, ...). An annotation's type constructor resolves through
  the module's own types and aliases, then the imports' exposed types (a later import's type
  replaces an earlier one of the same name, as `sm-item-type` says: ImportTypeByNameLaterReplacesTest),
  then qualified references.
- New builtin types: `Cmd` (`Platform.Cmd.Cmd`, 1 parameter), `Sub` (`Platform.Sub.Sub`, 1),
  `Program` (`Platform.Program`, 3), `Node` (`VirtualDom.Node`, 1; `Html.Html` is its alias),
  `Value` (`Json.Encode.Value`; `Json.Decode.Value` is its alias), `Array` (1), `Bytes` (0).
- The harness (D2): `Basis.value "Html" "text" = Just (anyScheme 1 (fn [ string ] (TCon "Node" [ v 1 ])))`.
- Ports: from `port p : τ -> Cmd msg` the direction `out` and payload `τ`; from
  `port p : (τ -> msg) -> Sub msg` the direction `in` and payload `τ`; the port's scheme is its
  annotation's. The payload type is converted to `PTy` after alias expansion: `Int`, `Float`,
  `Bool`, `String`, `Bytes`, `()`, `Json.Encode.Value`, `List τ`, `Maybe τ`, `Array τ`, 2- and
  3-tuples, closed records (fields sorted by label). Anything else is refused
  `construct:port-type` (such a program does not elaborate, Figure `fig:static-modules-port`).
- `main`: its type after the Float default must be `Node τ` (a view); `Program _ _ _` is refused
  `effects:worker` (step 5); anything else `construct:main-type`.
- Record alias constructors: an alias of a closed record `P` with fields `l1 ... ln` in the order
  written gives the constructor scheme `τ1 -> ... -> τn -> P` (with the alias's parameters).
- Logged labels: `Inferred.logTypes : Dict String (List Type)`, for each literal label the
  instance at which each `Debug.log "<label>"` occurrence is used (its type variable `a`).

### Specialisation (`Translate/Specialise.elm`)

- One program-wide pass over the modules in order, so a use in module B of A's `f` at `Int`
  requests A's copy `f$Int`, which is placed in A's declarations right after `f` (names as today:
  `name$Int`, one `$`-word per `number` variable).
- Exposing items stand for copies (`dynamic-modules.tex`, lines 74 to 79): in A's header, an item
  `f` becomes `f`, `f$Int`, ... for every copy of `f` made; in an importer's exposing list, an item
  `f` naming A's `f` becomes the same list. `(..)` is unchanged.
- A `Foreign` occurrence is renamed to its copy as a `Local` one is; its qualifier, if any, is kept.
- The program is `native` if any module uses a value of `nativeValues` (as today), now including
  `logBase`, `fromPolar`, `toPolar` (step 2).

### Printing (`Translate/ToLean.elm`) and the data written

Each test becomes one `def` of type `ModProgram` in its shard. Example (abridged):

```lean
/-- tests/elm/src/ImportExposingItemsTest.elm, tests/elm/src/ModuleExposingHelper.elm -/
def g_elm_ImportExposingItemsTest : ModProgram := {
  name := "ImportExposingItemsTest", source := "tests/elm/src",
  modules := [
    (Module.ofSource
      ⟨false, "ModuleExposingHelper", .items [.tycon "Closed", .opened "Open", .tycon "Point",
        .tycon "Shape", .var "double", .var "exposedCount", .var "makeClosed", .var "makeShape",
        .var "unwrapClosed", .var "unwrapShape"]⟩
      []
      [("Closed", [⟨"Closed", 1⟩]), ("Open", [⟨"One", 0⟩, ⟨"Two", 1⟩]), ("Shape", [⟨"Shape", 1⟩])]
      [⟨"Point", some ["x", "y"]⟩]
      [.defn (.fn "hidden" [] (i 100)),
       .defn (.fn "double" [pv "n"] (bin "*" (i 2) (v "n"))),
       ...]).get!,
    (Module.ofSource
      ⟨false, "ImportExposingItemsTest", .items [.var "main"]⟩
      [⟨"Html", "Html", none⟩,
       ⟨"ModuleExposingHelper", "ModuleExposingHelper",
         some (.items [.tycon "Closed", .opened "Open", .tycon "Point", .var "double"])⟩]
      [] []
      [.defn (.fn "openValue" [pv "o"] (caseOf (v "o") [...])),
       ...,
       .defn (.fn "main" [] (letDefs [.pat pw (debugLog "double" (ap (v "double") [i 21])), ...]
                                     (ap (qv "Html" "text") [str "done"])))]).get! ],
  checks := [.check "double: 42" .int, .check "open: [0,7]" (.list .int), .check "point: 3" .int,
             .check "closed: 5" .int, .check "qualified: 101" .int] }
```

`ToLean` prints: headers and exposing lists (`.var`, `.op`, `.tycon`, `.opened`); written imports
(`import M` as `⟨"M", "M", ...⟩`, `import M as Q` as `⟨"M", "Q", ...⟩`); custom types with each
constructor's name and arity; aliases with labels for closed records; items in source order; a
port as `.port "p" .out τ` with `τ` printed as a `PTy` term (`.tuple3 .int .string .bool`); shapes
from `Inferred.logTypes` (`Int` is `.int`, `List Int` is `.list .int`, a user custom type `T`
`.custom [(con, [shapes])]` to depth 3, `.any` beyond and for a label used at several types). A
module whose `Module.ofSource` would be `none` (no declaration) is refused
`construct:empty-module`; the `.get!` is then never reached.

Shard files import `StandardElmMech.Mod.Program` and define `shard_<S> : List ModProgram`;
`Checks<S>.lean` contains `#mod_program_theorems shard_<S>`; `All.lean` and
`AllPrograms.lean` hold `List ModProgram`.

### The manifest

Each entry gains `sources`, a list of `{ path, sha256 }`, one per module of the program in program
order (the test last); `sha256` stays the test file's hash, for compatibility. A refused test lists
the modules read before the refusal. `runner/mechanisation-data.js` marks a translation out of date
when any entry of `sources` differs from its file (today it compares the test file only).

### Translator tests (`definition/tools/tests/TranslateTest.elm`)

New group "modules":

- "a helper module is read from the project's src folder and comes before the test"
- "modules are ordered after the modules they import (post-order, imports in written order)"
- "an import cycle is refused (import:cycle)"
- "an import of Dict stays refused (import:Dict)"
- "two helpers' types of one name are distinct types (qualified type names)"
- "a later import's type replaces an earlier one's (ImportTypeByNameLaterReplacesTest)"
- "an exposing item of a declaration copied at Int stands for the copy"
- "an importer's exposing item stands for the exporter's copies"
- "a record alias constructor takes its fields in the order written"
- "an outgoing port of Bool has direction out and payload .bool"
- "an incoming port of a 3-tuple has direction in and payload .tuple3"
- "a port of a function type is refused (construct:port-type)"
- "main of type Html msg is a view; main of type Program is refused (effects:worker)"
- "Html.text has the harness's scheme"
- "a check whose label no Debug.log writes is refused (checks:unmatched)"
- "a check logged inside a function is accepted"
- "CHECK-DAG is read as CHECK; CHECK-NEXT follows its CHECK"
- "a regular-expression check is carried as printed"
- "an unlabelled CHECK is kept as a label check"
- "EXIT 1 with CHECK-NOT gives a program expected to have no meaning"
- "the manifest lists every module of the program with its hash"
- "the shape of a check is the logged value's inferred type"

Existing tests that assert refusals this step lifts ("a CHECK-NEXT", "an unlabelled CHECK line", "a
regular expression in a CHECK line", "a record alias used as a constructor", "a main that is not a
let", "a check logged by a pipe", "a flag directive" stays) are updated to assert the new
behaviour.

## Migration of the existing checks (once)

Every one of the 498 programs of step 2 is rewritten in module form, and its checks become log
statements; the let form (`Program`, `Check`, `LetChecks`, `#program_theorems`, `E0with`) is retired
from the generated files (the hand-stated ruling theorems of `Theorems.lean` keep using `E0`). In
module form all of a program's top-level values are evaluated once, before `main`, whether used or
not (`r:p-dyn-module`'s comment); in the let form each check re-evaluated the definitions it was
wrapped in. Nothing in the rules should change a value: the definitions are grouped by the same
`components` in both forms, and every top-level value was already evaluated in the let form (the
`let` around each check is strict, `r:d-atexp-let`). A changed value is a finding about the let
encoding or the module rules, to be explained before acceptance.

The comparison is a script, `runner/compare-example-run.js OLD NEW`: for every row of the old run,
the new run has a row with the same `program` and `label`, the same `expected`, a status beginning
with `agree`, and the same `definition` list. It prints the rows that differ and exits 1 unless
every difference is in the allowed list:

| Program | Label | Old | New |
|---------|-------|-----|-----|
| StandardLetStrictTest | `before` | `()`, kernel theorem (step 1) | `()` from the partial log, no theorem |
| StandardLetStrictTest | `let strict` | `(no value)`, `.noValue` theorem | `(no meaning)`, covered by `NoMeaning` |
| StandardApplicationStrictTest | `before` | `()`, kernel theorem | `()` from the partial log, no theorem |
| StandardApplicationStrictTest | `app strict` | `(no value)`, `.noValue` theorem | `(no meaning)`, covered by `NoMeaning` |

A label that the module form logs more than once (an inner `Debug.log` with the same label as the
check's) gives a longer `definition` list; any such row is listed in the step's report with the
reason, and the expected value must still be in the list.

## Tests gained

42 tests, 84 checks:

- User modules (group G), 9: CompilerIssue2119MutualRecursionUnannotatedTest,
  CompilerIssue2207MutualRecursionSecondFunctionTest, CovForeignTypesTest,
  EntryMainOfRootModuleTest (its helper's `main` logs `which: "helper"` too; the check
  `which: "root"` is met by the root's entry), ImportClosedTypeOpenItemTest, ImportExposingAllTest,
  ImportExposingItemsTest, ImportTypeByNameLaterReplacesTest, StandardA82MainInImportedModuleTest.
- Record alias constructors, 5: RecordRowsTest, TypeAliasCtorTest, WideRecordDecoder26Test,
  WideRecordDecoder30Test, WideRecordDecoder70Test.
- Views whose `main` is not `text "literal"`, 2: HelloTest, CharCasePredicateTest.
- Port modules whose `main` is a view, 15: CovPortIncomingArrayTest, CovPortIncomingJSONValueTest,
  CovPortIncomingTripleTest, CovPortIncomingUnitTest, CovPortOutgoingJSONValueTest,
  CovPortOutgoingUnitTest, PortEncodingDecodeFloatTest, PortEncodingDecodeListIntTest,
  PortEncodingDecodeMaybeIntTest, PortEncodingDecodeTuple2Test, PortEncodingEncodeBoolTest,
  PortEncodingEncodeFloatTest, PortEncodingEncodeMaybeRecordTest, PortEncodingEncodeTuple2Test,
  PortEncodingPortWithArrayTest.
- Log checks (group E), 9: CovEtaDebugLogTest, DebugLogLambdaBoundaryTest,
  DebugLogRecordTupleFieldTest, DebugNumberAtFloatTest, LetValueBindingTest,
  PureMutualRecursiveValueTest and PureRecursiveValueThunkTest (both through the thunk translation
  of `r:dm-topdec-val`), StandardA56PrefixAndOrTest, StringEscapesTest (its `CHECK: newline` and
  `CHECK: tab` are label checks).
- Regular-expression checks, by `native_decide` (D9), 2: CoreIssue1150CharToCodeLoneSurrogateTest
  (`{{code: -?[0-9]+(\n|$)}}`), CoreIssue960PowNegativeExponentIntTest (`{{pow: 0(\n|$)}}`).

## Acceptance

The commands of [conventions.md](conventions.md), then
`node runner/compare-example-run.js <step 2's example-run.json> definition/mechanisation/example-run.json`.
Expected:

- Translator: `elm-spec tests: 939, translated: 540`; the reasons `import:<local>`,
  `construct:record-alias-constructor`, `construct:main-shape`, `checks:unmatched`,
  `checks:unlabelled`, `checks:regex` have no test left, and `effects` has the 36 workers only;
  unit tests pass; `--check` up to date.
- `lake build`: no `sorry`, no new warning; each `Checks<S>.lean` logs its
  `#mod_program_theorems` line; `check-axioms` 0 problems; twins unchanged (21 pairs).
- `run-examples`: `Total: 1584 checks, 1584 agree, 0 diverge (0 known); K checks by decide +kernel,
  M by native_decide, in 540 program theorems.` with `K ≥ K2 - 2 + k`, where `K2` is step 2's
  figure, the `- 2` are the two `before: ()` rows (no theorem), and `k` is the number of the 84 new
  checks in programs proved by the kernel (all but the 2 regex checks and the checks of programs the
  translator marks native, listed in the report). The two CHECK-NOT rows of the strict tests count
  as kernel checks (covered by their `NoMeaning` theorems).
- The comparison script: `1500 rows compared, 4 changed (allowed), 0 other` (or other differences,
  each explained in the report as above).
- Memory budget: no `lean` process above 6.5 GB, summed PSS under 12 GB, measured by step 0's script.
  The module form evaluates each program once instead of once per check, which should lower the
  kernel's work; the default imports are evaluated per module (11 imports), which raises it a
  little. Programs moved to `budgetNative` are listed.
- Site: the test pages show the module-form translation (all modules) with their sources; each
  check links to its program's theorem; out-of-date detection uses `sources`; the rule pages of
  `r:dm-*` and `r:p-dyn-*` list the tests whose programs use them (by scanning the generated
  modules for the constructs each rule evaluates: `port` for `r:dm-topdec-port-*`, aliases with
  labels for `r:dm-typbind`, and so on, as `mechanisation-data.js` does for Core rules); the link
  audit at 0 problems. README ("What the theorems say": `ViewChecks`, `NoMeaning`, the tag
  `[harness]`, the order of the log and that `CHECK-NEXT` states that the book allows the order);
  report; preface count (540); plan status.

## Risks and fallbacks

- **Multi-module inference is the largest piece of work.** If qualified type names prove
  disruptive, a fallback keeps short names and refuses a program in which two modules declare types
  of one name (only ImportTypeByNameLaterReplacesTest needs both), counting it out of the gains.
- **Evaluating unused top-level values.** In module form every top-level value is evaluated
  (A59). A test whose unused value is costly or has no value would cost more or lose its meaning;
  in Elm/JS top-level values are also evaluated at initialisation, so such a test would already fail
  its run. If one appears, it is a finding about the test.
- **The kernel cost of a program's imports.** `evImports` runs per module inside every `decide`.
  If it shows in the budget, compute the environment of the default imports once,
  `E_default` (step 2), and let `Module.withDefaults` record that its first 11 imports are the
  defaults, with a lemma `evImports_defaults_append : evImports B (defaultImports ++ is) =
  (evImports B is).map (Env.merge E_default)` for `B` agreeing with `ME0` on the default modules,
  used by the evaluator.
- **The oracle search** is exponential in the number of choices; no test needs it today. If one
  does, the command's limit (12) is raised for that test only, by name.
- **Coordination with step 8.** Step 8 writes the source syntax and proves the derived form of
  modules; `Module.ofSource` and the translator's ordering of aliases are written to be replaced by
  it. Until then the grouping is trusted under `[elab]`.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

- **What "the value of a (program, label)" is in module form.** The plan's acceptance ("every
  (program, label) value in example-run.json unchanged") assumes one value per label. A module-form
  log may have several entries with one label (an inner `Debug.log` with the check's label, a
  helper's `main` logging the same label as EntryMainOfRootModuleTest's). This specification
  defines the row's `definition` as the distinct printed values of the entries with that label, and
  requires equality with the let form's list, listing any longer list with its reason.
- **K falls by 2 at this step.** Step 1 made the two `before: ()` checks of the strict tests kernel
  theorems; in module form they have no derivation to be about (the plan says so). The plan allows
  named exceptions; these are the two.
- **Statements are existential (D9) but often universal for free.** When the evaluator reads no
  choice, `viewChecks_every` turns the existential into "every derivation's log meets the check".
  This is true of every test today. The plan could say that the stronger reading is available
  wherever no function equality is evaluated, which matters for step 6's universal statements.
- **The translator still trusts the grouping of aliases.** Appendix A orders aliases by "mentions",
  which needs their type expressions; the reduced syntax drops them, so the translator orders them
  before printing. Aliases bind only record constructors, whose values do not depend on that order,
  so no dynamic result depends on it; step 8 brings the order into Lean.

## Progress

**2026-11-11, first increment done: the 498 programs of step 2 in module form.**

- `Mod/Program.lean`: Appendix A's derived form for modules (`Module.ofSource`: the custom types as
  one group, the aliases, then the definitions in `components`), the main module of a translated
  test (`Program.mainModule`: its top-level definitions, and `main` with main's locals and one
  `_ = Debug.log "label" e` per check in its let, `in text "done"`), `ViewChecks`, `NoMeaning`, their
  deciders proved sound (`viewChecks_sound`, `noMeaning_sound`) and `viewChecks_every`.
- This increment builds the module form in Lean from the let-form data the translator already
  writes (`Program` gains `types`); the translator's `ProgramIr` and `ModuleIr`, which the next
  increment needs for helper modules and ports, replace it there.
- `Theorems.lean`: `#mod_program_theorems` (one theorem per program: `ViewChecks`, or `NoMeaning`
  when a check expects no value); `#program_theorems`, `LetCheck`, `LetChecks` and `letChecks_sound`
  are retired. Main's let holding every check makes the kernel's reduction nest more deeply: the
  generated theorems set `maxRecDepth` 2048 (ContainerCompareCharTest and EqBoxedFastPathTest,
  with 20 checks each, need 1024).
- `Main.lean` (`run-examples`) runs each program once per constant oracle and reads each check's
  label in the log; a row's `definition` is the distinct printed values of the entries with that
  label. `runner/compare-example-run.js` compares two runs: against the let form's run, the two
  CHECK-NOT rows differ, as allowed; the two `before: ()` rows keep their value, from the partial
  log, with no theorem.
- 498 program theorems, 427 by the kernel and 71 native; 1,500 checks, all agreeing, 1,332 by the
  kernel and 166 native; 1,526 theorems, 0 axiom problems; largest process 3.0 GB, all together
  9.7 GB.

**2026-11-11, second increment done: the 42 tests, and one more.**

- Checks: the translator translates `main` whole and carries every CHECK line as written
  (`CheckLine`: CHECK, CHECK-DAG read as CHECK, CHECK-NEXT, CHECK-SAME, CHECK-NOT), with the kind
  of the value logged under its label (`Inferred.logTypes`); a labelled line must name a label that
  some `Debug.log` of the program writes as its literal first argument. `toLogChecks` (Theorems.lean)
  makes `.has`, `.run` and `.printed` statements; a `.printed` one is proved by `native_decide`.
  The translator no longer refuses CHECK-NEXT, CHECK-SAME, CHECK-DAG, `{{regex}}`, unlabelled
  CHECK lines, a check logged by a pipe, or a `main` that is not `let ... in text "..."`; `main`
  must be a view (`Node msg`), `Program` is refused `effects:worker`, anything else
  `construct:main-type`. `Html.text` has the harness's scheme. Gains: group E (9), HelloTest,
  CharCasePredicateTest, the two regular-expression checks; and CompilerIssue2019AliasOfTypeVariableTest,
  which the inventory had counted out ("a check the encoding cannot express"): it was refused only
  because `main` also logs a label that no CHECK line names, which the module form allows.
- Record alias constructors: the constructor scheme `τ1 -> ... -> τn -> P`, the aliases carried with
  their labels in the order written (5 tests).
- Modules: `Pipeline.resolve` reads a test's imports among its project's sources, depth-first
  post-order, refusing a cycle (`import:cycle`); `Convert.convertProgram` converts the modules in
  order with export tables (`Foreign` and `ForeignCon` names keep the spelling written); binding
  ids are unique across the program; a helper module's types are named `M.T` and its constructors'
  keys `M.K`; an annotation resolves through the module's own types and aliases, then the types its
  imports bring in (a later import's replacing an earlier one's); the modules are inferred in
  order with one substitution, and specialised as nested scopes, so a copy requested by a later
  module is placed in the module that declares it, and an exposing item stands for its copies, in
  the header and in an importer's list. The Lean `Program` gains its main module's exposing list
  and written imports and `helpers : List ModSrc` (9 tests).
- Ports: a port module and its port declarations are accepted; a port's direction and payload type
  come from its annotation (`portType`), anything else `construct:port-type`; imports of `Array`,
  `Bytes`, `Json.*`, `VirtualDom` and `Platform.*` are accepted (their values are still refused);
  the types `Cmd`, `Sub`, `Program`, `Value`, `Array`, `Bytes` are known to annotations.
  `Module.ofSource` puts the ports, each alone, after the aliases (15 tests).
- The manifest lists each program's `sources` with their hashes; the site marks a translation out
  of date when any of them changed, and names a program's modules on its test page. Theorems that
  name Chapter 7's or Chapter 9's rules (`r_dm_*`, `r_p_dyn_*`) link to the rules' pages.
- Translator tests: 90 (the "modules" group, the port tests, and the updated tests of the lifted
  refusals).
- Results: 541 of 939 tests translated (the 540 the plan expected and CompilerIssue2019); 1,585
  checks, all agreeing, 1,411 by the kernel and 172 native, in 541 program theorems; the comparison
  with the let form's run differs only in the two allowed rows. The inventory has no step 3 test
  left.

Differences from this specification: the Lean data keeps the let form's `Program` name and
shape (types, aliases, ports, definitions of the main module, plus `helpers`) rather than a
`ModProgram` with a list of modules; `Check.kind` keeps the translator's `CheckKind` rather than a
nested `Shape`; the rule pages of `r:dm-*` and `r:p-dyn-*` list tests by their TAGS, as the Core
rules' pages do, rather than by scanning the generated modules; and an imported alias is expanded
in the importing module's scope (no test depends on the difference).
