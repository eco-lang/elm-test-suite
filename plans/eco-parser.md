# Plan: replace elm-syntax with eco's parser in the translator

**Status (2026-11-14): reviewed once (adversarially, 21 findings, all folded in below) and lowered
to implementation steps. Done, 2026-11-14: steps 1 to 8, Acceptance 1 to 7 met (`verify.sh full`:
625 `legal_`, 287 refused, 611 `spec_`/`ident_`, 609 `mean_`, 15,680 theorems, 0 axiom problems;
191 translator unit tests; 0 broken links). Deviations, also in
`definition/tools/vendor/eco-parser/VENDORED.md`: the vendored modules are 12,219 lines, not about
13,500; a parse failure's manifest entry keeps `at` = the path and gains `detail` (E7), so the
entries of all 16 tests eco rejects change, not only those step 6 names; the Syn files of the changed
shards do not change as text (they name shards, not tests); the class `lexical-accepted` stays, now
with no test, beside the new `syntax-refused` (whose subclass is the front end's reason); E9's
reversal is an accessor (`Parse.recordPatternFields`) every reader uses, not a rewrite of the tree;
`describe` reads the innermost position from the error value, since the parser's own failure
position is the outermost; the Lean docstrings (step 7) were changed before the one `verify.sh
full` run, not after it.**

## Why

The translator (`definition/tools/src/Translate.elm`, `Translate/*.elm`) parses every test with
elm-syntax 7.3.9. Every theorem trusts that parse (`[parse]`), and elm-syntax is wrong both ways.

**Too strict.** It rejects `[-3, -2]` (a negative literal right after `[`), which Elm accepts.
So three compile-success tests are not in Lean: ContainerCompareIntTest,
ContainerEqualityFloatTest and ContainerEqualityIntTest.

**Too lenient.** It accepts programs Elm rejects:

- ParseErrorNumberBadHexDigitTest, ParseErrorNumberFractionThenLetterTest and
  ParseErrorStringEscapeTooFewDigitsTest are lexical errors.
- It groups operator chains with its own table, so the chains that `res:core-operator-chain`
  forbids cannot be seen afterwards: InfixMixedAssocComposeTest and InfixMixedAssocPipesTest.
- It reads `( )` as the unit pattern (StandardA1UnitPatternGapTest).

Each of these is a compile-error test that has no refusal theorem only because the parse lost the
error.

eco's parser (eco-compiler, `compiler/src/Compiler/Parse`) is a port of Elm's own. Two scratch
experiments ran it on all 941 `elm-spec` tests, their 13 helper modules and the 7 vendored elm/core
files (2026-11-14):

- **Compile-success tests:** it parses all 628 (elm-syntax: 625).
- **Lexical errors:** it rejects the three above.
- **Its tree** keeps an operator chain flat (`Binops`), a unit pattern's exact region, and whether a
  module has a header.
- **Same trees:** with chains grouped by the book's table, its tree is the same as elm-syntax's on
  every file both accept, but for the record-pattern field order (E9).

## What changes, and what does not

- **Changes.**
  - The translator's front end: every module that reads the parse tree. These are
    `Translate/Convert.elm`, `Source.elm`, `Classify.elm`, `Library.elm`, `LibraryTexts.elm`,
    `Pipeline.elm`, `Literal.elm` and `Translate.elm`.
  - The type expressions in `Translate/Ir.elm`, `Infer.elm` and `ToLean.elm`, which hold
    elm-syntax's `TypeAnnotation` today.
  - The front end also takes over two jobs elm-syntax did or skipped: grouping operator chains, and
    checking the restrictions on characters, tokens and layout that it can now see.
- **Does not change.** The rest of the IR, inference, specialisation, the printing of Lean, and
  Lean itself, but for docstrings. For every test both parsers accept and the front end does not
  refuse, the translator's Lean text and manifest entry stay byte for byte the same (Acceptance 1).

## Decisions

- **E1. Vendor eco's parser.**
  - **Where:** in `definition/tools/vendor/eco-parser/src/`, added to
    `definition/tools/elm.json`'s `source-directories`.
  - **Names:** eco's module names (`Compiler.*`) are kept, so that an upstream fix can be diffed
    and carried over.
  - **What else goes there:** eco's `LICENSE` (BSD-3, Evan Czaplicki and Décio Ferreira) and a
    `VENDORED.md`. The latter records the commit copied
    (`208a501d81ddf3aab19d8bbe21bd1f8123b785f3`), every edit made, and the kept modules with their
    line counts.
- **E2. What is kept** is the closure of `Compiler.Parse.Module.chompModule`, after the cuts of E3:

  | Directory | Modules |
  |---|---|
  | `Compiler/Lexer/` | `Primitives`, `Identifier`, `Keyword`, `Symbol`, `Unicode` |
  | `Compiler/Parse/` | `Module`, `Declaration`, `Expression`, `Pattern`, `Type`, `Variable`, `Number`, `String`, `Space`, and `Error` (types only) |
  | `Compiler/IR/` | `Source` (types and accessors only), `Source/Binop`, `Source/StringLiteral` |
  | `Compiler/Core/` | `Annotation`, `Name`, `Snippet` |
  | `Data/` | `Set`, `Map`, `Int64` |

  Why some of these are kept:
  - `Identifier` and `Symbol` import `Data.Set`, which imports `Data.Map`.
  - `Parse.Number` uses `Data.Int64`.
  - `StringLiteral` decodes literals (E8).
  - `Compiler.Core.Name` keeps only the names the kept modules use (about 11 of its 679 lines'
    worth).

  Target: about 13,500 lines in all, against 36,300 for eco's whole closure.
- **E3. What is cut, and the edit that cuts it.**
  - **Error reports:**
    - Cut `Compiler.Reporting.*`, `Text.PrettyPrint.ANSI.Leijen`, `Prelude` and
      `Compiler.Core.Index`.
    - `Parse/Error.elm` keeps lines 1–985 (the types) and loses `toReport` and everything after it.
      Its types' remaining uses of `ModuleName.Raw` become `String`.
  - **Codecs:**
    - Cut `Utils.Bytes.*`, `Compiler.Json.*`, `Data.NonEmptyList` and `Data.OneOrMore`.
    - Remove every encoder and decoder (and their imports) from `Source.elm`, `Annotation.elm`,
      `Binop.elm`, `Snippet.elm` and `Error.elm`.
  - **IO:**
    - Cut `Eco.*` and `System.*`. eco reads source as UTF-8 text too; the translator reads files
      with `BackendTask.File`.
    - `System.Crash.crash` in `Primitives.elm` (lines 103 and 697) becomes `Debug.todo`. The
      translator runs under `elm-pages run`, which compiles in debug mode.
  - **Packages and project types:**
    - Cut `Compiler.Elm.Package`, `Version`, `ModuleName` and `Compiler.Core.StringTable`.
    - `ProjectType` is removed. `chompModule` takes no argument.
    - It always parses `infix` declarations: elm/core's `List.elm` line 41 has one, and the
      library is parsed. The translator refuses a test program that declares one, as now.
    - `chompEffectModule` is removed, so `effect module` is a parse error.
  - **Default imports:** cut `Compiler.Parse.DefaultImports`. `chompModule` calls
    `chompImports []`, so the tree holds the imports as written. The translator handles the
    default imports itself, as now.
  - **eco's module checks:**
    - Cut `fromByteString` in `Parse/Module.elm`, `checkModule` and `checkKernelImports`.
    - On all 954 files, `chompModule` alone gives the same verdict as the checked parse.
    - The book's own rules (`res:modules-ports` and others) are checked by Lean, or by the front
      end (E6).
  - **Shaders:**
    - Cut `Compiler.Parse.Shader` and `Compiler.IR.Source.Shader`, the `Shader` constructor of
      `Expr_`, and the `[glsl|` branch of `Parse.Expression`.
    - No package for GLSL is added.
  - **Outside libraries in `StringLiteral.elm`:**
    - `NI.divMod` (`Numeric.Integer`) becomes `//` and `modBy`.
    - `Hex.toString` becomes a local four-line helper.
    - So no package is added to `definition/tools/elm.json`.
- **E4. One entry point: `Translate/Parse.elm`.**
  - It exposes `parse : String -> Result String Parsed`, with these types:

    ```elm
    type alias Parsed =
        { header : Maybe Header          -- eco's raw header: name, exposing, port flag, regions
        , imports : List Src.Import      -- in source order
        , infixes : List (A.Located Src.Infix)
        , decls : List Decl.Decl         -- in source order
        }
    ```

  - It runs `Compiler.Lexer.Primitives.fromByteString Module.chompModule E.ModuleBadEnd`, drops
    the comment wrappers, and turns an error (`E.Module`) into a short text with `describe`.
  - `describe` is in `Translate/Parse.elm`. It gives the row and column of the failure, then the
    first three constructor names of `Debug.toString` of the error.
- **E5. Grouping operators: `Translate/Fixity.elm`.**
  - The front end groups each `Binops` chain by the book's table, Figure `fig:core-fixities`
    (`definition/tex/syntax-core.tex`, about lines 360–375). It produces nested binary
    applications, as elm-syntax did. elm-syntax's table agrees with the book's on every operator
    the tests use.
  - A chain the book does not allow is refused. Its rule (`syntax-core.tex` lines 386–390): if two
    operators of the chain have equal precedence, and no operator of lower precedence stands
    between them, both must associate to the left or both to the right. A non-associative operator
    is neither. So `a << b >> c`, `1 < 2 == True` and `a == b == c` are all refused.
  - An operator not in the table is refused as outside the grammar.
- **E6. The front end checks what it can now see: `Translate/FrontEnd.elm`.**
  - These are the restrictions and grammar rules that belong to the concrete syntax, which stays
    outside Lean (`lean-full-definition.md`, "Out of scope"). Each refusal gives its reason and
    the row and column.

    | Reason | What it checks |
    |---|---|
    | `syntax:core-operator-chain` | E5 |
    | `syntax:operator` | an operator outside `fig:core-fixities` |
    | `syntax:tuple-arity` | a tuple expression, pattern or type with more than three components (ruling A12: tuple arity is in the grammar) |
    | `syntax:core-adjacent-items` | a `PUnit` whose region is not exactly two columns wide |
    | `syntax:core-escape-unicode` | an escape `\u{h}` in a character or string literal or pattern, read from the source text, whose value is a surrogate (D800–DFFF) or above 10FFFF |
    | `syntax:modules-header` | a module of the program (a helper module included) with no `module` or `port module` header |

  - **Adjacency.** eco's parser already rejects every other gap the restriction names: `( + )`,
    `x = ( )`, a type `( )`, `M. x`, `r. x` and `- x`. So only the unit pattern needs checking.
  - **Escapes are read from the source text,** at the literal's region, with a scanner that steps
    over `\\` (so `"\\u{D800}"` is not an escape). The region can span several lines (`"""`). This
    replaces today's `source:surrogate`.
  - **Tuple arity.** Today's unreachable `source:tuple-arity` (`Source.elm`) and
    `construct:tuple-arity` (`Convert.elm`) are removed.
- **E7. Where the checks run.** `FrontEnd.check : String -> Parsed -> List Refusal` runs on every
  module of a program, after it parses and before anything reads its tree:
  - in `Pipeline.parseAndTranslate`, for translation;
  - in `Translate.sourceSyntax`, for the source syntax.

  A refused program is not written as source syntax. Its manifest entry is
  `src: {status: "refused", reason: <reason>, at: <path>:<row>:<col>}`. A parse failure keeps
  `reason: "parse"`, with `detail` from `describe`.
- **E8. Literals are decoded.**
  - eco's `Chr`, `Str`, `PChr` and `PStr` hold the text JavaScript-escaped, not the value. For
    example `'\u{1F600}'` is held as `"\\uD83D\\uDE00"`.
  - The front end decodes them with `Compiler.IR.Source.StringLiteral.codePoints` into the code
    points, then into Elm `Char`s. Over 13,814 literals in 937 files this gave exactly elm-syntax's
    values.
  - `Int` and `Float` carry their source text (`Int 1 "0x1F"`). The translator keeps reading a
    literal's text from the source at its region (`Literal.textAt`), as now, so the printed
    constants do not change.
- **E9. Record-pattern fields are reversed.**
  - eco's `PRecord` holds the fields in reverse source order (`Parse/Pattern.elm`, line 214).
  - The front end reverses them back, before anything else reads them.
  - Eight test files depend on this, among them LetDestructRecordTest, RecordRowsTest and the
    WideRecord tests.
- **E10. Positions.**
  - eco's `Region` and elm-syntax's `Range` agree: rows and columns from 1, the end just past the
    last character, and columns counted in code points.
  - The translator gets its own `Translate.Region` (`{ start : {row,column}, end : {row,column} }`)
    from `A.Region`, and the manifest prints positions as before.
  - eco's `Import` has no region of its own. An `import:` refusal is placed at row = the row of the
    import's module name, column 1. Every import is at the start of its line, so this gives the
    same `17:1` as elm-syntax.
- **E11. Type expressions in the IR are eco's.**
  - `Ir.elm`, `Infer.elm`, `ToLean.elm` and `Library.elm` use `Compiler.IR.Source.Type` where they
    now use elm-syntax's `Node TypeAnnotation`.
  - `Infer.librarySchemes` takes the library's annotations as eco types.
  - `Classify` and `Source` print and read types through the same mapping (step 5).
- **E12. Node's stack.**
  - eco's parser recurses deeply. EtaExpandSeventeenArgumentAliasTest overflows node's default
    stack (about 984 KB), and 1,800 KB is enough for every file.
  - Every run of the translator becomes
    `node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm`.
    `elm-pages run` runs the script in-process, so the flag reaches it.
  - The flag is kept at 4,000. A much larger one (60,000) lets V8 run past the real 8 MB stack and
    segfault.
  - The flag goes in:
    - `.github/workflows/ci.yml` (line 146);
    - `definition/mechanisation/standard-elm-mech/scripts/verify.sh`;
    - `definition/tools/README.md`;
    - the top-level `README.md`;
    - the Lean README;
    - the command lines in `plans/` that run the translator.
  - The translator's elm-test suite runs in child processes, which cannot take the flag. So no unit
    test parses that test file.
- **E13. The tools hash covers the parser.** `toolsSha256` (`Translate.elm`, around lines 682 and
  702) hashes `definition/tools/src` and `definition/tools/vendor`. It calls
  `custom-backend-task.ts`'s `sha256Tree` on both and hashes the two results together.
- **E14. Trust.** `[parse]` now reads as follows:

  > eco's parser, vendored at commit 208a501, parses the test as Elm does. The translator's front
  > end groups operators by `fig:core-fixities` and checks the restrictions on characters, tokens
  > and layout.

  - One known difference from Elm: eco rejects an integer constant that does not fit a double
    exactly (`0x7FFFFFFFFFFFFFFF`, `NumberInexactOnHost`). No test has one.
  - This wording goes in the trust table of `lean-full-definition.md`, the Lean README,
    `Src/Syntax.lean` (`SExp`'s docstring: "as elm-syntax groups them"), `Src/SynCommand.lean`
    (line 16) and the site (`site/src/Mechanisation/View.elm`, `site/content/standard/generated.md`).
- **E15. elm-syntax stays only as an indirect dependency.**
  - elm-pages needs it, through elm-codegen and elm-syntax-dsl.
  - `stil4m/elm-syntax` moves from `direct` to `indirect` in `definition/tools/elm.json`.
  - No tools module imports `Elm.Syntax` or `Elm.Parser`.

## Implementation steps

Work in this order. Each step ends with a check that must pass before the next. Do not commit.

**Running things.** Run the translator from the repository root with E12's command, appending
`--check` to compare instead of writing. Run the translator's unit tests with
`cd definition/tools && ../../site/node_modules/.bin/elm-test --compiler ../../site/node_modules/.bin/elm`.
Lean is checked with `definition/mechanisation/standard-elm-mech/scripts/verify.sh quick|full`,
which runs itself in a 24 GB systemd scope.

**Before starting,** save the baseline:
`cp -r definition/mechanisation/standard-elm-mech/StandardElmMech/Generated <scratch>/gen-before`,
and copy `translation-manifest.json` and `static-classification.json`.

### Step 1. Vendor and trim

1. Copy the E2 modules from eco-compiler's `compiler/src/` (and `Data/` from there) into
   `definition/tools/vendor/eco-parser/src/`, at the same paths. Copy `compiler/LICENSE`.
2. Make the E3 edits, one module at a time:
   - `Parse/Module.elm`:
     - remove `fromByteString`, `checkModule`, `checkKernelImports`, `ProjectType`, `isCore`,
       `isKernel` and `chompEffectModule`;
     - `chompModule : P.Parser E.Module Module` always calls `chompInfixes` and passes `[]` to
       `chompImports`;
     - remove the `DefaultImports` import.
   - `Parse/Expression.elm`: remove the `Shader.shader` alternative and its import.
   - `IR/Source.elm`:
     - remove the `Shader` constructor, its import, and every `*Encoder` and `*Decoder` with
       their imports;
     - keep the types and plain accessors (`getName` and so on) the translator uses.
   - `Parse/Error.elm`: delete from `toReport` to the end of the file. Replace the
     `ModuleName.Raw` fields with `String`. Remove the codec functions and unused imports.
   - `Core/Annotation.elm`, `Core/Snippet.elm`, `IR/Source/Binop.elm`: remove the codecs.
   - `Core/Name.elm`: keep only the names some kept module uses (`grep -o 'Name\.[a-zA-Z]*'`).
   - `Lexer/Primitives.elm`: replace `System.Crash.crash` with `Debug.todo`.
   - `IR/Source/StringLiteral.elm`: replace `NI.divMod a b` with `( a // b, modBy b a )`, after
     checking the signs at its use. Replace `Hex.toString` with a local function.
3. Write `vendor/eco-parser/VENDORED.md`. It records the commit, the list of kept modules with line
   counts, and each edit above in one line per module.
4. Add `"vendor/eco-parser/src"` to `definition/tools/elm.json`'s `source-directories`.

**Check.**
- A throwaway module in `definition/tools/src/` that imports `Compiler.Parse.Module` compiles with
  `elm make` (delete it after).
- `grep -rn "^import" vendor/eco-parser/src` names only kept modules, elm/core modules, and nothing
  from `Utils`, `Json`, `Eco`, `System` or `Reporting`.
- `wc -l` of the kept modules is about 13,500.

### Step 2. `Translate/Parse.elm` and `Translate/Region.elm`

1. `Translate/Region.elm`:

   ```elm
   type alias Position = { row : Int, column : Int }
   type alias Region = { start : Position, end : Position }
   fromA : A.Region -> Region
   startText : Region -> String   -- "row:col", as Pipeline prints today
   ```

2. `Translate/Parse.elm`: `Parsed`, `parse` and `describe` as in E4. Also the accessors the
   consumers need:
   - `moduleName : Parsed -> Maybe String`;
   - `exposing_ : Parsed -> Src.Exposing`;
   - `isPortModule : Parsed -> Bool`;
   - `importsOf`, which gives the name, the alias, the exposing and the row of each import;
   - `declarations`.
3. Unit test (`definition/tools/tests/ParseTest.elm`): `parse` succeeds on a small module and on
   `[-3, -2]`; fails on `x = 0x1G`; keeps imports and declarations in source order; gives
   `header = Nothing` for a file without one.

**Check:** the unit tests pass. A throwaway elm-pages script that parses all 954 test files (tests
plus helpers) and the 7 library files gives exactly the reviewed verdicts: every compile-success
test parses, the 16 named compile-error tests fail, and all 7 library files parse.

### Step 3. `Translate/Fixity.elm`

1. Encode the book's operators, read from `fig:core-fixities` in `syntax-core.tex`:
   `table : Dict String { prec : Int, assoc : Left | Right | Non }`. List exactly the book's
   operators, no more.
2. Write `group : ( Expr, List ( op, Expr ) ) -> Result { reason : String, at : Region } Tree`, by
   precedence climbing. The tree is the translator's own binary form, which `Convert` and `Source`
   read where elm-syntax gave `OperatorApplication`.
3. Refuse a chain with E5's rule: equal precedence with no lower operator between, and not both
   left or both right. Refuse an operator not in the table.
4. Unit tests:
   - `a |> f |> g` groups to the left; `a :: b :: c` and `a ++ b ++ c` group to the right;
     `a + b * c` groups as `a + (b * c)`;
   - `a << b >> c`, `1 < 2 == True` and `a == b == c` are refused;
   - `a == (b == c)` is fine: the parentheses make a new chain.

**Check:** the unit tests pass.

### Step 4. `Translate/FrontEnd.elm`

1. `check : { path : String, source : String } -> Parsed -> List Refusal`, walking every
   expression, pattern and type of every declaration. Refusals follow E6's table.
2. The escape scanner works over the source text of a region. Within quotes it steps over `\x` as a
   pair; at `\u{` it reads hex digits to `}`.
3. Unit tests: one per row of E6's table, positive and negative. Include `"\\u{D800}"` (not an
   escape), a `"""` literal spanning lines, and `f () = 1` (fine).

**Check:**
- The unit tests pass.
- A throwaway run over all 954 files refuses exactly the 10 tests named in Acceptance 3, and
  nothing else.

### Step 5. Rewrite the consumers

Change each module from elm-syntax to `Parsed` and `Src`, in this order, compiling after each one.

The mapping:

| elm-syntax | eco | Note |
|---|---|---|
| `File`, `Module`, `Import`, `Declaration` | `Parsed`, `Header`, `Src.Import`, `Decl.Decl` | |
| `Node Range a` | `A.Located a` (`A.At region a`) | `Region.fromA` |
| `Exposing (All/Explicit)`, `TopLevelExpose` | `Src.Exposing (Open/Explicit)`, `Src.Exposed (Lower/Upper with Privacy/Operator)` | |
| `FunctionOrValue mod x` | `Var LowVar x`, `VarQual LowVar mod x` | |
| constructors | `Var CapVar`, `VarQual CapVar` | |
| `OperatorApplication` | `Binops` | grouped by `Fixity.group` |
| `PrefixOperator o` | `Op o` | |
| `Negation e` | `Negate e` | |
| `ParenthesizedExpression` | `Parens` | strip `C2` |
| `IfBlock` nested | `If first rest else` | a flat chain already; `Source.ifChain` reads it directly |
| `LetExpression` | `Let defs _ body` | `Define` / `Destruct` |
| `CaseExpression` | `Case` | |
| `LambdaExpression` | `Lambda` | |
| `Application (f :: args)` | `Call f arg args` | |
| `RecordExpr`, `RecordUpdateExpression` | `Record`, `Update` | strip `C2Eol`, keep field order |
| `RecordAccess`, `RecordAccessFunction` | `Access`, `Accessor` | |
| `TupledExpression` | `Tuple a b rest` | arity checked in step 4 |
| `UnitExpr` | `Unit` | |
| `ListExpr` | `List items _` | |
| `Integer`, `Hex`, `Floatable` | `Int value text`, `Float value text` | text from source as now (E8) |
| `CharLiteral`, `Literal` | `Chr`, `Str` | decoded (E8) |
| record pattern | `PRecord` | reversed (E9) |
| other patterns | `PAnything`, `PVar`, `PAlias`, `PTuple`, `PCtor`/`PCtorQual`, `PList`, `PCons`, `PChr`, `PStr`, `PInt`, `PUnit`, `PParens` | |
| `TypeAnnotation` | `Src.Type` | `TLambda`, `TVar`, `TType`/`TTypeQual`, `TRecord`, `TRecordExt`, `TUnit`, `TTuple`, `TParens` |

Comment wrappers are stripped with three small helpers in `Translate/Parse.elm`
(`c1 = Tuple.second`, `c2 = Tuple.second`, `c2eol = Tuple.second`).

The order:
1. `Literal.elm`: `textAt` takes a `Region` and reads across lines.
2. `Ir.elm`, `Infer.elm`, `ToLean.elm`: `Src.Type` for annotations (E11).
3. `Convert.elm`.
4. `Source.elm`. Drop its `isSurrogate` and `source:surrogate`, and the tuple-arity refusal.
5. `Classify.elm`. Its class `lexical-accepted` becomes `syntax-refused`, for a compile-error test
   the front end refuses.
6. `Library.elm`, `LibraryTexts.elm`.
7. `Pipeline.elm`: parse and run `FrontEnd.check` (E7).
8. `Translate.elm`: `sourceSyntax`, the library, the hash (E13), and the classification's class
   list (around line 979).

Rewrite `SourceTest`, `ClassifyTest` and `LibraryTest` for the new tree. `ClassifyTest` lines
68–71 expect a headerless helper to fail to parse; it now parses, and the front end refuses it.

**Check:**
- `grep -rln "Elm.Syntax\|Elm.Parser" definition/tools/src definition/tools/tests` is empty.
- The unit tests pass.
- Move `stil4m/elm-syntax` to indirect (E15). `elm make` still compiles all tools modules.

### Step 6. Run the translator; compare with the baseline

Run the translator (E12), then compare: `diff -r <scratch>/gen-before Generated`, and the manifest
and classification with a short script. The only differences allowed:

- **Container tests:** ContainerCompareIntTest, ContainerEqualityFloatTest and
  ContainerEqualityIntTest are now written, so the elm-core Src and Syn shards that hold them
  change. They are also translated if nothing else stops them.
- **Refused tests:** InfixMixedAssocComposeTest, InfixMixedAssocPipesTest,
  StandardA1UnitPatternGapTest, ParseErrorNumberBadHexDigitTest,
  ParseErrorNumberFractionThenLetterTest and ParseErrorStringEscapeTooFewDigitsTest are no
  longer written. So these shards and their Syn files change: `SrcElm_InfixAssocP`, `SrcElm_Mu`
  and `SrcElm_RecordNarrow06`.
- **Manifest:** the `src` entries of those nine tests and of the ten in Acceptance 3. A test's
  `detail`, where it held elm-syntax's text, now holds `describe`'s.
- **`toolsSha256`.**
- **Classification:** the entries of those nineteen tests.

Any other difference is a bug in steps 2–5. Fix it before going on.

### Step 7. Lean

Run `scripts/verify.sh full`. Then update:
- `Src/Syntax.lean` and `Src/SynCommand.lean` docstrings (E14);
- the Lean README (`[parse]`, the translator command);
- `plans/lean-full-definition.md`: the trust table, and one clause in the status line;
- a dated block at the top of `mechanisation-report.md` with the new counts.

### Step 8. Runner, site and documents

- **`runner/mechanisation-data.js`:**
  - `leanStaticStatus` maps `src.reason` `syntax:*` to a new status `error:syntax`, and reads the
    class `syntax-refused` where it read `lexical-accepted`;
  - `error:lexical` and `source:surrogate` are removed.
- **`site/src/Mechanisation/View.elm`:**
  - `staticWords`:
    - `error:parse`: "expected to be rejected, and eco's parser rejects it too";
    - `error:syntax`: "expected to be rejected, and the translator's front end refuses it: it
      breaks a restriction on characters, tokens and layout, which Lean does not model";
    - `success:parse`: name eco's parser.
  - `reasonWords "parse"`: "is not parsed by eco's parser".
- **`site/content/standard/generated.md`:** step 1 names eco's parser.
- **Commands:** apply E12's command everywhere it lists; also `definition/tools/README.md`.
- Regenerate the site data, build the site, and run the link audit.

## Acceptance

1. **Unchanged output.** For every test both parsers accept and the front end does not refuse, its
   definitions in `Generated/` and its manifest entry are unchanged. Only the files and entries
   step 6 names differ.
2. **Newly accepted.** The three Container tests are written as source syntax and have `legal_`
   theorems.
3. **No error lost.** Each of the 26 compile-error tests without a refusal theorem is now either
   rejected by eco's parser or refused by the front end:
   - **Rejected by eco's parser (16):**
     - AnnotationNotFollowedByDefinitionTest, ImportAliasQualifiedTest
     - InfixNoQualifiedOperatorTest, InfixNoSectionLeftTest, InfixNoSectionRightTest
     - ParseErrorCasePatternUnfinishedTest
     - ParseErrorNumberBadHexDigitTest, ParseErrorNumberFractionThenLetterTest
     - ParseErrorStringEscapeTooFewDigitsTest, ParseErrorStringEscapeUnclosedTest
     - PortProblemDeclarationWithoutNameTest, RecordUpdateNoFieldsTest
     - TopLevelPatternBindingTest, TypeExprUnitAppliedTest
     - UnexpectedPatternFloatWithExponentTest, WeirdElseBranchElseNotIndentedTest
   - **Refused by the front end (10):**

     | Reason | Tests |
     |---|---|
     | `core-operator-chain` | InfixNonAssocCompareTest, InfixNonAssocEqTwiceTest, InfixMixedAssocComposeTest, InfixMixedAssocPipesTest |
     | `operator` | UnknownOperatorAnUnknownOperatorTest |
     | `tuple-arity` | BadTupleATupleOfFourTest |
     | `core-escape-unicode` | CharLiteralSurrogateEscapeTest, StandardA8SurrogateEscapeTest |
     | `core-adjacent-items` | StandardA1UnitPatternGapTest |
     | `modules-header` | ModuleHeaderMissingImportedTest |

   No compile-error test keeps the class `lexical-accepted`.
4. **Nothing lost in Lean.** `scripts/verify.sh full` passes with:
   - 625 `legal_` (622 plus the Container tests) and 287 refused;
   - `spec_` and `ident_` at least 608;
   - run-examples and compare-e2e all agreeing;
   - 0 axiom problems.
5. **No direct elm-syntax.** `stil4m/elm-syntax` is only indirect in `definition/tools/elm.json`,
   and no tools module imports `Elm.Syntax` or `Elm.Parser`. The translator's unit tests pass.
6. **Small vendor.** The vendored modules come to about 13,500 lines. `VENDORED.md` lists them and
   every edit.
7. **Site.** The site builds, with 0 broken links. No page names elm-syntax as the parser.
