# Vendored: eco's parser

These modules are copied from eco-compiler (`gitlab.thesett.com/rupert/eco-compiler`), `compiler/src/`,
at commit `208a501d81ddf3aab19d8bbe21bd1f8123b785f3`, under its BSD-3 licence (`LICENSE`, Evan
Czaplicki and Décio Ferreira). eco's parser is a port of the Elm compiler's own. The module names
are eco's, so that an upstream fix can be diffed and carried over.

What is kept is the closure of `Compiler.Parse.Module.chompModule`, after the cuts below
(`plans/eco-parser.md`, decisions E1–E3). The translator reaches it only through
`src/Translate/Parse.elm`.

## Modules

| Module | Lines | Edits |
|---|---:|---|
| `Compiler/Core/Annotation.elm` | 153 | Binary encoders and decoders (`regionEncoder` … `locatedDecoder`) and their imports removed; docstring notes the cut. |
| `Compiler/Core/Name.elm` | 70 | Rewritten to keep only `Name`, `fromPtr` and `mainModule`, the names the kept modules use (eco has 679 lines). |
| `Compiler/Core/Snippet.elm` | 64 | `encoder` and `decoder` and their imports removed. |
| `Compiler/IR/Source.elm` | 768 | The `Shader` constructor of `Expr_` and its import removed; every encoder and decoder (from `-- ENCODERS and DECODERS` to the end) and their imports removed. Types and accessors unchanged. |
| `Compiler/IR/Source/Binop.elm` | 53 | The four codecs and their imports removed. |
| `Compiler/IR/Source/StringLiteral.elm` | 206 | `NI.divMod a 0x0400` (`Numeric.Integer`) becomes `( a // 0x0400, modBy 0x0400 a )` (its argument `code - 0x10000` is never negative there); `Hex.toString` becomes a local `hexString`. |
| `Compiler/Lexer/Identifier.elm` | 287 | none |
| `Compiler/Lexer/Keyword.elm` | 521 | none |
| `Compiler/Lexer/Primitives.elm` | 813 | `import System.Crash` removed; `crash` in `unsafeIndex` becomes `Debug.todo`. |
| `Compiler/Lexer/Symbol.elm` | 144 | `badOperatorEncoder` and `badOperatorDecoder` and the `Bytes` imports removed (not named in the plan; removed in the same spirit as the other codecs). |
| `Compiler/Lexer/Unicode.elm` | 2048 | none |
| `Compiler/Parse/Declaration.elm` | 544 | none |
| `Compiler/Parse/Error.elm` | 920 | Everything from `toReport` to the end (the reports and the codecs) removed, and the imports they used; the two `ModuleName.Raw` fields of `Error` become `String`. |
| `Compiler/Parse/Expression.elm` | 1406 | The `Shader.shader` alternative of `term` and its import removed, so `[glsl|` is a parse error. |
| `Compiler/Parse/Module.elm` | 648 | `fromByteString`, `ProjectType`, `isCore`, `isKernel`, `checkKernelImports`, `checkModule`, `checkEffects`, `categorizeDecls`, the doc-comment helpers, the `effect module` parsers (`chompEffectModule` … `spaces_em`) and the `DefaultImports` and `Package` imports removed. `chompModule` takes no argument, passes `[]` to `chompImports` and always calls `chompInfixes`. The `Manager` constructor of `Effects` is kept but never produced. |
| `Compiler/Parse/Number.elm` | 583 | none |
| `Compiler/Parse/Pattern.elm` | 516 | none |
| `Compiler/Parse/Space.elm` | 495 | none |
| `Compiler/Parse/String.elm` | 560 | none |
| `Compiler/Parse/Type.elm` | 488 | none |
| `Compiler/Parse/Variable.elm` | 390 | none |
| `Data/Int64.elm` | 150 | none |
| `Data/Map.elm` | 235 | none |
| `Data/Set.elm` | 157 | none |
| **Total** | **12219** | |

The plan estimated about 13,500 lines; the cut of `Compiler.Core.Name` to three names and of the
`effect module` parsers make it smaller.

## Cut whole

- **Error reports:** `Compiler.Reporting.*`, `Text.PrettyPrint.ANSI.Leijen`, `Prelude`, `Compiler.Core.Index`.
- **Codecs:** `Utils.Bytes.*`, `Compiler.Json.*`, `Data.NonEmptyList`, `Data.OneOrMore`.
- **IO:** `Eco.*`, `System.*`. The translator reads files with `BackendTask.File`.
- **Packages and project types:** `Compiler.Elm.Package`, `Compiler.Elm.Version`, `Compiler.Elm.ModuleName`, `Compiler.Core.StringTable`.
- **Default imports:** `Compiler.Parse.DefaultImports`. The tree holds the imports as written.
- **Shaders:** `Compiler.Parse.Shader`, `Compiler.IR.Source.Shader`. No GLSL package is added.

No package is added to `definition/tools/elm.json` for these modules.

## Running

eco's parser recurses deeply, so the translator runs as
`node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm`
(plan E12).

## Notes and deviations from plans/eco-parser.md

- **Size.** 12,219 lines, against the plan's estimate of about 13,500: `Compiler.Core.Name` keeps
  three names (the kept modules use only `Name`, `fromPtr` and `mainModule`), and the `effect module`
  parsers, the doc-comment helpers and the module checks of `Parse/Module.elm` are cut.
- **`Symbol.elm`'s codecs** are removed too, though the plan did not list them: they were the only
  use of `elm/bytes` left.
- **`Effects.Manager`** (in `Parse/Module.elm` and `Compiler.IR.Source`) is kept, so that the types
  stay as upstream's; the vendored parser never produces it.
- **Error positions.** `Primitives.fromByteString`'s error carries, at each wrapping constructor,
  the position where that construct began; the failure's own position is the innermost one.
  `Translate.Parse.describe` finds it by reading the error's `Debug.toString` as a tree and taking
  the innermost constructor that carries a position (the constructors of `Space`, `Char`, `String_`,
  `Number`, `Escape` and `BadOperator` carry none). No vendored file is changed for this.
- **Record patterns.** eco keeps a record pattern's fields reversed (`Parse/Pattern.elm`); the tree
  is not rewritten. `Translate.Parse.recordPatternFields` gives them in source order, and every
  reader of `PRecord` (Convert, Source, Classify) reads them through it.
- **Stack.** Without `node --stack-size=4000` the translator does not report an overflow: the run
  stops partway, with exit status 0 and no summary. `verify.sh`'s translate-check would then fail.

