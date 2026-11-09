# Language Survey: Elm 0.19.1 (eco 0.2.0)

Assembled from four survey parts. Each part cites `path:line` with the path
prefixes defined in its own Sources subsection. Candidate ambiguities from all
parts are in `ambiguity-log.md`, renumbered A1 to A86 with rulings; later
stages cite rulings as A<n> and author directions (in `book-brief.md`) as D<n>.

## Sources

| Part | Section here | Draft |
|------|--------------|-------|
| Lexis and syntax | "Lexis", "Phrase Classes" | `drafts/survey-syntax.md` |
| Static semantics | "Static Semantics" | `drafts/survey-static.md` |
| Dynamic semantics and basic operations | "Dynamic Semantics and Basic Operations" | `drafts/survey-dynamic.md` |
| Programs, platform, effects and ports | "Programs, Platform, Effects and Ports" | `drafts/survey-platform.md` |

Reference Elm 0.19.1 compiler source (Haskell) is at
`/home/rupert/sc/github/elm/compiler`; elm/core 1.0.5 source at
`/home/rupert/.eco/0.2.0/packages/elm/core/1.0.5/src`; Elm's JS kernel at
`/home/rupert/.elm/0.19.1/packages/elm/core/1.0.5/src/Elm/Kernel`.

## Lexis




Scope: the lexical and context-free syntax of Elm 0.19.1 as eco accepts it, plus the
restrictions eco enforces without type information (parser and canonicaliser). No typing,
no evaluation.

Cite convention: every path is relative to `/home/rupert/sc/gitlab/eco-compiler`, except
paths starting `elm/`, `elm-parser/` or `elm-url/`, which are relative to
`/home/rupert/.eco/0.2.0/packages/` (`elm/core/1.0.5/src/...`, `elm/parser/1.1.0/src/...`,
`elm/url/1.0.0/src/...`).

### Sources

| Part | Paths |
|------|-------|
| Design intent | `THEORY.md:7` (eco "adds back ends, not a language"; Guida's extensions removed), `design_docs/theory/compiler/front-end.md:7` (no underscores in numbers, no binary literals, no tuples above three), `design_docs/theory/compiler/front-end.md:38` (commit-on-consume parser discipline), `design_docs/elm-divergence.md:204-220` (eco-only size limits) |
| Lexer | `compiler/src/Compiler/Lexer/Keyword.elm`, `Identifier.elm`, `Symbol.elm`, `Primitives.elm` (combinators, indent state), `Unicode.elm` (letter classes) |
| Whitespace, comments, layout | `compiler/src/Compiler/Parse/Space.elm` |
| Literals | `compiler/src/Compiler/Parse/Number.elm`, `compiler/src/Compiler/Parse/String.elm` |
| Names | `compiler/src/Compiler/Parse/Variable.elm` |
| Phrase parsers | `compiler/src/Compiler/Parse/Expression.elm`, `Pattern.elm`, `Type.elm`, `Declaration.elm`, `Module.elm`, `Shader.elm`, `DefaultImports.elm` |
| Source AST | `compiler/src/Compiler/IR/Source.elm:334-787`, `compiler/src/Compiler/IR/Source/Binop.elm` |
| Canonicaliser (syntactic checks, operator grouping) | `compiler/src/Compiler/Canonicalize/Expression.elm`, `Pattern.elm`, `Type.elm`, `Module.elm`, `LocalEnvironment.elm`, `Environment.elm`, `Environment/Foreign.elm`, `Dups.elm`, `Error.elm` |
| Canonical AST (to see what is not desugared) | `compiler/src/Compiler/IR/Canonical.elm:150-220` |
| Fixities | `elm/core/1.0.5/src/Basics.elm:71-89`, `elm/core/1.0.5/src/List.elm:41`, `elm/parser/1.1.0/src/Parser.elm:58-59`, `elm/url/1.0.0/src/Url/Parser.elm:49-50` |
| Kernel-package test | `compiler/src/Compiler/Elm/Package.elm:29-31,158-160` |
| Parser unit tests | `compiler/tests/Compiler/Parse/*.elm` (Expression, Module, Number, String, Variable*) |
| Rejection catalogues | `compiler/tests/SourceIR/CanonicalizeFailsCases.elm`, `compiler/tests/SourceIR/PatternFailsCases.elm` |
| E2E tests | `test/elm/src/*.elm` (623 programs), `test/elm-compile-errors/src/*.elm` (223 files, must be rejected), `test/elm-bugs/src`, `test/elm-bug-fixes/src`, `test/eco-divergence/src` |

### Lexis

#### Reserved Words

| Word | Truly reserved? | Used in | Cite |
|------|-----------------|---------|------|
| `if` `then` `else` | yes | conditional | `compiler/src/Compiler/Lexer/Identifier.elm:78-80`; `Keyword.elm:98,105,112` |
| `case` `of` | yes | case expression | `Identifier.elm:81-82`; `Keyword.elm:123,130` |
| `let` `in` | yes | let expression | `Identifier.elm:83-84`; `Keyword.elm:141,148` |
| `type` | yes | custom type, `type alias` | `Identifier.elm:85`; `Keyword.elm:73` |
| `module` | yes | header | `Identifier.elm:86`; `Keyword.elm:191` |
| `where` | yes | effect-module header only | `Identifier.elm:87`; `Keyword.elm:230` |
| `import` `exposing` `as` | yes | imports, header, `as` patterns | `Identifier.elm:88-90`; `Keyword.elm:198,205,212` |
| `port` | yes | port declaration, `port module` | `Identifier.elm:91`; `Keyword.elm:87` |
| `alias` | no (contextual) | after `type` | `Keyword.elm:23-26,80` |
| `infix` `left` `right` `non` | no (contextual) | infix declaration (kernel only) | `Keyword.elm:23-26,159-180` |
| `effect` `command` `subscription` | no (contextual) | effect-module header | `Keyword.elm:23-26,223,237,248` |

- Reserved means: `Var.lower` refuses it as an unqualified lower-case identifier (`compiler/src/Compiler/Parse/Variable.elm:82-108`, `Identifier.elm:64-92`). Only unqualified names are checked; the last part of a qualified name is not (`Variable.elm:17-19,336-349`). See C-SYN-2.
- A keyword matches only as a whole word: the character after it must not be an identifier inner character (`Keyword.elm:10-21`). So `types`, `if_`, `letter` are identifiers.
- Upper-case words are never reserved (no upper-case keyword exists).

#### Identifier Classes

| Class | Lexical form | May be qualified? | Cite |
|-------|--------------|-------------------|------|
| lower identifier (values, fields, type variables, pattern variables) | lower-case letter, then inner chars; not a reserved word | values only, as `M1.M2.x` | `Identifier.elm:12-20`, `Variable.elm:82-108,315-349` |
| upper identifier (types, constructors, module-name parts, import alias) | upper-case or title-case letter, then inner chars | types and constructors, as `M1.M2.T` | `Identifier.elm:99-148`, `Variable.elm:54-71,240-274` |
| module name | upper identifiers joined by `.`, no spaces | n/a | `Variable.elm:136-176` |
| operator | maximal run of `+ - / * = . < > : & \| ^ ? % !` that is not exactly one of `.` `\|` `->` `=` `:` | never | `compiler/src/Compiler/Lexer/Symbol.elm:12-16,80-119,150-152` |

- Character classes: ASCII `a-z` / `A-Z` start lower / upper; inner chars are ASCII letters, ASCII digits, `_`. Beyond ASCII: upper start = Unicode Lu or Lt, lower start = Ll, inner = any letter (Lu, Ll, Lt, Lm, Lo); non-ASCII digits are not inner chars (`Identifier.elm:21-36,243-263`). Tables are Unicode 14.0.0 (`compiler/src/Compiler/Lexer/Unicode.elm:1-12`). An Lo letter (e.g. CJK) may continue but not start a name (`Identifier.elm:29-30`). See C-SYN-14.
- `_` cannot start an identifier; `_` alone is the wildcard pattern and `_x` is an error (`compiler/src/Compiler/Parse/Pattern.elm:139-175`).
- Qualification rule for `foreignAlpha` (expressions): upper parts followed by `.` form the home; the first lower part ends the name, so `List.map.x` is `List.map` then field `.x` (`Variable.elm:302-313`). `Maybe.Just` is a qualified constructor; `Maybe.withDefault` a qualified value.
- `foreignUpper` (types, constructor patterns): every part must be upper; `Maybe.withDefault` there is an error (`Variable.elm:230-239`).
- Record fields, type variables, pattern variables, declared names, import aliases (`Variable.upper`, single part) and operators are never qualified (`compiler/src/Compiler/Parse/Module.elm:1092-1100`).
- Operators: there is no syntax for a qualified operator; an operator is only in scope through an `exposing` list (see Infix and Precedence). No backtick infix application exists (backtick is in no character class).

#### Special Constants

| Kind | Form | Rules | Cite |
|------|------|-------|------|
| Int, decimal | `[0-9]+` | must start with a digit (no sign: `-1` is negation of `1`); a leading `0` may only be `0`, `0.`fraction or `0x`hex (`007` is `NumberNoLeadingZero`); must not run into an identifier char (`12abc`, `1_000` are `NumberEnd`) | `compiler/src/Compiler/Parse/Number.elm:11-28,247-270,410-431` |
| Int, hex | `0x[0-9a-fA-F]+` | lower-case `x` only; at least one digit; no fraction or exponent; no `_`; no binary or octal forms | `Number.elm:11-13,421-422,441-450,524-531`; `compiler/tests/Compiler/Parse/NumberTest.elm:116-140` |
| Int value | | digits taken modulo 2^64 as two's complement (`0xFFFFFFFFFFFFFFFF` = -1); when the compiler runs on JS a value needing >53 bits that cannot be read exactly is `NumberInexactOnHost` | `Number.elm:86-93,160-177`; `NumberTest.elm:141-160` |
| Float | digits `.` digits [exponent] or digits exponent; exponent = `e`/`E` [`+`/`-`] digits | `.` must be followed by a digit (`1.`, `1.e5` are `NumberDot`); `.5` is not a number; `0e5` is `NumberEnd` (no exponent after a lone `0`); value = `String.toFloat` of text | `Number.elm:11-13,276-302,335-372,405-406` |
| Char | `'` c `'` | exactly one code point or escape between quotes (`''`, `'ab'` are `CharNotString`); raw newline is an error; a bare `"` is allowed | `compiler/src/Compiler/Parse/String.elm:6-11,40-85,112-160` |
| String, single-line | `"` ... `"` | may not contain a raw newline; bare `'` allowed; `""` is the empty string unless a third `"` follows | `String.elm:163-222,284-335` |
| String, multi-line | `"""` ... `"""` | may span lines; raw `"` allowed; closes at the first `"""`; text after the opening `"""` is kept verbatim (a leading newline is not stripped) | `String.elm:351-416`; `test/elm-bugs/src/CompilerIssue1947MultilineStringInLetBinopTest.elm` (expects `"\n!"`) |
| Escapes (strings and chars) | `\n` `\r` `\t` `\"` `\'` `\\` `\u{H...}` | `\u{}` needs 4 to 6 hex digits (either case), value at most `10FFFF` (checked before length); any other escape is `EscapeUnknown` | `String.elm:6-11,448-520` |

- Literal values are kept in escaped source form, with normalisations (see Rewrites) (`String.elm:13-20`).
- Surrogate code points are not rejected in `\u{...}` (only `> 10FFFF` is) (`String.elm:510-511`). See C-SYN-8.
- Raw tab characters are legal inside strings and chars (no tab case in `String.elm:112-160,284-335`).

#### Comments

| Form | Nesting | Notes | Cite |
|------|---------|-------|------|
| `--` to end of line | n/a | may contain tabs; CR before LF is part of it | `compiler/src/Compiler/Parse/Space.elm:236-238,264-314` |
| `{-` ... `-}` | yes, counts `{-`/`-}` pairs | tab inside is an error; unclosed is `EndlessMultiComment` | `Space.elm:12-14,316-416` |
| `{-\|` ... `-}` doc comment | yes (inner `{-` `-}` nest) | NOT whitespace: a gap stops before `{-\|` (`Space.elm:16-18,332-333`), so it is legal only where the grammar reads one: after the module header (`Module.elm:558-590`) and before a top-level declaration (`compiler/src/Compiler/Parse/Declaration.elm:112-127`); the next token must then start in column 1 | `Space.elm:423-495` |

- Whitespace is space, LF, and CR (CR does not advance the column, `Space.elm:276-277`). A tab outside a line comment is the error `HasTab` (`Space.elm:13-15,279-280`).
- `--` is recognised only where a gap is read; inside an operator run it is part of the operator (`Symbol.elm:12-16`, `Space.elm:264-274`). See C-SYN-3.

#### Layout and Indentation

Elm has no layout tokens (no implicit braces or semicolons). The parser state carries one
integer, the _indent_, and every layout decision compares the start column of the next token
with it.

**Columns.** Rows and columns start at 1; LF resets the column to 1; each character
(code point, including astral ones) is one column; CR in whitespace adds no column
(`compiler/src/Compiler/Lexer/Primitives.elm:19-27`, `Space.elm:24-25,258-277`,
`Identifier.elm:35-36`). See C-SYN-6.

**Three predicates** on the current column `c` (the column of the next token after a gap):

| Predicate | Test | Cite |
|-----------|------|------|
| indented | `c > indent` and `c > 1` | `Space.elm:115-131,169-197` |
| aligned | `c == indent` | `Space.elm:134-148` |
| fresh line | `c == 1` | `Space.elm:151-162` |

**Setting the indent.** Initially 0 (`Primitives.elm:50,368`). `withIndent p` runs `p` with
indent := current column; `withBacksetIndent k p` with indent := current column - k; both
restore the old indent on success (`Primitives.elm:497-540`). These are used in exactly two
places, `let` and `case`:

| Context | Rule | Cite |
|---------|------|------|
| Module structure | header, each import, each `infix`, each top-level declaration starts on a fresh line (column 1); the file must be fully consumed | `Module.elm:492-532,724-742,1060-1090`, `Primitives.elm:363-398` |
| Inside a top-level declaration | indent stays 0, so every later token must be indented, i.e. column >= 2; a token in column 1 ends the declaration | `Declaration.elm:15-19`, `Module.elm:520-532` |
| Top-level annotation | `x : t` then the definition must start on a fresh line and repeat `x` | `Declaration.elm:26-27,163-164` |
| Doc comment | the token after a doc comment must be on a fresh line | `Declaration.elm:104-127`, `Module.elm:558-590` |
| `let` definitions | after `let`, indent := column of `let` (backset 3); the first definition must be indented relative to it; then indent := column of the first definition; each later definition must be aligned with it; tokens inside a definition must be indented relative to it | `compiler/src/Compiler/Parse/Expression.elm:1148-1176,1206-1222` |
| `let` annotation | the definition must be aligned with the annotation and repeat the name | `Expression.elm:1279-1290` |
| `in` and body | indent is restored to the enclosing value before `in`; `in` and the body need only be indented relative to the enclosing indent (not the `let` column) | `Expression.elm:1150-1152,1179-1187` |
| `case` branches | scrutinee, `of` and the first pattern are checked against the enclosing indent (not the `case` column); then indent := column of the first pattern; each later branch must be aligned with it; a branch body must be indented relative to it | `Expression.elm:1044-1068,1125-1141` |
| Everything else | arguments, operators and their right operands, `then`/`else`, lambda args/arrow/body, list/tuple/record entries and their `,` `]` `)` `}`, pattern `::`/`as`/constructor args, type args, `->` in types, `\|` between variants, header/import/exposing tokens: each must be indented relative to the current indent | `Expression.elm:29-33,184-224,591-617,795-837,946-1014`; `Pattern.elm:364,395-405,500`; `compiler/src/Compiler/Parse/Type.elm:18-22,300-332`; `Declaration.elm:402-414`; `Module.elm:1031-1036` |

Consequences recorded from the code:
- A construct ends at the first token that fails its test: `chompExprEnd`, `chompCaseEnd`, `chompLetDefs`, type `chompArgs`, `chompVariants` all fall back to "done" when the indentation check fails (`Expression.elm:588-723,1134-1141,1215-1222`; `Type.elm:311-332`; `Declaration.elm:402-414`).
- `let x = 1 in x` on one line is legal; two `let` definitions or two `case` branches cannot share a line (alignment is exact column equality).
- Nested `case` expressions are separated purely by pattern columns (`Expression.elm:1055-1068`).
- Continuation lines may sit left of where the construct began, provided they are right of the indent (e.g. an operator line left of the start of its left operand).
- The test is on the start column of the next token only; where the previous token ended is irrelevant except as the error position (`Space.elm:115-121`). See C-SYN-5 (multi-line strings).
- `test/elm-compile-errors/src/WeirdElseBranchElseNotIndentedTest.elm`: `else` aligned with the enclosing let definition is rejected.

#### Infix and Precedence

Operator chains are parsed flat (`Src.Binops`, operands and operators in source order) and
grouped during canonicalisation using each operator's declared fixity
(`Expression.elm:17-21`; `compiler/src/Compiler/Canonicalize/Expression.elm:33-37,682-860`).

Grouping algorithm (`Canonicalize/Expression.elm:793-860`): higher precedence binds tighter;
equal precedence groups left if both operators are `left`, right if both are `right`; any other
equal-precedence pair (either is `non`, or `left` meets `right`) is the error `Binop`
(`compiler/src/Compiler/IR/Source/Binop.elm:50-63`).

| Operator | Assoc | Prec | Function | Cite |
|----------|-------|------|----------|------|
| `<\|` | right | 0 | `apL` | `elm/core/1.0.5/src/Basics.elm:71` |
| `\|>` | left | 0 | `apR` | `Basics.elm:72` |
| `\|\|` | right | 2 | `or` | `Basics.elm:73` |
| `&&` | right | 3 | `and` | `Basics.elm:74` |
| `==` `/=` `<` `>` `<=` `>=` | non | 4 | `eq` `neq` `lt` `gt` `le` `ge` | `Basics.elm:75-80` |
| `++` | right | 5 | `append` | `Basics.elm:81` |
| `::` | right | 5 | `cons` | `elm/core/1.0.5/src/List.elm:41` |
| `+` `-` | left | 6 | `add` `sub` | `Basics.elm:82-83` |
| `*` `/` `//` | left | 7 | `mul` `fdiv` `idiv` | `Basics.elm:84-86` |
| `^` | right | 8 | `pow` | `Basics.elm:87` |
| `<<` | left | 9 | `composeL` | `Basics.elm:88` |
| `>>` | right | 9 | `composeR` | `Basics.elm:89` |
| `\|=` / `\|.` (elm/parser) | left | 5 / 6 | `keeper` / `ignorer` | `elm/parser/1.1.0/src/Parser.elm:58-59` |
| `</>` / `<?>` (elm/url) | right / left | 7 / 8 | `slash` / `questionMark` | `elm/url/1.0.0/src/Url/Parser.elm:49-50` |

- No core operator has precedence 1.
- Rejected mixes (equal precedence, incompatible associativity): any two comparison operators (`a < b < c`, `a == b /= c`); `<|` with `|>`; `<<` with `>>`; `|=` with `++` or `::`. Accepted: `x :: ys ++ zs` = `x :: (ys ++ zs)`.
- **Declaring infix.** `infix` declarations are parsed only when the project is a kernel project (`Module.elm:150-162,212-216`), i.e. a package whose author is `elm`, `elm-explorations` or `eco` (`Package.elm:29-31,158-160`), or an application compiled as such a package (`Module.elm:118-130`). Elsewhere `infix left 6 ...` is read as an ordinary value declaration named `infix` and fails to parse. Form and placement: Infix declarations below.
- **Scope.** A module's own infix declarations become its exportable operators (`compiler/src/Compiler/Canonicalize/Module.elm:109-111,146-162`) but are not added to its own scope; operators come only from imports (`compiler/src/Compiler/Canonicalize/Environment/Foreign.elm:233,239`). The default `import Basics exposing (..)` and `import List exposing ((::))` supply the core operators (`compiler/src/Compiler/Parse/DefaultImports.elm:9-11`). An operator not in scope is `NotFoundBinop` (`test/elm-compile-errors/src/UnknownOperatorAnUnknownOperatorTest.elm`).
- **Operator as value.** `(op)` with no whitespace or comment between the parentheses and the operator; the only operator form. There are no left or right sections and no tuple section `(,)` (`Expression.elm:232-241,255-320`).
- **Negation.** Prefix `-` immediately followed (no whitespace) by a term; applies to that term only, so `-f x` is `(-f) x` and `-r.x` is `-(r.x)` (`Expression.elm:23-27,740-756`). After a term, a `-` with whitespace before and none after (`f -x`) negates the next term, which becomes an argument; otherwise it is subtraction (`a - b`, `a-b`) (`Expression.elm:626-655`). `- x` (space after) at an operand position is a syntax error; `--x` is a comment; `(-x)` negates, `(-)` is subtraction, `(- x)` is an error (`Expression.elm:235-240,268-307`). Negation is not a fixity-table operator: it is `Src.Negate`, kept as `Can.Negate` (`compiler/src/Compiler/IR/Canonical.elm:206`).
- Operator lexing is maximal munch, so `a*-b` is the single unknown operator `*-` and `2^-1` uses `^-` (`Symbol.elm:12-16`). See C-SYN-3.
- Only the last operand of a chain may be `let`, `case`, `if` or a lambda (`Expression.elm:20-21,583,691-706`).

> **Note (2026-11-07):** where this survey says a file without a header is accepted, that is the parser only. Both eco and Elm 0.19.1 reject every header-less file under `make` with `MODULE NAME MISSING` (checked by compiling header-less `Main.elm` and other files with both). Rulings A16 and A30 were amended accordingly: every module has a header.

## Phrase Classes

### Phrase Classes

Notation: `[x]` optional, `x*` zero or more, `x+` one or more. "term" is the
atomic subclass of each phrase class (no unparenthesised application or operator).

#### Expressions

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| variable | `x`, `M.x`, `C`, `M.C` | unqualified lower must not be reserved; name must resolve (`NotFoundVar`, `AmbiguousVar`) | `Expression.elm:129-135`, `Variable.elm:315-349` |
| literals | Int, Float, Char, String | see Special Constants | `Expression.elm:84-116` |
| unit | `()` | no whitespace or comment inside | `Expression.elm:312-313` |
| parenthesised | `( e )` | | `Expression.elm:351-356` |
| tuple | `( e1 , e2 [, e3]* )` | parser accepts any n >= 2; canonicaliser rejects n > 3 (`TupleLargerThanThree`) | `Expression.elm:327-361`; `Canonicalize/Expression.elm:410-454` |
| operator value | `(op)` | op is a non-reserved operator, adjacent to both parens; must be in scope | `Expression.elm:232-241,265-310`; `Canonicalize/Expression.elm:231-238` |
| list | `[ ]`, `[ e1 (, ei)* ]` | | `Expression.elm:173-225` |
| record | `{ }`, `{ f1 = e1 (, fi = ei)* }` | duplicate field is `DuplicateField`; > 2047 fields is `TooLarge` (eco only) | `Expression.elm:368-436,474-504`; `Canonicalize/Expression.elm:384-401` |
| record update | `{ x \| f1 = e1 (, fi = ei)* }` | `x` is an unqualified lower variable (not `M.x`, not an upper name, not an expression); at least one field; duplicate field is `DuplicateField` | `Expression.elm:368-375,386-411`; `Canonicalize/Expression.elm:365-382`; `compiler/tests/Compiler/Parse/ExpressionTest.elm:74-94` |
| field access | `t.f`, chained `t.f.g` | no whitespace either side of `.`; `t` is a variable, a record/update, or a `(`-term (parens, tuple, unit, `(op)`) | `Expression.elm:12-13,62-81,138-166` |
| field accessor | `.f` | `f` lower, unqualified; not itself followed by access (C-SYN-4) | `Expression.elm:119-126` |
| application | `e0 a1 ... an` | each argument is a possibly negated term, indented; `let`/`case`/`if`/lambda as an argument need parentheses | `Expression.elm:591-614,759-770` |
| negation | `-t` | see Infix and Precedence | `Expression.elm:740-756` |
| operator chain | `e1 op1 e2 ... opn en` | ops must resolve; grouping by fixity; `Binop` error on non-associative mixes | `Expression.elm:615-737`; `Canonicalize/Expression.elm:682-860` |
| conditional | `if e then e (else if e then e)* else e` | `else` mandatory | `Expression.elm:777-933` |
| lambda | `\ p1 ... pn -> e`, n >= 1 | each `pi` is a pattern term; duplicate bound names `DuplicatePattern`; shadowing forbidden; > 2047 params `TooLarge` (eco only) | `Expression.elm:940-1015`; `Canonicalize/Expression.elm:254-289` |
| case | `case e of p1 -> e1 ... pn -> en`, n >= 1 | each `pi` is a full pattern; branches aligned | `Expression.elm:1022-1141`; `Canonicalize/Expression.elm:629` |
| let | `let d1 ... dn in e`, n >= 1 | definitions aligned; names distinct; shadowing forbidden; value cycles `RecursiveLet` | `Expression.elm:1148-1222`; `Canonicalize/Expression.elm:903-935,1365-1398` |
| GLSL | `[glsl\| ... \|]` | see GLSL shaders | `compiler/src/Compiler/Parse/Shader.elm:1-25` |

Term alternatives are tried in this order: variable, string, number, shader, list, record,
`(`-form, accessor, char (`Expression.elm:65-81`). Expression alternatives: `let`, `if`,
`case`, lambda, chain (`Expression.elm:520-553`).

#### Patterns

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| wildcard | `_` | not followed by an inner char (`_x` is `PWildcardNotVar`) | `Pattern.elm:139-175` |
| variable | `x` | binds `x`; not reserved | `Pattern.elm:85-86` |
| constructor | `C`, `M.C` (term); `C t1 ... tn` (pattern expression) | arguments are pattern terms; arity must match (`BadArity`); a record-alias constructor cannot be matched (`PatternHasRecordCtor`) | `Pattern.elm:87-106,457-516`; `compiler/src/Compiler/Canonicalize/Pattern.elm:266-297` |
| literal | Int (decimal or hex), Char, String (single- or multi-line) | Float is `PFloat`; no negative literal (no `-` alternative) | `Pattern.elm:15-17,107-131`; `test/elm-compile-errors/src/UnexpectedPatternFloatWithExponentTest.elm` |
| unit | `()`, `( )` | whitespace allowed inside (unlike expressions) | `Pattern.elm:243-263` |
| parenthesised / tuple | `( p )`, `( p1 , p2 [, p3]* )` | elements are full patterns; n > 3 `TupleLargerThanThree` | `Pattern.elm:248-299`; `Canonicalize/Pattern.elm:340-355` |
| list | `[ ]`, `[ p1 (, pi)* ]` | elements are full patterns | `Pattern.elm:306-350` |
| cons | `p1 :: p2` | right associative; operands are constructor applications or terms | `Pattern.elm:357-450` |
| alias | `p as x` | applies to the whole preceding pattern, including a `::` chain; nothing may follow `x` | `Pattern.elm:357-362,403-438` |
| record | `{ }`, `{ x1 (, xi)* }` | names fields and binds variables of the same names; no `{ f = p }` form | `Pattern.elm:182-236` |

- Position decides the size: function arguments, lambda arguments and `let` destructuring take a pattern term only; case branches and the elements inside `( )` and `[ ]` take full patterns (`Pattern.elm:6-13`, `Expression.elm:954-957,1081-1088,1352-1369`, `Declaration.elm:202-215`).
- Every bound name (variables, record-pattern fields, `as` names) must be distinct within one binding site, else `DuplicatePattern` with context lambda args, function args, case branch, let binding, destructuring (`Canonicalize/Pattern.elm:23-31,96-140`; `compiler/src/Compiler/Canonicalize/Error.elm:233-244`).
- `True`/`False` from `Basics` become `PBool` (`Canonicalize/Pattern.elm:14-17,277-291`).

#### Types

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| type variable | `a` | lower, not reserved | `Type.elm:91-96` |
| type constructor | `T`, `M.T` (term); `T t1 ... tn` (application) | arguments are type terms (`Maybe List a` gives `Maybe` two arguments); arity must match (`BadArity`) | `Type.elm:10-17,72-90,265-332`; `compiler/src/Compiler/Canonicalize/Type.elm:229` |
| unit | `()` | no whitespace inside | `Type.elm:99-101` |
| parenthesised / tuple | `( t )`, `( t1 , t2 [, t3]* )` | n > 3 `TupleLargerThanThree` | `Type.elm:28-31,98-111,339-390`; `Canonicalize/Type.elm:132` |
| record | `{ }`, `{ f1 : t1 (, fi : ti)* }` | duplicate field `DuplicateField`; > 2047 fields `TooLarge` (eco only) | `Type.elm:112-180,391-460`; `Canonicalize/Type.elm:136-152` |
| extensible record | `{ a \| f1 : t1 (, fi : ti)* }` | `a` is an unqualified lower variable; at least one field | `Type.elm:59-62,122-143` |
| function | `t1 -> t2` | right associative; left operand is an application or a term | `Type.elm:192-250` |

#### Declarations (let and top-level)

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| top-level value | `[doc] [x : t NEWLINE] x p1 ... pn = e` | `x` lower; `pi` pattern terms; annotation name repeated on a fresh line (`DeclDefNameMatch`); no top-level destructuring; no operator definitions; duplicate names `DuplicateDecl` (ports and effect names included); duplicate args `DuplicatePattern`; arg shadowing a top-level name `Shadowing`; zero-arg value cycles `RecursiveDecl`; > 2047 params `TooLarge` | `Declaration.elm:131-245`; `compiler/src/Compiler/Canonicalize/LocalEnvironment.elm:127-142`; `Canonicalize/Module.elm:311,340,371`; `Canonicalize/Module.elm:22-34,260` |
| let value | `[x : t] x p1 ... pn = e` | annotation and definition aligned, names equal; names distinct in one `let`; must not shadow any local or top-level name; recursion only among definitions with parameters | `Expression.elm:1229-1346`; `Canonicalize/Expression.elm:903-935,1371-1398` |
| let destructuring | `pterm = e` | pattern term only (`(Just x) = e`, `( a, b ) = e`, `_ = e`, even `5 = e` parse); exhaustiveness is checked later (UNSAFE PATTERN) | `Expression.elm:1349-1407`; `compiler/tests/SourceIR/PatternFailsCases.elm:276-530` |
| doc comment | `{-\| ... -}` before a top-level declaration | next token on a fresh line | `Declaration.elm:104-127` |
| custom type / alias / port / infix | see their subsections | | |

Alternatives at top level are tried in the order `type`, `port`, value (`Declaration.elm:86-99`);
in a `let`, named definition then destructuring (`Expression.elm:1232-1237`).

#### Module headers

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| plain | `module M exposing L` | header starts in column 1; may not declare ports (`UnexpectedPort`, or `NoPortsInPackage` in a package) | `Module.elm:724-758,346-370` |
| port module | `port module M exposing L` | refused in packages (`NoPortModulesInPackage`); must declare >= 1 port (`NoPorts`) | `Module.elm:760-779,371-388` |
| effect module | see Effect module headers | kernel projects only | `Module.elm:781-897` |
| none | (no header) | accepted; module gets no name, `exposing (..)`, and `Ports` effects exactly when it declares ports; no effect rule checked | `Module.elm:15-17,28-29,314-330` |
| module doc comment | `{-\| ... -}` on a fresh line after the header | optional | `Module.elm:552-590` |
| module body | header, imports, [kernel: infix decls], one or more declarations | at least one declaration; whole file consumed (`ModuleBadEnd`) | `Module.elm:186-235,505-514`; `Primitives.elm:356-398` |

#### Imports

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| import | `import M [as A] [exposing L]` | starts in column 1; `A` is a single upper identifier; `as` precedes `exposing`; ends at a fresh line; without `exposing` the list is empty | `Module.elm:1037-1172` |
| kernel import | `import Elm.Kernel.X` / `Eco.Kernel.X` | in a kernel project `as` is `KernelImportAlias`; outside one the module is not found | `Module.elm:239-273` |
| default imports | `Basics (..)`, `Debug`, `List ((::))`, `Maybe (Maybe(..))`, `Result (Result(..))`, `String (String)`, `Char (Char)`, `Tuple`, `Platform (Program)`, `Platform.Cmd as Cmd (Cmd)`, `Platform.Sub as Sub (Sub)` | prepended to every module except those of `elm/core` | `DefaultImports.elm:5-26,48-62`; `Module.elm:200-209` |
| exposing items | as Exposing lists | `T(..)` on an alias `ImportOpenAlias`; exposing a constructor by name `ImportCtorByName`; unknown item `ImportExposingNotFound` | `Environment/Foreign.elm:385-430` |

#### Exposing lists

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| open | `( .. )` | whitespace allowed around `..` | `Module.elm:1178-1200` |
| explicit | `( item (, item)* )` | at least one item | `Module.elm:1178-1237` |
| value item | `x` | | `Module.elm:1239-1253` |
| operator item | `(op)` | no whitespace inside; in a module export must be declared infix in that module | `Module.elm:1254-1262`; `Canonicalize/Module.elm:503-507` |
| type item | `T`, `T(..)` | whitespace allowed: `T (..)`, `T( .. )`; `Alias(..)` export is `ExportOpenAlias`; duplicate export `ExportDuplicate`; unknown `ExportNotFound` | `Module.elm:1263-1300`; `Canonicalize/Module.elm:457,476-520` |

#### Port declarations

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| port | `port x : t` | only in a `port module` (or a header-less file); not in packages; name in the value namespace (`DuplicateDecl`) | `Declaration.elm:418-455`; `Module.elm:346-388`; `LocalEnvironment.elm:145-168` |

The port-type shape checks (`PortTypeInvalid`, `PortPayloadInvalid`) need alias expansion and
are out of scope here (`Canonicalize/Error.elm:189-190,255-277`).

#### Type declarations (custom types)

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| custom type | `type T a1 ... an = C1 t* (\| Ci t*)*` | `T`, `Ci` unqualified upper; `ai` lower; >= 1 variant; constructor args are type terms; each `\|` indented; duplicate params `DuplicateUnionArg`; a variable used but not a param `TypeVarsUnboundInUnion` (unused params allowed); type name shared with aliases `DuplicateType`; constructor name unique across all unions and record aliases of the module `DuplicateCtor`; > 2040 ctor fields or a nullary ctor after index 1023 `TooLarge` (eco only) | `Declaration.elm:252-310,364-414`; `Type.elm:464-488`; `LocalEnvironment.elm:188-207,415-449,539-560,675-679`; `compiler/tests/SourceIR/CanonicalizeFailsCases.elm:141-162` |

#### Type aliases

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| alias | `type alias T a1 ... an = t` | duplicate params `DuplicateAliasArg`; params must be exactly the body's free variables, unused params included (`TypeVarsMessedUpInAlias`); recursive aliases `RecursiveAlias`; shares namespace with custom types | `Declaration.elm:255-290,314-360`; `LocalEnvironment.elm:451-495,280-300` |
| record constructor | an alias whose canonical body is a closed record also defines constructor `T` | see Rewrites | `LocalEnvironment.elm:578-628` |

#### Type annotations

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| top-level | `x : t` then, on a fresh line, `x ...` | the definition must follow (only comments between) and repeat the name | `Declaration.elm:131-182` |
| let | `x : t` then, aligned, `x ...` | same, aligned instead of fresh line | `Expression.elm:1264-1307` |
| more parameters than arrows | | `AnnotationTooShort`; needs alias expansion (`iteratedDealias`), so not purely syntactic | `Canonicalize/Expression.elm:1338-1360` |

#### Infix declarations

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| infix | `infix (left\|right\|non) d (op) = x` | kernel projects only; after imports, before all other declarations; `d` exactly one digit 0-9 (the next char is not examined); `(op)` adjacent parens; followed by a fresh line; duplicates not checked (C-SYN-11) | `Declaration.elm:458-540`; `Number.elm:540-570`; `Module.elm:212-216,537-549`; `Canonicalize/Module.elm:109-111` |

#### Effect module headers

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| effect module | `effect module M where { command = C } exposing L`, or `subscription = S`, or both in either order separated by `,` | kernel projects only (`NoEffectsOutsideKernel`); no ports (`UnexpectedPort`); every token indented; `command`/`subscription` become top-level names (`DuplicateDecl`); the named types and manager functions must exist (`EffectNotFound`, `EffectFunctionNotFound`) | `Module.elm:781-1029,390-399`; `LocalEnvironment.elm:145-168`; `Canonicalize/Error.elm:176-177` |

#### GLSL shaders

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| shader | `[glsl\|` text `\|]` | text ends at the first `\|]` (even inside a GLSL comment); text must parse as GLSL; inputs recorded are top-level single-name `attribute`/`uniform`/`varying` declarations of type `vec2 vec3 vec4 mat4 int float sampler2D bool`, others ignored | `Shader.elm:1-25,40-100` |

The native back end rejects shaders after type checking (`design_docs/elm-divergence.md:254-255`).

#### Rewrites

What the implementation changes before type checking. Everything not listed survives into the
canonical AST as its own node: list literals (`Can.List`), `if` with its `else if` list
(`Can.If`), negation (`Can.Negate`), accessor (`Can.Accessor`), access, update, tuples, unit,
shader, lambda with patterns, definitions with argument patterns
(`compiler/src/Compiler/IR/Canonical.elm:150-220`). There is no desugaring to `case`, to
cons cells, or to lambdas, and no fresh names are introduced.

| Construct | Rewrite (exact) | Phase | Needs types? Fresh names? | Cite |
|-----------|-----------------|-------|---------------------------|------|
| `else if` | chain flattened into one `Src.If` with a list of (condition, branch) pairs plus final else; not nested | parser | no / no | `Expression.elm:855-933` |
| parenthesised type without comments | returned as the inner type (no `TParens`) | parser | no / no | `Type.elm:28-31` |
| parentheses (expr, pattern, type) | dropped | canonicaliser | no / no | `Canonicalize/Expression.elm:436-437`; `Canonicalize/Pattern.elm:13-21`; `Canonicalize/Type.elm:76` |
| negative literal `-5` | `Negate (Int 5)`; no negative literal exists | parser | no / no | `Number.elm:13-14`; `Expression.elm:743-756` |
| pattern `a :: b :: c` | right-nested `PCons a (PCons b c)`; `as` wraps the folded whole | parser | no / no | `Pattern.elm:360-362,440-450` |
| string/char literal | kept in escaped form; bare `'` in a string becomes `\'`; bare `"` in a char becomes `\"`; raw LF/CR in `"""` become `\n`/`\r`; `\u{...}` becomes `\uXXXX` or a surrogate pair of them | parser | no / no | `String.elm:13-20` |
| operator chain | flat `Binops` regrouped into nested `Can.Binop op home name annotation left right` by fixity from imported interfaces | canonicaliser | no (fixity only) / no | `Canonicalize/Expression.elm:682-880`; `Canonical.elm:207` |
| `(op)` | `Can.VarOperator op home name annotation` | canonicaliser | no / no | `Canonicalize/Expression.elm:231-238`; `Canonical.elm:200` |
| upper-case variable | `VarCtor` (with constructor index) | canonicaliser | no / no | `Canonicalize/Expression.elm:202-217,1700-1735` |
| record alias name used as a value | `VarCtor Normal home T 0` whose type is the curried function over the fields in declaration order returning `T a1..an`; only when the alias body canonicalises to a closed `TRecord` (an alias of a record alias gets no constructor) | canonicaliser | no inference; uses the canonical alias body / no | `LocalEnvironment.elm:578-628`; `Canonical.elm:486-507`; `Canonicalize/Expression.elm:1720-1727`; `test/elm/src/TypeAliasCtorTest.elm`; `test/elm-bugs/src/CompilerIssue1822AliasOfRecordAliasConstructorTest.elm` |
| `True`/`False` patterns | `PBool` when the constructor is `Basics.Bool`'s | canonicaliser | no / no | `Canonicalize/Pattern.elm:14-17,285-286` |
| `Debug.x` | `VarDebug` carrying the current module's home | canonicaliser | no / no | `Canonicalize/Expression.elm:26-28,1608-1627` |
| `Elm.Kernel.X.f` in a kernel package | `VarKernel` without existence check | canonicaliser | no / no | `Canonicalize/Expression.elm:28-31` |
| `let` block | split into strongly connected components, nested `Let` / `LetRec` / `LetDestruct`, dependencies first; a destructuring's graph key is `Name.fromManyNames` of its names (a key, not a binder) | canonicaliser | no / no | `Canonicalize/Expression.elm:38-47,903-935` |
| top-level values | ordered into `Declare` / `DeclareRec` by dependency | canonicaliser | no / no | `Canonicalize/Module.elm:18-34` |
| annotated definition | argument patterns paired with the annotation's argument types | canonicaliser | dealiasing of the annotation / no | `Canonicalize/Expression.elm:1338-1360` |
| header-less module | name `Nothing`, `exposing (..)`, ports become effects | parser | no / no | `Module.elm:314-330` |
| import without `exposing` | empty explicit list | parser | no / no | `Module.elm:1056-1059,1071-1073` |
| default imports | prepended (not for `elm/core`) | parser | no / no | `Module.elm:200-209` |

### Syntactic Restrictions

| Restriction | Enforced in | Error | Cite |
|-------------|-------------|-------|------|
| Tab in whitespace or block comment | lexer (Space) | `HasTab` | `Space.elm:279-280,397-398` |
| Reserved word as unqualified lower name | parser | expectation error | `Variable.elm:99-100,336-338` |
| Number running into a name char; leading zeros; `1.`; `0X`; `_` in numbers | parser | `NumberEnd`, `NumberNoLeadingZero`, `NumberDot`, `NumberHexDigit` | `Number.elm:20-28`; `test/elm-compile-errors/src/ParseErrorNumberBadHexDigitTest.elm`, `ParseErrorNumberFractionThenLetterTest.elm` |
| Bad escapes; `\u` needs 4-6 hex digits, <= 10FFFF | parser | `EscapeUnknown`, `BadUnicodeFormat/Code/Length` | `String.elm:480-520`; `test/elm-compile-errors/src/ParseErrorStringEscapeTooFewDigitsTest.elm`, `ParseErrorStringEscapeUnclosedTest.elm` |
| Char literal holds exactly one code point | parser | `CharNotString` | `String.elm:63-66` |
| Float literal in a pattern | parser | `PFloat` (UNEXPECTED PATTERN) | `Pattern.elm:117-125` |
| `_name` pattern | parser | `PWildcardNotVar` | `Pattern.elm:141-167` |
| Operator is not exactly `.`, `\|`, `->`, `=`, `:` | parser | `OperatorReserved` etc. | `Symbol.elm:52-119` |
| Record update target is an unqualified lower variable; >= 1 field | parser | `RecordOpen`, field expected | `Expression.elm:368-411` |
| Extensible record has >= 1 field | parser | | `Type.elm:59-62` |
| Annotation followed by a definition of the same name (fresh line / aligned) | parser | `DeclDefNameRepeat`, `DeclDefNameMatch`, `DefNameMatch` | `Declaration.elm:163-164`; `Expression.elm:1286-1290` |
| Exposing list non-empty; module has >= 1 declaration; file fully consumed | parser | | `Module.elm:1178-1237,505-514` |
| `infix` only in kernel projects, before other declarations | parser | parse error | `Module.elm:212-216` |
| Effect module only in kernel projects; ports rules | parser (module check) | `NoEffectsOutsideKernel`, `UnexpectedPort`, `NoPorts`, `NoPortsInPackage`, `NoPortModulesInPackage` | `Module.elm:340-399` |
| Kernel import with `as` (kernel project) | parser (module check) | `KernelImportAlias` | `Module.elm:239-273` |
| Tuple (expr, pattern, type) has at most 3 elements | canonicaliser | `TupleLargerThanThree` (BAD TUPLE) | `Canonicalize/Expression.elm:443-454`; `Canonicalize/Pattern.elm:340-355`; `Canonicalize/Type.elm:132`; `test/elm-compile-errors/src/BadTupleATupleOfFourTest.elm` |
| Duplicate field in record literal, update, record type | canonicaliser | `DuplicateField` (NAME CLASH) | `Dups.elm:136-153`; `Canonicalize/Type.elm:150`; `test/elm-compile-errors/src/NameClashARecordFieldGivenTwiceTest.elm` |
| Duplicate name bound by one pattern site (args, lambda args, case branch, destructuring, as, record pattern) | canonicaliser | `DuplicatePattern` (NAME CLASH) | `Canonicalize/Pattern.elm:96-140`; `test/elm-compile-errors/src/NameClashTwoArgumentsOfOneNameTest.elm` |
| Duplicate names in one `let` | canonicaliser | `DuplicatePattern DPLetBinding` | `Canonicalize/Expression.elm:917`; `test/elm-compile-errors/src/NameClashTwoLetBindingsOfOneNameTest.elm` |
| Duplicate top-level value / port / effect name | canonicaliser | `DuplicateDecl` | `LocalEnvironment.elm:127-168` |
| Duplicate type name (unions and aliases share one namespace) | canonicaliser | `DuplicateType` | `LocalEnvironment.elm:188-207` |
| Duplicate constructor in the module (incl. across unions and record aliases) | canonicaliser | `DuplicateCtor` | `LocalEnvironment.elm:539-560` |
| Duplicate type parameters | canonicaliser | `DuplicateUnionArg`, `DuplicateAliasArg` | `LocalEnvironment.elm:433,468` |
| Union uses an undeclared type variable | canonicaliser | `TypeVarsUnboundInUnion` | `LocalEnvironment.elm:415-449` |
| Alias params differ from body free variables (unused or unbound) | canonicaliser | `TypeVarsMessedUpInAlias` | `LocalEnvironment.elm:451-495` |
| **No shadowing**: a new local (arg, lambda arg, pattern var, `as` name, let name) may not reuse a name bound locally or at top level (including later top-level names, ports); imported names may be shadowed | canonicaliser | `Shadowing` (SHADOWING) | `compiler/src/Compiler/Canonicalize/Environment.elm:270-320`; `CanonicalizeFailsCases.elm:205-265`; `test/elm-compile-errors/src/ShadowingAnArgumentShadowingATopLevelValueTest.elm`, `ShadowingShadowingInLambdaTest.elm` |
| Value cycle without parameters (top level / let) | canonicaliser | `RecursiveDecl` (CYCLIC DEFINITION) / `RecursiveLet` (CYCLIC VALUE) | `Canonicalize/Module.elm:22-34,260`; `Canonicalize/Expression.elm:1365-1398`; `test/elm-compile-errors/src/CyclicValueALetValueDefinedByItselfTest.elm` |
| Non-associative operator mix | canonicaliser | `Binop` | `Canonicalize/Expression.elm:776-780,846-860` |
| Constructor pattern arity | canonicaliser (needs constructor table, not types) | `BadArity PatternArity` | `Canonicalize/Pattern.elm:277-297` |
| Type application arity | canonicaliser (needs type table) | `BadArity TypeArity` | `Canonicalize/Type.elm:229` |
| Record-alias constructor in a pattern | canonicaliser | `PatternHasRecordCtor` | `Canonicalize/Pattern.elm:296-297` |
| Open alias in exposing (`Alias(..)`), exposing a constructor by name, duplicate export, missing export | canonicaliser | `ExportOpenAlias`, `ImportOpenAlias`, `ImportCtorByName`, `ExportDuplicate`, `ExportNotFound` | `Canonicalize/Module.elm:457,476-520`; `Environment/Foreign.elm:385-430` |
| eco-only size limits: > 2047 params per function or lambda, > 2047 params plus captures per closure, > 2047 record fields, > 2040 constructor fields, nullary constructor index > 1023 | canonicaliser | `TooLarge` | `Canonicalize/Expression.elm:50-57,1189-1232`; `compiler/src/Compiler/IR/Runtime/HeapLimits.elm:31-61`; `design_docs/elm-divergence.md:214-219` |

Not purely syntactic, noted for the boundary: exhaustiveness and redundancy (`Nitpick`,
`compiler/tests/SourceIR/PatternFailsCases.elm`), `AnnotationTooShort` and port-type shape
(need alias expansion), duplicate fields reached through record extension
(`test/elm-bugs/src/CompilerIssue1550RecordExtensionDuplicateFieldTest.elm`).

### Evidence

| Program | What it shows |
|---------|---------------|
| `test/elm-compile-errors/src/BadTupleATupleOfFourTest.elm` | `( 1, 2, 3, 4 )` rejected as BAD TUPLE (parses, rejected by canonicaliser) |
| `test/elm-compile-errors/src/ShadowingAnArgumentShadowingATopLevelValueTest.elm` | argument named like a top-level value is SHADOWING |
| `test/elm-compile-errors/src/ShadowingShadowingInLambdaTest.elm` | lambda arg shadowing an enclosing arg is SHADOWING |
| `compiler/tests/SourceIR/CanonicalizeFailsCases.elm:205-265` | shadowing in let, lambda, case pattern, let vs top-level, arg vs top-level |
| `test/elm-compile-errors/src/NameClashARecordFieldGivenTwiceTest.elm`, `NameClashTwoArgumentsOfOneNameTest.elm`, `NameClashTwoLetBindingsOfOneNameTest.elm` | the three duplicate-name forms are NAME CLASH |
| `compiler/tests/SourceIR/CanonicalizeFailsCases.elm:141-162` | duplicate constructor within one union and across two unions |
| `test/elm-compile-errors/src/WeirdElseBranchElseNotIndentedTest.elm` | `else` at the let-definition column is rejected (layout) |
| `test/elm-compile-errors/src/UnexpectedPatternFloatWithExponentTest.elm` | `1e3` in a pattern is UNEXPECTED PATTERN |
| `test/elm-compile-errors/src/UnknownOperatorAnUnknownOperatorTest.elm` | `<=>` is UNKNOWN OPERATOR (lexes as an operator, not in scope) |
| `test/elm-compile-errors/src/ParseErrorNumberBadHexDigitTest.elm`, `ParseErrorNumberFractionThenLetterTest.elm` | `0x1g`, `1.5a` rejected |
| `test/elm-compile-errors/src/ParseErrorStringEscapeTooFewDigitsTest.elm`, `ParseErrorStringEscapeUnclosedTest.elm` | `\u{41}`, `\u{12` rejected |
| `test/elm-compile-errors/src/ErrorMessagesIssue188TypeAnnotationJuxtapositionTest.elm` | `foo : () String Float` fails to parse (`()` is a term and cannot take arguments) |
| `test/elm-compile-errors/src/PortProblemDeclarationWithoutNameTest.elm` | bare `port` at end of file is PORT PROBLEM |
| `test/elm-compile-errors/src/ErrorMessagesIssue103ImportedModuleWithoutModuleLineTest.elm` | a header-less imported module is MODULE NAME MISSING (header-less files are only entry modules) |
| `test/elm-bug-fixes/src/ErrorMessagesIssue372EmptyRecordUpdateExtraCommaTest.elm` | `{ key \| }` rejected (update needs a field) |
| `test/elm-bug-fixes/src/ParseErrorCasePatternUnfinishedTest.elm` | unclosed `(` in a case pattern |
| `test/elm-bugs/src/CompilerIssue1947MultilineStringInLetBinopTest.elm` | `"""` closing in column 1 then `++` inside a let: rejected by Elm 0.19.1 (layout by token column); also pins that the first newline of `"""` is kept |
| `test/elm-bugs/src/CompilerIssue1246LargeIntLiteralTest.elm`, `test/eco-divergence/src/HexLiteralNegativeI64Test.elm` | Int literals wrap modulo 2^64 |
| `compiler/tests/Compiler/Parse/NumberTest.elm:56-190` | accepted and rejected number forms (`1_000`, `0b1010`, `0xDE_AD`, `0x`) |
| `compiler/tests/Compiler/Parse/StringTest.elm:45-100` | astral chars, `\u{10000}`, `'ab'` rejected |
| `compiler/tests/Compiler/Parse/ExpressionTest.elm:50-95` | record update target must be an unqualified lower name |
| `compiler/tests/Compiler/Parse/VariableNonAsciiTest.elm`, `VariableUnicodeExtraTest.elm` | non-ASCII identifier classes |
| `test/elm/src/IntNegateTest.elm` | `negate -5`: `-` after whitespace, before a term, is a negated argument |
| `test/elm/src/CaseAsPatternTest.elm`, `LetNumberAsPatternTest.elm` | `((x :: _) as whole)`, `(( a, _ ) as whole)` |
| `test/elm/src/TypeAliasCtorTest.elm` | record alias constructor takes fields in declaration order |
| `test/elm/src/AstralCharCasePatternTest.elm` | `'\u{1F600}'` and literal astral chars in patterns; hex Int literals |
| `test/elm/src/StringEscapesTest.elm` | `\n`, `\t`, `\"` in strings |
| `test/elm/src/*.elm` (passim) | many `_ = Debug.log ...` in one `let`: repeated wildcard destructurings are not duplicates |

## Static Semantics

Scope: scoping, canonicalisation, type inference and module-level static checks of Elm 0.19.1 as
implemented by the eco front end. Lexis and grammar, evaluation, and the Cmd/Sub/Task/port runtime
are surveyed elsewhere; the static checks on ports are here.

Background fact used throughout: eco's front end "is forked from Guida, which is a port of the
stock Elm compiler from Haskell to Elm", and keeps "Elm's grammar, scoping rules, type system and
error messages" (DD/theory/compiler/front-end.md:7). Where this survey does not flag a divergence,
Elm 0.19.1 is presumed to behave the same, but that presumption has not been checked against the
Haskell source unless stated.

### Sources

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

### Scoping and Recursion

#### Namespaces and environments

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

#### Shadowing

| Fact | Cite |
|---|---|
| Every local binder (function and lambda parameters, case-branch pattern variables, `let` names, record-pattern fields, `as` names) goes through `addLocals`. | C/Canonicalize/Environment.elm:272-295; C/Canonicalize/Module.elm:344, :375; C/Canonicalize/Expression.elm:917-921 |
| A new local whose name is already `Local` or `TopLevel` is a `Shadowing` error. | C/Canonicalize/Environment.elm:302-321 |
| A new local may shadow an imported (`Foreign`/`Foreigns`) value without error. | C/Canonicalize/Environment.elm:310-314 |
| Report title `SHADOWING`; message cites linters as the reason. | C/Canonicalize/Error.elm:1052-1066 |
| Shadowing does not apply to types, type variables or constructors (only `vars` are checked). | C/Canonicalize/Environment.elm:279-295 |

Evidence: CE/ShadowingAnArgumentShadowingATopLevelValueTest.elm, CE/ShadowingShadowingInLambdaTest.elm,
CT/SourceIR/CanonicalizeFailsCases.elm:222-261.

#### Duplicates

| Construct | Error | Cite |
|---|---|---|
| Two top-level values (or ports, or effect names) of one name | `DuplicateDecl` (`NAME CLASH`) | C/Canonicalize/LocalEnvironment.elm:131-142 |
| Two types (union or alias) of one name | `DuplicateType` | C/Canonicalize/LocalEnvironment.elm:188-207 |
| Two constructors of one name, across all unions and record-alias constructors of the module | `DuplicateCtor` | C/Canonicalize/LocalEnvironment.elm:539-553 |
| Duplicate field in a record literal, record update or record type | `DuplicateField` | C/Canonicalize/Expression.elm:373, :392; C/Canonicalize/Type.elm:143-152 |
| Duplicate alias / union type parameter | `DuplicateAliasArg` / `DuplicateUnionArg` | C/Canonicalize/LocalEnvironment.elm:433, :468 |
| A name bound twice in one pattern, one parameter list, or one `let` | `DuplicatePattern` (contexts: lambda args, function args, case branch, let binding, destructure) | C/Canonicalize/Error.elm:239-244; C/Canonicalize/Pattern.elm:96-135; C/Canonicalize/Expression.elm:917 |
| Name exported twice | `ExportDuplicate` (`REDUNDANT EXPORT`) | C/Canonicalize/Module.elm:457 |

#### Recursion and the cyclic-value check

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

### Types and Inference

#### Type language

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

#### Annotations, rigid and flexible variables

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

#### Let-polymorphism and generalisation

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

#### Occurs check

| Rule | Cite |
|---|---|
| Unification itself does not run an occurs check (except before accepting a `List`/tuple as comparable). | C/Type/Unify.elm:44-45, :806-823 |
| After a `let` body is solved, each name bound by that `let` is checked for an infinite type; a cycle gives `InfiniteType` (`INFINITE TYPE`). Top-level definitions are `let`s in the constraint tree, so they are checked too. | C/Type/Solve.elm:33-34, :375-379, :452-454, :532-555; C/Type/Error.elm:2840 |
| Occurs follows alias arguments only, not alias bodies. | C/Type/Occurs.elm:28-37 |

Evidence: CE/InfiniteTypeSelfAppliedArgumentOnBothSidesTest.elm, CT/SourceIR/TypeCheckFailsCases.elm:799-817, :1273-1283.

#### Expression typing summary (constraint generation)

| Form | Constraint | Cite |
|---|---|---|
| `if` | each condition `Bool`; all branches one type | C/Type/Constrain/Typed/Expression.elm:1265-1300, :1270 |
| `case` | subject type = every pattern's type; all branch bodies one type | C/Type/Constrain/Typed/Expression.elm:1741-1874 |
| list literal | all entries one type | C/Type/Constrain/Typed/Expression.elm:1904-1950 |
| operator `a op b` | operator's annotation instantiated (`CForeign`) | C/Type/Constrain/Typed/Expression.elm:424-425, :812-958 |
| call | function type unified with argument types; too many arguments is `TOO MANY ARGS` (`CallArity`) | C/Type/Constrain/Typed/Expression.elm:1007-1220; C/Type/Error.elm:1391-1436 |
| variable | local / top-level: instance of its scheme (`CLocal`); foreign, constructor, operator, Debug: instance of its annotation (`CForeign`) | C/Type/Constrain/Typed/Expression.elm:463-481 |
| kernel reference | annotation from `KernelIntrinsics` if it has a row; otherwise no constraint (kernel packages only) | C/Type/Constrain/Typed/Expression.elm:39-41, :469-475 |

### Constrained Type Variables

#### Naming

| Rule | Cite |
|---|---|
| A type variable is constrained by the _prefix_ of its name: `number*`, `comparable*`, `appendable*`, `compappend*` (`String.startsWith`). So `number1`, `comparable2` and also `numberOfThings`, `comparableKey` are constrained. | C/Core/Name.elm:196-223; C/Type/Type.elm:416-452 |
| Distinct names are distinct variables even with the same class (`comparable` vs `comparable2`). | CE/TypeMismatchDifferentlyNamedComparableVarsTest.elm |
| The same name applies to rigid (annotation) and flexible variables. | C/Type/Type.elm:420-437 |
| Class membership after solving is read from the solver root, not the name. | DD/theory/compiler/front-end.md:60 |

#### Which types satisfy each class (flexible variable meeting a structure)

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

#### Two flexible constrained variables (joins)

From C/Type/Unify.elm:651-701.

| meet | `number` | `comparable` | `appendable` | `compappend` |
|---|---|---|---|---|
| `number` | number | number | mismatch | mismatch |
| `comparable` | number | comparable | compappend | compappend |
| `appendable` | mismatch | compappend | appendable | compappend |
| `compappend` | mismatch | compappend | compappend | compappend |

A plain flexible variable takes the constrained content (C/Type/Unify.elm:535-570, :641-642).

#### Rigid constrained variables

A rigid constrained variable (from an annotation) accepts only: a flexible plain variable; a
flexible constrained variable of the same class; a flexible `comparable` if the rigid is `number`;
a flexible `comparable` or `appendable` if the rigid is `compappend` (C/Type/Unify.elm:704-711,
:575-610, :629-634). Everything else mismatches, including a concrete `Int` against a rigid
`number`, a rigid `comparable` used as `number`, and two different rigid variables.

Evidence: CE/TypeMismatchRigidComparableAsNumberTest.elm, CE/TypeMismatchRigidNumberAs*Test.elm (alias,
function, Maybe, record, rigid var, tuple, unit), CE/TypeMismatchRigidCompappendAsIntTest.elm,
CE/TypeMismatchRigidAppendableAddedTest.elm, CE/TypeMismatchCompappendAgainstARigidVarTest.elm.

#### Initial basis using classes

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

### Records and Rows

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

### Custom Types and Aliases

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

### Patterns, Exhaustiveness, Redundancy

#### Typing of patterns

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

#### Exhaustiveness and redundancy

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

### Equality and Comparison

| Rule | Cite |
|---|---|
| `(==)`, `(/=)` have type `a -> a -> Bool` with no class constraint: equality is statically allowed at every type, including functions, `Json.Encode.Value` and `Regex`. Only the two sides must have one type. | core/Basics.elm:325-350; CE/TypeMismatchFloatComparedForEqualityTest.elm |
| Elm documents that `==` on functions and JSON values "will crash if possible" at run time; eco instead returns `False` for distinct closures (runtime divergence, the type checker does not reject it). | core/Basics.elm:332-345; DD/elm-divergence.md:181-189 |
| `(<)`, `(>)`, `(<=)`, `(>=)`, `max`, `min`, `compare` require `comparable` (table above); `Bool`, unit, records, functions and custom types are rejected. | core/Basics.elm:367-418; CE/TypeMismatchBoolsComparedTest.elm, CE/TypeMismatchFunctionLeftOfGreaterThanTest.elm, CE/TypeMismatchRecordLeftOfAtMostTest.elm, CE/TypeMismatchUnitLeftOfAtLeastTest.elm |
| Tuples of comparables are comparable, of 2 or 3 components. | C/Type/Unify.elm:783-797; CE/TypeMismatchComparableAgainstATupleTest.elm |

### Modules

#### Header and effects kind

| Rule | Cite |
|---|---|
| Header forms: `module M exposing (...)`, `port module M exposing (...)`, `effect module M where { command = X, subscription = Y } exposing (...)`; a file with no header is accepted. | C/Parse/Module.elm:12-17 |
| Plain `module` may not declare ports (`UNEXPECTED PORTS`; in a package `PACKAGES CANNOT HAVE PORTS`). | C/Parse/Module.elm:24, :345-360; C/Parse/Error.elm:1032-1057, :1077-1086 |
| `port module` is refused in a package; elsewhere it must declare at least one port (`NO PORTS`). | C/Parse/Module.elm:25-26, :362-381; C/Parse/Error.elm:1059-1076, :1087-1108 |
| `effect module` only in a kernel project (author `elm`, `elm-explorations` or `eco`) and may not declare ports (`INVALID EFFECT MODULE`). | C/Parse/Module.elm:27-28, :383-392; C/Elm/Package.elm:155-160; C/Parse/Error.elm:1109-1124 |
| A file with no header is not checked: its ports, if any, become its effects. | C/Parse/Module.elm:29, :320-333 |
| Module name must match the file (`MODULE NAME MISMATCH`), and an imported module must have a header. | C/Parse/Error.elm:989-1031; CE/ErrorMessagesIssue103ImportedModuleWithoutModuleLineTest.elm |

#### Exposing lists (exports)

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

#### Imports

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

#### Module-level static checks summary

Canonicalisation order: imports, then local types, values, constructors, then top-level values,
effects, exports (C/Canonicalize/Module.elm:10-15, :113-139). Effect modules: must define
`init`, `onEffects`, `onSelfMsg`, plus `cmdMap` and/or `subMap`; each effect type must be a local
custom type (`EFFECT PROBLEM`) (C/Canonicalize/Effects.elm:16-20, :84-124, :217-251). Effect modules
are noted only; they are kernel-only.

### Ports (Static)

#### Shapes

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

#### Payload types (`checkPayload`)

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

### Main

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

### Static Errors Index

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

### Evidence

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

## Dynamic Semantics and Basic Operations

Scope: pure evaluation and the basic operations of the initial basis (arithmetic, comparison,
equality, Char, String basics, Bitwise). Cmd/Sub/Task/ports are covered elsewhere. Facts are
recorded for two implementations wherever they differ: **Elm-on-JS** (Elm 0.19.1 compiler plus
elm/core 1.0.5 JavaScript kernel) and **eco** (eco native output). eco's JavaScript output keeps
Elm-on-JS behaviour (eco/design_docs/float-semantics.md:10-11), so "eco" below always means the
native path.

### Sources

Path abbreviations used in every cite:

| Abbrev | Path |
|---|---|
| `eco/` | /home/rupert/sc/gitlab/eco-compiler/ |
| `core/` | /home/rupert/.eco/0.2.0/packages/elm/core/1.0.5/src/ (byte-identical to ~/.elm/0.19.1/packages/elm/core/1.0.5/src/: `diff -rq` empty) |
| `kjs/` | core/Elm/Kernel/ (Elm's JavaScript kernel) |
| `jsgen` | eco/compiler/src/Compiler/GenerateJs/Expression.elm (eco's port of Elm's JS generator; the erased path "stays identical to Elm's", eco/THEORY.md:35) |
| `tyopt` | eco/compiler/src/Compiler/LocalOpt/Typed/Expression.elm |
| `intr` | eco/compiler/src/Compiler/IR/Kernel/Intrinsics.elm |
| `arith` | eco/runtime/src/codegen/Passes/EcoToLLVMArith.cpp |
| `ecok/` | eco/elm-kernel-cpp/src/core/ |
| `strops` | eco/runtime/src/allocator/StringOps.hpp |
| `div` | eco/design_docs/elm-divergence.md |
| `fsem` | eco/design_docs/float-semantics.md |
| `ccase` | eco/design_docs/char-case-mapping.md |
| `dlog` | eco/design_docs/debug-log-ordering-policy.md |
| `vrep` | eco/design_docs/theory/value-representation.md |
| `clos` | eco/design_docs/theory/closures-and-calls.md |
| `T/` `TD/` `TC/` `TB/` | eco/test/elm/src/, eco/test/eco-divergence/src/, eco/test/elm-conformance/src/, eco/test/elm-bugs/src/ |

Test suite status: `T/` and `TC/` hold programs whose CHECK lines hold under both Elm-on-JS and
eco (div:27-28; `TC/` CHECKs are recorded from Elm on node, fsem:16-17). `TD/` CHECK lines are
eco's output, with Elm's output in `-- ELM:` lines (div:23-26). `TB/` (synced from
elm-test-suite) records known Elm 0.19.1 bugs: its CHECKs are the *desired* answer, it fails on Elm
0.19.1 and is **not run by eco's E2E harness** (commit 148adc96 message), so eco's result on a `TB/`
test is unverified.

Source-quality notes (the design notes are partly stale; where code and notes disagree the code
wins, eco/THEORY.md:43):
- div:50-58 (Int `^`, float-to-int TODOs), div:105-107 (String case mapping "keeps full mapping")
  and div:154-161 (compare on Float "proposed") are superseded by fsem:24-35, ccase:30-36 and the
  code cited below.
- div:149-150 and div:172 say equality never uses pointer identity; the code does (Equality, below).
- div:425-426 (Char predicates use eco Unicode tables) is wrong: `isUpper`, `isLower`, `isAlpha`,
  `isDigit`, `isOctDigit`, `isHexDigit` are Elm code over ASCII code ranges (core/Char.elm:82-194).

### Evaluation Strategy and Order

| Construct | Strategy | Elm-on-JS order | eco order | Tests | Cite |
|---|---|---|---|---|---|
| Application `f a b` | Call by value: function and arguments evaluated before the body | JS `A2(f, a, b)`: `f`, then `a`, `b` left to right | not pinned by any test | T/PartialApplicationTest:7-9 | kjs (F2/A2 helpers in Utils/JS prelude); clos:96-108 |
| `if c then t else e` | `c`, then only the chosen branch | same | same; no logging expression may be hoisted out of a branch | T/BoolShortCircuitTest:9-10 | dlog:31-35 |
| `case e of ...` | scrutinee once, then only the first matching branch | same | same | T/CaseOrderTest | eco/compiler/src/Compiler/GenerateMlir/Expr.elm:5762-5806 |
| `a && b`, `a \|\| b` (operator) | short-circuit: `a && b` = `if a then b else False`, `a \|\| b` = `if a then True else b` | JS `&&` `\|\|` | rewritten to `if` before codegen | T/BoolShortCircuitTest:9-10, T/BoolShortCircuitParserIdiomTest | jsgen:876-882; tyopt:509-516 |
| `(&&) a b` (prefix, saturated) | see C-DYN-17 | short-circuit (any saturated call of `Basics.and` becomes JS `&&`) | **strict**: only `Can.Binop` is rewritten; a `VarOperator` is an ordinary global, whose kernel intrinsic `eco.bool.and` has both operands evaluated | none | jsgen:682-690, 876-882; tyopt:450-455, 509-516; intr:213-215; arith:1084 |
| `(&&)`, `(\|\|)` as values | strict in both operands | `_Basics_and` gets evaluated arguments | `eco.bool.and` | none | kjs/Basics.js:62-63; intr:213-215 |
| `x \|> f`, `f <\| x` | identical to `f x` | rewritten to a call; JS then evaluates `f` before `x` | rewritten to a call | T/PipelineTest | jsgen:826-830, 963-975; tyopt:518-533 |
| `f << g`, `f >> g` | ordinary curried functions `composeL g f x = g (f x)` | not inlined | ordinary call | T/CompositionTest | core/Basics.elm:849, 860; jsgen:792-793 |
| `let` bindings | strict: every binding evaluated, even if unused; recursive functions not called until applied | bindings regrouped into strongly connected components, dependencies first (same front end); JS `var` per binding in that order | same regrouping; measured: named bindings before `_ =` bindings and not in source order among themselves; a run of `_ =` bindings is in source order | T/DebugLogOrderingTest:6-16, T/DebugLogNoDropTest:14 | eco/compiler/src/Compiler/Canonicalize/Expression.elm:39-47; dlog:18-22, 37-53 |
| Record literal `{ a = e1, b = e2 }` | each field once | field-name order: the canonical record is a Dict keyed by name, emitted as a JS object literal | layout order: unboxed (Int, Float, Char) fields first, then the rest, each group by name | none (T/DebugLogRecordTupleFieldTest is not discriminating) | eco/compiler/src/Compiler/IR/Canonical.elm:218; Optimized.elm:148; GenerateMlir/Expr.elm:528-542; vrep:19 |
| Tuple, list literal | each element once | left to right (JS literal) | not pinned (TC/ListLiteralDebugLogKindTest uses CHECK-DAG) | TC/ListLiteralDebugLogKindTest | vrep:17-18 |
| Top-level value (no parameters) | evaluated at most once in Elm-on-JS | once, at program start, in dependency order, before `main` runs; cyclic values through thunks | a thunk: literals folded at each use; boxed-ABI values memoised on first use; Int/Float/Char values recomputed at every use; a top-level value of function type re-runs its body per call | T/NonEntryMainEvaluatedOnceTest:8-15, TD/EtaExpandLogOrderTest:37-44 | eco/compiler/src/Compiler/GenerateJs/Generate.elm:358-395; eco/compiler/src/Compiler/GenerateMlir/ConstThunks.elm:3-8; eco/design_docs/theory/compiler/mlir-generation.md:112-137; GenerateMlir/Functions.elm:668 |
| `List.map f xs` (basis) | `f` applied once per element | last element first (`map` is `foldr`) | same, except eco may reorder when the callback is proven Debug-free | T/ListMapTemplateOrderTest:13-18 | core/List.elm:124-125, 177-204; dlog:66-80 |
| `List.map2`, `indexedMap` (basis) | `f` once per pair | first element first (kernel loop) | not pinned | none | core/List.elm:134-135, 437-439; kjs/List.js:37-44 |

Observability: Elm is pure, so evaluation order is visible only through `Debug.log` output, through
which of several failing or diverging subexpressions fires first, and through resource exhaustion.
eco states that within a let group the order is "unspecified-but-observable" and not a defect
(dlog:51-53). Under `--optimize` an optimiser may keep either of two failing occurrences (dlog:60-64).

No laziness anywhere: there are no lazy bindings, no call-by-need, and recursion through a
non-function value is accepted only when the self-reference sits inside a lambda
(T/PureRecursiveValueThunkTest:11, T/PureMutualRecursiveValueTest).

### Values

| Value | Meaning | Elm-on-JS representation | eco representation | Cite |
|---|---|---|---|---|
| Int | integer | JS number (IEEE double): see Arithmetic | i64, two's complement, unboxed | div:36-58; vrep:11 |
| Float | IEEE 754 binary64 | JS number | f64, unboxed | vrep:12; fsem:24-35 |
| Char | a character | JS string of 1 or 2 UTF-16 units (DEBUG: `String` object) | one code point 0..0x10FFFF in 32 bits | kjs/Utils.js:145-146; vrep:13, 29; ccase:30 |
| String | sequence of UTF-16 code units | JS string | one of six heap forms; length always in UTF-16 units | strops:1-27 |
| Bool | `type Bool = True \| False` | JS boolean | embedded constants 0x4/0x5 | core/Basics.elm:444; vrep:14, 56 |
| Order | `type Order = LT \| EQ \| GT` | DEBUG/PROD ctor objects; cmp uses -1/0/1 | null-cons words | core/Basics.elm:426; kjs/Utils.js:84-85; ecok/Utils.cpp:23-29 |
| `()` | unit | `0` (PROD) or `{ $: '#0' }` (DEBUG) | constant 0x6 | kjs/Utils.js:136-137; vrep:15 |
| Tuple (2, 3) | product | `{ a, b, c }` | Tuple2/Tuple3 heap object or SSA aggregate | kjs/Utils.js:139-143; vrep:18, 31 |
| List | finite cons list | `{ $, a, b }` cells | Cons cells or chunk views (not part of the value) | ecok/Utils.cpp:211-216 |
| Record | finite map from field names to values | JS object | Record, raw fields first, by name | vrep:19 |
| Custom type value | constructor tag plus fields | `{ $: tag, a, b, ... }` | Custom heap object; nullary ctor embedded | vrep:20-21 |
| Function | closure | JS function (F2..F9 wrappers for arity) | heap Closure with stage arity and captures | clos:18-46 |

### Application and Closures

| Aspect | Semantics | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Currying | every function of n parameters is a function of one parameter returning a function | `F2`..`F9` plus `A2`..`A9` | stages; "staging changes how many intermediate closures are built ... never the result" | T/FunctionChainedPartialApplicationTest, T/PartialAppChainTest | clos:7-9 |
| Partial application | builds a closure holding the given arguments; no body evaluation | `F_n` returns a curried function | `eco_pap_extend_l` copies, never mutates | T/PartialApplicationTest:7-9 | clos:100, 112 |
| Over-application | apply to the stage's arguments, then apply the result to the rest | `A2(f,a,b)` falls back to `f(a)(b)` | generic apply saturates then re-applies | T/CaseReturnFunctionTest, T/HigherOrderReturnLambdaBasedOnConditionTest | clos:96-110 |
| Captures | lexical scope, values captured at closure creation | JS closure over variables (see TCO bug) | captured values copied into the closure | T/ClosureCapture01Test..06 | clos:20, 58 |
| Constructors as functions | an n-ary constructor is an n-ary curried function | yes | yes | T/LssGapCtorAsValue, T/PapEtaCtorProbe | |
| Record alias constructor | `Point 1 2` builds `{ x = 1, y = 2 }` in declared field order | yes | yes | T/TypeAliasCtorTest | |
| Record accessor `.f` | function `\r -> r.f` | yes | yes | T/RecordAccessorFunctionTest | |
| Record update `{ r \| f = e }` | new record; `r` unchanged | `_Utils_update` copies | fresh object | T/RecordUpdateTest:6-7 | kjs/Utils.js:151-166 |
| Self tail calls | constant stack | `while` loop reassigning parameters; closures created in the loop capture the mutable variable (bug: TB/CompilerIssue1813...:13 expects `[1,2,3]`, TB/CompilerIssue2268...:14-15 expects `[3,2,1]`) | loop; capture-in-loop not pinned by a native test | T/TailRecursiveSumTest | TB files cited |
| Closure identity | not part of Elm's meaning | each evaluation of a lambda makes a new JS function | a zero-capture closure is interned: one object per wrapper for every evaluation | TD/FunctionEqualityFalseTest:13-19 | clos:88 |

### Pattern Matching

| Pattern | Matches | Binds | Notes | Cite |
|---|---|---|---|---|
| `_` | anything | nothing | | |
| variable | anything | the value | | |
| `p as x` | what `p` matches | `x` plus `p`'s bindings | | T/CaseAsPatternTest |
| `()` | unit | nothing | | |
| Int literal (incl. negative, hex) | Int equality | nothing | | T/CaseIntTest |
| Char literal | Elm-on-JS: JS string equality; eco: code-point equality | nothing | eco rejects at compile time a Char pattern that is not one code point (compiler crash path) | eco/compiler/src/Compiler/GenerateMlir/Patterns.elm:988-997; T/CaseCharTest, T/AstralCharCasePatternTest |
| String literal | String equality (UTF-16 units) | nothing | | T/CaseStringTest, T/CaseStringEmptyPatternTest |
| `( p1, p2 )`, `( p1, p2, p3 )` | componentwise | union | | T/CaseTupleTest |
| `[]`, `p :: ps`, `[ p1, ..., pn ]` | list shape | union | | T/CaseListConsTest |
| `{ f1, f2 }` | any record with these fields | the named fields | | T/LetDestructRecordTest |
| `C p1 ... pn` | value with tag `C` and matching fields | union | | T/CaseCustomTypeTest |

- Order: branches are tried in source order (first match wins); the decision-tree compilation order
  is not observable because tests are pure.
- No residual failure: incomplete `case`, and refutable patterns in `let`, lambda and function
  parameters, are rejected statically (static survey); eco's decision tree always ends in a
  fallback edge (eco/compiler/src/Compiler/GenerateMlir/Expr.elm:5751-5806), and the Elm-on-JS
  generator emits a default branch. Neither emits a "no match" crash.

### Let and Recursion

| Aspect | Semantics | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Simple binding | evaluate once, bind | JS `var` | SSA value | T/LetBasicTest | |
| Destructuring `( a, b ) = e` | evaluate `e` once, match (irrefutable) | `Opt.Destruct` paths | same | T/LetDestructuringTest | Canonicalize/Expression.elm:41-43 |
| Recursive function | members of an SCC; every member must have parameters | `var` function | `eco.papCreateGroup` allocates the group together | T/LetRecClosureTest, T/LetMutualRecursionBetweenLocalsTest | Canonicalize/Expression.elm:44-47; clos:62, 90 |
| Recursive value | rejected statically unless the self-reference is under a lambda | | | T/PureRecursiveValueThunkTest:11 | Canonicalize/Expression.elm:45-47 |
| Shadowing | not allowed (static) | | | | |
| Top-level value timing | see Evaluation Strategy | eager at init | lazy, memoised or per-use | TD/EtaExpandLogOrderTest:37-44 | mlir-generation.md:116-137 |
| Top-level cyclic value that needs itself while computed | divergence | recursion without end; DEBUG wraps the error as "Some top-level definitions from `M` are causing infinite recursion" | thunk recursion: stack overflow (not tested) | none | eco/compiler/src/Compiler/GenerateJs/Generate.elm:362-395 |

### Equality

`==` and `/=` have type `a -> a -> Bool` (core/Basics.elm:75-76, 349-359); `/=` is `not (==)` in
both implementations (kjs/Utils.js:78; ecok/Utils.cpp:756-758; arith:871 `une` for Float).

| Value kind | Meaning | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Int | numeric | `===`; `-0 === 0` | `icmp eq` | T/EqualityTest | arith:855; intr:344-348 |
| Float | IEEE: NaN unequal to all, `-0 == 0` | `===` (IEEE) except `x == 0` with an Int-literal `0` compiles to `!x`, so `nan == 0` is True and `nan /= 0` False | `oeq` / `une`, every path | T/FloatNegativeZeroTest:6-8, TC/FloatEdgeTest:26-28, TB/CoreIssue1115NanEqualsLiteralZeroTest | jsgen:1079-1102, 1118-1141; arith:855-885; fsem:26 |
| Char | same character | JS string equality (multi-unit Chars from case mapping are possible) | code-point equality | TD/CharAstralRoundTripTest:15-23 | ccase:33 |
| String | same UTF-16 unit sequence | JS `===` | unit-by-unit over any of six forms | T/EqBoxedFastPathTest | strops:1620-1645 |
| Tuple, List, Record, Custom | structural, componentwise; lists also by length | `_Utils_eqHelp` walks object keys; deep values deferred past depth 100 | `eqHelp` by tag, slot kinds, depth bound 100 with deferral | TC/DeepEqualityTest:17-22, T/ContainerEqualityFloatTest:20-39, T/ContainerEqualityCustomFloatTest | kjs/Utils.js:15-75; ecok/Utils.cpp:434-446, 502-697 |
| Same object on both sides | (not defined by Elm's prose) | `x === y` returns True before looking inside | `a == b` returns True before looking inside, in the kernel and in the inline fast path | TB/CompilerIssue2362NanTupleEqualityTest:13-15 (desired: `p == p` False), TB/CoreIssue988NanContainerSelfEqualityTest:17-24 | kjs/Utils.js:29-32; ecok/Utils.cpp:503; eco/runtime/src/codegen/EcoBackend.cpp:2216-2236 |
| Dict, Set | same key/value pairs in key order, whatever the tree shape | converted with `Dict.toList` then compared | `dictEq` walks both trees in order, ignoring colour | TC/DeepEqualityTest:22 | kjs/Utils.js:46-65; ecok/Utils.cpp:625-632, 699-754 |
| Array | same elements | structural on the internal tree (canonical for a given length) | element by element | none | ecok/Utils.cpp:658-675 |
| Function | Elm prose: not comparable | crash 5 "Trying to use `(==)` on functions" unless the same JS object | True iff same closure object, else False, at any depth | TD/FunctionEqualityFalseTest:13-19 | kjs/Utils.js:34-37; kjs/Debug.js:262-263; ecok/Utils.cpp:691-692; div:181-189 |
| Bytes | same bytes | n/a here | `memcmp` | | ecok/Utils.cpp:515-521 |
| Regex, Json values | see other parts | | | | div:362-372 |

### Comparison and Order

`compare : comparable -> comparable -> Order`; `<`, `>`, `<=`, `>=` on `comparable`
(core/Basics.elm:77-80, 368-420). Comparable types: Int, Float, Char, String, and lists and tuples
of comparables (core/Basics.elm:411-414). `min x y = if lt x y then x else y`, `max x y = if gt x y
then x else y` (core/Basics.elm:396-407).

| Type | Order | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|
| Int | numeric | JS `<` or `_Utils_cmp` | signed i64 compare | T/IntCompareTest, T/CompareIntTest | arith:1351 area (int cmp_order); kjs/Utils.js:89-92 |
| Float, `<` `<=` `>` `>=` | IEEE ordered predicates | raw JS operator when either operand is a literal, else `_Utils_cmp(a,b) op 0`, which treats NaN as GT: `one > nan` True, `nan >= nan` True | IEEE on every path (`olt` etc.) | TD/FloatNaNOrderTest:13-64, TB/CoreIssue1050NanGreaterThanNanTest | jsgen:925-934, 940-965; kjs/Utils.js:91; arith:253-312 (float cmp); ecok/Utils.cpp:769-790; fsem:27 |
| Float, `compare` | eco: total order, NaN = NaN > every number, -0 = +0 | `_Utils_cmp`: LT only if `a < b`, EQ if `===`, else GT (NaN always GT; not antisymmetric) | total order | TD/FloatIeeeSemanticsTest:40-52, TD/FloatDivergenceTest:11-24 | kjs/Utils.js:91; arith:1346-1380; ecok/Utils.hpp:82-89; fsem:28 |
| Float inside tuples and lists, `<` etc. | eco: lexicographic by `compare`'s total order | `_Utils_cmp` | total order, so `nan < 1` is False but `( nan, 0 ) < ( 1, 0 )` is also False and `[ nan ] > [ 1 ]` True | TD/FloatIeeeSemanticsTest:53-58 | fsem:29 |
| Char | eco: code point; Elm: UTF-16 string order | JS string `<` | unsigned code point compare | T/CompareCharTest, TD/CharAstralRoundTripTest:22-23 | arith:1177; ecok/Utils.cpp:330-336; vrep:29 |
| String | lexicographic over UTF-16 code units, prefix first | JS string `<` | same, by units | T/CompareStringTest | strops:1647-1660 |
| List | lexicographic, shorter prefix first | cons walk | same | T/CompareEmptyListTest, T/OrderingEmptyListTest | kjs/Utils.js:117-119; ecok/Utils.cpp:374-403 |
| Tuple | lexicographic over components | `a`, `b`, `c` | same | T/CompareTupleWithEmptyListTest | kjs/Utils.js:110-115; ecok/Utils.cpp:340-372 |
| `sort`, `Dict`, `Set` with NaN | needs a total order | inconsistent comparator, behaviour undefined | NaNs sort last and are one key; -0 and +0 are one key | TD/FloatIeeeSemanticsTest:59-65 | fsem:30, 53 |
| `min`/`max` at Float | see Arithmetic | elm/core body | IEEE 754-2019 minimum/maximum | TD/FloatIeeeSemanticsTest:66-84 | eco/compiler/src/Compiler/MonoOpt/FloatMinMax.elm:1-18 |

### Arithmetic

Notation: `trunc`, `floor`, `ceil` on reals; `wrap64(n)` = the unique m in [-2^63, 2^63) with
m = n mod 2^64; `ToInt32` = JS's conversion (truncate, then mod 2^32 into [-2^31, 2^31), NaN and
infinities to 0); `dbl(r)` = r rounded to the nearest double. Elm-on-JS Int results are doubles, so
any Int result above 2^53 is `dbl` of the exact value, and may be a fraction, NaN or an infinity.

| Operation | Type | Mathematical meaning | Edge cases | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|---|---|---|
| `a + b`, `a - b`, `a * b` | Int | exact sum, difference, product | overflow | `dbl` of exact result (53-bit precision, then Infinity) | `wrap64` of exact result | T/IntAddTest, T/IntMulTest | kjs/Basics.js:10-12; jsgen:843-850; arith:52-87; eco/runtime/src/allocator/IntArith.hpp:23-36 |
| `a + b`, `a - b`, `a * b` | Float | IEEE 754 round-to-nearest | NaN, ±Infinity, -0 | IEEE | IEEE (`addf` etc.) | T/FloatAddTest | arith:267-305 |
| `a / b` | Float | IEEE division | `x / 0` = ±Infinity, `0 / 0` = NaN, `1 / -0` = -Infinity | IEEE | IEEE | T/FloatDivTest, T/FloatNegativeZeroTest:6-8 | kjs/Basics.js:13; arith:309-316; fsem:35 |
| `a // b` | Int | `trunc(a / b)` | `b = 0` gives 0; `minInt // -1`; results outside ±2^31 | `ToInt32(a / b)`: `x // 0` is 0 (Infinity and NaN map to 0); any quotient outside ±2^31 wraps to 32 bits (e.g. `5000000000 // 1` is 705032704) | `trunc`, total: `x // 0` = 0, `x // -1` = `wrap64(-x)` so `minInt // -1` = minInt | T/IntDivTest:10-13, T/IntDivByZeroTest:6-7 | kjs/Basics.js:14; jsgen:855-856; arith:91-123; ecok/Basics.cpp:87-89 |
| `modBy m x` | Int | floored modulus: `x - m * floor(x / m)`, sign of `m` | `m = 0`; `m < 0`; result -0 | JS `%` then sign fix-up; `m = 0` crashes ("Cannot perform mod 0. Division by zero error."); `modBy 4 -4` is -0 | same formula; `m = 0` and `m = -1` give 0 | T/IntModByTest:13-17, TD/ModByZeroKernelPathTest:25-28, TD/IntNegativeZeroTest:14-21 | kjs/Basics.js:20-29; kjs/Debug.js:290-291; arith:125-167; ecok/Basics.cpp:91-102; core/Basics.elm:515-541 |
| `remainderBy d x` | Int | truncated remainder `x - d * trunc(x / d)`, sign of `x` | `d = 0` | JS `x % d`; `d = 0` gives NaN in an Int; `remainderBy 4 -4` is -0 | `srem`; `d = 0` and `d = -1` give 0 | T/IntRemainderByTest:11-14, TD/RemainderByZeroTest:14-23 | kjs/Basics.js:17; jsgen:887-888; arith:169-197; ecok/Basics.cpp:104-106 |
| `b ^ e` | Int | `b` to the power `e` for `e >= 0`; `0 ^ 0 = 1` | `e < 0`; overflow | `Math.pow`: `2 ^ -1` is 0.5, `0 ^ -1` Infinity; overflow loses precision | square-and-multiply mod 2^64; any `e < 0` gives 0 (also `1 ^ -1` and `(-1) ^ -1`) | T/IntPowTest:6-9, TC/FloatEdgeTest:43, TB/CoreIssue960PowNegativeExponentIntTest:12 | kjs/Basics.js:15; arith:238-260; IntArith.hpp:38-54; div:38-39, 50-51 |
| `b ^ e` | Float | IEEE/libm `pow` | `pow(1, ±Infinity)`, `pow(1, NaN)`, `pow(-1, ±Infinity)` | ECMAScript `Math.pow`: NaN for these | LLVM `pow` (C99 Annex F: 1 for these); not pinned by a test | T/FloatPowTest:9-12 | kjs/Basics.js:15; arith:351-358; ecok/Basics.cpp:51-53 |
| `negate n` (and prefix `-`) | Int, Float | `0 - n` (Float: sign flip) | Int minInt; Int 0 | `-n`: `negate 0` is -0 | Int: `wrap64(0 - n)`, one zero; Float: `fneg` | T/IntNegateTest, T/FloatNegateTest:6-8, TD/IntNegativeZeroTest:16 | core/Basics.elm:567-568; jsgen:809-810; arith:199-211, 323-330 |
| `abs n` | Int, Float | `if n < 0 then -n else n` (elm/core body in both) | Int minInt; Float -0, NaN | `abs -0.0` is -0 | Int `abs minInt` = minInt; Float body kept, so `abs -0.0` = -0 | T/IntAbsTest, T/FloatAbsTest:6-8 | core/Basics.elm:581-582 |
| `toFloat n` | Int -> Float | the same number | n beyond 2^53 | identity | `sitofp`, round to nearest | T/ToFloatTest | kjs/Basics.js:47; jsgen:812-813; arith:573 |
| `round x` | Float -> Int | nearest integer, ties toward +Infinity (`round -2.5 = -2`) | NaN, ±Inf, out of Int range; -0 | `Math.round`: NaN or Infinity stored in an Int; `round -0.4` is -0 | `floor(x) + (x - floor(x) >= 0.5 ? 1 : 0)`, then saturate: NaN 0, beyond range the Int bound | T/FloatRoundTest:10-14, TD/FloatIeeeSemanticsTest:91-104, TD/FloatToIntRangeTest:10-19 | kjs/Basics.js:53; arith:586-635; ecok/Basics.cpp:116-137; fsem:33-34 |
| `floor x`, `ceiling x` | Float -> Int | `floor`, `ceil` | as `round`; `ceiling -0.5` | `Math.floor`/`Math.ceil`: NaN/Infinity in an Int; `ceiling -0.5` is -0 | `floor`/`ceil` then saturate | T/FloorToIntTest, T/CeilingToIntTest, TD/FloatIeeeSemanticsTest:97-103, 109-110 | kjs/Basics.js:51-52; ecok/Basics.cpp:123-129 |
| `truncate x` | Float -> Int | `trunc` | beyond ±2^31 | `ToInt32(x)`: `truncate 3e10` is -64771072, NaN and ±Infinity give 0 | saturating `trunc`: 30000000000; NaN 0; `truncate 1e20` maxInt | T/FloatTruncateTest, TD/FloatToIntRangeTest:14, TD/FloatDivergenceTest:17, 24 | kjs/Basics.js:48; jsgen:815-816; arith:681; ecok/Basics.cpp:139-141 |
| `sqrt`, `logBase b x`, `e`, `pi` | Float | sqrt; `log x / log b` (elm/core definition, not a primitive); constants | `sqrt -1` NaN; `logBase 10 1000` = 2.9999999999999996 in Elm | `Math.sqrt`, `Math.log`, `Math.E`, `Math.PI` | `llvm.sqrt`, `llvm.log`; `e`, `pi` folded constants | T/FloatSqrtTest, T/LetNumberLogBaseTest, TB/CoreIssue1048LogBaseTenTest:12-13 (desired 3) | core/Basics.elm:610-630; kjs/Basics.js:34-35, 54-55; intr:196-200, 293-297 |
| `sin cos tan acos asin atan atan2` | Float | the real functions, approximated | precision; NaN | `Math.*` (ECMAScript: implementation-approximated) | `sin`, `cos` LLVM intrinsics; `tan` lowered as `sin x / cos x`; `asin acos atan atan2` libm calls | T/FloatMathTanTest, T/FloatMathAtan2Test, T/FloatMathSin2PlusCos21Test | kjs/Basics.js:36-42; arith:379-516 |
| `isNaN`, `isInfinite` | Float -> Bool | classification | | `isNaN`, `=== ±Infinity` | `fcmp uno`; `abs x == inf` | T/FloatMathIsNaNTest, T/FloatInfinityTest | kjs/Basics.js:49, 56; arith:532-570 |
| `min`, `max` | comparable | elm/core: `if lt x y then x else y` / `if gt x y ...` | Float NaN, ±0 | elm/core body: `max 1 nan` = 1, `max nan 1` = NaN; `max -0 0` and `max 0 -0` depend on order | Float: IEEE 754-2019 maximum/minimum (NaN propagates, -0 < +0); Int and other types: elm/core body | T/IntMinMaxTest, T/FloatMinMaxTest, T/ComparableMinMaxTest, TD/FloatIeeeSemanticsTest:66-84 | core/Basics.elm:396-407; MonoOpt/FloatMinMax.elm:1-18, 70-95; arith:919-945 |
| `clamp lo hi x` | number | elm/core: `if x < lo then lo else if x > hi then hi else x` | NaN; `lo > hi` | elm/core body: `clamp 0 1 nan` = 1 | Float: `min (max x lo) hi`, so NaN in any argument gives NaN and `lo > hi` always gives `hi`; Int: elm/core body | TD/FloatNaNOrderTest:36, TD/FloatIeeeSemanticsTest:85-90, TB/CoreIssue1080ClampNanTest | core/Basics.elm:593-599; MonoOpt/FloatMinMax.elm:75-82 |
| `String.fromInt` | Int -> String | decimal | | `n + ''`: an Int holding 0.5 prints "0.5", 1e21 prints "1e+21" | exact decimal of i64 | T/StringFromNumberIntTest | kjs/String.js:270-273; strops:1272-1280 |
| `String.fromFloat`, `Debug.toString` Float | Float -> String | JS `Number.prototype.toString` | -0, NaN, Infinity, exponent form | native | shortest round-trip digits; fixed for 1e-6 <= abs < 1e21, else exponent; "0" for -0 | TC/DebugToStringTest:47-58, T/StringFromFloatJsFormatTest | kjs/String.js:270-273; strops:1288-1300 |
| `String.toInt` | String -> Maybe Int | optional `+`/`-` then one or more ASCII digits | overflow; long input; "-0" | digit loop in doubles: no overflow check, rounds above 2^53 (`"9007199254740991"` gives ...992), "-0" gives -0 | `Nothing` on 64-bit overflow or input over 64 units; exact otherwise | TC/StringKernelEdgeTest:20, TB/CoreIssue1142StringToIntMaxSafeTest:13-14 | kjs/String.js:278-299; strops:1186-1222; div:199-202 |
| `String.toFloat` | String -> Maybe Float | JS `Number(s)` minus forms with whitespace or `x`, `b`, `o` | "Infinity", overflow | `+s` after the regex filter | replicates: rejects whitespace and x/b/o, accepts signed "Infinity", `strtod` otherwise | none | kjs/String.js:302-312; strops:1224-1270 |
| Int literal | Int | its value | beyond 64 bits | Elm 0.19.1 reads literals into a 64-bit Int and wraps silently (TB/CompilerIssue1246LargeIntLiteralTest:13-14 desires no wrap); some hex literals rejected | 64-bit two's complement, hex at or above 2^63 negative | TD/HexLiteralNegativeI64Test:18-20 | (lexis: other part) |

Basic arithmetic is total in eco by design: "may return a wrong answer (wrapping, `x // 0 == 0`,
NaN), but it never returns a value of a different type and never raises a runtime error" (div:19-21).

### Bitwise

| Operation | Meaning | Elm-on-JS (32-bit) | eco (64-bit) | Tests | Cite |
|---|---|---|---|---|---|
| `and`, `or`, `xor` | bitwise on two's complement | operands `ToInt32`, result signed 32-bit | i64 | T/BitwiseAndTest, T/BitwiseOrTest, T/BitwiseXorTest | kjs/Bitwise.js:6-19; jsgen:758-767; ecok/Bitwise.cpp:5-15 |
| `complement` | `-n - 1` | `~ToInt32(n)` | `~n` on i64 | T/BitwiseComplementTest:6-7 | kjs/Bitwise.js:21-24; ecok/Bitwise.cpp:17 |
| `shiftLeftBy k n` | `n * 2^k` truncated to width | `ToInt32(n) << (k mod 32)`: `shiftLeftBy 32 1` = 1 | `n << (k mod 64)`: `shiftLeftBy 32 1` = 4294967296, `shiftLeftBy 63 1` = minInt | T/BitwiseShiftLeftTest, TD/BitwiseLargeShiftTest:7-8 | kjs/Bitwise.js:26-29; arith:1010-1030; ecok/Bitwise.cpp:21-23 |
| `shiftRightBy k n` | arithmetic shift | `>>`, count mod 32 | `ashr`, count mod 64 | T/BitwiseShiftRightTest:6-8 | kjs/Bitwise.js:31-34; arith:1032-1045 |
| `shiftRightZfBy k n` | logical shift | `>>>`: result is an *unsigned* 32-bit value (`shiftRightZfBy 0 -1` = 4294967295) | `lshr` on 64 bits reinterpreted signed (`shiftRightZfBy 0 -1` = -1) | T/BitwiseShiftRightZfTest | kjs/Bitwise.js:36-39; arith:1049-1060; ecok/Bitwise.cpp:30-32 |
| negative shift count | | `k & 31` | `k & 63` | none | as above |

### Char and String Basics

| Aspect | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|
| What a Char is | JS string of one code point, 1 or 2 UTF-16 units; case mapping can make it longer | exactly one code point in 0..0x10FFFF; a lone surrogate is a Char of its own unit value | TD/CharAstralRoundTripTest:15-23 | ccase:30; vrep:29 |
| `Char.toCode` | first code point; a lone high surrogate reads past its end and gives NaN | the code point | T/CharAstralCodeTest:12-17, TB/CoreIssue1150CharToCodeLoneSurrogateTest | kjs/Char.js:8-16 |
| `Char.fromCode n` | U+FFFD for n < 0 or n > 0x10FFFF, else the code point (surrogates pass through) | same | T/CharAstralCodeTest:16-17, TC/CharFromCodeWideIntTest:17-21 | kjs/Char.js:18-31; arith:1146-1167 |
| `Char.toUpper`/`toLower` | JS full case mapping: 103 code points give multi-code-point "Chars" (`toUpper 'ß'` = "SS") | Unicode 17.0 simple case mapping (`toUpper 'ß'` = 'ß'); `toLower 'İ'` = 'i' | TD/CharSimpleCaseTest, TD/CaseMappingDivergenceTest, TC/CharCaseOrdinaryTest | kjs/Char.js:33-41; ccase:34, 62-77 |
| `toLocaleUpper`/`Lower` | host locale (browser); on node equal to `toUpper` | equal to `toUpper`/`toLower` | TC/CharLocaleCaseTest | ccase:35, 86-88 |
| Char predicates | ASCII code ranges in Elm code (`isUpper` 0x41..0x5A etc.) | same Elm code | T/CharIsAlphaTest, T/CharIsDigitTest | core/Char.elm:82-194 |
| String unit of length and index | UTF-16 code units | UTF-16 code units in every form | T/StringAstralLengthTest:10-11, TC/NonBmpStringTest:13 | kjs/String.js:32-35; strops:15-17 |
| String to Chars (`toList`, `foldl`, `uncons`, `map`, `filter`, `any`, `all`) | combines a high surrogate with *any* next unit (foldr: low with any previous); lone surrogates loop until out of memory | combines only a valid high-low pair; lone surrogate is its own Char; `fromList (toList s) == s` | TC/NonBmpStringTest:13-27, TD/StringLoneSurrogateTest:15-23 | kjs/String.js:15-25, 105-122; vrep:29 |
| `String.reverse` | reverses code points, high surrogate glued to the next unit | reverses code points; valid pairs kept, lone surrogates moved as units | TC/NonBmpStringTest | kjs/String.js:81-103; strops:881-885 |
| `String.slice` | JS `slice` (negative counts from end), in units | units | TC/StringKernelEdgeTest | kjs/String.js:151-153 |
| `String.toUpper`/`toLower` | JS full mapping, Final_Sigma rule (`"ΟΔΟΣ"` to "οδος") | simple mapping per code point, no Final_Sigma ("οδοσ"); length preserved | TC/StringCaseTest | kjs/String.js:180-188; ccase:36, 75-77 |
| `++` | concatenation of units / lists | same (ropes internally) | T/StringConcatTest | kjs/Utils.js:173-193; ecok/Utils.cpp:794-816 |

### Remaining Runtime Failures

| Failure | Elm-on-JS | eco | Tests | Cite |
|---|---|---|---|---|
| `Debug.todo msg` | throws "TODO in module `M` on line N" plus message (crash 8; crash 9 inside a case branch) | prints "Debug.todo: msg" to stderr, exits status 1 | TD/DebugTodoPendingTimerTest:15-17 | kjs/Debug.js:26-41, 269-287; ecok/DebugExports.cpp:43-52 |
| `modBy 0 x` | throws "Cannot perform mod 0. Division by zero error." | 0 | TD/ModByZeroKernelPathTest:25-28 | kjs/Basics.js:23-24; div:66-73 |
| `==` on two different functions | throws crash 5 | False (True for the same object) | TD/FunctionEqualityFalseTest:13-19 | kjs/Utils.js:36; div:181-189 |
| Stack overflow (deep non-tail recursion) | catchable `RangeError` at roughly 10k frames | native stack, larger limit, hard crash (SIGSEGV); separate GC shadow-root stack aborts with "[eco] FATAL: GC shadow root stack overflow" | none (TB/CoreIssue1123NestedCmdBatchStackOverflowTest is a Cmd case) | div:435-440; eco/runtime/src/allocator/RootSet.cpp:36 |
| Out of memory | JS engine heap failure | "eco: out of memory: ..." then `abort()` | none | eco/runtime/src/allocator/ThreadLocalHeap.cpp:424-440 |
| Cyclic top-level value | DEBUG: "causing infinite recursion" error; PROD: stack overflow | stack overflow (thunk) | none | GenerateJs/Generate.elm:362-395 |
| Lone surrogate in `String.toList` etc. | loops until out of memory | well defined | TD/StringLoneSurrogateTest:14 | |
| Ill-typed program accepted by an unsound checker | Elm accepts some unannotated recursive groups and then fails at run time (`str.toUpperCase is not a function`) | rejected statically (`TYPE MISMATCH`) | eco/compiler/tests/SourceIR (TypeCheckFailsCases) | div:262-293 |
| Non-termination | loops | loops | T/BoolShortCircuitTest (used as a bomb) | |
| Pattern-match failure | none (static exhaustiveness) | none | | Pattern Matching above |
| Array index, `List.head` etc. | none: results are `Maybe` | none | | |

### Implementation-Dependent Points

| Point | Elm-on-JS | eco | Cite |
|---|---|---|---|
| Int width | IEEE double: exact to 2^53, then rounded, can reach ±Infinity | i64, wraps mod 2^64 | div:36-49; IntArith.hpp:9-12 |
| Int can hold a non-integer, NaN or Infinity | yes (`2 ^ -1`, `remainderBy 0`, `round (0/0)`, `toCode` of lone surrogate) | never | div:38-41; TD/RemainderByZeroTest:19-23 |
| Int negative zero | `negate 0`, `0 * -1`, `modBy 4 -4`, `remainderBy 4 -4`, `round -0.4`, `ceiling -0.5` are -0 (visible as `1 / toFloat n` = -Infinity) | one zero | TD/IntNegativeZeroTest:14-23; div:75-81 |
| `//` width | quotient through `ToInt32` (32-bit wrap) | full 64-bit truncation | kjs/Basics.js:14; jsgen:855-856; arith:91-123 |
| `x // 0`, `minInt // -1` | 0; n/a | 0; minInt | arith:91-123 |
| `modBy 0`, `remainderBy 0` | crash; NaN | 0; 0 | div:66-73 |
| Int `^` negative exponent | real-valued result in an Int | 0 | div:38-39; IntArith.hpp:38-44 |
| `truncate` | 32-bit (`ToInt32`) | saturating 64-bit | fsem:34, 55 |
| `round`/`floor`/`ceiling` of NaN, ±Inf, out of range | NaN or ±Infinity in an Int | NaN 0; Int bounds | fsem:34, 54 |
| Float `<` `>` `<=` `>=` with NaN | depends on whether an operand is a source literal | IEEE everywhere | fsem:39-47 |
| Float `==` against Int literal `0` | `!x`: `nan == 0` True | IEEE False | jsgen:1079-1102; TB/CoreIssue1115NanEqualsLiteralZeroTest |
| `compare` with NaN | NaN always GT (`compare 1 nan` = GT) | total order (`compare 1 nan` = LT, `compare nan nan` = EQ) | fsem:48; TD/FloatDivergenceTest:12-13, 19-20 |
| `max`/`min`/`clamp` at Float | argument-order dependent with NaN and ±0 | IEEE 754-2019 maximum/minimum; `clamp` = `min (max x lo) hi` | fsem:31-32, 49-52 |
| `clamp lo hi x` at Float with `lo > hi` | `lo` if `x < lo`, else `hi` if `x > hi`, else `x` | always `hi` (undocumented in eco notes) | core/Basics.elm:593-599; MonoOpt/FloatMinMax.elm:75-82 |
| `sort`/`Dict`/`Set` with NaN keys | undefined (inconsistent comparator) | well defined | fsem:53 |
| Float `pow` special cases | ECMAScript: `1 ^ (1/0)` NaN | C99: 1 (unpinned) | kjs/Basics.js:15; arith:351-358 |
| Transcendentals | engine's `Math.*` (implementation-approximated) | libm / LLVM intrinsics; `tan` as `sin/cos` | arith:405-418 |
| Equality on the same object | identity shortcut (True even holding NaN) | identity shortcut, kernel and inline | kjs/Utils.js:29-32; ecok/Utils.cpp:503; EcoBackend.cpp:2222 |
| Function equality | crash unless same object | identity; zero-capture closures interned | div:181-189; clos:88 |
| Char representation | 1-2 UTF-16 units, may become longer by case mapping | one code point | ccase:30, 47-56 |
| Char order | UTF-16 string order | code-point order (differs for U+E000..U+FFFF against astral; String order stays UTF-16, so Char order and String order disagree in eco) | vrep:29; ecok/Utils.cpp:330-336; strops:1647-1650 |
| Char/String case mapping | full mapping, engine Unicode version, Final_Sigma | simple mapping, Unicode 17.0 fixed | ccase:62-77, 92-98 |
| Lone surrogates | `toCode` NaN; `toList` loops | well defined | TD/StringLoneSurrogateTest:14 |
| Bitwise width | 32-bit, `>>>` unsigned | 64-bit, all signed, counts mod 64 | TD/BitwiseLargeShiftTest:6-8 |
| `String.toInt` | no overflow check, rounds above 2^53, "-0" gives -0 | `Nothing` on overflow or more than 64 units | strops:1186-1222 |
| `String.fromInt` of large Int | exponent form at 1e21 | always plain decimal | kjs/String.js:270-273 |
| Top-level value evaluation | once, eagerly at start | lazily; memoised only for boxed values; per use for Int/Float/Char; per call for function-typed | TD/EtaExpandLogOrderTest:37-44; mlir-generation.md:116-137 |
| Record field evaluation order | field-name order | unboxed fields first, then by name | GenerateMlir/Expr.elm:528-542 |
| `(&&) a b` prefix form | short-circuit | strict | jsgen:876-882; tyopt:450-455 |
| Closures made inside a self-tail-call loop | capture the loop's mutable variable | capture values (unpinned) | TB/CompilerIssue1813...:13 |
| Stack depth | about 10k frames, `RangeError` | native stack, SIGSEGV | div:435-440 |
| `Debug.*` under `--optimize` | compile error | allowed, output kept | div:191-197 |
| `Debug.todo` message | "TODO in module ..." | "Debug.todo: msg", exit 1 | TD/DebugTodoPendingTimerTest:15-17 |

### Evidence

| Test | Expression | CHECK (eco) | Elm-on-JS (`-- ELM:` or source) |
|---|---|---|---|
| T/IntDivTest:10-13 | `10 // 3`, `-10 // 3`, `10 // -3`, `-10 // -3` | 3, -3, -3, 3 | same |
| T/IntDivByZeroTest:6-7 | `10 // 0`, `-5 // 0` | 0, 0 | same |
| T/IntModByTest:13-17 | `modBy 4 7`, `modBy 4 -7`, `modBy 5 0` | 3, 1, 0 | same |
| T/IntRemainderByTest:11-14 | `remainderBy 4 7`, `4 -7`, `-4 7`, `-4 -7` | 3, -3, 3, -3 | same |
| T/IntPowTest:6-9 | `2^3`, `5^0`, `2^10`, `(-2)^3` | 8, 1, 1024, -8 | same |
| T/FloatPowTest:9-12 | `2.0 ^ -1.0` | 0.5 | same |
| T/FloatRoundTest:10-14 | `round 2.7, 2.3, -2.7, 2.5, 3.5` | 3, 2, -3, 3, 4 | same |
| TC/FloatEdgeTest:20-25 | `round` of 2.5, -2.5, 0.5, -0.5, 1.5, -1.5 | 3, -2, 1, 0, 2, -1 | same (recorded on node) |
| TC/FloatEdgeTest:26-28, 38-39 | `nan == nan`, `nan /= nan`, `Just nan == Just nan`, `[nan] /= [nan]` | False, True, False, True | same |
| TC/FloatEdgeTest:43 | `3 ^ 33` | 5559060566555523 | same |
| T/FloatNegativeZeroTest:6-8 | `-0 == 0.0`, `1/0`, `1/-0` | True, Infinity, -Infinity | same |
| TD/IntNegativeZeroTest:14-23 | `1 / toFloat (remainderBy 4 -4)` etc. | "0 Infinity" | "0 -Infinity" |
| TD/RemainderByZeroTest:14-23 | `remainderBy 0 7`, `+ 1` | 0, 1 | NaN, NaN |
| TD/ModByZeroKernelPathTest:25-28 | `modBy 0 5`, `List.map2 modBy [0,4] [9,-7]` | 0, [0,1] | crash |
| TD/FloatToIntRangeTest:10-19 | `round nan`, `round inf`, `truncate 3e10` | 0, 9223372036854775807, 30000000000 | NaN, Infinity, -64771072 |
| TD/FloatDivergenceTest:11-24 | `min nan 1`, `compare 1 nan`, `compare nan nan`, `truncate inf` | NaN, LT, EQ, 9223372036854775807 | 1, GT, GT, 0 |
| TD/FloatNaNOrderTest:13-64 | `one > nan` (variables), `max 1 nan`, `clamp 0 1 nan` | False, NaN, NaN | True, 1, 1 |
| TD/FloatIeeeSemanticsTest:53-65 | `compare (nan,1) (1,1)`, `(nan,0) == (nan,0)`, `sort [..nan..]`, `Dict` NaN keys | GT, False, "1,2,3,NaN,NaN", size 2 | (eco only) |
| TD/FloatIeeeSemanticsTest:73-76 | `max -0 0`, `max 0 -0`, `min 0 -0` | +0, +0, -0 | order dependent |
| TD/BitwiseLargeShiftTest:7-8 | `shiftLeftBy 32 1`, `shiftLeftBy 63 1` | 4294967296, -9223372036854775808 | 1, (32-bit) |
| T/BitwiseShiftRightTest:6-8 | `shiftRightBy 4 -1` | -1 | same |
| TD/FunctionEqualityFalseTest:13-19 | `f == f`, `(\x -> x) == (\x -> x + 0)`, `Just f == Just g` | True, False, False | True, crash, crash |
| T/ContainerEqualityFloatTest:20-39 | pairs, triples, lists with NaN, ±0, ±Inf | NaN containers unequal, -0 = 0 | same |
| TC/DeepEqualityTest:17-22 | values nested 120-500 deep | exact answers | same |
| T/CharAstralCodeTest:12-17 | `toCode` of astral; `fromCode -1`, `fromCode 0x110000` | 128512, 65533, 65533 | same |
| TD/CharAstralRoundTripTest:15-23 | `toCode (fromCode 55357)` and astral order | 55357 | NaN |
| TD/StringLoneSurrogateTest:15-23 | lone surrogates through `toList`, `foldr`, `uncons` | defined values | loops to OOM |
| TC/NonBmpStringTest:13-27 | `String.length "a😀b"`, `toList` | 4, [97,128512,98] | same |
| T/BoolShortCircuitTest:9-10 | `False && bomb`, `True \|\| bomb` | False, True | same |
| T/DebugLogOrderingTest:6-16 | five `_ = Debug.log` | source order | same |
| T/ListMapTemplateOrderTest:13-18 | `List.map (Debug.log "m")` on 5 elements | e, d, c, b, a | same |
| TD/EtaExpandLogOrderTest:37-44 | top-level `counted : St Int` with a `Debug.log` | `init` printed per call (3 times) | once |
| T/NonEntryMainEvaluatedOnceTest:8-15 | imported `main` used twice | logged once | same |
| TC/DebugToStringTest:24-82 | `Debug.toString` of each value form | e.g. `{ age = 3, name = "x" }`, `Just -1`, `1e+21`, `0` for -0 | same |
| TD/DebugTodoPendingTimerTest:15-17 | `Debug.todo "boom"` | "Debug.todo: boom", exit 1 | "TODO in module ..." |
| TB/CompilerIssue2362NanTupleEqualityTest:13-15 | `p == p` with `p = (nan, 1)` | desired False (eco unverified; code gives True) | True |
| TB/CompilerIssue2268TcoClosureCaptureTest:14-15 | lambdas made in a tail loop | desired `[3,2,1]` (eco unverified) | `[3,3,3]` |

## Programs, Platform, Effects and Ports

Scope: what a program is, `main`, flags, `Platform.Program` and the update loop, `Cmd`, `Sub`, `Task`,
`Process`, effect managers as far as they bear on program meaning, and ports at runtime. Static port
typing is recorded by another part; only the payload type grammar is repeated here, because the
runtime conversion is defined over it.

Path abbreviations used in cites:

| Abbrev | Path |
|---|---|
| `core/` | `/home/rupert/.eco/0.2.0/packages/elm/core/1.0.5/src/` (byte-identical to `~/.elm/0.19.1/packages/elm/core/1.0.5/src/`; `diff -rq` reports no difference) |
| `kjs/` | `/home/rupert/.elm/0.19.1/packages/elm/core/1.0.5/src/Elm/Kernel/` (Elm's JS kernel, reference behaviour) |
| `json-kjs/` | `/home/rupert/.elm/0.19.1/packages/elm/json/1.1.3/src/Elm/Kernel/Json.js` |
| `browser/` | `/home/rupert/.elm/0.19.1/packages/elm/browser/1.0.2/src/` |
| `elmc/` | `/home/rupert/sc/github/elm/compiler/` (reference Elm 0.19.1 Haskell compiler, commit 2f6dd29) |
| `eco/` | `/home/rupert/sc/gitlab/eco-compiler/` |
| `rt/` | `eco/runtime/src/platform/` |
| `kc/` | `eco/elm-kernel-cpp/src/` |
| `cs/` | `eco/compiler/src/Compiler/` |
| `sched.md` | `eco/design_docs/theory/runtime/scheduler-and-services.md` |
| `div.md` | `eco/design_docs/elm-divergence.md` |

### Sources

| Area | Files |
|---|---|
| Platform API (Elm) | `core/Platform.elm`, `core/Platform/Cmd.elm`, `core/Platform/Sub.elm`, `core/Task.elm`, `core/Process.elm` |
| Reference runtime (JS) | `kjs/Platform.js` (521 lines), `kjs/Scheduler.js` (195), `kjs/Process.js` (18), `kjs/Debug.js:233-292` (crash messages), `json-kjs` (decoders) |
| Browser program shapes | `browser/Browser.elm:63-219`, `browser/Elm/Kernel/Browser.js:29-140` |
| Reference compiler | `elmc/compiler/src/Optimize/Module.hs:245-272` (main), `elmc/compiler/src/Optimize/Port.hs` (codecs), `elmc/compiler/src/Canonicalize/Effects.hs:155-230` (payload check), `elmc/compiler/src/Generate/JavaScript/Expression.hs:1037-1049`, `elmc/compiler/src/Reporting/Error/Main.hs:20-110`, `elmc/terminal/src/Make.hs:95-233` |
| eco compiler | `cs/Canonicalize/Effects.elm:141-423`, `cs/LocalOpt/Erased/Port.elm` (JS codecs), `cs/LocalOpt/Typed/Port.elm` (native codecs), `cs/LocalOpt/Typed/Module.elm:180-200, 593-663`, `cs/LocalOpt/Error.elm:60-100`, `cs/PreMono/EntryPrep.elm`, `cs/GenerateMlir/Functions.elm:60-160, 375-400`, `cs/GenerateJs/Generate.elm:183-214`, `cs/GenerateJs/Expression.elm:1584-1595` |
| eco runtime | `rt/PlatformRuntime.cpp` (dispatch, initWorker, flags), `rt/Scheduler.cpp` (stepper, spawn, kill, run queue), `rt/PortRuntime.cpp` (ports, host API), `kc/EffectManagerRegistry.cpp`, `kc/core/TaskEffectManager.cpp`, `kc/core/PlatformExports.cpp`, `kc/core/ProcessExports.cpp`, `kc/json/JsonExports.cpp:1940-2100, 2636-2663` (payload checker), `kc/browser/BrowserExports.cpp`, `eco/runtime/src/embed/eco_embed.cpp`, `eco/runtime/src/embed/eco_node_addon.cpp` |
| Design notes | `sched.md` (main source for eco semantics), `div.md` sections 4.5, 4.6, 5.4, 5.10, 6; `eco/design_docs/debug-log-ordering-policy.md`; `eco/design_docs/invariants.csv:603-613` (PORT_001-011), `:703` (LIVE_004), `:706-708` (SCHED_001-002); `eco/docs/embedding.md`; `eco/docs/options.md:389-396`; `eco/THEORY.md:11, 78` |
| Test harness | `eco/test/ElmE2ETestBase.hpp:755-771, 931-1020` (echo bounce, `-- FLAGS:` directive), `eco/test/aot_port_host.cpp:1-80`, `eco/test/CheckPatterns.hpp:1-50` (CHECK semantics). Note: `eco/test/TestPort.hpp` is unrelated to Elm ports (it picks free TCP ports for server tests, `TestPort.hpp:1-16`). |
| Tests | `eco/test/elm/src/` (Port*, CovPort*, OutgoingPort*, Task*, Timer*, CmdBatchOrder*, Flags*, Entry*, NonEntryMain*), `eco/test/elm-core/src/Process*`, `TaskOnErrorCascadeTest`, `eco/test/elm-bugs/src/CoreIssue*`, `eco/test/eco-divergence/src/{FlagsBytesNative,PortBytes*}Test.elm` |

### Programs and main

A program is the module given to the compiler as root; its entry point is its top-level `main`.

| Fact | Cite |
|---|---|
| The optimizer recognises any top-level definition named `main` (`name /= Name._main` test); it does not consult the export list. | `elmc/compiler/src/Optimize/Module.hs:246-249`; eco `cs/LocalOpt/Typed/Module.elm:606-609` |
| `main`'s type, deep-dealiased, must be `VirtualDom.Node a` (Html, Svg) or `Platform.Program flags model msg`. Anything else (including any function type, so `main` with parameters) is `BAD MAIN TYPE`: "I only know how to handle Html, Svg, and Programs". | `elmc/compiler/src/Optimize/Module.hs:257-272`; `elmc/compiler/src/Reporting/Error/Main.hs:39-52`; eco `cs/LocalOpt/Typed/Module.elm:627-663` |
| `main` may not be recursive (`BAD MAIN`, "should be a boring value with no recursion"). | `elmc/compiler/src/Reporting/Error/Main.hs:54-66`; `div.md:206-208` |
| A `Node` main is `Static`; a `Program` main is `Dynamic msgType flagsDecoder`. | `elmc/compiler/src/Optimize/Module.hs:259-267`; `elmc/compiler/src/AST/Optimized.hs:144-145` |
| JS: a static main is rendered once by `_VirtualDom_init(main)(0)(0)`; a dynamic main is `main(flagsDecoder)(debugMetadata)` and the result is the `init` exported as `Elm.<Module>.init`. | `elmc/compiler/src/Generate/JavaScript/Expression.hs:1037-1049`; eco `cs/GenerateJs/Expression.elm:1584-1595`; `elmc/compiler/src/Generate/JavaScript.hs:504-560` |
| `elm make` to JS requires every root to have a `main` ("NO MAIN"); `--output=/dev/null` skips. | `elmc/terminal/src/Make.hs:106-113, 220-233`; `elmc/builder/src/Reporting/Exit.hs:1696-1708`; eco keeps `MakeNoMain`, `MakeNonMainFilesIntoJavaScript` (`eco/compiler/src/Builder/Reporting/Exit.elm:2058-2059`) |
| A `main` in an imported (non-root) module is an ordinary top-level value, evaluated once. | `eco/test/elm/src/NonEntryMainEvaluatedOnceTest.elm:1-15`; `EntryMainOfRootModuleTest.elm:1-14` |
| Native: the generated `main` is renamed `eco_main`; the C `main` calls it on a 64 MiB-stack thread and discards its value; the process exit code is what the program recorded, not `main`'s value. | `eco/runtime/src/codegen/eco_entry.cpp:3-14, 100-106, 158`; `sched.md:180` |
| Native: evaluating `Platform.worker impl` *runs* the program (`Elm_Kernel_Platform_worker` calls `initWorker`, which ends in the event loop). | `kc/core/PlatformExports.cpp:107-112`; `rt/PlatformRuntime.cpp:769-887` |
| Native: a static (`Html`) main is only evaluated; nothing renders. Many tests use `main = let _ = Debug.log ... in Html.text "done"`. | `eco/test/elm/src/CovPortIncomingUnitTest.elm:38-43` |
| Native: `Browser.element`, `document`, `application` return their record unchanged, so `init` never runs; `Browser.Navigation.*` ends the program with "... is not supported natively", exit 1; `Browser.Dom` tasks fail with `NotFound`. | `kc/browser/BrowserExports.cpp:3-10, 35-45` |
| Program shapes (`elm/browser`): `sandbox {init : model, view, update : msg -> model -> model} -> Program () model msg` (defined via `element` with `Cmd.none`/`Sub.none`); `element` and `document` take `{init : flags -> (model, Cmd msg), view, update, subscriptions}`; `application` adds `init : flags -> Url -> Navigation.Key -> ...`, `onUrlRequest`, `onUrlChange`. | `browser/Browser.elm:63-75, 104-111, 122-129, 207-219` |
| eco extension: a `Program` whose flags type is eco/system's `System.Environment` gets a built-in environment decoder; no payload check applies. | `cs/LocalOpt/Typed/Module.elm:634-647`; `eco/docs/getting-started.md:69-72` |
| One program per process natively (embedding: `eco_app_start` once; Node addon `init` once). JS allows several `init` calls, sharing the global `_Platform_effectsQueue`. | `eco/docs/options.md:393-394`; `kjs/Platform.js:238-239` |

### Flags

| Fact | Cite |
|---|---|
| Permitted flags types are exactly the port payload types (`checkPayload`), else `BAD FLAGS` with a per-reason message (extended record, function, type variable, unsupported type). | `elmc/compiler/src/Optimize/Module.hs:265-269`; `elmc/compiler/src/Reporting/Error/Main.hs:68-110`; eco `cs/LocalOpt/Typed/Module.elm:649-657` |
| Flags decoder = port decoder for the type, except flags of type `()` decode with `Json.Decode.succeed ()`, accepting any value (a `()` port accepts only `null`). | `elmc/compiler/src/Optimize/Port.hs:141-149`; eco `cs/LocalOpt/Erased/Port.elm:245-260` |
| JS: flags are `args.flags` of `Elm.M.init(args)`, or `undefined` if absent; decoded with `Json.run`; failure throws "Problem with the flags given to your Elm program on initialization." from `init` (crash 2). | `kjs/Platform.js:37-38`; `kjs/Debug.js:249-251` |
| eco native: absent flags decode as JSON `null`; a decode failure prints `eco: problem with the flags given to this program: <json>` and aborts. Flags given to a program with no decoder abort unless they are `null`. | `rt/PlatformRuntime.cpp:740-790` (esp. `:752`, `:778`, `:783`) |
| eco embedding: `eco_app_start(argc, argv, flags_json)` checks the flags against the compiled descriptor on the calling thread before starting; mismatch returns `ECO_APP_ERR_BAD_FLAGS` with the JS message, and the host may retry. Node addon: `JSON.stringify(opts.flags)`, `undefined` becomes `null`, BAD_FLAGS becomes a thrown error. | `eco/runtime/src/embed/eco_embed.cpp:267-295`; `eco_node_addon.cpp:744`; `eco/docs/options.md:393-394` |
| Standalone native executables parse no runtime flags; tests supply flags by a `-- FLAGS: {json}` directive read by the harness. | `eco/docs/options.md:395`; `eco/test/ElmE2ETestBase.hpp:944-1014` |
| Native only: `Bytes` anywhere in the flags type is `BAD FLAGS` ("wants `Bytes` in its flags"); the JS target accepts it. | `cs/LocalOpt/Typed/Module.elm:650-651`; `cs/LocalOpt/Error.elm:74-86`; `eco/test/eco-divergence/src/FlagsBytesNativeTest.elm:1-14` |

### The Update Loop

Reference algorithm (`kjs/Platform.js:35-55`), for `worker`, `element`, `document`, `application`:

1. Decode flags (above). 2. `initPair = init flags`; `model = initPair.a`. 3. Build the view stepper (worker: no-op, `Platform.js:26`). 4. Set up every effect manager and port (`_Platform_setupEffects`, `:82-101`). 5. `enqueueEffects(initPair.b, subscriptions model)` (`:52`). 6. Return `{ports}` to the host (`:54`).

Each message `msg` delivered to the program runs `sendToApp` (`:45-50`): `(model', cmd) = update msg model`; set `model := model'`; call the stepper (view); `enqueueEffects(cmd, subscriptions model')`.

| Property | Reference behaviour | eco | Cites |
|---|---|---|---|
| Message queue | None: a message is applied by direct call of `sendToApp` from whatever produced it (a task's `sendToApp` binding, an incoming port `send`, a DOM event). | Same direct call (`deliverToApp`, `sendToApp`), but host port sends are queued (below). | `kjs/Platform.js:153-160, 457-468`; `rt/PlatformRuntime.cpp:563-579` |
| Effects queue | `enqueueEffects` pushes `(cmdBag, subBag)` onto a FIFO; if already dispatching, returns; otherwise dispatches until empty. Prevents FX of a later update overtaking an earlier one (elm/core #980). | Same algorithm (`effectsQueue_`, `effectsActive_`). | `kjs/Platform.js:209-254`; `rt/PlatformRuntime.cpp:318-341` |
| When `subscriptions` runs | After `init` and after every `update`, on the new model, whether or not it changed. | Same (`initWorker`, `workerSendToAppEvaluator`). | `kjs/Platform.js:49, 52`; `rt/PlatformRuntime.cpp:698-726, 873-874` |
| Who receives effects | Every manager receives an `fx` message on every dispatch, with empty lists if it has no effects, so a manager can drop subscriptions. | Same: every manager's `onEffects` runs every dispatch. | `kjs/Platform.js:263-269`; `rt/PlatformRuntime.cpp:353-431`; `sched.md:150` |
| Dispatch timing | `rawSend` to each manager process; at top level (init) the scheduler runs to completion inside the send; inside a step the processes are only queued. | Each manager's `onEffects` task is spawned and the whole run queue drained before the next manager; dispatch completes inside the drain that ran the update (LIVE_004). | `kjs/Scheduler.js:88-92, 135-148`; `rt/PlatformRuntime.cpp:395-430`; `invariants.csv:703` |
| Manager order within a dispatch | `for (var home in managers)`: JS object key order, i.e. registration order of managers and ports in the generated code. | `std::unordered_map` iteration order (unspecified). | `kjs/Platform.js:87, 263`; `rt/PlatformRuntime.hpp:243, 266` |
| View | `element`/`document`: `view` drawn at init, then at most once per animation frame after updates (`_Browser_makeAnimator`). Not observable to Elm code. | Not run natively. | `browser/Elm/Kernel/Browser.js:110-136`; `kc/browser/BrowserExports.cpp:35-45` |
| Re-entrancy | An update can run inside another dispatch (e.g. a synchronous task); its effects are queued behind the current batch. | Same. | `kjs/Platform.js:211-227`; `sched.md:150` |

### Cmd

`type Cmd msg = Cmd` is opaque in Elm (`core/Platform/Cmd.elm:47`); the runtime representation is a bag tree.

| Construct | Elm signature (cite) | Runtime meaning | Cite |
|---|---|---|---|
| leaf | (internal) `command : MyCmd msg -> Cmd msg` generated for an effect module, `port p : a -> Cmd msg` | `{LEAF, home, value}`; `home` is the manager's module name or the bare port name | `kjs/Platform.js:176-186`; `kc/core/PlatformExports.cpp:114` |
| `Cmd.batch : List (Cmd msg) -> Cmd msg` | `core/Platform/Cmd.elm:66-68` | `{NODE, bags}` | `kjs/Platform.js:189-195`; `kc/core/PlatformExports.cpp` (`Elm_Kernel_Platform_batch`) |
| `Cmd.none = batch []` | `core/Platform/Cmd.elm:53-55` | empty node. Doc: `none`, `batch [none, none]`, `batch []` "all do the same thing" | `core/Platform/Cmd.elm:63-64` |
| `Cmd.map : (a -> msg) -> Cmd a -> Cmd msg` | `core/Platform/Cmd.elm:83-85` | `{MAP, func, bag}`; at gather time the chain of taggers (innermost first) is handed to the manager's `cmdMap` as one function | `kjs/Platform.js:198-205, 290-316`; `rt/PlatformRuntime.cpp:434-541` |
| Ordering doc | "Each is handed to the runtime at the same time ... there are no ordering guarantees about the results." | | `core/Platform/Cmd.elm:58-61` |
| Ordering as implemented | Gathering conses each leaf onto its manager's list, so a manager receives a batch's commands in **reverse** (flattened depth-first) order. Task manager spawns in list order, so `batch [perform a, perform b]` runs `b` first; ports deliver `batch [out 1, out 2]` as 2 then 1. | eco gathers in source order and then iterates last-first in the Task and port managers to reproduce it (PORT_005). | `kjs/Platform.js:319-328`; `kc/core/TaskEffectManager.cpp:62-68, 85-98`; `rt/PortRuntime.cpp:168-197`; test `CmdBatchOrderTest` |
| Deep nesting | JS gathers recursively: 100000 nested batches overflow the stack (elm/core #1123). | eco gathers with an explicit worklist. | `kjs/Platform.js:273-297`; `rt/PlatformRuntime.cpp:440-446`; `eco/test/elm-bugs/src/CoreIssue1123NestedCmdBatchStackOverflowTest.elm:1-13` |
| Leaf for unknown home | JS: impossible (every home is registered). | eco: silently dropped when no manager is registered for the home. | `rt/PlatformRuntime.cpp:471-473` |

### Sub

| Construct | Signature (cite) | Meaning | Cite |
|---|---|---|---|
| `Sub.batch`, `Sub.none = batch []`, `Sub.map` | `core/Platform/Sub.elm:54-56, 65-67, 82-84` | Same bag kernels as Cmd (`Elm.Kernel.Platform.batch`, `map`); gathered with `isCmd = false` | `kjs/Platform.js:189-205, 260-261` |
| Lifetime | A subscription is active exactly while it appears in the latest `subscriptions model`; managers receive the full current list every dispatch and diff it themselves (e.g. an incoming port just replaces its list). | | `kjs/Platform.js:449-453`; `rt/PortRuntime.cpp:225-243, 543-548` |
| `Sub.map` on an incoming port | `subMap f g = \v -> f (g v)` (composition). | eco same. | `kjs/Platform.js:430-436`; `rt/PortRuntime.cpp:13-15, 251-289` |
| `Cmd.map` on an outgoing port | Taggers dropped (`outgoingPortMap tagger value = value`): a port command produces no message. | eco same. | `kjs/Platform.js:360`; `rt/PortRuntime.cpp:245-249` |
| Several subscriptions to one incoming port | Each delivered value is passed to every tagger; list is reversed (consed), so taggers run last-first. | eco iterates last-first (PORT_005). | `kjs/Platform.js:464-467`; `rt/PortRuntime.cpp:706-714` |

### Task and Process

`Task x a` is `Platform.Task x a` (`core/Task.elm:59-60`, `core/Platform.elm:83`); it is a description, not a running computation (`core/Task.elm:56-57`). Running a Task value twice performs its effects twice (`sched.md:71`).

| Function | Type | Definition / semantics | Cite |
|---|---|---|---|
| `succeed` | `a -> Task x a` | kernel `{SUCCEED, value}` | `core/Task.elm:78-80`; `kjs/Scheduler.js:10-16` |
| `fail` | `x -> Task x a` | kernel `{FAIL, value}` | `core/Task.elm:92-94`; `kjs/Scheduler.js:18-24` |
| `andThen` | `(a -> Task x b) -> Task x a -> Task x b` | kernel node; continuation runs on success | `core/Task.elm:207-209`; `kjs/Scheduler.js:35-42` |
| `onError` | `(x -> Task y a) -> Task x a -> Task y a` | kernel node; handler runs on failure | `core/Task.elm:227-229`; `kjs/Scheduler.js:44-51` |
| `map`, `map2`..`map5` | | defined by `andThen`/`succeed`; **sequential**, left to right | `core/Task.elm:117-170` |
| `sequence` | `List (Task x a) -> Task x (List a)` | `List.foldr (map2 (::)) (succeed [])`; "run in order one-by-one and if any task fails the whole sequence fails" | `core/Task.elm:175-185` |
| `mapError` | `(x -> y) -> Task x a -> Task y a` | `onError (fail << convert)` | `core/Task.elm:246-249` |
| `perform` | `(a -> msg) -> Task Never a -> Cmd msg` | `command (Perform (map toMessage task))`; `Never` error type makes failure impossible | `core/Task.elm:282-284` |
| `attempt` | `(Result x a -> msg) -> Task x a -> Cmd msg` | `task |> andThen (succeed << f << Ok) |> onError (succeed << f << Err)` | `core/Task.elm:311-317` |
| `Process.spawn` | `Task x a -> Task y Id` | binding: `rawSpawn task`, succeed with the id; spawned process cannot receive messages | `core/Process.elm:70-84`; `kjs/Scheduler.js:81-86`; `rt/Scheduler.cpp:514-522` |
| `Process.sleep` | `Float -> Task x ()` | ms delay; JS `setTimeout(time)`, killable | `core/Process.elm:87-95`; `kjs/Process.js:9-18`; `kc/core/ProcessExports.cpp` (`sleepBindingBody`) |
| `Process.kill` | `Id -> Task x ()` | calls the parked binding's kill handle (aborts timers, HTTP), sets root to null | `core/Process.elm:98-105`; `kjs/Scheduler.js:102-115`; `rt/Scheduler.cpp:530-570` |

Scheduler semantics (reference `kjs/Scheduler.js:131-195`, eco `rt/Scheduler.cpp` `stepProcess`, `sched.md:44-71`):

| Property | Reference | eco | Cite |
|---|---|---|---|
| Model | A process = id, root task, stack of `(SUCCEED|FAIL, callback)` frames, mailbox. Single run queue, FIFO. | Same structure, immutable heap values, 64-bit ids, processes replaced not mutated. | `kjs/Scheduler.js:66-79, 118-132`; `sched.md:15-29, 75-81` |
| Stepping | `AND_THEN`/`ON_ERROR` push a frame; `SUCCEED`/`FAIL` pop frames until one of the same kind and apply it; `BINDING` runs its callback and parks; `RECEIVE` takes the oldest mailbox message or parks. | Same case analysis. | `kjs/Scheduler.js:151-195`; `sched.md:46-67` |
| Pre-emption | None: a process runs until it parks at a binding or an empty receive. (The `Process` doc says the runtime "will pause it at an `andThen`"; the stepper does not.) | None. | `core/Process.elm:53-57`; `kjs/Scheduler.js:153-193`; `sched.md:46-67` |
| Enqueue | `_Scheduler_enqueue` runs the queue to completion if not already running (synchronous). | Enqueue never runs; only explicit drains (event loop, dispatch) run processes. | `kjs/Scheduler.js:135-148`; `rt/Scheduler.cpp:576-585`; `sched.md:85-91` |
| Unhandled `fail` | Process ends silently (`if (!proc.__stack) return`). | Process ends; warning `[eco-runtime] unhandled top-level Task.fail ...` on stderr (SCHED_002). | `kjs/Scheduler.js:158-165`; `rt/Scheduler.cpp:993-1000`; `invariants.csv:708` |
| Kill finished / twice | `proc.__root` is null: reading `.$` throws TypeError (elm/core #955). | No-op; a process killing itself is not stopped. | `kjs/Scheduler.js:105`; `rt/Scheduler.cpp:556-566`; `elm-bugs/src/CoreIssue955KillProcessTwiceTest.elm:1-12` |
| `sleep 0`, negative | `setTimeout(0)`, about 1 ms on node. | Wakes at once (a yield). | `div.md:325-328, 486` |
| `sleep` NaN, infinite, > 2^31-1 ms | node `setTimeout` treats as about 1 ms. | 1 ms (copied from node). | `div.md:325-327`; `elm-core/src/ProcessSleepNonFiniteTest.elm:1-17` |
| Program liveness | Browser/node event loop. | Program runs while a hold exists (pending timer, HTTP, queued host send); exits when none remain and nothing is runnable. | `sched.md:3, 118-126` |
| Divergence statement | | "The order in which eco's scheduler runs Tasks, Cmds, subscriptions and `Process.sleep` callbacks may differ from Elm's JS scheduler ... TODO: list what eco guarantees." | `div.md:442-447` |

### Effect Managers

| Fact | Cite |
|---|---|
| An effect manager is an `effect module M where { command = C }` and/or `{ subscription = S }` defining `init : Task Never state`, `onEffects : Router msg self -> List (C msg) -> [List (S msg) ->] state -> Task Never state`, `onSelfMsg : Router msg self -> self -> state -> Task Never state`, `cmdMap`, `subMap`. | `core/Task.elm:1, 256-351`; `cs/Canonicalize/Effects.elm:16-20` |
| Runtime instance: a process looping `receive msg -> (SELF ? onSelfMsg : onEffects)`, threading the state. | `kjs/Platform.js:116-146` |
| `Router appMsg selfMsg`; `sendToApp : Router msg a -> msg -> Task x ()` delivers to `update`; `sendToSelf : Router a msg -> msg -> Task x ()` posts to the manager's own mailbox. Both are Tasks (act when run). | `core/Platform.elm:95-120`; `kjs/Platform.js:153-169`; `kc/core/PlatformExports.cpp` (`sendToApp`, `sendToSelf` bindings, "Until 2026-11-06 both sent at once") |
| Task manager: `onEffects` spawns one process per `Perform task`, each `task |> andThen (sendToApp router)`; state `()`; `onSelfMsg` ignores (`Never`). | `core/Task.elm:329-351`; eco C++ reimplementation `kc/core/TaskEffectManager.cpp:62-140, 216-238` |
| Managers in the elm/* packages: `Task` (core, command), `Time` (subscription), `Http` (command, subscription), `Random` (command), `Browser.Events`, `Browser.AnimationManager` (subscription). | `grep '^effect module'` over `~/.elm/0.19.1/packages`: `elm/time/1.0.0/src/Time.elm:1`, `elm/http/2.0.0/src/Http.elm:1`, `elm/random/1.0.0/src/Random.elm:1`, `elm/browser/1.0.2/src/Browser/Events.elm:1`, `.../AnimationManager.elm:1`, `core/Task.elm:1` |
| Ports are pseudo-managers keyed by the bare port name: outgoing has only `cmdMap`, incoming only `subMap`. | `kjs/Platform.js:348-357, 418-427`; `sched.md:160`; `invariants.csv:603` |
| eco native registers only Time, Http, Task (C++), eco/system managers (generated preamble), and ports. Commands for any other home (e.g. `Random.generate`, `Browser.Events`) find no manager and are dropped. | `kc/EffectManagerRegistry.cpp:13-22`; `sched.md:130-137`; `cs/GenerateMlir/Functions.elm:142-160, 383-394`; `rt/PlatformRuntime.cpp:471-473` |
| eco runs each manager's `init` at setup, then every handler synchronously; a handler task that parks would lose state (LIVE_004). | `rt/PlatformRuntime.cpp:198-312`; `sched.md:148-156, 215` |

### Ports at Runtime

Payload grammar (shared by ports and flags; checked statically): `P ::= Int | Float | Bool | String | Json.Encode.Value | () | Maybe P | List P | Array P | (P, P) | (P, P, P) | { l1 : P, ..., ln : P }` (closed record), after alias expansion. Everything else is rejected: `Char`, custom types (incl. `Dict`, `Set`, `Result`), type variables, functions, extensible records. eco adds `Bytes.Bytes`. Cites: `elmc/compiler/src/Canonicalize/Effects.hs:158-200`; `cs/Canonicalize/Effects.elm:255-347`.

Port shapes: outgoing `p : P -> Cmd msg` with `msg` a variable; incoming `p : (P -> msg) -> Sub msg` with the same variable (`cs/Canonicalize/Effects.elm:130-210`). Codecs are compiler-generated from the type (`elmc/compiler/src/Optimize/Port.hs`; `cs/LocalOpt/Erased/Port.elm` for JS, `cs/LocalOpt/Typed/Port.elm` for native).

Host interface:

| | Reference (JS) | eco native (embedding C API / Node addon) | Cites |
|---|---|---|---|
| Handle | `app.ports.p.subscribe(f)` / `unsubscribe(f)` for outgoing; `app.ports.p.send(v)` for incoming; only ports reachable from `main` exist. | `eco_port_subscribe(name, cb, user)`, `eco_port_send(name, json)` (0 queued, 1 not a port, 2 rejected + `eco_last_error()`); Node addon mirrors `app.ports`. Only ports reached during monomorphization are registered (PORT_003). | `kjs/Platform.js:388-410, 457-470`; `rt/PortRuntime.cpp:1182-1218`; `invariants.csv:605`; `eco/docs/embedding.md:29-42, 123-128` |
| Value form | JS values (objects, arrays, numbers...). | UTF-8 JSON text in both directions; Bytes ports carry raw bytes. | `rt/PortRuntime.cpp:3-15, 179-197`; `eco/docs/embedding.md:41-42` |
| Outgoing: when | The port manager's `init` is `Process.sleep 0`, and `onEffects` returns that sleep as the next state: the first delivery waits one timer tick (so the host can subscribe after `init` returns), and after each batch the manager sleeps 0 ms before taking the next batch. | Delivered synchronously inside dispatch of the update that issued it; the program waits while subscribers run. | `kjs/Platform.js:128-145, 370-386`; `rt/PortRuntime.cpp:179-197, 550-573`; `eco/docs/embedding.md:34-35` |
| Outgoing: no subscriber | Value is converted and discarded. | Buffered until the first subscriber, then handed to it in order; once a port has had a subscriber, values sent with none are dropped. | `kjs/Platform.js:375-383`; `rt/PortRuntime.cpp:550-566`; `rt/PortRuntime.hpp:20-31, 345-350` |
| Outgoing: order | Reverse of batch order within one dispatch (above); separate updates in update order. | Same within a batch (PORT_005). | `rt/PortRuntime.cpp:168-172`; test `CmdBatchOrderTest` |
| Incoming: when | `send` decodes, then calls `sendToApp` for each current subscription **synchronously**: `update` runs inside `send`. | Checked on the calling thread, then queued; delivered on the eco thread after the current run queue drains. A send from inside a subscriber is also queued. | `kjs/Platform.js:457-468`; `rt/PortRuntime.cpp:755-779, 605-718`; `sched.md:160-162, 174`; `eco/docs/embedding.md:36-37` |
| Incoming: no subscription | Decoded (and may throw), then delivered to nobody. | Delivered to no tagger. | `kjs/Platform.js:464`; `rt/PortRuntime.cpp:706-714` |
| Incoming mismatch | `send` throws `Error("Trying to send an unexpected type of value through port \`p\`:\n" + problem)` to the caller (crash 4); program state unaffected. | Embedding: `eco_port_send` returns 2 and `eco_last_error()` holds the same message; Node addon throws it. If no descriptor is known the eco thread decodes, and failure aborts: `eco ports: trying to send an unexpected value through port 'p': <json>`. | `kjs/Platform.js:459-461`; `kjs/Debug.js:257-261`; `rt/PortRuntime.cpp:755-779, 694-697, 338-343`; `eco_node_addon.cpp:450-459`; `invariants.csv:611` |
| Duplicate names | Second registration of a port name throws "There can only be one port named ..." at load (crash 3). | Abort: "duplicate port name" or "collides with an existing effect manager" (e.g. a port named `Task`). | `kjs/Platform.js:335-341`; `kjs/Debug.js:253-255`; `rt/PortRuntime.cpp:449-468`; `invariants.csv:603` |

Conversion table. "JSON" means the JSON value model (eco: JSON text; JS: the JS value before stringification). Incoming checks are the `Json.Decode` primitive rules (`json-kjs:45-79, 202-311`) and, in eco, the payload checker (`kc/json/JsonExports.cpp:1944-2060`) plus the eco-thread decoder.

| Elm type | Outgoing representation | Incoming accepted | On mismatch / edge cases | Cite |
|---|---|---|---|---|
| `Int` | JSON number (`Json.Encode.int`) | JS: any `number` with no fractional part that is finite (`1.0` ok; `1e300` ok, `-0` ok). eco: JSON integer or integral float in the signed 64-bit range (`1.0` gives 1, `-0.0` gives 0). | `1.5`, NaN, Infinity, strings: "Expecting an INT". eco: `9223372036854775808`, `1e300` rejected. Outgoing above 2^53: JS cannot hold it; eco writes it exactly. | `elmc/.../Port.hs:49`; `json-kjs:45-55`; `kc/json/JsonExports.cpp:1972, 2054-2059`; `div.md:330-338, 399-405` |
| `Float` | JSON number | any number | non-number rejected ("a FLOAT"). JS: NaN/Infinity pass both ways as JS numbers. eco: outgoing NaN/Infinity written as `null` (JSON.stringify rule); incoming NaN not expressible in JSON text; Node addon stringifies NaN to `null`, which a Float port rejects. | `json-kjs:63-67`; `kc/json/JsonExports.cpp:1973`; `div.md:399-402`; `eco_node_addon.cpp:425-441` |
| `Bool` | `true`/`false` | JSON boolean only | `0`, `"true"` rejected | `json-kjs:57-61`; `JsonExports.cpp:1974` |
| `String` | JSON string (eco: lone surrogates as `\udxxx`) | JSON string (JS also a `String` object) | other types rejected | `json-kjs:73-79`; `div.md:399-405` |
| `Char` | rejected statically | | | `cs/Canonicalize/Effects.elm:258-264` |
| `()` | `null` | `null` only (port); any value (flags) | JS `undefined` (e.g. `send()`) rejected | `elmc/.../Port.hs:40-41, 247-250`; `cs/LocalOpt/Erased/Port.elm:63-64, 391-396`; `JsonExports.cpp:1976` |
| `Maybe a` | `Nothing` as `null`; `Just v` as v's encoding (no wrapper) | `oneOf [null Nothing, map Just a]`: `null` first, so `Maybe (Maybe Int)` maps `null` to outer `Nothing`; `Just Nothing` is not representable | JS `undefined` and missing values are not `null`: rejected. | `cs/LocalOpt/Erased/Port.elm:127-151, 313-352`; `elmc/.../Port.hs:202-216`; `JsonExports.cpp:1977-1983` |
| `List a` | JSON array | JSON array (JS also `FileList`), each element decoded | non-array: "Expecting a LIST"; first bad element reported with its index | `json-kjs:214-219, 313-327, 329-332` |
| `Array a` | JSON array | JSON array | "Expecting an ARRAY" | `json-kjs:221-226` |
| `(a, b)`, `(a, b, c)` | JSON array of 2 or 3 elements in order | array decoded by `index 0..n-1`: arrays with **extra** elements accepted, extras ignored | too short: "a LONGER array"; non-array rejected | `cs/LocalOpt/Erased/Port.elm:180-238, 399-461`; `json-kjs:237-248`; `JsonExports.cpp:2000-2021` |
| closed record `{f : a, ...}` | JSON object, keys = field names, emitted in field-name (alphabetical) order | object with every field, decoded by `field`; **extra fields ignored** | missing field: "Expecting an OBJECT with a field named \`f\`"; fields are decoded last-alphabetical first, so with several missing the reported field is the alphabetically last (eco's checker walks in descriptor order) | `elmc/.../Port.hs:66-75`; `cs/LocalOpt/Erased/Port.elm:96-120, 465-523`; `json-kjs:228-235`; `JsonExports.cpp:2022-2040` |
| extensible record, type variable, function, custom type | rejected statically | | | `elmc/.../Effects.hs:176-200` |
| `Json.Encode.Value` | passed through (`identity`) | anything (`Json.Decode.value`) | never fails. JS: non-JSON JS values (functions, DOM nodes, `undefined`) pass through untouched; eco: only JSON text can cross | `elmc/.../Port.hs:53`; `json-kjs:69-71`; `JsonExports.cpp:1971` |
| `Bytes` (eco only) | JS target: `Uint8Array` over the bytes. Native: allowed only as the whole payload ("bytes port"), raw bytes, no copy for subscribers. | JS: `Uint8Array`, `ArrayBuffer`, `DataView`. Native: host buffer copied once. | JS: "Expecting a BYTES value (...)". Native: `Bytes` nested in another payload type is a compile error (`PORT ERROR`). Elm 0.19.1 rejects `Bytes` statically. | `cs/Canonicalize/Effects.elm:295-296`; `cs/GenerateJs/Generate.elm:190-214`; `cs/LocalOpt/Typed/Module.elm:180-200`; `sched.md:164-170`; `eco-divergence/src/PortBytesNestedNativeTest.elm:1-23` |

eco payload descriptor grammar (for host-side checks): `i f b s u v`, `M<x> L<x> A<x>`, `(<x><y>[<z>])`, `{<len>:<name><x>...}`; an unknown descriptor letter is accepted and left to the eco-thread decoder (`kc/json/JsonExports.cpp:1944-1956, 2041-2045`).

### Eco Differences

| # | Topic | Elm 0.19.1 (JS) | eco | Cite |
|---|---|---|---|---|
| E1 | Host value form | JS values | JSON text (and raw bytes) | `rt/PortRuntime.cpp:3-15` |
| E2 | Incoming delivery | synchronous inside `send` | queued, delivered after current work; fixes elm/core #1110, #1141, #1154 (reply lost because the subscription was not yet installed) | `sched.md:160-162, 174`; `elm-bugs/src/CoreIssue1110*`, `*1141*`, `*1154*` |
| E3 | Outgoing with no subscriber | dropped | buffered until first subscriber | `rt/PortRuntime.cpp:550-566` |
| E4 | Outgoing timing | asynchronous (port manager sleeps 0 between batches) | synchronous in dispatch | `kjs/Platform.js:370-386` |
| E5 | Bad incoming value | JS exception to caller | error code at call; abort if found on eco thread | `rt/PortRuntime.cpp:755-779, 694-697` |
| E6 | Absent flags | `undefined` | `null` | `kjs/Platform.js:37`; `rt/PlatformRuntime.cpp:776-778` |
| E7 | Bad flags | exception from `init` | abort (executable) or `ECO_APP_ERR_BAD_FLAGS` (embedding) | `rt/PlatformRuntime.cpp:750-756`; `eco_embed.cpp:274-282` |
| E8 | Int range at boundary | any integral double | signed 64-bit | `div.md:330-338` |
| E9 | NaN/Infinity Float out | JS NaN/Infinity | `null` | `div.md:399-402` |
| E10 | Bytes payloads | rejected | allowed (JS anywhere; native whole payload only; not in native flags) | `cs/Canonicalize/Effects.elm:260-262`; `cs/LocalOpt/Error.elm:74-86` |
| E11 | Manager order in dispatch | registration order | hash order | `rt/PlatformRuntime.hpp:243, 266` |
| E12 | Unhandled spawned failure | silent | stderr warning | `rt/Scheduler.cpp:993-1000` |
| E13 | Kill finished process | TypeError crash | no-op | `rt/Scheduler.cpp:556-566` |
| E14 | `Process.sleep 0`/negative | about 1 ms | immediate yield | `div.md:325-328` |
| E15 | Deep `Cmd.batch` | stack overflow | works | `rt/PlatformRuntime.cpp:440-446` |
| E16 | Native Browser programs and Elm-source managers | full | `init` never runs; `Random`, `Browser.Events` commands/subs dropped | `kc/browser/BrowserExports.cpp:35-45`; `kc/EffectManagerRegistry.cpp:13-22` |
| E17 | Environment flags | n/a | `Program System.Environment ...` gets a built-in decoder | `cs/LocalOpt/Typed/Module.elm:634-647` |
| E18 | Instances | many `init` calls per page | one program per process | `eco/docs/options.md:393-394` |
| E19 | `Debug.log` under `--optimize` | compile error | allowed natively, output kept | `div.md:190-196, 470`; `debug-log-ordering-policy.md:7-16` |

### Evidence

Reading rules. The Elm E2E hosts match `-- CHECK:` lines **unordered**: each positive pattern need only appear somewhere in the output (`eco/test/CheckPatterns.hpp:29-34`), so the order of CHECK lines is not evidence of ordering; only values that encode order (lists logged once) are. Port tests rely on the harness echo: every `echoOut` payload is sent back on `echoIn` (`ElmE2ETestBase.hpp:755-771, 931-937`; `aot_port_host.cpp:1-23`). Flags come from a `-- FLAGS:` line (`ElmE2ETestBase.hpp:944-1014`). The `elm-bugs` package is not among the suites listed in `eco/test/CMakeLists.txt:16-38`, so its tests are statements of intended behaviour, not confirmed runs. `Debug.log` writes `label: value` to the program output stream at evaluation time (`debug-log-ordering-policy.md:7-16`); wildcard `_ = Debug.log` sequences keep source order, named `let` bindings do not (`:37-53`).

| Test (path under `eco/test/`) | Shows | CHECK values |
|---|---|---|
| `elm/src/CmdBatchOrderTest.elm` | reverse batch order for Task and port managers, nested batch flattened | `tasks: [3,2,1]`; `port: [5,4,3,2,1]` |
| `elm/src/PortEchoIntTest.elm` | Int round trip incl. 32-bit and 2^53-1 limits | `0`, `-1`, `42`, `2147483647`, `-2147483648`, `9007199254740991`, `-9007199254740991`, `"done"` |
| `elm/src/PortEchoFloatTest.elm` | Float round trip | `0`, `1.5`, `-0.25`, `0.1`, `30000000000`, `-1e-7`, `123456.789` |
| `elm/src/PortEchoBoolTest.elm` | Bool | `True`, `False` |
| `elm/src/PortEchoStringTest.elm` | String incl. quotes, backslash, control chars, NUL, astral char (logged as code lists) | `[]`, `[104,101,108,108,111]`, ..., `[99,97,102,233,32,128512]`, `[110,117,108,0,105,...]` |
| `elm/src/PortEchoMaybeIntTest.elm` | Maybe as null/value | `Just 3`, `Nothing`, `Just -7` |
| `elm/src/PortEchoListIntTest.elm` | List | `[]`, `[1,2,3]`, `[1..20]` |
| `elm/src/PortEchoArrayStringTest.elm` | Array | `Array.fromList []`, `Array.fromList ["a","b","c"]` |
| `elm/src/PortEchoTuple2Test.elm`, `PortEchoTuple3Test.elm` | tuples as arrays | `(1,"one")`, `(-2,"")`; `(1,2.5,True)`, `(0,-0.5,False)` |
| `elm/src/PortEchoUnitTest.elm` | unit as null | `()` twice |
| `elm/src/PortEchoNestedTest.elm` | `List (Maybe (Int, List String))` | `[Just (1,["x","y"]),Nothing,Just (2,[])]`, `[]` |
| `elm/src/PortEchoJsonValueTest.elm` | Value passthrough | `"{\"a\":[1,true,null],\"b\":\"x\"}"`, `"\"plain\""`, `"2.5"`, `"null"` |
| `elm/src/PortAliasEchoTest.elm` | port type via alias; record round trip | `{ n = 42, s = "hi" }`, `"ok"` |
| `elm/src/PortEchoTest.elm` | basic echo | `got: 42`, `done: "ok"` |
| `elm/src/CovPort*Test.elm`, `PortEncoding*Test.elm`, `OutgoingPortTuple3Test.elm` | declarations of each payload kind compile and run (ports unused or unsubscribed) | `testValue: 1` / `testValue: 0` / `"sent"` |
| `elm/src/FlagsRecordTest.elm` | record flags; FLAGS `{"count":42,"label":"native-flags","enabled":true}` | `label: "native-flags"`, `count: 43`, `enabled: True` |
| `elm/src/TaskPerformValueTest.elm` | `Task.perform` values | `a: 42`, `b: "nullary ok"`, `c: -7`, `d: "hello"` |
| `elm/src/TaskAttemptErrorTest.elm` | `attempt` gives `Ok`/`Err` | `ok: 42`, `err: "boom"` |
| `elm/src/TaskSucceedAsArgTest.elm` | | `got: 7` |
| `elm/src/TimerEffectTest.elm` | chained `Process.sleep 100` via `perform` | `"fired 1"` .. `"fired 5"`, `"done"` |
| `elm/src/EntryMainOfRootModuleTest.elm` | root module's `main` is the entry | `which: "root"`, `greeting: "hello"` |
| `elm/src/NonEntryMainEvaluatedOnceTest.elm` | imported `main` is an ordinary CAF | `auxMain: "abab"`, CHECK-NEXT `uses: 2`, no second `auxMain` |
| `elm-core/src/TaskOnErrorCascadeTest.elm` | `onError` skips the rest of a failed chain | `recovered 1..3`, `final: 60` |
| `elm-core/src/ProcessSpawnKillHalfTest.elm` | killed sleeping processes never continue | `fired 1,3,5,7,9`, `done` |
| `elm-core/src/ProcessSpawnRecursiveTest.elm` | nested spawns | `spawned 1..5`, `bottom`, `done` |
| `elm-core/src/ProcessYieldThrashingTest.elm` | two `sleep 0` loops both finish (order not checked) | `A 1..5`, `B 1..5`, `done` |
| `elm-core/src/ProcessSleepNonFiniteTest.elm` | `1/0`, `0/0`, `1e300` sleeps wake before 2000 ms | CHECK-DAG `inf/nan/huge: woke first`, `reference woke` |
| `elm-bugs/src/CoreIssue1043PortErrorObjectObjectTest.elm` | bad incoming value: `EXIT: 1`, message names the value | `Trying to send an unexpected type of value through port \`echoIn\``, `1337`, NOT `[object Object]` |
| `elm-bugs/src/CoreIssue1110*`, `CoreIssue1141*`, `CoreIssue1154*` | subscription returned with a port command is live for its synchronous reply | `got: "hello"` |
| `elm-bugs/src/CoreIssue1123NestedCmdBatchStackOverflowTest.elm` | 100000-deep batch | `got: 1` |
| `elm-bugs/src/CoreIssue955KillProcessTwiceTest.elm` | double kill is a no-op | `killed twice: ()` |
| `eco-divergence/src/PortBytesEchoTest.elm` | Bytes port round trip (eco extension) | `sent: 4`, `got: [1,2,254,255]` |
| `eco-divergence/src/PortBytesNestedNativeTest.elm`, `FlagsBytesNativeTest.elm` | native compile errors | `-- PORT ERROR -`; `-- BAD FLAGS -`, "wants \`Bytes\` in its flags" |


## Initial Basis

What the definition's initial basis must contain: the predefined types, constructors and values that the rules, the derived forms, the platform section or the port rules mention, plus all of `Basics` (direction D4). Types and fixities are from elm/core 1.0.5 (`core/` = `/home/rupert/.eco/0.2.0/packages/elm/core/1.0.5/src/`). Meanings: see "Arithmetic", "Equality", "Comparison and Order" above and rulings A40 to A65. A basis function written in Elm is defined by its elm/core definition (A60).

### Types

| Identifier | Kind | Static Meaning | Dynamic Meaning | Cite |
|------------|------|----------------|-----------------|------|
| Int | type, arity 0 | number, comparable | the implementation's Int range (A40) | core/Basics.elm:121 |
| Float | type, arity 0 | number, comparable | IEEE 754 binary64 values | core/Basics.elm:144 |
| Bool | custom type `True \| False` | | | core/Basics.elm:444 |
| Order | custom type `LT \| EQ \| GT` | | | core/Basics.elm:426 |
| Never | custom type with no values | | | core/Basics.elm:948 |
| Char | type, arity 0 | comparable | abstract characters (A52) | core/Char.elm |
| String | type, arity 0 | comparable, appendable | finite sequences of characters | core/String.elm |
| List | type, arity 1, constructors `[]` and `::` | comparable and appendable per element | finite lists | core/List.elm |
| Maybe | custom type `Just a \| Nothing` | | | core/Maybe.elm |
| Result | custom type `Ok a \| Err e` | | | core/Result.elm |
| Array | abstract type, arity 1 | port payload | finite sequences | core/Array.elm |
| Json.Encode.Value / Json.Decode.Value | abstract type | port payload | JSON values (A74) | elm/json |
| Cmd, Sub | abstract types, arity 1 | | effect descriptions | core/Platform/Cmd.elm, core/Platform/Sub.elm |
| Task | abstract type, arity 2 | | task descriptions | core/Task.elm |
| Process.Id | abstract type | | process identifiers | core/Process.elm |
| Program | abstract type, arity 3 | type of `main` | program descriptions | core/Platform.elm |
| Html (VirtualDom.Node) | abstract type, arity 1 | permitted type of `main` | host-rendered views | elm/virtual-dom |
| unit, 2-tuples, 3-tuples | built-in types | comparable when components are | | survey "Types and Inference" |

### Values of Basics, with fixities

| Identifier | Type | Fixity | Cite |
|------------|------|--------|------|
| `(+)` add, `(-)` sub, `(*)` mul | number -> number -> number | left 6, left 6, left 7 | core/Basics.elm:82-84,168-186 |
| `(/)` fdiv | Float -> Float -> Float | left 7 | core/Basics.elm:85,203 |
| `(//)` idiv | Int -> Int -> Int | left 7 | core/Basics.elm:86,225 |
| `(^)` pow | number -> number -> number | right 8 | core/Basics.elm:87,235 |
| `(==)`, `(/=)` | a -> a -> Bool | non 4 | core/Basics.elm:75-76,348-357 |
| `(<)`, `(>)`, `(<=)`, `(>=)` | comparable -> comparable -> Bool | non 4 | core/Basics.elm:77-80,367-385 |
| `(&&)`, `(\|\|)` | Bool -> Bool -> Bool | right 3, right 2 | core/Basics.elm:73-74,468-484 |
| `(++)` append | appendable -> appendable -> appendable | right 5 | core/Basics.elm:81,510 |
| `(<\|)`, `(\|>)` | function application | right 0, left 0 | core/Basics.elm:71-72,894-904 |
| `(<<)`, `(>>)` | function composition | left 9, right 9 | core/Basics.elm:88-89,848-859 |
| `(::)` | a -> List a -> List a | right 5 | core/List.elm |
| toFloat, round, floor, ceiling, truncate | Int -> Float; Float -> Int | | core/Basics.elm:252-316 |
| min, max, compare | comparable -> comparable -> ...; Order | | core/Basics.elm:395-418 |
| not, xor | Bool functions | | core/Basics.elm:452,496 |
| modBy, remainderBy | Int -> Int -> Int | | core/Basics.elm:539-555 |
| negate, abs | number -> number | | core/Basics.elm:566-580 |
| clamp | number -> number -> number -> number | | core/Basics.elm:592 |
| sqrt, logBase, e, pi, cos, sin, tan, acos, asin, atan, atan2, radians, degrees, turns, fromPolar, toPolar, isNaN, isInfinite | Float functions and constants | | core/Basics.elm:609-826 |
| identity, always, never | a -> a; a -> b -> a; Never -> a | | core/Basics.elm:912-968 |

### Values beyond Basics that the definition needs

| Identifier | Why Needed | Cite |
|------------|------------|------|
| Debug.log, Debug.todo, Debug.toString | Ruling A62 | core/Debug.elm |
| Platform.worker | the program form of Section 8 | core/Platform.elm |
| Cmd.none, Cmd.batch, Cmd.map; Sub.none, Sub.batch, Sub.map | direction D10 | core/Platform/Cmd.elm, core/Platform/Sub.elm |
| Task.succeed, fail, andThen, onError, map, perform, attempt | direction D10 | core/Task.elm |
| Process.spawn, sleep, kill | Task section | core/Process.elm |

### Default Imports

See "Modules" under Static Semantics for the exact default import list (from `Parse/DefaultImports.elm`).

## Out of Scope

| Construct or Feature | Reason |
|----------------------|--------|
| `infix` declarations, `effect module` headers, `Elm.Kernel.*` references | Kernel-only syntax (A11, A16, A37, A85) |
| GLSL shader blocks `[glsl\| ... \|]` | WebGL extension syntax; not used outside elm-explorations/webgl |
| Library modules beyond the initial basis (String, Char and List functions, Dict, Set, Bitwise, Json decoders and encoders, Time, Random, Browser) | Library, not language (A54, A55, A64); only types and the platform functions listed above are in the basis |
| eco extensions: Bytes payloads, System.Environment flags, size limits | Implementation appendix (A13, A18, A33, A34) |
| Resource exhaustion | A61 |
