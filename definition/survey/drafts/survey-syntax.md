# Survey Part 1: Lexis and Syntax

Scope: the lexical and context-free syntax of Elm 0.19.1 as eco accepts it, plus the
restrictions eco enforces without type information (parser and canonicaliser). No typing,
no evaluation.

Cite convention: every path is relative to `/home/rupert/sc/gitlab/eco-compiler`, except
paths starting `elm/`, `elm-parser/` or `elm-url/`, which are relative to
`/home/rupert/.eco/0.2.0/packages/` (`elm/core/1.0.5/src/...`, `elm/parser/1.1.0/src/...`,
`elm/url/1.0.0/src/...`).

## Sources

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

## Lexis

### Reserved Words

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

### Identifier Classes

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

### Special Constants

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

### Comments

| Form | Nesting | Notes | Cite |
|------|---------|-------|------|
| `--` to end of line | n/a | may contain tabs; CR before LF is part of it | `compiler/src/Compiler/Parse/Space.elm:236-238,264-314` |
| `{-` ... `-}` | yes, counts `{-`/`-}` pairs | tab inside is an error; unclosed is `EndlessMultiComment` | `Space.elm:12-14,316-416` |
| `{-\|` ... `-}` doc comment | yes (inner `{-` `-}` nest) | NOT whitespace: a gap stops before `{-\|` (`Space.elm:16-18,332-333`), so it is legal only where the grammar reads one: after the module header (`Module.elm:558-590`) and before a top-level declaration (`compiler/src/Compiler/Parse/Declaration.elm:112-127`); the next token must then start in column 1 | `Space.elm:423-495` |

- Whitespace is space, LF, and CR (CR does not advance the column, `Space.elm:276-277`). A tab outside a line comment is the error `HasTab` (`Space.elm:13-15,279-280`).
- `--` is recognised only where a gap is read; inside an operator run it is part of the operator (`Symbol.elm:12-16`, `Space.elm:264-274`). See C-SYN-3.

### Layout and Indentation

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

### Infix and Precedence

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

## Phrase Classes

Notation: `[x]` optional, `x*` zero or more, `x+` one or more. "term" is the
atomic subclass of each phrase class (no unparenthesised application or operator).

### Expressions

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

### Patterns

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

### Types

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| type variable | `a` | lower, not reserved | `Type.elm:91-96` |
| type constructor | `T`, `M.T` (term); `T t1 ... tn` (application) | arguments are type terms (`Maybe List a` gives `Maybe` two arguments); arity must match (`BadArity`) | `Type.elm:10-17,72-90,265-332`; `compiler/src/Compiler/Canonicalize/Type.elm:229` |
| unit | `()` | no whitespace inside | `Type.elm:99-101` |
| parenthesised / tuple | `( t )`, `( t1 , t2 [, t3]* )` | n > 3 `TupleLargerThanThree` | `Type.elm:28-31,98-111,339-390`; `Canonicalize/Type.elm:132` |
| record | `{ }`, `{ f1 : t1 (, fi : ti)* }` | duplicate field `DuplicateField`; > 2047 fields `TooLarge` (eco only) | `Type.elm:112-180,391-460`; `Canonicalize/Type.elm:136-152` |
| extensible record | `{ a \| f1 : t1 (, fi : ti)* }` | `a` is an unqualified lower variable; at least one field | `Type.elm:59-62,122-143` |
| function | `t1 -> t2` | right associative; left operand is an application or a term | `Type.elm:192-250` |

### Declarations (let and top-level)

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| top-level value | `[doc] [x : t NEWLINE] x p1 ... pn = e` | `x` lower; `pi` pattern terms; annotation name repeated on a fresh line (`DeclDefNameMatch`); no top-level destructuring; no operator definitions; duplicate names `DuplicateDecl` (ports and effect names included); duplicate args `DuplicatePattern`; arg shadowing a top-level name `Shadowing`; zero-arg value cycles `RecursiveDecl`; > 2047 params `TooLarge` | `Declaration.elm:131-245`; `compiler/src/Compiler/Canonicalize/LocalEnvironment.elm:127-142`; `Canonicalize/Module.elm:311,340,371`; `Canonicalize/Module.elm:22-34,260` |
| let value | `[x : t] x p1 ... pn = e` | annotation and definition aligned, names equal; names distinct in one `let`; must not shadow any local or top-level name; recursion only among definitions with parameters | `Expression.elm:1229-1346`; `Canonicalize/Expression.elm:903-935,1371-1398` |
| let destructuring | `pterm = e` | pattern term only (`(Just x) = e`, `( a, b ) = e`, `_ = e`, even `5 = e` parse); exhaustiveness is checked later (UNSAFE PATTERN) | `Expression.elm:1349-1407`; `compiler/tests/SourceIR/PatternFailsCases.elm:276-530` |
| doc comment | `{-\| ... -}` before a top-level declaration | next token on a fresh line | `Declaration.elm:104-127` |
| custom type / alias / port / infix | see their subsections | | |

Alternatives at top level are tried in the order `type`, `port`, value (`Declaration.elm:86-99`);
in a `let`, named definition then destructuring (`Expression.elm:1232-1237`).

### Module headers

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| plain | `module M exposing L` | header starts in column 1; may not declare ports (`UnexpectedPort`, or `NoPortsInPackage` in a package) | `Module.elm:724-758,346-370` |
| port module | `port module M exposing L` | refused in packages (`NoPortModulesInPackage`); must declare >= 1 port (`NoPorts`) | `Module.elm:760-779,371-388` |
| effect module | see Effect module headers | kernel projects only | `Module.elm:781-897` |
| none | (no header) | accepted; module gets no name, `exposing (..)`, and `Ports` effects exactly when it declares ports; no effect rule checked | `Module.elm:15-17,28-29,314-330` |
| module doc comment | `{-\| ... -}` on a fresh line after the header | optional | `Module.elm:552-590` |
| module body | header, imports, [kernel: infix decls], one or more declarations | at least one declaration; whole file consumed (`ModuleBadEnd`) | `Module.elm:186-235,505-514`; `Primitives.elm:356-398` |

### Imports

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| import | `import M [as A] [exposing L]` | starts in column 1; `A` is a single upper identifier; `as` precedes `exposing`; ends at a fresh line; without `exposing` the list is empty | `Module.elm:1037-1172` |
| kernel import | `import Elm.Kernel.X` / `Eco.Kernel.X` | in a kernel project `as` is `KernelImportAlias`; outside one the module is not found | `Module.elm:239-273` |
| default imports | `Basics (..)`, `Debug`, `List ((::))`, `Maybe (Maybe(..))`, `Result (Result(..))`, `String (String)`, `Char (Char)`, `Tuple`, `Platform (Program)`, `Platform.Cmd as Cmd (Cmd)`, `Platform.Sub as Sub (Sub)` | prepended to every module except those of `elm/core` | `DefaultImports.elm:5-26,48-62`; `Module.elm:200-209` |
| exposing items | as Exposing lists | `T(..)` on an alias `ImportOpenAlias`; exposing a constructor by name `ImportCtorByName`; unknown item `ImportExposingNotFound` | `Environment/Foreign.elm:385-430` |

### Exposing lists

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| open | `( .. )` | whitespace allowed around `..` | `Module.elm:1178-1200` |
| explicit | `( item (, item)* )` | at least one item | `Module.elm:1178-1237` |
| value item | `x` | | `Module.elm:1239-1253` |
| operator item | `(op)` | no whitespace inside; in a module export must be declared infix in that module | `Module.elm:1254-1262`; `Canonicalize/Module.elm:503-507` |
| type item | `T`, `T(..)` | whitespace allowed: `T (..)`, `T( .. )`; `Alias(..)` export is `ExportOpenAlias`; duplicate export `ExportDuplicate`; unknown `ExportNotFound` | `Module.elm:1263-1300`; `Canonicalize/Module.elm:457,476-520` |

### Port declarations

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| port | `port x : t` | only in a `port module` (or a header-less file); not in packages; name in the value namespace (`DuplicateDecl`) | `Declaration.elm:418-455`; `Module.elm:346-388`; `LocalEnvironment.elm:145-168` |

The port-type shape checks (`PortTypeInvalid`, `PortPayloadInvalid`) need alias expansion and
are out of scope here (`Canonicalize/Error.elm:189-190,255-277`).

### Type declarations (custom types)

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| custom type | `type T a1 ... an = C1 t* (\| Ci t*)*` | `T`, `Ci` unqualified upper; `ai` lower; >= 1 variant; constructor args are type terms; each `\|` indented; duplicate params `DuplicateUnionArg`; a variable used but not a param `TypeVarsUnboundInUnion` (unused params allowed); type name shared with aliases `DuplicateType`; constructor name unique across all unions and record aliases of the module `DuplicateCtor`; > 2040 ctor fields or a nullary ctor after index 1023 `TooLarge` (eco only) | `Declaration.elm:252-310,364-414`; `Type.elm:464-488`; `LocalEnvironment.elm:188-207,415-449,539-560,675-679`; `compiler/tests/SourceIR/CanonicalizeFailsCases.elm:141-162` |

### Type aliases

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| alias | `type alias T a1 ... an = t` | duplicate params `DuplicateAliasArg`; params must be exactly the body's free variables, unused params included (`TypeVarsMessedUpInAlias`); recursive aliases `RecursiveAlias`; shares namespace with custom types | `Declaration.elm:255-290,314-360`; `LocalEnvironment.elm:451-495,280-300` |
| record constructor | an alias whose canonical body is a closed record also defines constructor `T` | see Rewrites | `LocalEnvironment.elm:578-628` |

### Type annotations

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| top-level | `x : t` then, on a fresh line, `x ...` | the definition must follow (only comments between) and repeat the name | `Declaration.elm:131-182` |
| let | `x : t` then, aligned, `x ...` | same, aligned instead of fresh line | `Expression.elm:1264-1307` |
| more parameters than arrows | | `AnnotationTooShort`; needs alias expansion (`iteratedDealias`), so not purely syntactic | `Canonicalize/Expression.elm:1338-1360` |

### Infix declarations

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| infix | `infix (left\|right\|non) d (op) = x` | kernel projects only; after imports, before all other declarations; `d` exactly one digit 0-9 (the next char is not examined); `(op)` adjacent parens; followed by a fresh line; duplicates not checked (C-SYN-11) | `Declaration.elm:458-540`; `Number.elm:540-570`; `Module.elm:212-216,537-549`; `Canonicalize/Module.elm:109-111` |

### Effect module headers

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| effect module | `effect module M where { command = C } exposing L`, or `subscription = S`, or both in either order separated by `,` | kernel projects only (`NoEffectsOutsideKernel`); no ports (`UnexpectedPort`); every token indented; `command`/`subscription` become top-level names (`DuplicateDecl`); the named types and manager functions must exist (`EffectNotFound`, `EffectFunctionNotFound`) | `Module.elm:781-1029,390-399`; `LocalEnvironment.elm:145-168`; `Canonicalize/Error.elm:176-177` |

### GLSL shaders

| Construct | Form | Restrictions without type information | Cite |
|-----------|------|----------------------------------------|------|
| shader | `[glsl\|` text `\|]` | text ends at the first `\|]` (even inside a GLSL comment); text must parse as GLSL; inputs recorded are top-level single-name `attribute`/`uniform`/`varying` declarations of type `vec2 vec3 vec4 mat4 int float sampler2D bool`, others ignored | `Shader.elm:1-25,40-100` |

The native back end rejects shaders after type checking (`design_docs/elm-divergence.md:254-255`).

### Rewrites

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

## Syntactic Restrictions

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

## Evidence

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

## Candidate Ambiguities

### C-SYN-1: Whitespace inside `()`
- Construct: unit in expressions, patterns, types.
- Question: Is `( )` (or `({- c -})`) a unit?
- Implementation: patterns accept it (`Pattern.elm:251-262`); expressions take the unit branch only when nothing follows `(` directly, otherwise require an expression (`Expression.elm:246-264,312-313`); types take `()` only with `)` immediately (`Type.elm:99-101`).
- Notes: silent.
- Options: (a) record the inconsistency as is; (b) define unit as `()` with no gap everywhere and treat the pattern case as a parser leniency; (c) allow a gap everywhere.
- Affects: syntax

### C-SYN-2: Reserved words as the last part of a qualified name
- Construct: qualified variables.
- Question: Is `List.if` lexically a qualified identifier?
- Implementation: only unqualified names are checked against reserved words (`Variable.elm:17-19,336-349`); `M.if` parses as `VarQual` and fails later as not found.
- Notes: silent.
- Options: (a) lexical rule excludes reserved words in every position; (b) only unqualified; the qualified case is a scope error.
- Affects: syntax

### C-SYN-3: Maximal munch over `-` and `--` in operators
- Construct: operator lexing; negation; comments.
- Question: Does `a*-b`, `2^-1` or `x +--c` lex as one operator?
- Implementation: an operator is the longest run of operator characters, read whole (`Symbol.elm:12-16,126-132`); `--` starts a comment only where a gap is read (`Space.elm:264-274`). So `*-`, `^-`, `+--` are single (unknown) operators.
- Notes: silent.
- Options: (a) record maximal munch exactly; (b) split a trailing `-`/`--` off an operator run.
- Affects: syntax

### C-SYN-4: Which terms admit `.field`, and `.f.g`
- Construct: field access, accessor.
- Question: Which expressions may be followed by `.f`, and what is `.x.y`?
- Implementation: access follows only a variable, a record/update, or a `(`-form (parens, tuple, unit, even `(op)`) (`Expression.elm:65-81`); an accessor is not followed by access, so `.x.y` parses as the application `(.x) (.y)` and `"s".x` as `"s" (.x)` (`Expression.elm:119-126,591-614`).
- Notes: silent.
- Options: (a) grammar exactly as implemented; (b) access on any atomic expression; (c) `.x.y` as a composed accessor.
- Affects: syntax

### C-SYN-5: Layout measures token start columns, not ends of multi-line tokens
- Construct: layout rule with `"""` strings.
- Question: Is a token that continues a construct judged by its own start column even when the previous token ended at a low column on a later line?
- Implementation: every check uses the current column only (`Space.elm:115-131`); `"""` closing in column 1 then `++` in column 5 inside a let definition at column 9 ends the definition and fails at `in`.
- Notes: Elm 0.19.1 rejects the same program; the test treats it as a bug (`test/elm-bugs/src/CompilerIssue1947MultilineStringInLetBinopTest.elm`).
- Options: (a) layout by start column only (implementation and Elm); (b) exempt tokens on the line where a multi-line token ends.
- Affects: syntax

### C-SYN-6: What a column is
- Construct: layout.
- Question: How are columns counted for non-ASCII, astral characters and CR?
- Implementation: one column per code point (surrogate pair = 1) in identifiers, strings, comments (`Primitives.elm:19-27`, `Identifier.elm:33-36`, `String.elm:149-160`); CR in whitespace counts 0 (`Space.elm:276-277`) but in block comments counts 1 (`Space.elm:380-381`); tabs are illegal in whitespace.
- Notes: silent.
- Options: (a) code points, CR ignored; (b) UTF-16 units; (c) bytes; (d) grapheme clusters.
- Affects: syntax

### C-SYN-7: Negative literal patterns
- Construct: literal patterns.
- Question: Is `-1 -> ...` a legal case branch?
- Implementation: no `-` alternative in pattern terms; a number must start with a digit (`Pattern.elm:80-132`, `Number.elm:12-14`), so it is a syntax error.
- Notes: silent (eco's `Pattern.elm` mirrors upstream's structure; to confirm against elm/compiler `Parse/Pattern.hs`).
- Options: (a) no negative patterns; (b) allow `-` digit in Int patterns.
- Affects: syntax

### C-SYN-8: Surrogate code points in `\u{...}`
- Construct: escapes in Char and String literals.
- Question: Is `'\u{D800}'` a legal Char literal?
- Implementation: only values above `10FFFF` are refused (`String.elm:510-511`); the escape is re-encoded as `\uD800` (`String.elm:17-19`).
- Notes: lone surrogate values are a recorded runtime divergence (`test/eco-divergence/src/StringLoneSurrogateTest.elm`); the lexer is silent.
- Options: (a) allow (implementation); (b) restrict to Unicode scalar values.
- Affects: syntax

### C-SYN-9: Int literals beyond 64 bits
- Construct: Int special constant.
- Question: Is an Int literal outside the 64-bit range an error, or reduced modulo 2^64?
- Implementation: reduced modulo 2^64 as two's complement (`Number.elm:86-93`); on the JS host an inexact read is `NumberInexactOnHost` (`Number.elm:160-177`).
- Notes: Elm 0.19.1 also wraps; the test calls that a bug (`test/elm-bugs/src/CompilerIssue1246LargeIntLiteralTest.elm`); eco documents 64-bit Int (`design_docs/elm-divergence.md:12,32-60`).
- Options: (a) modulo 2^64 (implementation); (b) static error outside [-2^63, 2^64).
- Affects: syntax

### C-SYN-10: Doc comments as tokens
- Construct: `{-| -}`.
- Question: Is a doc comment in an arbitrary position a comment or a syntax error?
- Implementation: a gap stops before `{-|` (`Space.elm:16-18,332-333`), so anywhere other than after the header or before a top-level declaration it is a parse error.
- Notes: silent.
- Options: (a) doc comments are tokens of the module grammar (implementation); (b) treat them as ordinary comments elsewhere.
- Affects: syntax

### C-SYN-11: Duplicate infix declarations
- Construct: infix declarations (kernel only).
- Question: May one module declare the same operator twice?
- Implementation: collected with `Dict.fromList`, no duplicate check (`Canonicalize/Module.elm:109-111`); the surviving entry depends on list order.
- Notes: silent.
- Options: (a) error; (b) last wins; (c) out of scope with kernel syntax (C-SYN-16).
- Affects: syntax

### C-SYN-12: Tuple arity in the grammar or as a restriction
- Construct: tuples in expressions, patterns, types.
- Question: Should the grammar admit only 2- and 3-tuples, or all n >= 2 with a separate restriction?
- Implementation: parser accepts any n (`Type.elm:31-32`, `Expression.elm:327-361`); canonicaliser rejects n > 3 (`Canonicalize/Expression.elm:443-454`).
- Notes: `design_docs/theory/compiler/front-end.md:7` says eco keeps tuples at three.
- Options: (a) grammar n >= 2 plus restriction; (b) grammar with exactly 2 or 3.
- Affects: syntax

### C-SYN-13: eco-only size limits
- Construct: function/lambda parameters, closures, records, constructors.
- Question: Are the heap-layout limits (2047 params, 2047 fields, 2040 constructor fields, 1024 nullary constructors) part of the language?
- Implementation: canonicaliser `TooLarge` errors (`HeapLimits.elm:31-61`, `Canonicalize/Expression.elm:50-57`).
- Notes: documented as divergences from Elm, which has no such limits (`design_docs/elm-divergence.md:214-219`).
- Options: (a) implementation limits outside the Definition; (b) restrictions in the Definition.
- Affects: syntax

### C-SYN-14: Unicode version of identifier classes
- Construct: identifiers.
- Question: Which Unicode version fixes Lu/Ll/Lt/Lm/Lo?
- Implementation: Unicode 14.0.0 tables (`Unicode.elm:1-12`).
- Notes: upstream depends on the GHC that built it (`Unicode.elm:8-11`).
- Options: (a) fix 14.0.0; (b) "some Unicode version", implementation-defined.
- Affects: syntax

### C-SYN-15: Closing `"""` among longer quote runs
- Construct: multi-line strings.
- Question: How is `""""` at the end of a multi-line string read?
- Implementation: the first `"""` closes (`String.elm:362-367`); a fourth `"` then opens a new string literal.
- Notes: silent.
- Options: (a) first-match close (implementation); (b) last three quotes of the run close.
- Affects: syntax

### C-SYN-16: Kernel-only syntax and header-less files
- Construct: `infix` declarations, `effect module`, `Elm.Kernel.*` references, files without a header.
- Question: Which of these belong to Standard Elm?
- Implementation: `infix` and effect modules only in kernel projects (`Module.elm:150-162,212-216,390-399`); kernel references only in kernel packages (`Canonicalize/Expression.elm:28-31`); header-less files are accepted and checked less (`Module.elm:28-29,314-330`) but cannot be imported (`test/elm-compile-errors/src/ErrorMessagesIssue103ImportedModuleWithoutModuleLineTest.elm`).
- Notes: silent.
- Options: (a) core language excludes kernel syntax, with an appendix; (b) include with a "kernel" side condition; (c) header optional only for the main module.
- Affects: syntax

### C-SYN-17: Annotation placement differs between top level and let
- Construct: type annotations.
- Question: Must a top-level definition after its annotation start in column 1 while a let definition must align with its annotation, and may anything but comments come between?
- Implementation: top level `checkFreshLine` (`Declaration.elm:163`); let `checkAligned` (`Expression.elm:1288`); only a gap is read in between.
- Notes: silent.
- Options: (a) state both rules as layout instances (same rule: the definition starts at the annotation's column); (b) separate rules.
- Affects: syntax
