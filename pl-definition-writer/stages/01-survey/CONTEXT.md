# Stage 01: Survey

Read the implementation and the design notes, and record what the language is and where they disagree.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| User | (conversation) | The book brief questions in `references/survey-format.md` "Book Brief" | Facts about this book, collected fresh each run |
| Implementation | The path in the brief | Lexer, parser, type checker or elaborator, evaluator, built-in library, tests | Ground truth for what the language does |
| Design notes | The paths in the brief | Full files | What the language was meant to do |
| Config | `../../shared/run-config.md` | Full file | House settings |
| Reference | `references/survey-method.md` | Full file | How to read an implementation for its semantics |
| Reference | `references/survey-format.md` | Full file | The three output formats |

## Process

1. Ask the user the Book Brief questions and the Author Directions, and write `definition/survey/book-brief.md`.
2. Find the semantic sources in the implementation, as `survey-method.md` "Locating the Semantics" describes. List them with paths.
3. Inventory the lexis: reserved words, identifier classes, special constants, comments, infix handling. Cite a source line for each.
4. Inventory the phrase classes and every construct in each, from the parser. Cite each.
5. For each construct, record its static checks and its runtime behaviour, from the elaborator and the evaluator. Cite each.
6. Read the design notes and mark each construct as agreeing, disagreeing or silent.
7. Write every disagreement, every silence on behaviour that matters, and every implementation quirk into the ambiguity log, one entry each.
8. Run the audit below, then write `definition/survey/language-survey.md` and `definition/survey/ambiguity-log.md`.

## Checkpoints

| After Step | Agent Presents | Human Decides |
|------------|---------------|---------------|
| 4 | The phrase class list and construct counts, plus anything left out of scope | Whether the scope of the book is right |
| 7 | Each ambiguity entry with the options | A ruling per entry: implementation, intent, or deliberately unspecified |

## Audit

| Check | Pass Condition |
|-------|---------------|
| Cited | Every construct, check and behaviour cites a file and line |
| Ruled | Every ambiguity entry has a ruling, and every "unspecified" ruling says why |
| Complete | Every production in the implementation's parser maps to a construct in the survey, or to an out-of-scope note |
| No design | The survey records the language; it proposes no notation, rules or structure |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Book brief | `definition/survey/book-brief.md` | `survey-format.md` "Book Brief" |
| Language survey | `definition/survey/language-survey.md` | `survey-format.md` "Language Survey" |
| Ambiguity log | `definition/survey/ambiguity-log.md` | `survey-format.md` "Ambiguity Log" |
