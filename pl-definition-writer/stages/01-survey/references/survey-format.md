# Survey Formats

The three files stage 01 writes. Later stages read them by section name, so
keep the headings exactly as given.

## Book Brief

Ask these in one message at the start of each run. Write the answers as a
table under the heading `# Book Brief`.

| Field | Question | Example |
|-------|----------|---------|
| Title | What is the book called? | The Definition of Foo |
| Slug | A short lowercase-with-hyphens name for files | foo-definition |
| Authors | Who are the authors, in order? | A. Author, B. Author |
| Year | Year of publication or draft | 2027 |
| Edition | Which draft or edition this is; shown under the title and stamped into the PDF file name | Draft version 0.1 |
| Language | Name of the language being defined | Foo |
| Version | Which version or revision of the language | 1.2 |
| Implementation | Path to the implementation's source tree | ~/src/foo |
| Design notes | Paths to design notes, RFCs or an informal manual | ~/src/foo/docs/design |
| Scope | Anything deliberately left out (a library, an experimental feature) | Concurrency extension |
| Previous edition | Path to an earlier definition, if this is a revision | none |

Then ask for **Author Directions**: decisions the authors have already made
about the language or the book (a design philosophy the definition must
express, features to stress, where implementation details go). Write them
under the table as a numbered list headed `## Author Directions`, in the
authors' words where possible. Later stages treat each direction like an
ambiguity ruling: binding, and cited as `D<n>`.

## Language Survey

```
# Language Survey: <Language> <Version>

## Sources
| Part | Paths |   (lexer, parser, desugarer, elaborator, evaluator, basis, tests)

## Lexis
### Reserved Words      (list, with source cite)
### Identifier Classes  (class, lexical form, may be qualified?, cite)
### Special Constants   (kind, lexical form, cite)
### Comments            (form, nesting, cite)
### Infix and Precedence (default fixities, declarations, cite)

## Phrase Classes
One subsection per phrase class, in parser order:
### <Class>
| Construct | Form | Static Checks | Runtime Behaviour | Evaluation Order | Cite |
Notes: rewrites the implementation applies (candidate derived forms).

## Initial Basis
| Identifier | Kind (type, constructor, exception, value) | Static Meaning | Dynamic Meaning | Cite |

## Evidence
Programs run against the implementation and their observed results.

## Out of Scope
What the brief excludes, and constructs found but not covered, with reasons.
```

## Ambiguity Log

```
# Ambiguity Log

## A<n>: <short title>
- **Construct:** <phrase class and construct>
- **Question:** <one sentence>
- **Implementation:** <what it does> (cite)
- **Notes say:** <what the notes say, or "silent"> (cite)
- **Options:** <the realistic answers, each one line>
- **Ruling:** IMPLEMENTATION | INTENT | UNSPECIFIED | <custom>
- **Reason:** <the human's reason, one or two sentences>
- **Affects:** syntax | static | dynamic | basis
```

Number entries A1, A2, ... and never renumber. Later stages cite rulings by
number ("per A7").
