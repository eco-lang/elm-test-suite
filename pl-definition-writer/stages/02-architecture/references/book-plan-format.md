# Book Plan Format

The book plan is the map every later stage works from. Later stages read it by
section name and update only the Status column of the checklist.

```
# Book Plan: <Title>

## Grid
| Level | Syntax | Static Semantics | Dynamic Semantics |
| Core    | syntax-core    | static-core    | dynamic-core    |
| Modules | syntax-modules | static-modules | dynamic-modules |
| Programs | programs (all three phases) |

One line under the table for each level, saying what it covers.

## Bare and Derived
### Bare Constructs
| Phrase Class | Construct | Survey Ref |
### Derived Forms
| Phrase Class | Derived Form | Equivalent Form (sketch) | Fresh Names | Survey Ref |
### Out of Scope
| Construct | Reason |

## Chapter Outline
One subsection per chapter, in book order:
### <file name>: <chapter title>
- Kind: syntax | static | dynamic | programs | appendix | framing
- Level: <level>
- Defines: phrase classes, semantic objects, operations
- Depends on: earlier chapters it uses
- Rulings: ambiguity log entries it must honour (A3, A7)
- Exemplar: rows of exemplar-index.md most useful for it

## Chapter Order
The exact list of file names, in the order stage 08 includes them, with
`preface` and `introduction` first and appendices last.

## Chapter Checklist
| Chapter | Stage | Status | Rules | Notes |
| syntax-core | 03 | pending | - | |
| static-core | 04 | pending | | |
| preface | 05 | pending | - | |
Status moves pending -> drafted (writing stage) -> audited (stage 07).
Rules: the range of rule numbers the chapter uses once drafted (e.g. 1-62).
```

## Rules for the Plan

- The grid follows definition-style S1 to S4. A level appears only if it has
  its own phrase classes.
- Chapters are named `<phase>-<level>` (`static-core`), the top level by its
  level name (`programs`), appendices `appendix-<topic>`.
- Every chapter in the outline appears once in Chapter Order and once in the
  checklist.
- The plan records decisions. Reasons longer than one line belong in the
  ambiguity log or a checkpoint discussion, not here.
