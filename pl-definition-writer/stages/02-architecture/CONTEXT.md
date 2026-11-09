# Stage 02: Architecture

Decide the shape of the book and fix its notation before any chapter is written.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| Previous stage | `definition/survey/book-brief.md` | Full file | Scope, previous edition |
| Previous stage | `definition/survey/language-survey.md` | Full file | Every construct to place |
| Previous stage | `definition/survey/ambiguity-log.md` | Rulings | Constraints on the design |
| Shared | `../../shared/definition-style.md` | "Structure", "Bare Language and Derived Forms", "Semantic Objects" | The form being planned for |
| Shared | `../../shared/exemplar-index.md` | "Structure and Method" rows | The grid as the exemplar draws it |
| Shared | `../../shared/latex/latex-conventions.md` | "Notation Discipline", "Label Scheme" | What macros.sty must provide |
| Shared | `../../shared/latex/defn.sty` | Command names only | Names macros.sty must not reuse |
| Reference | `references/book-plan-format.md` | Full file | Book plan format |
| Reference | `references/notation-format.md` | Full file | Registry format and macro generation |

## Process

1. Propose the levels of the language and the phase by level grid, with one line per cell saying what it covers.
2. Classify every surveyed construct as bare or derived, applying the test in definition-style B2. For each derived form, sketch its translation in one line.
3. Write the chapter outline: one entry per grid cell and appendix, in book order, with the phrase classes and objects each will define. Decide the optional appendices.
4. Build the chapter checklist from the outline, every row `pending`.
5. Write the notation registry: syntactic classes and their metavariables, semantic classes and theirs, operations, and one judgment form per phrase class per phase.
6. Generate `macros.sty` from the registry as `notation-format.md` "Generating macros.sty" describes, with the generator script `definition/architecture/gen_notation.py`, which writes `definition/architecture/notation.md` and `definition/tex/macros.sty`; compile it once to prove it loads.
7. Run the audit below, then write the three outputs.

## Checkpoints

| After Step | Agent Presents | Human Decides |
|------------|---------------|---------------|
| 2 | The grid, and the bare or derived list with translation sketches | Levels, cells, and each borderline bare or derived call |
| 5 | The notation registry | Every symbol and judgment form; this is the last cheap moment to change notation |

## Audit

| Check | Pass Condition |
|-------|---------------|
| Placement | Every construct in the survey is bare, derived, or listed as out of scope |
| Derived test | Every derived form passes definition-style B2 and B4 |
| Judgments | Every bare phrase class has a judgment form for each phase it takes part in |
| One name | No symbol, metavariable or macro name is registered twice, and none clashes with `defn.sty` |
| Generated | Every registry row has exactly one macro in `macros.sty`, and `macros.sty` loads without error |
| Rulings | Every ruling marked as affecting syntax, static or dynamic is reflected in the plan |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Book plan | `definition/architecture/book-plan.md` | `book-plan-format.md` |
| Notation registry | `definition/architecture/notation.md` | `notation-format.md` "Registry" |
| Macro package | `definition/tex/macros.sty` | Generated LaTeX package |
| Generator | `definition/architecture/gen_notation.py` | The script that writes the registry and the macro package from one table |
