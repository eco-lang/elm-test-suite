# Stage 03: Syntax

Write the syntax chapter for each level, then the derived forms appendix.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| Stage 02 | `definition/architecture/book-plan.md` | "Grid", "Bare and Derived", the outline entry for the target chapter, "Chapter Checklist" | What to write and in what order |
| Stage 02 | `definition/architecture/notation.md` | "Syntactic Classes", "Special Symbols" | The only names allowed |
| Stage 02 | `definition/tex/macros.sty` | Used by the preview build | Notation macros |
| Stage 01 | `definition/survey/language-survey.md` | "Lexis", and the phrase classes of the target level | The constructs being written up |
| Stage 01 | `definition/survey/ambiguity-log.md` | Entries that affect syntax | Rulings to honour |
| Shared | `../../shared/definition-style.md` | "Syntax Chapters", "Bare Language and Derived Forms" | Form rules |
| Shared | `../../shared/prose-style.md` | Full file | Voice |
| Shared | `../../shared/value-framework.md` | Full file | Value targets for the chapter |
| Shared | `../../shared/latex/latex-conventions.md` | Full file | How to typeset |
| Shared | `../../shared/exemplar-index.md` | "Syntax" rows, then those pages only | The form in use |
| Reference | `references/syntax-guide.md` | Full file | Procedure for each part of a syntax chapter |
| Skill | `../../skills/latex/references/known-errors.md` | Only when a preview fails | Known LaTeX errors and fixes |

## Process

1. Take the first `pending` syntax chapter in the checklist, lowest level first. The derived forms appendix comes after every level.
2. Lock the chapter's value targets with the human (see Checkpoints) and write the value brief comment.
3. Write the lexis sections in the order definition-style G1 gives, following `syntax-guide.md` "Lexis".
4. Write the grammar figures for the bare productions, one figure per group of related phrase classes, following `syntax-guide.md` "Grammar Figures".
5. Write precedence and associativity in prose, then the syntactic restrictions list.
6. For the derived forms appendix: one table per phrase class from the plan's "Derived Forms", with fresh identifier notes. The tables are generated: each row is written in `definition/tools/src/DerivedForms/Table.elm` (its derived form, its equivalent form as a term of the bare syntax, and its Lean function), and `site/node_modules/.bin/elm-pages run definition/tools/src/GenerateDerivedForms.elm`, run from the repository's root, writes them between the `% BEGIN GENERATED derived-forms:<Block>` and `% END GENERATED` lines of `appendix-derived-forms.tex`, and the same rows' functions into `Derived.lean`. Write the appendix's prose, figures and headings by hand; never edit inside the markers.
7. Compile a preview as `../../shared/latex/latex-conventions.md` "Preview" describes, with `macros.sty` from `definition/tex/`, and fix every error.
8. Run the audit below, write the chapter to `definition/tex/`, and set its checklist row to `drafted`.
9. Return to step 1 until no syntax chapter is `pending`.

## Checkpoints

| After Step | Agent Presents | Human Decides |
|------------|---------------|---------------|
| 1 | The chapter's proposed value targets and evidence plan | Which values the chapter must deliver |
| 4 | The grammar figures for the level, as a rendered preview or the LaTeX | Production shape, labels, which constructs are grouped together |

## Audit

| Check | Pass Condition |
|-------|---------------|
| Coverage | Every bare construct the plan assigns to this level has a production; every derived form has a table row |
| Bare only | No derived form appears in a bare grammar figure |
| Closed | Every equivalent form uses only bare syntax or earlier rows (B4) |
| Restrictions are syntactic | No restriction needs type or binding information beyond the phrase itself (G6) |
| Notation | Every metavariable and terminal is written with its registered macro |
| Rulings | Every syntax ruling assigned to this chapter is reflected, and cited in a `%` comment beside the text it shaped |
| Values | Every locked value target has its planned evidence |
| Prose | No breach of the prose-style Hard Constraints |
| Builds | The preview compiles with no errors |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Syntax chapter per level | `definition/tex/syntax-<level>.tex` | LaTeX chapter file |
| Derived forms appendix | `definition/tex/appendix-derived-forms.tex` | LaTeX chapter file; its tables generated from `definition/tools/src/DerivedForms/Table.elm` |
| Advanced checklist | `definition/architecture/book-plan.md` | Status column set to `drafted` |
