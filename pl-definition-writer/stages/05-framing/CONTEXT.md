# Stage 05: Framing

Write the preface, the introduction and the remaining appendices around the finished chapters.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| Stage 01 | `definition/survey/book-brief.md` | Full file | Title, language, version, previous edition |
| Stage 01 | `definition/survey/language-survey.md` | "Initial Basis" | Entries for the basis appendices |
| Stage 02 | `definition/architecture/book-plan.md` | "Grid", "Chapter Outline", "Chapter Checklist" | Structure to describe; optional appendices chosen |
| Stage 02 | `definition/architecture/notation.md` | Full file | The only names allowed |
| Stage 02 | `definition/tex/macros.sty` | Used by the preview build | Notation macros |
| Stage 03 | `definition/tex/syntax-<level>.tex`, `definition/tex/appendix-derived-forms.tex` | Grammar figures and derived forms tables | Source for the full grammar appendix |
| Stage 04 | `definition/tex/static-<level>.tex`, `dynamic-<level>.tex`, `effects.tex`, `programs.tex` | Object figures, judgment boxes, rule numbers | What the introduction and basis appendices refer to |
| Shared | `../../shared/definition-style.md` | "Structure", "Initial Basis" | Form rules |
| Shared | `../../shared/prose-style.md` | Full file | Voice; the preface is where extended argument is allowed |
| Shared | `../../shared/value-framework.md` | Full file | Value targets |
| Shared | `../../shared/latex/latex-conventions.md` | Full file | How to typeset |
| Shared | `../../shared/exemplar-index.md` | "Structure and Method" and "Appendices" rows, then those pages only | The form in use |
| Reference | `references/framing-guide.md` | Full file | What each framing part contains |

## Process

1. Confirm every syntax and semantics chapter in the checklist is `drafted` or `audited`. Stop and say which are not, if any.
2. Draft the preface, following `framing-guide.md` "Preface".
3. Write the introduction, following `framing-guide.md` "Introduction".
4. Write the full grammar appendix by collating the grammar figures and derived forms (B6).
5. Write the initial static basis and initial dynamic basis appendices.
6. Write any optional appendices the plan chose (overloading or special cases, history, changes).
7. Compile a preview as `../../shared/latex/latex-conventions.md` "Preview" describes, with `macros.sty` from `definition/tex/`, and fix every error.
8. Run the audit below, write the files to `definition/tex/`, and set their checklist rows to `drafted`.

## Checkpoints

| After Step | Agent Presents | Human Decides |
|------------|---------------|---------------|
| 2 | The preface draft | Its stance on the language, the method, and what it says about earlier editions |

## Audit

| Check | Pass Condition |
|-------|---------------|
| Keystone | The preface states the method as a sentence of the form background, phrase, meaning, and explains it in words |
| Grid | The introduction's grid table matches the plan's "Grid" cell for cell |
| Full grammar | Every production in the syntax chapters and every derived form appears in the full grammar, derived ones marked |
| Basis paired | Every identifier in the static basis appendix has a dynamic entry and the reverse (I2) |
| Basis faithful | Every entry matches the survey's "Initial Basis" and its rulings |
| Prose | No breach of the prose-style Hard Constraints |
| Builds | Every preview compiles with no errors |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Preface | `definition/tex/preface.tex` | LaTeX, unnumbered chapter |
| Introduction | `definition/tex/introduction.tex` | LaTeX chapter file |
| Appendices | `definition/tex/appendix-<topic>.tex` | LaTeX chapter files |
| Advanced checklist | `definition/architecture/book-plan.md` | Status column set to `drafted` |
