# Stage 04: Semantics

Write one semantics chapter per run: its objects, then its rules with Comments.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| Stage 02 | `definition/architecture/book-plan.md` | The outline entry for the target chapter, "Chapter Checklist" | What this chapter defines and depends on |
| Stage 02 | `definition/architecture/notation.md` | Full file | The only names allowed |
| Stage 02 | `definition/tex/macros.sty` | Used by the preview build | Notation macros |
| Stage 03 | `definition/tex/syntax-<level>.tex` | Grammar figures for the target level | The productions the rules must cover |
| Stage 01 | `definition/survey/language-survey.md` | The phrase classes of the target level; "Initial Basis" | Static checks, runtime behaviour, evaluation order |
| Stage 01 | `definition/survey/ambiguity-log.md` | Entries affecting this phase | Rulings to honour |
| This stage | `definition/tex/static-<level>.tex` | Object figures and operation names only (dynamic chapters only) | Names the dynamic chapter must agree with |
| This stage | Earlier chapters listed under "Depends on" | Object definitions and operations they introduce | Notation defined once, reused |
| Shared | `../../shared/definition-style.md` | "Semantic Objects", "Inference Rules", "Comments"; "Dynamic Conventions" for dynamic chapters | Form rules |
| Shared | `../../shared/prose-style.md` | Full file | Voice |
| Shared | `../../shared/value-framework.md` | Full file | Value targets |
| Shared | `../../shared/latex/latex-conventions.md` | Full file | How to typeset |
| Shared | `../../shared/exemplar-index.md` | "Static Semantics" or "Dynamic Semantics" rows, then those pages only | The form in use |
| Reference | `references/semantics-guide.md` | Full file | Procedure for objects, rules and comments |

## Process

1. Take the first `pending` semantics chapter in Chapter Order. Static chapters for a level come before the dynamic chapter of that level.
2. Lock the value targets with the human and write the value brief comment.
3. Dynamic chapters only: write the reduced syntax section (D1).
4. Write the opening paragraph, then the semantic objects, following `semantics-guide.md` "Objects".
5. Write the operations on those objects, and any property the rules rely on.
6. Write the rules section opening: sentence form, pronunciation, options convention, and for dynamic chapters the effect conventions.
7. For each phrase class in grammar order, write one rule group, following `semantics-guide.md` "Rules", then its Comments.
8. Compile a preview as `../../shared/latex/latex-conventions.md` "Preview" describes, with `macros.sty` from `definition/tex/`, and fix every error.
9. Run the audit below, write the chapter to `definition/tex/`, and set its checklist row to `drafted` with its rule number range.

## Checkpoints

| After Step | Agent Presents | Human Decides |
|------------|---------------|---------------|
| 1 | The value targets and evidence plan | Which values the chapter must deliver |
| 5 | The object figures and operations | Whether the objects are right before any rule depends on them |
| 7 | Each rule group with its Comments, one group at a time | Rule shape, side conditions, what deserves a Comment |

## Audit

| Check | Pass Condition |
|-------|---------------|
| Coverage | Every production in the level's bare grammar figures is covered by a rule (R3) |
| Defined | Every object, operation and metavariable in a rule is in the registry and defined in this chapter or one it depends on (R8) |
| Order | Every operation is defined before its first use (O6); conventions are stated before the first rule (R1, D2) |
| Numbering | Rules carry consecutive numbers following the previous chapter's range |
| Comments | Every Comment cites an existing rule, none paraphrases its rule (C3), and every side condition has a Comment or is self-evident |
| Faithful | Each behaviour in the survey for this level is produced by the rules; every ruling for this phase is honoured and cited in a `%` comment |
| Consistent | A dynamic chapter's object names agree with the static chapter of the same level |
| Values | Every locked value target has its planned evidence |
| Prose | No breach of the prose-style Hard Constraints |
| Builds | The preview compiles with no errors |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Semantics chapter | `definition/tex/<static or dynamic>-<level>.tex`, or `definition/tex/programs.tex` | LaTeX chapter file |
| Advanced checklist | `definition/architecture/book-plan.md` | Status `drafted`, Rules column filled |
