# Stage 07: Audit

Check the whole book for consistency across chapters, and report what must be fixed and where.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| Stages 03 to 05 | `definition/tex/` | Every chapter file named in Chapter Order | Chapters under audit |
| Stage 02 | `definition/architecture/notation.md` | Full file | The notation every chapter must use |
| Stage 02 | `definition/architecture/book-plan.md` | Full file | Structure, Chapter Order, checklist |
| Stage 01 | `definition/survey/language-survey.md` | Full file | What the book must cover |
| Stage 01 | `definition/survey/ambiguity-log.md` | Full file | Rulings the book must honour |
| Stage 06 | `definition/mechanisation/mechanisation-report.md` | Full file, if the file exists | Findings and divergences to carry forward |
| Shared | `../../shared/definition-style.md` | Full file | The form rules findings cite |
| Shared | `../../shared/prose-style.md` | "Hard Constraints", "Terminology" | Voice checks |
| Shared | `../../shared/latex/latex-conventions.md` | "Label Scheme", "Notation Discipline" | LaTeX checks |
| Reference | `references/audit-checklist.md` | Full file | Every check and how to run it |

## Process

1. Confirm every chapter in the checklist is `drafted`. List any that are not and audit the rest.
2. Run each check in `audit-checklist.md`, in order. Read the chapters in Chapter Order so a definition is seen before its uses.
3. Record each finding with its severity, location, the rule or check it breaks, and the stage that owns the fix. Fix nothing here: a fix is made by rerunning the owning stage, so that stage's audit runs on it.
4. Carry forward open items from the mechanisation report, if there is one.
5. Write the report and present the findings.
6. After the human triages, set every chapter with no open blocker or major finding to `audited` in the checklist.

## Checkpoints

| After Step | Agent Presents | Human Decides |
|------------|---------------|---------------|
| 5 | Findings grouped by owning stage, most severe first | Per finding: fix now (which stage reruns), defer, or reject |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Audit report | `definition/audit/audit-report.md` | `audit-checklist.md` "Report" |
| Advanced checklist | `definition/architecture/book-plan.md` | Status column set to `audited` |
