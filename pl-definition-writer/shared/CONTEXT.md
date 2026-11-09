# Shared Context

Files used by more than one stage. Nothing here references a stage.

## Routing

| Resource | File | Load When | Scope |
|----------|------|-----------|-------|
| Form of a definition | `definition-style.md` | Planning (02), writing (03 to 05), auditing (07) | The sections each stage's Inputs table names; rule IDs are cited in audits |
| Prose voice | `prose-style.md` | Writing any prose (03 to 05) | Full file |
| Value framework | `value-framework.md` | At the first checkpoint of a chapter (03 to 05), and in its audit | Full file |
| Exemplar index | `exemplar-index.md` | When applying a form rule and an example would help | The row for that rule, then only those PDF pages |
| Run configuration | `run-config.md` | Every stage, at the start | Full file |
| TeX Live setup | `texlive-setup.md` | At setup, and when a build tool is missing (03 to 05, 08) | "Verify" first; install steps only if needed |
| LaTeX conventions | `latex/latex-conventions.md` | Writing or building any `.tex` (02 to 05, 08) | Full file |
| Layout package | `latex/defn.sty` | Generating macros (02), building (08) | Comments at the head of each block |
| Templates | `latex/book-template.tex`, `latex/chapter-preview.tex` | Previews (03 to 05), the final build (08) | Full file |
