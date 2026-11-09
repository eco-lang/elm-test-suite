# PL Definition Writer

Formal definitions of programming languages, from survey to printed book.

## Task Routing

| Task Type | Go To | Description |
|-----------|-------|-------------|
| Survey | `stages/01-survey/CONTEXT.md` | Read the implementation and notes; log and rule on ambiguities |
| Architecture | `stages/02-architecture/CONTEXT.md` | Grid, bare and derived forms, chapter plan, notation registry |
| Syntax | `stages/03-syntax/CONTEXT.md` | Lexis, grammar figures, restrictions, derived forms appendix |
| Semantics | `stages/04-semantics/CONTEXT.md` | Objects, numbered rules and Comments, one chapter per run |
| Framing | `stages/05-framing/CONTEXT.md` | Preface, introduction, full grammar and basis appendices |
| Mechanisation | `stages/06-mechanisation/CONTEXT.md` | Optional: encode the rules and test against the implementation |
| Audit | `stages/07-audit/CONTEXT.md` | Cross-chapter consistency report |
| Typeset | `stages/08-typeset/CONTEXT.md` | Assemble and build the PDF |

## Shared Resources

| Resource | Location | Contains |
|----------|----------|----------|
| Output tree | `../definition/` | Everything the stages write; folder by stage in `shared/run-config.md` "Output Tree" |
| Shared context | `shared/CONTEXT.md` | Routes to the definition style, prose style, value framework, exemplar index, run config and LaTeX files |
| Bundled skills | `skills/CONTEXT.md` | The latex build skill, its provenance and scope |
| Onboarding | `setup/questionnaire.md` | House settings asked once at setup |
