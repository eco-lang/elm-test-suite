# PL Definition Writer

Writes a formal definition of a programming language, in the form of *The
Definition of Standard ML*, from an existing implementation and its design
notes: grammar, semantic objects, numbered inference rules and Comments, in
LaTeX, built to PDF.

This copy writes *A Standard Definition of Elm?* and lives in the
`elm-test-suite` repository. The workspace holds only the agent's
instructions, which should rarely change. Everything the stages produce (the
survey and rulings, the book's LaTeX, the mechanisation, the audits and the
PDF) goes to the output tree `../definition/`, which changes with the
definition and the tests; see `shared/run-config.md` "Output Tree".

## Folder Map

```
elm-test-suite/
├── pl-definition-writer/  (this workspace: instructions only)
└── definition/            (the output tree: everything the stages write)
    ├── survey/            (01: book brief, language survey, ambiguity log)
    ├── architecture/      (02: book plan and checklist, notation registry, its generator)
    ├── tex/               (02, 03 to 05, 08: the book's LaTeX sources, read by the website)
    ├── mechanisation/     (06: the encoding and its report)
    ├── audit/             (07: audit reports)
    ├── typeset/           (08: build report, earlier editions, build folder)
    └── <slug>-<stamp>.pdf (08: the current edition)

pl-definition-writer/
├── CLAUDE.md          (you are here)
├── CONTEXT.md         (start here for task routing)
├── setup/             (onboarding questionnaire)
├── shared/            (definition style, prose style, values, exemplar index, run config, latex/)
├── skills/            (bundled latex build skill)
└── stages/
    ├── 01-survey/          (read the implementation and notes; rule on ambiguities)
    ├── 02-architecture/    (grid, bare vs derived, chapter plan, notation registry, macros.sty)
    ├── 03-syntax/          (syntax chapter per level, derived forms appendix)
    ├── 04-semantics/       (one static or dynamic chapter per run)
    ├── 05-framing/         (preface, introduction, grammar and basis appendices)
    ├── 06-mechanisation/   (optional: encode and test the rules)
    ├── 07-audit/           (whole-book consistency report)
    └── 08-typeset/         (assemble and build the PDF)
```

## Triggers

| Keyword | Action |
|---------|--------|
| `setup` | Run onboarding questionnaire |
| `status` | Show pipeline and chapter completion |
| `next` | Run the next piece of work: the first stage, or chapter, that is not done |

### How `status` works

A stage is COMPLETE if its main output exists in the output tree, otherwise
PENDING:

| Stage | COMPLETE when this exists |
|-------|---------------------------|
| 01 | `../definition/survey/ambiguity-log.md` |
| 02 | `../definition/architecture/book-plan.md` and `../definition/tex/macros.sty` |
| 03, 04, 05 | Every row of the Chapter Checklist owned by the stage is `drafted` or `audited` |
| 06 | `../definition/mechanisation/mechanisation-report.md` |
| 07 | `../definition/audit/audit-report.md` |
| 08 | `../definition/typeset/build-report.md` and a PDF in `../definition/` |

Then print the Chapter Checklist from `../definition/architecture/book-plan.md`
with counts of pending, drafted and audited. Render:

```
Pipeline Status: pl-definition-writer

  [01-survey] --> [02-architecture] --> [03-syntax] --> [04-semantics] --> [05-framing]
     STATUS            STATUS              STATUS           STATUS            STATUS
  --> [06-mechanisation] --> [07-audit] --> [08-typeset]
          STATUS               STATUS          STATUS

Chapters: N pending, N drafted, N audited
```

### How `next` works

If 01 or 02 is PENDING, run it. Otherwise take the first chapter in Chapter
Order that is `pending` and run its stage (03, 04 or 05). When every chapter is
drafted, run 06 if it exists, then 07, then 08.

## Routing

| Task | Go To |
|------|-------|
| Survey the language | `stages/01-survey/CONTEXT.md` |
| Plan the book and notation | `stages/02-architecture/CONTEXT.md` |
| Write syntax chapters | `stages/03-syntax/CONTEXT.md` |
| Write a semantics chapter | `stages/04-semantics/CONTEXT.md` |
| Write preface, introduction, appendices | `stages/05-framing/CONTEXT.md` |
| Mechanise the rules | `stages/06-mechanisation/CONTEXT.md` |
| Audit the whole book | `stages/07-audit/CONTEXT.md` |
| Build the PDF | `stages/08-typeset/CONTEXT.md` |

## What to Load

| Task | Load These | Do NOT Load |
|------|-----------|-------------|
| Survey | 01 CONTEXT and references, `shared/run-config.md` | Any style file; nothing is being written yet |
| Architecture | 01 outputs (`definition/survey/`), 02 references, the style sections the 02 CONTEXT names | The exemplar beyond the pages indexed; implementation source |
| Syntax or semantics chapter | The rows the stage CONTEXT names; only the target level's survey sections | Other chapters' text, except the object figures a dependency defines; the implementation source |
| Framing | 02 outputs (`definition/architecture/`), chapter figures and rule numbers | Full chapter prose |
| Audit | All chapters, registry, plan, survey, log, checklist | The exemplar; the implementation source |
| Typeset | Plan, chapters as files to copy, build guide, latex skill | Chapter contents beyond build errors |

## Rules That Hold Everywhere

- `shared/definition-style.md` decides form; `../definition/architecture/notation.md` decides notation. Nothing overrides either.
- Agents never learn style from other chapters' output. Docs over outputs.
- No silent decisions about the language: a new question becomes an ambiguity log entry and a checkpoint.
- The exemplar is copyright: read it for form, never copy its text.

## Stage Handoffs

Each stage writes its output to its folder of the output tree
(`../definition/`, table in `shared/run-config.md` "Output Tree"), and the
next stage reads from there. The chapter stages 03 to 05 all write to
`../definition/tex/`, which is the single copy of the book's text. If you edit
an output file, the next stage picks up your edits. Stages 03 to 05 and 07
also advance the Chapter Checklist in `../definition/architecture/book-plan.md`.

The website is built from the output tree (`runner/definition-data.js` reads
`definition/tex/` and the current PDF). After a stage changes the book,
rebuild the site data as the repository README describes.
