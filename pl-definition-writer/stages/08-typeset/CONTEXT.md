# Stage 08: Typeset

Assemble every chapter into one master document and build the book's PDF.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| Stage 01 | `definition/survey/book-brief.md` | "Title", "Slug", "Authors", "Year", "Edition" rows | Title page and file names |
| Stage 02 | `definition/architecture/book-plan.md` | "Chapter Order", "Chapter Checklist" | What to include, in what order |
| Stage 02 | `definition/tex/macros.sty` | Copied into the build | Notation |
| Stages 03 to 05 | `definition/tex/` | Every `.tex` named in Chapter Order | The book |
| Config | `../../shared/run-config.md` | "Typesetting" | Engine and paper size |
| Shared | `../../shared/latex/book-template.tex`, `../../shared/latex/defn.sty` | Full files | Master skeleton and layout |
| Reference | `references/build-guide.md` | Full file | Assembly, build and report |
| Shared | `../../shared/texlive-setup.md` | "Verify"; the rest only if a tool is missing | Installing TeX Live and latexmk |
| Skill | `../../skills/latex/SKILL.md` | "Critical Rules", Phases 1 to 4 and 6 only | Fail-closed build, compile-fix loop, box report, quality score |

## Process

1. Check the build tools, as `../../shared/texlive-setup.md` "Verify" describes. Stop and point the user to the guide if any is missing.
2. Report any chapter in Chapter Order whose checklist status is not `audited`. Build anyway if the user agrees; the report records it.
3. Write the master document and assemble the build folder as `build-guide.md` "Assemble" describes.
4. Build with the latex skill's compile-fix loop. A fix the skill would make inside a chapter is not made here: record it as a finding for the stage that owns the chapter.
5. Produce the skill's final report, box report and quality score, and add the checks in `build-guide.md` "Book Checks".
6. Publish the PDF as `definition/<slug>-<stamp>.pdf` (stamp from the brief's Edition), as `build-guide.md` "Publish" says, and write the build report.

## Audit

| Check | Pass Condition |
|-------|---------------|
| Complete | Every file in Chapter Order is included exactly once |
| Clean | Zero errors and zero undefined references or citations |
| Numbering | Rules run 1 to N in the PDF with no gaps, and figures are numbered through the book |
| Untouched | No chapter source was edited by this stage |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Master document | `definition/tex/<slug>.tex`, with `definition/tex/defn.sty` | The book's master file and layout package, beside the chapters |
| Build folder | `definition/typeset/build/` | A copy of `definition/tex/`, `.latexmkrc` and `out/`; rebuilt every time, not a source |
| Book | `definition/<slug>-<stamp>.pdf` | PDF, named by edition; earlier editions in `definition/typeset/editions/` |
| Build report | `definition/typeset/build-report.md` | `build-guide.md` "Report" |
