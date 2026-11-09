# Build Guide

How stage 08 assembles and builds the book. The compile-fix loop, box report
and quality score come from the bundled `skills/latex` skill; this file covers
what is specific to this workspace.

## Assemble

The book's sources live in `definition/tex/`: the chapters (stages 03 to 05),
`macros.sty` (stage 02), and the master document and `defn.sty`, which this
stage writes there. The website reads the same folder, so it must always hold
a complete, buildable book.

1. Copy `shared/latex/defn.sty` to `definition/tex/defn.sty`.
2. Copy `shared/latex/book-template.tex` to `definition/tex/<slug>.tex` and
   fill every line marked FILL:
   - the `% !TEX program =` line from run-config "TeX engine";
   - the paper size option from run-config "Paper size";
   - title, edition, authors and year from the book brief (the edition appears
     in brackets under the title and in the PDF metadata title);
   - one `\include{<file>}` per chapter in Chapter Order, framing first,
     appendices after `\appendix`;
   - delete the example comment lines once filled.
   If the master already exists and the brief and Chapter Order are
   unchanged, keep it.
3. Work in `definition/typeset/build/`. Empty it first; it is rebuilt from
   sources every time and is never a source itself. Copy every file of
   `definition/tex/` into it.
4. Copy `skills/latex/templates/build-config/.latexmkrc` into it, unchanged.
   Nothing else may be added to `.latexmkrc`; the skill's Critical Rule 1
   explains why.
5. If the book cites sources, put the `.bib` file in `definition/tex/` (so it
   is copied with the rest) and add the bibliography lines to the master; the
   skill's Phase 5 citation audit then applies.

## Build

From `definition/typeset/build/`, follow the skill's Phase 2 with
`latexmk <slug>.tex`. The skill writes auxiliary files to `out/` and copies
the PDF back beside `<slug>.tex`.

Skip the skill's Phase 2.4 (paper backup), Phase 6.1 (output manifest) and
breadcrumb steps: they rely on files this workspace does not have.

**Fix boundary.** The skill may add a package to the master document or fix
the master's preamble; make that fix in `definition/tex/<slug>.tex`, not in
the build folder's copy. It may not edit a chapter file: a chapter error is a
finding for the owning stage (03, 04 or 05), which fixes the chapter in
`definition/tex/`, and the build folder is then assembled again.

## Publish

The published PDF is named `<slug>-<stamp>.pdf`, where the stamp is the
brief's Edition in lower case with spaces as hyphens and the word "version"
dropped (`Draft version 0.1` gives `draft-0.1`), so that circulated drafts
cannot be mistaken for one another.

Copy the built PDF to `definition/<slug>-<stamp>.pdf`. `definition/` holds
the PDF of the current edition only, because the website publishes the one
PDF it finds there. When the edition changes, first move the previous
edition's PDF into `definition/typeset/editions/`; never overwrite it.

## Book Checks

After a clean build, add these to the skill's report:

- **Rule sequence.** Extract the rule numbers in order from the PDF text
  and check they run 1 to N. Rule tags are the lines that hold nothing but
  `(n)`; Comment entries also start with `(n)`, so do not match those:
  `pdftotext <slug>.pdf - | grep -oE '^\([0-9]+\)$'`.
- **Figure sequence.** Figure captions run 1 to M through the book.
- **Contents.** The table of contents lists every chapter in Chapter Order.
- **Page count** and the page each chapter starts on.

## Report

```
# Build Report: <Title>

## Status
| Field | Value |   (status, iterations, pages, warnings, boxes, engine)

## Chapters
| Chapter | Checklist Status | Start Page |

## Book Checks
Rule sequence, figure sequence, contents: pass or the problem.

## Findings for Other Stages
| Chapter | Problem | Owner Stage |

## Box Report
(from the skill)

## Quality Score
(from the skill)
```
