# Run Configuration

House settings that stay the same from book to book. Set once by `setup`.
Book-specific facts (title, authors, language, source paths) are not here:
the survey stage collects them at the start of each book, in its book brief.

## Output Tree

This workspace holds only instructions. Everything a stage writes goes to the
book's output tree, `definition/` at the root of the repository that holds
this workspace (`elm-test-suite/definition/`, which is `../definition/` from
the workspace folder and `../../../definition/` from a stage folder). Paths
in the stage files that start `definition/` are in this tree. Nothing is
written inside the workspace, and the workspace has no `output/` folders.

| Folder | Written by | Holds |
|--------|-----------|-------|
| `definition/survey/` | 01 | `book-brief.md`, `language-survey.md`, `ambiguity-log.md`, `drafts/` |
| `definition/architecture/` | 02 | `book-plan.md` (with the Chapter Checklist), `notation.md`, `gen_notation.py`, `requests/` |
| `definition/tex/` | 02, 03, 04, 05, 08 | The book's LaTeX sources: `macros.sty` (02), the chapters (03 to 05), the master `<slug>.tex` and `defn.sty` (08) |
| `definition/mechanisation/` | 06 | The encoding, its README and example run, `mechanisation-report.md` |
| `definition/audit/` | 07 | `audit-report.md`, `drafts/` |
| `definition/typeset/` | 08 | `build-report.md`, `editions/` (PDFs of earlier editions), `build/` (rebuilt every time) |
| `definition/` | 08 | `<slug>-<stamp>.pdf`, the PDF of the current edition |

`definition/tex/` is the single copy of the book's text. The website
(`runner/definition-data.js`) reads it and the current PDF, so a stage that
writes a chapter there publishes it at the next site build. Edit a chapter in
place; never keep a second copy of it elsewhere.

## Writing

- **Spelling:** British
- **Exemplar PDF:** `/home/rupert/sc/gitlab/icm-agents/sml97-defn.pdf`

## Typesetting

- **TeX engine:** pdflatex
- **Paper size:** a4paper
- **Preview builds:** stages 03 to 05 compile each chapter on its own with
  `shared/latex/chapter-preview.tex` before writing it to `definition/tex/`.

## Mechanisation

- **Tool:** Lean 4
- **Example corpus:** every example is a test program of this repository's
  `tests/` (most of them in `tests/elm/` and `tests/elm-core/`), translated by
  hand into the encoding, with its expected values copied from the test's
  `-- CHECK:` lines. No example is taken from another implementation's test
  suite, from the survey or from the book's text alone: an example the
  mechanisation needs that no test provides is first written as a test (tagged
  `elm-spec`, with its expected values the book's), and then translated. The
  site's build compares each translation's expected values with its test's
  CHECK lines and reports a difference.
