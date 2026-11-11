# Build Report: A Standard Definition of Elm? (Draft version 0.3)

Changes since Draft 0.2: Bytes is a port and flags payload type (A92, author); `min`, `max` and `clamp` at Float are IEEE 754-2019 `minimum`/`maximum` and `min (max x lo) hi` (A48, A49, author); every module has a header (A16, A30 amended by the author); A43 confirmed. Two new rules (encoding and decoding of Bytes), so 194 rules.

Rebuilt on 2026-11-09 after revisions to the same edition: six new syntactic restrictions in Chapter 2 (`core-escape-unicode`, `core-constant-separated`, `core-adjacent-items`, `core-layout-rule`, `core-identifier-characters`, `core-operator-chain`), so 39 restrictions; `Char.toCode` and `Char.fromCode` in the initial bases (Appendices C and D) and the Char requirement in Appendix E; and the preface's account of the mechanisation. The number of rules (194) and figures (60) is unchanged; the book has one more page. The build now runs in `definition/typeset/build/`, assembled from `definition/tex/`.

Rebuilt on 2026-11-10 after ruling A27 was revised: a `number` variable that nothing fixes is now Float, and the default copy of number specialisation is the copy at Float (restriction `core-number-default` and the closure of groups in Chapter 4, number specialisation and the comment on `r:d-atexp-scon` in Chapter 6, Dflt in Chapter 9, the copies of `abs` in Appendix D, and two rows of Appendix E's Evaluation table). Then, the same day: Appendix E's introduction states what conformance requires of a program the definition gives no value (A94), a new section "Number Specialisation" records the requirement to close a free `number` to Float and how Elm/JS and eco make and evaluate copies, and the A56 and A87 rows leave the list of divergences. Then: the defaulting rule names annotations as binders (A27); Chapter 4 gains a section "Principal Derivations" with a property, and the defaulting of `number` moves from Chapter 4's further restrictions to the start of number specialisation in Chapter 6 (A95), so the book has 38 restrictions. Then: the further restrictions of Chapters 4 and 5, and the type of `main` in Chapter 9, are judged on the principal derivation, which Section "Principal Derivations" now defines for phrases and modules as well as programs, with examples of why no other derivation will do (A96); the Standard ML comparison's row on incomplete matches says so. Then: the inhabitants of a type may be infinite (the clauses are read coinductively), so `Never` and `type V = V V` have inhabitants, every type has one, and the further restrictions give the same answer in every derivation; the examples of A96 in "Principal Derivations" give way to that fact (A97). The book has 186 pages. Then, after the third review (definition/audit/audit-report.md, round 3): Principal Derivations moves after the Inference Rules (now Section 4.10) and is stated for Core phrases, with a new Section 5.6 for modules (generated type names renamed); Chapter 9 takes each module premise from a principal derivation and checks the flags type before the default; defaulting exempts type-declaration parameters; Appendix E's statement of A94 is limited to programs without a meaning, and two divergence rows return (A56, A87 in a step of a running program). The book has 187 pages, 194 rules, no warnings and the same 3 overfull boxes. Rules (194) and figures (60) are unchanged; the book had 185 pages. The same 3 overfull boxes, no warnings.

## Status

| Field | Value |
|-------|-------|
| Status | Clean |
| Engine | pdflatex (run-config), via latexmk with the latex skill's canonical `.latexmkrc` (byte-identical) |
| Iterations | 1 of 5 (no fixes needed) |
| Pages | 185 |
| LaTeX/package warnings | 0 (no undefined references, no multiply defined labels, no font substitutions) |
| Typographic boxes | 3 overfull (5.3pt, 4.5pt, 1.4pt); 26 underfull (ragged-right table cells and float pages) |
| Fixes applied | none in the build. A 59pt overfull line from the new `Char.fromCode` row of the APPLY figure for conversions was fixed at source, in `appendix-dynamic-basis.tex` (owner stage 05), by setting its side condition on two lines |
| Unresolved errors | none |
| Output | `definition/standard-elm-definition-draft-0.3.pdf` (Draft version 0.3; copied from `build/`). Drafts 0.1 and 0.2 are kept, unchanged, in `definition/typeset/editions/` |

## Chapters

All chapters were `audited` in the checklist when the book was first built. The revisions of 2026-11-09 to `syntax-core`, `appendix-static-basis`, `appendix-dynamic-basis`, `appendix-implementation` and `preface` were made directly and have not been through a stage 07 audit; the checklist still shows them `audited`.

| Chapter | Checklist Status | Start Page |
|---------|------------------|------------|
| preface | audited | vii |
| introduction | audited | 1 |
| syntax-core | audited | 4 |
| syntax-modules | audited | 16 |
| static-core | audited | 23 |
| static-modules | audited | 40 |
| dynamic-core | audited | 52 |
| dynamic-modules | audited | 65 |
| effects | audited | 74 |
| programs | audited | 89 |
| appendix-derived-forms | audited | 103 |
| appendix-full-grammar | audited | 109 |
| appendix-static-basis | audited | 114 |
| appendix-dynamic-basis | audited | 123 |
| appendix-implementation | audited | 143 |
| appendix-standard-ml | audited | 165 |

## Book Checks

- **Rule sequence:** pass. Rules (1) to (194), each exactly once (pdftotext reads some side-by-side rules out of order; the set is 1 to 194 with none missing or repeated) (by chapter: static-core 1 to 45, static-modules 46 to 64, dynamic-core 65 to 112, dynamic-modules 113 to 132, effects 133 to 171, programs 172 to 194).
- **Figure sequence:** pass. Figures 1 to 60 through the book, none missing.
- **Contents:** pass. Every chapter in Chapter Order appears in the table of contents, in order.

## Findings for Other Stages

| Chapter | Problem | Owner Stage |
|---------|---------|-------------|
| static-modules (near page 42) | Two overfull lines, 5.3pt and 4.5pt (source lines 185 and 194 of the included file) | 04 (cosmetic: reword or allow a break) |
| appendix-dynamic-basis (near page 134) | One overfull line, 1.4pt, in the APPLY display for the trigonometric functions | 05 (cosmetic) |

## Box Report

| Overflow | Location |
|----------|----------|
| 5.3 pt | static-modules, line 185 |
| 4.5 pt | static-modules, line 194 |
| 1.4 pt | appendix-dynamic-basis, line 796 |

Underfull boxes: 26, all from ragged-right `p{}` table columns (Appendix E) and float-only pages; none affects legibility. Per the skill, prose was not reworded to close boxes.

## Source Pathologies

No source pathologies detected (all nine detectors: spacing hacks, vertical-rhythm surgery, line breaks in headings or captions, forced floats, shrink-to-fit, tiny-table typography, absolute positioning, fixed widths, label before caption). `chktex` and `latexindent` are not installed.

## Citation Audit

Not applicable: the book has no bibliography.

## Quality Score

| Metric | Value |
|--------|-------|
| **Score** | 84 / 100 |
| **Verdict** | Revise (cosmetic only) |

### Deductions

| # | Issue | Tier | Deduction | Category |
|---|-------|------|-----------|----------|
| 1 | Overfull hbox 1 to 10pt, 3 instances | Minor | -6 | Typography |
| 2 | Underfull boxes, 26 instances (cap) | Minor | -10 | Typography |
| | **Total deductions** | | **-16** | |

The verdict comes entirely from box messages; there are no errors, warnings, broken references or rendering problems.
