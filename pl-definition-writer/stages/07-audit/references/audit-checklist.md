# Audit Checklist

Whole-book checks. Each stage's own audit already checked its chapter alone;
these checks look across chapters. Cite definition-style rule IDs (S1, R3)
in findings.

## Checks

### A1 Notation

- Every macro used in any chapter is defined in `macros.sty` or `defn.sty`.
  Method: collect every `\name` used; subtract both packages and the LaTeX
  and amsmath commands in use.
- No registered symbol is written raw (e.g. `\tau` where the registry gives a
  macro for that metavariable's class, or a hand-typed judgment).
- Every registry row is used somewhere. Unused rows are minor findings.

### A2 Definitions Before Use

- Walk the chapters in Chapter Order. Every semantic class, operation and
  convention is defined before its first use (O1, O6, R1, D2).
- Nothing in a lower level mentions a higher level (S3).

### A3 Coverage

- Every bare production in every grammar figure is covered by a static rule
  and, where it survives reduced syntax, a dynamic rule (R3, D1).
- Every construct in the survey is in a grammar figure, a derived form, or the
  plan's Out of Scope list.
- Every derived form's equivalent is bare or earlier (B4).
- Every identifier in the survey's "Initial Basis" is in both basis
  appendices (I2).

### A4 Rulings

- Every ambiguity entry has a `% A<n>` citation somewhere in the book, or is
  marked in the log as affecting nothing written. Check the cited text
  matches the ruling.

### A5 Numbering and References

- Rule numbers run 1 to N with no gap or repeat across the whole book (S7).
- Every `\ruleref`, `\ref` and `\eqref` has a matching `\label`; every label is
  unique and follows the label scheme.
- Every Comment cites a rule in its own group (C1).

### A6 Static and Dynamic Agreement

- Every dynamic chapter's reduced syntax removes exactly the type-only phrases
  (D1).
- Objects shared between static and dynamic chapters (identifiers, status
  descriptors, environments' shape) are defined once and agree.

### A7 Voice

- Search for hedging words ("usually", "typically", "should", "might",
  "probably"); check each against Hard Constraint 1.
- Search for banned terms from the Terminology table.
- Search for em dashes (`---` in LaTeX source, and the Unicode character).
- Search for implementation talk outside the introduction (Hard Constraint 3).

### A8 Build Health

- Compile every chapter preview; record errors and undefined references other
  than cross-chapter ones.

## Severity

| Severity | Meaning |
|----------|---------|
| Blocker | The book is wrong or incomplete: a missing rule, an undefined object, a broken ruling, a build error |
| Major | A form rule broken in a way a reader would notice: unnumbered rule, paraphrasing Comment, raw notation |
| Minor | Polish: unused registry row, wording, long Comment |

## Report

```
# Audit Report: <Title>

## Summary
Chapters audited, findings by severity, chapters ready to mark audited.

## Findings
| ID | Severity | Chapter:line | Check / Rule | Finding | Owner Stage | Disposition |
| F1 | Blocker | static-core.tex:212 | A3, R3 | No rule for `exp : ty` | 04 | |

## Carried From Mechanisation
| Item | Owner Stage | Disposition |
```

Number findings F1, F2, ... Dispositions are filled at the checkpoint.
