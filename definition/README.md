# A Standard Definition of Elm?

The LaTeX sources of *A Standard Definition of Elm?* (Draft version 0.3), a formal definition of the
Elm language, and the PDF of that edition. The website (`site/`) shows the book with a page for every
rule; `runner/definition-data.js` turns these sources into the site's data.

```
tex/standard-elm-definition.tex   the master file: title, edition and the order of the chapters
tex/*.tex                         the preface, chapters and appendices
tex/defn.sty                      the layout of a formal definition: rules, rule groups, comments,
                                  grammar, semantic object and derived form tables
tex/macros.sty                    the book's notation, one macro per symbol
standard-elm-definition-*.pdf     the PDF of this edition
```

The book is written with the `pl-definition-writer` workspace of icm-agents, which keeps its
working files (survey, rulings, audits, Lean mechanisation) and typesets the PDF; these files are a
copy of its output for this edition. To publish a new edition, replace `tex/` and the PDF with the new output.

## The website data

```sh
pnpm install                          # once: KaTeX, among the other packages
node runner/definition-data.js        # writes site/data-standard/ and site/public/downloads/
```

The converter reads the commands and environments of `defn.sty` and the standard LaTeX the book
uses, and renders every formula with KaTeX using the macros of `macros.sty`. Anything it does not
understand, any formula KaTeX cannot render and any reference to a missing label is listed, and the
exit status is then 1, so a construct new to the book is noticed rather than shown wrongly.

With `--check-aux <dir>` it also compares the numbers it gives chapters, sections, figures and rules
with those in the `.aux` files of a LaTeX build of the same sources:

```sh
node runner/definition-data.js --check-aux <latex build dir>
```

Rule pages are addressed by the rule's label without its `r:` prefix
(`\defnrule[r:d-atexp-var]` is `/standard/rules/d-atexp-var`), so a rule keeps its address when
rules are renumbered. A label, once published, should not change.

Three other kinds of item have labels and pages of their own, given with `\citelabel` of `defn.sty`
where the item is stated:

| Item | Label | Page |
|------|-------|------|
| A syntactic or further restriction | `res:core-no-float-pattern` | `/standard/restrictions/core-no-float-pattern` |
| A derived form | `df:if` | `/standard/derived-forms/if` |
| An entry of the initial basis: a type with its constructors, or a value (an operator under the hidden variable it stands for) | `b:Platform.Cmd.none` | `/standard/basis/Platform/Cmd/none` |

Each of these items, every rule and every chapter also has a Discussions section on the site: a
discussion in the *Standard* category of the repository's GitHub Discussions is shown on an item's
page when its title holds the item's label in square brackets, `[r:d-atexp-var]` (for a chapter,
`[ch:static-core]`). This is another reason a published label does not change: the discussions
about an item are attached to it by its label.

An entry of the basis is labelled at its row in the static basis (Appendix C); `\citealso` marks
its row in the dynamic basis (Appendix D). Its page collects those rows, the definition of its
`APPLY` and its text in Elm. In the chapters, each item has an anchor (the label with `:` and `.` as
`-`) and a link to its page.

## Licence

The text of the Definition, as LaTeX and as PDF, is licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/): it may be shared and adapted for any
purpose, with credit, a link to the licence and a note of any changes. See [LICENSE](LICENSE). The
repository's BSD 3-Clause licence covers its code. Every page of the book on the website states the
licence.
