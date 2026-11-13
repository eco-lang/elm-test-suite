# Site content

The site's prose, as Markdown, rendered by `src/Content.elm` with dillonkearns/elm-markdown. The
book itself (its chapters, rules, figures and basis) is not here: it is generated from
`definition/tex/` by `runner/definition-data.js`.

| File | Page |
|---|---|
| `about.md` | `/about`, the whole page |
| `results.md` | `/results`, the introduction |
| `discussions.md` | `/discussions`, the title and introduction |
| `standard/front.md` | `/standard`, the text around the title and contents |
| `standard/rules.md`, `restrictions.md`, `derived-forms.md`, `basis.md`, `figures.md` | the introductions of the book's lists |
| `standard/discussions.md` | `/standard/discussions`, the introduction |
| `standard/proofs.md` | `/standard/proofs`, the text above the theorems, with the coverage tables |
| `standard/generated.md` | `/standard/proofs/kc`, the account of the generated theorems |

What the renderer adds to Markdown:

- `{{name}}` is replaced by a value the page computes (a count, a version, a URL). The names a page
  provides are in its view, where it calls `Content.view`.
- The paragraphs that open a page, after its `#` title if it has one, are its lede.
- On the test-suite pages (not the book's), each `##` heading starts a section.
- `<slot name="x"></slot>` places something the page computes: a table, the book's buttons.
- `<button-link href="/standard" text="Text"></button-link>` is a button (`quiet="true"` for a quiet
  one); put buttons in `<actions>` to set them in a row.
- `<note class="sd-draft-note">`, blank line, Markdown, blank line, `</note>` is a box of that
  class.
- A link to an address starting with `http` opens in a new tab.

A file that does not parse, or uses another HTML element, fails the site's build with its name.
