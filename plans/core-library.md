# Plan: a Core Library page, specifying elm/core against the book

**Status (2026-11-13): step 3 done, in the form of [library-elm-texts.md](library-elm-texts.md)**
(decision D2 of [lean-full-definition.md](lean-full-definition.md)): the Elm texts of the 12 library
values the tests name are values of the dynamic test basis, not a prelude added to each program,
and 28 of the 29 tests of group D are translated and proved. The site pages (steps 1 and 2, and
step 3's coverage table) are not started.

## Why

The Definition of Standard ML has a companion, *The Standard ML Basis Library* (Gansner and Reppy,
eds., Cambridge University Press, 2004; online at sml-family.org/Basis). The Revised Definition
(1997) keeps its own initial basis close to what the language needs and leaves the rest of the
library to the companion, which is a reference manual of signatures and English, not formal.

A Standard Definition of Elm? already draws the same line. Appendix C's "Library functions"
paragraph (`definition/tex/appendix-static-basis.tex`) puts every function of List, String, Tuple,
Array, Maybe and Result, and the Char functions apart from `toCode` and `fromCode`, outside the
definition. Section "Values Written in Elm" of Appendix D defines a value of the basis by its
elm/core 1.0.5 text, and already does so for `List.foldr`, which `Task.sequence` needs.

What is missing is a specification of the rest of elm/core. Without one, the tests that use a
library function only incidentally cannot be checked against the book (group D of
[untranslated-tests.md](untranslated-tests.md), 28 tests, mostly number specialisation and record
narrowing), and nothing says what a conforming implementation's `List.sortBy` or `String.slice`
must do. Putting it in the book would roughly double the appendices for material that is not the
language.

Elm has an advantage SML did not: most of elm/core is written in Elm, and the book already gives
Elm text a meaning. So the companion can be formal at small cost.

## What it is, and is not

- **A part of the website, not a book.** A new "Core Library" section of the site, in web form:
  one page per module, laid out like package documentation, with code blocks, anchors per value
  and cross-links. No LaTeX source, no PDF.
- **Not part of the definition.** It specifies elm/core 1.0.5 in terms of the book. The book
  stays the definition of the language. The book changes by one sentence: Appendix C's "Library
  functions" paragraph says where the library is specified (the site's Core Library page), as the
  Revised Definition points to the Basis Library.
- **Pinned to elm/core 1.0.5**, the version the book cites throughout.

## Scope

| Modules | In this plan |
|---------|--------------|
| Maybe, Result, Tuple | yes, first (Elm text only, no kernel) |
| List | yes (Elm text, and 7 kernel functions: `map2` to `map5`, `sortBy`, `sortWith`, and `cons`, which is `::`) |
| Char | yes (Elm text, and the case conversions; `toCode`, `fromCode` are in the book) |
| Dict, Set | yes (Elm text only) |
| Bitwise | yes (7 kernel functions) |
| Array | yes, after Bitwise (Elm text over `Elm.JsArray`, a hidden module of 15 kernel functions) |
| String | yes, last (33 kernel references; most dependent on the implementation) |
| Basics, Debug | the book has them; their pages link to the book's basis pages |
| Platform, Platform.Cmd, Platform.Sub, Task, Process | no: effects, Chapters 8 and 9; what the book needs of them is in the book |
| elm/json, elm/html, elm/bytes, others | no |

## The three kinds of value

Every exposed value of a module in scope is one of these, and its page says which.

1. **In the book.** The value is in the initial basis (Appendices C and D). The entry gives its
   type and links to its page under `/standard/basis/`. Nothing is restated.
2. **Elm text.** The value's elm/core 1.0.5 definition is written in Elm. The definition *is* that
   text, read under the book's dynamic semantics, in an environment built as Appendix D builds
   `E_modid`: the module's imports, the values of the basis, and the further library values the
   text names, each by its own entry. The entry shows the text as it stands in the file, with a
   link to the file and line at the `1.0.5` tag, and links from each library value it names to that
   value's entry.
3. **Kernel.** The value's definition refers to `Elm.Kernel.*`. The entry gives a specification,
   preferably a **model text**: a definition written in Elm, over the book's basis and earlier
   library values, marked as a model and not elm/core's text. For example `List.map2` as a
   recursion on two lists, or `List.sortBy` as a stable insertion or merge sort. A model text has
   three advantages: it reads like the rest of the page; the book already gives it a meaning; and
   the translator and the Lean mechanisation handle it as they handle Elm text, with no new APPLY
   cases. Where a model text would not say what the implementation does, the entry states it
   instead in a short display (KaTeX, which the site already renders), as Appendix D does for the
   basic values. Examples: Bitwise's 32-bit truncation; String's indices counted in UTF-16 code
   units.

Each entry may also have **implementation notes**: what the specification leaves to the
implementation, and what Elm/JS and eco do there. These are in the form of Appendix E's tables,
and link to Appendix E where it already covers the point (Char and String, A52 and A53).

### String needs a decision first

String is the hardest module. The book's model of a string must be fixed against Appendix E's
"In both, `String.length` and string indices count UTF-16 code units". A model of `String` over
`String.toList` and `String.fromList` would count characters, not code units, and so would be
wrong for `length`, `slice`, `left`, `indexes` and the rest on text above U+FFFF. Before String is
specified, decide one of:

- a model over a hidden `String.toUnits` / `fromUnits` (UTF-16 code units as Ints), with the
  character functions defined from them; or
- character-based models, with the code unit counting stated as implementation-dependent.

The first is faithful to both implementations; the second is simpler but specifies less.

## The web pages

- **Navigation.** A "Core Library" link in the site header (`site/app/Shared.elm`), between
  "Standard" and "Results".
- **`/core`.** An index of the modules in scope. For each: one line on what it is, and counts of
  its values by kind (book, Elm text, kernel), and of the tests and mechanised checks that use it.
- **`/core/<Module>`.** One page per module, ordered as elm/core's documentation orders it (its
  `@docs` lines). Each value has an anchor (`/core/List#map2`) and shows:
  - its type annotation, in Elm syntax as elm/core writes it (the page header links once to
    Appendix C for how an annotation reads as a type scheme);
  - a badge for its kind, and its definition (Elm text, model text, or display);
  - "uses": the library values its definition names, linked;
  - implementation notes, if any;
  - "tests": the `elm-spec` tests that use the value, linked to their test pages, with how many of
    their checks the mechanisation proves.
- **elm/core's own documentation.** elm/core is BSD-3-Clause, so its doc comments may be shown
  with its copyright notice. Show each value's doc comment, collapsed under the definition, and
  the notice in the page footer. The specification is the definition, not the doc comment.

## Data

- **Vendor elm/core 1.0.5** into `definition/library/elm-core-1.0.5/` (the `src/` files of the
  modules in scope, `Elm/JsArray.elm`, and its `LICENSE`), so that the site build does not depend
  on an `ELM_HOME` cache on Netlify. Only the Elm files; the kernel JavaScript is not needed.
- **Kernel specifications** in `definition/library/kernel/<Module>.md`, the hand-written edit
  surface: one section per kernel value, holding its model text (a fenced `elm` block), or its
  display, and its implementation notes.
- **An extractor**, `definition/tools/src/Library.elm` (an elm-pages script, like the
  translator). It parses the vendored files with elm-syntax and, for each exposed value, takes
  its annotation, doc comment, source text and position, and the qualified values its text names.
  It classifies the value: kernel if its text names `Elm.Kernel.*`, book if Appendix C's index
  (from `runner/definition-data.js`'s output) has it, Elm text otherwise. It joins the kernel
  specifications. It writes `site/data-standard/core-library.json`, next to the data
  `runner/definition-data.js` writes. With `--check` it reports any kernel value without a
  specification and any specification naming no value. It reports; it does not fail CI.
- **Tests per value** come from the translation manifest and the test index the site already
  builds: a test uses a library value if its translation or its source names it.

## Mechanisation

> **Superseded in part (2026-11-11).** Decision D2 of [lean-full-definition.md](lean-full-definition.md)
> replaces the top-level-definition device below once programs are translated in module form
> (that plan's step 3): the library values become entries of the test basis, extending the
> interfaces `B0` already has for `List`, `Tuple`, `String`, `Maybe` and `Array`, with the copy
> at `Int` of any text whose scheme quantifies a `number` variable bound under a new variable, as
> `ME0(Basics)` does for `abs`. In module form a qualified name resolves through an import's
> qualifier, so a top-level definition under a qualified name would not be found.

- **Translator.** A library prelude. For a test, the translator collects the library values the
  test names, and those their texts name, transitively. It adds each value's Elm text or model text
  to the program as a top-level definition under its qualified name, and specialises it like the
  program's own code. `List.sum` then gets its copy at Float, which is what the `LetNumber*` tests
  exercise. The program records the library values it used (`library := [...]` in Lean, like
  `native`), and the test's mechanisation page lists them, linked to their Core Library entries.
- **Lean.** No new APPLY cases while every kernel value has a model text: model texts are Elm and
  translate like Elm text. Where a value needs a display instead (Bitwise, String's code units),
  add its cases in a separate module, `StandardElmMech/Library/`, with its own soundness lemma, so
  that the book's `Apply` and `applySet_sound` do not grow with the library.
- **Conformance of the model texts.** A model text is a claim about elm/core's kernel. For each
  module with kernel values, a test program applies the model and elm/core's function to the same
  inputs and logs whether they agree, run by the suite's runner against each compiler. A
  disagreement is a finding: about the model, or about an implementation.

## Steps

1. **Book sentence and decisions.** Add the sentence pointing to the Core Library page to
   Appendix C's "Library functions" paragraph. Record the decision (library tests are checked
   against the book plus the library's Elm and model texts, and marked as such) in
   [untranslated-tests.md](untranslated-tests.md) group D.
2. **Maybe, Result, Tuple.** Vendor elm/core; write the extractor; the `/core` index and the three
   module pages; the header link. Rebuild the site; the link audit passes.
3. **Translator prelude for Elm text.** Gains the group D tests whose library functions are Elm
   text: all but LetNumberMap2Test (`List.map2` is kernel), and LetNumberResultMapTest once `Ok`
   and `Err` are encoded (group B). The coverage table counts library checks apart from language
   checks.
4. **List, Char.** Their Elm text pages; model texts for `map2` to `map5`, `sortBy`, `sortWith`,
   and the Char case conversions (the case tables are Unicode's, so `toUpper`'s model names
   Unicode's simple case mapping by display, and the notes give Elm/JS's full mapping, A52); their
   conformance tests. Gains LetNumberMap2Test.
5. **Dict, Set.** Elm text only. Gains DictMapStagedCaptureTest (group H, `import:Dict`), once
   imports of library modules are allowed (the translator's `import:*` refusal, for these modules
   only).
6. **Bitwise, then Array.** Bitwise by display (32-bit, as both implementations do it, with the
   Int range of Appendix E); `Elm.JsArray` by model texts over lists; Array's Elm text. Gains the
   Bitwise and Array tests of group H.
7. **String.** After the decision above. Model texts and displays; implementation notes from
   Appendix E (A52, A53) and the suite's String tests.

Each step: rebuild the site data and the site, run the link audit, run the translator with
`--check`, `lake build` and `lake exe run-examples`, and update the README counts.

## Out of scope

Effects modules beyond what the book defines, packages other than elm/core, and elm/core versions
other than 1.0.5. Basics and Debug stay in the book.
