# The Definition's tools

Two Elm programs, run as `elm-pages` scripts, that keep parts of *A Standard Definition of Elm?*
and its Lean mechanisation generated from one source. The design is
[plans/elm-to-lean-translator.md](../../plans/elm-to-lean-translator.md).

Run them from the repository's root, with the `elm-pages` the site installs:

```sh
site/node_modules/.bin/elm-pages run definition/tools/src/GenerateDerivedForms.elm
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm            # write
site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm --check    # compare only
```

and their tests from this folder:

```sh
../../site/node_modules/.bin/elm-test --compiler ../../site/node_modules/.bin/elm
```

## GenerateDerivedForms

The derived forms of Appendix A are one table, `src/DerivedForms/Table.elm`: for each row, its
derived form (LaTeX pieces), its equivalent form (a term of the bare syntax with metavariables, in
the template language of `src/DerivedForms/Term.elm`) and its Lean function. The script writes the
six tables of `definition/tex/appendix-derived-forms.tex` and the derived-form functions of
`StandardElmMech/Derived.lean`, each between `BEGIN GENERATED` and `END GENERATED` marker lines,
leaving the rest of both files as it is. To change a derived form, change its row and run the
script; never edit inside the markers. The three groupings (function bindings, `let`, modules) are
computed, so their LaTeX is given in the table and their Lean stays hand-written.

## Translate

Translates the tests of `tests/` tagged `elm-spec` into Lean, for the mechanisation's examples:

- `src/Translate/Directives.elm`: a test's `-- TAGS`, `-- CHECK`, `-- CHECK-NOT`, `-- EXIT` lines,
  and the directives that keep it out;
- `src/Translate/Convert.elm`: from elm-syntax's tree to the translator's representation
  (`src/Translate/Ir.elm`): names resolved against the program, its imports and the names the Lean
  environment binds; literals read exactly from the source text; `main`'s checks; and every reason a
  test is outside the fragment, the most important reported;
- `src/Translate/Infer.elm`, `Types.elm`, `Basis.elm`: Hindley-Milner inference with Standard Elm's
  classes and records with rows, recording the type of every integer constant and the instance of
  every use of a declaration; a group is closed as one (ruling A93);
- `src/Translate/Specialise.elm`: the book's number specialisation (default copies, copies per
  instance, named with `$`: `incF$Float`); it also marks a program `native` when it uses a value
  whose result only the C library computes (round, floor, ceiling, truncate, the elementary
  functions, `^` at Float, `Debug.toString`), whose checks Lean then proves by `native_decide`
  only;
- `src/Translate/ToLean.elm`: printing in the helper notation of `Derived.lean`;
- `src/Translate/Library.elm`, `LibraryTexts.elm`: the core library values the translator evaluates
  (`evaluatedLibrary` in `src/Translate.elm`: 12 values of `List`, `Maybe`, `Result`, `Tuple`,
  plans/library-elm-texts.md). A test may name them as values of the basis, at the schemes of their
  annotations in the vendored elm/core 1.0.5; the closure of their texts is translated by the same
  pipeline into `Generated/Library.lean`, `List.sum` with its copy `sum$Int`, and a program that
  names one records it (`library := [...]`, and in the manifest).

It writes `definition/mechanisation/standard-elm-mech/StandardElmMech/Generated/` (the programs, in
shards that are fixed alphabetical buckets of `project/Test`, `All.lean`, one file of theorems per
shard, and the source programs in buckets of their own with a file of syntactic theorems each; a
file there it wrote before but no longer writes is removed), the list of those modules in
`StandardElmMech.lean`, and `definition/mechanisation/translation-manifest.json`, which lists every
`elm-spec` test as translated or refused, with its reason and the sha256 of its source. Two
reasons are about size, not the fragment: `construct:large-program` (a source over 20000
characters) and `construct:large-computation` (a test of a compiler's limits named in
`src/Translate/Pipeline.elm`, too many steps for the Lean evaluator). Then build
the Lean project and run `lake exe run-examples` (see the mechanisation's README).

`custom-backend-task.ts` computes the sha256s for the manifest.
