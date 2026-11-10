# Mechanisation: A Standard Definition of Elm?

The Lean 4 project is in `standard-elm-mech/`. Build it, check every proof,
and run the examples with:

```
cd standard-elm-mech && lake build && lake exe run-examples
```

(Lean 4.35.0 and Lake, from `elan`; put `~/.elan/bin` on the PATH.)
`standard-elm-mech/README.md` describes the files and the theorems.
`example-run.md` and `example-run.json` are written by `lake exe run-examples`;
`translation-manifest.json` by the translator, `definition/tools/src/Translate.elm`,
which writes the examples (every `elm-spec` test it can translate) into
`standard-elm-mech/StandardElmMech/Generated/`. Run the translator before
building when the tests have changed.
