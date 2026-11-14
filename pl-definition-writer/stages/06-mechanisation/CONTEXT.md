# Stage 06: Mechanisation (optional)

Encode the grammar and rules in a proof assistant or semantics tool, and test them against the implementation.

Paths starting `definition/` are in the book's output tree, `elm-test-suite/definition/`, which is `../../../definition/` from this folder (see `../../shared/run-config.md` "Output Tree"). Other paths are relative to this folder.

## Inputs

| Source | File/Location | Section/Scope | Why |
|--------|--------------|---------------|-----|
| Config | `../../shared/run-config.md` | "Mechanisation" | Which tool to use |
| Stage 01 | `definition/survey/book-brief.md` | "Implementation" row | Where to run examples |
| Stage 01 | `definition/survey/language-survey.md` | "Evidence" | Programs with known results |
| Stage 02 | `definition/architecture/notation.md` | Full file | Names to carry into the encoding |
| Stage 03 | `definition/tex/syntax-<level>.tex`, `definition/tex/appendix-derived-forms.tex` | Grammar figures and derived forms | What to encode as syntax |
| Stage 04 | `definition/tex/static-<level>.tex`, `dynamic-<level>.tex` | Object figures, operations, numbered rules | What to encode as relations |
| Reference | `references/mechanisation-guide.md` | "Common Method", then the section for the configured tool | How to encode and test |
| Reference | `references/mechanisation-setup.md` | The section for the configured tool | Install and verify the tool |

## Process

1. Check the configured tool is installed, using `mechanisation-setup.md`. Stop and point the user to it if not.
2. Encode the bare grammar, then the semantic objects, then each rule group as an inductive relation, keeping each rule's book number as its name or a comment.
3. Build the encoding and fix every error. An error that reveals a problem in the book, not the encoding, is recorded as a finding.
4. Build the example corpus as `mechanisation-guide.md` "Example Corpus" describes: from the repository's root, run `site/node_modules/.bin/elm-pages run definition/tools/src/GenerateDerivedForms.elm` if the derived forms changed, then `node --stack-size=4000 site/node_modules/.bin/elm-pages run definition/tools/src/Translate.elm`, which translates every `elm-spec` test it can into `StandardElmMech/Generated/` and writes `definition/mechanisation/translation-manifest.json`.
5. From `definition/mechanisation/standard-elm-mech/`, run `lake build` (every theorem, the generated ones included) and `lake exe run-examples`, which runs every example and writes `definition/mechanisation/example-run.md` and `example-run.json`. Each disagreement is either a bug in the translator or the encoding, which is fixed, or a finding about the book or the test, recorded in `knownDiv` (Theorems.lean) with its reason and put to the human at the checkpoint. Then rebuild the site's data (`node runner/definition-data.js`). Commit the generated files.
6. List every divergence and every rule that could not be encoded.
7. Run the audit below, then write the report and the encoding.

## Checkpoints

| After Step | Agent Presents | Human Decides |
|------------|---------------|---------------|
| 6 | Each divergence and each unencodable rule, with the book rule and the implementation behaviour | Per item: fix the book (which stage), fix the implementation, or record as known |

## Audit

| Check | Pass Condition |
|-------|---------------|
| Rule coverage | Every numbered rule is encoded, or listed as not encodable with the reason |
| Traceable | Every encoded rule names its book rule number |
| Builds | The encoding builds with no errors |
| Dispositions | Every divergence and finding has the human's disposition |

## Outputs

| Artifact | Location | Format |
|----------|----------|--------|
| Encoding | `definition/mechanisation/` | Source files for the configured tool, with a build command in a README |
| Report | `definition/mechanisation/mechanisation-report.md` | `mechanisation-guide.md` "Report" |
