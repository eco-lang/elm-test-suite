# Onboarding Questionnaire: PL Definition Writer

Read this file when the user types `setup`. Ask ALL questions below in one
message; the user should be able to answer everything at once. Replace each
placeholder in the files listed. Then scan the workspace (excluding `skills/` and `setup/`)
for any remaining `{{` and ask for whatever is missing.

These questions set house preferences that stay the same from book to book.
Facts about a particular book (title, authors, language, implementation path,
design notes) are NOT asked here: stage 01 collects them at the start of each
book.

### Q1: Which spelling should the books use?
- Placeholder: `{{SPELLING}}`
- Files: `shared/run-config.md`
- Type: selection
- Options: British (elaborate, realisation, behaviour), American (realization, behavior)
- Default: British, as in the exemplar
- Derived field: `{{PAPER_SIZE}}` in `shared/run-config.md`: `a4paper` for British, `letterpaper` for American. Do not ask.

### Q2: Where is your copy of *The Definition of Standard ML (Revised)* PDF?
- Placeholder: `{{EXEMPLAR_PDF_PATH}}`
- Files: `shared/run-config.md`
- Type: free text (absolute path)
- Default: the `sml97-defn.pdf` at the root of this repository, written as an absolute path
- Note: check the file exists and has about 136 pages. The page numbers in `shared/exemplar-index.md` assume the 1997 MIT Press revised edition; if the user's copy differs, say so and offer to re-index.

### Q3: Which TeX engine should build the books?
- Placeholder: `{{TEX_ENGINE}}`
- Files: `shared/run-config.md`
- Type: selection
- Options: pdflatex, xelatex, lualatex
- Default: pdflatex. Choose xelatex or lualatex only if the books need system fonts or a lot of Unicode in the source.

### Q4: Do you want to machine-check the rules against the implementation (stage 06)?
- Type: yes/no
- Default: yes
- If YES: ask Q5. Keep the `{{?MECHANISATION}}` section in `shared/run-config.md` and remove only its two marker lines.
- If NO: remove the `{{?MECHANISATION}}` ... `{{/MECHANISATION}}` section from `shared/run-config.md`; delete `stages/06-mechanisation/`; remove the 06 rows from the Folder Map, the status diagram and the Routing table in `CLAUDE.md`, and the 06 row from the Task Routing table in `CONTEXT.md`. Stage 07 already treats the mechanisation report as optional.

### Q5: Which tool should encode the rules? (only if Q4 is yes)
- Placeholder: `{{MECH_TOOL}}`
- Files: `shared/run-config.md`
- Type: selection
- Options: Ott (closest to paper notation, checks rules are well formed), Lean 4 (proofs and executable checkers), Coq (proofs, extraction to OCaml), PLT Redex (fastest route to running examples, no proofs)
- Default: PLT Redex if the main aim is testing against the implementation; Ott if it is checking the rules are well formed

---

## After Onboarding

1. Show the user the filled `shared/run-config.md`.
2. Check the tools: run the "Verify" steps in `shared/texlive-setup.md`, and, if Q4 was yes, the section for the chosen tool in `stages/06-mechanisation/references/mechanisation-setup.md`. List anything missing with its install command.
3. Tell the user: "Setup is done. To start a book, say `next`, or open stage 01, Survey. I will ask for the book's title, authors, language, implementation path and design notes there."

After all replacements, scan the entire workspace (excluding `skills/` and `setup/`) for remaining `{{` patterns. If any remain, ask for the missing information.
