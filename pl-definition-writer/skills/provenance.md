# Skill Provenance

Where each bundled skill came from, what was copied, and what was considered
and left out.

## Sources

| Skill | Source | Commit | Licence |
|-------|--------|--------|---------|
| latex | github.com/flonat/claude-research, `skills/latex` and the two files it uses from `skills/shared` | 08dd9bdf9367f7321c27b7db8c08a125598a613f | MIT (`latex/LICENSE`) |

Copied: `SKILL.md`; `references/` known-errors, latex-configs, quality-rubric,
source-pathologies; `templates/build-config/` (`.latexmkrc`, README);
`../shared/` quality-scoring and overfull-boxes. Left out: the working-paper
template and `references/templates.md` (not used here), and the files the
skill names for Phase 2.4, Phase 6.1 and its breadcrumb, which stage 08 skips.

`.latexmkrc` is Perl that latexmk executes. It was read in full before
bundling: it selects the engine from the sources, builds into `out/`, and
copies the PDF back only after a successful build. It makes no network
calls. Re-read it before updating it from upstream.

## Considered and Not Bundled

- **typing-rule-generator** (a5c-ai/babysitter): the skill body is a list of
  capabilities with no rules or guidance. Its intended ground is covered by
  `shared/definition-style.md` and the semantics stage's own guide.
- **latex-manual** (enuno/claude-command-and-control, via a registry
  archive): no licence upstream, so it may not be redistributed. The latex
  skill's `known-errors.md` covers preview troubleshooting instead.
