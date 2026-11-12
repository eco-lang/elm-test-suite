// mechanisation-data.js: the data from which the website shows the Lean proofs of the mechanisation
// of A Standard Definition of Elm? (definition/mechanisation/standard-elm-mech/).
//
// Called by definition-data.js, which writes it under its --out directory (site/data-standard):
//   mechanisation/index.json            the Lean version, the files, every theorem in file order
//                                       (name, place, first sentence of its doc comment, method of
//                                       proof) and the summary of the generated theorems
//   mechanisation/proofs/<slug>.json    one theorem: doc comment, statement, proof, the theorems it
//                                       uses and that use it, the book's rules it names
//   mechanisation/proofs/kc.json        the theorems kc_<Shard>_<n> that the command #kernel_checks
//                                       generates at compile time, one per check the kernel can compare
//   mechanisation/translations/<project>/<Test>.json
//                                       an elm-spec test's Lean translation and what became of each of
//                                       its checks, or why it is not translated
//
// The theorems are read from the Lean source text, so nothing here needs Lean. The generated ones are
// not in the source: their names come from example-run.json, which `lake exe run-examples` writes with
// the selection #kernel_checks makes (kernelCheck? in Theorems.lean). The translations and the reasons
// come from translation-manifest.json, which definition/tools/src/Translate.elm writes.
'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const MECH = path.join(ROOT, 'definition', 'mechanisation');
const PROJECT = path.join(MECH, 'standard-elm-mech');

// A theorem's address: its Lean name, with a prime spelled out.
// A theorem's page slug: Lean names may contain ' and ?, which a URL path cannot carry as they are
// (`?` starts a query).
function slugOf(name) {
    return name.replace(/'/g, '-prime').replace(/\?/g, '-q');
}

function escapeRe(s) {
    return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

// The descriptions of the files, from the Files table of the project's README.
function fileDescriptions() {
    const out = new Map();
    const readme = fs.readFileSync(path.join(PROJECT, 'README.md'), 'utf8');
    for (const m of readme.matchAll(/^\| `([^`]+\.lean)` \| (.*) \|$/gm)) out.set(m[1], m[2].trim());
    return out;
}

// The top-level theorems of one file, with their doc comments and the section (/-! ## ... -/) each is in.
function theoremsOf(rel) {
    const lines = fs.readFileSync(path.join(PROJECT, rel), 'utf8').split('\n');
    const found = [];
    let section = null;
    for (let i = 0; i < lines.length; i++) {
        const sec = lines[i].match(/^\/-!\s*#+\s*(.*?)\s*-\/\s*$/);
        if (sec) section = sec[1];
        const mac = lines[i].match(/^macro\s+"([^"]+)"\s*:\s*tactic/);
        const m = mac ? [null, mac[1]] : lines[i].match(/^(?:private |protected )?theorem\s+(\S+)/);
        if (!m) continue;
        // The doc comment ends on the line before.
        let doc = '';
        if (i > 0 && /-\/\s*$/.test(lines[i - 1])) {
            let j = i - 1;
            while (j >= 0 && !lines[j].startsWith('/--')) j--;
            if (j >= 0) doc = lines.slice(j, i).join('\n').replace(/^\/--\s*/, '').replace(/\s*-\/\s*$/, '');
        }
        // The declaration runs to the next line that starts in the first column.
        let end = i + 1;
        while (end < lines.length && (lines[end] === '' || /^\s/.test(lines[end]))) end++;
        while (end > i + 1 && lines[end - 1].trim() === '') end--;
        const text = lines.slice(i, end).join('\n');
        const at = text.indexOf(':=');
        found.push({
            macro: !!mac,
            name: m[1],
            file: rel,
            line: i + 1,
            section,
            doc: doc.split('\n').map((l) => l.trim()).join(' ').trim(),
            statement: at >= 0 ? text.slice(0, at).trimEnd() : text,
            proof: at >= 0 ? dedent(text.slice(at + 2).replace(/^[ \t]+/, '')) : '',
            source: text,
        });
    }
    return found;
}

function methodOf(proof) {
    if (/\bnative_decide\b/.test(proof)) return 'native_decide';
    if (/decide \+kernel/.test(proof)) return 'kernel';
    if (/^by\b/.test(proof.trim())) return 'tactics';
    return 'term';
}

// The doc comment, or its first sentence when it is long.
function firstSentence(doc) {
    if (doc.length <= 160) return doc;
    const m = doc.match(/^(.*?[^.]\.)\s+(?=[A-Z`(])/);
    return (m ? m[1] : doc).trim();
}

// Removes the indentation common to the lines of a block.
function dedent(text) {
    const lines = text.replace(/^\n+/, '').split('\n');
    const ind = Math.min(...lines.filter((l) => l.trim()).map((l) => l.match(/^ */)[0].length));
    return lines.map((l) => l.slice(Number.isFinite(ind) ? ind : 0)).join('\n');
}

// The run of the examples, as `lake exe run-examples` writes it (example-run.json): every check of
// every program, by shard, with the definition's value, the status, and the theorem #kernel_checks
// made for it (kc_<Shard>_<n>) or why it made none.
function exampleRun() {
    const file = path.join(MECH, 'example-run.json');
    if (!fs.existsSync(file)) return { rows: [], total: null };
    const run = JSON.parse(fs.readFileSync(file, 'utf8'));
    return {
        rows: run.checks.map((c) => ({ ...c, definition: c.definition.join(' or ') })),
        total: { checks: run.total.checks, agree: run.total.agree, diverge: run.total.diverge },
    };
}

// The translator's manifest: every elm-spec test, translated or refused with its reason.
// The per-test theorems of the static semantics and of the end-to-end pipeline (plan steps 9 and
// 10), as `lake exe certify` lists them in ../static-report.json.
let staticReport = null;
function staticOf(key) {
    if (staticReport === null) {
        const file = path.join(MECH, 'static-report.json');
        staticReport = fs.existsSync(file) ? JSON.parse(fs.readFileSync(file, 'utf8')) : {};
    }
    const per = (staticReport.tests || {})[key];
    return per ? { legal: per.legal || null, refuse: per.refuse || null, spec: per.spec || null, mean: per.mean || null, native: !!per.native } : null;
}

function manifest() {
    const file = path.join(MECH, 'translation-manifest.json');
    return fs.existsSync(file) ? JSON.parse(fs.readFileSync(file, 'utf8')).tests : [];
}

// The hand translations of `handPartial` (Examples.lean): def pX : Program := { name := "...", ... },
// with the doc comment before each, by the program's name.
function handPrograms() {
    const rel = 'StandardElmMech/Examples.lean';
    const lines = fs.readFileSync(path.join(PROJECT, rel), 'utf8').split('\n');
    const out = new Map();
    for (let i = 0; i < lines.length; i++) {
        const m = lines[i].match(/^def (\w+) : Program := \{/);
        if (!m) continue;
        let end = i + 1;
        while (end < lines.length && (lines[end] === '' || /^\s/.test(lines[end]))) end++;
        while (end > i + 1 && lines[end - 1].trim() === '') end--;
        const text = lines.slice(i, end).join('\n');
        const name = text.match(/name := "([^"]+)"/);
        if (name) out.set(name[1], { def: m[1], file: rel, line: i + 1, source: text });
    }
    return out;
}

// The CHECK lines of a test program: label -> expected value. A label the test must not print
// (`-- CHECK-NOT: label:`, in a test that stops at Debug.todo) expects no value, written "(no value)".
function checkLines(project, name) {
    const file = path.join(ROOT, 'tests', project, 'src', name + '.elm');
    const out = new Map();
    if (!fs.existsSync(file)) return out;
    const text = fs.readFileSync(file, 'utf8');
    for (const m of text.matchAll(/^-- CHECK: (.*)$/gm)) {
        const at = m[1].indexOf(': ');
        if (at > 0) out.set(m[1].slice(0, at), m[1].slice(at + 2).trim());
    }
    for (const m of text.matchAll(/^-- CHECK-NOT: (.*):\s*$/gm)) out.set(m[1], '(no value)');
    return out;
}

function sha256(file) {
    return require('crypto').createHash('sha256').update(fs.readFileSync(file)).digest('hex');
}

// Writes the data under <out>/mechanisation. ruleSlugs: the slugs of the book's rules, so that a rule
// named in Lean (r_d_atexp_var) links to its page (d-atexp-var). Returns the problems found.
function writeMechanisation(out, ruleSlugs, writeJson) {
    const problems = [];
    if (!fs.existsSync(PROJECT)) return problems;
    const descriptions = fileDescriptions();
    // The theorems of each shard of the translated tests, in their own files.
    const generatedDir = path.join(PROJECT, 'StandardElmMech', 'Generated');
    const checkFiles = fs.existsSync(generatedDir)
        ? fs.readdirSync(generatedDir).filter((f) => /^Checks.*\.lean$/.test(f)).sort().map((f) => 'StandardElmMech/Generated/' + f)
        : [];
    for (const f of checkFiles) {
        descriptions.set(f, 'The theorems of the translated tests of shard ' + f.replace(/^.*Checks(.*)\.lean$/, '$1') + ': one generated theorem per check the kernel can compare, and the derivability of every check');
    }
    const files = [...descriptions.keys()].filter((f) => f.endsWith('.lean') && fs.existsSync(path.join(PROJECT, f)));
    const declared = files.flatMap(theoremsOf);
    const theorems = declared.filter((t) => !t.macro);
    // Tactic macros a proof calls by name (sound_fin): shown with the proof, and searched for the
    // rules and theorems they use.
    const macros = declared.filter((t) => t.macro);
    const macrosOf = (t) => macros.filter((mc) => new RegExp('(^|[^\\w])' + escapeRe(mc.name) + '(?![\\w])').test(t.proof));
    const names = theorems.map((t) => t.name);
    const nameRe = new Map(names.map((n) => [n, new RegExp('(^|[^\\w.\'])' + escapeRe(n) + '(?![\\w\'])')]));

    const rulesOf = (t) => {
        const found = new Set();
        // Chapter 6's rules (r_d_*), Chapter 7's (r_dm_*), Chapter 8's (r_e_*), Chapter 9's
        // rules (r_p_*, r_p_stat_*), and the static rules of Chapters 4 (r_s_*) and 5 (r_sm_*)
        for (const m of [t.source, t.doc, ...macrosOf(t).map((mc) => mc.source)].join(' ').matchAll(/\br_(d|dm|p|e|sm|s)_([a-z_]+)|\br:((?:d|dm|p|e|sm|s)-[a-z-]+)/g)) {
            // a logged constructor (RulesL.lean, plan decision D4) is the rule's twin: r_d_exp_app_l
            let slug = m[2] ? m[1].replace(/_/g, '-') + '-' + m[2].replace(/_/g, '-') : m[3];
            if (m[2] && !ruleSlugs.has(slug) && slug.endsWith('-l') && ruleSlugs.has(slug.slice(0, -2))) slug = slug.slice(0, -2);
            // r_sm_topdec_seq_types is a second constructor for r:sm-topdec-seq (Stat/Modules.lean)
            if (slug === 'sm-topdec-seq-types') slug = 'sm-topdec-seq';
            if (ruleSlugs.has(slug)) found.add(slug);
            else problems.push(`${t.name} (${t.file}:${t.line}) names the rule ${slug}, which the book does not have`);
        }
        return [...found];
    };
    const rulingsOf = (t) => [...new Set([...(t.name + ' ' + t.doc).matchAll(/\b[aA](\d{1,3})(?![\d\w])/g)].map((m) => 'A' + m[1]))];

    const proofText = (t) => [t.proof, ...macrosOf(t).map((mc) => mc.source)].join('\n');
    const uses = new Map(theorems.map((t) => [t.name, names.filter((n) => n !== t.name && nameRe.get(n).test(proofText(t)))]));
    const usedBy = new Map(names.map((n) => [n, names.filter((m) => uses.get(m).includes(n))]));

    const run = exampleRun();
    const generated = run.rows.filter((c) => c.theorem);
    const tests = manifest();
    const kernelSource = (() => {
        const lines = fs.readFileSync(path.join(PROJECT, 'StandardElmMech/Theorems.lean'), 'utf8').split('\n');
        const from = lines.findIndex((l) => l.startsWith('/-- Programs whose theorem is moved to `native_decide`'));
        const to = lines.findIndex((l) => l.includes('logInfo m!"#mod_program_theorems'));
        return from >= 0 && to > from ? { file: 'StandardElmMech/Theorems.lean', line: from + 1, text: lines.slice(from, to + 1).join('\n') } : null;
    })();
    if (!kernelSource) problems.push('Theorems.lean: the command #mod_program_theorems was not found');
    if (!run.total) problems.push('definition/mechanisation/example-run.json is missing: run `lake exe run-examples`');

    const toolchain = fs.readFileSync(path.join(PROJECT, 'lean-toolchain'), 'utf8').trim();
    // the book's rules encoded as constructors: Chapters 6, 7 (with Chapter 9's dynamic rules), 8,
    // Chapter 9's dispatch, start and transitions, and the static rules of Chapters 4, 5 and 9
    const ruleFiles = ['StandardElmMech/Rules.lean', 'StandardElmMech/Mod/Rules.lean', 'StandardElmMech/Eff/EncDec.lean',
        'StandardElmMech/Eff/Task.lean', 'StandardElmMech/Eff/Messages.lean', 'StandardElmMech/Prog/Dispatch.lean',
        'StandardElmMech/Prog/Rules.lean', 'StandardElmMech/Stat/Rules.lean', 'StandardElmMech/Stat/Modules.lean',
        'StandardElmMech/Stat/Program.lean'];
    const ruleCount = ruleFiles
        .map((f) => (fs.readFileSync(path.join(PROJECT, f), 'utf8').match(/^\s*\|\s*r_(d|dm|p|e|sm|s)_\w+(?<!_l)\s*[(:]/gm) || []).length)
        .reduce((a, b) => a + b, 0);
    const summary = (t) => ({
        name: t.name,
        slug: slugOf(t.name),
        file: t.file,
        line: t.line,
        section: t.section,
        summary: firstSentence(t.doc),
        method: methodOf(t.proof),
    });

    // The elm-spec tests by status and reason, for the coverage table.
    const reasonClass = (r) => (r.startsWith('checks:unmatched:') ? 'checks:unmatched' : r);
    const byReason = new Map();
    for (const t of tests) {
        const k = t.status === 'translated' ? 'translated' : reasonClass(t.reason);
        if (!byReason.has(k)) byReason.set(k, []);
        byReason.get(k).push({ project: t.project, name: t.name });
    }
    const coverage = [...byReason.entries()]
        .map(([reason, list]) => ({ reason, count: list.length, tests: list }))
        .sort((a, b) => (a.reason === 'translated' ? -1 : b.reason === 'translated' ? 1 : b.count - a.count || (a.reason < b.reason ? -1 : 1)));

    const dir = path.join(out, 'mechanisation');
    writeJson(path.join(dir, 'index.json'), {
        lean: toolchain.replace(/^leanprover\/lean4:/, ''),
        rules: ruleCount,
        checks: run.total,
        files: files
            .filter((f) => theorems.some((t) => t.file === f))
            .map((f) => ({ path: f, description: descriptions.get(f) || '' })),
        theorems: theorems.map(summary),
        generated: { count: generated.length, slug: 'kc' },
        coverage: { total: tests.length, reasons: coverage },
    });
    theorems.forEach((t, i) => {
        const link = (u) => (u ? { name: u.name, slug: slugOf(u.name) } : null);
        writeJson(path.join(dir, 'proofs', slugOf(t.name) + '.json'), {
            ...summary(t),
            doc: t.doc,
            fileDescription: descriptions.get(t.file) || '',
            statement: t.statement,
            proof: t.proof,
            uses: uses.get(t.name).map((n) => ({ name: n, slug: slugOf(n) })),
            usedBy: usedBy.get(t.name).map((n) => ({ name: n, slug: slugOf(n) })),
            rules: rulesOf(t),
            tactics: macrosOf(t).map((mc) => ({ name: mc.name, file: mc.file, line: mc.line, doc: mc.doc, source: mc.source })),
            rulings: rulingsOf(t),
            prev: link(theorems[i - 1]),
            next: link(theorems[i + 1]),
        });
    });

    // The shards, with how many checks of each became theorems.
    const shardNames = [...new Set(run.rows.map((r) => r.shard))];
    const groups = shardNames.map((g) => {
        const rows = run.rows.filter((c) => c.shard === g);
        const projects = [...new Set(rows.map((r) => r.project))].filter((x) => x);
        return {
            key: g,
            title: g === 'Hand' ? 'Hand: partial hand translations of tests the translator refuses' : g + ': tests/' + projects.join(', tests/'),
            programs: new Set(rows.map((r) => r.program)).size,
            checks: rows.length,
            generated: rows.filter((r) => r.theorem).length,
        };
    });
    const skipped = (why) => run.rows.filter((c) => c.skipped === why).length;
    writeJson(path.join(dir, 'proofs', 'kc.json'), {
        count: generated.length,
        source: kernelSource,
        groups,
        // since plan step 1 every check is a conjunct of its program's theorem; `native` counts the
        // checks proved by native_decide, `value` those whose CHECK value could not be stated
        skipped: { divergence: 0, native: run.rows.filter((c) => c.proof === 'native').length, float: 0, value: skipped('unparsed') },
        checks: generated.map((c) => ({
            name: c.theorem,
            program: c.program,
            project: c.project || null,
            label: c.label,
            expected: c.expected,
            kind: c.kind,
        })),
    });

    // Each elm-spec test's page: its Lean translation, with what became of each check, or why it is
    // not translated. A translation made from an older version of the test is marked out of date.
    const hand = handPrograms();
    const written = [];
    let outOfDate = 0;
    for (const t of tests) {
        const key = t.project + '/' + t.name;
        // a translation is current when every module of its program is as it was translated (plan
        // step 3: the manifest lists each module's file and hash, the test last)
        const sources = t.sources && t.sources.length ? t.sources : [{ path: 'tests/' + t.project + '/src/' + t.name + '.elm', sha256: t.sha256 }];
        const current = sources.every((s) => fs.existsSync(path.join(ROOT, s.path)) && sha256(path.join(ROOT, s.path)) === s.sha256);
        const rows = run.rows.filter((r) => r.program === t.name && (r.project === t.project || r.shard === 'Hand'));
        const isHand = t.status !== 'translated' && hand.has(t.name) && rows.length > 0;
        const lines = checkLines(t.project, t.name);
        const checks = rows.map((r) => ({
            label: r.label,
            expected: r.expected,
            checkLine: lines.has(r.label) ? lines.get(r.label) : null,
            definition: r.definition,
            status: r.status,
            theorem: r.theorem,
            skipped: r.skipped,
        }));
        if (t.status === 'translated' && !current) outOfDate++;
        written.push(key);
        writeJson(path.join(dir, 'translations', t.project, t.name + '.json'), {
            name: t.name,
            project: t.project,
            status: isHand ? 'hand' : t.status,
            reason: t.reason || null,
            detail: t.detail || null,
            def: isHand ? hand.get(t.name).def : t.def || '',
            file: isHand ? hand.get(t.name).file : t.shard ? 'StandardElmMech/Generated/' + t.shard + '.lean' : '',
            shard: isHand ? 'Hand' : t.shard || '',
            source: isHand ? hand.get(t.name).source : t.lean || '',
            sources: sources.map((s) => s.path),
            current,
            checks,
            kind: t.kind || 'view',
            host: t.host || null,
            flags: t.flags || null,
            native: !!t.native,
            dropped: t.dropped || [],
            // plan steps 9 and 10 (lake exe certify, ../static-report.json): the test's static
            // theorems and, for a translated test, its end-to-end theorems
            statics: staticOf(t.project + '/' + t.name),
        });
    }
    writeJson(path.join(dir, 'translations', 'index.json'), written);

    // The restrictions decided on the syntax tree (plan step 8): each restriction page names its
    // Lean Prop (Src/Restrictions.lean, whose doc comment starts with the label) and how many
    // written programs break it (syntactic-report.json).
    const restrictionsFile = path.join(PROJECT, 'StandardElmMech/Src/Restrictions.lean');
    if (fs.existsSync(restrictionsFile)) {
        const lines = fs.readFileSync(restrictionsFile, 'utf8').split('\n');
        const synReportPath = path.join(ROOT, 'definition/mechanisation/syntactic-report.json');
        const synReport = fs.existsSync(synReportPath) ? JSON.parse(fs.readFileSync(synReportPath, 'utf8')) : { programs: [] };
        const restrictions = {};
        lines.forEach((line, i) => {
            const m = line.match(/^\/-- (res:[a-z-]+)/);
            if (!m) return;
            let j = i;
            while (j < lines.length && !/^def /.test(lines[j])) j++;
            const d = j < lines.length ? lines[j].match(/^def (\w+)/) : null;
            if (!d) return;
            const label = m[1];
            restrictions[label.replace(/^res:/, '')] = {
                label,
                prop: 'Src.' + d[1],
                file: 'StandardElmMech/Src/Restrictions.lean',
                line: j + 1,
                broken: synReport.programs.filter((p) => (p.breaks || []).includes(label)).map((p) => p.name),
            };
        });
        writeJson(path.join(dir, 'restrictions.json'), restrictions);
    }
    if (outOfDate) console.warn(`  warning: ${outOfDate} Lean translations were made from an older version of their test; run the translator and the mechanisation stage`);
    console.log(`  Lean mechanisation: ${theorems.length} theorems in ${files.filter((f) => theorems.some((t) => t.file === f)).length} files, ${generated.length} checks in the generated program theorems, ${tests.filter((t) => t.status === 'translated').length} of ${tests.length} elm-spec tests translated`);
    return problems;
}

module.exports = { writeMechanisation };
