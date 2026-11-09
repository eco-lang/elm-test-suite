// mechanisation-data.js: the data from which the website shows the Lean proofs of the mechanisation
// of A Standard Definition of Elm? (definition/mechanisation/standard-elm-mech/).
//
// Called by definition-data.js, which writes it under its --out directory (site/data-standard):
//   mechanisation/index.json            the Lean version, the files, every theorem in file order
//                                       (name, place, first sentence of its doc comment, method of
//                                       proof) and the summary of the generated theorems
//   mechanisation/proofs/<slug>.json    one theorem: doc comment, statement, proof, the theorems it
//                                       uses and that use it, the book's rules it names
//   mechanisation/proofs/kc.json        the theorems kc_0, kc_1, ... that the command #kernel_checks
//                                       of Theorems.lean generates at compile time, one per check
//
// The theorems are read from the Lean source text, so nothing here needs Lean. The generated ones are
// not in the source: they are listed from example-run.md (the output of `lake exe run-examples`) by
// the selection #kernel_checks makes (see generatedChecks below), in the same order, so that kc_<n>
// here is kc_<n> in Lean. The build of the Lean project prints their number; if Theorems.lean
// changes how it selects them, change generatedChecks to match.
'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const MECH = path.join(ROOT, 'definition', 'mechanisation');
const PROJECT = path.join(MECH, 'standard-elm-mech');

// A theorem's address: its Lean name, with a prime spelled out.
function slugOf(name) {
    return name.replace(/'/g, '-prime');
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

// The rows of example-run.md: program, label, CHECK value, the definition's value, status, and the
// group (corpus, rulings or coverage) whose table the row is in.
function exampleRun() {
    const text = fs.readFileSync(path.join(MECH, 'example-run.md'), 'utf8');
    const rows = [];
    let group = null;
    for (const l of text.split('\n')) {
        const h = l.match(/^## (\S+)/);
        if (h) group = h[1].toLowerCase().startsWith('corpus') ? 'corpus' : h[1].toLowerCase().startsWith('ruling') ? 'rulings' : 'coverage';
        if (!/^\| (?!Program \||---)/.test(l)) continue;
        const c = l.slice(2, -2).split(' | ');
        rows.push({ group, program: c[0], label: c[1], expected: c[2], definition: c[3], status: c[4] });
    }
    const total = text.match(/^Total: (\d+) checks, (\d+) agree, (\d+) diverge\./m);
    return { rows, total: total ? { checks: +total[1], agree: +total[2], diverge: +total[3] } : null };
}

// What #kernel_checks (Theorems.lean) does with each check of allPrograms (corpus ++ rulings ++
// coverage, the order of example-run.md): a known divergence (knownDiv) and a check compared as a
// printed float (floatValued) are skipped, and so is a check whose value expectOf cannot read as an
// Int, a constructor without arguments or a string; every other check gets the theorem kc_<n>, n
// counting from 0 in that order. Returns the rows with `theorem` (its name, or null), `kind` and
// `skipped` (null, 'divergence', 'float' or 'value').
function classifyChecks(rows) {
    // knownDiv and floatValued of Theorems.lean.
    const knownDiv = new Set([]);
    const floatValued = (r) => r.program === 'CoreIssue1080ClampNanTest';
    const expectOf = (s) => {
        if (/^-?\d+$/.test(s)) return 'Int';
        const inner = s.slice(1, -1);
        if (s.length >= 2 && s[0] === '"' && s[s.length - 1] === '"' && !inner.includes('"')) return 'String';
        if (/^[A-Z][A-Za-z0-9]*$/.test(s)) return 'constructor';
        return null;
    };
    let k = 0;
    return rows.map((r) => {
        const skipped = knownDiv.has(r.program + '\u0000' + r.label) ? 'divergence' : floatValued(r) ? 'float' : expectOf(r.expected) ? null : 'value';
        return { ...r, kind: skipped ? null : expectOf(r.expected), skipped, theorem: skipped ? null : 'kc_' + k++ };
    });
}

// The program definitions of Examples.lean (def pX : Program := { name := "...", ... }), with the
// doc comment before each, by the program's name.
function programsOf() {
    const rel = 'StandardElmMech/Examples.lean';
    const lines = fs.readFileSync(path.join(PROJECT, rel), 'utf8').split('\n');
    const out = new Map();
    for (let i = 0; i < lines.length; i++) {
        const m = lines[i].match(/^def (\w+) : Program := \{/);
        if (!m) continue;
        let doc = '';
        if (i > 0 && /-\/\s*$/.test(lines[i - 1])) {
            let j = i - 1;
            while (j >= 0 && !lines[j].startsWith('/--')) j--;
            if (j >= 0) doc = lines.slice(j, i).map((l) => l.trim()).join(' ').replace(/^\/--\s*/, '').replace(/\s*-\/$/, '');
        }
        let end = i + 1;
        while (end < lines.length && (lines[end] === '' || /^\s/.test(lines[end]))) end++;
        while (end > i + 1 && lines[end - 1].trim() === '') end--;
        const text = lines.slice(i, end).join('\n');
        const name = text.match(/name := "([^"]+)"/);
        if (name) out.set(name[1], { def: m[1], file: rel, line: i + 1, doc, source: text });
    }
    return out;
}

// The CHECK lines of a test program: label -> expected value. A label the test must not print
// (`-- CHECK-NOT: label:`, in a test that stops at Debug.todo) expects no value, which the
// examples write "(no value)".
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

// Where each test program is in tests/, for links to its page.
function testIndex() {
    const out = new Map();
    const tests = path.join(ROOT, 'tests');
    for (const project of fs.readdirSync(tests)) {
        const src = path.join(tests, project, 'src');
        if (!fs.existsSync(src)) continue;
        for (const f of fs.readdirSync(src)) if (f.endsWith('.elm') && !out.has(f.slice(0, -4))) out.set(f.slice(0, -4), project);
    }
    return out;
}

// Writes the data under <out>/mechanisation. ruleSlugs: the slugs of the book's rules, so that a rule
// named in Lean (r_d_atexp_var) links to its page (d-atexp-var). Returns the problems found.
function writeMechanisation(out, ruleSlugs, writeJson) {
    const problems = [];
    if (!fs.existsSync(PROJECT)) return problems;
    const descriptions = fileDescriptions();
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
        for (const m of [t.source, t.doc, ...macrosOf(t).map((mc) => mc.source)].join(' ').matchAll(/\br_d_([a-z_]+)|\br:(d-[a-z-]+)/g)) {
            const slug = m[1] ? 'd-' + m[1].replace(/_/g, '-') : m[2];
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
    const classified = classifyChecks(run.rows);
    const generated = classified.filter((c) => c.theorem);
    const tests = testIndex();
    const programs = programsOf();
    const kernelSource = (() => {
        const lines = fs.readFileSync(path.join(PROJECT, 'StandardElmMech/Theorems.lean'), 'utf8').split('\n');
        const from = lines.findIndex((l) => l.startsWith('open Lean Elab Command in'));
        const to = lines.findIndex((l) => l.trim() === '#kernel_checks');
        return from >= 0 && to > from ? { file: 'StandardElmMech/Theorems.lean', line: from + 1, text: lines.slice(from, to + 1).join('\n') } : null;
    })();
    if (!kernelSource) problems.push('Theorems.lean: the command #kernel_checks was not found');

    const toolchain = fs.readFileSync(path.join(PROJECT, 'lean-toolchain'), 'utf8').trim();
    const ruleCount = (fs.readFileSync(path.join(PROJECT, 'StandardElmMech/Rules.lean'), 'utf8').match(/^\s*\|\s*r_d_\w+/gm) || []).length;
    const summary = (t) => ({
        name: t.name,
        slug: slugOf(t.name),
        file: t.file,
        line: t.line,
        section: t.section,
        summary: firstSentence(t.doc),
        method: methodOf(t.proof),
    });
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
    // The three lists of examples, with how many checks of each became theorems.
    const groupTitles = {
        corpus: 'corpus: test programs that accompany the book',
        rulings: "rulings: test programs for the book's rulings",
        coverage: "coverage: test programs for rules the corpus reaches only in passing, and for the book's Comments",
    };
    const groups = ['corpus', 'rulings', 'coverage'].map((g) => {
        const rows = classified.filter((c) => c.group === g);
        return { key: g, title: groupTitles[g], programs: new Set(rows.map((r) => r.program)).size, checks: rows.length, generated: rows.filter((r) => r.theorem).length };
    });
    const skipped = (why) => classified.filter((c) => c.skipped === why).length;
    writeJson(path.join(dir, 'proofs', 'kc.json'), {
        count: generated.length,
        source: kernelSource,
        groups,
        skipped: { divergence: skipped('divergence'), float: skipped('float'), value: skipped('value') },
        checks: generated.map((c) => ({
            name: c.theorem,
            program: c.program,
            project: tests.get(c.program) || null,
            label: c.label,
            expected: c.expected,
            kind: c.kind,
        })),
    });

    // The translation of each test program of tests/ that the examples include, for the test's page,
    // with what became of each of its checks; and a warning where a translation's expected value is no
    // longer the test's CHECK line (the translations are kept by hand, so they can fall behind).
    for (const name of new Set(classified.map((r) => r.program))) {
        if (!tests.has(name)) problems.push(`the example ${name} is not a test program of tests/`);
    }
    const translated = [];
    for (const [name, prog] of programs) {
        const project = tests.get(name);
        const rows = classified.filter((c) => c.program === name);
        if (!project || !rows.length) continue;
        const lines = checkLines(project, name);
        const checks = rows.map((r) => {
            const now = lines.has(r.label) ? lines.get(r.label) : null;
            if (now !== r.expected) {
                console.warn(`  warning: the Lean translation of ${project}/${name} expects ${r.label}: ${r.expected}, but the test's CHECK line ` +
                    (now === null ? 'is gone' : `says ${now}`));
            }
            return { label: r.label, expected: r.expected, checkLine: now, definition: r.definition, status: r.status, theorem: r.theorem, skipped: r.skipped };
        });
        translated.push(project + '/' + name);
        writeJson(path.join(dir, 'translations', project, name + '.json'), {
            name,
            project,
            def: prog.def,
            file: prog.file,
            line: prog.line,
            doc: prog.doc,
            group: rows[0].group,
            source: prog.source,
            checks,
        });
    }
    writeJson(path.join(dir, 'translations', 'index.json'), translated);
    console.log(`  Lean mechanisation: ${theorems.length} theorems in ${files.filter((f) => theorems.some((t) => t.file === f)).length} files, ${generated.length} generated by #kernel_checks, ${translated.length} test programs translated`);
    return problems;
}

module.exports = { writeMechanisation };
