#!/usr/bin/env node
// Step 0 of plans/lean-full-definition.md: turns the translator's report of every refusal
// (Translate.elm --report-all-refusals) and a file of hand annotations into the plan's table
// "Part I gains", checking both against the manifest. Prints Markdown; exits 1 on an inconsistency.
//
//   node runner/part1-inventory.js definition/mechanisation/refusal-report.json \
//       definition/mechanisation/refusal-annotations.json
'use strict';
const fs = require('fs');
const path = require('path');

const ROOT = path.join(__dirname, '..');
const [reportPath, annotationsPath] = process.argv.slice(2);
if (!reportPath || !annotationsPath) {
    console.error('usage: node runner/part1-inventory.js REPORT ANNOTATIONS');
    process.exit(2);
}
const report = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
const annotations = JSON.parse(fs.readFileSync(annotationsPath, 'utf8')).annotations;
const manifest = JSON.parse(fs.readFileSync(path.join(ROOT, 'definition/mechanisation/translation-manifest.json'), 'utf8'));

const problems = [];
const tests = report.tests;
if (tests.length !== 939) problems.push(`the report has ${tests.length} entries, not 939`);

const byName = new Map(tests.map((t) => [t.name, t]));
const annotationOf = new Map(annotations.map((a) => [a.name, a]));
for (const a of annotations) if (!byName.has(a.name)) problems.push(`annotation names no test: ${a.name}`);

// The modules of elm/core beyond the default imports, Html and the modules the effect steps
// encode: a test that imports one needs the core library.
const effectModules = new Set(['Task', 'Process', 'Platform', 'Platform.Cmd', 'Platform.Sub']);
// Modules whose dynamic interface the book makes empty and which step 2 adds (decision D3): an
// import of one is a library need only when the test uses one of its values.
const typeOnlyModules = new Set(['Array', 'Bytes', 'Json.Encode', 'Json.Decode', 'VirtualDom']);
// The values of Basics written in Elm, which step 2 encodes (decision D3).
const basicsTexts = new Set(['logBase', 'degrees', 'radians', 'turns', 'fromPolar', 'toPolar', 'never']);
const step2Reason = (r) => r === 'basis:Result.Ok' || r === 'basis:Result.Err' ||
    (r.startsWith('basis:Basics.') && basicsTexts.has(r.slice('basis:Basics.'.length)));

// The reasons that decide a test's step. A refusal of inference or specialisation that follows a
// refusal of an earlier stage is a consequence of the lenient conversion (a name it could not
// resolve), so it counts only when no earlier stage refused. A `basis:Basics.<x>` refusal names a
// value that conversion looked for in Basics: when `x` is a name imported from a local module or
// a port, it is an artefact of the module form, not a need of the basis.
function reasonsOf(t) {
    const earlier = t.refusals.filter((f) => !['infer', 'specialise'].includes(f.stage));
    const used = earlier.length ? earlier : t.refusals;
    const local = (t.localModules || []).length > 0;
    return new Set(
        used
            .map((f) => (f.reason.startsWith('checks:unmatched:') ? 'checks:unmatched' : f.reason))
            .filter((r) => !(r.startsWith('basis:Basics.') && !step2Reason(r) && (local || t.ports)))
            .filter((r) => !(r.startsWith('basis:') && (t.localModules || []).includes(r.slice(6, r.lastIndexOf('.')))))
    );
}

function isLibraryReason(r, t) {
    if (r.startsWith('import:')) {
        const m = r.slice('import:'.length);
        if ((t.localModules || []).includes(m) || m === 'Html' || effectModules.has(m)) return false;
        if (typeOnlyModules.has(m)) return t.refusals.some((f) => f.reason.startsWith(`basis:${m}.`));
        return true;
    }
    if (r.startsWith('basis:')) return !step2Reason(r);
    return false;
}

const subset = (R, allowed) => [...R].every((r) => allowed(r));

function classify(t) {
    const a = annotationOf.get(t.name) || {};
    const R = reasonsOf(t);
    if (a.out) return ['out', a.out];
    if ([...R].some((r) => r === 'parse' || r === 'number' || r.startsWith('construct:large'))) {
        return ['out', [...R].filter((r) => r === 'parse' || r === 'number' || r.startsWith('construct:large')).join(', ')];
    }
    if (a.library) return ['library', a.library];
    if ([...R].some((r) => isLibraryReason(r, t))) return ['library', [...R].filter((r) => isLibraryReason(r, t)).join(', ')];
    if (subset(R, (r) => step2Reason(r) || r === 'type')) return ['2', ''];
    const step3 = (r) =>
        r === 'construct:record-alias-constructor' || r === 'construct:main-shape' || r === 'effects' ||
        r === 'checks:unmatched' || r === 'checks:unlabelled' || r === 'checks:regex' || r === 'type' ||
        (r.startsWith('import:') && typeOnlyModules.has(r.slice('import:'.length))) ||
        (r.startsWith('import:') && (t.localModules || []).includes(r.slice('import:'.length)));
    if (!t.worker && subset(R, step3)) return ['3', ''];
    if (t.worker) {
        if (a.checkNot) return ['6', a.checkNot];
        if (a.partial) return ['5', a.partial];
        if (R.has('checks:check-not')) return ['unclassified', 'a CHECK-NOT worker with no annotation'];
        return ['5', ''];
    }
    return ['unclassified', [...R].join(', ')];
}

const manifestByName = new Map(manifest.tests.map((t) => [t.name, t]));
const rows = new Map();
for (const t of tests) {
    const m = manifestByName.get(t.name);
    if (!m) { problems.push(`not in the manifest: ${t.name}`); continue; }
    if (m.status === 'translated') {
        if (t.refusals.length) problems.push(`translated in the manifest but refused in the report: ${t.name}`);
        continue;
    }
    const first = t.refusals[0];
    if (!first) { problems.push(`refused in the manifest but not in the report: ${t.name}`); continue; }
    const same = first.reason === m.reason || (m.reason === 'type' && first.reason.startsWith('unknown-type:'));
    if (!same) problems.push(`${t.name}: the report's first refusal is ${first.reason}, the manifest's ${m.reason}`);
    if (m.reason === 'compile-error') continue;
    const [step, why] = classify(t);
    if (step === 'unclassified') problems.push(`not classified: ${t.name} (${why})`);
    if (!rows.has(step)) rows.set(step, []);
    rows.get(step).push(why ? `${t.name} (${why})` : t.name);
}

const order = ['2', '3', '5', '6', 'library', 'out', 'unclassified'];
let total = 0;
console.log('| Step | Tests | Which |');
console.log('|-----:|------:|-------|');
for (const step of order) {
    const names = rows.get(step) || [];
    if (!names.length) continue;
    total += names.length;
    console.log(`| ${step} | ${names.length} | ${names.sort().join(', ')} |`);
}
const gains = ['2', '3', '5', '6'].reduce((n, s) => n + (rows.get(s) || []).length, 0);
console.log(`\nRefused tests that do not expect a compile error: ${total}; Part I gains: ${gains}.`);

if (problems.length) {
    console.error(`\n${problems.length} problem(s):`);
    for (const p of problems) console.error(`  ${p}`);
    process.exit(1);
}
