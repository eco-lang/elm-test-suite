#!/usr/bin/env node
// run-all.js — runs the suite with several compilers and reports where their outcomes differ.
//
// Usage:
//   node runner/run-all.js [--compilers <name>[,<name>...]] [any run.js option but --compiler/--json]
//   node runner/run-all.js --report-only [--compilers ...]
//
// Without --compilers every compiler of compilers.json runs, one after the other (each with
// runner/run.js, its results in .work/results/<compiler>.json). --report-only skips the runs and
// reports on the stored results. The report goes to the console and to .work/report.md:
//   - per compiler: version, and tests passed, failed and skipped;
//   - per project: the same, one column per compiler; and likewise per tag (`-- TAGS:`);
//   - every test whose outcome is not the same under all compilers, with each compiler's outcome
//     and, for a failure, the first line of its reason;
//   - how many results came from the result cache, and (after --refresh) every result that differs
//     from the cached one. --no-cache and --refresh are passed on to run.js.
// The exit status is 0 when every compiler ran (whatever its results), 2 on a usage error.
'use strict';

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const ROOT = path.resolve(__dirname, '..');
const RESULTS = path.join(ROOT, '.work', 'results');

function parseArgs(argv) {
    const opts = { compilers: null, reportOnly: false, pass: [] };
    for (let i = 0; i < argv.length; i++) {
        const a = argv[i];
        if (a === '--compilers' || a.startsWith('--compilers=')) {
            const v = a.includes('=') ? a.slice(a.indexOf('=') + 1) : argv[++i];
            opts.compilers = v.split(',').map((s) => s.trim()).filter(Boolean);
        } else if (a === '--report-only') {
            opts.reportOnly = true;
        } else if (a === '--help' || a === '-h') {
            console.log(fs.readFileSync(__filename, 'utf8').split('\n').slice(1, 17)
                .map((l) => l.replace(/^\/\/ ?/, '')).join('\n'));
            process.exit(0);
        } else if (a === '--compiler' || a.startsWith('--compiler=') || a === '--json' || a.startsWith('--json=')) {
            throw new Error(a + ' is set per compiler by run-all.js');
        } else {
            opts.pass.push(a);
        }
    }
    return opts;
}

const short = (s, n) => (s.length > n ? s.slice(0, n - 1) + '…' : s);

function report(names) {
    const runs = names.map((n) => {
        const f = path.join(RESULTS, n + '.json');
        if (!fs.existsSync(f)) throw new Error('no results for ' + n + ' (' + f + '); run it first');
        return JSON.parse(fs.readFileSync(f, 'utf8'));
    });
    const projects = [...new Set(runs.flatMap((r) => Object.keys(r.projects)))].sort();
    const out = [];
    const count = (tests, status) => Object.values(tests || {}).filter((t) => t.status === status).length;

    out.push('# Elm test suite: comparison of ' + names.length + ' compilers', '');
    out.push('| Compiler | Version | Target | Passed | Failed | Skipped |', '|---|---|---|---|---|---|');
    for (const r of runs) {
        const all = Object.assign({}, ...Object.entries(r.projects).map(([p, t]) =>
            Object.fromEntries(Object.entries(t).map(([k, v]) => [p + '/' + k, v]))));
        out.push(`| ${r.compiler} | ${r.version} | ${r.target} | ${count(all, 'pass')} | ${count(all, 'fail')} | ${count(all, 'skip')} |`);
    }
    out.push('', '## By project (passed / failed / skipped)', '');
    out.push('| Project | ' + names.join(' | ') + ' |', '|---|' + names.map(() => '---|').join(''));
    for (const p of projects) {
        out.push('| ' + p + ' | ' + runs.map((r) => {
            const t = r.projects[p];
            return t ? `${count(t, 'pass')} / ${count(t, 'fail')} / ${count(t, 'skip')}` : '–';
        }).join(' | ') + ' |');
    }
    // Every tag but the projects' (each test is tagged with its project): the same totals.
    const tags = [...new Set(runs.flatMap((r) => Object.values(r.projects).flatMap((ts) =>
        Object.values(ts).flatMap((t) => t.tags || []))))].filter((g) => !projects.includes(g)).sort();
    if (tags.length) {
        out.push('', '## By tag (passed / failed / skipped)', '');
        out.push('| Tag | ' + names.join(' | ') + ' |', '|---|' + names.map(() => '---|').join(''));
        for (const g of tags) {
            out.push('| ' + g + ' | ' + runs.map((r) => {
                const t = Object.values(r.projects).flatMap((ts) => Object.values(ts)).filter((x) => (x.tags || []).includes(g));
                return `${count(t, 'pass')} / ${count(t, 'fail')} / ${count(t, 'skip')}`;
            }).join(' | ') + ' |');
        }
    }
    const diffs = [];
    for (const p of projects) {
        const tests = [...new Set(runs.flatMap((r) => Object.keys(r.projects[p] || {})))].sort();
        for (const t of tests) {
            const outcomes = runs.map((r) => (r.projects[p] || {})[t] || { status: 'missing', reason: '' });
            if (new Set(outcomes.map((o) => o.status)).size > 1) diffs.push({ test: p + '/' + t, outcomes });
        }
    }
    out.push('', '## Tests whose outcome differs (' + diffs.length + ')', '');
    if (diffs.length) {
        out.push('| Test | ' + names.join(' | ') + ' |', '|---|' + names.map(() => '---|').join(''));
        for (const d of diffs) {
            out.push('| ' + d.test + ' | ' + d.outcomes.map((o) =>
                o.status === 'pass' ? 'pass' : o.status + (o.reason ? ': ' + short(o.reason, 70).replace(/\|/g, '\\|') : '')
            ).join(' | ') + ' |');
        }
    } else {
        out.push('None: every test has the same outcome under every compiler.');
    }
    // The result cache (run.js): how many results it gave, and with --refresh, every result that
    // differs from the one the cache held (a flaky test, or an input missing from the cache's key).
    if (runs.some((r) => r.cache)) {
        out.push('', '## The result cache', '');
        out.push(runs.map((r) => r.compiler + ': ' + (r.cache ? r.cache.hits + ' from the cache, ' + r.cache.written + ' run and kept' : 'not used')).join('; ') + '.');
        const mismatches = runs.flatMap((r) => ((r.cache || {}).mismatches || []).map((m) => Object.assign({ compiler: r.compiler }, m)));
        if (mismatches.length) {
            out.push('', '### Results that differ from the cache (' + mismatches.length + ')', '');
            out.push('| Compiler | Test | Cached | Now |', '|---|---|---|---|');
            for (const m of mismatches) out.push(`| ${m.compiler} | ${m.test} | ${m.was} (${m.ranAt.slice(0, 10)}) | ${m.now} |`);
        }
    }
    const text = out.join('\n') + '\n';
    fs.mkdirSync(path.join(ROOT, '.work'), { recursive: true });
    fs.writeFileSync(path.join(ROOT, '.work', 'report.md'), text);
    console.log('\n' + text + '\n(written to .work/report.md)');
}

function main() {
    const opts = parseArgs(process.argv.slice(2).filter((a) => a !== '--'));   // pnpm passes `--` through
    const cfg = JSON.parse(fs.readFileSync(path.join(ROOT, 'compilers.json'), 'utf8'));
    const names = opts.compilers || Object.keys(cfg.compilers);
    const unknown = names.filter((n) => !cfg.compilers[n]);
    if (unknown.length) throw new Error('unknown compiler(s): ' + unknown.join(', '));
    if (!opts.reportOnly) {
        for (const n of names) {
            console.log('\n=== ' + n + ' ===');
            const r = spawnSync(process.execPath,
                [path.join(__dirname, 'run.js'), '--compiler', n, '--json', path.join(RESULTS, n + '.json'), ...opts.pass],
                { stdio: 'inherit' });
            if (r.status === 2) throw new Error(n + ' could not run (see above)');
        }
    }
    report(names);
    return 0;
}

try {
    process.exit(main());
} catch (e) {
    console.error('run-all.js: ' + (e && e.message || e));
    process.exit(2);
}
