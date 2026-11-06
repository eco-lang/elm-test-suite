#!/usr/bin/env node
// site-data.js — writes the data the report website (site/) is built from.
//
// Usage:
//   node runner/site-data.js [--out <dir>]
//
// Reads the results of the last run of each compiler in compilers.json (.work/results/<compiler>.json,
// written by run-all.js), the test sources under tests/ and the project descriptions in README.md,
// and writes, under --out (default site/data):
//   report.json               the compilers and their totals, each project's totals per compiler,
//                             and every test whose outcome is not the same under all compilers
//   projects/<project>.json   each test of the project, its summary and its outcome per compiler
//   tests/<project>/<Test>.json
//                             one test: its doc comment, issue links, source, and per compiler its
//                             outcome, failure message and output
// A compiler with no results is left out. The exit status is 2 when no compiler has results.
'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const RESULTS = path.join(ROOT, '.work', 'results');

function parseArgs(argv) {
    const opts = { out: path.join(ROOT, 'site', 'data') };
    for (let i = 0; i < argv.length; i++) {
        if (argv[i] === '--out') opts.out = path.resolve(argv[++i]);
        else throw new Error('unknown option ' + argv[i]);
    }
    return opts;
}

// The `| \`project\` | count | description |` rows of README.md's table of projects.
function projectDescriptions() {
    const readme = fs.readFileSync(path.join(ROOT, 'README.md'), 'utf8');
    const out = {};
    for (const m of readme.matchAll(/^\| `([a-z-]+)` \| \d+ \| (.+) \|$/gm)) out[m[1]] = m[2];
    return out;
}

// The module's doc comment, without its `{-|` and `-}`, or '' when there is none.
function docComment(source) {
    const m = source.match(/\{-\|([\s\S]*?)-\}/);
    return m ? m[1].replace(/^\s+/, '').replace(/\s+$/, '') : '';
}

// The first sentence-ish line of a doc comment, for tables.
function summary(doc) {
    const para = doc.split(/\n\s*\n/)[0] || '';
    return para.replace(/\s+/g, ' ').trim();
}

// Output as a terminal shows it: each line keeps only what follows its last carriage return (the
// compilers redraw "Verifying dependencies (1/4)" and the like in place).
function terminalText(s) {
    return (s || '').split('\n').map((l) => l.replace(/\r+$/, '').replace(/^[^\n]*\r/, '')).join('\n');
}

function writeJson(file, value) {
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, JSON.stringify(value) + '\n');
}

function main() {
    const opts = parseArgs(process.argv.slice(2).filter((a) => a !== '--'));
    const cfg = JSON.parse(fs.readFileSync(path.join(ROOT, 'compilers.json'), 'utf8'));
    const runs = Object.keys(cfg.compilers)
        .map((n) => path.join(RESULTS, n + '.json'))
        .filter((f) => fs.existsSync(f))
        .map((f) => JSON.parse(fs.readFileSync(f, 'utf8')));
    if (!runs.length) throw new Error('no results in ' + RESULTS + '; run `pnpm test:all` first');

    const descriptions = projectDescriptions();
    const projects = [...new Set(runs.flatMap((r) => Object.keys(r.projects)))].sort();
    const missing = { status: 'missing', reason: 'not run', message: '', output: '' };
    const count = (tests) => {
        const c = { pass: 0, fail: 0, skip: 0 };
        for (const t of Object.values(tests || {})) if (t.status in c) c[t.status]++;
        return c;
    };

    if (fs.existsSync(opts.out)) {
        if (path.basename(opts.out) !== 'data') throw new Error('refusing to clear ' + opts.out);
        fs.rmSync(opts.out, { recursive: true, force: true });
    }

    const report = {
        generated: new Date().toISOString(),
        commit: process.env.GITHUB_SHA || '',
        repository: process.env.GITHUB_REPOSITORY || '',
        runUrl: process.env.GITHUB_RUN_ID
            ? `${process.env.GITHUB_SERVER_URL}/${process.env.GITHUB_REPOSITORY}/actions/runs/${process.env.GITHUB_RUN_ID}`
            : '',
        node: runs[0].node || process.version,
        compilers: runs.map((r) => {
            const c = { pass: 0, fail: 0, skip: 0 };
            for (const p of Object.values(r.projects)) {
                const k = count(p);
                c.pass += k.pass; c.fail += k.fail; c.skip += k.skip;
            }
            return { name: r.compiler, version: r.version, description: r.description, target: r.target, ...c };
        }),
        projects: [],
        differing: [],
    };

    for (const p of projects) {
        const srcDir = path.join(ROOT, 'tests', p, 'src');
        const names = [...new Set(runs.flatMap((r) => Object.keys(r.projects[p] || {})))].sort();
        const rows = [];
        for (const name of names) {
            const file = path.join(srcDir, name + '.elm');
            const source = fs.existsSync(file) ? fs.readFileSync(file, 'utf8') : '';
            const doc = docComment(source);
            const outcomes = runs.map((r) => (r.projects[p] || {})[name] || missing);
            const issues = [...new Set(doc.match(/https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/(?:issues|pull)\/\d+/g) || [])];
            rows.push({
                name,
                summary: summary(doc),
                compileError: /^-- COMPILE-ERROR:/m.test(source),
                outcomes: outcomes.map((o) => ({ status: o.status, reason: o.reason || '' })),
            });
            writeJson(path.join(opts.out, 'tests', p, name + '.json'), {
                project: p,
                name,
                doc,
                issues,
                source,
                results: outcomes.map((o, i) => ({
                    compiler: runs[i].compiler,
                    status: o.status,
                    message: terminalText(o.message || o.reason),
                    output: terminalText(o.output),
                    ms: typeof o.ms === 'number' ? o.ms : null,
                })),
            });
            if (new Set(outcomes.map((o) => o.status)).size > 1) {
                report.differing.push({ project: p, test: name, outcomes: outcomes.map((o) => o.status) });
            }
        }
        writeJson(path.join(opts.out, 'projects', p + '.json'), { name: p, description: descriptions[p] || '', tests: rows });
        report.projects.push({
            name: p,
            description: descriptions[p] || '',
            total: names.length,
            counts: runs.map((r) => count(r.projects[p])),
        });
    }
    writeJson(path.join(opts.out, 'report.json'), report);
    console.log('site data for ' + runs.length + ' compiler(s), ' + projects.length + ' projects, written to ' +
        path.relative(ROOT, opts.out));
    return 0;
}

try {
    process.exit(main());
} catch (e) {
    console.error('site-data.js: ' + (e && e.message || e));
    process.exit(2);
}
