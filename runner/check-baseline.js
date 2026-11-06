#!/usr/bin/env node
// check-baseline.js — fails when the default compiler fails a test it is expected to pass.
//
// Usage:
//   node runner/check-baseline.js [--compiler <name>] [--expect-failures <project>[,<project>...]]
//
// Reads .work/results/<compiler>.json (default: compilers.json's "default") and exits 1 if a test
// failed outside the projects named by --expect-failures (default: elm-bugs,elm-bug-fixes, whose
// tests expect the correct behaviour where Elm 0.19.1 has a bug), listing each such test. CI runs
// it after publishing the report, so a regression still gets a report.
'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');

function main() {
    const argv = process.argv.slice(2).filter((a) => a !== '--');
    const cfg = JSON.parse(fs.readFileSync(path.join(ROOT, 'compilers.json'), 'utf8'));
    let compiler = cfg.default;
    let expected = ['elm-bugs', 'elm-bug-fixes'];
    for (let i = 0; i < argv.length; i++) {
        if (argv[i] === '--compiler') compiler = argv[++i];
        else if (argv[i] === '--expect-failures') expected = argv[++i].split(',').map((s) => s.trim()).filter(Boolean);
        else throw new Error('unknown option ' + argv[i]);
    }
    const file = path.join(ROOT, '.work', 'results', compiler + '.json');
    if (!fs.existsSync(file)) throw new Error('no results for ' + compiler + ' (' + file + ')');
    const results = JSON.parse(fs.readFileSync(file, 'utf8'));
    const failures = [];
    for (const [project, tests] of Object.entries(results.projects)) {
        if (expected.includes(project)) continue;
        for (const [name, t] of Object.entries(tests)) {
            if (t.status === 'fail') failures.push(project + '/' + name + ': ' + t.reason);
        }
    }
    if (failures.length) {
        console.log(compiler + ' failed ' + failures.length + ' test(s) outside ' + expected.join(', ') + ':');
        for (const f of failures) console.log('  ' + f);
        return 1;
    }
    console.log(compiler + ' passed every test outside ' + expected.join(', '));
    return 0;
}

try {
    process.exit(main());
} catch (e) {
    console.error('check-baseline.js: ' + (e && e.message || e));
    process.exit(2);
}
