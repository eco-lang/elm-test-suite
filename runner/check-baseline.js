#!/usr/bin/env node
// check-baseline.js: reports the tests the default compiler fails that are not tagged to fail.
//
// Usage:
//   node runner/check-baseline.js [--compiler <name>] [--expect-failures <tag>[,<tag>...]]
//
// Reads .work/results/<compiler>.json (default: compilers.json's "default") and lists, in Markdown,
// each test that failed and has none of the tags named by --expect-failures (default: elm19-bug,
// elm19-bug-fix, whose tests expect the correct behaviour where Elm 0.19.1 has a bug). A tag may be
// a project's name, since every test is tagged with its project. A test marked `-- XFAIL:` is
// expected to fail too; one that passes is listed as an unexpected pass. The suite
// reports on compilers already released, so a failure is a finding, never an error: the exit
// status is 0 whatever the results, and 2 only on a usage error or missing results.
'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');

function main() {
    const argv = process.argv.slice(2).filter((a) => a !== '--');
    const cfg = JSON.parse(fs.readFileSync(path.join(ROOT, 'compilers.json'), 'utf8'));
    let compiler = cfg.default;
    let expected = ['elm19-bug', 'elm19-bug-fix'];
    for (let i = 0; i < argv.length; i++) {
        if (argv[i] === '--compiler') compiler = argv[++i];
        else if (argv[i] === '--expect-failures') expected = argv[++i].split(',').map((s) => s.trim()).filter(Boolean);
        else throw new Error('unknown option ' + argv[i]);
    }
    const file = path.join(ROOT, '.work', 'results', compiler + '.json');
    if (!fs.existsSync(file)) throw new Error('no results for ' + compiler + ' (' + file + ')');
    const results = JSON.parse(fs.readFileSync(file, 'utf8'));
    const failures = [];
    const xpasses = [];
    for (const [project, tests] of Object.entries(results.projects)) {
        for (const [name, t] of Object.entries(tests)) {
            const tags = t.tags || [project];
            if (t.status === 'fail' && !t.xfail && !tags.some((g) => expected.includes(g))) {
                failures.push(project + '/' + name + ': ' + t.reason);
            }
            if (t.status === 'pass' && t.xfail) xpasses.push(project + '/' + name + ': expected to fail, ' + t.xfail);
        }
    }
    const outside = 'not tagged ' + expected.join(' or ') + ' nor marked XFAIL';
    console.log('## ' + compiler + ': tests ' + outside + '\n');
    if (failures.length) {
        console.log(compiler + ' failed ' + failures.length + ' test(s) ' + outside + ':\n');
        for (const f of failures) console.log('- ' + f.replace(/\n/g, ' '));
    } else {
        console.log(compiler + ' passed every test ' + outside + '.');
    }
    if (xpasses.length) {
        console.log('\n' + compiler + ' passed ' + xpasses.length + ' test(s) marked XFAIL:\n');
        for (const f of xpasses) console.log('- ' + f.replace(/\n/g, ' '));
    }
    return 0;
}

try {
    process.exit(main());
} catch (e) {
    console.error('check-baseline.js: ' + (e && e.message || e));
    process.exit(2);
}
