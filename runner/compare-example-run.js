#!/usr/bin/env node
// Compares two runs of the mechanisation's examples (definition/mechanisation/example-run.json),
// as plans/lean-full-definition/step-03-module-form.md specifies for the migration of the checks
// from the let form to the module form: for every row of the old run, the new run has a row with
// the same program and label, the same expected value, a status beginning with "agree", and the
// same definition list. Prints the rows that differ and exits 1 unless every difference is one
// the plan allows.
//
// Usage: node runner/compare-example-run.js OLD.json NEW.json

'use strict';

const fs = require('fs');

// The differences the plan allows (step 3, "Migration of the existing checks"): the strict
// programs have no meaning in module form; the values they log before they stop come from the
// partial log, with no theorem.
const ALLOWED = [
  { program: 'StandardLetStrictTest', label: 'before', definition: ['()'] },
  { program: 'StandardLetStrictTest', label: 'let strict', definition: ['(no meaning)'] },
  { program: 'StandardApplicationStrictTest', label: 'before', definition: ['()'] },
  { program: 'StandardApplicationStrictTest', label: 'app strict', definition: ['(no meaning)'] },
];

function main(argv) {
  if (argv.length !== 2) {
    console.error('usage: node runner/compare-example-run.js OLD.json NEW.json');
    return 2;
  }
  const [oldRun, newRun] = argv.map((f) => JSON.parse(fs.readFileSync(f, 'utf8')));
  const key = (r) => `${r.program}\u0000${r.label}`;
  const fresh = new Map();
  for (const r of newRun.checks) {
    const k = key(r);
    if (!fresh.has(k)) fresh.set(k, []);
    fresh.get(k).push(r);
  }
  const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
  const allowed = (o, n) =>
    ALLOWED.some(
      (a) => a.program === o.program && a.label === o.label && n && same(n.definition, a.definition),
    );
  const differ = [];
  let unexplained = 0;
  for (const o of oldRun.checks) {
    const ns = fresh.get(key(o)) || [];
    const n = ns.find((r) => r.expected === o.expected);
    const ok =
      n && n.status.startsWith('agree') && same(n.definition, o.definition);
    if (ok) continue;
    const isAllowed = allowed(o, n) && n.status.startsWith('agree');
    if (!isAllowed) unexplained += 1;
    differ.push({
      program: o.program,
      label: o.label,
      old: `${o.definition.join(' or ')} (${o.status}${o.theorem ? `, ${o.theorem}` : ''})`,
      new: n
        ? `${n.definition.join(' or ')} (${n.status}${n.theorem ? `, ${n.theorem}` : ''})`
        : '(missing)',
      allowed: isAllowed,
    });
  }
  const added = newRun.checks.filter(
    (n) => !oldRun.checks.some((o) => key(o) === key(n) && o.expected === n.expected),
  );
  for (const d of differ) {
    console.log(`${d.allowed ? 'allowed' : 'DIFFERS'}: ${d.program}: ${d.label}: old ${d.old}; new ${d.new}`);
  }
  console.log(
    `compare-example-run: ${oldRun.checks.length} old rows, ${newRun.checks.length} new rows; ` +
      `${differ.length} differ (${differ.length - unexplained} allowed, ${unexplained} not); ` +
      `${added.length} new rows not in the old run`,
  );
  return unexplained === 0 ? 0 : 1;
}

process.exitCode = main(process.argv.slice(2));
