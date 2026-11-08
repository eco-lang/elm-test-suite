// spec-items.js: the names of the rules and restrictions of A Standard Definition of Elm?, read from
// its LaTeX sources (definition/tex/), so that a test's tag naming one is known as a check of it.
// A rule is written `\defnrule[r:<name>]`, a restriction `\citelabel{res:<name>}`; the names are the
// stable addresses of their pages (/standard/rules/<name>, /standard/restrictions/<name>).
'use strict';

const fs = require('fs');
const path = require('path');

const TEX = path.resolve(__dirname, '..', 'definition', 'tex');

// Map name -> 'rule' | 'restriction'.
function specItems() {
    const items = new Map();
    for (const f of fs.readdirSync(TEX).filter((n) => n.endsWith('.tex')).sort()) {
        const src = fs.readFileSync(path.join(TEX, f), 'utf8');
        for (const m of src.matchAll(/\\defnrule\[r:([^\]]+)\]/g)) items.set(m[1], 'rule');
        for (const m of src.matchAll(/\\citelabel\{res:([^}]+)\}/g)) items.set(m[1], 'restriction');
    }
    return items;
}

module.exports = { specItems };
