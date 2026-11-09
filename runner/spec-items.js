// spec-items.js: the names of the rules, restrictions, derived forms and entries of the initial basis
// of A Standard Definition of Elm?, read from its LaTeX sources (definition/tex/), so that a test's
// tag naming one is known as a check of it. A rule is written `\defnrule[r:<name>]` and tagged
// `<name>`; a restriction `\citelabel{res:<name>}`, tagged `<name>`; a derived form
// `\citelabel{df:<name>}`, tagged `df:<name>`; an entry of the basis `\citelabel{b:<name>}`, tagged
// `b:<name>` (`b:Basics.compare`). The names are the stable addresses of their pages
// (/standard/rules/<name>, /standard/restrictions/<name>, /standard/derived-forms/<name>,
// /standard/basis/Basics/compare). A figure or section, `\label{fig:<name>}` or
// `\label{sec:<name>}`, is tagged by its label (`fig:core-grammar-patterns`, `sec:syntax-core-layout`).
// A figure has a page (/standard/figures/core-grammar-patterns); a section has none, so it is a place
// in its chapter (/standard/syntax-core#sec-syntax-core-layout). Figures are for what the book
// defines only by a figure, such as its grammar.
'use strict';

const fs = require('fs');
const path = require('path');

const TEX = path.resolve(__dirname, '..', 'definition', 'tex');

// Map tag -> 'rule' | 'restriction' | 'derived-form' | 'basis' | 'figure' | 'section'.
function specItems() {
    const items = new Map();
    for (const f of fs.readdirSync(TEX).filter((n) => n.endsWith('.tex')).sort()) {
        const src = fs.readFileSync(path.join(TEX, f), 'utf8');
        for (const m of src.matchAll(/\\defnrule\[r:([^\]]+)\]/g)) items.set(m[1], 'rule');
        for (const m of src.matchAll(/\\citelabel\{res:([^}]+)\}/g)) items.set(m[1], 'restriction');
        for (const m of src.matchAll(/\\citelabel\{df:([^}]+)\}/g)) items.set('df:' + m[1], 'derived-form');
        for (const m of src.matchAll(/\\citelabel\{b:([^}]+)\}/g)) items.set('b:' + m[1], 'basis');
        for (const p of placesIn(f, src).keys()) items.set(p, p.startsWith('fig:') ? 'figure' : 'section');
    }
    return items;
}

// The figures and sections of one chapter's source: tag -> { chapter, anchor, title }. The chapter is
// the file's name, the anchor the label with `:` as `-` (as definition-data.js writes it), the title
// the figure's caption or the section's heading, with its TeX reduced to plain text.
function placesIn(file, src) {
    const plain = (t) => t.replace(/\\[a-zA-Z]+\*?(\{\})?/g, '').replace(/[{}~]/g, ' ').replace(/\s+/g, ' ').trim();
    const places = new Map();
    for (const m of src.matchAll(/\\label\{((fig|sec):[a-z0-9-]+)\}/g)) {
        const before = src.slice(Math.max(0, m.index - 600), m.index);
        const heads = [...before.matchAll(m[2] === 'fig' ? /\\caption\{([^}]*)\}/g : /\\(?:sub)*section\*?\{([^}]*)\}/g)];
        places.set(m[1], {
            chapter: path.basename(file, '.tex'),
            anchor: m[1].replace(':', '-'),
            title: heads.length ? plain(heads[heads.length - 1][1]) : m[1],
        });
    }
    return places;
}

// Every figure and section of the book: tag -> { chapter, anchor, title }.
function specPlaces() {
    const all = new Map();
    for (const f of fs.readdirSync(TEX).filter((n) => n.endsWith('.tex')).sort()) {
        for (const [k, v] of placesIn(f, fs.readFileSync(path.join(TEX, f), 'utf8'))) all.set(k, v);
    }
    return all;
}

// The name of an item's page: its tag without the `df:`, `b:` or `fig:` in front.
const itemName = (tag) => tag.replace(/^(df|b|fig):/, '');

module.exports = { specItems, specPlaces, itemName };
