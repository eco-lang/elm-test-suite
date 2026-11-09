#!/usr/bin/env node
// definition-data.js: writes the data from which the website (site/) shows A Standard Definition of Elm?
//
// Usage:
//   node runner/definition-data.js [--out <dir>] [--check-aux <dir>]
//
// Reads the LaTeX sources of the book under definition/tex/ (the master file
// standard-elm-definition.tex, the chapters it includes, defn.sty and macros.sty) and writes, under
// --out (default site/data-standard):
//   index.json               the title, edition, contents (chapters and their sections) and the list
//                            of every rule
//   chapters/<slug>.json     one chapter: its text as blocks, with rules, figures and tables
//   rules/<label>.json       one rule: its rule group, comments, place in the book and the places
//                            that refer to it
// It also copies the PDF of the edition (definition/*.pdf) to site/public/downloads/, and writes the
// Lean proofs of the mechanisation (definition/mechanisation/) under mechanisation/, with
// runner/mechanisation-data.js.
//
// Mathematics is rendered with KaTeX here, at build time, using the book's own macros, and stored as
// a tree of elements (["span", {"class": "mord"}, [children]], or a string for text) that the site
// turns into Html; the site ships no KaTeX JavaScript, only its stylesheet and fonts.
//
// The converter knows the commands and environments the book uses, from defn.sty and the standard
// LaTeX it relies on. Anything it does not know is kept as visible raw TeX and listed at the end, as
// is any formula KaTeX cannot render and any \ref to a missing label; then the exit status is 1.
//
// --check-aux <dir> compares the numbers given to chapters, sections, figures and rules with those
// in the .aux files of a LaTeX build of the same sources, and fails on any difference.
'use strict';

const fs = require('fs');
const path = require('path');
const katex = require('katex');
const { writeMechanisation } = require('./mechanisation-data');

const ROOT = path.resolve(__dirname, '..');
const DEF = path.join(ROOT, 'definition');
const TEX = path.join(DEF, 'tex');
const MASTER = 'standard-elm-definition.tex';

function parseArgs(argv) {
    const opts = { out: path.join(ROOT, 'site', 'data-standard'), checkAux: null };
    for (let i = 0; i < argv.length; i++) {
        if (argv[i] === '--out') opts.out = path.resolve(argv[++i]);
        else if (argv[i] === '--check-aux') opts.checkAux = path.resolve(argv[++i]);
        else throw new Error('unknown option ' + argv[i]);
    }
    return opts;
}

const problems = { unknown: new Map(), katex: [], refs: new Set() };

function noteUnknown(name, where) {
    const k = '\\' + name;
    if (!problems.unknown.has(k)) problems.unknown.set(k, { count: 0, where });
    problems.unknown.get(k).count++;
}

// ---------------------------------------------------------------------------------------------
// Low-level scanning
// ---------------------------------------------------------------------------------------------

const isLetter = (c) => /[A-Za-z]/.test(c || '');

// The balanced group that opens at s[i] === '{'; returns [content, index after '}'].
function group(s, i) {
    if (s[i] !== '{') throw new Error('expected { at ' + JSON.stringify(s.slice(i, i + 40)));
    let depth = 0;
    for (let j = i; j < s.length; j++) {
        const c = s[j];
        if (c === '\\') { j++; continue; }
        if (c === '{') depth++;
        else if (c === '}' && --depth === 0) return [s.slice(i + 1, j), j + 1];
    }
    throw new Error('unbalanced { in ' + JSON.stringify(s.slice(i, i + 60)));
}

// An optional argument [..] at s[i] (after spaces), or null.
function optional(s, i) {
    let j = skipSpace(s, i);
    if (s[j] !== '[') return null;
    let depth = 0;
    for (let k = j + 1; k < s.length; k++) {
        const c = s[k];
        if (c === '\\') { k++; continue; }
        if (c === '{') depth++;
        else if (c === '}') depth--;
        else if (c === ']' && depth === 0) return [s.slice(j + 1, k), k + 1];
    }
    throw new Error('unbalanced [ in ' + JSON.stringify(s.slice(j, j + 60)));
}

// Spaces and at most one newline: what TeX skips before an argument.
function skipSpace(s, i) {
    let nl = 0;
    while (i < s.length && /\s/.test(s[i])) {
        if (s[i] === '\n' && ++nl > 1) break;
        i++;
    }
    return i;
}

// A mandatory argument: a group, or a single token.
function arg(s, i) {
    const j = skipSpace(s, i);
    if (s[j] === '{') return group(s, j);
    if (s[j] === '\\') {
        let k = j + 1;
        if (isLetter(s[k])) while (isLetter(s[k])) k++;
        else k++;
        return [s.slice(j, k), k];
    }
    return [s[j], j + 1];
}

// The command name after the backslash at s[i]: letters (and a trailing *), or one other character.
function commandName(s, i) {
    let j = i + 1;
    if (isLetter(s[j])) {
        while (isLetter(s[j])) j++;
        if (s[j] === '*') j++;
    } else {
        j++;
    }
    return [s.slice(i + 1, j), j];
}

// The index of the \end{name} that closes an environment whose body starts at i.
function envEnd(s, name, i) {
    const open = '\\begin{' + name + '}';
    const close = '\\end{' + name + '}';
    let depth = 1;
    let j = i;
    while (j < s.length) {
        const o = s.indexOf(open, j);
        const c = s.indexOf(close, j);
        if (c < 0) throw new Error('no ' + close);
        if (o >= 0 && o < c) { depth++; j = o + open.length; continue; }
        if (--depth === 0) return [c, c + close.length];
        j = c + close.length;
    }
    throw new Error('no ' + close);
}

// The end of inline math that opened before i: the next unescaped $.
function dollarEnd(s, i) {
    for (let j = i; j < s.length; j++) {
        if (s[j] === '\\') { j++; continue; }
        if (s[j] === '$') return j;
    }
    throw new Error('unclosed $ near ' + JSON.stringify(s.slice(i - 20, i + 40)));
}

// Comments go, with the newline and the next line's leading spaces, as in TeX.
function stripComments(s) {
    let out = '';
    let i = 0;
    while (i < s.length) {
        const c = s[i];
        if (c === '\\') { out += s.slice(i, i + 2); i += 2; continue; }
        if (c === '%') {
            let j = s.indexOf('\n', i);
            if (j < 0) break;
            j++;
            while (s[j] === ' ' || s[j] === '\t') j++;
            i = j;
            continue;
        }
        out += c;
        i++;
    }
    return out;
}

// ---------------------------------------------------------------------------------------------
// Macros
// ---------------------------------------------------------------------------------------------

// Every \newcommand{\name}[n]{body} and \newenvironment{name}{begin}{end} in a source.
function definitions(src) {
    const cmds = new Map();
    const envs = new Map();
    let i = 0;
    while ((i = src.indexOf('\\new', i)) >= 0) {
        const [name, after] = commandName(src, i);
        if (name === 'newcommand' || name === 'renewcommand') {
            let [target, j] = arg(src, after);
            target = target.trim().replace(/^\\/, '');
            const o = optional(src, j);
            let n = 0;
            if (o) { n = parseInt(o[0], 10); j = o[1]; }
            const [body, k] = arg(src, j);
            cmds.set(target, { n, body, start: i, stop: k });
            i = k;
        } else if (name === 'newenvironment') {
            const [target, j] = arg(src, after);
            const [begin, k] = arg(src, j);
            const [end, l] = arg(src, k);
            envs.set(target, { begin, end, start: i, stop: l });
            i = l;
        } else {
            i = after;
        }
    }
    return { cmds, envs };
}

const defnSty = stripComments(fs.readFileSync(path.join(TEX, 'defn.sty'), 'utf8'));
const macrosSty = stripComments(fs.readFileSync(path.join(TEX, 'macros.sty'), 'utf8'));
const defnDefs = definitions(defnSty);
const notationDefs = definitions(macrosSty);

// Layout commands and environments of defn.sty that this converter expands as text before parsing:
// they turn into ordinary tabular, quote and so on.
const EXPAND_CMDS = ['gprod', 'galt', 'gnote', 'objrow', 'objdef', 'dform'];
const EXPAND_ENVS = ['grammar', 'objtable', 'derivedforms', 'property'];

// KaTeX's macro table: the notation, plus defn.sty's typefaces and options, with the few LaTeX
// primitives KaTeX lacks given meanings it has.
const KATEX_MACROS = {};
for (const [name, d] of notationDefs.cmds) KATEX_MACROS['\\' + name] = d.body;
for (const name of ['kw', 'mv', 'cls', 'opt', 'optt', 'premsep']) KATEX_MACROS['\\' + name] = defnDefs.cmds.get(name).body;
Object.assign(KATEX_MACROS, {
    '\\ensuremath': '#1',
    '\\kwlb': '\\{',
    '\\kwrb': '\\}',
    '\\textsuperscript': '^{\\text{#1}}',
    '\\fgderived': '{}^{\\dagger}',
});

// Arities of the notation macros, for reading their arguments where they appear in running text.
const NOTATION_ARITY = new Map();
for (const [name, d] of notationDefs.cmds) NOTATION_ARITY.set(name, d.n);
for (const name of ['mv', 'cls', 'opt', 'optt']) NOTATION_ARITY.set(name, 1);

// Expands the given commands and environments in s, textually, until none is left.
function expand(s, cmds, envs) {
    for (let round = 0; round < 50; round++) {
        let changed = false;
        for (const [name, d] of envs) {
            const b = '\\begin{' + name + '}';
            const e = '\\end{' + name + '}';
            if (s.includes(b)) { s = s.split(b).join(d.begin); changed = true; }
            if (s.includes(e)) { s = s.split(e).join(d.end); changed = true; }
        }
        for (const [name, d] of cmds) {
            let i = 0;
            while ((i = s.indexOf('\\' + name, i)) >= 0) {
                const [n, after] = commandName(s, i);
                if (n !== name) { i = after; continue; }
                let j = after;
                const args = [];
                for (let k = 0; k < d.n; k++) {
                    const [a, next] = arg(s, j);
                    args.push(a);
                    j = next;
                }
                const body = d.body.replace(/#(\d)/g, (_, k) => args[k - 1]);
                s = s.slice(0, i) + body + s.slice(j);
                changed = true;
            }
        }
        if (!changed) return s;
    }
    throw new Error('macro expansion did not terminate');
}

// ---------------------------------------------------------------------------------------------
// KaTeX
// ---------------------------------------------------------------------------------------------

const MATHML = new Set(['math']);

function decodeEntities(t) {
    return t.replace(/&(#x[0-9a-fA-F]+|#\d+|amp|lt|gt|quot|apos|nbsp);/g, (_, e) => {
        if (e[0] === '#') return String.fromCodePoint(e[1] === 'x' ? parseInt(e.slice(2), 16) : parseInt(e.slice(1), 10));
        return { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: '\u00a0' }[e];
    });
}

// KaTeX's markup as a tree: ["tag", {attrs}, [children]] or a string. KaTeX writes regular markup
// (quoted attributes, closed tags), which is all this reads; the tree is serialised again and
// compared with the original, so anything it misreads stops the run.
function htmlTree(html) {
    const root = ['#root', {}, []];
    const stack = [root];
    const re = /<(\/?)([a-zA-Z][\w-]*)((?:\s+[\w:-]+(?:\s*=\s*(?:"[^"]*"|'[^']*'))?)*)\s*(\/?)>|([^<]+)/g;
    let m;
    let consumed = 0;
    while ((m = re.exec(html))) {
        if (m.index !== consumed) throw new Error('unreadable KaTeX markup at ' + html.slice(consumed, consumed + 40));
        consumed = re.lastIndex;
        if (m[5] !== undefined) {
            stack[stack.length - 1][2].push(decodeEntities(m[5]));
            continue;
        }
        const [, closing, tag, attrText, selfClose] = m;
        if (closing) {
            const top = stack.pop();
            if (top[0] !== tag) throw new Error('mismatched </' + tag + '> in KaTeX markup');
            continue;
        }
        const attrs = {};
        for (const a of attrText.matchAll(/([\w:-]+)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'))?/g)) {
            if (a[1] === 'xmlns') continue;
            attrs[a[1]] = decodeEntities(a[2] !== undefined ? a[2] : a[3] !== undefined ? a[3] : '');
        }
        const node = [tag, attrs, []];
        stack[stack.length - 1][2].push(node);
        if (!selfClose) stack.push(node);
    }
    if (consumed !== html.length || stack.length !== 1) throw new Error('unbalanced KaTeX markup');
    return root[2];
}

function textOf(tree) {
    return tree.map((n) => (typeof n === 'string' ? n : textOf(n[2]))).join('');
}

const katexCache = new Map();

// Labels known from a first pass over the book, for the \ref commands inside formulas.
let KNOWN_LABELS = new Map();

// KaTeX's array has no @{...} column material and no [t] position: the material moves into the
// cells it separates, and the position goes.
function fixArrays(tex) {
    let out = '';
    let i = 0;
    for (;;) {
        const b = tex.indexOf('\\begin{array}', i);
        if (b < 0) return out + tex.slice(i);
        out += tex.slice(i, b);
        let j = b + '\\begin{array}'.length;
        const o = optional(tex, j);
        if (o) j = o[1];
        const [spec, k] = group(tex, skipSpace(tex, j));
        const [bodyEnd, next] = envEnd(tex, 'array', k);
        const body = fixArrays(tex.slice(k, bodyEnd));
        let cols = '';
        let before = '';
        const after = [];
        for (let x = 0; x < spec.length; x++) {
            const c = spec[x];
            if (c === '@') {
                const [g, y] = group(spec, x + 1);
                const n = cols.replace(/\|/g, '').length;
                if (n === 0) before += g;
                else after[n - 1] = (after[n - 1] || '') + g;
                x = y - 1;
            } else if ('lcr|'.includes(c)) {
                cols += c;
            } else if ('pmb'.includes(c)) {
                const [, y] = group(spec, x + 1);
                cols += 'l';
                x = y - 1;
            } else if (!/\s/.test(c)) {
                throw new Error('array column type ' + c + ' in ' + spec);
            }
        }
        // Rows and cells: KaTeX has no \\multicolumn either, so a spanning cell becomes its content
        // in the first of the columns it spans.
        const rows = splitTop(body, '\\\\');
        const newBody = rows
            .map((row, r) => {
                const sep = rows.seps[r] || '';
                const cells = [];
                for (const cell of splitTop(row, '&')) {
                    const lead = cell.match(/^(\s*\\(hline|cline\s*\{[^}]*\}))*\s*/)[0];
                    let rest = cell.slice(lead.length);
                    const mc = rest.match(/^\\multicolumn\s*/);
                    if (mc) {
                        const [a2] = readArgs(rest, mc[0].length, 'aaa');
                        const n = parseInt(a2[0], 10);
                        // A spanning cell has its own template, without the columns' @{...} material.
                        cells.push({ lead, rest: a2[2], spanned: true });
                        for (let k = 1; k < n; k++) cells.push({ lead: '', rest: '', spanned: true });
                    } else {
                        cells.push({ lead, rest });
                    }
                }
                if (cells.length === 1 && !cells[0].rest.trim()) return row + sep;
                return (
                    cells
                        .map((c, ci) => {
                            if (c.spanned) return c.lead + c.rest;
                            return c.lead + (ci === 0 && before.trim() ? '{' + before + '}' : '') + c.rest + (after[ci] && after[ci].trim() ? '{' + after[ci] + '}' : '');
                        })
                        .join('&') + sep
                );
            })
            .join('');
        out += '\\begin{array}{' + cols + '}' + newBody + '\\end{array}';
        i = next;
    }
}

// Citable items other than rules (\citelabel and \citealso of defn.sty), by the prefix of their
// labels; the site gives each a page at <path>/<label without its prefix>, where for an entry of
// the basis the dots of its qualified name are slashes (/standard/basis/Platform/Cmd/none), so that
// no address ends in what looks like a file extension.
const ITEM_KINDS = {
    res: { name: 'restriction', path: '/standard/restrictions/' },
    df: { name: 'derived-form', path: '/standard/derived-forms/' },
    b: { name: 'basis', path: '/standard/basis/', url: (slug) => slug.replace(/\./g, '/') },
    fig: { name: 'figure', path: '/standard/figures/' },
};
const itemUrl = (label) => {
    const k = ITEM_KINDS[labelPrefix(label)];
    return k.path + (k.url ? k.url(labelSlug(label)) : labelSlug(label));
};
const labelPrefix = (label) => label.slice(0, label.indexOf(':'));
const labelSlug = (label) => label.slice(label.indexOf(':') + 1);
const isItemLabel = (label) => labelPrefix(label) in ITEM_KINDS;

// In mathematics, a name followed by \citelabel or \citealso links to its item's page, and a
// \citelabel also puts the item's anchor there (ids is false where the formula is shown again,
// on an item's page). Any other mark is dropped.
function citeMarks(tex, ids) {
    tex = tex.replace(/(\\kw\{(?:[^{}]|\{\})*\})((?:\s*\\cite(?:label|also)\{[^}]*\})+)/g, (_, name, tags) => {
        const marks = [...tags.matchAll(/\\cite(label|also)\{([^}]*)\}/g)];
        const first = marks[0][2].trim();
        if (!isItemLabel(first)) throw new Error('\\cite' + marks[0][1] + ' with an unknown prefix: ' + first);
        let out = '\\href{' + itemUrl(first) + '}{' + name + '}';
        if (ids) for (const m of marks) if (m[1] === 'label') out = '\\htmlId{' + anchorOf(m[2].trim()) + '}{' + out + '}';
        return out;
    });
    return tex.replace(/\\cite(?:label|also)\{[^}]*\}/g, '');
}

function prepareMath(tex) {
    tex = tex.replace(/\\(ref|ruleref|eqref)\{([^}]*)\}/g, (_, cmd, label) => {
        const t = KNOWN_LABELS.get(label.trim());
        const text = t ? t.text : '??';
        return cmd === 'ref' ? text : '(' + text + ')';
    });
    return fixArrays(tex);
}

// Renders TeX; returns the tree, or a raw node and a recorded problem when KaTeX refuses it.
function math(tex, display, where, ids = true) {
    tex = citeMarks(tex, ids);
    const key = (display ? 'D' : 'I') + tex;
    if (katexCache.has(key)) {
        const hit = katexCache.get(key);
        if (hit.error) problems.katex.push({ where, tex, message: hit.error });
        return hit.tree;
    }
    let result;
    let error = null;
    try {
        const html = katex.renderToString(prepareMath(tex), {
            displayMode: display,
            macros: { ...KATEX_MACROS },
            throwOnError: true,
            strict: false,
            output: 'htmlAndMathml',
            // Only the links and anchors of citeMarks.
            trust: (c) => c.command === '\\href' || c.command === '\\htmlId',
        });
        const tree = htmlTree(html);
        // The text content must survive the round trip through the tree.
        const plain = decodeEntities(html.replace(/<[^>]*>/g, ''));
        if (textOf(tree) !== plain) throw new Error('KaTeX markup did not survive parsing');
        result = tree;
    } catch (e) {
        error = e.message.split('\n')[0];
        problems.katex.push({ where, tex, message: error });
        result = null;
    }
    katexCache.set(key, { tree: result, error });
    return result;
}

const mathInline = (tex, where) => {
    const m = math(tex, false, where);
    return m ? { t: 'm', m } : { t: 'raw', tex: '$' + tex + '$' };
};

// ---------------------------------------------------------------------------------------------
// Parsing: a source becomes a list of nodes, arguments kept as raw strings
// ---------------------------------------------------------------------------------------------

// How many arguments each text command takes: 'o' an optional one, 'a' a mandatory one.
const ARGS = {
    chapter: 'a', 'chapter*': 'a', section: 'a', 'section*': 'a', subsection: 'a', 'subsection*': 'a',
    subsubsection: 'a', 'subsubsection*': 'a', paragraph: 'a',
    label: 'a', ref: 'a', ruleref: 'a', eqref: 'a', caption: 'oa',
    emph: 'a', textit: 'a', textbf: 'a', texttt: 'a', textrm: 'a', textnormal: 'a', textsf: 'a', textsc: 'a',
    kw: 'a', textsuperscript: 'a', mbox: 'a', text: 'a',
    defnrule: 'oaa', rulegroup: 'aa', rcomment: 'a', item: 'o', citelabel: 'a', citealso: 'a',
    setlength: 'aa', addcontentsline: 'aaa', vspace: 'a', 'vspace*': 'a', hspace: 'a', 'hspace*': 'a',
    noalign: 'a', multicolumn: 'aaa', cline: 'a', renewcommand: 'aa', phantom: 'a', include: 'a', input: 'a',
};

// Environments whose body is kept raw, with how many arguments follow \begin{name}.
const ENV_ARGS = { tabular: 'a', minipage: 'oa', figure: 'o', array: 'a', verbatim: '' };

function readArgs(s, i, spec) {
    const out = [];
    for (const k of spec) {
        if (k === 'o') {
            const o = optional(s, i);
            out.push(o ? o[0] : null);
            if (o) i = o[1];
        } else {
            const [a, j] = arg(s, i);
            out.push(a);
            i = j;
        }
    }
    return [out, i];
}

function parse(s) {
    const nodes = [];
    let text = '';
    const flush = () => { if (text) { nodes.push({ k: 'text', v: text }); text = ''; } };
    let i = 0;
    while (i < s.length) {
        const c = s[i];
        if (c === '\n' && isParBreak(s, i)) {
            flush();
            nodes.push({ k: 'par' });
            i = i + 1;
            while (/\s/.test(s[i] || '')) i++;
            continue;
        }
        if (c === '$') {
            flush();
            if (s[i + 1] === '$') {
                const j = s.indexOf('$$', i + 2);
                nodes.push({ k: 'math', display: true, tex: s.slice(i + 2, j) });
                i = j + 2;
            } else {
                const j = dollarEnd(s, i + 1);
                nodes.push({ k: 'math', display: false, tex: s.slice(i + 1, j) });
                i = j + 1;
            }
            continue;
        }
        if (c === '{') {
            flush();
            const [g, j] = group(s, i);
            nodes.push({ k: 'group', v: g });
            i = j;
            continue;
        }
        if (c === '\\') {
            const [name, after] = commandName(s, i);
            if (name === '[' || name === '(') {
                flush();
                const close = name === '[' ? '\\]' : '\\)';
                const j = s.indexOf(close, after);
                nodes.push({ k: 'math', display: name === '[', tex: s.slice(after, j) });
                i = j + 2;
                continue;
            }
            if (name === 'begin') {
                flush();
                const [envName, j] = group(s, skipSpace(s, after));
                const spec = ENV_ARGS[envName] || '';
                const [args, k] = readArgs(s, j, spec);
                let bodyEnd, next;
                try { [bodyEnd, next] = envEnd(s, envName, k); } catch (e) { throw new Error(e.message + " for the \\begin{" + envName + "} in: " + JSON.stringify(s.slice(Math.max(0, i - 200), i + 200))); }
                nodes.push({ k: 'env', name: envName, args, body: s.slice(k, bodyEnd) });
                i = next;
                continue;
            }
            if (!isLetter(name[0])) {
                // \\, \,, \ , \&, \%, \$, \#, \_, \{, \}, \', \~ and the like.
                flush();
                if (name === '\\') {
                    const o = optional(s, after);
                    nodes.push({ k: 'cmd', name, args: [] });
                    i = o ? o[1] : after;
                } else {
                    nodes.push({ k: 'cmd', name, args: [] });
                    i = after;
                }
                continue;
            }
            flush();
            const bare = name.replace(/\*$/, '');
            let spec = ARGS[name];
            if (spec === undefined && NOTATION_ARITY.has(bare)) spec = 'a'.repeat(NOTATION_ARITY.get(bare));
            if (spec === undefined) spec = '';
            const [args, j] = readArgs(s, after, spec);
            nodes.push({ k: 'cmd', name, args, raw: s.slice(i, j) });
            i = spec === '' ? skipControlWordSpace(s, j) : j;
            continue;
        }
        text += c;
        i++;
    }
    flush();
    return nodes;
}

// A blank line (a paragraph break) starts at s[i] === '\n'.
function isParBreak(s, i) {
    const re = /\n[ \t]*\n/y;
    re.lastIndex = i;
    return re.test(s);
}

// TeX skips spaces (and one newline) after a control word.
function skipControlWordSpace(s, i) {
    let j = i;
    while (s[j] === ' ' || s[j] === '\t') j++;
    if (s[j] === '\n' && !isParBreak(s, j)) {
        j++;
        while (s[j] === ' ' || s[j] === '\t') j++;
    }
    return j;
}

// ---------------------------------------------------------------------------------------------
// Converting: nodes become the blocks and inlines the site renders
// ---------------------------------------------------------------------------------------------

function typography(t) {
    return t
        .replace(/\s+/g, ' ')
        .replace(/---/g, '\u2014')
        .replace(/--/g, '\u2013')
        .replace(/``/g, '\u201c')
        .replace(/''/g, '\u201d')
        .replace(/`/g, '\u2018')
        .replace(/'/g, '\u2019')
        .replace(/~/g, '\u00a0');
}

const CHAR_CMDS = {
    '&': '&', '%': '%', '$': '$', '#': '#', '_': '_', '{': '{', '}': '}', ' ': ' ', ',': '\u2009',
    ';': '\u2005', ':': '\u2005', '!': '', '/': '', '-': '', '@': '',
    ldots: '\u2026', dots: '\u2026', textbackslash: '\\', textasciicircum: '^', textasciitilde: '~',
    textquotesingle: "'", ss: '\u00df', kwlb: '{', kwrb: '}', S: '\u00a7', dag: '\u2020', ddag: '\u2021',
    textless: '<', textgreater: '>', textbar: '|', textendash: '\u2013', textemdash: '\u2014',
    LaTeX: 'LaTeX', TeX: 'TeX', quad: '\u2003', qquad: '\u2003\u2003', copyright: '\u00a9',
};

// Commands with no output in this rendering of the book.
const IGNORED = new Set([
    'noindent', 'indent', 'centering', 'raggedright', 'raggedleft', 'arraybackslash', 'small', 'footnotesize',
    'scriptsize', 'normalsize', 'large', 'Large', 'smallskip', 'medskip', 'bigskip', 'hline', 'setlength',
    'phantomsection', 'addcontentsline', 'allowbreak', 'vspace', 'vspace*', 'hspace', 'hspace*', 'maketitle',
    'nopagebreak', 'newpage', 'clearpage', 'cleardoublepage', 'pagebreak', 'linebreak', 'frontmatter',
    'mainmatter', 'backmatter', 'appendix', 'hfill', 'vfill', 'noalign', 'relax', 'protect', 'leavevmode',
    'strut', 'break', 'tableofcontents', 'sloppy', 'normalfont', 'par', 'cline', 'renewcommand',
]);

// Text of a \kw{...}: code, with the book's escapes for braces and specials undone.
function codeText(s) {
    let out = '';
    for (const n of parse(s)) {
        if (n.k === 'text') out += n.v.replace(/~/g, '\u00a0');
        else if (n.k === 'group') out += codeText(n.v);
        else if (n.k === 'cmd' && n.name in CHAR_CMDS) out += CHAR_CMDS[n.name];
        else if (n.k === 'cmd' && IGNORED.has(n.name)) { /* no output */ }
        else if (n.k === 'cmd' && n.name === '\\') out += '\n';
        else if (n.k === 'math') out += n.tex;
        else if (n.k === 'cmd' && (n.name === 'texttt' || n.name === 'textnormal' || n.name === 'kw')) out += codeText(n.args[0]);
        else { noteUnknown(n.name || n.k, 'in \\kw'); out += n.raw || ''; }
    }
    return out;
}

// A \kw{...} as inlines: code, with any formula or notation macro inside it as mathematics.
function codeInlines(s, ctx) {
    const out = [];
    let code = '';
    const flush = () => { if (code) out.push({ t: 'code', v: code }); code = ''; };
    for (const n of parse(s)) {
        if (n.k === 'math') { flush(); out.push(mathInline(n.tex, ctx.chapter)); }
        else if (n.k === 'cmd' && NOTATION_ARITY.has(n.name.replace(/\*$/, '')) && !(n.name in CHAR_CMDS)) { flush(); out.push(mathInline(n.raw, ctx.chapter)); }
        else if (n.k === 'group') { flush(); out.push(...codeInlines(n.v, ctx)); }
        else if (n.k === 'text') code += codeText(n.v);
        else if (n.k === 'cmd') code += codeText(n.raw !== undefined ? n.raw : '\\' + n.name);
        else if (n.k === 'par') code += ' ';
        else { noteUnknown(n.k + ' in \\kw', ctx.chapter); code += unparse([n]); }
    }
    flush();
    return out;
}

class Ctx {
    constructor(chapter) {
        this.chapter = chapter;
    }
}

function inlines(nodes, ctx) {
    const out = [];
    const push = (x) => {
        if (typeof x === 'string') {
            if (!x) return;
            const last = out[out.length - 1];
            if (typeof last === 'string') out[out.length - 1] = last + x;
            else out.push(x);
        } else {
            out.push(x);
        }
    };
    for (const n of nodes) {
        switch (n.k) {
            case 'text':
                push(typography(n.v));
                break;
            case 'par':
                push(' ');
                break;
            case 'group':
                for (const x of inlines(parse(n.v), ctx)) push(x);
                break;
            case 'math':
                push(mathInline(n.tex, ctx.chapter));
                break;
            case 'env':
                // An environment inside running text (a tabular in a cell, say) is kept raw.
                noteUnknown('begin{' + n.name + '} (inline)', ctx.chapter);
                push({ t: 'raw', tex: '\\begin{' + n.name + '}' + n.body + '\\end{' + n.name + '}' });
                break;
            case 'cmd': {
                const name = n.name;
                if (name in CHAR_CMDS) push(CHAR_CMDS[name]);
                else if (name === '\\' || name === 'newline') push({ t: 'br' });
                else if (IGNORED.has(name)) { /* nothing */ }
                else if (name === 'emph' || name === 'textit') push({ t: 'em', c: inlines(parse(n.args[0]), ctx) });
                else if (name === 'textbf') push({ t: 'strong', c: inlines(parse(n.args[0]), ctx) });
                else if (name === 'kw' || name === 'texttt') for (const x of codeInlines(n.args[0], ctx)) push(x);
                else if (['textrm', 'textnormal', 'mbox', 'text', 'textsf', 'textsc'].includes(name)) for (const x of inlines(parse(n.args[0]), ctx)) push(x);
                else if (name === 'textsuperscript') push({ t: 'sup', c: inlines(parse(n.args[0]), ctx) });
                else if (name === 'fgderived') push({ t: 'sup', c: ['\u2020'] });
                else if (name === 'ref') push({ t: 'ref', label: n.args[0].trim(), paren: false });
                else if (name === 'ruleref' || name === 'eqref') push({ t: 'ref', label: n.args[0].trim(), paren: true });
                else if (name === 'label') {
                    // A label in running text: \ref gives the number of the section it is in.
                    const label = n.args[0].trim();
                    const id = anchorOf(label);
                    const here = ctx.section && ctx.section.number ? ctx.section.number : ctx.chapterRecord.number || '';
                    ctx.book.labels.set(label, { kind: 'sec', chapter: ctx.chapter, anchor: id, text: here });
                    push({ t: 'anchor', id });
                }
                else if (name === 'phantom') { /* invisible */ }
                else if (NOTATION_ARITY.has(name.replace(/\*$/, ''))) push(mathInline(n.raw, ctx.chapter));
                else {
                    noteUnknown(name, ctx.chapter);
                    push({ t: 'raw', tex: n.raw || '\\' + name });
                }
                break;
            }
            default:
                throw new Error('unexpected node ' + n.k);
        }
    }
    // Trim the ends.
    if (typeof out[0] === 'string') out[0] = out[0].replace(/^\s+/, '');
    const l = out.length - 1;
    if (typeof out[l] === 'string') out[l] = out[l].replace(/\s+$/, '');
    return out.filter((x) => x !== '');
}

const anchorOf = (label) => label.replace(/[^A-Za-z0-9_-]+/g, '-');

const blank = (xs) => xs.every((x) => typeof x === 'string' && !x.trim());

// Splits s at top-level occurrences of a separator (& or \\), outside braces, $..$ and environments.
function splitTop(s, sep) {
    const parts = [];
    const seps = [];
    parts.seps = seps;
    let depth = 0;
    let envDepth = 0;
    let inMath = false;
    let start = 0;
    for (let i = 0; i < s.length; i++) {
        const c = s[i];
        if (c === '\\') {
            if (s.startsWith('\\begin{', i)) envDepth++;
            else if (s.startsWith('\\end{', i)) envDepth--;
            else if (sep === '\\\\' && s[i + 1] === '\\' && depth === 0 && envDepth === 0 && !inMath) {
                parts.push(s.slice(start, i));
                const at = i;
                i += 2;
                const o = optional(s, i);
                if (o) i = o[1];
                seps.push(s.slice(at, i));
                start = i;
                i--;
                continue;
            }
            i++;
            continue;
        }
        if (c === '{') depth++;
        else if (c === '}') depth--;
        else if (c === '$') inMath = !inMath;
        else if (c === '&' && sep === '&' && depth === 0 && envDepth === 0 && !inMath) {
            parts.push(s.slice(start, i));
            start = i + 1;
        }
    }
    parts.push(s.slice(start));
    return parts;
}

// A tabular column specification: one entry per column, with its alignment and whether its cells
// are mathematics (>{$}..<{$}).
function columns(spec) {
    const cols = [];
    let pre = '';
    let i = 0;
    while (i < spec.length) {
        const c = spec[i];
        if (/\s|\|/.test(c)) { i++; continue; }
        if (c === '@' || c === '!' || c === '<') { i = group(spec, i + 1)[1]; continue; }
        if (c === '>') { const [g, j] = group(spec, i + 1); pre += g; i = j; continue; }
        if (c === '*') {
            const [n, j] = group(spec, i + 1);
            const [inner, k] = group(spec, j);
            spec = spec.slice(0, i) + inner.repeat(parseInt(n, 10)) + spec.slice(k);
            continue;
        }
        if ('lcr'.includes(c)) {
            cols.push({ align: { l: 'left', c: 'center', r: 'right' }[c], math: pre.includes('$'), wrap: false });
            pre = '';
            i++;
            continue;
        }
        if ('pmb'.includes(c)) {
            const [, j] = group(spec, i + 1);
            cols.push({ align: 'left', math: pre.includes('$'), wrap: true });
            pre = '';
            i = j;
            continue;
        }
        throw new Error('unknown column type ' + c + ' in ' + spec);
    }
    return cols;
}

// The rows of a display formula's arrays that belong to entries of the basis: those marked with
// \citelabel or \citealso, and those defining APPLY of a basic value. Each row, with the rows that
// continue it (their first cell empty) and the array's header, is kept as a formula of its own for
// the entry's page.
function harvest(tex, ctx) {
    if (!/\\cite(label|also)\{|\\APPLY\(\\kw\{/.test(tex)) return;
    const book = ctx.book;
    const role = (label, mark) => (mark === 'apply' ? 'apply' : ctx.chapter === 'appendix-dynamic-basis' ? 'dynamic' : 'static');
    const record = (unit, marks) => {
        const m = math(unit, true, ctx.chapter, false);
        const seen = new Set();
        for (const [mark, label] of marks) {
            if (seen.has(label)) continue;
            seen.add(label);
            if (mark === 'label') book.defineItem(label, ctx, null);
            const item = book.items.get(label);
            if (!item) {
                if (mark !== 'apply') problems.refs.add(label + ' (\\citealso before its \\citelabel)');
                continue;
            }
            item.places.push({ role: role(label, mark), figure: ctx.figure, chapter: ctx.chapter, section: ctx.section ? { ...ctx.section } : null, blocks: [m ? { t: 'math', m } : { t: 'raw', tex: unit }] });
        }
    };
    const marksIn = (s) => [...s.matchAll(/\\cite(label|also)\{([^}]*)\}/g)].map((x) => [x[1], x[2].trim()]);
    let found = false;
    let i = 0;
    for (;;) {
        const b = tex.indexOf('\\begin{array}', i);
        if (b < 0) break;
        found = true;
        let j = b + '\\begin{array}'.length;
        const o = optional(tex, j);
        if (o) j = o[1];
        const [spec, k] = group(tex, skipSpace(tex, j));
        const [bodyEnd, next] = envEnd(tex, 'array', k);
        i = next;
        const bars = spec.includes('|');
        let header = null;
        let first = true;
        const units = [];
        let cur = null;
        for (let row of splitTop(tex.slice(k, bodyEnd), '\\\\')) {
            row = row.replace(/^(\s*\\(hline|cline\s*\{[^}]*\}))+/, '');
            if (!row.trim()) continue;
            if (/^\s*\\multicolumn/.test(row)) { cur = null; first = false; continue; }
            if (first && !/\\kw\{|\\APPLY/.test(row)) { header = row; first = false; continue; }
            first = false;
            if (cur && !splitTop(row, '&')[0].trim()) { cur.push(row); continue; }
            cur = [row];
            units.push(cur);
        }
        for (const rows of units) {
            const marks = marksIn(rows.join(' '));
            const apply = rows[0].match(/^\s*\\APPLY\(\\kw\{([^}]*)\}/);
            if (apply) marks.push(['apply', 'b:' + (apply[1].includes('.') ? apply[1] : 'Basics.' + apply[1])]);
            if (!marks.length) continue;
            const unit = '\\begin{array}{' + spec + '}' + (bars ? '\\hline ' : '') + (header ? header + '\\\\\\hline ' : '') + rows.join('\\\\') + (bars ? '\\\\\\hline' : '') + '\\end{array}';
            record(unit, marks);
        }
    }
    // A formula without an array is one unit.
    if (!found) record(tex, marksIn(tex));
}

// The texts in Elm of values of Basics (a verbatim block of the dynamic basis): one per entry.
function harvestElm(text, ctx) {
    for (const def of text.split(/\n\s*\n/)) {
        const m = def.trim().match(/^([a-z][A-Za-z0-9]*)\b/);
        const item = m && ctx.book.items.get('b:Basics.' + m[1]);
        if (item) item.places.push({ role: 'elm', figure: ctx.figure, chapter: ctx.chapter, section: ctx.section ? { ...ctx.section } : null, blocks: [{ t: 'pre', v: def.replace(/^\n+/, '').replace(/\s+$/, '') }] });
    }
}

// A leading \emph{...} of a run of nodes, without its final full stop: the name of a group of
// restrictions ("Records") or of one ("Irredundancy").
function leadEmph(nodes, ctx) {
    const first = nodes.find((x) => !(x.k === 'text' && !x.v.trim()));
    if (!first || first.k !== 'cmd' || first.name !== 'emph') return null;
    const c = inlines(parse(first.args[0]), ctx);
    const l = c.length - 1;
    if (typeof c[l] === 'string') c[l] = c[l].replace(/\.\s*$/, '');
    return c;
}

// The first sentence of some blocks, as inlines: a summary of a restriction for the lists.
function firstSentence(bs) {
    const p = bs.find((b) => b.t === 'p');
    if (!p) return [];
    const out = [];
    for (const x of p.c) {
        if (typeof x === 'string') {
            const m = x.match(/^[^]*?\.(?=\s|$)/);
            if (m) { out.push(m[0]); return out; }
        }
        out.push(x);
    }
    return out;
}

function table(spec, body, ctx) {
    const cols = columns(spec);
    const rows = [];
    let pendingRule = false;
    for (let rowSrc of splitTop(body, '\\\\')) {
        // A \citelabel in a row (a derived form) makes the row an item.
        let label = null;
        rowSrc = rowSrc.replace(/\\citelabel\s*\{([^}]*)\}/, (_, l) => { label = l.trim(); return ''; });
        // Leading \hline and \noalign{...} mark a rule above the row.
        for (;;) {
            const t = rowSrc.replace(/^\s+/, '');
            if (t.startsWith('\\hline')) { pendingRule = true; rowSrc = t.slice(6); continue; }
            if (t.startsWith('\\cline')) { pendingRule = true; rowSrc = t.slice(group(t, t.indexOf('{'))[1]); continue; }
            if (t.startsWith('\\noalign')) { rowSrc = t.slice(t.indexOf('}', t.indexOf('{')) + 1); continue; }
            break;
        }
        if (!rowSrc.trim()) continue;
        const cells = splitTop(rowSrc, '&').map((cellSrc, ci) => {
            let span = 1;
            let src = cellSrc;
            const mc = cellSrc.trim().match(/^\\multicolumn/);
            if (mc) {
                const [a, j] = readArgs(cellSrc.trim(), '\\multicolumn'.length, 'aaa');
                span = parseInt(a[0], 10);
                src = a[2];
                void j;
            }
            const col = cols[ci] || { align: 'left', math: false };
            const trimmed = src.trim();
            if (!trimmed) return { c: [], span, align: col.align };
            if (col.math && !mc) return { c: [mathInline(trimmed, ctx.chapter)], span, align: col.align };
            return { c: inlines(parse(trimmed), ctx), span, align: col.align };
        });
        const row = { rule: pendingRule, cells };
        if (label) {
            const item = ctx.book.defineItem(label, ctx, ctx.tableLead ? ctx.tableLead() : null);
            row.item = item.ref;
            // On the item's page: the row under the table's header row.
            const head = rows[0] && !rows[0].item ? [{ rule: true, cells: rows[0].cells }] : [];
            item.summary = cells.map((c) => c.c);
            item.places.push({ role: 'statement', figure: ctx.figure, chapter: ctx.chapter, section: ctx.section ? { ...ctx.section } : null, blocks: [{ t: 'table', cols: cols.map((c) => ({ align: c.align, wrap: c.wrap })), rows: [...head, { rule: true, cells }], ruleBelow: true }] });
        }
        rows.push(row);
        pendingRule = false;
    }
    return { t: 'table', cols: cols.map((c) => ({ align: c.align, wrap: c.wrap })), rows, ruleBelow: pendingRule };
}

// Blocks of a source. The book state (numbering, the current figure) lives in ctx.
function blocks(src, ctx) {
    const out = [];
    let para = [];
    const flush = () => {
        const c = inlines(para, ctx);
        if (!blank(c)) {
            out.push({ t: 'p', c });
            ctx.lastPara = c;
            ctx.lastLead = leadEmph(para, ctx);
        }
        para = [];
    };
    // A \label attaches to the heading or figure it follows, when nothing but space comes between.
    let labellable = null;
    const nodes = parse(src);
    for (let idx = 0; idx < nodes.length; idx++) {
        const n = nodes[idx];
        if (n.k === 'text' && !n.v.trim()) { para.push(n); continue; }
        if (n.k === 'cmd' && n.name === 'label' && labellable) {
            labellable.label = n.args[0].trim();
            labellable.id = anchorOf(labellable.label);
            ctx.book.labels.set(labellable.label, labellable.target());
            labellable = null;
            continue;
        }
        const keepLabellable = n.k === 'cmd' && IGNORED.has(n.name);
        if (!keepLabellable) labellable = null;
        if (n.k === 'par') { flush(); continue; }
        if (n.k === 'math' && n.display) {
            flush();
            harvest(n.tex, ctx);
            const m = math(n.tex, true, ctx.chapter);
            out.push(m ? { t: 'math', m } : { t: 'raw', tex: '\\[' + n.tex + '\\]' });
            continue;
        }
        if (n.k === 'cmd' && /^(chapter|section|subsection|subsubsection)\*?$/.test(n.name)) {
            flush();
            ctx.lastLead = null;
            const h = ctx.book.heading(n.name, inlines(parse(n.args[0]), ctx), ctx);
            if (h.block) out.push(h.block);
            labellable = h;
            continue;
        }
        if (n.k === 'cmd' && n.name === 'defnrule') {
            flush();
            out.push(ctx.book.rule(n.args, ctx));
            continue;
        }
        if (n.k === 'cmd' && n.name === 'rulegroup') {
            flush();
            const judgement = math(n.args[1], false, ctx.chapter);
            const g = { t: 'rulegroup', title: inlines(parse(n.args[0]), ctx), judgement, tex: n.args[1].trim() };
            ctx.group = g;
            out.push(g);
            continue;
        }
        if (n.k === 'cmd' && n.name === 'caption' && ctx.figure) {
            ctx.figure.caption = inlines(parse(n.args[1]), ctx);
            ctx.figure.number = ++ctx.book.figureNo;
            const fig = ctx.figure;
            labellable = { target: () => ({ kind: 'fig', chapter: ctx.chapter, anchor: fig.id, text: String(fig.number) }) };
            Object.defineProperty(labellable, 'id', { set: (v) => { fig.id = v; } });
            // The label is kept off the figure's data: it is only for its item (Book.defineFigure).
            Object.defineProperty(labellable, 'label', { get: () => fig.label, set: (v) => { Object.defineProperty(fig, 'label', { value: v, enumerable: false }); } });
            continue;
        }
        if (n.k === 'env') {
            // A list that continues a paragraph takes its group from that paragraph's lead.
            const pending = para.every((x) => x.k === 'text' && !x.v.trim()) ? null : para;
            ctx.listLead = pending ? leadEmph(pending, ctx) : ctx.lastLead;
            // A table's group is the paragraph it continues, or else the one before it.
            ctx.tableLead = () => (pending ? inlines(pending, ctx) : ctx.lastPara);
            const b = envBlock(n, ctx);
            if (b === null) { para.push(n); continue; }
            flush();
            if (Array.isArray(b)) out.push(...b);
            else out.push(b);
            continue;
        }
        para.push(n);
    }
    flush();
    return out;
}

function envBlock(n, ctx) {
    switch (n.name) {
        case 'figure': {
            const outer = ctx.figure;
            const fig = { t: 'figure', id: null, number: null, caption: [], c: [] };
            ctx.figure = fig;
            fig.c = blocks(n.body, ctx);
            ctx.figure = outer;
            if (!fig.number) throw new Error('figure without a caption in ' + ctx.chapter);
            if (!fig.label || !fig.label.startsWith('fig:')) throw new Error('figure ' + fig.number + ' without a fig: label in ' + ctx.chapter);
            ctx.book.defineFigure(fig, ctx);
            return fig;
        }
        case 'center':
            return { t: 'div', cls: 'center', c: blocks(n.body, ctx) };
        case 'flushright':
            return { t: 'div', cls: 'right', c: blocks(n.body, ctx) };
        case 'minipage':
            return { t: 'div', cls: 'minipage', c: blocks(n.body, ctx) };
        case 'quote':
        case 'quotation':
            return { t: 'quote', c: blocks(n.body, ctx) };
        case 'itemize':
        case 'enumerate': {
            const group = ctx.listLead;
            const items = [];
            let cur = null;
            for (const x of parse(n.body)) {
                if (x.k === 'cmd' && x.name === 'item') {
                    cur = [];
                    items.push(cur);
                    if (x.args[0]) cur.push({ k: 'text', v: '' }, { k: 'group', v: '\\textbf{' + x.args[0] + '} ' });
                } else if (cur) {
                    cur.push(x);
                }
            }
            return {
                t: 'list',
                ordered: n.name === 'enumerate',
                items: items.map((xs) => {
                    // An item that starts with \citelabel is a citable item (a restriction).
                    const at = xs.findIndex((x) => !(x.k === 'text' && !x.v.trim()));
                    if (at < 0 || xs[at].k !== 'cmd' || xs[at].name !== 'citelabel') return { c: blocks(unparse(xs), ctx) };
                    const rest = xs.slice(at + 1);
                    const item = ctx.book.defineItem(xs[at].args[0].trim(), ctx, group);
                    item.title = leadEmph(rest, ctx);
                    const c = blocks(unparse(rest), ctx);
                    item.summary = [firstSentence(c)];
                    item.places.push({ role: 'statement', figure: ctx.figure, chapter: ctx.chapter, section: ctx.section ? { ...ctx.section } : null, blocks: c });
                    return { c, item: item.ref };
                }),
            };
        }
        case 'tabular':
            return table(n.args[0], n.body, ctx);
        case 'verbatim':
            if (ctx.chapter === 'appendix-dynamic-basis' && ctx.figure) harvestElm(n.body, ctx);
            return { t: 'pre', v: n.body.replace(/^\n/, '').replace(/\s+$/, '') };
        case 'rulecomments': {
            const items = [];
            const parts = n.body.split(/\\rcomment\s*/);
            for (const part of parts.slice(1)) {
                const [label, j] = group(part, 0);
                items.push({ rule: label.trim(), c: blocks(part.slice(j), ctx) });
            }
            for (const it of items) ctx.book.comment(it.rule, it.c);
            return { t: 'comments', items };
        }
        case 'document':
            return blocks(n.body, ctx);
        default:
            return null;
    }
}

// Nodes back to source, to convert a slice of them as blocks.
function unparse(nodes) {
    return nodes
        .map((x) => {
            switch (x.k) {
                case 'text': return x.v;
                case 'par': return '\n\n';
                case 'group': return '{' + x.v + '}';
                case 'math': return x.display ? '\\[' + x.tex + '\\]' : '$' + x.tex + '$';
                case 'env': {
                    const spec = ENV_ARGS[x.name] || '';
                    const a = x.args.map((v, i) => (v === null ? '' : spec[i] === 'o' ? '[' + v + ']' : '{' + v + '}')).join('');
                    return '\\begin{' + x.name + '}' + a + x.body + '\\end{' + x.name + '}';
                }
                case 'cmd': {
                    // A space after a control word keeps it apart from a following letter, as TeX would.
                    const src = x.raw !== undefined ? x.raw : '\\' + x.name;
                    return /[A-Za-z]$/.test(src) ? src + ' ' : src;
                }
                default: throw new Error('unparse ' + x.k);
            }
        })
        .join('');
}

// ---------------------------------------------------------------------------------------------
// The book
// ---------------------------------------------------------------------------------------------

class Book {
    constructor() {
        this.labels = new Map();
        this.items = new Map();
        this.rules = [];
        this.ruleByLabel = new Map();
        this.figureNo = 0;
        this.ruleNo = 0;
        this.chapterNo = 0;
        this.appendixNo = 0;
        this.part = 'front';
        this.chapters = [];
    }

    heading(cmd, title, ctx) {
        const starred = cmd.endsWith('*');
        const level = cmd.replace(/\*$/, '');
        const ch = ctx.chapterRecord;
        if (level === 'chapter') {
            let number = null;
            if (!starred && this.part === 'main') number = String(++this.chapterNo);
            if (!starred && this.part === 'appendix') number = String.fromCharCode(65 + this.appendixNo++);
            ch.number = number;
            ch.title = title;
            ch.sec = 0;
            const rec = { block: null };
            rec.target = () => ({ kind: 'ch', chapter: ctx.chapter, anchor: '', text: number || '' });
            return rec;
        }
        let number = null;
        if (!starred) {
            if (level === 'section') { ch.sec++; ch.sub = 0; number = ch.number + '.' + ch.sec; }
            else if (level === 'subsection') { ch.sub++; ch.subsub = 0; number = ch.number + '.' + ch.sec + '.' + ch.sub; }
            else { ch.subsub = (ch.subsub || 0) + 1; number = ch.number + '.' + ch.sec + '.' + ch.sub + '.' + ch.subsub; }
        }
        const lvl = { section: 1, subsection: 2, subsubsection: 3 }[level];
        const id = 'h-' + ch.slug + '-' + (number || anchorOf(textOfInlines(title)).toLowerCase());
        const block = { t: 'h', level: lvl, number, id, c: title };
        ch.sections.push({ level: lvl, number, id, title });
        ctx.section = { number, id, title };
        const rec = { block };
        Object.defineProperty(rec, 'id', { set: (v) => { block.id = v; ch.sections[ch.sections.length - 1].id = v; ctx.section.id = v; } });
        rec.target = () => ({ kind: 'sec', chapter: ctx.chapter, anchor: block.id, text: number || '' });
        return rec;
    }

    rule(args, ctx) {
        const [labelRaw, premises, conclusion] = args;
        const number = ++this.ruleNo;
        if (!labelRaw) throw new Error('rule ' + number + ' has no label');
        const label = labelRaw.trim();
        const slug = label.replace(/^r:/, '');
        const tex = '\\frac{\\begin{array}{c}' + premises + '\\end{array}}{\\begin{array}{c}' + conclusion + '\\end{array}}';
        const m = math(tex, true, label);
        const block = { t: 'rule', slug, number, id: anchorOf(label), m };
        const record = {
            slug,
            label,
            number,
            chapter: ctx.chapter,
            section: ctx.section ? { ...ctx.section } : null,
            group: ctx.group ? { title: ctx.group.title, judgement: ctx.group.judgement } : null,
            m,
            tex: { premises: premises.trim(), conclusion: conclusion.trim() },
            comments: [],
            referencedFrom: [],
        };
        this.rules.push(record);
        this.ruleByLabel.set(label, record);
        this.labels.set(label, { kind: 'rule', chapter: ctx.chapter, anchor: block.id, text: String(number), rule: slug });
        return block;
    }

    comment(label, c) {
        const r = this.ruleByLabel.get(label);
        if (!r) { problems.refs.add(label + ' (comment for an unknown rule)'); return; }
        r.comments.push(c);
    }

    // A citable item other than a rule, at its \citelabel. Its places (the statement, or for an
    // entry of the basis its rows and texts) are added as they are found.
    defineItem(label, ctx, group) {
        if (!isItemLabel(label)) throw new Error('\\citelabel with an unknown prefix: ' + label);
        if (this.items.has(label)) throw new Error('label defined twice: ' + label);
        const kind = ITEM_KINDS[labelPrefix(label)].name;
        const slug = labelSlug(label);
        const anchor = anchorOf(label);
        const item = {
            label,
            kind,
            slug,
            anchor,
            chapter: ctx.chapter,
            section: ctx.section ? { ...ctx.section } : null,
            group: group || null,
            title: null,
            summary: [],
            places: [],
            referencedFrom: [],
            ref: { kind, slug, id: anchor },
        };
        this.items.set(label, item);
        const text = ctx.section && ctx.section.number ? ctx.section.number : ctx.chapterRecord.number || '';
        this.labels.set(label, { kind: labelPrefix(label), chapter: ctx.chapter, anchor, text, item: slug });
        return item;
    }

    // A figure, as an item with a page of its own: its title is its caption, and its one place is
    // the figure itself. Its label stays the figure's (a \ref to it is to its place in its chapter).
    defineFigure(fig, ctx) {
        const label = fig.label;
        if (this.items.has(label)) throw new Error('label defined twice: ' + label);
        const slug = labelSlug(label);
        const section = ctx.section ? { ...ctx.section } : null;
        this.items.set(label, {
            label,
            kind: 'figure',
            slug,
            anchor: fig.id,
            number: fig.number,
            chapter: ctx.chapter,
            section,
            group: null,
            title: fig.caption,
            summary: [fig.caption],
            places: [{ role: 'statement', figure: null, chapter: ctx.chapter, section, blocks: [fig] }],
            referencedFrom: [],
            ref: { kind: 'figure', slug, id: fig.id },
        });
    }
}

function textOfInlines(xs) {
    return xs
        .map((x) => {
            if (typeof x === 'string') return x;
            if (x.t === 'code') return x.v;
            if (x.c) return textOfInlines(x.c);
            return '';
        })
        .join('');
}

// Fills in every reference with where its label points, and records which places refer to each rule.
function resolve(book) {
    const walk = (x, place) => {
        if (Array.isArray(x)) { for (const y of x) walk(y, place); return; }
        if (!x || typeof x !== 'object') return;
        if (x.t === 'h') { place.section = { number: x.number, id: x.id, title: x.c }; }
        if (x.t === 'rule') { place.rule = x; }
        if (x.t === 'ref') {
            const target = book.labels.get(x.label);
            if (!target) {
                problems.refs.add(x.label);
                x.target = null;
                x.text = '??';
            } else {
                Object.assign(x, target, { text: x.paren ? '(' + target.text + ')' : target.text });
                const r = target.kind === 'rule' ? book.ruleByLabel.get(x.label) : book.items.get(x.label);
                if (r) {
                    const from = {
                        chapter: place.chapter,
                        section: place.section ? place.section.number : null,
                        sectionTitle: place.section ? place.section.title : null,
                        anchor: place.inComment ? 'r-' + place.inComment : place.section ? place.section.id : '',
                        comment: place.inComment || null,
                    };
                    const key = JSON.stringify(from);
                    if (!r.referencedFrom.some((f) => JSON.stringify(f) === key) && from.comment !== r.slug) r.referencedFrom.push(from);
                }
            }
            delete x.label;
            delete x.paren;
            return;
        }
        if (x.t === 'comments') {
            for (const it of x.items) {
                walk(it.c, { ...place, inComment: it.rule.replace(/^r:/, '') });
                it.number = book.ruleByLabel.get(it.rule) ? book.ruleByLabel.get(it.rule).number : null;
                it.rule = it.rule.replace(/^r:/, '');
            }
            return;
        }
        if (x.t === 'm' || x.t === 'math') return;
        for (const k of Object.keys(x)) if (k !== 'm' && k !== 'judgement') walk(x[k], place);
    };
    for (const ch of book.chapters) walk(ch.blocks, { chapter: ch.slug, section: null });
    // Rule records share their comment blocks with the chapters, so they are resolved now too.
}

// ---------------------------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------------------------

function writeJson(file, value) {
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, JSON.stringify(value) + '\n');
}

function master() {
    const src = stripComments(fs.readFileSync(path.join(TEX, MASTER), 'utf8'));
    const titleArg = arg(src, src.indexOf('\\title') + '\\title'.length)[0];
    const [mainTitle, rest] = titleArg.split(/\\\\(?:\[[^\]]*\])?/);
    const edition = (rest || '').replace(/\\large/g, '').replace(/[()]/g, '').trim();
    const author = arg(src, src.indexOf('\\author') + '\\author'.length)[0].trim();
    const order = [];
    for (const m of src.matchAll(/\\(frontmatter|mainmatter|appendix|backmatter)\b|\\include\{([^}]+)\}/g)) {
        order.push(m[2] ? { file: m[2] } : { part: m[1] });
    }
    return { title: mainTitle.trim(), edition, author, order };
}

function checkAux(book, dir) {
    const expected = new Map();
    for (const f of fs.readdirSync(dir).filter((f) => f.endsWith('.aux'))) {
        for (const m of fs.readFileSync(path.join(dir, f), 'utf8').matchAll(/\\newlabel\{([^}]+)\}\{\{\{?([^{}]*)\}?\}/g)) {
            expected.set(m[1], m[2]);
        }
    }
    let bad = 0;
    for (const [label, target] of book.labels) {
        if (!expected.has(label)) { console.error('  not in the .aux files: ' + label); bad++; continue; }
        // A citable item has a page of its own; its \ref number (that of the enclosing section or
        // list item) is not used, so only its presence is compared.
        if (isItemLabel(label)) continue;
        if (expected.get(label) !== target.text) {
            console.error(`  ${label}: here ${target.text}, LaTeX ${expected.get(label)}`);
            bad++;
        }
    }
    for (const label of expected.keys()) if (/^(r|fig|sec|ch|res|df|b):/.test(label) && !book.labels.has(label)) { console.error('  missing here: ' + label); bad++; }
    console.log(bad ? `--check-aux: ${bad} difference(s)` : `--check-aux: all ${book.labels.size} labels agree with LaTeX`);
    return bad === 0;
}

function main() {
    const opts = parseArgs(process.argv.slice(2).filter((a) => a !== '--'));
    const m = master();
    // The first pass numbers everything; the second has every label for the formulas that refer to one.
    KNOWN_LABELS = convert(m).labels;
    problems.unknown.clear();
    problems.katex.length = 0;
    problems.refs.clear();
    for (const k of [...katexCache.keys()]) if (/\\(ref|ruleref|eqref)\{/.test(k)) katexCache.delete(k);
    const book = convert(m);
    output(opts, m, book);
}

function convert(m) {
    const book = new Book();

    for (const item of m.order) {
        if (item.part) {
            book.part = item.part === 'mainmatter' ? 'main' : item.part === 'appendix' ? 'appendix' : item.part === 'frontmatter' ? 'front' : 'back';
            continue;
        }
        let src = stripComments(fs.readFileSync(path.join(TEX, item.file + '.tex'), 'utf8'));
        // Commands and environments the chapter defines for itself, and the layout ones of defn.sty.
        const own = definitions(src);
        for (const d of [...own.cmds.values(), ...own.envs.values()].sort((a, b) => b.start - a.start)) {
            src = src.slice(0, d.start) + src.slice(d.stop);
        }
        const cmds = new Map([...EXPAND_CMDS.map((n) => [n, defnDefs.cmds.get(n)]), ...own.cmds]);
        const envs = new Map([...EXPAND_ENVS.map((n) => [n, defnDefs.envs.get(n)]), ...own.envs]);
        src = expand(src, cmds, envs);

        const labelMatch = src.match(/\\chapter\*?\{[^]*?\}\s*\\label\{ch:([^}]+)\}/);
        const slug = labelMatch ? labelMatch[1] : item.file;
        const record = { slug, file: item.file, part: book.part, number: null, title: [], sections: [], blocks: [] };
        book.chapters.push(record);
        const ctx = new Ctx(slug);
        ctx.book = book;
        ctx.chapterRecord = record;
        ctx.figure = null;
        ctx.group = null;
        ctx.section = null;
        const firstRule = book.ruleNo + 1;
        record.blocks = blocks(src, ctx);
        record.rules = book.ruleNo >= firstRule ? [firstRule, book.ruleNo] : null;
    }

    resolve(book);
    return book;
}

function output(opts, m, book) {
    const ok = opts.checkAux ? checkAux(book, opts.checkAux) : true;

    // Output.
    if (fs.existsSync(opts.out)) {
        if (path.basename(opts.out) !== 'data-standard') throw new Error('refusing to clear ' + opts.out);
        fs.rmSync(opts.out, { recursive: true, force: true });
    }
    const pdf = fs.readdirSync(DEF).find((f) => f.endsWith('.pdf')) || null;
    if (pdf) {
        const dl = path.join(ROOT, 'site', 'public', 'downloads');
        fs.mkdirSync(dl, { recursive: true });
        fs.copyFileSync(path.join(DEF, pdf), path.join(dl, pdf));
    }
    const chapterSummary = (ch) => ({ slug: ch.slug, number: ch.number, title: ch.title, part: ch.part });
    writeJson(path.join(opts.out, 'index.json'), {
        title: m.title,
        edition: m.edition,
        author: m.author,
        pdf: pdf ? 'downloads/' + pdf : null,
        chapters: book.chapters.map((ch) => ({
            ...chapterSummary(ch),
            rules: ch.rules,
            sections: ch.sections.map((s) => ({ level: s.level, number: s.number, id: s.id, title: s.title })),
        })),
        rules: book.rules.map((r) => ({ slug: r.slug, number: r.number, chapter: r.chapter, group: r.group ? r.group.title : [] })),
        items: [...book.items.values()].map((it) => ({
            kind: it.kind,
            slug: it.slug,
            number: it.number || null,
            chapter: it.chapter,
            section: it.section ? it.section.number : null,
            group: it.group,
            title: it.title,
            summary: it.summary,
        })),
    });
    book.chapters.forEach((ch, i) => {
        writeJson(path.join(opts.out, 'chapters', ch.slug + '.json'), {
            ...chapterSummary(ch),
            blocks: ch.blocks,
            prev: i > 0 ? chapterSummary(book.chapters[i - 1]) : null,
            next: i + 1 < book.chapters.length ? chapterSummary(book.chapters[i + 1]) : null,
        });
    });
    const chapterOf = new Map(book.chapters.map((ch) => [ch.slug, chapterSummary(ch)]));
    book.rules.forEach((r, i) => {
        writeJson(path.join(opts.out, 'rules', r.slug + '.json'), {
            slug: r.slug,
            number: r.number,
            chapter: chapterOf.get(r.chapter),
            section: r.section,
            group: r.group,
            m: r.m,
            tex: r.tex,
            comments: r.comments,
            referencedFrom: r.referencedFrom.map((f) => ({ ...f, chapter: chapterOf.get(f.chapter) })),
            prev: i > 0 ? { slug: book.rules[i - 1].slug, number: book.rules[i - 1].number } : null,
            next: i + 1 < book.rules.length ? { slug: book.rules[i + 1].slug, number: book.rules[i + 1].number } : null,
        });
    });

    const items = [...book.items.values()];
    const counts = {};
    for (const kind of Object.values(ITEM_KINDS).map((k) => k.name)) {
        const ofKind = items.filter((it) => it.kind === kind);
        counts[kind] = ofKind.length;
        const link = (it) => (it ? { slug: it.slug, title: it.title } : null);
        ofKind.forEach((it, i) => {
            if (!it.places.length) problems.refs.add(it.label + ' (an item with nothing to show)');
            writeJson(path.join(opts.out, 'items', kind, it.slug + '.json'), {
                kind,
                slug: it.slug,
                number: it.number || null,
                title: it.title,
                group: it.group,
                chapter: chapterOf.get(it.chapter),
                section: it.section,
                anchor: it.anchor,
                places: it.places.map((p) => ({
                    role: p.role,
                    chapter: chapterOf.get(p.chapter),
                    section: p.section,
                    figure: p.figure ? { number: p.figure.number, id: p.figure.id || '', caption: p.figure.caption } : null,
                    blocks: p.blocks,
                })),
                referencedFrom: it.referencedFrom.map((f) => ({ ...f, chapter: chapterOf.get(f.chapter) })),
                prev: link(ofKind[i - 1]),
                next: link(ofKind[i + 1]),
            });
        });
    }

    // The Lean proofs of the mechanisation (definition/mechanisation/), linked to the rules they name.
    const mechProblems = writeMechanisation(opts.out, new Set(book.rules.map((r) => r.slug)), writeJson);

    // Report.
    console.log(`${m.title} (${m.edition}): ${book.chapters.length} chapters, ${book.rules.length} rules, ${book.figureNo} figures, ${katexCache.size} formulas -> ${path.relative(ROOT, opts.out)}`);
    console.log(`  ${counts.restriction} restrictions, ${counts['derived-form']} derived forms, ${counts.basis} entries of the basis, ${counts.figure} figures`);
    let failed = !ok;
    if (mechProblems.length) {
        failed = true;
        console.error('Problems in the Lean mechanisation:');
        for (const pr of mechProblems) console.error('  ' + pr);
    }
    if (problems.katex.length) {
        failed = true;
        console.error(`${problems.katex.length} formula(s) KaTeX could not render:`);
        for (const p of problems.katex) console.error(`  [${p.where}] ${p.message}\n      ${p.tex.slice(0, 160)}`);
    }
    if (problems.refs.size) {
        failed = true;
        console.error(`${problems.refs.size} reference(s) to missing labels: ${[...problems.refs].join(', ')}`);
    }
    if (problems.unknown.size) {
        failed = true;
        console.error(`${problems.unknown.size} command(s) not understood, kept as raw TeX:`);
        for (const [k, v] of [...problems.unknown].sort((a, b) => b[1].count - a[1].count)) console.error(`  ${k} x${v.count} (first in ${v.where})`);
    }
    process.exitCode = failed ? 1 : 0;
}

main();
