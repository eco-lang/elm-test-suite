// directives.js — reading a test's directives (the `-- CHECK:` family, `-- EXIT:`, `-- STDIN:`,
// `-- ENV:` and the rest, described in README.md) and checking a program's output against them.
'use strict';

const fs = require('fs');
const path = require('path');

// --- CHECK patterns (README.md, "Writing a test") ------------------------------------------

const CHECK = '-- CHECK:';
const CHECK_NOT = '-- CHECK-NOT:';
const variant = (word) => '-- CHECK-' + word + ':';

function extractCheckPatterns(content) {
    const same = variant('SAME'), next = variant('NEXT'), dag = variant('DAG'), label = variant('LABEL');
    const patterns = [];
    let lastPositive = -1;
    const grab = (line, pos, len) => line.slice(pos + len).replace(/^[ \t]+/, '').replace(/[ \t\r\n]+$/, '');
    const positive = (p) => { patterns.push({ pattern: p, negated: false, continuations: [] }); lastPositive = patterns.length - 1; };
    for (const line of content.split('\n')) {
        let pos, p;
        if ((pos = line.indexOf(CHECK_NOT)) >= 0) {
            p = grab(line, pos, CHECK_NOT.length);
            if (p) { patterns.push({ pattern: p, negated: true, continuations: [] }); lastPositive = -1; }
        } else if ((pos = line.indexOf(same)) >= 0 || (pos = line.indexOf(next)) >= 0) {
            const kind = line.indexOf(same) >= 0 ? 'same' : 'next';
            p = grab(line, pos, (kind === 'same' ? same : next).length);
            if (!p) continue;
            if (lastPositive >= 0) patterns[lastPositive].continuations.push({ kind, pattern: p });
            else positive(p);
        } else if ((pos = line.indexOf(dag)) >= 0) {
            p = grab(line, pos, dag.length);
            if (p) positive(p);
        } else if ((pos = line.indexOf(label)) >= 0) {
            p = grab(line, pos, label.length);
            if (p) positive(p);
        } else if ((pos = line.indexOf(CHECK)) >= 0) {
            p = grab(line, pos, CHECK.length);
            if (p) positive(p);
        } else if ((pos = line.indexOf('-- CHECK-')) >= 0) {
            const base = pos + '-- CHECK'.length;
            const colon = line.indexOf(':', base);
            const ws = line.slice(base).search(/[ \t]/);
            const wordEnd = ws < 0 ? -1 : base + ws;
            if (colon >= 0 && (wordEnd < 0 || colon < wordEnd)) {
                const word = line.slice(base + 1, colon);
                if (!word.startsWith('MLIR')) {
                    throw new Error('unsupported CHECK variant in test file: ' + line.slice(pos, colon + 1) +
                        ' (supported: CHECK, CHECK-NOT, CHECK-DAG, CHECK-SAME, CHECK-NEXT, CHECK-LABEL)');
                }
            }
        }
    }
    return patterns;
}

function patternRegex(pattern) {
    if (pattern.indexOf('{{') < 0) return null;
    let re = '';
    let pos = 0;
    const lit = (s) => s.replace(/[.^$|?*+()[\]{}\\]/g, '\\$&');
    while (pos < pattern.length) {
        const open = pattern.indexOf('{{', pos);
        if (open < 0) { re += lit(pattern.slice(pos)); break; }
        re += lit(pattern.slice(pos, open));
        const close = pattern.indexOf('}}', open + 2);
        if (close < 0) { re += lit(pattern.slice(open)); break; }
        re += pattern.slice(open + 2, close);
        pos = close + 2;
    }
    try { return new RegExp(re); } catch (e) { return null; }
}

// [begin, end) of the first match of `pattern` in text at or after `from`, or null.
function findPattern(text, from, pattern) {
    if (from > text.length) return null;
    const re = patternRegex(pattern);
    if (!re) {
        const p = text.indexOf(pattern, from);
        return p < 0 ? null : [p, p + pattern.length];
    }
    const m = re.exec(text.slice(from));
    return m ? [from + m.index, from + m.index + m[0].length] : null;
}

function groupMatches(lines, cp) {
    for (let i = 0; i < lines.length; i++) {
        let searchFrom = 0;
        for (;;) {
            const base = findPattern(lines[i], searchFrom, cp.pattern);
            if (!base) break;
            let curLine = i, curPos = base[1], ok = true;
            for (const c of cp.continuations) {
                if (c.kind === 'same') {
                    const m = findPattern(lines[curLine], curPos, c.pattern);
                    if (!m) { ok = false; break; }
                    curPos = m[1];
                } else {
                    curLine++;
                    if (curLine >= lines.length) { ok = false; break; }
                    const m = findPattern(lines[curLine], 0, c.pattern);
                    if (!m) { ok = false; break; }
                    curPos = m[1];
                }
            }
            if (ok) return true;
            searchFrom = base[0] + 1;
        }
    }
    return false;
}

function verifyPatterns(output, patterns) {
    const lines = output.split('\n').map((l) => l.replace(/\r$/, ''));
    if (lines.length && lines[lines.length - 1] === '' && output.endsWith('\n')) lines.pop();
    for (const cp of patterns) {
        if (cp.negated) {
            if (findPattern(output, 0, cp.pattern)) return 'Unexpected pattern (CHECK-NOT): ' + cp.pattern;
        } else if (!cp.continuations.length) {
            if (!findPattern(output, 0, cp.pattern)) return 'Missing pattern: ' + cp.pattern;
        } else if (!groupMatches(lines, cp)) {
            return 'Missing pattern: ' + cp.pattern + ' (with ' + cp.continuations.length +
                ' CHECK-SAME/CHECK-NEXT continuation(s))';
        }
    }
    return '';
}

// --- Process directives ---------------------------------------------------------------------

function directiveLines(content, marker) {
    return content.split('\n').filter((l) => l.startsWith(marker)).map((l) => l.slice(marker.length).replace(/\r$/, ''));
}

function extractExit(content) {
    const lines = directiveLines(content, '-- EXIT:');
    if (!lines.length) return 0;
    const t = lines[0].trim();
    if (!/^[+-]?\d+$/.test(t)) throw new Error("malformed EXIT directive: '" + lines[0] + "'");
    return parseInt(t, 10);
}

function extractStdin(content) {
    const lines = directiveLines(content, '-- STDIN:');
    if (!lines.length) return null;
    let out = '';
    for (const rest of lines) {
        const text = rest.startsWith(' ') ? rest.slice(1) : rest;
        for (let i = 0; i < text.length; i++) {
            if (text[i] === '\\' && i + 1 < text.length) {
                const n = text[i + 1];
                if (n === 'n') { out += '\n'; i++; continue; }
                if (n === 't') { out += '\t'; i++; continue; }
                if (n === '\\') { out += '\\'; i++; continue; }
            }
            out += text[i];
        }
    }
    return out;
}

// `-- ENV:` / `-- UNSETENV:` / `-- RLIMIT-FSIZE:` / `-- STDIN-DELAY-MS:` (README.md).
function extractEnv(content) {
    return directiveLines(content, '-- ENV:').map((rest) => {
        const t = rest.trim();
        const eq = t.indexOf('=');
        const name = eq < 0 ? t : t.slice(0, eq);
        if (eq < 0 || !name || /[ \t$]/.test(name)) {
            throw new Error("malformed ENV directive (want NAME=VALUE): '" + rest + "'");
        }
        return [name, t.slice(eq + 1)];
    });
}

function extractUnsetenv(content) {
    const out = [];
    for (const rest of directiveLines(content, '-- UNSETENV:')) {
        const names = rest.trim().split(/\s+/).filter(Boolean);
        if (!names.length) throw new Error('empty UNSETENV directive');
        if (names.some((n) => /[=$]/.test(n))) throw new Error("malformed UNSETENV directive: '" + rest + "'");
        out.push(...names);
    }
    return out;
}

function extractCount(content, marker) {
    const lines = directiveLines(content, marker);
    if (!lines.length) return null;
    const t = lines[0].trim();
    if (!/^\d{1,18}$/.test(t)) throw new Error('malformed ' + marker + " directive: '" + lines[0] + "'");
    return Number(t);
}

function expandVars(value, lookup) {
    let out = '';
    for (let i = 0; i < value.length; i++) {
        if (value[i] !== '$') { out += value[i]; continue; }
        if (value[i + 1] === '$') { out += '$'; i++; continue; }
        if (value[i + 1] === '{') {
            const close = value.indexOf('}', i + 2);
            if (close < 0) throw new Error("unterminated ${ in ENV value '" + value + "'");
            const name = value.slice(i + 2, close);
            const v = lookup(name);
            if (v === undefined) throw new Error("ENV value '" + value + "': ${" + name + '} is not known to this harness');
            out += v;
            i = close;
            continue;
        }
        out += '$';
    }
    return out;
}

// The child's environment: `base` with the test's ENV lines (expanded against `base`) set and
// its UNSETENV names removed.
function childEnv(t, base) {
    const env = Object.assign({}, base);
    for (const [name, value] of t.env) {
        if (t.unset.includes(name)) throw new Error('ENV and UNSETENV both name ' + name);
        env[name] = expandVars(value, (n) => base[n]);
    }
    for (const name of t.unset) delete env[name];
    return env;
}

let prlimitPath;
function findPrlimit() {
    if (prlimitPath !== undefined) return prlimitPath;
    prlimitPath = null;
    for (const dir of (process.env.PATH || '').split(path.delimiter).concat(['/usr/bin', '/bin'])) {
        if (!dir) continue;
        const p = path.join(dir, 'prlimit');
        try { fs.accessSync(p, fs.constants.X_OK); prlimitPath = p; break; } catch (e) { /* next */ }
    }
    return prlimitPath;
}

function extractSkip(content) {
    const linux = directiveLines(content, '-- LINUX-ONLY:');
    if (linux.length && process.platform !== 'linux') {
        return 'LINUX-ONLY: ' + (linux[0].trim() || '(no reason given)');
    }
    return null;
}

// A test's `-- TAGS: a, b` labels (README.md, "Tags"), in the order written: one or more lines, each a
// comma-separated list of lower-case names (letters, digits, `.` and `-`). The runner adds the
// test's project in front; naming a project here is an error, as is a malformed name.
function extractTags(content, projects = []) {
    const tags = [];
    for (const rest of directiveLines(content, '-- TAGS:')) {
        const names = rest.split(',').map((s) => s.trim());
        if (names.some((n) => !/^[a-z0-9][a-z0-9.-]*$/.test(n))) throw new Error("malformed TAGS directive: '" + rest + "'");
        for (const n of names) {
            if (projects.includes(n)) throw new Error('TAGS names the project ' + n + ': a test is tagged with its own project already');
            if (!tags.includes(n)) tags.push(n);
        }
    }
    return tags;
}

// Why a test's result is never taken from the result cache (run.js), or null: its outcome may
// differ between two runs of the same program, so each run must be a real one.
//   `-- NO-CACHE: <why>`        any test, for a reason the harness cannot see
//   `-- STDIN-DELAY-MS:`        its input arrives after a delay
//   Time.now, Time.every, Process.sleep, Random.generate in its source, qualified or exposed by
//   its import: it depends on the clock or on a seed taken from it
const TIMING = /\b(Time\.now|Time\.every|Process\.sleep|Random\.generate)\b/;
const TIMING_IMPORT = /^import\s+(Time|Process|Random)\b[^\n]*\bexposing\s*\(([^)]*)\)/gm;
const TIMING_NAMES = { Time: ['now', 'every'], Process: ['sleep'], Random: ['generate'] };
function uncacheable(content) {
    const no = directiveLines(content, '-- NO-CACHE:');
    if (no.length) return 'NO-CACHE: ' + (no[0].trim() || '(no reason given)');
    if (directiveLines(content, '-- STDIN-DELAY-MS:').length) return 'STDIN-DELAY-MS';
    const m = TIMING.exec(content);
    if (m) return 'uses ' + m[1];
    for (const im of content.matchAll(TIMING_IMPORT)) {
        const exposed = im[2].split(',').map((x) => x.trim());
        const hit = TIMING_NAMES[im[1]].find((n) => exposed.includes(n) || exposed.includes('..'));
        if (hit) return 'uses ' + im[1] + '.' + hit;
    }
    return null;
}

// --- Files ---------------------------------------------------------------------------------------

function writeIfChanged(file, content) {
    try {
        if (fs.readFileSync(file).equals(Buffer.from(content))) return false;
    } catch (e) { /* missing */ }
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, content);
    return true;
}

function mtimeMs(file) {
    try { return fs.statSync(file).mtimeMs; } catch (e) { return -1; }
}

module.exports = {
    extractCheckPatterns, verifyPatterns, directiveLines, extractExit, extractStdin, extractEnv,
    extractUnsetenv, extractCount, childEnv, findPrlimit, extractSkip, extractTags, uncacheable, writeIfChanged, mtimeMs,
};
