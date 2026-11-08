#!/usr/bin/env node
// run.js — runs the test projects under tests/ with one Elm compiler.
//
// Usage:
//   node runner/run.js [--compiler <name>] [--project <name>[,<name>...]]
//        [--filter <substr>[,<substr>...]] [--jobs <n>] [--compile-jobs <n>] [--timeout <seconds>]
//        [--compile-timeout <seconds>] [--compile-memory <MB>]
//        [--json <file>] [--no-cache] [--refresh] [--list-compilers]
//   node runner/run.js --compiler <name> --project <name> --record <TestName>
//
// --compiler names an entry of compilers.json (default: its "default"). Each entry gives:
//   command      the compiler: a path relative to this project (node_modules/...), an absolute
//                path, or a name looked up on PATH
//   args         the arguments before the source file (default ["make"])
//   target       "js": the compiler writes JavaScript (`--output=<Name>.js`), which runs on node;
//                "native": it writes an executable (`--output=<Name>`), which runs directly
//   env          extra environment variables for the compiler (optional)
//   elmVersion   the "elm-version" written into each project's elm.json (an application must
//                name the compiler's exact version); default: the compiler's `--version` when
//                that is an Elm version (0.19.x), else elm.json is left as it is
//   description  free text, shown in reports
// The compiler runs with its own ELM_HOME, .work/<compiler>/elm-home, so compilers never share a
// package cache.
//
// For every tests/<project>/src/*.elm that has a top-level `main` or a `-- COMPILE-ERROR:` line, and
// no `-- HELPER:` line:
//   1. The project is mirrored into one directory per compile worker, .work/<compiler>/<project>/
//      project-<k> (a compiler is not safe to run twice at once in one project). A compiler
//      that crashes can leave elm-stuff corrupt, so elm-stuff is cleared after a compile that
//      crashed or was killed, and a compile that hangs, is killed or reports a corrupt cache is
//      tried once more with an empty elm-stuff.
//   2. The test is compiled (debug mode: the tests use Debug.log) to .work/<compiler>/<project>/out/.
//      A test is recompiled when its output is older than the test, a helper module, elm.json,
//      this runner, compilers.json or the compiler. A COMPILE-ERROR test is always compiled and
//      passes iff the compiler rejects it and its CHECK lines match the compiler's output.
//   3. The program runs in its own process. On the js target that is `node <Name>.run.js`, a
//      launcher that installs a minimal `document` (runner/dom.js, so that `main = Html.text ...`
//      starts), calls Elm.<Name>.init({ node, flags }) with the `-- FLAGS:` JSON, and echoes each
//      value sent out through a port `echoOut` back in through a port `echoIn`. On the native
//      target the executable runs, and tests that need a JavaScript host (`-- FLAGS:`, or a port
//      module) are skipped. stdin is the `-- STDIN:` text (else /dev/null), the environment has the
//      `-- ENV:` lines, and the test passes iff the program exits on its own within the timeout
//      (default 60 s) with the `-- EXIT:` status (default 0) and its stdout+stderr satisfy the
//      CHECK lines.
//   `-- LINUX-ONLY:` skips the test on other hosts; with `-- NO-SKIP:` a skip is a failure instead.
//   `-- MODE-GUARD:` makes a Char equality whose debug-mode answer differs from --optimize's throw
//   (patchModeGuard). `-- UNICODE: <version>` names the Unicode version the expectations were
//   recorded with; under a node with another, the runner warns.
//   `-- TAGS: a, b` labels the test; its project is always its first tag.
// The result cache: a test's result is kept in .work/result-cache/<compiler>/<key>.json, the key a
// hash of everything the result depends on (the compiler's executable, this runner, Node, the
// project's elm.json, the test's source and the modules it imports, ...), and a later run takes it
// from there instead of compiling and running the test again. A result that may be an accident of
// the moment (a compile that crashed, timed out or ran out of memory, a program that timed out or
// was killed) is kept only once two runs in a row have given it: the first is a pending entry,
// never used. Every result of a test that directives.uncacheable names (`-- NO-CACHE:`,
// `-- STDIN-DELAY-MS:`, the clock) is never kept. A missing or unreadable entry is a miss. --no-cache neither reads
// nor writes it; --refresh runs every test, rewrites the entries and reports each result that
// differs from the one it replaces. A run of every test of a compiler removes that compiler's
// entries it did not use. See plans/test-result-cache.md.
// --record <TestName> runs one test without checking it and prints each non-empty output line as
// `-- CHECK: <line>`. Each test's output is kept in .work/<compiler>/<project>/out/<Name>.log.
// --json writes every test's outcome, its failure message, its tags and up to 4000 characters of its
// output (the program's, or the compiler's for a COMPILE-ERROR test) to a file (run-all.js and
// runner/site-data.js read it). The exit status is 1 if any test failed, 2 on a usage or setup
// error, else 0.
'use strict';

const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawn, spawnSync } = require('child_process');
const D = require('./directives');

const ROOT = path.resolve(__dirname, '..');

// --- Arguments ---------------------------------------------------------------------------------

function parseArgs(argv) {
    const opts = {
        compiler: null,
        filters: [],
        jobs: 8,
        compileJobs: Math.max(1, Math.min(8, os.cpus().length)),
        timeoutSec: 60,
        compileTimeoutSec: 60,
        compileMemoryMB: 4096,
        projects: [],
        record: null,
        json: null,
        listCompilers: false,
        noCache: false,
        refresh: false,
    };
    for (let i = 0; i < argv.length; i++) {
        const a = argv[i];
        const next = () => {
            if (i + 1 >= argv.length) throw new Error('missing value after ' + a);
            return argv[++i];
        };
        const eq = a.indexOf('=');
        const key = eq > 0 && a.startsWith('--') ? a.slice(0, eq) : a;
        const val = eq > 0 && a.startsWith('--') ? () => a.slice(eq + 1) : next;
        const list = () => val().split(',').map((s) => s.trim()).filter(Boolean);
        switch (key) {
            case '--compiler': case '-c': opts.compiler = val(); break;
            case '--filter': case '-f': opts.filters.push(...list()); break;
            case '--project': case '-p': opts.projects.push(...list()); break;
            case '--jobs': case '-j': opts.jobs = Math.max(1, parseInt(val(), 10) || 1); break;
            case '--compile-jobs': opts.compileJobs = Math.max(1, parseInt(val(), 10) || 1); break;
            case '--timeout': opts.timeoutSec = Math.max(1, parseInt(val(), 10) || 60); break;
            case '--compile-timeout': opts.compileTimeoutSec = Math.max(1, parseInt(val(), 10) || 60); break;
            case '--compile-memory': opts.compileMemoryMB = Math.max(64, parseInt(val(), 10) || 4096); break;
            case '--record': opts.record = val(); break;
            case '--json': opts.json = path.resolve(val()); break;
            case '--list-compilers': opts.listCompilers = true; break;
            case '--no-cache': opts.noCache = true; break;
            case '--refresh': opts.refresh = true; break;
            case '--help': case '-h':
                console.log(fs.readFileSync(__filename, 'utf8').split('\n').slice(1, 60)
                    .map((l) => l.replace(/^\/\/ ?/, '')).join('\n'));
                process.exit(0);
                break;
            default:
                throw new Error('unknown argument: ' + a);
        }
    }
    return opts;
}

// --- Compilers ---------------------------------------------------------------------------------

function loadCompilers() {
    const file = path.join(ROOT, 'compilers.json');
    const cfg = JSON.parse(fs.readFileSync(file, 'utf8'));
    if (!cfg.compilers || typeof cfg.compilers !== 'object') throw new Error(file + ': no "compilers" object');
    return cfg;
}

// The compiler entry `name`, with its command resolved to an executable.
function resolveCompiler(cfg, name) {
    const entry = cfg.compilers[name];
    if (!entry) {
        throw new Error('unknown compiler ' + name + ' (known: ' + Object.keys(cfg.compilers).join(', ') + ')');
    }
    const c = Object.assign({ args: ['make'], target: 'js', env: {} }, entry, { name });
    if (!['js', 'native'].includes(c.target)) throw new Error(name + ': target must be "js" or "native"');
    if (c.command.includes('/') || c.command.includes(path.sep)) {
        c.command = path.resolve(ROOT, c.command);
        if (!fs.existsSync(c.command)) {
            throw new Error(name + ': ' + c.command + ' not found' +
                (c.command.includes('node_modules') ? ' (run `pnpm install`)' : ''));
        }
    }
    const v = spawnSync(c.command, ['--version'], { encoding: 'utf8', env: Object.assign({}, process.env, c.env) });
    if (v.error) throw new Error(name + ': cannot run ' + c.command + ': ' + v.error.message);
    c.version = ((v.stdout || '') + (v.stderr || '')).trim().split('\n')[0] || '?';
    if (!c.elmVersion && /^0\.19\.\d+$/.test(c.version)) c.elmVersion = c.version;
    return c;
}

// --- Child processes ---------------------------------------------------------------------------

// The resident memory, in MB, of a process and its descendants, from /proc (Linux); null where
// /proc is not available.
function treeRssMB(pid) {
    try {
        let kb = 0;
        const visit = (p) => {
            const m = /VmRSS:\s+(\d+)/.exec(fs.readFileSync('/proc/' + p + '/status', 'utf8'));
            if (m) kb += parseInt(m[1], 10);
            for (const t of fs.readdirSync('/proc/' + p + '/task')) {
                const kids = fs.readFileSync('/proc/' + p + '/task/' + t + '/children', 'utf8').trim();
                if (kids) kids.split(/\s+/).forEach(visit);
            }
        };
        visit(pid);
        return kb / 1024;
    } catch (e) {
        return null;
    }
}

// The command line that runs argv without leaving a core dump: a compiler that crashes, or a test
// that runs out of memory on purpose, would otherwise write hundreds of MB into .work on every run.
// `exec` keeps the pid, so killing the child and measuring its memory still reach the command.
function noCoreDumps(argv) {
    return process.platform === 'win32' ? argv : ['/bin/sh', '-c', 'ulimit -c 0 && exec "$@"', 'sh', ...argv];
}

// With limits.timeoutSec, the child is killed after that many seconds and the result has timedOut
// set. With limits.memoryMB, it is killed once it (with its descendants) holds more memory than that,
// checked every 250 ms, and the result has outOfMemory set: a compiler that loops while allocating
// would otherwise take the machine's memory before the timeout.
function run(cmd, args, options, limits = {}) {
    return new Promise((resolve) => {
        const argv = noCoreDumps([cmd, ...args]);
        const child = spawn(argv[0], argv.slice(1), Object.assign({ stdio: ['ignore', 'pipe', 'pipe'] }, options));
        let timedOut = false, outOfMemory = false;
        const timer = limits.timeoutSec
            ? setTimeout(() => { timedOut = true; child.kill('SIGKILL'); }, limits.timeoutSec * 1000) : null;
        const poll = limits.memoryMB ? setInterval(() => {
            const mb = treeRssMB(child.pid);
            if (mb === null || mb <= limits.memoryMB) return;
            outOfMemory = true;
            child.kill('SIGKILL');
        }, 250) : null;
        const chunks = [];
        child.stdout.on('data', (d) => chunks.push(d));
        child.stderr.on('data', (d) => chunks.push(d));
        child.on('error', (e) => chunks.push(Buffer.from(String(e))));
        child.on('close', (code, signal) => {
            if (timer) clearTimeout(timer);
            if (poll) clearInterval(poll);
            resolve({ code, signal, timedOut, outOfMemory, output: Buffer.concat(chunks).toString('utf8') });
        });
    });
}

async function pool(items, jobs, fn) {
    let next = 0;
    const worker = async () => {
        while (next < items.length) {
            const i = next++;
            await fn(items[i], i);
        }
    };
    await Promise.all(Array.from({ length: Math.min(jobs, items.length) }, worker));
}

// The launcher of a js-target test: a minimal DOM for static Html programs, the program with its
// `-- FLAGS:` JSON, and the port echo.
const domShim = path.join(__dirname, 'dom.js');
function launcher(name, flags) {
    return 'const node = require(' + JSON.stringify(domShim) + ').install();\n' +
        "const app = require('./" + name + ".js').Elm." + name + '.init({ node' +
        (flags === null ? '' : ', flags: ' + flags) + ' });\n' +
        'if (app && app.ports && app.ports.echoOut && app.ports.echoIn) {\n' +
        '    app.ports.echoOut.subscribe((v) => app.ports.echoIn.send(v));\n' +
        '}\n';
}

// --- Projects ----------------------------------------------------------------------------------

// The test projects: every directory of tests/ with an elm.json.
function projectSpecs() {
    const dir = path.join(ROOT, 'tests');
    return fs.readdirSync(dir).sort()
        .filter((n) => fs.existsSync(path.join(dir, n, 'elm.json')))
        .map((name) => ({ name, dir: path.join(dir, name) }));
}

// --- Mode guard --------------------------------------------------------------------------------

// The tests are compiled in debug mode (Debug.log is rejected under --optimize), where a Char is a
// `String` object and Elm's _Utils_eqHelp walks it with `for (var key in x)`, which makes `x == y` a
// prefix test. A test with `-- MODE-GUARD:` takes --optimize (string equality) as its reference, so
// in it a Char equality whose two answers differ is made to throw. A compiler whose output has no
// _Utils_eqHelp is left unpatched.
const GUARD_MARKER = '/* elm-test-suite mode guard */';
const EQ_DEF = 'function _Utils_eqHelp(x, y, depth, stack)';
const GUARD = GUARD_MARKER + '\n' +
    'function _Utils_eqHelp(x, y, depth, stack) {\n' +
    '\tvar r = _Utils_eqHelp_raw(x, y, depth, stack);\n' +
    '\tif (x instanceof String && y instanceof String && r !== (x.valueOf() === y.valueOf()))\n' +
    "\t\tthrow new Error('elm-test-suite: Char equality differs between debug and --optimize: '\n" +
    "\t\t\t+ JSON.stringify(x.valueOf()) + ' == ' + JSON.stringify(y.valueOf()));\n" +
    '\treturn r;\n' +
    '}\n';

function patchModeGuard(jsFile) {
    const src = fs.readFileSync(jsFile, 'utf8');
    const first = src.indexOf(EQ_DEF);
    if (src.includes(GUARD_MARKER) || first < 0 || src.indexOf(EQ_DEF, first + 1) >= 0) return;
    fs.writeFileSync(jsFile, src.slice(0, first) + GUARD +
        'function _Utils_eqHelp_raw(x, y, depth, stack)' + src.slice(first + EQ_DEF.length));
}

// --- Package sources -----------------------------------------------------------------------------

// Fills the compiler's package cache with the source of each dependency of `elmJsonData` that it
// lacks but another cache has: another compiler's under .work, or the user's ELM_HOME (~/.elm).
// A package version's source is the same for every compiler; only its build artifacts
// (artifacts.dat and the like) are compiler-specific, and those are not copied, so the compiler
// builds its own. This saves downloads, and gets the suite past a package that GitHub fails to serve.
function seedPackages(elmJsonData, compiler, elmHome) {
    if (!compiler.elmVersion) return;
    const deps = Object.assign({}, ...['direct', 'indirect'].map((k) => (elmJsonData.dependencies || {})[k] || {}));
    const caches = [];
    const work = path.join(ROOT, '.work');
    for (const other of fs.existsSync(work) ? fs.readdirSync(work) : []) {
        const home = path.join(work, other, 'elm-home');
        if (home !== elmHome && fs.existsSync(home)) caches.push(home);
    }
    caches.push(process.env.ELM_HOME || path.join(os.homedir(), '.elm'));
    for (const [pkg, version] of Object.entries(deps)) {
        const dest = path.join(elmHome, compiler.elmVersion, 'packages', ...pkg.split('/'), version);
        if (fs.existsSync(dest)) continue;
        for (const home of caches) {
            const versions = fs.existsSync(home) ? fs.readdirSync(home) : [];
            const src = versions.map((v) => path.join(home, v, 'packages', ...pkg.split('/'), version))
                .find((d) => fs.existsSync(path.join(d, 'elm.json')) && fs.existsSync(path.join(d, 'src')));
            if (!src) continue;
            fs.mkdirSync(dest, { recursive: true });
            for (const f of fs.readdirSync(src)) {
                if (f.startsWith('artifacts')) continue;
                fs.cpSync(path.join(src, f), path.join(dest, f), { recursive: true });
            }
            break;
        }
    }
}

// --- Result cache --------------------------------------------------------------------------------

const crypto = require('crypto');
const CACHE_FORMAT = 1;
const sha256 = (data) => crypto.createHash('sha256').update(data).digest('hex');

// The executable a command runs: its path, or the first match on PATH; null if not found.
function executable(command) {
    if (command.includes('/') || command.includes(path.sep)) return fs.existsSync(command) ? command : null;
    for (const dir of (process.env.PATH || '').split(path.delimiter)) {
        if (!dir) continue;
        const p = path.join(dir, command);
        try { fs.accessSync(p, fs.constants.X_OK); return p; } catch (e) { /* next */ }
    }
    return null;
}

// The cache of one run of this runner for one compiler: what every key of it shares (the compiler,
// the judge, the environment, the limits), and the entries used, written and found to differ.
function openCache(opts, compiler) {
    const enabled = !opts.noCache && !opts.record;
    const exe = executable(compiler.command);
    const judge = ['run.js', 'directives.js', 'dom.js'].map((f) => [f, sha256(fs.readFileSync(path.join(__dirname, f)))]);
    const common = {
        format: CACHE_FORMAT,
        compiler: {
            name: compiler.name, target: compiler.target, args: compiler.args, env: compiler.env,
            elmVersion: compiler.elmVersion || null, version: compiler.version,
            executable: exe ? sha256(fs.readFileSync(exe)) : compiler.command,
        },
        judge,
        environment: {
            node: process.version, platform: process.platform, arch: process.arch,
            image: [process.env.ImageOS || null, process.env.ImageVersion || null],
        },
        limits: { run: opts.timeoutSec, compile: opts.compileTimeoutSec, memory: opts.compileMemoryMB },
    };
    return {
        enabled,
        refresh: opts.refresh,
        dir: path.join(ROOT, '.work', 'result-cache', compiler.name),
        common,
        used: new Set(),
        hits: 0,
        written: 0,
        pending: 0,
        mismatches: [],
    };
}

// The module names a source imports.
function importsOf(content) {
    return [...content.matchAll(/^import\s+([A-Z][A-Za-z0-9_.]*)/gm)].map((m) => m[1]);
}

// A test's key: the cache's shared inputs, the project, and the source of the test and of every
// module of the project it imports, directly or not.
function cacheKey(cache, project, modules, name) {
    const closure = new Set();
    const visit = (m) => {
        if (closure.has(m) || !modules.has(m)) return;
        closure.add(m);
        importsOf(modules.get(m)).forEach(visit);
    };
    visit(name);
    const sources = [...closure].sort().map((m) => [m, sha256(modules.get(m))]);
    return { key: sha256(JSON.stringify({ ...cache.common, project, test: name, sources })), closure };
}

// The entry under `key`, or null: one that is missing, unreadable, of another format or for
// another key is a miss.
function readEntry(cache, key) {
    try {
        const e = JSON.parse(fs.readFileSync(path.join(cache.dir, key + '.json'), 'utf8'));
        if (e && e.format === CACHE_FORMAT && e.key === key && e.result && typeof e.result.status === 'string') return e;
    } catch (e) { /* a miss */ }
    return null;
}

// Writes an entry whole or not at all: to a temporary file, then renamed over the entry. A pending
// entry records a result seen once that is used only when the next run gives it again.
function writeEntry(cache, key, project, test, result, pending) {
    fs.mkdirSync(cache.dir, { recursive: true });
    const file = path.join(cache.dir, key + '.json');
    const tmp = file + '.' + process.pid + '-' + crypto.randomBytes(4).toString('hex') + '.tmp';
    const entry = { format: CACHE_FORMAT, key, project, test, ranAt: new Date().toISOString(), pending,
        result: { status: result.status, message: result.message || '', output: result.output || '',
            ms: result.ms, compileError: result.compileError } };
    fs.writeFileSync(tmp, JSON.stringify(entry));
    fs.renameSync(tmp, file);
    cache.used.add(key);
    cache.written++;
    if (pending) cache.pending++;
}

// After a run of every test: removes the compiler's entries this run did not use, and any
// temporary file an interrupted run left.
function pruneCache(cache) {
    if (!fs.existsSync(cache.dir)) return 0;
    let removed = 0;
    for (const f of fs.readdirSync(cache.dir)) {
        const key = f.endsWith('.json') ? f.slice(0, -5) : null;
        if (key !== null && cache.used.has(key)) continue;
        fs.rmSync(path.join(cache.dir, f), { force: true });
        removed++;
    }
    return removed;
}

// --- One project -------------------------------------------------------------------------------

async function runProject(spec, opts, compiler, cache, projectNames) {
    const work = path.join(ROOT, '.work', compiler.name, spec.name);
    const projects = Array.from({ length: opts.compileJobs }, (_, k) => path.join(work, 'project-' + k));
    const outDir = path.join(work, 'out');
    const srcDir = path.join(spec.dir, 'src');
    fs.mkdirSync(outDir, { recursive: true });

    // 1. Mirror the project; discover the tests.
    // An application's elm.json names the exact compiler version it needs: write the compiler's.
    const elmJsonData = JSON.parse(fs.readFileSync(path.join(spec.dir, 'elm.json'), 'utf8'));
    if (compiler.elmVersion) elmJsonData['elm-version'] = compiler.elmVersion;
    const elmJson = JSON.stringify(elmJsonData, null, 4) + '\n';
    const sources = fs.readdirSync(srcDir).filter((f) => f.endsWith('.elm')).sort();
    const tests = [];
    for (const f of sources) {
        const content = fs.readFileSync(path.join(srcDir, f), 'utf8');
        // A module with `-- HELPER:` is never a test, even with a top-level `main` (one that tests
        // what a `main` outside the main module is).
        if ((/^main\b/m.test(content) || /^-- COMPILE-ERROR:/m.test(content)) && !/^-- HELPER:/m.test(content)) {
            tests.push({ name: f.slice(0, -4), content });
        }
    }
    for (const p of projects) {
        D.writeIfChanged(path.join(p, 'elm.json'), elmJson);
        for (const f of sources) D.writeIfChanged(path.join(p, 'src', f), fs.readFileSync(path.join(srcDir, f)));
        for (const f of fs.readdirSync(path.join(p, 'src'))) {
            if (f.endsWith('.elm') && !sources.includes(f)) fs.unlinkSync(path.join(p, 'src', f));
        }
    }

    const selected = opts.record
        ? tests.filter((t) => t.name === opts.record)
        : tests.filter((t) => !opts.filters.length || opts.filters.some((f) => (spec.name + '/' + t.name).includes(f)));
    if (opts.record && !selected.length) throw new Error('--record: no test ' + opts.record + ' in ' + spec.name);
    if (!selected.length) return { passed: 0, failed: 0, skipped: 0, failures: [], results: {} };
    console.log(compiler.name + ' / ' + spec.name + ': ' + selected.length + ' of ' + tests.length + ' tests' +
        (opts.filters.length ? ' (filter: ' + opts.filters.join(',') + ')' : ''));

    const results = new Map();   // name -> { status: 'pass'|'fail'|'skip', message }
    const toRun = [];
    const otherUnicode = [];
    for (const t of selected) {
        let skip;
        t.tags = [spec.name];
        try {
            t.tags.push(...D.extractTags(t.content, projectNames));
            t.modeGuard = D.directiveLines(t.content, '-- MODE-GUARD:').length > 0;
            t.noSkip = D.directiveLines(t.content, '-- NO-SKIP:').length > 0;
            const unicode = D.directiveLines(t.content, '-- UNICODE:').map((l) => l.trim());
            if (unicode.length && unicode[0] !== process.versions.unicode) otherUnicode.push(t.name);
            skip = D.extractSkip(t.content);
            t.patterns = D.extractCheckPatterns(t.content);
            t.exit = D.extractExit(t.content);
            t.stdin = D.extractStdin(t.content);
            t.env = D.extractEnv(t.content);
            t.unset = D.extractUnsetenv(t.content);
            t.fsize = D.extractCount(t.content, '-- RLIMIT-FSIZE:');
            t.stdinDelay = D.extractCount(t.content, '-- STDIN-DELAY-MS:');
            const flags = D.directiveLines(t.content, '-- FLAGS:');
            t.flags = flags.length ? (JSON.parse(flags[0].trim()), flags[0].trim()) : null;
            t.compileError = D.directiveLines(t.content, '-- COMPILE-ERROR:').length > 0;
            if (t.compileError && !t.patterns.length) {
                throw new Error('a COMPILE-ERROR test needs a CHECK line (the report title)');
            }
            if (skip === null && compiler.target === 'native' && !t.compileError &&
                (t.flags !== null || /^port module\b/m.test(t.content))) {
                skip = 'needs a JavaScript host (flags or ports), which a native executable does not have';
            }
            if (skip === null && t.fsize !== null && !D.findPrlimit()) {
                skip = 'RLIMIT-FSIZE needs prlimit (util-linux), not found on this host';
            }
        } catch (e) {
            results.set(t.name, { status: 'fail', message: String(e.message || e) });
            continue;
        }
        if (skip !== null && t.noSkip) {
            results.set(t.name, { status: 'fail', message: skip + ': the test has NO-SKIP' });
        } else if (skip !== null) results.set(t.name, { status: 'skip', message: skip });
        else toRun.push(t);
    }
    if (otherUnicode.length) {
        console.log('  WARNING: ' + otherUnicode.join(', ') + ' recorded expectations under another Unicode version ' +
            'than this node (' + process.version + ', Unicode ' + process.versions.unicode + '), and may fail for that reason alone');
    }

    // The result cache: a test whose result is cached is neither compiled nor run.
    const modules = new Map(sources.map((f) => [f.slice(0, -4), fs.readFileSync(path.join(srcDir, f), 'utf8')]));
    const project = { name: spec.name, elmJson };
    const keys = new Map();   // test name -> its key, for a test whose result may be cached
    if (cache.enabled) {
        for (const t of toRun) {
            const { key, closure } = cacheKey(cache, project, modules, t.name);
            if ([...closure].some((m) => D.uncacheable(modules.get(m)) !== null)) continue;
            keys.set(t.name, key);
            if (cache.refresh) continue;
            const e = readEntry(cache, key);
            if (!e || e.pending) continue;
            cache.used.add(key);
            cache.hits++;
            results.set(t.name, Object.assign({}, e.result, { cached: e.ranAt }));
        }
        const fromCache = toRun.filter((t) => results.has(t.name)).length;
        if (fromCache) console.log('  ' + fromCache + ' from the cache');
        for (let i = toRun.length - 1; i >= 0; i--) if (results.has(toRun[i].name)) toRun.splice(i, 1);
    }

    // 2. Compile.
    const ext = compiler.target === 'js' ? '.js' : '';
    const outFile = (t) => path.join(outDir, t.name + ext);
    const shared = Math.max(
        D.mtimeMs(path.join(spec.dir, 'elm.json')), D.mtimeMs(__filename), D.mtimeMs(path.join(ROOT, 'compilers.json')),
        compiler.command.includes(path.sep) ? D.mtimeMs(compiler.command) : -1,
        ...sources.filter((f) => !tests.some((t) => t.name + '.elm' === f)).map((f) => D.mtimeMs(path.join(srcDir, f))));
    const stale = toRun.filter((t) => t.compileError ||
        D.mtimeMs(outFile(t)) < Math.max(shared, D.mtimeMs(path.join(srcDir, t.name + '.elm'))));
    console.log('  compiling ' + stale.length + ' (' + (toRun.length - stale.length) + ' up to date)');
    const elmHome = path.join(ROOT, '.work', compiler.name, 'elm-home');
    seedPackages(elmJsonData, compiler, elmHome);
    const env = Object.assign({}, process.env, compiler.env, { ELM_HOME: elmHome });
    const compileOne = async (t, k) => {
        const out = outFile(t);
        const compile = () => run(compiler.command, [...compiler.args, 'src/' + t.name + '.elm', '--output=' + out],
            { cwd: projects[k], env }, { timeoutSec: opts.compileTimeoutSec, memoryMB: opts.compileMemoryMB });
        // A compiler that crashes can leave elm-stuff half-written, and the next compile in it then
        // reports a CORRUPT CACHE (Elm 0.19.2, Lamdera) or hangs (Elm 0.19.3). So elm-stuff is cleared
        // after a compile that crashed or was killed, and a compile that hangs, is killed or finds a
        // corrupt cache is tried once more with an empty elm-stuff. So is one that trips over its own
        // lock on an elm-stuff file ("d.dat: withBinaryFile: resource busy (file is locked)"): a race
        // between the threads of one Elm 0.19.2 or 0.19.3 process, seen on GitHub's runners.
        const elmStuff = path.join(projects[k], 'elm-stuff');
        if (!elmStuff.startsWith(path.join(ROOT, '.work') + path.sep)) throw new Error('unexpected path ' + elmStuff);
        const killed = (r) => r.timedOut || r.outOfMemory || r.signal;
        const corruptCache = (r) => /^-- CORRUPT CACHE|Corrupt File:/m.test(r.output);
        const selfLocked = (r) => /resource busy \(file is locked\)/.test(r.output);
        const crashed = (r) => /bypassed the normal error reporting|CallStack \(from HasCallStack\)/.test(r.output);
        let r = await compile();
        if ((killed(r) || corruptCache(r) || selfLocked(r)) && fs.existsSync(elmStuff)) {
            fs.rmSync(elmStuff, { recursive: true, force: true });
            console.log('  retrying ' + t.name + ' with an empty elm-stuff');
            r = await compile();
        }
        if (killed(r) || corruptCache(r) || crashed(r)) fs.rmSync(elmStuff, { recursive: true, force: true });
        const produced = fs.existsSync(out);
        const died = r.outOfMemory ? 'compiler used more than ' + opts.compileMemoryMB + ' MB of memory'
            : r.timedOut ? 'compiler timed out after ' + opts.compileTimeoutSec + ' s'
            : r.signal ? 'compiler killed by ' + r.signal : null;
        if (died) {
            try { fs.unlinkSync(out); } catch (e) { /* none */ }
            results.set(t.name, { status: 'fail', message: died + '\n' + r.output.slice(0, 4000), compileError: t.compileError,
                volatile: true });
        } else if (t.compileError) {
            try { fs.unlinkSync(out); } catch (e) { /* none */ }
            let message = r.code === 0 || produced ? 'compiled, but a compile error was expected'
                : D.verifyPatterns(r.output, t.patterns);
            if (message) message += '\n--- compiler output ---\n' + r.output.slice(0, 4000);
            results.set(t.name, { status: message ? 'fail' : 'pass', message, compileError: true,
                output: r.output.slice(0, 4000) });
        } else if (r.code !== 0 || !produced) {
            try { fs.unlinkSync(out); } catch (e) { /* none */ }
            results.set(t.name, { status: 'fail', message: 'compile failed (exit ' + r.code + '):\n' + r.output.slice(0, 4000) });
        } else if (t.modeGuard && compiler.target === 'js') {
            patchModeGuard(out);
        }
    };
    if (stale.length) {
        await compileOne(stale[0], 0);   // alone: it fills ELM_HOME
        let next = 1;
        await Promise.all(projects.map(async (_, k) => {
            while (next < stale.length) await compileOne(stale[next++], k);
        }));
    }
    if (compiler.target === 'js') {
        for (const t of toRun) D.writeIfChanged(path.join(outDir, t.name + '.run.js'), launcher(t.name, t.flags));
    }

    // 3. Run.
    const runnable = toRun.filter((t) => !results.has(t.name));
    const outputs = new Map();
    await pool(runnable, opts.jobs, async (t) => {
        const started = Date.now();
        let childEnv;
        try {
            childEnv = D.childEnv(t, Object.assign({}, process.env));
        } catch (e) {
            results.set(t.name, { status: 'fail', message: 'bad test directive: ' + String(e.message || e) });
            return;
        }
        const r = await new Promise((resolve) => {
            const piped = t.stdin !== null || t.stdinDelay !== null;
            const stdin = piped ? 'pipe' : fs.openSync(os.devNull, 'r');
            const base = compiler.target === 'js' ? [process.execPath, t.name + '.run.js'] : [outFile(t)];
            const argv = noCoreDumps(t.fsize === null ? base : [D.findPrlimit(), '--fsize=' + t.fsize + ':' + t.fsize, ...base]);
            const child = spawn(argv[0], argv.slice(1), { cwd: outDir, stdio: [stdin, 'pipe', 'pipe'], env: childEnv });
            if (typeof stdin === 'number') fs.closeSync(stdin);
            const chunks = [];
            child.stdout.on('data', (d) => chunks.push(d));
            child.stderr.on('data', (d) => chunks.push(d));
            child.on('error', (e) => chunks.push(Buffer.from(String(e))));
            let stdinTimer = null;
            if (piped) {
                child.stdin.on('error', () => {});
                const feed = () => child.stdin.end(t.stdin === null ? '' : t.stdin);
                if (t.stdinDelay === null) feed();
                else stdinTimer = setTimeout(feed, t.stdinDelay);
            }
            let timedOut = false;
            const timer = setTimeout(() => { timedOut = true; child.kill('SIGKILL'); }, opts.timeoutSec * 1000);
            child.on('close', (code, signal) => {
                clearTimeout(timer);
                if (stdinTimer) clearTimeout(stdinTimer);
                resolve({ code, signal, timedOut, output: Buffer.concat(chunks).toString('utf8') });
            });
        });
        fs.writeFileSync(path.join(outDir, t.name + '.log'), r.output);
        outputs.set(t.name, r);
        let message = '';
        if (r.timedOut) message = 'timed out after ' + opts.timeoutSec + ' s';
        else if (r.signal) message = 'killed by ' + r.signal;
        else if (r.code !== t.exit) message = 'exit code ' + r.code + ', expected ' + t.exit;
        if (!message && !opts.record) message = D.verifyPatterns(r.output, t.patterns);
        if (message) message += '\n--- output ---\n' + r.output.slice(0, 4000);
        results.set(t.name, { status: message ? 'fail' : 'pass', message, ms: Date.now() - started,
            output: r.output.slice(0, 4000), volatile: r.timedOut || r.signal !== null });
    });

    // Keep the results: one that may be an accident of the moment (r.volatile) is kept pending until
    // the next run gives it again. With --refresh, note each result that differs from the confirmed
    // entry it replaces.
    const firstLine = (m) => (m || '').split('\n')[0];
    for (const t of toRun) {
        const key = keys.get(t.name);
        const r = results.get(t.name);
        if (key === undefined || !r || r.status === 'skip') continue;
        const old = readEntry(cache, key);
        const pending = Boolean(r.volatile) &&
            !(old && old.result.status === r.status && firstLine(old.result.message) === firstLine(r.message));
        if (cache.refresh && old && !old.pending) {
            if (old.result.status !== r.status || (r.volatile ? firstLine(old.result.message) !== firstLine(r.message)
                : (old.result.message || '') !== (r.message || ''))) {
                cache.mismatches.push({ test: spec.name + '/' + t.name, was: old.result.status, now: r.status,
                    ranAt: old.ranAt });
                console.log('  DIFFERS FROM THE CACHE ' + spec.name + '/' + t.name + ': cached ' + old.result.status +
                    ' (ran ' + old.ranAt + '), now ' + r.status);
            }
        }
        writeEntry(cache, key, spec.name, t.name, r, pending);
    }

    // --record: print the run's output as CHECK lines.
    if (opts.record) {
        const t = selected[0];
        const res = results.get(t.name);
        if (res.status !== 'pass') {
            console.log('  FAIL ' + spec.name + '/' + t.name + '\n    ' + res.message.split('\n').join('\n    '));
            return { passed: 0, failed: 1, skipped: 0, failures: [spec.name + '/' + t.name], results: {} };
        }
        const lines = outputs.get(t.name).output.split('\n').map((l) => l.replace(/\r$/, ''))
            .filter((l) => l.trim() && !l.startsWith('Compiled in DEV mode.'));
        for (const l of lines) console.log('-- CHECK: ' + l);
        return { passed: 1, failed: 0, skipped: 0, failures: [], results: {} };
    }

    // 4. Summary.
    let passed = 0, failed = 0, skipped = 0;
    const failures = [];
    const json = {};
    for (const t of selected) {
        const r = results.get(t.name);
        json[t.name] = { status: r.status, reason: r.status === 'pass' ? '' : (r.message || '').split('\n')[0],
            message: r.status === 'pass' ? '' : (r.message || ''), output: r.output || '', tags: t.tags };
        if (r.ms !== undefined && r.ms !== null) json[t.name].ms = r.ms;
        if (r.cached) json[t.name].cached = r.cached;
        if (r.status === 'pass') passed++;
        else if (r.status === 'skip') { skipped++; console.log('  SKIP ' + spec.name + '/' + t.name + ': ' + r.message); }
        else {
            failed++;
            failures.push(spec.name + '/' + t.name);
            console.log('  FAIL ' + spec.name + '/' + t.name + '\n    ' + r.message.split('\n').join('\n    '));
        }
    }
    console.log('  ' + spec.name + ': passed ' + passed + ', failed ' + failed + ', skipped ' + skipped);
    return { passed, failed, skipped, failures, results: json };
}

// --- Main --------------------------------------------------------------------------------------

async function main() {
    const opts = parseArgs(process.argv.slice(2).filter((a) => a !== '--'));   // pnpm passes `--` through
    const cfg = loadCompilers();
    if (opts.listCompilers) {
        for (const [name, c] of Object.entries(cfg.compilers)) {
            console.log(name + (name === cfg.default ? ' (default)' : '') + ': ' + (c.description || c.command));
        }
        return 0;
    }
    const compiler = resolveCompiler(cfg, opts.compiler || cfg.default);
    const specs = projectSpecs();
    const unknown = opts.projects.filter((n) => !specs.some((s) => s.name === n));
    if (unknown.length) {
        throw new Error('unknown project(s): ' + unknown.join(', ') + ' (known: ' + specs.map((s) => s.name).join(', ') + ')');
    }
    if (opts.record && opts.projects.length !== 1) throw new Error('--record needs exactly one --project');
    const chosen = specs.filter((s) => !opts.projects.length || opts.projects.includes(s.name));
    console.log('Compiler ' + compiler.name + ': ' + compiler.command + ' (' + compiler.version + '), target ' + compiler.target);

    const cache = openCache(opts, compiler);
    let passed = 0, failed = 0, skipped = 0;
    const failures = [];
    const report = { compiler: compiler.name, version: compiler.version, description: compiler.description || '',
        target: compiler.target, node: process.version, projects: {} };
    for (const spec of chosen) {
        const r = await runProject(spec, opts, compiler, cache, specs.map((s) => s.name));
        passed += r.passed; failed += r.failed; skipped += r.skipped;
        failures.push(...r.failures);
        report.projects[spec.name] = r.results;
    }
    if (opts.record) return failed ? 1 : 0;
    if (cache.enabled) {
        const complete = !opts.projects.length && !opts.filters.length;
        const pruned = complete ? pruneCache(cache) : 0;
        console.log(compiler.name + ': ' + cache.hits + ' result(s) from the cache, ' + cache.written + ' written' +
            (cache.pending ? ' (' + cache.pending + ' pending a second run)' : '') +
            (pruned ? ', ' + pruned + ' unused entr' + (pruned === 1 ? 'y' : 'ies') + ' removed' : ''));
        report.cache = { hits: cache.hits, written: cache.written, pending: cache.pending, mismatches: cache.mismatches };
    }
    if (opts.json) {
        fs.mkdirSync(path.dirname(opts.json), { recursive: true });
        fs.writeFileSync(opts.json, JSON.stringify(report, null, 1));
    }
    console.log(compiler.name + ': tests run: ' + (passed + failed) + ', passed: ' + passed + ', failed: ' + failed +
        ', skipped: ' + skipped);
    return failed ? 1 : 0;
}

main().then((code) => process.exit(code), (e) => {
    console.error('run.js: ' + (e && e.message || e));
    process.exit(2);
});
