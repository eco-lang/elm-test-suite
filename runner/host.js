// host.js — the test driver's side of a pipe test (plans/host-pipe-tests.md): a test with
// `-- HOST-SEND: <port> <value>` lines has the driver send those boundary values, in order, on an
// incoming port, and print `<port> sent: <value>` for each value the program sends out on any
// outgoing port, for its CHECK lines to match.
//
// Boundary values are written as JSON, plus a byte sequence `bytes(00 ff 10)` (two hex digits a
// byte, separated by spaces), which is deliberately not JSON. `show` prints a value canonically: no
// spaces, object keys in increasing order, numbers as JSON.stringify prints them.
'use strict';

// A byte sequence of the notation, before it is given to the program.
class ByteSeq {
    constructor(os) { this.os = os; }
}

// Parse the notation; throws on a malformed text.
function parse(text) {
    let i = 0;
    const fail = (what) => { throw new Error('boundary value: ' + what + ' at ' + i + ' in ' + JSON.stringify(text)); };
    const ws = () => { while (i < text.length && /\s/.test(text[i])) i++; };
    const value = () => {
        ws();
        if (text.startsWith('bytes(', i)) {
            const close = text.indexOf(')', i);
            if (close < 0) fail('unclosed bytes(');
            const body = text.slice(i + 6, close).trim();
            const os = body === '' ? [] : body.split(/\s+/).map((h) => {
                if (!/^[0-9a-fA-F]{2}$/.test(h)) fail('bad byte ' + JSON.stringify(h));
                return parseInt(h, 16);
            });
            i = close + 1;
            return new ByteSeq(os);
        }
        const c = text[i];
        if (c === '[') {
            i++; ws();
            const xs = [];
            if (text[i] === ']') { i++; return xs; }
            for (;;) {
                xs.push(value()); ws();
                if (text[i] === ',') { i++; continue; }
                if (text[i] === ']') { i++; return xs; }
                fail('expected , or ]');
            }
        }
        if (c === '{') {
            i++; ws();
            const o = {};
            if (text[i] === '}') { i++; return o; }
            for (;;) {
                ws();
                if (text[i] !== '"') fail('expected a key');
                const k = jsonToken();
                ws();
                if (text[i] !== ':') fail('expected :');
                i++;
                o[k] = value(); ws();
                if (text[i] === ',') { i++; continue; }
                if (text[i] === '}') { i++; return o; }
                fail('expected , or }');
            }
        }
        return jsonToken();
    };
    // a JSON string, number or literal, read by JSON.parse
    const jsonToken = () => {
        const m = /^(?:"(?:[^"\\]|\\.)*"|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|true|false|null)/.exec(text.slice(i));
        if (!m) fail('unexpected text');
        i += m[0].length;
        return JSON.parse(m[0]);
    };
    const v = value();
    ws();
    if (i !== text.length) fail('trailing text');
    return v;
}

// The bytes of a host value, if it is a byte sequence.
function bytesOf(v) {
    if (v instanceof ByteSeq) return v.os;
    if (typeof DataView !== 'undefined' && v instanceof DataView) {
        return Array.from(new Uint8Array(v.buffer, v.byteOffset, v.byteLength));
    }
    if (v instanceof ArrayBuffer) return Array.from(new Uint8Array(v));
    if (ArrayBuffer.isView(v)) return Array.from(new Uint8Array(v.buffer, v.byteOffset, v.byteLength));
    return null;
}

// The canonical text of a boundary value.
function show(v) {
    if (v === undefined) return 'undefined';
    if (v === null || typeof v === 'boolean' || typeof v === 'string') return JSON.stringify(v);
    if (typeof v === 'number') return JSON.stringify(v);
    const os = bytesOf(v);
    if (os) return 'bytes(' + os.map((o) => o.toString(16).padStart(2, '0')).join(' ') + ')';
    if (Array.isArray(v)) return '[' + v.map(show).join(',') + ']';
    if (typeof v === 'object') {
        return '{' + Object.keys(v).sort().map((k) => JSON.stringify(k) + ':' + show(v[k])).join(',') + '}';
    }
    return String(v);
}

// The value the program is given: a byte sequence becomes a Uint8Array, the representation the book
// names for eco/JS (Appendix E, "Bytes at the Boundary"; Elm/JS has none).
function toHost(v) {
    if (v instanceof ByteSeq) return Uint8Array.from(v.os);
    if (Array.isArray(v)) return v.map(toHost);
    if (v !== null && typeof v === 'object') {
        const o = {};
        for (const k of Object.keys(v)) o[k] = toHost(v[k]);
        return o;
    }
    return v;
}

// Drive a started program: print what every outgoing port sends, then send each value of `sends`
// ([port, text] pairs) in order, one per turn of the event loop. A value the port rejects (Elm/JS
// throws from `send`) is dropped, as r:p-in-reject says, and the run goes on.
function drive(app, sends) {
    const ports = (app && app.ports) || {};
    for (const name of Object.keys(ports).sort()) {
        if (typeof ports[name].subscribe === 'function') {
            ports[name].subscribe((v) => console.log(name + ' sent: ' + show(v)));
        }
    }
    let k = 0;
    const next = () => {
        if (k >= sends.length) return;
        const [port, text] = sends[k++];
        const p = ports[port];
        if (!p || typeof p.send !== 'function') {
            console.error('host: the program has no incoming port ' + port);
            process.exitCode = 1;
            return;
        }
        try {
            p.send(toHost(parse(text)));
        } catch (e) {
            // rejected at the boundary
        }
        setTimeout(next, 0);
    };
    setTimeout(next, 0);
}

module.exports = { parse, show, drive, ByteSeq };
