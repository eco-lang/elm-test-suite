# Pipe tests: the test driver sends a boundary value in and checks what comes out

**Status (2026-11-15): done.** Ten pipe tests, all `elm-spec`, all translated and proved in Lean
(`scripts/verify.sh full`: 628 of 949 `elm-spec` tests end to end, 1,835 checks agree). The seven
JSON pipe tests pass on the four compilers; the Bytes tests cannot run on any of them (below).

## Why

The rules of the port boundary (Chapter 8, §8.7 "Ports": the Encoding rules `Enc_τ(v) = j` and
the Decoding rules `Dec_τ(j) = v`) are rules of the book's body. They mention the types `Value`,
`Bytes` and `Array` of the initial basis, but they need none of those modules' library functions.
A program can get a value of such a type from the boundary and send it straight back out. A test
needs only a host that can put the right boundary value in, and a way to see what comes out.

Today's tests reach the boundary in two ways:

- the **echo host** (`runner/run.js`, `launcher`), which sends every value sent out on `echoOut`
  back in on `echoIn`, so a test observes `Dec(Enc(v))` through `Debug.log`;
- the **flags** (`-- FLAGS:`), decoded at `main`'s flags type.

Neither lets the test driver observe `Enc_τ(Dec_τ(j))` for a `j` it chooses. That leaves
`e-enc-bytes`/`e-dec-bytes` without a test inside the basis (no program can make a `Bytes` value
from JSON), and makes the `Value` rules observable only after a second decode at a concrete type.
Comparing in Elm with `==` is no substitute: Elm's `==` on `Value` ignores keys only the right side
has, and on `Bytes` it compares nothing (`_Utils_eqHelp` loops over the left side's enumerable
keys; see `plans/test-review-candidates.md`).

## The idea: a pipe

The program receives a value on an incoming port at type `τ` and sends it out on an outgoing port of
the same type (or of a type that adds a counter, for the rejection tests). The driver sends the
values the test names, prints each value the program sends out, and the test's CHECK lines say what
those must be. The expected value need not be the value sent: a longer array at a tuple type comes
out shorter, an object with an extra key at a record type comes out without it.

```elm
-- HOST-SEND: valueIn {"b":[1,true,null],"a":"x"}
-- CHECK: valueOut sent: {"a":"x","b":[1,true,null]}

port valueIn : (Value -> msg) -> Sub msg
port valueOut : Value -> Cmd msg
```

## Directives and notation

- `-- HOST-SEND: <port> <boundary value>`: after `init`, the driver sends each value, in the order
  written, on the incoming port. A value the port rejects (Elm/JS throws from `send`) is dropped and
  the run goes on, as `p-in-reject` says. All the HOST-SEND lines of a test name one port.
- `-- CHECK: <port> sent: <boundary value>`: an ordinary CHECK line. In a test with HOST-SEND lines,
  the driver prints `<port> sent: <value>` for each value sent out on any outgoing port, in order.
- **Boundary values** are written as JSON, canonically: no spaces, object keys in increasing order
  (ASCII keys only), numbers as JavaScript's `JSON.stringify` prints them (tests use numbers whose
  printed form is exact). A byte sequence is `bytes(00 ff 10)`: two hex digits a byte, separated by
  spaces; `bytes()` is the empty sequence. It is deliberately not JSON, so it cannot be mistaken for
  a `Value`.

## Changes

1. **Runner** (`runner/run.js`, `runner/directives.js`): read HOST-SEND lines; parse the notation;
   in the launcher, subscribe to every outgoing port and print what it sends in canonical form, and
   send the HOST-SEND values one after another, catching a rejection. Tests without HOST-SEND lines
   are launched as before. README documents the directive.
2. **Lean** (`Prog/Exec.lean`, `Prog/Sched.lean`, `Prog/Worker.lean`):
   - `Host.feed i js`: sends the values `js`, in order, on the port `i`; it allows every outgoing
     event. Its state is the list of values sent so far, so `WorkerExec` and the hand theorems of
     `Prog/Inv` are unchanged.
   - `WorkerTest.sent : List (String × BVal)`: the values the test says are sent out, a sublist of
     the run's `Out` events, in order. `WorkerTest.Holds` adds this; `holds_of_run` proves it from
     the scheduler's run, by `decide +kernel` as before.
   - `run-examples` reports a row for each `sent` check.
3. **Translator** (`definition/tools`): read HOST-SEND lines and the `<port> sent:` CHECK lines of
   such a test; emit `host := .feed ...` and `sent := [...]`. The notation's parser is
   `Translate.Json`, with the bytes literal allowed only here (not in FLAGS, which the runner gives
   to `JSON.parse`).
4. **Tests** (`tests/elm/src/PortPipe*Test.elm`), all `elm-spec`:

   | Test | Pipe type | Sent → expected | Rules |
   |---|---|---|---|
   | PortPipeValueTest | `Value` | objects (key order), nested arrays, mixed array, string, number, null | `e-dec-value`, `e-enc-value` |
   | PortPipeTupleTest | `( Int, ( String, Bool ), Int )` | `[1,["a",false,"extra"],7]` → `[1,["a",false],7]` | `e-dec-tuple`, `e-enc-tuple` |
   | PortPipeRecordTest | `{ a : Int, b : { c : String } }` | `{"z":0,"b":{"d":1,"c":"x"},"a":1}` → `{"a":1,"b":{"c":"x"}}` | `e-dec-record`, `e-enc-record` |
   | PortPipeMaybeTest | `( Maybe Int, Maybe (Maybe Int) )` | `[null,null]`, `[5,7]` | `e-dec-nothing`, `e-dec-just`, `e-enc-nothing`, `e-enc-just` |
   | PortPipeScalarsTest | `{ f : Float, i : Int, s : String, t : Bool, u : () }` | `2.5` and `3` at `f`, `true`, `null` | `e-dec-float`, `e-enc-float`, `e-dec-true`, … |
   | PortPipeListArrayTest | `( List Int, Array String )` | `[[1,2,3],["a","b"]]`, `[[],[]]` | `e-dec-list`, `e-enc-list`, `e-dec-array`, `e-enc-array` |
   | PortPipeRejectTest | `Int` in, `( Int, Int )` out | `1.5`, `"3"`, `null`, `3`, `4` → `[1,3]`, `[2,4]` | `p-in-reject`, `p-in-accept`, `e-dec-int` |
   | PortPipeBytesTest | `Bytes` | `bytes(00 ff 10)`, `bytes()` → the same | `e-dec-bytes`, `e-enc-bytes` |
   | PortPipeBytesRejectTest | `Bytes` in, `( Int, Bytes )` out | `"00ff10"`, `[0,255,16]`, `null`, `bytes(01)` → `[1,bytes(01)]` | `e-dec-bytes`, `p-in-reject` |
   | PortPipeValueRejectsBytesTest | `Value` in, `( Int, Value )` out | `bytes(01)`, `{"a":bytes(02)}`, `null` → `[1,null]` | `e-dec-value` |

   The counter makes a rejection observable as a positive check: the first value accepted is
   numbered 1.

## Bytes at the JavaScript host

The book (Appendix E, "Bytes at the Boundary") says Elm/JS has no representation for bytes: Elm
0.19.x rejects every program with `Bytes` in a port type, so the Bytes tests are `elm19-bug`. eco/JS
represents a byte sequence as a `Uint8Array`, which is what the driver sends; it reads a `DataView`,
an `ArrayBuffer` or a typed array as bytes. The probe found that Lamdera 1.5.0 compiles `Bytes`
ports only with the `lamdera/codecs` package, which the shared test project cannot depend on
(Elm's compilers do not know it), so the Bytes tests fail on Lamdera too.

PortPipeValueRejectsBytesTest has no `Bytes` in its types, so every compiler builds it, but to
Elm/JS the driver's `Uint8Array` is a JavaScript value that is not a boundary value (outside the
definition), and a `Value` port passes it through. It is marked XFAIL with that reason.

## Order of work

1. This plan.
2. Runner and the JSON pipe tests; run them on the four compilers.
3. Lean host and checks, translator; translate the pipe tests; `verify.sh full`.
4. Lamdera probe; the Bytes tests; verify again.
5. README, `plans/untranslated-tests.md`, the mechanisation report, the site.
