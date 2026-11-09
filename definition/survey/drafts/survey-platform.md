# Survey Part 4: Programs, Platform, Effects and Ports

Scope: what a program is, `main`, flags, `Platform.Program` and the update loop, `Cmd`, `Sub`, `Task`,
`Process`, effect managers as far as they bear on program meaning, and ports at runtime. Static port
typing is recorded by another part; only the payload type grammar is repeated here, because the
runtime conversion is defined over it.

Path abbreviations used in cites:

| Abbrev | Path |
|---|---|
| `core/` | `/home/rupert/.eco/0.2.0/packages/elm/core/1.0.5/src/` (byte-identical to `~/.elm/0.19.1/packages/elm/core/1.0.5/src/`; `diff -rq` reports no difference) |
| `kjs/` | `/home/rupert/.elm/0.19.1/packages/elm/core/1.0.5/src/Elm/Kernel/` (Elm's JS kernel, reference behaviour) |
| `json-kjs/` | `/home/rupert/.elm/0.19.1/packages/elm/json/1.1.3/src/Elm/Kernel/Json.js` |
| `browser/` | `/home/rupert/.elm/0.19.1/packages/elm/browser/1.0.2/src/` |
| `elmc/` | `/home/rupert/sc/github/elm/compiler/` (reference Elm 0.19.1 Haskell compiler, commit 2f6dd29) |
| `eco/` | `/home/rupert/sc/gitlab/eco-compiler/` |
| `rt/` | `eco/runtime/src/platform/` |
| `kc/` | `eco/elm-kernel-cpp/src/` |
| `cs/` | `eco/compiler/src/Compiler/` |
| `sched.md` | `eco/design_docs/theory/runtime/scheduler-and-services.md` |
| `div.md` | `eco/design_docs/elm-divergence.md` |

## Sources

| Area | Files |
|---|---|
| Platform API (Elm) | `core/Platform.elm`, `core/Platform/Cmd.elm`, `core/Platform/Sub.elm`, `core/Task.elm`, `core/Process.elm` |
| Reference runtime (JS) | `kjs/Platform.js` (521 lines), `kjs/Scheduler.js` (195), `kjs/Process.js` (18), `kjs/Debug.js:233-292` (crash messages), `json-kjs` (decoders) |
| Browser program shapes | `browser/Browser.elm:63-219`, `browser/Elm/Kernel/Browser.js:29-140` |
| Reference compiler | `elmc/compiler/src/Optimize/Module.hs:245-272` (main), `elmc/compiler/src/Optimize/Port.hs` (codecs), `elmc/compiler/src/Canonicalize/Effects.hs:155-230` (payload check), `elmc/compiler/src/Generate/JavaScript/Expression.hs:1037-1049`, `elmc/compiler/src/Reporting/Error/Main.hs:20-110`, `elmc/terminal/src/Make.hs:95-233` |
| eco compiler | `cs/Canonicalize/Effects.elm:141-423`, `cs/LocalOpt/Erased/Port.elm` (JS codecs), `cs/LocalOpt/Typed/Port.elm` (native codecs), `cs/LocalOpt/Typed/Module.elm:180-200, 593-663`, `cs/LocalOpt/Error.elm:60-100`, `cs/PreMono/EntryPrep.elm`, `cs/GenerateMlir/Functions.elm:60-160, 375-400`, `cs/GenerateJs/Generate.elm:183-214`, `cs/GenerateJs/Expression.elm:1584-1595` |
| eco runtime | `rt/PlatformRuntime.cpp` (dispatch, initWorker, flags), `rt/Scheduler.cpp` (stepper, spawn, kill, run queue), `rt/PortRuntime.cpp` (ports, host API), `kc/EffectManagerRegistry.cpp`, `kc/core/TaskEffectManager.cpp`, `kc/core/PlatformExports.cpp`, `kc/core/ProcessExports.cpp`, `kc/json/JsonExports.cpp:1940-2100, 2636-2663` (payload checker), `kc/browser/BrowserExports.cpp`, `eco/runtime/src/embed/eco_embed.cpp`, `eco/runtime/src/embed/eco_node_addon.cpp` |
| Design notes | `sched.md` (main source for eco semantics), `div.md` sections 4.5, 4.6, 5.4, 5.10, 6; `eco/design_docs/debug-log-ordering-policy.md`; `eco/design_docs/invariants.csv:603-613` (PORT_001-011), `:703` (LIVE_004), `:706-708` (SCHED_001-002); `eco/docs/embedding.md`; `eco/docs/options.md:389-396`; `eco/THEORY.md:11, 78` |
| Test harness | `eco/test/ElmE2ETestBase.hpp:755-771, 931-1020` (echo bounce, `-- FLAGS:` directive), `eco/test/aot_port_host.cpp:1-80`, `eco/test/CheckPatterns.hpp:1-50` (CHECK semantics). Note: `eco/test/TestPort.hpp` is unrelated to Elm ports (it picks free TCP ports for server tests, `TestPort.hpp:1-16`). |
| Tests | `eco/test/elm/src/` (Port*, CovPort*, OutgoingPort*, Task*, Timer*, CmdBatchOrder*, Flags*, Entry*, NonEntryMain*), `eco/test/elm-core/src/Process*`, `TaskOnErrorCascadeTest`, `eco/test/elm-bugs/src/CoreIssue*`, `eco/test/eco-divergence/src/{FlagsBytesNative,PortBytes*}Test.elm` |

## Programs and main

A program is the module given to the compiler as root; its entry point is its top-level `main`.

| Fact | Cite |
|---|---|
| The optimizer recognises any top-level definition named `main` (`name /= Name._main` test); it does not consult the export list. | `elmc/compiler/src/Optimize/Module.hs:246-249`; eco `cs/LocalOpt/Typed/Module.elm:606-609` |
| `main`'s type, deep-dealiased, must be `VirtualDom.Node a` (Html, Svg) or `Platform.Program flags model msg`. Anything else (including any function type, so `main` with parameters) is `BAD MAIN TYPE`: "I only know how to handle Html, Svg, and Programs". | `elmc/compiler/src/Optimize/Module.hs:257-272`; `elmc/compiler/src/Reporting/Error/Main.hs:39-52`; eco `cs/LocalOpt/Typed/Module.elm:627-663` |
| `main` may not be recursive (`BAD MAIN`, "should be a boring value with no recursion"). | `elmc/compiler/src/Reporting/Error/Main.hs:54-66`; `div.md:206-208` |
| A `Node` main is `Static`; a `Program` main is `Dynamic msgType flagsDecoder`. | `elmc/compiler/src/Optimize/Module.hs:259-267`; `elmc/compiler/src/AST/Optimized.hs:144-145` |
| JS: a static main is rendered once by `_VirtualDom_init(main)(0)(0)`; a dynamic main is `main(flagsDecoder)(debugMetadata)` and the result is the `init` exported as `Elm.<Module>.init`. | `elmc/compiler/src/Generate/JavaScript/Expression.hs:1037-1049`; eco `cs/GenerateJs/Expression.elm:1584-1595`; `elmc/compiler/src/Generate/JavaScript.hs:504-560` |
| `elm make` to JS requires every root to have a `main` ("NO MAIN"); `--output=/dev/null` skips. | `elmc/terminal/src/Make.hs:106-113, 220-233`; `elmc/builder/src/Reporting/Exit.hs:1696-1708`; eco keeps `MakeNoMain`, `MakeNonMainFilesIntoJavaScript` (`eco/compiler/src/Builder/Reporting/Exit.elm:2058-2059`) |
| A `main` in an imported (non-root) module is an ordinary top-level value, evaluated once. | `eco/test/elm/src/NonEntryMainEvaluatedOnceTest.elm:1-15`; `EntryMainOfRootModuleTest.elm:1-14` |
| Native: the generated `main` is renamed `eco_main`; the C `main` calls it on a 64 MiB-stack thread and discards its value; the process exit code is what the program recorded, not `main`'s value. | `eco/runtime/src/codegen/eco_entry.cpp:3-14, 100-106, 158`; `sched.md:180` |
| Native: evaluating `Platform.worker impl` *runs* the program (`Elm_Kernel_Platform_worker` calls `initWorker`, which ends in the event loop). | `kc/core/PlatformExports.cpp:107-112`; `rt/PlatformRuntime.cpp:769-887` |
| Native: a static (`Html`) main is only evaluated; nothing renders. Many tests use `main = let _ = Debug.log ... in Html.text "done"`. | `eco/test/elm/src/CovPortIncomingUnitTest.elm:38-43` |
| Native: `Browser.element`, `document`, `application` return their record unchanged, so `init` never runs; `Browser.Navigation.*` ends the program with "... is not supported natively", exit 1; `Browser.Dom` tasks fail with `NotFound`. | `kc/browser/BrowserExports.cpp:3-10, 35-45` |
| Program shapes (`elm/browser`): `sandbox {init : model, view, update : msg -> model -> model} -> Program () model msg` (defined via `element` with `Cmd.none`/`Sub.none`); `element` and `document` take `{init : flags -> (model, Cmd msg), view, update, subscriptions}`; `application` adds `init : flags -> Url -> Navigation.Key -> ...`, `onUrlRequest`, `onUrlChange`. | `browser/Browser.elm:63-75, 104-111, 122-129, 207-219` |
| eco extension: a `Program` whose flags type is eco/system's `System.Environment` gets a built-in environment decoder; no payload check applies. | `cs/LocalOpt/Typed/Module.elm:634-647`; `eco/docs/getting-started.md:69-72` |
| One program per process natively (embedding: `eco_app_start` once; Node addon `init` once). JS allows several `init` calls, sharing the global `_Platform_effectsQueue`. | `eco/docs/options.md:393-394`; `kjs/Platform.js:238-239` |

## Flags

| Fact | Cite |
|---|---|
| Permitted flags types are exactly the port payload types (`checkPayload`), else `BAD FLAGS` with a per-reason message (extended record, function, type variable, unsupported type). | `elmc/compiler/src/Optimize/Module.hs:265-269`; `elmc/compiler/src/Reporting/Error/Main.hs:68-110`; eco `cs/LocalOpt/Typed/Module.elm:649-657` |
| Flags decoder = port decoder for the type, except flags of type `()` decode with `Json.Decode.succeed ()`, accepting any value (a `()` port accepts only `null`). | `elmc/compiler/src/Optimize/Port.hs:141-149`; eco `cs/LocalOpt/Erased/Port.elm:245-260` |
| JS: flags are `args.flags` of `Elm.M.init(args)`, or `undefined` if absent; decoded with `Json.run`; failure throws "Problem with the flags given to your Elm program on initialization." from `init` (crash 2). | `kjs/Platform.js:37-38`; `kjs/Debug.js:249-251` |
| eco native: absent flags decode as JSON `null`; a decode failure prints `eco: problem with the flags given to this program: <json>` and aborts. Flags given to a program with no decoder abort unless they are `null`. | `rt/PlatformRuntime.cpp:740-790` (esp. `:752`, `:778`, `:783`) |
| eco embedding: `eco_app_start(argc, argv, flags_json)` checks the flags against the compiled descriptor on the calling thread before starting; mismatch returns `ECO_APP_ERR_BAD_FLAGS` with the JS message, and the host may retry. Node addon: `JSON.stringify(opts.flags)`, `undefined` becomes `null`, BAD_FLAGS becomes a thrown error. | `eco/runtime/src/embed/eco_embed.cpp:267-295`; `eco_node_addon.cpp:744`; `eco/docs/options.md:393-394` |
| Standalone native executables parse no runtime flags; tests supply flags by a `-- FLAGS: {json}` directive read by the harness. | `eco/docs/options.md:395`; `eco/test/ElmE2ETestBase.hpp:944-1014` |
| Native only: `Bytes` anywhere in the flags type is `BAD FLAGS` ("wants `Bytes` in its flags"); the JS target accepts it. | `cs/LocalOpt/Typed/Module.elm:650-651`; `cs/LocalOpt/Error.elm:74-86`; `eco/test/eco-divergence/src/FlagsBytesNativeTest.elm:1-14` |

## The Update Loop

Reference algorithm (`kjs/Platform.js:35-55`), for `worker`, `element`, `document`, `application`:

1. Decode flags (above). 2. `initPair = init flags`; `model = initPair.a`. 3. Build the view stepper (worker: no-op, `Platform.js:26`). 4. Set up every effect manager and port (`_Platform_setupEffects`, `:82-101`). 5. `enqueueEffects(initPair.b, subscriptions model)` (`:52`). 6. Return `{ports}` to the host (`:54`).

Each message `msg` delivered to the program runs `sendToApp` (`:45-50`): `(model', cmd) = update msg model`; set `model := model'`; call the stepper (view); `enqueueEffects(cmd, subscriptions model')`.

| Property | Reference behaviour | eco | Cites |
|---|---|---|---|
| Message queue | None: a message is applied by direct call of `sendToApp` from whatever produced it (a task's `sendToApp` binding, an incoming port `send`, a DOM event). | Same direct call (`deliverToApp`, `sendToApp`), but host port sends are queued (below). | `kjs/Platform.js:153-160, 457-468`; `rt/PlatformRuntime.cpp:563-579` |
| Effects queue | `enqueueEffects` pushes `(cmdBag, subBag)` onto a FIFO; if already dispatching, returns; otherwise dispatches until empty. Prevents FX of a later update overtaking an earlier one (elm/core #980). | Same algorithm (`effectsQueue_`, `effectsActive_`). | `kjs/Platform.js:209-254`; `rt/PlatformRuntime.cpp:318-341` |
| When `subscriptions` runs | After `init` and after every `update`, on the new model, whether or not it changed. | Same (`initWorker`, `workerSendToAppEvaluator`). | `kjs/Platform.js:49, 52`; `rt/PlatformRuntime.cpp:698-726, 873-874` |
| Who receives effects | Every manager receives an `fx` message on every dispatch, with empty lists if it has no effects, so a manager can drop subscriptions. | Same: every manager's `onEffects` runs every dispatch. | `kjs/Platform.js:263-269`; `rt/PlatformRuntime.cpp:353-431`; `sched.md:150` |
| Dispatch timing | `rawSend` to each manager process; at top level (init) the scheduler runs to completion inside the send; inside a step the processes are only queued. | Each manager's `onEffects` task is spawned and the whole run queue drained before the next manager; dispatch completes inside the drain that ran the update (LIVE_004). | `kjs/Scheduler.js:88-92, 135-148`; `rt/PlatformRuntime.cpp:395-430`; `invariants.csv:703` |
| Manager order within a dispatch | `for (var home in managers)`: JS object key order, i.e. registration order of managers and ports in the generated code. | `std::unordered_map` iteration order (unspecified). | `kjs/Platform.js:87, 263`; `rt/PlatformRuntime.hpp:243, 266` |
| View | `element`/`document`: `view` drawn at init, then at most once per animation frame after updates (`_Browser_makeAnimator`). Not observable to Elm code. | Not run natively. | `browser/Elm/Kernel/Browser.js:110-136`; `kc/browser/BrowserExports.cpp:35-45` |
| Re-entrancy | An update can run inside another dispatch (e.g. a synchronous task); its effects are queued behind the current batch. | Same. | `kjs/Platform.js:211-227`; `sched.md:150` |

## Cmd

`type Cmd msg = Cmd` is opaque in Elm (`core/Platform/Cmd.elm:47`); the runtime representation is a bag tree.

| Construct | Elm signature (cite) | Runtime meaning | Cite |
|---|---|---|---|
| leaf | (internal) `command : MyCmd msg -> Cmd msg` generated for an effect module, `port p : a -> Cmd msg` | `{LEAF, home, value}`; `home` is the manager's module name or the bare port name | `kjs/Platform.js:176-186`; `kc/core/PlatformExports.cpp:114` |
| `Cmd.batch : List (Cmd msg) -> Cmd msg` | `core/Platform/Cmd.elm:66-68` | `{NODE, bags}` | `kjs/Platform.js:189-195`; `kc/core/PlatformExports.cpp` (`Elm_Kernel_Platform_batch`) |
| `Cmd.none = batch []` | `core/Platform/Cmd.elm:53-55` | empty node. Doc: `none`, `batch [none, none]`, `batch []` "all do the same thing" | `core/Platform/Cmd.elm:63-64` |
| `Cmd.map : (a -> msg) -> Cmd a -> Cmd msg` | `core/Platform/Cmd.elm:83-85` | `{MAP, func, bag}`; at gather time the chain of taggers (innermost first) is handed to the manager's `cmdMap` as one function | `kjs/Platform.js:198-205, 290-316`; `rt/PlatformRuntime.cpp:434-541` |
| Ordering doc | "Each is handed to the runtime at the same time ... there are no ordering guarantees about the results." | | `core/Platform/Cmd.elm:58-61` |
| Ordering as implemented | Gathering conses each leaf onto its manager's list, so a manager receives a batch's commands in **reverse** (flattened depth-first) order. Task manager spawns in list order, so `batch [perform a, perform b]` runs `b` first; ports deliver `batch [out 1, out 2]` as 2 then 1. | eco gathers in source order and then iterates last-first in the Task and port managers to reproduce it (PORT_005). | `kjs/Platform.js:319-328`; `kc/core/TaskEffectManager.cpp:62-68, 85-98`; `rt/PortRuntime.cpp:168-197`; test `CmdBatchOrderTest` |
| Deep nesting | JS gathers recursively: 100000 nested batches overflow the stack (elm/core #1123). | eco gathers with an explicit worklist. | `kjs/Platform.js:273-297`; `rt/PlatformRuntime.cpp:440-446`; `eco/test/elm-bugs/src/CoreIssue1123NestedCmdBatchStackOverflowTest.elm:1-13` |
| Leaf for unknown home | JS: impossible (every home is registered). | eco: silently dropped when no manager is registered for the home. | `rt/PlatformRuntime.cpp:471-473` |

## Sub

| Construct | Signature (cite) | Meaning | Cite |
|---|---|---|---|
| `Sub.batch`, `Sub.none = batch []`, `Sub.map` | `core/Platform/Sub.elm:54-56, 65-67, 82-84` | Same bag kernels as Cmd (`Elm.Kernel.Platform.batch`, `map`); gathered with `isCmd = false` | `kjs/Platform.js:189-205, 260-261` |
| Lifetime | A subscription is active exactly while it appears in the latest `subscriptions model`; managers receive the full current list every dispatch and diff it themselves (e.g. an incoming port just replaces its list). | | `kjs/Platform.js:449-453`; `rt/PortRuntime.cpp:225-243, 543-548` |
| `Sub.map` on an incoming port | `subMap f g = \v -> f (g v)` (composition). | eco same. | `kjs/Platform.js:430-436`; `rt/PortRuntime.cpp:13-15, 251-289` |
| `Cmd.map` on an outgoing port | Taggers dropped (`outgoingPortMap tagger value = value`): a port command produces no message. | eco same. | `kjs/Platform.js:360`; `rt/PortRuntime.cpp:245-249` |
| Several subscriptions to one incoming port | Each delivered value is passed to every tagger; list is reversed (consed), so taggers run last-first. | eco iterates last-first (PORT_005). | `kjs/Platform.js:464-467`; `rt/PortRuntime.cpp:706-714` |

## Task and Process

`Task x a` is `Platform.Task x a` (`core/Task.elm:59-60`, `core/Platform.elm:83`); it is a description, not a running computation (`core/Task.elm:56-57`). Running a Task value twice performs its effects twice (`sched.md:71`).

| Function | Type | Definition / semantics | Cite |
|---|---|---|---|
| `succeed` | `a -> Task x a` | kernel `{SUCCEED, value}` | `core/Task.elm:78-80`; `kjs/Scheduler.js:10-16` |
| `fail` | `x -> Task x a` | kernel `{FAIL, value}` | `core/Task.elm:92-94`; `kjs/Scheduler.js:18-24` |
| `andThen` | `(a -> Task x b) -> Task x a -> Task x b` | kernel node; continuation runs on success | `core/Task.elm:207-209`; `kjs/Scheduler.js:35-42` |
| `onError` | `(x -> Task y a) -> Task x a -> Task y a` | kernel node; handler runs on failure | `core/Task.elm:227-229`; `kjs/Scheduler.js:44-51` |
| `map`, `map2`..`map5` | | defined by `andThen`/`succeed`; **sequential**, left to right | `core/Task.elm:117-170` |
| `sequence` | `List (Task x a) -> Task x (List a)` | `List.foldr (map2 (::)) (succeed [])`; "run in order one-by-one and if any task fails the whole sequence fails" | `core/Task.elm:175-185` |
| `mapError` | `(x -> y) -> Task x a -> Task y a` | `onError (fail << convert)` | `core/Task.elm:246-249` |
| `perform` | `(a -> msg) -> Task Never a -> Cmd msg` | `command (Perform (map toMessage task))`; `Never` error type makes failure impossible | `core/Task.elm:282-284` |
| `attempt` | `(Result x a -> msg) -> Task x a -> Cmd msg` | `task |> andThen (succeed << f << Ok) |> onError (succeed << f << Err)` | `core/Task.elm:311-317` |
| `Process.spawn` | `Task x a -> Task y Id` | binding: `rawSpawn task`, succeed with the id; spawned process cannot receive messages | `core/Process.elm:70-84`; `kjs/Scheduler.js:81-86`; `rt/Scheduler.cpp:514-522` |
| `Process.sleep` | `Float -> Task x ()` | ms delay; JS `setTimeout(time)`, killable | `core/Process.elm:87-95`; `kjs/Process.js:9-18`; `kc/core/ProcessExports.cpp` (`sleepBindingBody`) |
| `Process.kill` | `Id -> Task x ()` | calls the parked binding's kill handle (aborts timers, HTTP), sets root to null | `core/Process.elm:98-105`; `kjs/Scheduler.js:102-115`; `rt/Scheduler.cpp:530-570` |

Scheduler semantics (reference `kjs/Scheduler.js:131-195`, eco `rt/Scheduler.cpp` `stepProcess`, `sched.md:44-71`):

| Property | Reference | eco | Cite |
|---|---|---|---|
| Model | A process = id, root task, stack of `(SUCCEED|FAIL, callback)` frames, mailbox. Single run queue, FIFO. | Same structure, immutable heap values, 64-bit ids, processes replaced not mutated. | `kjs/Scheduler.js:66-79, 118-132`; `sched.md:15-29, 75-81` |
| Stepping | `AND_THEN`/`ON_ERROR` push a frame; `SUCCEED`/`FAIL` pop frames until one of the same kind and apply it; `BINDING` runs its callback and parks; `RECEIVE` takes the oldest mailbox message or parks. | Same case analysis. | `kjs/Scheduler.js:151-195`; `sched.md:46-67` |
| Pre-emption | None: a process runs until it parks at a binding or an empty receive. (The `Process` doc says the runtime "will pause it at an `andThen`"; the stepper does not.) | None. | `core/Process.elm:53-57`; `kjs/Scheduler.js:153-193`; `sched.md:46-67` |
| Enqueue | `_Scheduler_enqueue` runs the queue to completion if not already running (synchronous). | Enqueue never runs; only explicit drains (event loop, dispatch) run processes. | `kjs/Scheduler.js:135-148`; `rt/Scheduler.cpp:576-585`; `sched.md:85-91` |
| Unhandled `fail` | Process ends silently (`if (!proc.__stack) return`). | Process ends; warning `[eco-runtime] unhandled top-level Task.fail ...` on stderr (SCHED_002). | `kjs/Scheduler.js:158-165`; `rt/Scheduler.cpp:993-1000`; `invariants.csv:708` |
| Kill finished / twice | `proc.__root` is null: reading `.$` throws TypeError (elm/core #955). | No-op; a process killing itself is not stopped. | `kjs/Scheduler.js:105`; `rt/Scheduler.cpp:556-566`; `elm-bugs/src/CoreIssue955KillProcessTwiceTest.elm:1-12` |
| `sleep 0`, negative | `setTimeout(0)`, about 1 ms on node. | Wakes at once (a yield). | `div.md:325-328, 486` |
| `sleep` NaN, infinite, > 2^31-1 ms | node `setTimeout` treats as about 1 ms. | 1 ms (copied from node). | `div.md:325-327`; `elm-core/src/ProcessSleepNonFiniteTest.elm:1-17` |
| Program liveness | Browser/node event loop. | Program runs while a hold exists (pending timer, HTTP, queued host send); exits when none remain and nothing is runnable. | `sched.md:3, 118-126` |
| Divergence statement | | "The order in which eco's scheduler runs Tasks, Cmds, subscriptions and `Process.sleep` callbacks may differ from Elm's JS scheduler ... TODO: list what eco guarantees." | `div.md:442-447` |

## Effect Managers

| Fact | Cite |
|---|---|
| An effect manager is an `effect module M where { command = C }` and/or `{ subscription = S }` defining `init : Task Never state`, `onEffects : Router msg self -> List (C msg) -> [List (S msg) ->] state -> Task Never state`, `onSelfMsg : Router msg self -> self -> state -> Task Never state`, `cmdMap`, `subMap`. | `core/Task.elm:1, 256-351`; `cs/Canonicalize/Effects.elm:16-20` |
| Runtime instance: a process looping `receive msg -> (SELF ? onSelfMsg : onEffects)`, threading the state. | `kjs/Platform.js:116-146` |
| `Router appMsg selfMsg`; `sendToApp : Router msg a -> msg -> Task x ()` delivers to `update`; `sendToSelf : Router a msg -> msg -> Task x ()` posts to the manager's own mailbox. Both are Tasks (act when run). | `core/Platform.elm:95-120`; `kjs/Platform.js:153-169`; `kc/core/PlatformExports.cpp` (`sendToApp`, `sendToSelf` bindings, "Until 2026-11-06 both sent at once") |
| Task manager: `onEffects` spawns one process per `Perform task`, each `task |> andThen (sendToApp router)`; state `()`; `onSelfMsg` ignores (`Never`). | `core/Task.elm:329-351`; eco C++ reimplementation `kc/core/TaskEffectManager.cpp:62-140, 216-238` |
| Managers in the elm/* packages: `Task` (core, command), `Time` (subscription), `Http` (command, subscription), `Random` (command), `Browser.Events`, `Browser.AnimationManager` (subscription). | `grep '^effect module'` over `~/.elm/0.19.1/packages`: `elm/time/1.0.0/src/Time.elm:1`, `elm/http/2.0.0/src/Http.elm:1`, `elm/random/1.0.0/src/Random.elm:1`, `elm/browser/1.0.2/src/Browser/Events.elm:1`, `.../AnimationManager.elm:1`, `core/Task.elm:1` |
| Ports are pseudo-managers keyed by the bare port name: outgoing has only `cmdMap`, incoming only `subMap`. | `kjs/Platform.js:348-357, 418-427`; `sched.md:160`; `invariants.csv:603` |
| eco native registers only Time, Http, Task (C++), eco/system managers (generated preamble), and ports. Commands for any other home (e.g. `Random.generate`, `Browser.Events`) find no manager and are dropped. | `kc/EffectManagerRegistry.cpp:13-22`; `sched.md:130-137`; `cs/GenerateMlir/Functions.elm:142-160, 383-394`; `rt/PlatformRuntime.cpp:471-473` |
| eco runs each manager's `init` at setup, then every handler synchronously; a handler task that parks would lose state (LIVE_004). | `rt/PlatformRuntime.cpp:198-312`; `sched.md:148-156, 215` |

## Ports at Runtime

Payload grammar (shared by ports and flags; checked statically): `P ::= Int | Float | Bool | String | Json.Encode.Value | () | Maybe P | List P | Array P | (P, P) | (P, P, P) | { l1 : P, ..., ln : P }` (closed record), after alias expansion. Everything else is rejected: `Char`, custom types (incl. `Dict`, `Set`, `Result`), type variables, functions, extensible records. eco adds `Bytes.Bytes`. Cites: `elmc/compiler/src/Canonicalize/Effects.hs:158-200`; `cs/Canonicalize/Effects.elm:255-347`.

Port shapes: outgoing `p : P -> Cmd msg` with `msg` a variable; incoming `p : (P -> msg) -> Sub msg` with the same variable (`cs/Canonicalize/Effects.elm:130-210`). Codecs are compiler-generated from the type (`elmc/compiler/src/Optimize/Port.hs`; `cs/LocalOpt/Erased/Port.elm` for JS, `cs/LocalOpt/Typed/Port.elm` for native).

Host interface:

| | Reference (JS) | eco native (embedding C API / Node addon) | Cites |
|---|---|---|---|
| Handle | `app.ports.p.subscribe(f)` / `unsubscribe(f)` for outgoing; `app.ports.p.send(v)` for incoming; only ports reachable from `main` exist. | `eco_port_subscribe(name, cb, user)`, `eco_port_send(name, json)` (0 queued, 1 not a port, 2 rejected + `eco_last_error()`); Node addon mirrors `app.ports`. Only ports reached during monomorphization are registered (PORT_003). | `kjs/Platform.js:388-410, 457-470`; `rt/PortRuntime.cpp:1182-1218`; `invariants.csv:605`; `eco/docs/embedding.md:29-42, 123-128` |
| Value form | JS values (objects, arrays, numbers...). | UTF-8 JSON text in both directions; Bytes ports carry raw bytes. | `rt/PortRuntime.cpp:3-15, 179-197`; `eco/docs/embedding.md:41-42` |
| Outgoing: when | The port manager's `init` is `Process.sleep 0`, and `onEffects` returns that sleep as the next state: the first delivery waits one timer tick (so the host can subscribe after `init` returns), and after each batch the manager sleeps 0 ms before taking the next batch. | Delivered synchronously inside dispatch of the update that issued it; the program waits while subscribers run. | `kjs/Platform.js:128-145, 370-386`; `rt/PortRuntime.cpp:179-197, 550-573`; `eco/docs/embedding.md:34-35` |
| Outgoing: no subscriber | Value is converted and discarded. | Buffered until the first subscriber, then handed to it in order; once a port has had a subscriber, values sent with none are dropped. | `kjs/Platform.js:375-383`; `rt/PortRuntime.cpp:550-566`; `rt/PortRuntime.hpp:20-31, 345-350` |
| Outgoing: order | Reverse of batch order within one dispatch (above); separate updates in update order. | Same within a batch (PORT_005). | `rt/PortRuntime.cpp:168-172`; test `CmdBatchOrderTest` |
| Incoming: when | `send` decodes, then calls `sendToApp` for each current subscription **synchronously**: `update` runs inside `send`. | Checked on the calling thread, then queued; delivered on the eco thread after the current run queue drains. A send from inside a subscriber is also queued. | `kjs/Platform.js:457-468`; `rt/PortRuntime.cpp:755-779, 605-718`; `sched.md:160-162, 174`; `eco/docs/embedding.md:36-37` |
| Incoming: no subscription | Decoded (and may throw), then delivered to nobody. | Delivered to no tagger. | `kjs/Platform.js:464`; `rt/PortRuntime.cpp:706-714` |
| Incoming mismatch | `send` throws `Error("Trying to send an unexpected type of value through port \`p\`:\n" + problem)` to the caller (crash 4); program state unaffected. | Embedding: `eco_port_send` returns 2 and `eco_last_error()` holds the same message; Node addon throws it. If no descriptor is known the eco thread decodes, and failure aborts: `eco ports: trying to send an unexpected value through port 'p': <json>`. | `kjs/Platform.js:459-461`; `kjs/Debug.js:257-261`; `rt/PortRuntime.cpp:755-779, 694-697, 338-343`; `eco_node_addon.cpp:450-459`; `invariants.csv:611` |
| Duplicate names | Second registration of a port name throws "There can only be one port named ..." at load (crash 3). | Abort: "duplicate port name" or "collides with an existing effect manager" (e.g. a port named `Task`). | `kjs/Platform.js:335-341`; `kjs/Debug.js:253-255`; `rt/PortRuntime.cpp:449-468`; `invariants.csv:603` |

Conversion table. "JSON" means the JSON value model (eco: JSON text; JS: the JS value before stringification). Incoming checks are the `Json.Decode` primitive rules (`json-kjs:45-79, 202-311`) and, in eco, the payload checker (`kc/json/JsonExports.cpp:1944-2060`) plus the eco-thread decoder.

| Elm type | Outgoing representation | Incoming accepted | On mismatch / edge cases | Cite |
|---|---|---|---|---|
| `Int` | JSON number (`Json.Encode.int`) | JS: any `number` with no fractional part that is finite (`1.0` ok; `1e300` ok, `-0` ok). eco: JSON integer or integral float in the signed 64-bit range (`1.0` gives 1, `-0.0` gives 0). | `1.5`, NaN, Infinity, strings: "Expecting an INT". eco: `9223372036854775808`, `1e300` rejected. Outgoing above 2^53: JS cannot hold it; eco writes it exactly. | `elmc/.../Port.hs:49`; `json-kjs:45-55`; `kc/json/JsonExports.cpp:1972, 2054-2059`; `div.md:330-338, 399-405` |
| `Float` | JSON number | any number | non-number rejected ("a FLOAT"). JS: NaN/Infinity pass both ways as JS numbers. eco: outgoing NaN/Infinity written as `null` (JSON.stringify rule); incoming NaN not expressible in JSON text; Node addon stringifies NaN to `null`, which a Float port rejects. | `json-kjs:63-67`; `kc/json/JsonExports.cpp:1973`; `div.md:399-402`; `eco_node_addon.cpp:425-441` |
| `Bool` | `true`/`false` | JSON boolean only | `0`, `"true"` rejected | `json-kjs:57-61`; `JsonExports.cpp:1974` |
| `String` | JSON string (eco: lone surrogates as `\udxxx`) | JSON string (JS also a `String` object) | other types rejected | `json-kjs:73-79`; `div.md:399-405` |
| `Char` | rejected statically | | | `cs/Canonicalize/Effects.elm:258-264` |
| `()` | `null` | `null` only (port); any value (flags) | JS `undefined` (e.g. `send()`) rejected | `elmc/.../Port.hs:40-41, 247-250`; `cs/LocalOpt/Erased/Port.elm:63-64, 391-396`; `JsonExports.cpp:1976` |
| `Maybe a` | `Nothing` as `null`; `Just v` as v's encoding (no wrapper) | `oneOf [null Nothing, map Just a]`: `null` first, so `Maybe (Maybe Int)` maps `null` to outer `Nothing`; `Just Nothing` is not representable | JS `undefined` and missing values are not `null`: rejected. | `cs/LocalOpt/Erased/Port.elm:127-151, 313-352`; `elmc/.../Port.hs:202-216`; `JsonExports.cpp:1977-1983` |
| `List a` | JSON array | JSON array (JS also `FileList`), each element decoded | non-array: "Expecting a LIST"; first bad element reported with its index | `json-kjs:214-219, 313-327, 329-332` |
| `Array a` | JSON array | JSON array | "Expecting an ARRAY" | `json-kjs:221-226` |
| `(a, b)`, `(a, b, c)` | JSON array of 2 or 3 elements in order | array decoded by `index 0..n-1`: arrays with **extra** elements accepted, extras ignored | too short: "a LONGER array"; non-array rejected | `cs/LocalOpt/Erased/Port.elm:180-238, 399-461`; `json-kjs:237-248`; `JsonExports.cpp:2000-2021` |
| closed record `{f : a, ...}` | JSON object, keys = field names, emitted in field-name (alphabetical) order | object with every field, decoded by `field`; **extra fields ignored** | missing field: "Expecting an OBJECT with a field named \`f\`"; fields are decoded last-alphabetical first, so with several missing the reported field is the alphabetically last (eco's checker walks in descriptor order) | `elmc/.../Port.hs:66-75`; `cs/LocalOpt/Erased/Port.elm:96-120, 465-523`; `json-kjs:228-235`; `JsonExports.cpp:2022-2040` |
| extensible record, type variable, function, custom type | rejected statically | | | `elmc/.../Effects.hs:176-200` |
| `Json.Encode.Value` | passed through (`identity`) | anything (`Json.Decode.value`) | never fails. JS: non-JSON JS values (functions, DOM nodes, `undefined`) pass through untouched; eco: only JSON text can cross | `elmc/.../Port.hs:53`; `json-kjs:69-71`; `JsonExports.cpp:1971` |
| `Bytes` (eco only) | JS target: `Uint8Array` over the bytes. Native: allowed only as the whole payload ("bytes port"), raw bytes, no copy for subscribers. | JS: `Uint8Array`, `ArrayBuffer`, `DataView`. Native: host buffer copied once. | JS: "Expecting a BYTES value (...)". Native: `Bytes` nested in another payload type is a compile error (`PORT ERROR`). Elm 0.19.1 rejects `Bytes` statically. | `cs/Canonicalize/Effects.elm:295-296`; `cs/GenerateJs/Generate.elm:190-214`; `cs/LocalOpt/Typed/Module.elm:180-200`; `sched.md:164-170`; `eco-divergence/src/PortBytesNestedNativeTest.elm:1-23` |

eco payload descriptor grammar (for host-side checks): `i f b s u v`, `M<x> L<x> A<x>`, `(<x><y>[<z>])`, `{<len>:<name><x>...}`; an unknown descriptor letter is accepted and left to the eco-thread decoder (`kc/json/JsonExports.cpp:1944-1956, 2041-2045`).

## Eco Differences

| # | Topic | Elm 0.19.1 (JS) | eco | Cite |
|---|---|---|---|---|
| E1 | Host value form | JS values | JSON text (and raw bytes) | `rt/PortRuntime.cpp:3-15` |
| E2 | Incoming delivery | synchronous inside `send` | queued, delivered after current work; fixes elm/core #1110, #1141, #1154 (reply lost because the subscription was not yet installed) | `sched.md:160-162, 174`; `elm-bugs/src/CoreIssue1110*`, `*1141*`, `*1154*` |
| E3 | Outgoing with no subscriber | dropped | buffered until first subscriber | `rt/PortRuntime.cpp:550-566` |
| E4 | Outgoing timing | asynchronous (port manager sleeps 0 between batches) | synchronous in dispatch | `kjs/Platform.js:370-386` |
| E5 | Bad incoming value | JS exception to caller | error code at call; abort if found on eco thread | `rt/PortRuntime.cpp:755-779, 694-697` |
| E6 | Absent flags | `undefined` | `null` | `kjs/Platform.js:37`; `rt/PlatformRuntime.cpp:776-778` |
| E7 | Bad flags | exception from `init` | abort (executable) or `ECO_APP_ERR_BAD_FLAGS` (embedding) | `rt/PlatformRuntime.cpp:750-756`; `eco_embed.cpp:274-282` |
| E8 | Int range at boundary | any integral double | signed 64-bit | `div.md:330-338` |
| E9 | NaN/Infinity Float out | JS NaN/Infinity | `null` | `div.md:399-402` |
| E10 | Bytes payloads | rejected | allowed (JS anywhere; native whole payload only; not in native flags) | `cs/Canonicalize/Effects.elm:260-262`; `cs/LocalOpt/Error.elm:74-86` |
| E11 | Manager order in dispatch | registration order | hash order | `rt/PlatformRuntime.hpp:243, 266` |
| E12 | Unhandled spawned failure | silent | stderr warning | `rt/Scheduler.cpp:993-1000` |
| E13 | Kill finished process | TypeError crash | no-op | `rt/Scheduler.cpp:556-566` |
| E14 | `Process.sleep 0`/negative | about 1 ms | immediate yield | `div.md:325-328` |
| E15 | Deep `Cmd.batch` | stack overflow | works | `rt/PlatformRuntime.cpp:440-446` |
| E16 | Native Browser programs and Elm-source managers | full | `init` never runs; `Random`, `Browser.Events` commands/subs dropped | `kc/browser/BrowserExports.cpp:35-45`; `kc/EffectManagerRegistry.cpp:13-22` |
| E17 | Environment flags | n/a | `Program System.Environment ...` gets a built-in decoder | `cs/LocalOpt/Typed/Module.elm:634-647` |
| E18 | Instances | many `init` calls per page | one program per process | `eco/docs/options.md:393-394` |
| E19 | `Debug.log` under `--optimize` | compile error | allowed natively, output kept | `div.md:190-196, 470`; `debug-log-ordering-policy.md:7-16` |

## Evidence

Reading rules. The Elm E2E hosts match `-- CHECK:` lines **unordered**: each positive pattern need only appear somewhere in the output (`eco/test/CheckPatterns.hpp:29-34`), so the order of CHECK lines is not evidence of ordering; only values that encode order (lists logged once) are. Port tests rely on the harness echo: every `echoOut` payload is sent back on `echoIn` (`ElmE2ETestBase.hpp:755-771, 931-937`; `aot_port_host.cpp:1-23`). Flags come from a `-- FLAGS:` line (`ElmE2ETestBase.hpp:944-1014`). The `elm-bugs` package is not among the suites listed in `eco/test/CMakeLists.txt:16-38`, so its tests are statements of intended behaviour, not confirmed runs. `Debug.log` writes `label: value` to the program output stream at evaluation time (`debug-log-ordering-policy.md:7-16`); wildcard `_ = Debug.log` sequences keep source order, named `let` bindings do not (`:37-53`).

| Test (path under `eco/test/`) | Shows | CHECK values |
|---|---|---|
| `elm/src/CmdBatchOrderTest.elm` | reverse batch order for Task and port managers, nested batch flattened | `tasks: [3,2,1]`; `port: [5,4,3,2,1]` |
| `elm/src/PortEchoIntTest.elm` | Int round trip incl. 32-bit and 2^53-1 limits | `0`, `-1`, `42`, `2147483647`, `-2147483648`, `9007199254740991`, `-9007199254740991`, `"done"` |
| `elm/src/PortEchoFloatTest.elm` | Float round trip | `0`, `1.5`, `-0.25`, `0.1`, `30000000000`, `-1e-7`, `123456.789` |
| `elm/src/PortEchoBoolTest.elm` | Bool | `True`, `False` |
| `elm/src/PortEchoStringTest.elm` | String incl. quotes, backslash, control chars, NUL, astral char (logged as code lists) | `[]`, `[104,101,108,108,111]`, ..., `[99,97,102,233,32,128512]`, `[110,117,108,0,105,...]` |
| `elm/src/PortEchoMaybeIntTest.elm` | Maybe as null/value | `Just 3`, `Nothing`, `Just -7` |
| `elm/src/PortEchoListIntTest.elm` | List | `[]`, `[1,2,3]`, `[1..20]` |
| `elm/src/PortEchoArrayStringTest.elm` | Array | `Array.fromList []`, `Array.fromList ["a","b","c"]` |
| `elm/src/PortEchoTuple2Test.elm`, `PortEchoTuple3Test.elm` | tuples as arrays | `(1,"one")`, `(-2,"")`; `(1,2.5,True)`, `(0,-0.5,False)` |
| `elm/src/PortEchoUnitTest.elm` | unit as null | `()` twice |
| `elm/src/PortEchoNestedTest.elm` | `List (Maybe (Int, List String))` | `[Just (1,["x","y"]),Nothing,Just (2,[])]`, `[]` |
| `elm/src/PortEchoJsonValueTest.elm` | Value passthrough | `"{\"a\":[1,true,null],\"b\":\"x\"}"`, `"\"plain\""`, `"2.5"`, `"null"` |
| `elm/src/PortAliasEchoTest.elm` | port type via alias; record round trip | `{ n = 42, s = "hi" }`, `"ok"` |
| `elm/src/PortEchoTest.elm` | basic echo | `got: 42`, `done: "ok"` |
| `elm/src/CovPort*Test.elm`, `PortEncoding*Test.elm`, `OutgoingPortTuple3Test.elm` | declarations of each payload kind compile and run (ports unused or unsubscribed) | `testValue: 1` / `testValue: 0` / `"sent"` |
| `elm/src/FlagsRecordTest.elm` | record flags; FLAGS `{"count":42,"label":"native-flags","enabled":true}` | `label: "native-flags"`, `count: 43`, `enabled: True` |
| `elm/src/TaskPerformValueTest.elm` | `Task.perform` values | `a: 42`, `b: "nullary ok"`, `c: -7`, `d: "hello"` |
| `elm/src/TaskAttemptErrorTest.elm` | `attempt` gives `Ok`/`Err` | `ok: 42`, `err: "boom"` |
| `elm/src/TaskSucceedAsArgTest.elm` | | `got: 7` |
| `elm/src/TimerEffectTest.elm` | chained `Process.sleep 100` via `perform` | `"fired 1"` .. `"fired 5"`, `"done"` |
| `elm/src/EntryMainOfRootModuleTest.elm` | root module's `main` is the entry | `which: "root"`, `greeting: "hello"` |
| `elm/src/NonEntryMainEvaluatedOnceTest.elm` | imported `main` is an ordinary CAF | `auxMain: "abab"`, CHECK-NEXT `uses: 2`, no second `auxMain` |
| `elm-core/src/TaskOnErrorCascadeTest.elm` | `onError` skips the rest of a failed chain | `recovered 1..3`, `final: 60` |
| `elm-core/src/ProcessSpawnKillHalfTest.elm` | killed sleeping processes never continue | `fired 1,3,5,7,9`, `done` |
| `elm-core/src/ProcessSpawnRecursiveTest.elm` | nested spawns | `spawned 1..5`, `bottom`, `done` |
| `elm-core/src/ProcessYieldThrashingTest.elm` | two `sleep 0` loops both finish (order not checked) | `A 1..5`, `B 1..5`, `done` |
| `elm-core/src/ProcessSleepNonFiniteTest.elm` | `1/0`, `0/0`, `1e300` sleeps wake before 2000 ms | CHECK-DAG `inf/nan/huge: woke first`, `reference woke` |
| `elm-bugs/src/CoreIssue1043PortErrorObjectObjectTest.elm` | bad incoming value: `EXIT: 1`, message names the value | `Trying to send an unexpected type of value through port \`echoIn\``, `1337`, NOT `[object Object]` |
| `elm-bugs/src/CoreIssue1110*`, `CoreIssue1141*`, `CoreIssue1154*` | subscription returned with a port command is live for its synchronous reply | `got: "hello"` |
| `elm-bugs/src/CoreIssue1123NestedCmdBatchStackOverflowTest.elm` | 100000-deep batch | `got: 1` |
| `elm-bugs/src/CoreIssue955KillProcessTwiceTest.elm` | double kill is a no-op | `killed twice: ()` |
| `eco-divergence/src/PortBytesEchoTest.elm` | Bytes port round trip (eco extension) | `sent: 4`, `got: [1,2,254,255]` |
| `eco-divergence/src/PortBytesNestedNativeTest.elm`, `FlagsBytesNativeTest.elm` | native compile errors | `-- PORT ERROR -`; `-- BAD FLAGS -`, "wants \`Bytes\` in its flags" |

## Candidate Ambiguities

### C-PLT-1: Order of commands within one `Cmd.batch`
- Construct: `Cmd.batch [c1, c2]` where both go to the same manager (Task, a port).
- Question: Does the definition fix the order in which they are performed and their messages arrive?
- Implementation (cite): Reverse order: `kjs/Platform.js:319-328` conses; eco reproduces explicitly (`kc/core/TaskEffectManager.cpp:62-68`; `rt/PortRuntime.cpp:168-172`; `CmdBatchOrderTest`).
- Notes or Elm reference behaviour: Docs say "no ordering guarantees about the results" (`core/Platform/Cmd.elm:58-61`).
- Options: (a) unspecified; (b) specify source order; (c) specify reverse order as observed.
- Affects: dynamic

### C-PLT-2: Order across effect managers in one dispatch
- Construct: `Cmd.batch [ port out, Task.perform ... ]`, and incoming vs outgoing port managers.
- Question: Is the relative order of different managers' effects defined?
- Implementation (cite): JS: object key (registration) order `kjs/Platform.js:87, 263`; eco: `std::unordered_map` order `rt/PlatformRuntime.hpp:243, 266`.
- Notes or Elm reference behaviour: elm/core #1110 and #1154 show JS outcomes depending on declaration order (`elm-bugs/src/CoreIssue1110PortDeclarationOrderTest.elm:1-12`).
- Options: (a) unspecified; (b) all subscriptions installed before any command runs; (c) a fixed manager order.
- Affects: dynamic

### C-PLT-3: Synchronous or queued delivery of an incoming port value
- Construct: host `send` on an incoming port.
- Question: Does `update` run during `send`, or later; may a send made from inside an outgoing subscriber callback observe the new subscriptions?
- Implementation (cite): JS synchronous `kjs/Platform.js:457-468`; eco queued `rt/PortRuntime.cpp:755-779`, `sched.md:174`.
- Notes or Elm reference behaviour: silent in docs; JS behaviour causes elm/core #1141, #1154.
- Options: (a) host interaction is outside the definition; (b) define delivery as an event queued after the current step.
- Affects: dynamic

### C-PLT-4: Outgoing port values sent when no host subscriber exists
- Construct: `port out : P -> Cmd msg` used before (or after) the host subscribes.
- Question: Are such values lost or kept?
- Implementation (cite): JS drops (`kjs/Platform.js:375-383`), with a `sleep 0` before the first delivery so init-time values survive the host's subscribe (`:370-372`); eco buffers until first subscriber (`rt/PortRuntime.cpp:550-566`).
- Notes or Elm reference behaviour: silent.
- Options: (a) host-defined; (b) lost; (c) buffered.
- Affects: dynamic

### C-PLT-5: Timing of outgoing port delivery
- Construct: an update returning a port command.
- Question: Is delivery to the host synchronous with the update or deferred?
- Implementation (cite): JS deferred by the port manager's `sleep 0` after each batch (`kjs/Platform.js:128-145, 370-386`); eco synchronous (`rt/PortRuntime.cpp:179-197`; `eco/docs/embedding.md:34-35`).
- Notes or Elm reference behaviour: silent.
- Options: (a) unspecified "eventually, in order per port"; (b) synchronous.
- Affects: dynamic

### C-PLT-6: Outcome of an incoming value that does not match the port type
- Construct: host sends `1337` to `port p : (String -> msg) -> Sub msg`.
- Question: Is this a program error, a host error, or ignored? Can it end the program?
- Implementation (cite): JS throws to the caller of `send`, Elm state untouched (`kjs/Platform.js:459-461`); eco returns code 2 with the same message, or aborts the process if detected on the eco thread (`rt/PortRuntime.cpp:755-779, 694-697`); `CoreIssue1043` expects `EXIT: 1`.
- Notes or Elm reference behaviour: no-runtime-errors philosophy (author direction) suggests the Elm program never sees the value.
- Options: (a) rejected at the boundary, program unaffected; (b) program terminates.
- Affects: dynamic

### C-PLT-7: Absent flags
- Construct: `Program (Maybe Int) ...` or `Program Json.Decode.Value ...` started without flags.
- Question: What value do absent flags denote?
- Implementation (cite): JS `undefined` (`kjs/Platform.js:37`), rejected by `null`/`Maybe`; eco `null` (`rt/PlatformRuntime.cpp:776-778`; `eco_embed.cpp:271-275`), so `Maybe` flags give `Nothing`.
- Notes or Elm reference behaviour: silent.
- Options: (a) absent flags are `null`; (b) absent flags are an error unless the flags type is `()`.
- Affects: dynamic

### C-PLT-8: Range of Int at the boundary
- Construct: incoming `Int` (port or flags) given `1e300`, `9223372036854775808`, or `-0`; outgoing Int above 2^53.
- Question: Which numbers are valid `Int` values at the boundary?
- Implementation (cite): JS: any finite integral double (`json-kjs:45-55`); eco: signed 64-bit (`kc/json/JsonExports.cpp:2054-2059`; `div.md:330-338`).
- Notes or Elm reference behaviour: follows from Elm's Int representation (JS double); see the numeric part of the survey.
- Options: (a) tie to the definition's Int range; (b) implementation-defined.
- Affects: dynamic, basis

### C-PLT-9: Non-JSON values at the boundary
- Construct: outgoing `Float` NaN or Infinity; incoming NaN into `Float`; `Json.Encode.Value` carrying a JS function, DOM node or `undefined`.
- Question: Is the boundary JSON (values as text) or host values?
- Implementation (cite): JS passes JS values through (`json-kjs:63-71`; `kjs/Platform.js:379`); eco is JSON text: NaN out becomes `null` (`div.md:399-402`), Node addon rejects non-serialisable sends (`eco_node_addon.cpp:425-441`).
- Notes or Elm reference behaviour: silent; the compiler builds codecs from `Json.Encode`/`Json.Decode`.
- Options: (a) define the boundary over the JSON value model; (b) over host values.
- Affects: dynamic, basis

### C-PLT-10: `Bytes` as a port or flags payload
- Construct: `port out : Bytes -> Cmd msg`, `port out : List Bytes -> Cmd msg`, `Program Bytes ...`.
- Question: Is `Bytes` a payload type of the language?
- Implementation (cite): Elm 0.19.1 rejects (`elmc/compiler/src/Canonicalize/Effects.hs:164-179`); eco accepts (`cs/Canonicalize/Effects.elm:295-296`), native only as whole port payload, never in native flags (`cs/LocalOpt/Typed/Module.elm:194-195, 650-651`).
- Notes or Elm reference behaviour: Elm 0.19.1 rejects.
- Options: (a) exclude (Standard Elm); (b) include as an eco extension in an appendix.
- Affects: static, dynamic

### C-PLT-11: Field order and error reporting for records at the boundary
- Construct: outgoing record; incoming object missing several fields.
- Question: Is the key order of an outgoing object part of the meaning; which error is reported?
- Implementation (cite): keys emitted alphabetically (`elmc/compiler/src/Optimize/Port.hs:66-75`; `cs/LocalOpt/Erased/Port.elm:111-118`); decoding runs alphabetically-last field first (`cs/LocalOpt/Erased/Port.elm:468-476`); eco's host checker walks the descriptor order (`kc/json/JsonExports.cpp:2022-2040`).
- Notes or Elm reference behaviour: silent.
- Options: (a) objects unordered, error text unspecified; (b) specify.
- Affects: dynamic

### C-PLT-12: Unit at the boundary: ports versus flags
- Construct: `port p : (() -> msg) -> Sub msg` versus `Program () model msg`.
- Question: Should `()` accept only `null` (ports) but anything (flags)?
- Implementation (cite): `elmc/compiler/src/Optimize/Port.hs:141-149, 247-250`; `cs/LocalOpt/Erased/Port.elm:245-260, 391-396`.
- Notes or Elm reference behaviour: as implemented, deliberately.
- Options: (a) record the asymmetry; (b) unify.
- Affects: dynamic

### C-PLT-13: Pre-emption and interleaving of processes
- Construct: `Process.spawn t1 |> andThen (\_ -> Process.spawn t2)`.
- Question: May a process be paused at an `andThen`, as `Process` documentation says, or only at a primitive that waits?
- Implementation (cite): Both schedulers switch only at a binding or empty receive (`kjs/Scheduler.js:151-195`; `sched.md:46-67`).
- Notes or Elm reference behaviour: doc: "we will pause it at an `andThen` and switch over" (`core/Process.elm:53-57`).
- Options: (a) definition allows switching at any `andThen` (weakest); (b) only at waits.
- Affects: dynamic

### C-PLT-14: Unhandled failure in a spawned process
- Construct: `Process.spawn (Task.fail e)`.
- Question: Is the failure observable at all?
- Implementation (cite): JS silent (`kjs/Scheduler.js:158-165`); eco stderr warning (`rt/Scheduler.cpp:993-1000`; `invariants.csv:708`).
- Notes or Elm reference behaviour: silent; failure is isolated to the process in both.
- Options: (a) the process ends, nothing else happens; (b) implementation may report.
- Affects: dynamic

### C-PLT-15: `Process.kill` of a finished or already killed process
- Construct: `Process.kill pid` twice.
- Question: No-op or error?
- Implementation (cite): JS TypeError (`kjs/Scheduler.js:105`, elm/core #955); eco no-op (`rt/Scheduler.cpp:556-566`).
- Notes or Elm reference behaviour: JS behaviour is a known bug.
- Options: (a) no-op.
- Affects: dynamic

### C-PLT-16: `Process.sleep` with zero, negative or non-finite delay
- Construct: `Process.sleep 0`, `Process.sleep -5`, `Process.sleep (0/0)`.
- Question: What does the definition say about delays other than positive finite ones?
- Implementation (cite): JS `setTimeout` rules; eco 0/negative immediate, non-finite 1 ms (`div.md:325-328`; `kc/core/ProcessExports.cpp` sanitizeDelayMs comment).
- Notes or Elm reference behaviour: doc gives only "the given number of milliseconds" (`core/Process.elm:87-90`).
- Options: (a) at least max(0, d) ms, non-finite unspecified; (b) treat as host timer semantics.
- Affects: dynamic

### C-PLT-17: Which `main` types and modules make a program
- Construct: `main` not exposed; `main` in an imported module; `main : Html msg`; `main` with parameters.
- Question: Must `main` be exposed; is a static `main` a program with no update loop; what does a non-root `main` mean?
- Implementation (cite): any top-level `main` checked regardless of exports (`elmc/compiler/src/Optimize/Module.hs:246-272`); non-root `main` is an ordinary value (`NonEntryMainEvaluatedOnceTest`); static main rendered once in JS, only evaluated natively.
- Notes or Elm reference behaviour: "I only know how to handle Html, Svg, and Programs" (`elmc/compiler/src/Reporting/Error/Main.hs:39-52`).
- Options: (a) program = root module with `main : Program f m msg` or `main : Html msg`; (b) restrict the definition to `Program`.
- Affects: static, dynamic

### C-PLT-18: Browser programs and managers absent on a platform
- Construct: `Browser.element ...` as `main` natively; `Random.generate` or `Browser.Events.onResize` on the native target.
- Question: Is it a property of the language that every `Program` runs `init`, and every effect is performed by some manager?
- Implementation (cite): eco native returns the record without running it (`kc/browser/BrowserExports.cpp:35-45`) and drops leaves with no registered manager (`rt/PlatformRuntime.cpp:471-473`; `kc/EffectManagerRegistry.cpp:13-22`).
- Notes or Elm reference behaviour: in JS every effect module is a registered manager (`elmc/compiler/src/Generate/JavaScript.hs:440-456`).
- Options: (a) define the platform as a parameter of the definition; (b) treat as non-conformance of a platform.
- Affects: dynamic, basis

### C-PLT-19: Duplicate port names and name collisions
- Construct: two modules each declaring `port send`; a port named `Task` or `Time`.
- Question: Static error, or load-time failure?
- Implementation (cite): runtime crash at registration in both (`kjs/Platform.js:335-341`; `rt/PortRuntime.cpp:449-468`; `invariants.csv:603`).
- Notes or Elm reference behaviour: no static check.
- Options: (a) state that port names are global and must be unique per program (static rule); (b) leave as runtime failure.
- Affects: static, dynamic

### C-PLT-20: Effect dispatch when an effect-manager handler waits
- Construct: a user-defined effect module whose `onEffects` returns a task that sleeps.
- Question: Must manager handlers complete without waiting?
- Implementation (cite): JS allows it (the manager process just waits) (`kjs/Platform.js:128-145`); eco requires synchronous handlers or the state update is lost (`sched.md:150-152, 215`; `invariants.csv:703`).
- Notes or Elm reference behaviour: effect modules are restricted to core packages in practice (`core/Platform.elm:17-25`).
- Options: (a) effect modules out of scope of the definition (only the managers' observable behaviour defined); (b) specify handler semantics.
- Affects: dynamic, basis

### C-PLT-21: Where the update loop's ordering guarantees stop
- Construct: messages from different sources (two timers, a task and a port).
- Question: Beyond "one message at a time; each update sees the previous model; effects of an earlier update are dispatched before a later one", what is guaranteed?
- Implementation (cite): `kjs/Platform.js:209-254` (FIFO effects queue); eco same (`rt/PlatformRuntime.cpp:318-341`); eco explicitly lists Task/Cmd/Sub/sleep ordering as possibly different (`div.md:442-447`).
- Notes or Elm reference behaviour: silent beyond the effects-queue comment.
- Options: (a) define only the serialisation guarantees; (b) define a full event order.
- Affects: dynamic
