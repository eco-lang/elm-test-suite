# Step 1: Core foundations

Part of [the plan](../lean-full-definition.md) (decisions D1, D4, D9). Conventions:
[conventions.md](conventions.md). Size: medium. Needs: nothing. Status: **done 2026-11-11** (see "Done" at the end).

## Goal

Give Chapter 6 the three things every later step builds on.

1. **D1, one evaluator with an oracle.** Replace the evaluator of `Eval.lean`, which takes one
   Boolean `ch` for every member choice of APPLY, by an evaluator that reads a sequence of Booleans,
   one per choice, and returns an outcome `value v`, `stuck` (no rule applies) or `outOfFuel`.
   Prove soundness, completeness (every derivation is found by some oracle and fuel), fuel
   monotonicity and oracle independence when no choice is read. From these, a statement "this
   phrase has no value" becomes provable: `noValue_of_stuck`.
2. **D4, the logged relations.** Beside each of the 17 relations of `Rules.lean`, a relation with
   the same rules and one more index, the log `List (String × Val)`. Prove *forget* and *lift* by
   mutual structural recursion. The evaluator computes the log, so its soundness is stated for the
   logged relations and the book's soundness follows by forget.
3. **D9's statement forms.** The extended `Expect` (lists, tuples, records, constructor values with
   arguments, characters, functions), the statements about a single value used by today's let form,
   and the statements about a log (`LogCheck`) that step 3 will use, each with a Boolean decider
   proved sound.

Then re-prove every existing generated theorem through the new evaluator, one theorem per program
`t_<project>_<Test>` instead of one per check, and the hand-stated ruling theorems; add the
constructor-correspondence check of D4 and the axioms script of the conventions.

No test is gained. What changes for the tests: 177 checks whose values `Expect` could not state
(158 data, 13 characters, 6 functions) and the 2 checks that expect no value become kernel-checked
statements, so the number of checks proved by `decide +kernel` rises from 1162 to about 1341.

## Prerequisites

- Step 0 done (the baseline numbers recorded).
- Lean 4.35.0, whose `Float` is a structure over `Float.Model` with `deriving DecidableEq`
  (`Init/Data/Float/Float.lean`, line 46 of the toolchain source), so `SVal` can derive
  `DecidableEq` and the evaluator can decide `v = val(scon)` for every constant, floats included.
- The book: `dynamic-core.tex`, Section `sec:dynamic-core-rules` (the 48 rules, lines 341 to 749),
  Section `sec:dynamic-core-basic` (APPLY and the only non-determinism of the Core, function
  equality); `appendix-dynamic-basis.tex`, Figure `fig:dynamic-basis-eq` (lines 906 to 939: Eq is
  `{True, False}` exactly when two function values meet) and Section
  `sec:appendix-dynamic-basis-debug` (lines 1122 to 1138: `APPLY(Debug.log, s, v) = {v}`,
  `APPLY(Debug.todo, s) = ∅`); `appendix-implementation.tex`, Section
  `sec:appendix-implementation-order` (lines 545 to 583: the order of evaluation within a phrase
  carries no meaning, A57, A58).

## Files

| File | Change |
|------|--------|
| `StandardElmMech/Objects.lean` | `SVal` derives `DecidableEq`; `Log`; `Val.toList?` |
| `StandardElmMech/Apply.lean` | `logEntry`; `applySet_complete`; `applySet_length_le_two` |
| `StandardElmMech/RulesL.lean` (new) | the 17 logged relations; `forget` and `lift` |
| `StandardElmMech/Eval.lean` (rewritten) | `Oracle`, `Outcome`, `Res`, the 17 evaluator functions |
| `StandardElmMech/Sound.lean` (rewritten) | soundness for the logged relations, and for the book's by forget |
| `StandardElmMech/Complete.lean` (new) | `next_ge`, monotonicity, agreement, independence, completeness, `noValue_of_stuck`, uniqueness |
| `StandardElmMech/Checks.lean` (new) | `Expect`, `Shape`, `CheckStmt`, `LetCheck`, `EntryPat`, `Rx`, `LogCheck`, deciders and soundness |
| `StandardElmMech/Theorems.lean` | `#program_theorems` replaces `#kernel_checks`; ruling theorems re-proved; `derivableOf` retired |
| `StandardElmMech/Twins.lean` (new, imports `Lean`) | `#check_twins` and its 17 uses |
| `scripts/check-axioms.lean` (new) | `#check_axioms` |
| `Main.lean` | the new evaluator, the new counts |
| `definition/tools/src/Translate.elm` | `checksFile` emits `#program_theorems` |
| `runner/mechanisation-data.js` | generated theorems are `t_*`, one per program |

Import order: `Rules` → `RulesL` → `Eval` → `Sound` → `Complete` → `Checks` (imports `Show`) →
`Basis` → `Examples` → `Theorems`. Only `Theorems.lean` and `Twins.lean` import `Lean`.

## Lean definitions

### Objects

```lean
inductive SVal where
  | int (n : Int) | float (x : Float) | char (c : Char) | str (s : String)
  deriving Repr, Inhabited, DecidableEq

/-- A log: the entries `(label, value)` of the applications of Debug.log in a derivation of a
    logged relation, in the order the logged rules fix (D4). -/
abbrev Log := List (String × Val)

/-- The elements of a list value `v1 :: ... :: vn :: []`. -/
def Val.toList? : Val → Option (List Val)
  | .con c [] => if c = conNil then some [] else none
  | .con c [h, t] => if c = conCons then (Val.toList? t).map (h :: ·) else none
  | _ => none
```

### APPLY

```lean
/-- The log entry of an application of a basic value: Debug.log adds `(s, v)`, every other
    basic value nothing. Used only by `r_d_app_basic_apply_l`. -/
def logEntry : BasVal → List Val → Log
  | .debugLog, [.sv (.str s), v] => [(s, v)]
  | _, _ => []

theorem applySet_complete {b vs v} : Apply b vs v → v ∈ applySet b vs
theorem applySet_length_le_two (b vs) : (applySet b vs).length ≤ 2
```

`applySet_complete`: `cases` on the derivation, then `simp [applySet, ...]` per constructor; the
cases that need care are those where `applySet` matches a float pattern before a general one
(`lt_cmp` with `isFloat v = false`: the first pattern of `.lt` does not match when `v` is not a
float, or matches only when both are floats, which `lt_cmp`'s `cmp v v' = some o` excludes because
`cmp` of two floats is `some`; split on `v` and `v'`). `applySet_length_le_two`: `unfold applySet;
split` and `simp` each branch (`boolSetList` and the `neq` list have at most two members).

### The oracle and the outcome (D1)

```lean
/-- An oracle: the Boolean for the i-th member choice of APPLY in an evaluation (D1). The
    evaluator reads `o k` at its k-th choice and passes `k + 1` on. -/
abbrev Oracle := Nat → Bool

def Oracle.const (b : Bool) : Oracle := fun _ => b
/-- The plan's "list of Booleans consumed one per choice": entry i, then false. -/
def Oracle.ofList (L : List Bool) : Oracle := fun i => L.getD i false

inductive Outcome (α : Type) where
  | value (a : α)
  | stuck        -- no rule applies (Debug.todo, a failed match of a lambda, an ill-typed step)
  | outOfFuel
  deriving Repr, Inhabited

/-- A result: the outcome, the log so far (on `stuck` and `outOfFuel` too: the partial log that
    run-examples reports), and the index of the next unread choice. -/
structure Res (α : Type) where
  out : Outcome α
  log : Log
  next : Nat
```

Choice made: the oracle is a function with an index threaded through the evaluator, not a list
that is consumed. Both are "one Boolean per choice"; the index form makes oracle independence a
statement about a range of indices, needs no default for an exhausted list, and gives the constant
oracles of today's theorems as `Oracle.const false` and `Oracle.const true`. `Oracle.ofList` is the
plan's list.

### The evaluator

`Eval.lean` is rewritten. One function per relation, all in one `mutual` block, structural on the
fuel (first explicit `Nat`), the oracle index `k` last:

```lean
mutual
def evAtExp        (o : Oracle) : Nat → Env → AtExp → Nat → Res Val
def evExpOpt       (o : Oracle) : Nat → Env → Option Exp → Nat → Res (Option Val)
def evExpRow       (o : Oracle) : Nat → Env → ExpRow → Nat → Res Record
def evExpRowOpt    (o : Oracle) : Nat → Env → Option ExpRow → Nat → Res Record
def evExp          (o : Oracle) : Nat → Env → Exp → Nat → Res Val
def appVal         (o : Oracle) : Nat → Val → Val → Nat → Res Val
def evMatch        (o : Oracle) : Nat → Env → Val → Match → Nat → Res VF
def evMRule        (o : Oracle) : Nat → Env → Val → MRule → Nat → Res VF
def evDec          (o : Oracle) : Nat → Env → Dec → Nat → Res ValEnv
def evValBind      (o : Oracle) : Nat → Env → ValBind → Nat → Res ValEnv
def evValBindOpt   (o : Oracle) : Nat → Env → Option ValBind → Nat → Res ValEnv
def matchAtPat     (o : Oracle) : Nat → Env → Val → AtPat → Nat → Res VEF
def matchPatOpt    (o : Oracle) : Nat → Env → Option Val → Option Pat → Nat → Res VEF
def matchPatRow    (o : Oracle) : Nat → Env → Record → PatRow → Nat → Res ValEnv
def matchPatRowOpt (o : Oracle) : Nat → Env → Record → Option PatRow → Nat → Res ValEnv
def matchPat       (o : Oracle) : Nat → Env → Val → Pat → Nat → Res VEF
def matchAtPats    (o : Oracle) : Nat → Env → List Val → List AtPat → Nat → Res VEF
end
```

Rules for writing it, each of which the proofs rely on:

- Fuel 0 gives `⟨.outOfFuel, [], k⟩`.
- Each case follows the premises of its rule in the order the rule writes them (the order of the
  table below), with an explicit `match` on each recursive result, as `Eval.lean` does today.
- A premise whose outcome is `stuck` or `outOfFuel` ends the case with that outcome, the logs so
  far concatenated, and the premise's `next`. Write the two arms explicitly
  (`| ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩` and the same for `.outOfFuel`), not through a
  helper, so that `split` sees them.
- On success the log is built in exactly the syntactic shape of the logged constructor's
  conclusion (`l1 ++ (l2 ++ l3)`, which is how Lean parses `l1 ++ l2 ++ l3`), or `solve_by_elim`
  in the soundness proof will not unify (feasibility review, F-9).
- A side condition that fails (a lookup that is `none`, a value of the wrong form) gives `stuck`.
- Every case where the old evaluator returned `none` without recursion now returns `stuck`.
- `sconTest` becomes total and decides `v = val(scon)` for every constant, floats included:

  ```lean
  def sconTest (v : Val) (sc : SCon) : Bool :=
    match valof sc, v with
    | .sv s, .sv s' => decide (s' = s)
    | _, _ => false
  ```

  so that `r:d-atpat-scon` and `r:d-atpat-scon-fail` are decided for every value, as completeness
  needs (the old `sconTest` returned `none` for float constants).

Two cases written out, as the pattern for all:

```lean
def evExp (o : Oracle) : Nat → Env → Exp → Nat → Res Val
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, e, k =>
    match e with
    | .atexp a => evAtExp o n E a k
    | .app e a =>
      match evExp o n E e k with
      | ⟨.value v1, l1, k1⟩ =>
        match evAtExp o n E a k1 with
        | ⟨.value v2, l2, k2⟩ =>
          match appVal o n v1 v2 k2 with
          | ⟨r, l3, k3⟩ => ⟨r, l1 ++ (l2 ++ l3), k3⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .lam p e => ⟨.value (.closure p e E []), [], k⟩
    | .caseE e m => ...

def appVal (o : Oracle) : Nat → Val → Val → Nat → Res Val
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, f, v, k =>
    match f with
    | .basApp b vs =>
      if vs.length + 1 < b.arity then ⟨.value (.basApp b (vs ++ [v])), [], k⟩
      else if vs.length + 1 = b.arity then
        match applySet b (vs ++ [v]) with
        | [] => ⟨.stuck, [], k⟩                                  -- Debug.todo: APPLY is empty
        | [w] => ⟨.value w, logEntry b (vs ++ [v]), k⟩            -- no choice: nothing read
        | w :: w' :: _ =>                                         -- function equality: read o k
          ⟨.value (if o k then w' else w), logEntry b (vs ++ [v]), k + 1⟩
      else ⟨.stuck, [], k⟩
    | ...
```

With `Oracle.const false` the evaluator picks the first member and with `Oracle.const true` the last,
as `ch = false` and `ch = true` do today, so every value `run-examples` prints is unchanged.

### The 17 logged relations (D4)

`RulesL.lean` copies the `mutual` block of `Rules.lean`. Each relation `R` becomes `RL` with one more
index, the log, last; each constructor `c` becomes `c_l`, with the same hypotheses in the same
order, each relation premise given its own log variable, and the conclusion's log the
concatenation of the premises' logs in the order written. Side conditions (lookups, equations,
`isRecursive`, `Apply`) carry no log.

| # | Book relation (`Rules.lean`) | Logged relation (`RulesL.lean`) |
|--:|------------------------------|---------------------------------|
| 1 | `EvalAtExp : Env → AtExp → Val → Prop` | `EvalAtExpL : Env → AtExp → Val → Log → Prop` |
| 2 | `EvalExpRow : Env → ExpRow → Record → Prop` | `EvalExpRowL : Env → ExpRow → Record → Log → Prop` |
| 3 | `EvalExp : Env → Exp → Val → Prop` | `EvalExpL : Env → Exp → Val → Log → Prop` |
| 4 | `AppVal : Val → Val → Val → Prop` | `AppValL : Val → Val → Val → Log → Prop` |
| 5 | `EvalMatch : Env → Val → Match → VF → Prop` | `EvalMatchL : Env → Val → Match → VF → Log → Prop` |
| 6 | `EvalMRule : Env → Val → MRule → VF → Prop` | `EvalMRuleL : Env → Val → MRule → VF → Log → Prop` |
| 7 | `EvalDec : Env → Dec → ValEnv → Prop` | `EvalDecL : Env → Dec → ValEnv → Log → Prop` |
| 8 | `EvalValBind : Env → ValBind → ValEnv → Prop` | `EvalValBindL : Env → ValBind → ValEnv → Log → Prop` |
| 9 | `MatchAtPat : Env → Val → AtPat → VEF → Prop` | `MatchAtPatL : Env → Val → AtPat → VEF → Log → Prop` |
| 10 | `MatchPatRow : Env → Record → PatRow → ValEnv → Prop` | `MatchPatRowL : Env → Record → PatRow → ValEnv → Log → Prop` |
| 11 | `MatchPat : Env → Val → Pat → VEF → Prop` | `MatchPatL : Env → Val → Pat → VEF → Log → Prop` |
| 12 | `EvalExpOpt : Env → Option Exp → Option Val → Prop` | `EvalExpOptL : Env → Option Exp → Option Val → Log → Prop` |
| 13 | `EvalExpRowOpt : Env → Option ExpRow → Record → Prop` | `EvalExpRowOptL : Env → Option ExpRow → Record → Log → Prop` |
| 14 | `EvalValBindOpt : Env → Option ValBind → ValEnv → Prop` | `EvalValBindOptL : Env → Option ValBind → ValEnv → Log → Prop` |
| 15 | `MatchPatOpt : Env → Option Val → Option Pat → VEF → Prop` | `MatchPatOptL : Env → Option Val → Option Pat → VEF → Log → Prop` |
| 16 | `MatchPatRowOpt : Env → Record → Option PatRow → ValEnv → Prop` | `MatchPatRowOptL : Env → Record → Option PatRow → ValEnv → Log → Prop` |
| 17 | `MatchAtPats : Env → List Val → List AtPat → VEF → Prop` | `MatchAtPatsL : Env → List Val → List AtPat → VEF → Log → Prop` |

Pattern matching evaluates no expression, so the logs of relations 9, 10, 11, 15, 16 and 17 are
always empty (lemma `matchL_log_nil`, below); they are logged relations all the same, so that the
twin check covers every relation and the generated proofs treat every premise alike.

The log of each constructor's conclusion, premises in the order the book writes them
(`dynamic-core.tex`, the rule at the line given). `l1`, `l2`, `l3` are the logs of the first, second
and third relation premises; `[]` means no relation premise.

| Rule (constructor `_l`) | Line | Relation premises in order | Conclusion's log |
|-------------------------|-----:|----------------------------|------------------|
| `r_d_atexp_scon` | 389 | none | `[]` |
| `r_d_atexp_var` | 391 | none (lookup) | `[]` |
| `r_d_atexp_con` | 393 | none (lookup) | `[]` |
| `r_d_atexp_op` | 395 | none (`OT_dyn`) | `[]` |
| `r_d_atexp_unit` | 397 | none | `[]` |
| `r_d_atexp_tuple` | 399 | exp1, exp2, [exp3] (`EvalExpOptL`) | `l1 ++ l2 ++ l3` |
| `r_d_atexp_nil` | 405 | none | `[]` |
| `r_d_atexp_record` | 407 | [exprow] (`EvalExpRowOptL`) | `l1` |
| `r_d_atexp_update` | 411 | (`E(var) = r`), exprow | `l1` |
| `r_d_atexp_paren` | 415 | exp | `l1` |
| `r_d_atexp_let` | 417 | dec, exp | `l1 ++ l2` |
| `r_d_exprow_field` | 461 | exp, [exprow] | `l1 ++ l2` |
| `r_d_exp_atexp` | 472 | atexp | `l1` |
| `r_d_exp_app` | 474 | exp, atexp, application | `l1 ++ l2 ++ l3` |
| `r_d_exp_lambda` | 478 | none | `[]` |
| `r_d_exp_case` | 482 | exp, match | `l1 ++ l2` |
| `r_d_app_closure` | 506 | atpat (`MatchAtPatL`), exp | `l1 ++ l2` |
| `r_d_app_con` | 511 | none | `[]` |
| `r_d_app_basic_partial` | 515 | none | `[]` |
| `r_d_app_basic_apply` | 519 | none (`Apply` is a side condition) | `logEntry b (vs ++ [v])` |
| `r_d_match_first` | 552 | mrule | `l1` |
| `r_d_match_fail` | 556 | mrule | `l1` |
| `r_d_match_next` | 560 | mrule, match | `l1 ++ l2` |
| `r_d_mrule_match` | 576 | pat, exp | `l1 ++ l2` |
| `r_d_mrule_fail` | 580 | pat | `l1` |
| `r_d_dec_nonrec` | 591 | valbind | `l1` |
| `r_d_dec_rec` | 595 | valbind | `l1` |
| `r_d_valbind_var` | 617 | exp, [valbind] | `l1 ++ l2` |
| `r_d_valbind_pat` | 621 | exp, atpat | `l1 ++ l2` |
| `r_d_atpat_wild`, `_scon`, `_scon_fail`, `_var`, `_con`, `_con_fail`, `_unit`, `_nil`, `_nil_fail` | 633 to 665 | none | `[]` |
| `r_d_atpat_tuple` | 655 | pat1, pat2, [pat3] | `l1 ++ l2 ++ l3` |
| `r_d_atpat_record` | 667 | [patrow] | `l1` |
| `r_d_atpat_paren` | 671 | pat | `l1` |
| `r_d_patrow_field` | 692 | [patrow] | `l1` |
| `r_d_pat_atpat` | 708 | atpat | `l1` |
| `r_d_pat_con` | 712 | atpat1 ... atpatn (`MatchAtPatsL`) | `l1` |
| `r_d_pat_con_fail`, `r_d_pat_cons_fail` | 719, 729 | none | `[]` |
| `r_d_pat_cons` | 723 | pat1, pat2 | `l1 ++ l2` |
| `r_d_pat_as` | 733 | pat | `l1` |
| `opt_none` (all five `Opt`) | | none | `[]` |
| `opt_some` (all five `Opt`) | | the phrase | `l1` |
| `seq_nil` (`MatchAtPatsL`) | | none | `[]` |
| `seq_cons` (`MatchAtPatsL`) | | atpat, the rest | `l1 ++ l2` |

Two constructors written out:

```lean
  /-- r:d-exp-app -/
  | r_d_exp_app_l (E : Env) (e : Exp) (a : AtExp) (v1 v2 v : Val) (l1 l2 l3 : Log) :
      EvalExpL E e v1 l1 → EvalAtExpL E a v2 l2 → AppValL v1 v2 v l3 →
      EvalExpL E (.app e a) v (l1 ++ l2 ++ l3)
  /-- r:d-app-basic-apply -/
  | r_d_app_basic_apply_l (b : BasVal) (vs : List Val) (v v' : Val) :
      vs.length + 1 = b.arity → Apply b (vs ++ [v]) v' →
      AppValL (.basApp b vs) v v' (logEntry b (vs ++ [v]))
```

The order "premises as written" is one linearisation the book allows: the order of evaluation
within a phrase carries no meaning (A57, A58; `appendix-implementation.tex`, lines 550 to 553). It
differs from Elm/JS's for record fields, which Elm/JS evaluates by field name (the table at lines 572
to 583): `r_d_exprow_field_l` logs the fields in the order written.

### Statements about values and logs (D9)

`Checks.lean`:

```lean
/-- The value a CHECK line states, structurally (D9). `num s` is a number whose printed form is
    `s`, Int or Float: used where the translator gives no type (a nested position in step 1). -/
inductive Expect where
  | int (n : Int)
  | flt (s : String)                      -- a Float, as `showFloat` prints it
  | num (s : String)
  | chr (c : Char)
  | str (s : String)
  | unit
  | con (name : String) (args : List Expect)   -- a complete constructor value, not [] or ::
  | list (es : List Expect)
  | tuple (es : List Expect)                   -- two or three components
  | record (fs : List (String × Expect))       -- the labels as a set
  | fn                                          -- a function value (`<function>`)

mutual
def Expect.check : Expect → Val → Bool
def Expect.checkList : List Expect → List Val → Bool
def Expect.checkFields : List (String × Expect) → Record → Bool
end

/-- Written `x.holds v`. Today's `Expect.holds` takes the value first; the arguments are swapped so
    that dot notation on the `Expect` reads as the statement. -/
def Expect.holds (x : Expect) (v : Val) : Prop := x.check v = true
```

`Expect.check` is structural on the `Expect`:

| `Expect` | holds of `v` when |
|----------|-------------------|
| `int n` | `v = .sv (.int n)` |
| `flt s` | `v = .sv (.float x)` and `showFloat x = s` |
| `num s` | `v = .sv (.int n)` and `toString n = s`, or `v = .sv (.float x)` and `showFloat x = s` |
| `chr c`, `str s`, `unit` | `v` is that character, string, `()` |
| `con k xs` | `v = .con c vs`, `c.name = k`, `vs.length = c.arity = xs.length`, componentwise |
| `list xs` | `v.toList? = some vs`, `xs.length = vs.length`, componentwise |
| `tuple [a, b]`, `tuple [a, b, c]` | `v = .tuple v1 v2 none` (or `some v3`), componentwise |
| `record fs` | `v = .record r`, `recDomEq r (fs.map ·.1)`, each `fs` field holds of `fmLookup r l` |
| `fn` | `isFun v = true` |

Characterisation lemmas, one per row (`Expect.holds_int : (Expect.int n).holds v ↔ v = .sv (.int n)`,
and so on), proved by `simp [Expect.holds, Expect.check]`, so that a reader of a theorem can
replace the Boolean by the table.

```lean
/-- The shape of a value, for parsing a CHECK line's printed value (D9). -/
inductive Shape where
  | any | int | float | char | string | unit | fn
  | list (s : Shape) | tuple (ss : List Shape) | record (fs : List (String × Shape))
  | custom (cs : List (String × List Shape))

/-- Parses Elm's printed form of a value (the `CHECK: label: value` text) at a shape: numbers at
    `int` and `float` become `int` and `flt`, at `any` `num`. Used only when generating theorem
    statements, which then show the result literally, so it is not trusted. -/
partial def Expect.parse (s : Shape) (text : String) : Option Expect
```

`Expect.parse` reads integers (with a leading `-`), floats as JavaScript prints them (`1.5`, `1e21`,
`NaN`, `Infinity`, `-Infinity`), `'c'` with the escapes `\'`, `\\`, `\n`, `\t`, `\r`, strings with
`\"`, `\\`, `\n`, `\t`, `\r`, `()`, `(a,b)`, `(a,b,c)`, `[a,b]`, `{ l = v, ... }`, `{}`,
`Con a b` with parenthesised arguments (`Just (-1)`, `Just (Just 1)`), `True`, `<function>`.

The let-form statements (today's checks, step 1 to step 2):

```lean
inductive CheckStmt where
  | value (x : Expect)
  | noValue

/-- What a check of a let-form program states. -/
def LetCheck (p : Program) (ck : Check) : CheckStmt → Prop
  | .value x => ∃ v, EvalExp p.env (p.phrase ck) v ∧ x.holds v
  | .noValue => ¬ ∃ v, EvalExp p.env (p.phrase ck) v

/-- A program's theorem: the listed checks, by index. -/
def LetChecks (p : Program) (ss : List (Nat × CheckStmt)) : Prop :=
  ∀ i s, (i, s) ∈ ss → LetCheck p (p.checks[i]!) s

def fuelT : Nat := 100000

def letCheckB (o : Oracle) (p : Program) (ck : Check) : CheckStmt → Bool
  | .value x => match evExp o fuelT p.env (p.phrase ck) 0 with
      | ⟨.value v, _, _⟩ => x.check v
      | _ => false
  | .noValue => match evExp o fuelT p.env (p.phrase ck) 0 with
      | ⟨.stuck, _, 0⟩ => true          -- stuck, and no choice read
      | _ => false

def letChecksB (p : Program) (ss : List (Nat × CheckStmt)) : Bool :=
  ss.all fun (i, s) =>
    letCheckB (.const false) p (p.checks[i]!) s || letCheckB (.const true) p (p.checks[i]!) s
```

The log statements (step 3 states every check this way; step 1 defines them and proves their
deciders sound):

```lean
/-- One CHECK pattern about one log entry. -/
inductive EntryPat where
  | entry (label : String) (x : Expect)   -- CHECK: label: value
  | label (label : String)                -- CHECK: text, with no ": " (StringEscapesTest)

def EntryPat.Holds : EntryPat → String × Val → Prop
  | .entry l x, (s, v) => s = l ∧ x.holds v
  | .label l, (s, _) => s = l

/-- Regular expressions, the subset of JavaScript's that the suite's `{{...}}` patterns use. -/
inductive Rx where
  | eps | chr (c : Char) | any                      -- `.` (not newline)
  | cls (neg : Bool) (ranges : List (Char × Char))  -- `[...]`, `[^...]`, `\d`
  | bol | eol                                        -- `^`, `$` (no multiline flag: ends of input)
  | seq (a b : Rx) | alt (a b : Rx) | star (a : Rx) | plus (a : Rx) | opt (a : Rx)

/-- Backtracking matcher with fuel; `search r s` is JavaScript's `RegExp.test`. -/
def Rx.search (r : Rx) (s : String) : Bool
partial def Rx.parse (pattern : String) : Option Rx     -- generation only

/-- The log printed as Elm/JS prints Debug.log lines (D9: used only for regex and CHECK-SAME). -/
def renderLog (l : Log) : String := String.join (l.map fun (s, v) => s ++ ": " ++ showElm v ++ "\n")

inductive LogCheck where
  | has (p : EntryPat)            -- CHECK, and CHECK-DAG read as CHECK
  | run (ps : List EntryPat)      -- a CHECK followed by CHECK-NEXT lines: consecutive entries
  | printed (r : Rx)              -- {{regex}}, or a CHECK with CHECK-SAME continuations [native]

def LogCheck.Holds (l : Log) : LogCheck → Prop
  | .has p => ∃ e ∈ l, p.Holds e
  | .run ps => ∃ pre mid post, l = pre ++ mid ++ post ∧ List.Forall₂ EntryPat.Holds ps mid
  | .printed r => r.search (renderLog l) = true

def EntryPat.check : EntryPat → String × Val → Bool
def LogCheck.check (l : Log) : LogCheck → Bool
  -- .run: some suffix of l (l.tails) begins with entries satisfying ps in order

/-- A phrase evaluates, in some derivation, with a log that meets the checks. -/
def ExpChecks (E : Env) (e : Exp) (cs : List LogCheck) : Prop :=
  ∃ v l, EvalExpL E e v l ∧ ∀ c ∈ cs, c.Holds l

def expChecksB (o : Oracle) (E : Env) (e : Exp) (cs : List LogCheck) : Bool :=
  match evExp o fuelT E e 0 with
  | ⟨.value _, l, _⟩ => cs.all (·.check l)
  | _ => false
```

A CHECK-SAME `p1` then `p2` is `.printed` of `lit p1` followed by `[^\n]*` and `lit p2`.

### The generator command

`Theorems.lean` replaces `#kernel_checks` by

```lean
/-- `#program_theorems shard` emits, for each program `g` of the list `shard`, the theorem
    `t_<project>_<Name> : LetChecks g [(i, stmt_i), ...]`, proved by
    `letChecks_sound (by decide +kernel)`, or by `native_decide` when `g.native` or
    `budgetNative.contains g.name`. -/
elab "#program_theorems " ps:ident : command
```

It reads the list's definition (`getConstInfoDefn`) and takes the constant names of its elements
(`g_elm_AccessorFunctionFieldInListTest`, ...), so that statements name the program, not
`shard[i]!`. For each check it computes the statement at elaboration time: `.noValue` if the
expected text is `(no value)`, else `.value (Expect.parse (shapeOf ck.kind) ck.expected)` with
`shapeOf .int = .int`, `.float = .float`, `.string = .string`, `.char = .char`, `.function = .fn`,
`.data = .any`, `.unknown = .any`. A check whose text does not parse is an elaboration error that
names the program and label (none is expected; the build fails until the parser is fixed). Each
theorem has the docstring `tests/<project>/src/<Name>.elm [parse] [elab] [params]`, with ` [native]`
added when proved by `native_decide`; the project is read from `p.source` (`tests/elm-core/src` gives
`elm_core` in the name). It logs
`#program_theorems Elm01: 40 theorems (37 kernel, 3 native), 112 checks`.

Example of what it emits:

```lean
/-- tests/elm/src/AccessorFunctionFieldInListTest.elm [parse] [elab] [params] -/
theorem t_elm_AccessorFunctionFieldInListTest :
    LetChecks g_elm_AccessorFunctionFieldInListTest [(0, .value (.list [.num "11", .num "20"]))] :=
  letChecks_sound (by decide +kernel)
```

`budgetNative : List String` (in `Theorems.lean`, empty at first) lists programs moved to
`native_decide` by the memory budget; each entry is recorded in the step's report.

The theorems `derivable_<Shard>` and `derivableOf` are retired: every check they covered (compared as
printed by `native_decide`) is now a conjunct of its program's `t_` theorem with a structural
statement, by the kernel unless the program is native. `kc_<Shard>_<n>` are retired (conventions,
"Names").

### The twin check

`Twins.lean` (imports `Lean`, `StandardElmMech.RulesL`):

```lean
/-- Fails unless `L` has exactly the constructors of `R`: the same number, in the same order, each
    named as `R`'s with `_l` appended, each with the same sequence of premises that are relations
    of the block (heads compared with the trailing `L` removed), and `L` having one more index. -/
elab "#check_twins " r:ident l:ident : command

#check_twins EvalAtExp EvalAtExpL
#check_twins EvalExpRow EvalExpRowL
-- ... one line for each of the 17 pairs of the table above
```

Implementation: `getConstInfoInduct` on both; for each constructor pair, `forallTelescope` over its
type, collect the heads (`Expr.getAppFn.constName?`) of the hypotheses whose head is one of the 34
relation names, and compare. This file is the "test in the build" of D4.

### The axioms script

`scripts/check-axioms.lean`:

```lean
import StandardElmMech
open Lean Elab Command

/-- Every theorem of the modules `StandardElmMech.*` depends only on `propext`,
    `Classical.choice` and `Quot.sound`, and additionally on `Lean.ofReduceBool` (and
    `Lean.trustCompiler`, if the toolchain adds it) when its docstring contains `[native]`.
    Fails, listing each offender, otherwise; `sorryAx` is never allowed. -/
elab "#check_axioms" : command => do ...

#check_axioms
```

It enumerates `(← getEnv).constants`, keeps theorems whose module (`env.getModuleIdxFor?`) has a
name starting with `StandardElmMech`, runs `Lean.collectAxioms`, reads `findDocString?`, and prints
`check-axioms: T theorems (K kernel, M native), 0 problems`. It also reports a theorem tagged
`[native]` that does not use `Lean.ofReduceBool` (a tag that overstates the trust), as a warning.

## Theorems

All in namespace `StandardElm`. The 17 forms of each mutual theorem are listed by their `EvalExp`
member; the others are the same with the relation, evaluator and arguments of the table above.

### Forget and lift (`RulesL.lean`)

```lean
theorem EvalExpL.forget {E e v l} : EvalExpL E e v l → EvalExp E e v
theorem EvalExp.lift {E e v} : EvalExp E e v → ∃ l, EvalExpL E e v l
theorem MatchPatL.log_nil {E v p r l} : MatchPatL E v p r l → l = []   -- and the 5 other pattern relations
```

Method: one `mutual` block of 17 theorems each, defined by pattern matching on the derivation
(structural recursion on the `Prop` inductive; the feasibility review compiled a three-relation
version of exactly this with Lean 4.35.0). Each case applies the twin constructor to the recursive
results. For `lift`, destructure the existential of each recursive call (`obtain ⟨l1, h1⟩ := ...`).
If elaborating 17 mutually recursive theorems is slow, split into `forget` and `lift` blocks in
separate files.

### Soundness (`Sound.lean`)

```lean
def SoundAt (o : Oracle) (n : Nat) : Prop :=
  (∀ E a k v l k', evAtExp o n E a k = ⟨.value v, l, k'⟩ → EvalAtExpL E a v l) ∧
  -- ... one conjunct per evaluator function, 17 in all, in the order of the mutual block
  (∀ E vs as k r l k', matchAtPats o n E vs as k = ⟨.value r, l, k'⟩ → MatchAtPatsL E vs as r l)

theorem soundAt (o : Oracle) : ∀ n, SoundAt o n

theorem evExp_sound_l {o n E e k v l k'} : evExp o n E e k = ⟨.value v, l, k'⟩ → EvalExpL E e v l
theorem evExp_sound {o n E e k v} : (evExp o n E e k).out = .value v → EvalExp E e v
```

Method: as `Sound.lean` today, induction on the fuel with the 17 conjuncts, and the `sound_fin`
macro adapted: `split at h` on every `match`, `simp only [Res.mk.injEq, Outcome.value.injEq,
reduceCtorEq] at *`, `subst_vars`, then `solve_by_elim` over the `_l` constructors, the induction
hypotheses and the helper lemmas (`sconTest_true : sconTest v sc = true → v = valof sc`,
`sconTest_false`, `conIs_*`, `conArgs_*`, and `pick_apply` replaced by
`applySet_mem_head : applySet b vs = w :: ws → Apply b vs w` and
`applySet_mem_second : applySet b vs = w :: w' :: ws → Apply b vs w'`, from `applySet_sound`).
`evExp_sound` is `forget ∘ evExp_sound_l`. Also `evDec_sound`, and the `_l` and plain forms of the
other 16 functions, projected from `soundAt`.

### Fuel, oracle and completeness (`Complete.lean`)

```lean
/-- The index only grows. -/
theorem evExp_next_ge (o n E e k) : k ≤ (evExp o n E e k).next

/-- Fuel monotonicity: a result other than outOfFuel does not change with more fuel. -/
theorem evExp_mono {o n m E e k} :
    (evExp o n E e k).out ≠ .outOfFuel → n ≤ m → evExp o m E e k = evExp o n E e k

/-- The evaluator reads the oracle only at the indices it consumes. -/
theorem evExp_agree {o o' n E e k} :
    (∀ i, k ≤ i → i < (evExp o n E e k).next → o i = o' i) → evExp o' n E e k = evExp o n E e k

/-- Oracle independence when no choice is consulted. -/
theorem evExp_indep {o n E e k} (h : (evExp o n E e k).next = k) (o' : Oracle) :
    evExp o' n E e k = evExp o n E e k

def Agrees (o : Oracle) (k : Nat) (L : List Bool) : Prop :=
  ∀ i (h : i < L.length), o (k + i) = L[i]

/-- Completeness for the logged relation: the evaluator finds every logged derivation, with its
    log, for every oracle that makes its choices. -/
theorem evExp_complete_l {E e v l} (h : EvalExpL E e v l) :
    ∃ (L : List Bool) (n : Nat), ∀ (o : Oracle) (k m : Nat), n ≤ m → Agrees o k L →
      evExp o m E e k = ⟨.value v, l, k + L.length⟩

/-- D1's completeness: every derivation of the book is found by some oracle and fuel. -/
theorem evExp_complete {E e v} (h : EvalExp E e v) :
    ∃ (L : List Bool) (n : Nat), (evExp (Oracle.ofList L) n E e 0).out = .value v

theorem noValue_iff {E e} :
    (¬ ∃ v, EvalExp E e v) ↔ ∀ (L : List Bool) (n : Nat) (v : Val),
      (evExp (Oracle.ofList L) n E e 0).out ≠ .value v

/-- A phrase on which the evaluator is stuck without reading a choice has no value. -/
theorem noValue_of_stuck {o n E e k l} (h : evExp o n E e k = ⟨.stuck, l, k⟩) :
    ¬ ∃ v, EvalExp E e v

/-- A value found without reading a choice is the only one, and so is its log. -/
theorem evExp_unique_l {o n E e k v l} (h : evExp o n E e k = ⟨.value v, l, k⟩) :
    ∀ v' l', EvalExpL E e v' l' → v' = v ∧ l' = l
theorem evExp_unique {o n E e k v l} (h : evExp o n E e k = ⟨.value v, l, k⟩) :
    ∀ v', EvalExp E e v' → v' = v
```

The first four are proved for all 17 functions at once, by induction on the fuel, with a
`Prop` of 17 conjuncts as `SoundAt` (`NextAt`, `MonoAt`, `AgreeAt`). In the step case, split each
`match` of the function; the IH gives each recursive call's property; for monotonicity, a recursive
call whose outcome is `outOfFuel` makes the whole result `outOfFuel`, contradicting the hypothesis,
so every recursive call satisfies the IH's premise. Prove `next_ge` first (agreement uses it to
split the index range at each premise).

Completeness: a `mutual` block of 17 theorems by pattern matching on the logged derivation, each
with the statement form

```lean
def CompleteFor {α} (run : Oracle → Nat → Nat → Res α) (a : α) (l : Log) : Prop :=
  ∃ (L : List Bool) (n : Nat), ∀ o k m, n ≤ m → Agrees o k L → run o m k = ⟨.value a, l, k + L.length⟩
-- EvalExpL.complete : EvalExpL E e v l → CompleteFor (fun o m k => evExp o m E e k) v l
```

For a rule with premises giving `(L1, n1)`, `(L2, n2)`, `(L3, n3)`: take `L := L1 ++ L2 ++ L3` and
`n := max n1 (max n2 n3) + 1`; for `m ≥ n` write `m = m' + 1` and unfold one step of the
evaluator; `Agrees o k (L1 ++ L2 ++ L3)` splits by `Agrees.append` (below) into agreement at `k`,
`k + |L1|` and `k + |L1| + |L2|`; rewrite each recursive call by its IH at fuel `m'`; the remaining
goal is the arithmetic of the indices (`omega`) and the log's shape (`rfl`). For
`r_d_app_basic_apply_l`: by `applySet_complete` and `applySet_length_le_two`, `applySet b args` is
`[v']`, giving `L = []`, or `[w, w']` with `v' = w` (`L = [false]`) or `v' = w'` (`L = [true]`).
Side conditions are decided the same way by the evaluator (lookups, `isRecursive`, `sconTest` with
`sconTest_true`/`sconTest_false` as iff lemmas, `conArgs`).

```lean
theorem Agrees.append {o k L1 L2} :
    Agrees o k (L1 ++ L2) ↔ Agrees o k L1 ∧ Agrees o (k + L1.length) L2
```

`evExp_complete` from `lift` and `evExp_complete_l` with `o := Oracle.ofList L`, `k := 0`.
`noValue_of_stuck`: suppose `EvalExp E e v`; lift and complete give `L`, `n'`; let
`o' i := if k ≤ i ∧ i < k + L.length then L[i - k]! else o i`, which agrees with `L` at `k`; at
fuel `max n n'` completeness gives `value`; by `evExp_indep` (from `h`, `next = k`) and
`evExp_mono` (`stuck ≠ outOfFuel`), `evExp o' (max n n') E e k = ⟨.stuck, l, k⟩`: contradiction.
`evExp_unique_l` is the same argument, which also forces `L = []` and the logs equal.

The same seven statements are stated for `appVal`, `evDec` and `evValBind`, which step 2 uses.

### Deciders

```lean
theorem Expect.check_sound_iff {x v} : x.check v = true ↔ x.holds v        -- by definition
theorem letChecks_sound {p ss} : letChecksB p ss = true → LetChecks p ss
theorem EntryPat.check_sound {p e} : p.check e = true → p.Holds e
theorem LogCheck.check_sound {c l} : c.check l = true → c.Holds l
theorem expChecks_sound {o E e cs} : expChecksB o E e cs = true → ExpChecks E e cs
```

`letChecks_sound`: `List.all_eq_true`, then for `.value` `evExp_sound` and `check`, for `.noValue`
`noValue_of_stuck`. `LogCheck.check_sound` for `.run` needs a lemma that a matching suffix gives the
decomposition `pre ++ mid ++ post` (induction on `l`).

### The ruling theorems, re-proved

The theorems of `Theorems.lean` keep their names and statements, with `Expect.con "True"` written
`Expect.con "True" []`, and are proved through the new evaluator: `kcheck_sound (ch := false)`
becomes `valueCheck_sound (o := .const false)`, where

```lean
def valueCheckB (o : Oracle) (E : Env) (e : Exp) (x : Expect) : Bool :=
  match evExp o fuelT E e 0 with | ⟨.value v, _, _⟩ => x.check v | _ => false
theorem valueCheck_sound {o E e x} : valueCheckB o E e x = true → ∃ v, EvalExp E e v ∧ x.holds v
```

and `checkShowWith_sound` likewise over `evExp`. Two theorems are added, which D1 makes possible:

```lean
/-- A43: 1 ^ -1 has the value 1 and no other: the evaluator reads no choice. -/
theorem a43_one_unique : ∀ w, EvalExp E0 (bin "^" (i 1) (i (-1))) w → w = .int 1

/-- A51: the two values of `(\x -> x) == (\x -> x)` are found by the two oracles, and the
    evaluator reads exactly one choice. -/
theorem a51_one_choice :
    let eqLam := eq (.atexp (.paren (lams [pv "x"] (v "x")))) (.atexp (.paren (lams [pv "x"] (v "x"))))
    (evExp (.const false) fuelT E0 eqLam 0).next = 1 ∧ (evExp (.const true) fuelT E0 eqLam 0).next = 1
```

`a43_one_unique` from `evExp_unique` and `decide +kernel` on the evaluator's result (`next = 0`).
A demonstration of the logged relation, used by the README's explanation of D4:

```lean
/-- D4: `Debug.log "a" 1 + Debug.log "b" 2` logs a then b in the logged relation's order, one of
    the orders the book allows (A58). -/
theorem log_order_demo :
    ExpChecks E0 (bin "+" (debugLog "a" (i 1)) (debugLog "b" (i 2)))
      [.run [.entry "a" (.int 1), .entry "b" (.int 2)]] :=
  expChecks_sound (o := .const false) (by decide +kernel)
```

## Translator changes

Only the text of the theorem file per shard. In `definition/tools/src/Translate.elm`,
`checksFile shard` becomes

```elm
checksFile shard =
    header
        ++ "import StandardElmMech.Generated." ++ shard.name
        ++ "\nimport StandardElmMech.Theorems\n\nnamespace StandardElm\nopen StandardElm.D\n\n#program_theorems shard_"
        ++ shard.name
        ++ "\n\nend StandardElm\n"
```

No other generated file changes: the programs (`Generated/<Shard>.lean`) are untouched, so
`lake exe dump-phrases` prints the same phrases as before (a check that the step changed no
translation).

## Main.lean (run-examples)

- Evaluate each check with `evExp (.const false) fuel p.env (p.phrase ck) 0` and with
  `.const true`; print `showElm v` for `.value v`, `(no value)` for `.stuck`, `(out of fuel)` for
  `.outOfFuel`. A check expecting `(no value)` agrees only with `(no value)`.
- `theorem` of a row is the program's `t_<project>_<Name>`; a new field `proof` is `"kernel"` or
  `"native"`; `skipped` is `null`, or `"unparsed"` for a check the generator could not state (none
  expected).
- The summary line becomes
  `Total: N checks, A agree, D diverge (X known); K checks by decide +kernel, M by native_decide, in T program theorems.`
  and `example-run.json`'s `total` gains `kernelChecks`, `nativeChecks` and `programTheorems`
  (`theorems` is kept, equal to `kernelChecks`, for the site until it is updated).

## Site and reports

- `runner/mechanisation-data.js`: the generated theorems are the `t_*` theorems of the
  `Checks*.lean` files; `proofs/kc.json` becomes `proofs/generated.json`, one entry per program
  theorem with its checks; a test page links each check to its program's theorem; the count line
  says "N program theorems (K checks kernel, M native)". The rule-link pattern is unchanged in this
  step (`r_d_` only; the `_l` constructors are not linked).
- README ("What the theorems say"): replace the `kc_` and `derivable_` paragraphs by the `t_`
  theorems, with the trust tags `[parse] [elab] [params]` and `[native]`; replace the closing
  paragraph "Soundness only ..." by the completeness, uniqueness and `noValue_of_stuck` theorems;
  add the D4 paragraph (logged relations, forget and lift, the order of the log). Files table: rows
  for `RulesL.lean`, `Complete.lean`, `Checks.lean`, `Twins.lean`, `scripts/check-axioms.lean`.
- `mechanisation-report.md`: an "Update" block with the new counts.

## Tests gained

None. Checks newly proved by `decide +kernel`: the 158 `data`, 13 `char` and 6 `function` checks
marked `skipped: "value"` in today's `example-run.json`, and the 2 checks expecting no value
(StandardLetStrictTest `let strict`, StandardApplicationStrictTest `app strict`), whose statement is
now `.noValue`.

## Acceptance

The commands of [conventions.md](conventions.md), plus `lake exe dump-phrases` (output identical to
before the step). Expected:

- `lake build`: no `sorry`, no new warning; `Twins.lean` elaborates (17 pairs agree); each
  `Checks<Shard>.lean` logs its `#program_theorems` line.
- `lake env lean scripts/check-axioms.lean` prints `check-axioms: T theorems (...), 0 problems`.
- `lake exe run-examples` prints
  `Total: 1487 checks, 1487 agree, 0 diverge (0 known); K checks by decide +kernel, M by native_decide, in 491 program theorems.`
  with `K ≥ 1162` and target `K = 1341`, `M = 146` (the checks of programs marked `native`), less
  any moved to `budgetNative`, which then appear in `M` and in the report. Every `(program, label)`
  row of `example-run.json` has the same `definition` values as before the step.
- Translator: unit tests pass; `--check` reports up to date after regenerating (only the 13
  `Checks*.lean` files change).
- Memory budget (the step 0 script): no `lean` process above 6.5 GB, summed PSS under 12 GB.
  The program to watch is AppendTypeSplitTest (6.02 GB alone today, one check): if its theorem
  breaks 6.5 GB through the new evaluator, add it to `budgetNative` and record it.
- Site rebuilt, link audit 0 problems; README, report, preface sentence (counts unchanged:
  491 programs) and the plan's status line updated.

## Risks and fallbacks

- **Kernel cost of the logged evaluator.** Every result now carries a log and an index. Most logs
  are `[]` and `[] ++ l` reduces in one step, so the cost should be small, but it is unmeasured.
  Fallback, if the budget or the build time (today about a minute and a half) grows by more than a
  third: add an unlogged evaluator `evExpV` with the same structure and a theorem
  `(evExp o n E e k).out = (evExpV o n E e k).out ∧ (evExp o n E e k).next = (evExpV ...).next`
  by fuel induction, and generate the let-form theorems through `evExpV`.
- **Mutual structural recursion over 17 inductive predicates** (forget, lift, completeness) may be
  slow to elaborate. Fallback: prove each by `EvalExpL.rec` with explicit motives (one
  `theorem` per motive set), or split each mutual block across files.
- **`sound_fin` and the new match arms.** The two failure arms per premise triple the number of
  goals after `split`; most close by `simp` (`reduceCtorEq`, since `.stuck ≠ .value _`). If
  `solve_by_elim` gets slow, raise `maxDepth` only for the cases that need it.
- **Float equality in `sconTest`.** `decide (s' = s)` on `SVal` reduces through `Float.Model`'s
  derived `DecidableEq`. No test has a float pattern (the syntactic restrictions forbid them), so
  this only matters for completeness, not for the generated theorems.
- **`Expect.parse` against `showElm`.** `showStr` escapes only `"` and `\`; Elm/JS also escapes
  newlines in `Debug.toString`. A check whose string contains a newline would then parse to a
  string that the value does not equal. None of today's 1487 checks has one (they all agree as
  printed); the generator fails loudly if one appears.

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

- **The count "K" cannot be a count of theorems once theorems are per program.** The plan's
  acceptance ("the number of checks and of kernel theorems not lower than before the step") and
  the conventions' summary line (`K theorems by decide +kernel`) assume one theorem per check; the
  conventions' "Names" make generated theorems one per program from this step. Read literally, K
  falls from 1162 to about 450 in step 1. This specification counts K as the number of checks
  proved by `decide +kernel` (conjuncts of the `t_` theorems) and changes the summary line
  accordingly; the plan's acceptance paragraph and conventions.md's acceptance section should say
  "checks proved by `decide +kernel`".
- **The plan's "list of Booleans".** D1's oracle is implemented as `Nat → Bool` with an index;
  `Oracle.ofList` is the list. This is a representation, not a change of meaning; recorded so that
  the plan's wording is not read as requiring a consumed list.
- **D9 does not say what an unlabelled CHECK line states.** StringEscapesTest's `CHECK: newline` has
  no `: `. This specification states it as `EntryPat.label "newline"` (an entry with that label),
  stronger than the runner's substring search and true of the program. D9 should list the case.
- **CHECK-NEXT and lines.** D9 states CHECK-NEXT as adjacency of log entries; the runner reads it
  as adjacency of output lines. They coincide unless a logged value prints with a newline, which
  `showElm` never produces (it does not escape newlines inside strings, see the risk above, and no
  test logs such a string). Worth a sentence in D9.
- **`derivable_<Shard>` is retired, not re-proved.** The plan says the existing `#kernel_checks`
  theorems are re-proved; it does not mention the 13 shard theorems proved by `native_decide`.
  They are subsumed by the per-program theorems (same checks, stronger structural statements), so
  this specification retires them; the native-theorem count of the report changes meaning
  accordingly (programs proved natively instead of shards).

## Done (2026-11-11)

Implemented, with these differences from the specification:

- **Proof route for D1.** Instead of fuel monotonicity, agreement and oracle independence proved by
  fuel induction (`evExp_mono`, `evExp_agree`, `evExp_indep`), one theorem by induction on the
  derivation does the work: `nostuck` (NoStuck.lean): for a derivation with value v and log l, the
  evaluator at any oracle, fuel and index runs out of fuel, reads a choice, or gives exactly v and
  l. `noValue_of_stuck`, `evExp_unique` and `evExp_unique_l` follow at once. Completeness
  (Completeness.lean) is stated with "for every fuel m >= n" built in, so it needs no separate
  monotonicity. Only `next_ge` (Complete.lean) is proved by fuel induction. The three lemmas the
  specification names are not needed and were not written.
- **Generated proofs.** `forget`/`lift`, `nostuck` and `complete` are one case per constructor (60
  each); they are generated from RulesL.lean by `scripts/gen_forget.py`, `scripts/gen_nostuck.py`
  and `scripts/gen_complete.py`, and checked by the build. Two small tactics (Tactics.lean,
  `apply_to_eqs`, `split_ors`) close the cases.
- **Logs are left-nested.** Lean's `++` is `infixl`, so `l1 ++ l2 ++ l3` is `(l1 ++ l2) ++ l3`; the
  evaluator builds exactly the logged constructors' expression.
- **`#program_theorems g1 g2 ...` takes the program names.** A long list literal is not elaborated
  as a chain of `List.cons`, so the shard list cannot be read back; the translator writes the names.
- **Memory.** Through the logged evaluator AppendTypeSplitTest needs 14.7 GB and DeepEqualityTest
  9.4 GB in the kernel; both are in `budgetNative`, so their 19 checks are native. Kernel checks:
  1,322 (target 1,341 less those 19); native: 165. Largest process 3.3 GB, all together 7.8 GB.
- **`Expect.parse`.** A constructor argument printed without parentheses is atomic (`W 1 True 2`),
  as `showElm` prints it.
- **The axioms script** recognises `native_decide`'s axioms in Lean 4.35, one per theorem named
  `<theorem>._native.native_decide.ax_...`, and the seven native ruling theorems are tagged
  `[native]`.

Results: `lake build` with no warning; `#check_twins` agrees for the 17 pairs; `check-axioms`:
1,251 theorems, 77 native, 0 problems; `run-examples`: `Total: 1487 checks, 1487 agree, 0 diverge
(0 known); 1322 checks by decide +kernel, 165 by native_decide, in 491 program theorems.`, every
`(program, label)` value as before; translator tests 67 pass, `--check` up to date; site built,
link audit 0 problems.
