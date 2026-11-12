/-
  A Standard Definition of Elm? Mechanisation, part 11.
  Machine-checked statements that the definition derives the examples' values.

  * `t_<project>_<Test>`: one theorem per translated test program, in module form (plan step 3):
    the program's modules, evaluated by Chapter 7's rules in the test basis `Btest []`, have a
    derivation whose log meets every check (`ViewChecks`, Mod/Program.lean), or, for a test that
    stops at Debug.todo, no meaning (`NoMeaning`). Proved by `decide +kernel` on the decider (the
    kernel itself runs the evaluator), or by `native_decide` for a program that uses a value only
    the C library computes (`Program.native`) or that the memory budget moves (`budgetNative`);
    such a theorem is tagged `[native]`. The command `#mod_program_theorems` below generates them;
    each shard of the translated tests runs it in its own file (Generated/Checks<Shard>.lean).
  * Hand-stated theorems for the rulings A42, A43, A44, A48, A49 and A51, and theorems that D1 (the
    oracle evaluator and `nostuck`) makes possible: a value that is the only one, and a phrase with
    exactly one choice.
-/
import Lean
import StandardElmMech.Checks
import StandardElmMech.Mod.Program

namespace StandardElm
open StandardElm.D

/-! ## The values of Basics written in Elm (sec:appendix-dynamic-basis-elm) -/

/-- A text `var atpat1 ... atpatn = exp`, not recursive, evaluates in E by
    r:d-dec-nonrec (with r:d-valbind-var and r:d-exp-lambda) to the closure
    that InitialBasis.lean binds. -/
theorem elmText_derivation (E : Env) (x : Var) (p : AtPat) (ps : List AtPat) (e : Exp)
    (h : isRecursive [(x, .closure p (lams ps e) E [])] (.var x (lams (p :: ps) e) none) = false) :
    EvalDec E (.val (.var x (lams (p :: ps) e) none)) [(x, .closure p (lams ps e) E [])] := by
  have hv : EvalValBind E (.var x (lams (p :: ps) e) none) (fmPlus [(x, .closure p (lams ps e) E [])] []) :=
    EvalValBind.r_d_valbind_var _ _ _ _ _ _ (EvalExp.r_d_exp_lambda E p (lams ps e)) (EvalValBindOpt.opt_none _)
  have he : fmPlus [(x, Val.closure p (lams ps e) E [])] ([] : ValEnv) = [(x, .closure p (lams ps e) E [])] := by
    simp [fmPlus]
  rw [he] at hv
  exact EvalDec.r_d_dec_nonrec _ _ _ hv h

def elmTextNonRec : Def → Bool
  | .fn x (p :: ps) e => !isRecursive [(x, .closure p (lams ps e) E_K [])] (.var x (lams (p :: ps) e) none)
  | _ => false

theorem elmTexts_nonrec : elmTexts.all elmTextNonRec = true := by decide +kernel

/-- Every text of the fragment evaluates in E_K to the value VE_elm binds. -/
theorem elmTexts_eval : ∀ x p ps e, Def.fn x (p :: ps) e ∈ elmTexts →
    EvalDec E_K (.val (.var x (lams (p :: ps) e) none)) [(x, .closure p (lams ps e) E_K [])] := by
  intro x p ps e hm
  apply elmText_derivation
  have := List.all_eq_true.mp elmTexts_nonrec _ hm
  simpa [elmTextNonRec] using this

/-- The text of `never` (recursive) evaluates in E_K, by r:d-dec-rec, to Rec of its closure. -/
theorem never_eval :
    EvalDec E_K (.val (.var "never" (lams [neverPat] neverBody) none))
      (recVE [("never", .closure neverPat neverBody E_K [])]) := by
  have hv : EvalValBind E_K (.var "never" (lams [neverPat] neverBody) none)
      (fmPlus [("never", .closure neverPat neverBody E_K [])] []) :=
    EvalValBind.r_d_valbind_var _ _ _ _ _ _ (EvalExp.r_d_exp_lambda _ _ _) (EvalValBindOpt.opt_none _)
  have he : fmPlus [("never", Val.closure neverPat neverBody E_K [])] ([] : ValEnv) =
      [("never", .closure neverPat neverBody E_K [])] := by simp [fmPlus]
  rw [he] at hv
  exact EvalDec.r_d_dec_rec _ _ _ hv (by decide +kernel)

/-- ME0 binds `never` to that value. -/
theorem never_value : (recVE [("never", .closure neverPat neverBody E_K [])]) = [("never", neverValue)] := rfl

/-! ## The generated theorems -/

/-- Programs whose theorem is moved to `native_decide` by the memory budget
    (plans/lean-full-definition/conventions.md). -/
def budgetNative : List String :=
  [ -- 14.7 GB in the kernel alone (it builds and compares strings of 2^16 characters); 6.0 GB with
    -- the evaluator before plan step 1 (2026-11-11)
    "AppendTypeSplitTest",
    -- 9.4 GB in the kernel alone (deep structural equality of large values)
    "DeepEqualityTest" ]

def Shape.ofKind : CheckKind → Shape
  | .int => .int | .float => .float | .string => .string | .char => .char
  | .function => .fn | .data => .any | .unknown => .any

/-- The Lean name of the project of a program, from its source folder. -/
def Program.project (p : Program) : String :=
  match p.source.splitOn "/" with
  | "tests" :: proj :: _ => proj.replace "-" "_"
  | _ => "hand"

partial def Expect.toLean : Expect → String
  | .int n => s!"(.int ({n}))"
  | .flt s => s!"(.flt {repr s})"
  | .num s => s!"(.num {repr s})"
  | .chr c => s!"(.chr {repr c})"
  | .str s => s!"(.str {repr s})"
  | .unit => ".unit"
  | .con k xs => s!"(.con {repr k} [{", ".intercalate (xs.map Expect.toLean)}])"
  | .list xs => s!"(.list [{", ".intercalate (xs.map Expect.toLean)}])"
  | .tuple xs => s!"(.tuple [{", ".intercalate (xs.map Expect.toLean)}])"
  | .record fs => s!"(.record [{", ".intercalate (fs.map fun (l, x) => s!"({repr l}, {Expect.toLean x})")}])"
  | .fn => ".fn"

/-! ## The generated theorems in module form (plan step 3) -/

/-- The entry pattern of a line without a regular expression: its label alone, or its label and
    the value its text states, read at the kind the translator inferred. -/
def Check.entryPat? (ck : Check) : Option EntryPat :=
  if ck.isRegex then none
  else if ck.labelOnly then some (.label ck.text)
  else (Expect.parse (Shape.ofKind ck.kind) ck.expected).map (.entry ck.label)

/-- The regular expression of a line's pattern as JavaScript reads it (runner/directives.js,
    `patternRegex`): the text outside `{{...}}` literally, the text inside as written. -/
def Check.regexSource (ck : Check) : String := Id.run do
  let lit (t : String) : String :=
    String.join (t.toList.map fun c => if ".^$|?*+()[]{}\\".toList.contains c then "\\" ++ c.toString else c.toString)
  let parts := ck.text.splitOn "{{"
  let mut out := lit (parts.headD "")
  for part in parts.drop 1 do
    match part.splitOn "}}" with
    | inner :: rest@(_ :: _) => out := out ++ inner ++ lit ("}}".intercalate rest)
    | _ => out := out ++ lit ("{{" ++ part)
  return out

/-- The log statements of a test's CHECK lines (D9), in order. A CHECK with its CHECK-NEXT lines is
    a run of consecutive entries; one with a CHECK-SAME line or a regular expression is a statement
    about the printed log; a CHECK-NOT is not stated here (the program has no meaning, or step 6
    states it). `none` when a value cannot be read. -/
partial def toLogChecks (lines : List Check) : Option (List LogCheck) :=
  go (lines.filter (·.line != .not_))
where
  go : List Check → Option (List LogCheck)
    | [] => some []
    | first :: rest =>
      let conts := rest.takeWhile fun c => c.line == .next || c.line == .same
      let after := rest.drop conts.length
      let group := first :: conts
      let printed := group.any fun c => c.isRegex || c.line == .same
      let stmt : Option LogCheck :=
        if printed then
          let src := group.foldl (fun acc c =>
            if acc.isEmpty then c.regexSource
            else if c.line == .same then acc ++ "[^\n]*" ++ c.regexSource
            else acc ++ "[^\n]*\n[^\n]*" ++ c.regexSource) ""
          (Rx.parse src).map .printed
        else if conts.isEmpty then first.entryPat?.map .has
        else (group.mapM Check.entryPat?).map .run
      match stmt, go after with
      | some s, some ss => some (s :: ss)
      | _, _ => none

/-- Whether a program has a statement about its printed log, decided by `native_decide` (D9). -/
def Program.hasPrinted (p : Program) : Bool :=
  p.checks.any fun c => c.line != .not_ && (c.isRegex || c.line == .same)

/-- Whether a program's theorem is proved by `native_decide`. -/
def Program.proofNative (p : Program) : Bool :=
  p.native || p.hasPrinted || budgetNative.contains p.name

def EntryPat.toLean : EntryPat → String
  | .entry l x => s!"(.entry {repr l} {x.toLean})"
  | .label l => s!"(.label {repr l})"

def LogCheck.toLean : LogCheck → String
  | .has e => s!".has {e.toLean}"
  | .run ps => s!".run [{", ".intercalate (ps.map EntryPat.toLean)}]"
  | .printed r => s!".printed ({(repr r).pretty 100000})"

open Lean Elab Command in
/-- `#mod_program_theorems g1 g2 ...` emits, for each test program `g`, in module form (its modules
    `g.modules`, evaluated by r:p-dyn-module and r:p-dyn-main in the test basis `Btest []`):
    * `t_<project>_<Name> : NoMeaning (Btest []) g.modules` when the test expects the program to
      stop (EXIT 1 with CHECK-NOT lines: it stops at Debug.todo), by `noMeaning_sound`;
    * otherwise `t_<project>_<Name> : ViewChecks (Btest []) g.modules [checks]`, by
      `viewChecks_sound` with the constant oracle that meets every check;
    by `decide +kernel`, or `native_decide` when `g.proofNative`. -/
elab "#mod_program_theorems " gs:ident* : command => do
  let mut kernel : Nat := 0
  let mut native : Nat := 0
  let mut checks : Nat := 0
  for gi in gs do
    let g ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo gi
    let p ← liftTermElabM <| unsafe Meta.evalExpr Program (mkConst ``StandardElm.Program) (mkConst g)
    checks := checks + p.checks.length
    let nat := p.proofNative
    let tac := if nat then "native_decide" else "decide +kernel"
    if nat then native := native + 1 else kernel := kernel + 1
    let tag := if nat then " [native]" else ""
    -- the kernel's reduction of a program that logs many values nests deeper than the default
    -- limit (512); 1024 suffices for every test (2026-11-11)
    let doc := s!"set_option maxRecDepth 2048 in\n/-- {p.source}/{p.name}.elm [parse] [elab] [harness] [params]{tag} -/\n"
    let stx ←
      if !p.meaning then
        pure s!"{doc}theorem t_{p.project}_{p.name} : Mod.NoMeaning (Mod.Btest []) {g}.modules :=\n  Mod.noMeaning_sound (by {tac})"
      else
        match toLogChecks p.checks with
        | none => throwError "#mod_program_theorems: {p.name}: a check whose value cannot be stated"
        | some cs =>
          let csL := ", ".intercalate (cs.map LogCheck.toLean)
          let ok (b : Bool) : Bool := Mod.viewChecksB (.const b) (Mod.Btest []) p.modules cs
          let orc := if ok false then "false" else if ok true then "true" else "none"
          if orc == "none" then throwError "#mod_program_theorems: {p.name}: neither constant oracle meets the checks"
          pure s!"{doc}theorem t_{p.project}_{p.name} : Mod.ViewChecks (Mod.Btest []) {g}.modules [{csL}] :=\n  Mod.viewChecks_sound (o := .const {orc}) (by {tac})"
    match Parser.runParserCategory (← getEnv) `command stx with
    | .ok cmd => elabCommand cmd
    | .error err => throwError "#mod_program_theorems: {p.name}: {err}"
  let total := kernel + native
  logInfo m!"#mod_program_theorems: {total} theorems ({kernel} kernel, {native} native), {checks} checks"

/-! ## Statements that the oracle evaluator makes possible (D1) -/

/-- A43: 1 ^ -1 has the value 1 and no other: the evaluator reads no choice, so by `nostuck` every
    derivation gives it. -/
theorem a43_one_unique :
    (∃ v, EvalExp E0 (bin "^" (i 1) (i (-1))) v) ∧ ∀ w, EvalExp E0 (bin "^" (i 1) (i (-1))) w → (Expect.int 1).holds w :=
  uniqueValue_sound (o := .const false) (by decide +kernel)

/-- A51: `(\x -> x) == (\x -> x)` reads exactly one choice of the oracle, whichever it is. -/
theorem a51_one_choice :
    (evExp (.const false) fuelT E0 (eq (.atexp (.paren (lams [pv "x"] (v "x")))) (.atexp (.paren (lams [pv "x"] (v "x"))))) 0).next = 1 ∧
    (evExp (.const true) fuelT E0 (eq (.atexp (.paren (lams [pv "x"] (v "x")))) (.atexp (.paren (lams [pv "x"] (v "x"))))) 0).next = 1 := by
  decide +kernel

/-- D4: `Debug.log "a" 1 + Debug.log "b" 2` logs a then b in the logged relation's order, one of
    the orders the book allows (A58). -/
theorem log_order_demo :
    ExpChecks E0 (bin "+" (debugLog "a" (i 1)) (debugLog "b" (i 2)))
      [.run [.entry "a" (.int 1), .entry "b" (.int 2)]] :=
  expChecks_sound (o := .const false) (by decide +kernel)

/-! ## The rulings, stated directly (kernel-checked) -/

/-- A43: 1 ^ -1 is 1 (eco: 0). -/
theorem a43_one : ∃ w, EvalExp E0 (bin "^" (i 1) (i (-1))) w ∧ (Expect.int 1).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)

/-- A43: (-1) ^ -3 is -1 (eco: 0). -/
theorem a43_minus_one_odd :
    ∃ w, EvalExp E0 (bin "^" (.atexp (.paren (i (-1)))) (i (-3))) w ∧ (Expect.int (-1)).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)

/-- A43: (-1) ^ -2 is 1 (eco: 0). -/
theorem a43_minus_one_even :
    ∃ w, EvalExp E0 (bin "^" (.atexp (.paren (i (-1)))) (i (-2))) w ∧ (Expect.int 1).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)

/-- A43: APPLY(pow, 1, -1) = {1}: the set has one member, so the definition
    gives no other value for 1 ^ -1 at this step. -/
theorem a43_apply_singleton : applySet .pow [.int 1, .int (-1)] = [.int 1] := by
  simp [applySet, BasVal.isEffect, BasVal.isNew, applySetCore]

/-- A42: 3 // 0, modBy 0 3 and remainderBy 0 3 are all 0. -/
theorem a42_idiv : ∃ w, EvalExp E0 (bin "//" (i 3) (i 0)) w ∧ (Expect.int 0).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)
theorem a42_modBy : ∃ w, EvalExp E0 (ap (v "modBy") [i 0, i 3]) w ∧ (Expect.int 0).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)
theorem a42_remainderBy : ∃ w, EvalExp E0 (ap (v "remainderBy") [i 0, i 3]) w ∧ (Expect.int 0).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)

/-- A48: at floats APPLY(max) and APPLY(min) are IEEE 754-2019 maximum and
    minimum, whatever the order of the arguments: NaN when either is NaN,
    +0 for max and -0 for min of the two zeros. Floats are compared as
    printed, so this is proved by `native_decide`. [native] -/
theorem a48_float :
    let f (x : Float) : Val := .sv (.float x)
    let nan : Float := 0 / 0
    let nz : Float := -0
    ([applySet .max [f nan, f 1], applySet .max [f 1, f nan],
      applySet .min [f nan, f 1], applySet .min [f 1, f nan],
      applySet .max [f 0, f nz], applySet .max [f nz, f 0],
      applySet .min [f 0, f nz], applySet .min [f nz, f 0]].map (·.map showElmSigned))
      = [["NaN"], ["NaN"], ["NaN"], ["NaN"], ["+0"], ["+0"], ["-0"], ["-0"]] := by
  native_decide

/-- A48: at Int, max and min give the elm/core text's result
    (kernel-checked). -/
theorem a48_int_max : ∃ w, EvalExp E0 (ap (v "max") [i 3, i 10]) w ∧ (Expect.int 10).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)
theorem a48_int_min : ∃ w, EvalExp E0 (ap (v "min") [i 3, i 10]) w ∧ (Expect.int 3).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)

/-- A49: at floats APPLY(clamp, lo, hi, x) is min (max x lo) hi with the
    IEEE 754-2019 minimum and maximum: hi when lo > hi, NaN when any argument
    is NaN, +0 for clamp 0 1 -0. Floats are compared as printed, so this is
    proved by `native_decide`. [native] -/
theorem a49_apply_float :
    let f (x : Float) : Val := .sv (.float x)
    let nan : Float := 0 / 0
    let nz : Float := -0
    ([applySet .clamp [f 10, f 0, f 5], applySet .clamp [f nan, f 1, f 0.5],
      applySet .clamp [f 0, f nan, f 0.5], applySet .clamp [f 0, f 1, f nan],
      applySet .clamp [f 0, f 1, f nz], applySet .clamp [f (-1), f nz, f 0],
      applySet .clamp [f 0, f 1, f 0.5]].map (·.map showElmSigned))
      = [["+0"], ["NaN"], ["NaN"], ["NaN"], ["+0"], ["-0"], ["0.5"]] := by
  native_decide

/-- A49 through the rules: `clamp 10 0 5` at Float evaluates to +0 (hi),
    by r:d-app-basic-partial and r:d-app-basic-apply with APPLY(clamp). [native] -/
theorem a49_float_lo_gt_hi :
    ∃ w, EvalExp E0 (ap (v "clamp") [fI 10, fI 0, fI 5]) w ∧ showElmSigned w = "+0" :=
  checkShowWith_sound (o := .const false) (by native_decide)

/-- A49: `clamp nan 1 0.5` at Float evaluates to NaN. [native] -/
theorem a49_float_nan_bound :
    ∃ w, EvalExp E0 (ap (v "clamp") [.atexp (.paren (bin "/" (fI 0) (fI 0))), fI 1, fHalf]) w ∧
      showElm w = "NaN" :=
  checkShowWith_sound (shw := showElm) (o := .const false) (by native_decide)

/-- A49: `clamp 0 1 -0` at Float evaluates to +0. [native] -/
theorem a49_float_signed_zero :
    ∃ w, EvalExp E0 (ap (v "clamp") [fI 0, fI 1, .atexp (neg (.scon (.intF 0)))]) w ∧
      showElmSigned w = "+0" :=
  checkShowWith_sound (o := .const false) (by native_decide)

/-- A49: at Int, clamp gives the elm/core text's result: `clamp 10 0 5` is
    10 (lo, since 5 < 10), kernel-checked. -/
theorem a49_int_lo_gt_hi : ∃ w, EvalExp E0 (ap (v "clamp") [i 10, i 0, i 5]) w ∧ (Expect.int 10).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)

/-- A49: APPLY(clamp, 10, 0, 5) = {10} at Int: the set has one member. -/
theorem a49_int_apply_singleton : applySet .clamp [.int 10, .int 0, .int 5] = [.int 10] := by
  simp [applySet, BasVal.isEffect, BasVal.isNew, applySetCore, cmp, cmpInt, isFloat, pickFirst]

/-- A51: `(\x -> x) == (\x -> x)` evaluates to True ... -/
theorem a51_true :
    ∃ w, EvalExp E0 (eq (.atexp (.paren (lams [pv "x"] (v "x")))) (.atexp (.paren (lams [pv "x"] (v "x")))))
      w ∧ (Expect.con "True" []).holds w :=
  valueCheck_sound (o := .const false) (by decide +kernel)

/-- ... and to False: both results are derivable. -/
theorem a51_false :
    ∃ w, EvalExp E0 (eq (.atexp (.paren (lams [pv "x"] (v "x")))) (.atexp (.paren (lams [pv "x"] (v "x")))))
      w ∧ (Expect.con "False" []).holds w :=
  valueCheck_sound (o := .const true) (by decide +kernel)

/-- A44: the conversions to Int at 2.5, -2.5, NaN, the infinities and 1e300,
    in that order: `round` rounds a half upward (x + 1/2 exact), and every
    conversion saturates into [-2^63, 2^63 - 1], NaN giving 0. `Float.floor`
    is computed by the C library, so this is proved by `native_decide`. [native] -/
theorem a44_conversions :
    let f (x : Float) : Val := .sv (.float x)
    let xs : List Float := [2.5, -2.5, 0 / 0, 1 / 0, -1 / 0, 1e300]
    [BasVal.round, .floor, .ceiling, .truncate].map (fun b => xs.map fun x => (applySet b [f x]).map showElm)
      = [[["3"], ["-2"], ["0"], ["9223372036854775807"], ["-9223372036854775808"], ["9223372036854775807"]],
         [["2"], ["-3"], ["0"], ["9223372036854775807"], ["-9223372036854775808"], ["9223372036854775807"]],
         [["3"], ["-2"], ["0"], ["9223372036854775807"], ["-9223372036854775808"], ["9223372036854775807"]],
         [["2"], ["-2"], ["0"], ["9223372036854775807"], ["-9223372036854775808"], ["9223372036854775807"]]] := by
  native_decide

/-- A44: `round -2.5` is -2, by the rules from E0. [native] -/
theorem a44_round_minus_half :
    ∃ w, EvalExp E0 (ap (v "round") [.atexp (neg (.scon (.float 25 (-1))))]) w ∧ showElm w = "-2" :=
  checkShowWith_sound (o := .const false) (by native_decide)

end StandardElm
