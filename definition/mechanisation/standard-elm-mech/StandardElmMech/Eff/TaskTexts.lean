/-
  A Standard Definition of Elm? Mechanisation: the texts of Task and of the List functions it
  reaches (plan decision D3), and the dynamic interfaces ME0(Task) and ME0(Process)
  (appendix-dynamic-basis.tex, sec:appendix-dynamic-basis-env, Figure fig:dynamic-basis-others),
  plan step 4.

  The texts are those of elm/core 1.0.5, after the derived forms: src/List.elm, foldl (lines 150 to
  157), foldr (172 to 174), foldrHelper (177 to 206) and reverse (259 to 261); src/Task.elm, map
  (117 to 120), map2 to map5 (139 to 173), sequence (183 to 185), mapError (246 to 249), perform
  (282 to 284) and attempt (311 to 317). `<<` is left-associative and `|>` left-associative
  (Figure fig:core-fixities, as Basics.elm declares them); the integer constants of foldrHelper are
  at Int (number specialisation: ctr is an Int).

  The values are taken in order: the text of a value of the module is evaluated in E_modid and the
  values of the texts before it (sec:appendix-dynamic-basis-elm). `textValue_eval` derives every
  text's value, by r:d-dec-nonrec, or r:d-dec-rec for the recursive foldl and foldrHelper.
-/
import StandardElmMech.InitialBasis
import StandardElmMech.Derived
import StandardElmMech.RulesL

namespace StandardElm.Eff
open StandardElm StandardElm.D

/-! ## The List texts -/

def foldlText : Def := .fn "foldl" [pv "func", pv "acc", pv "list"]
  (caseOf (v "list")
    [ (pcon "[]" [], v "acc"),
      (.cons (P (pv "x")) (P (pv "xs")), ap (v "foldl") [v "func", ap (v "func") [v "x", v "acc"], v "xs"]) ])

def reverseText : Def := .fn "reverse" [pv "list"] (ap (v "foldl") [v "cons", listE [], v "list"])

def foldrHelperText : Def := .fn "foldrHelper" [pv "fn", pv "acc", pv "ctr", pv "ls"]
  (caseOf (v "ls")
    [ (pcon "[]" [], v "acc"),
      (.cons (P (pv "a")) (P (pv "r1")),
        caseOf (v "r1")
          [ (pcon "[]" [], ap (v "fn") [v "a", v "acc"]),
            (.cons (P (pv "b")) (P (pv "r2")),
              caseOf (v "r2")
                [ (pcon "[]" [], ap (v "fn") [v "a", ap (v "fn") [v "b", v "acc"]]),
                  (.cons (P (pv "c")) (P (pv "r3")),
                    caseOf (v "r3")
                      [ (pcon "[]" [], ap (v "fn") [v "a", ap (v "fn") [v "b", ap (v "fn") [v "c", v "acc"]]]),
                        (.cons (P (pv "d")) (P (pv "r4")),
                          letDefs
                            [.fn "res" []
                              (ifte (bin ">" (v "ctr") (i 500))
                                (ap (v "foldl") [v "fn", v "acc", ap (v "reverse") [v "r4"]])
                                (ap (v "foldrHelper") [v "fn", v "acc", bin "+" (v "ctr") (i 1), v "r4"]))]
                            (ap (v "fn") [v "a", ap (v "fn") [v "b", ap (v "fn") [v "c",
                              ap (v "fn") [v "d", v "res"]]]])) ]) ]) ]) ])

def foldrText : Def := .fn "foldr" [pv "fn", pv "acc", pv "ls"]
  (ap (v "foldrHelper") [v "fn", v "acc", i 0, v "ls"])

/-- The List texts in order: foldl, reverse, foldrHelper, foldr. -/
def listTexts : List Def := [foldlText, reverseText, foldrHelperText, foldrText]

/-! ## The Task texts -/

/-- taskA |> andThen (\a -> taskB |> andThen (\b -> ... succeed (func a b ...))), for the task and
    variable names given. -/
def mapNBody : List (String × String) → List String → Exp
  | [], vars => ap (v "succeed") [ap (v "func") (vars.map v)]
  | (task, x) :: rest, vars =>
    bin "|>" (v task) (ap (v "andThen") [lams [pv x] (mapNBody rest (vars ++ [x]))])

def mapText : Def := .fn "map" [pv "func", pv "taskA"] (mapNBody [("taskA", "a")] [])
def map2Text : Def := .fn "map2" [pv "func", pv "taskA", pv "taskB"]
  (mapNBody [("taskA", "a"), ("taskB", "b")] [])
def map3Text : Def := .fn "map3" [pv "func", pv "taskA", pv "taskB", pv "taskC"]
  (mapNBody [("taskA", "a"), ("taskB", "b"), ("taskC", "c")] [])
def map4Text : Def := .fn "map4" [pv "func", pv "taskA", pv "taskB", pv "taskC", pv "taskD"]
  (mapNBody [("taskA", "a"), ("taskB", "b"), ("taskC", "c"), ("taskD", "d")] [])
def map5Text : Def := .fn "map5" [pv "func", pv "taskA", pv "taskB", pv "taskC", pv "taskD", pv "taskE"]
  (mapNBody [("taskA", "a"), ("taskB", "b"), ("taskC", "c"), ("taskD", "d"), ("taskE", "e")] [])

def sequenceText : Def := .fn "sequence" [pv "tasks"]
  (ap (qv "List" "foldr") [ap (v "map2") [.atexp (.op "::")], ap (v "succeed") [listE []], v "tasks"])

def mapErrorText : Def := .fn "mapError" [pv "convert", pv "task"]
  (bin "|>" (v "task") (ap (v "onError") [bin "<<" (v "fail") (v "convert")]))

def performText : Def := .fn "perform" [pv "toMessage", pv "task"]
  (ap (v "command") [ap (c "Perform") [ap (v "map") [v "toMessage", v "task"]]])

/-- `succeed << resultToMessage << Ok` is `(succeed << resultToMessage) << Ok` (left). -/
def attemptText : Def := .fn "attempt" [pv "resultToMessage", pv "task"]
  (ap (v "command") [ap (c "Perform")
    [bin "|>"
      (bin "|>" (v "task") (ap (v "andThen") [bin "<<" (bin "<<" (v "succeed") (v "resultToMessage")) (c "Ok")]))
      (ap (v "onError") [bin "<<" (bin "<<" (v "succeed") (v "resultToMessage")) (c "Err")])]])

/-- map to map5, sequence (after map2), mapError, perform (after map), attempt. -/
def taskTexts : List Def :=
  [mapText, map2Text, map3Text, map4Text, map5Text, sequenceText, mapErrorText, performText, attemptText]

/-! ## Values of texts taken in order -/

/-- The value of a text `x p ps = e` in E: the closure (p, \ps -> e, E, ∅) (r:d-dec-nonrec), or
    Rec of it for a recursive text (r:d-dec-rec). -/
def textValue (E : Env) : Def → ValEnv
  | .fn x (p :: ps) e =>
    if isRecursive [(x, .closure p (lams ps e) E [])] (.var x (lams (p :: ps) e) none)
    then recVE [(x, .closure p (lams ps e) E [])]
    else [(x, .closure p (lams ps e) E [])]
  | _ => []

/-- The values of texts taken in order: text k is evaluated in E + (the values of texts 0..k-1). -/
def textValuesFrom (E : Env) : ValEnv → List Def → ValEnv
  | acc, [] => acc
  | acc, d :: ds => textValuesFrom E (fmPlus acc (textValue (E.plusVE acc) d)) ds

def textValues (E : Env) (ds : List Def) : ValEnv := textValuesFrom E [] ds

/-- Every text derives its value in its environment. -/
theorem textValue_eval (E : Env) (x : Var) (p : AtPat) (ps : List AtPat) (e : Exp) :
    EvalDec E (.val (.var x (lams (p :: ps) e) none)) (textValue E (.fn x (p :: ps) e)) := by
  have hv : EvalValBind E (.var x (lams (p :: ps) e) none) (fmPlus [(x, .closure p (lams ps e) E [])] []) :=
    EvalValBind.r_d_valbind_var _ _ _ _ _ _ (EvalExp.r_d_exp_lambda E p (lams ps e)) (EvalValBindOpt.opt_none _)
  have he : fmPlus [(x, Val.closure p (lams ps e) E [])] ([] : ValEnv) = [(x, .closure p (lams ps e) E [])] := by
    simp [fmPlus]
  rw [he] at hv
  simp only [textValue]
  split
  · rename_i h; exact EvalDec.r_d_dec_rec _ _ _ hv h
  · rename_i h; exact EvalDec.r_d_dec_nonrec _ _ _ hv (by simpa using h)

/-- The same derivation in the logged relation, with the empty log (a lambda logs nothing). -/
theorem textValue_evalL (E : Env) (x : Var) (p : AtPat) (ps : List AtPat) (e : Exp) :
    EvalDecL E (.val (.var x (lams (p :: ps) e) none)) (textValue E (.fn x (p :: ps) e)) [] := by
  have hv : EvalValBindL E (.var x (lams (p :: ps) e) none) (fmPlus [(x, .closure p (lams ps e) E [])] []) ([] ++ []) :=
    EvalValBindL.r_d_valbind_var_l _ _ _ _ _ _ _ _ (EvalExpL.r_d_exp_lambda_l E p (lams ps e))
      (EvalValBindOptL.opt_none_l _)
  have he : fmPlus [(x, Val.closure p (lams ps e) E [])] ([] : ValEnv) = [(x, .closure p (lams ps e) E [])] := by
    simp [fmPlus]
  rw [he] at hv
  simp only [textValue]
  split
  · rename_i h; exact EvalDecL.r_d_dec_rec_l _ _ _ _ hv h
  · rename_i h; exact EvalDecL.r_d_dec_nonrec_l _ _ _ _ hv (by simpa using h)

/-! ## The environments and the interfaces -/

/-- E_List: the qualifier Basics (the derived form of `if` uses Basics.True and Basics.False), and
    `cons`, whose text `cons = Elm.Kernel.List.cons` is the list constructor `::`. -/
def E_List0 : Env := E0base.plus [("Basics", .mk [] VE_K)] [("cons", conv conCons)]

def listTextValues : ValEnv := textValues E_List0 listTexts

/-- The value of List.foldr. -/
def foldrVal : Val := (fmLookup listTextValues "foldr").getD .unit

/-- The values Task's texts see: its basic values, the two hidden names (A60, A85), and the
    constructors of Result and Maybe. -/
def VE_Task0 : ValEnv :=
  [ ("succeed", bas .taskSucceed), ("fail", bas .taskFail), ("andThen", bas .taskAndThen),
    ("onError", bas .taskOnError),
    ("command", bas .taskCommand), ("Perform", conv conPerform),
    ("Ok", conv conOk), ("Err", conv conErr), ("Just", conv conJust), ("Nothing", conv conNothing) ]

def QE_Task : List (String × Env) := [("List", .mk [] [("foldr", foldrVal)])]

def E_Task0 : Env := E0base.plus QE_Task VE_Task0

def taskTextValues : ValEnv := textValues E_Task0 taskTexts

def VE_TaskIface : ValEnv :=
  [ ("succeed", bas .taskSucceed), ("fail", bas .taskFail),
    ("andThen", bas .taskAndThen), ("onError", bas .taskOnError) ] ++ taskTextValues

def VE_Process : ValEnv :=
  [ ("spawn", bas .processSpawn), ("sleep", bas .processSleep), ("kill", bas .processKill) ]

/-- Each text of Task derives its value in the environment of the texts before it. -/
theorem taskTexts_eval : ∀ k x p ps e, taskTexts[k]? = some (.fn x (p :: ps) e) →
    EvalDec (E_Task0.plusVE (textValues E_Task0 (taskTexts.take k))) (.val (.var x (lams (p :: ps) e) none))
      (textValue (E_Task0.plusVE (textValues E_Task0 (taskTexts.take k))) (.fn x (p :: ps) e)) :=
  fun _ x p ps e _ => textValue_eval _ x p ps e

/-- Each text of List (foldl and foldrHelper by r:d-dec-rec, reverse and foldr by r:d-dec-nonrec)
    derives its value in the environment of the texts before it. -/
theorem listTexts_eval : ∀ k x p ps e, listTexts[k]? = some (.fn x (p :: ps) e) →
    EvalDec (E_List0.plusVE (textValues E_List0 (listTexts.take k))) (.val (.var x (lams (p :: ps) e) none))
      (textValue (E_List0.plusVE (textValues E_List0 (listTexts.take k))) (.fn x (p :: ps) e)) :=
  fun _ x p ps e _ => textValue_eval _ x p ps e

/-- The logged derivations, with the empty log. -/
theorem taskTexts_evalL : ∀ k x p ps e, taskTexts[k]? = some (.fn x (p :: ps) e) →
    EvalDecL (E_Task0.plusVE (textValues E_Task0 (taskTexts.take k))) (.val (.var x (lams (p :: ps) e) none))
      (textValue (E_Task0.plusVE (textValues E_Task0 (taskTexts.take k))) (.fn x (p :: ps) e)) [] :=
  fun _ x p ps e _ => textValue_evalL _ x p ps e

/-- foldl and foldrHelper are recursive, reverse and foldr are not (so their values are Rec of
    their closures, and the closures themselves). -/
theorem listTexts_recursive :
    (listTexts.map fun d => match d with
      | .fn x (p :: ps) e => isRecursive [(x, .closure p (lams ps e) E_List0 [])] (.var x (lams (p :: ps) e) none)
      | _ => false) = [true, false, true, false] := by decide +kernel

end StandardElm.Eff
