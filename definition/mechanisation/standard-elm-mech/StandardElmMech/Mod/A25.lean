/-
  A Standard Definition of Elm? Mechanisation: ruling A25, plan step 2 (dynamic-modules.tex, the
  comment on r:dm-topdec-val about a group variable forced during its own evaluation).

  The module `x = let f _ = x in f ()` has no meaning: the thunk translation makes x's right-hand
  side the body of the closure bound to #x, and forcing #x applies that closure, whose body applies
  f, whose body forces #x again. Each turn of the loop costs the evaluator 8 units of fuel
  (`step`), so the evaluator runs out of fuel at every fuel (`a25_loop`, by strong induction), and
  by completeness (`evExp_complete`) no derivation of the forcing exists. The module's derivation
  needs one (r:dm-topdec-val's premise), so there is none (`a25_no_value`), and no program that
  begins with the module has a meaning (`a25_no_meaning`). The loop is unfolded symbolically: the
  closure's environment E1 stays abstract, since every lookup finds its variable at the head.
-/
import StandardElmMech.Mod.Complete

namespace StandardElm.Mod
open StandardElm StandardElm.D


def a25Body : Exp := .atexp (.letE (.val (.var "f" (.lam .wild (v "x")) none)) (.app (v "f") .unit))
/-- The thunk of x's group: let f _ = (#x ()) in f (). -/
def a25T : Exp :=
  .atexp (.letE (.val (.var "f" (.lam .wild (.atexp (.paren (.app (.atexp (.var ⟨none, "#x"⟩)) .unit))))
    none)) (.app (.atexp (.var ⟨none, "f"⟩)) .unit))
theorem a25T_eq : thunkExp ["x"] a25Body = a25T := rfl
def cloA25 (E1 : Env) : Val := .closure .wild a25T E1 [("#x", .closure .wild a25T E1 [])]

/-- Applying a closure whose pattern is `_` evaluates its body, two fuel levels down. -/
theorem appVal_wild_out (o : Oracle) (n : Nat) (e : Exp) (E : Env) (VE : ValEnv) (v : Val) (k : Nat) :
    (appVal o (n+2) (.closure .wild e E VE) v k).out =
      (evExp o (n+1) ((E.plusVE (recVE VE)).plusVE []) e k).out := by
  simp only [appVal, matchAtPat, List.nil_append]
  split <;> simp_all

theorem appVal_wild (o : Oracle) (n : Nat) (e : Exp) (E : Env) (VE : ValEnv) (v : Val) (k : Nat) :
    appVal o (n+2) (.closure .wild e E VE) v k =
      match evExp o (n+1) ((E.plusVE (recVE VE)).plusVE []) e k with
      | ⟨.value x, l2, k2⟩ => ⟨.value x, l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l2, k2⟩ := by
  simp only [appVal, matchAtPat]
  rfl

/-- One turn of the loop: forcing at fuel M + 14 comes back to forcing at M + 6. -/
theorem a25_step (E1 : Env) (o : Oracle) (M k : Nat) :
    (appVal o (M + 14) (cloA25 E1) .unit k).out = (appVal o (M + 6) (cloA25 E1) .unit k).out := by
  conv => lhs; rw [show M + 14 = (M + 12) + 2 from rfl, cloA25, appVal_wild_out]
  simp (config := {decide := true}) only [a25T, evExp, evAtExp, evDec, evValBind, evValBindOpt,
    isRecursive, recVE, Env.plusVE, fmPlus, Env.lookup, fmLookup, Env.VE, Env.QE, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.nil_append,
    List.cons_append, Bool.or_false, Bool.not_false, ite_true, ite_false,
    fmDom, fvValBindRhs, fvValBindRhsOpt, fvExp, fvAtExp, boundAtPat, removeAll,
    List.contains_cons, List.contains_nil, List.append_nil]
  rw [show M + 10 = (M + 8) + 2 from rfl, appVal_wild]
  simp (config := {decide := true}) only [evExp, evAtExp, recVE, Env.plusVE, fmPlus,
    Env.lookup, fmLookup, Env.VE, Env.QE, List.filter_cons, List.map_nil,
    List.any_nil, List.nil_append, Bool.not_false,
    ite_true, List.append_nil]
  rw [cloA25, a25T]
  generalize appVal o (M + 6) _ Val.unit k = r
  rcases r with ⟨out, l, k'⟩
  cases out <;> rfl

/-- The evaluator runs out of fuel forcing the thunk, at every fuel. -/
theorem a25_loop (E1 : Env) (o : Oracle) (k : Nat) :
    ∀ n, (appVal o n (cloA25 E1) .unit k).out = .outOfFuel := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 14
    · have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
          n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [cloA25, a25T, appVal, matchAtPat, evExp, evAtExp, evDec,
        evValBind, evValBindOpt, isRecursive, recVE, Env.plusVE, fmPlus, Env.lookup, fmLookup, Env.VE,
        Env.QE, fmDom, fvValBindRhs, fvValBindRhsOpt, fvExp, fvAtExp]
    · obtain ⟨M, rfl⟩ : ∃ M, n = M + 14 := ⟨n - 14, by omega⟩
      rw [a25_step]; exact ih (M + 6) (by omega)

/-- Forcing x's thunk, in the environment the group's value binding gives, never ends. -/
theorem a25_force_out (Ev : Env) (o : Oracle) (k : Nat) : ∀ n,
    (evExp o n (Ev.plusVE (recVE [("#x", .closure .wild a25T Ev [])])) (forceExp "#x") k).out =
      .outOfFuel := by
  intro n
  rcases n with _ | _ | _ | n
  · simp [evExp]
  · simp (config := {decide := true}) [evExp, recVE, Env.plusVE, fmPlus,
      Env.VE, Env.QE, forceExp]
  · simp (config := {decide := true}) [evExp, evAtExp, recVE, Env.plusVE, fmPlus,
      Env.VE, Env.QE, forceExp]
  · have hl := a25_loop Ev o k
    simp (config := {decide := true}) only [evExp, evAtExp, recVE, Env.plusVE, fmPlus, Env.lookup,
      fmLookup, Env.VE, Env.QE, forceExp, List.map_cons,
      List.map_nil, List.any_cons, List.any_nil, List.nil_append, List.cons_append, Bool.or_false,
      ite_true, List.append_nil]
    have h := hl (n + 2)
    rw [cloA25] at h
    generalize appVal o (n + 2) _ Val.unit k = r at h ⊢
    rcases r with ⟨out, l, k'⟩
    cases out <;> simp_all

def mA25 : Module := .withDefaults ⟨false, "A25", .all⟩ [] (.val [("x", a25Body)])

theorem thunkGroup_a25 : thunkGroup [("x", a25Body)] = .var "#x" (.lam .wild a25T) none := rfl

/-- A25: a delayed self-reference forced during its own evaluation has no result: the module
    `x = let f _ = x in f ()` has no meaning, in any basis. -/
theorem a25_no_value (B : Basis) : ¬ ∃ B' VE, EvalModule B mA25 B' VE := by
  rintro ⟨B', VE, d⟩
  cases d with
  | r_dm_module h is td E I m I' himp htd hh =>
  cases htd with
  | r_dm_topdec_val _ _ VE1 vs hne hvb hforce =>
  rw [thunkGroup_a25] at hvb
  cases hvb with
  | r_d_valbind_var _ _ _ _ v VE2 hexp hopt =>
  cases hexp
  cases hopt
  simp only [List.map_cons, List.map_nil, Function.comp, thunkVar] at hforce
  cases hforce with
  | seq_cons _ _ v' vs' hfx _ =>
  obtain ⟨L, n, hn⟩ := evExp_complete hfx
  have hfmp : fmPlus [("#x", Val.closure AtPat.wild a25T (E0base.plusEnv E) [])] ([] : ValEnv) =
      [("#x", Val.closure AtPat.wild a25T (E0base.plusEnv E) [])] := by simp [fmPlus]
  have hx : ("#" ++ "x" : String) = "#x" := rfl
  rw [hfmp, hx, a25_force_out] at hn
  cases hn

/-- A25: a program whose first module is `x = let f _ = x in f ()` has no meaning. -/
theorem a25_no_meaning (B : Basis) (p : List Module) : ¬ ∃ v, EvalProgram B (mA25 :: p) v := by
  rintro ⟨v, d⟩
  cases d with
  | r_p_dyn_module _ _ _ B' VE _ hm _ _ => exact a25_no_value B ⟨B', VE, hm⟩
  | r_p_dyn_main _ _ B' VE _ hm _ => exact a25_no_value B ⟨B', VE, hm⟩

end StandardElm.Mod
