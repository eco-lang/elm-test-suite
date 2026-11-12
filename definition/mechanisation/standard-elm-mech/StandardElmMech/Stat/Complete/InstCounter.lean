/-
  A Standard Definition of Elm? Mechanisation: a regression test of step 9's instance relation
  (milestone (b) of plan step 11; a finding about `Principal.lean`, fixed 2026-11-12).

  `\y -> let f = \x -> x in f y` has a derivation `a1` (W's, up to its choice of variables) that
  gives `f` the scheme `∀β. β → β`, instantiated at `α` at `f y`, and a derivation `a2` that gives
  `x` the variable of `y`, so `f : α → α`, not generalised (closure does not generalise `α`, which
  is free in the context), with an empty instance at `f y`.

  Step 9's occurrence nodes carried the type of the occurrence followed by its instance (the types
  chosen for the bound variables of the scheme), and `NodeInstance` compares the types of two
  nodes with `mapM`; at `f y` the two derivations carried lists of lengths 2 and 1, so neither was
  an instance of the other and no derivation of the phrase was principal: `PrincipalExistsCore`
  was false, and `InferPrincipalFor` false for every program where a polymorphic `let` is also
  derivable monomorphically.

  The book's sentence at an occurrence is `C ⊢ longvar ⇒ τ`: the instance is a witness of the side
  condition `σ ≻ τ`, not a type of the sentence. Occurrence nodes now carry only `τ`, and `a2` is
  an instance of `a1` (`a2_instance_a1`), by the substitution taking `β` to `α`.
-/
import StandardElmMech.Stat.Complete.W
import StandardElmMech.Stat.Principal

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BAtPat BAtExp BExp BDec BValBind)

namespace InstCounter

def C0 : Ctx := ⟨[], [], Env.empty⟩

def lv (x : String) : LongId := ⟨none, x⟩

/-- `\y -> let f = \x -> x in f y`. -/
def eY : BExp :=
  .lam (.var "y") (.atexp (.letE (.val (.var "f" none (.lam (.var "x") (.atexp (.var (lv "x")))) none))
    (.app (.atexp (.var (lv "f"))) (.var (lv "y")))))

def α : Ty := .var (.fresh 0 .any)
def β : Ty := .var (.fresh 1 .any)

/-- `x : β`, so `f : ∀β. β → β`, instantiated at `α`. -/
def a1 : AExp :=
  .lam (.var "y" α) (.atexp (.letE
    (.val [("f", (mono (.fn β β), .v))] (.var "f" none (.fn β β) (.lam (.var "x" β) (.atexp (.var (lv "x") [] β))) none))
    (.app (.atexp (.var (lv "f") [α] (.fn α α))) (.var (lv "y") [] α))))

/-- `x : α`, the variable of `y`, so `f : α → α`, not generalised. -/
def a2 : AExp :=
  .lam (.var "y" α) (.atexp (.letE
    (.val [("f", (mono (.fn α α), .v))] (.var "f" none (.fn α α) (.lam (.var "x" α) (.atexp (.var (lv "x") [] α))) none))
    (.app (.atexp (.var (lv "f") [] (.fn α α))) (.var (lv "y") [] α))))

theorem a1_checks : checkExp C0 a1 = true := by decide
theorem a2_checks : checkExp C0 a2 = true := by decide
theorem a1_erase : a1.erase = eY := rfl
theorem a2_erase : a2.erase = eY := rfl

/-- W's derivation is `a1`, up to its choice of variables. -/
theorem w_eY : (inferExpW wFuel C0 eY).isOk = true := by decide +kernel

/-! ## The monomorphic derivation is an instance of the polymorphic one -/

mutual
theorem apply_substId : (τ : Ty) → Subst.id.apply τ = some τ
  | .var a => by simp [Subst.apply, Subst.id]
  | .record ρ none => by simp [Subst.apply, applyRow_substId ρ]
  | .record ρ (some e) => by
    have h := applyRow_substId ρ
    simp only [Subst.apply]
    rw [h]; rfl
  | .fn a b => by simp [Subst.apply, apply_substId a, apply_substId b]
  | .con as t => by simp [Subst.apply, applyList_substId as]
theorem applyRow_substId : (ρ : Row) → Subst.id.applyRow ρ = some ρ
  | [] => rfl
  | (l, τ) :: rest => by simp [Subst.applyRow, apply_substId τ, applyRow_substId rest]
theorem applyList_substId : (l : List Ty) → Subst.id.applyList l = some l
  | [] => rfl
  | τ :: rest => by simp [Subst.applyList, apply_substId τ, applyList_substId rest]
end

theorem gen_mono {σ : Scheme} (hb : σ.bound = []) {τ : Ty} (h : Gen σ τ) : τ = σ.body := by
  obtain ⟨ts, S, hS, _, ha⟩ := h
  rw [hb] at hS
  cases ts with
  | nil =>
    simp only [bindSubst, Option.some.injEq] at hS
    subst hS
    rw [apply_substId] at ha
    exact (Option.some.inj ha).symm
  | cons _ _ => simp [bindSubst] at hS

/-- A decidable sufficient condition for `NodeInstance`: each scheme of the second node is S of
    the first's, or binds nothing and is an instance of S of the first's at `w`. -/
def nodeOK (S : Subst) (w : List Ty) (n n' : Node) : Bool :=
  n.U.isEmpty && n'.U.isEmpty && n.tys.mapM S.apply == some n'.tys &&
    n.schemes.length == n'.schemes.length &&
    (n.schemes.zip n'.schemes).all fun (σ, σ') =>
      match S.applyScheme σ with
      | some σS => σS == σ' || (σ'.bound.isEmpty && genAt σS w σ'.body)
      | none => false

theorem nodeOK_spec {S : Subst} {w : List Ty} {n n' : Node} (h : nodeOK S w n n' = true) :
    NodeInstance S n n' := by
  simp only [nodeOK, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hU, hU'⟩, ht⟩, hl⟩, hs⟩ := h
  refine ⟨⟨[], by simp [hU], by simp [SetEq, hU']⟩, ht, hl, ?_⟩
  intro i hi hi' τ hg
  have hm : (n.schemes[i], n'.schemes[i]) ∈ n.schemes.zip n'.schemes := by
    rw [List.mem_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩
  have hc := hs _ hm
  cases ha : S.applyScheme n.schemes[i] with
  | none => simp only [ha] at hc; cases hc
  | some σS =>
    simp only [ha, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.isEmpty_iff] at hc
    refine ⟨σS, rfl, ?_⟩
    rcases hc with e | ⟨hb, hg'⟩
    · rw [e]; exact hg
    · rw [gen_mono hb hg]; exact gen_of_genAt hg'

/-- The substitution taking `a1`'s `β` to `α`. -/
def S12 : Subst := ⟨[(.fresh 1 .any, α)], []⟩

theorem nodes12 :
    (nodesExp C0 [] a1).all (fun n => (nodesExp C0 [] a2).all fun n' =>
      !(n.path == n'.path) || nodeOK S12 [α] n n') = true ∧
    ((nodesExp C0 [] a1).flatMap (·.tys)).all (fun τ => (S12.apply τ).isSome) = true := by
  decide

/-- The monomorphic derivation is an instance of the polymorphic one: the two are comparable, as
    they were not while occurrence nodes carried the instance lists. -/
theorem a2_instance_a1 : InstanceOf C0 a2 a1 := by
  refine ⟨rfl, S12, by decide, fun v _ => by simp [C0, Ctx.tyvars, Env.tyvars, Env.empty, FMap.tyvarsBy, TyEnv.tyvars, ValEnv.tyvars], fun τ hτ =>
    List.all_eq_true.mp nodes12.2 τ hτ, ?_⟩
  intro n hn n' hn' e
  have := List.all_eq_true.mp (List.all_eq_true.mp nodes12.1 n hn) n' hn'
  simp only [e, beq_self_eq_true, Bool.not_true, Bool.false_or] at this
  exact nodeOK_spec this

end InstCounter

end StandardElm.Stat.Complete
