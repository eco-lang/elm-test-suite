/-
  A Standard Definition of Elm? Mechanisation: a regression test of `genNames` (plan step 10, found
  2026-11-12 while proving the invariance lemma).

  `genNames B a` was every type name of the module's environment outside `T of B`. A derivation may
  record any type at a node the sentence leaves free, a type name that is in no basis among them
  (the checker does not ask that the names of a type be in `T of C`). For `main = text "x"` the
  inference gives `main : ∀msg. Html msg`; the derivation `mJ` that takes `msg` to `t = ⟨5000, 0⟩`
  (`main : Html t`) also checks, erases to the same module and has no free `bnd` variable, and
  generated one name where the inferred one generated none, so it was not an instance of the
  inferred derivation (no bijection between the generated names), which was therefore not
  principal: D11's hypothesis was false for most tests.

  `genNames` is now the names of the module's custom types (sec:static-modules-principal: the names
  "a derivation chooses freely outside T of B"). Both derivations generate none (`facts`), and `mJ`
  is an instance of the inferred derivation by the substitution taking `msg` to `t`
  (`mJ_instance`).
-/
import StandardElmMech.Stat.EndToEnd
import StandardElmMech.Stat.TestBasis

namespace StandardElm.Stat
open StandardElm.Src (prog mdl hdr imp val v app str)

namespace JunkCE

def ceProg : Src.SProgram := Src.canonOrder <| prog "ce" "Junk" [
  mdl (hdr false "Main" (.items [.var "main"])) [imp "Html" none (some (.items [.var "text"]))]
    [val "main" none [] (app (v "text") [str "x"])]]

/-- The derivation the inference gives. -/
def ceA : AProgram := match inferProgram Btest (bareOf ceProg) with | .ok a => a | .error _ => []

def mA : AModule := ceA.headD ⟨⟨false, "", .all⟩, [], none⟩

/-- A type name in no basis. -/
def tJ : TyName := ⟨5000, 0⟩
def hJ : Ty := .con [.con [] tJ] tNode

/-- `main : Html t`. -/
def vbJ : AValBind :=
  .var "main" none hJ (.app (.atexp (.var ⟨none, "text"⟩ [.con [] tJ] (.fn tStringTy hJ)))
    (.scon (.str "x") tStringTy)) none

def mJ : AModule := ⟨mA.header, mA.imports, some (.value vbJ.ve vbJ)⟩

set_option maxRecDepth 100000 in
theorem facts : (inferProgram Btest (bareOf ceProg)).toOption.isSome = true ∧ ceA.length = 1 ∧
    checkProgram Btest ceA = true ∧ checkModule Btest mA = true ∧ checkModule Btest mJ = true ∧
    mJ.erase = mA.erase ∧ genNames Btest mA = [] ∧ genNames Btest mJ = [] := by
  decide +kernel

theorem mJ_noFreeBnd : mJ.NoFreeBnd := by
  intro d hd
  simp only [mJ, Option.some.injEq] at hd
  subst hd
  intro C path n hn τ hτ x hx
  simp [vbJ, nodesValBind, nodesValBindOpt, nodesExp, nodesAtExp, AExp.ty, AAtExp.ty, Ty.cod, litInst]
    at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hJ, tStringTy] at hτ <;>
    rcases hτ with rfl | rfl <;> simp [Ty.vars, Ty.listVars] at hx

/-! ## `mJ` is an instance of the inferred derivation -/

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

/-- A decidable sufficient condition for `NodeInstance` when the second node's schemes bind
    nothing, every bound variable of the first's taken to `t`. -/
def nodeOK (S : Subst) (n n' : Node) : Bool :=
  n.U.isEmpty && n'.U.isEmpty && n.tys.mapM S.apply == some n'.tys &&
    n.schemes.length == n'.schemes.length &&
    (n.schemes.zip n'.schemes).all fun (σ, σ') =>
      σ'.bound.isEmpty && match S.applyScheme σ with
        | some σS => genAt σS (σS.bound.map fun _ => .con [] tJ) σ'.body
        | none => false

theorem nodeOK_spec {S : Subst} {n n' : Node} (h : nodeOK S n n' = true) : NodeInstance S n n' := by
  simp only [nodeOK, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hU, hU'⟩, ht⟩, hl⟩, hs⟩ := h
  refine ⟨⟨[], by simp [hU], by simp [SetEq, hU']⟩, ht, hl, ?_⟩
  intro i hi hi' τ hg
  have hm : (n.schemes[i], n'.schemes[i]) ∈ n.schemes.zip n'.schemes := by
    rw [List.mem_iff_getElem]; exact ⟨i, by simp; omega, by simp⟩
  have hc := hs _ hm
  obtain ⟨hb, hc⟩ := hc
  rw [gen_mono hb hg]
  cases ha : S.applyScheme n.schemes[i] with
  | none => rw [ha] at hc; cases hc
  | some σS => rw [ha] at hc; exact ⟨σS, rfl, gen_of_genAt hc⟩

/-- The substitution taking the inferred derivation's `msg` to `t`. -/
def SJ : Subst := ⟨[(.fresh 1 .any, .con [] tJ)], []⟩

set_option maxRecDepth 100000 in
theorem mJ_nodes :
    ((nodesModule Btest mA).map (Node.renameNames [])).all (fun n =>
      (nodesModule Btest mJ).all fun n' => !(n.path == n'.path) || nodeOK SJ n n') = true ∧
    (((nodesModule Btest mA).map (Node.renameNames [])).flatMap (·.tys)).all
      (fun τ => (SJ.apply τ).isSome) = true := by
  decide +kernel

/-- The junk derivation is an instance of the inferred one. -/
theorem mJ_instance : InstanceOfMod Btest mJ mA := by
  obtain ⟨-, -, -, -, -, he, gA, gJ⟩ := facts
  refine ⟨he, [], by rw [gA, gJ]; exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, .nil, .nil⟩, SJ, by decide,
    fun v hv => by simp, fun τ hτ => List.all_eq_true.mp mJ_nodes.2 τ hτ, ?_⟩
  intro n hn n' hn' e
  have := List.all_eq_true.mp (List.all_eq_true.mp mJ_nodes.1 n hn) n' hn'
  simp only [e, beq_self_eq_true, Bool.not_true, Bool.false_or] at this
  exact nodeOK_spec this

end JunkCE

end StandardElm.Stat
