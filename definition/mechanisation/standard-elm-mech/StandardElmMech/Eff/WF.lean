/-
  A Standard Definition of Elm? Mechanisation: well-formed values (decision D5), plan step 4.

  A boundary value that is not a JSON value (one holding a byte sequence, A92) is not a value of
  the language (sec:effects-compound): `Val.bv j` holds a JSON value everywhere except as the
  argument of a leaf of an outgoing port, where the book's CmdVal admits Val ∪ BVal. `BadBv v`
  says that a non-JSON boundary value occurs in v elsewhere, and `Val.WF v` that none does. An
  out leaf may carry bytes (`wf_out_leaf`); a boundary value elsewhere must be JSON
  (`wf_bv_iff`); `a92_value_no_bytes` shows that Json.Encode.Value never carries bytes.
-/
import StandardElmMech.Eff.Properties

namespace StandardElm.Eff
open StandardElm

mutual
  /-- A non-JSON boundary value occurs in the value, not as the argument of an out leaf. -/
  inductive BadBv : Val → Prop where
    | here (j : BVal) : j.isJson = false → BadBv (.bv j)
    | basApp (b : BasVal) (args : List Val) (v : Val) : v ∈ args → BadBv v → BadBv (.basApp b args)
    | con (c : Con) (args : List Val) (v : Val) : v ∈ args → BadBv v → BadBv (.con c args)
    | record (r : List (String × Val)) (l : String) (v : Val) : (l, v) ∈ r → BadBv v → BadBv (.record r)
    | tuple1 (v1 v2 : Val) (v3 : Option Val) : BadBv v1 → BadBv (.tuple v1 v2 v3)
    | tuple2 (v1 v2 : Val) (v3 : Option Val) : BadBv v2 → BadBv (.tuple v1 v2 v3)
    | tuple3 (v1 v2 v3 : Val) : BadBv v3 → BadBv (.tuple v1 v2 (some v3))
    | closureE (p : AtPat) (e : Exp) (E : Env) (VE : List (String × Val)) :
        BadBvEnv E → BadBv (.closure p e E VE)
    | closureVE (p : AtPat) (e : Exp) (E : Env) (VE : List (String × Val)) (x : String) (v : Val) :
        (x, v) ∈ VE → BadBv v → BadBv (.closure p e E VE)
    | batch (cs : List Val) (v : Val) : v ∈ cs → BadBv v → BadBv (.batch cs)
    | mapF (f c : Val) : BadBv f → BadBv (.mapE f c)
    | mapC (f c : Val) : BadBv c → BadBv (.mapE f c)
    | prog (r : List (String × Val)) (l : String) (v : Val) : (l, v) ∈ r → BadBv v → BadBv (.prog r)
    | succeed (v : Val) : BadBv v → BadBv (.succeed v)
    | fail (v : Val) : BadBv v → BadBv (.fail v)
    | andThenF (f t : Val) : BadBv f → BadBv (.andThen f t)
    | andThenT (f t : Val) : BadBv t → BadBv (.andThen f t)
    | onErrorF (f t : Val) : BadBv f → BadBv (.onError f t)
    | onErrorT (f t : Val) : BadBv t → BadBv (.onError f t)
    | prim (π : Prim) (args : List Val) (v : Val) : v ∈ args → BadBv v → BadBv (.prim π args)
    /-- inside a leaf, except a boundary value directly under an out leaf -/
    | leaf (m : Mgr) (v : Val) : (¬ ∃ p j, m = .out p ∧ v = .bv j) → BadBv v → BadBv (.leaf m v)
  inductive BadBvEnv : Env → Prop where
    | qe (QE : List (String × Env)) (VE : List (String × Val)) (m : String) (E : Env) :
        (m, E) ∈ QE → BadBvEnv E → BadBvEnv (.mk QE VE)
    | ve (QE : List (String × Env)) (VE : List (String × Val)) (x : String) (v : Val) :
        (x, v) ∈ VE → BadBv v → BadBvEnv (.mk QE VE)
end

/-- Well-formed: no boundary value outside JVal, except as the argument of an out leaf. -/
def _root_.StandardElm.Val.WF (v : Val) : Prop := ¬ BadBv v

/-- An out leaf may carry any boundary value, a byte sequence included (A92). -/
theorem wf_out_leaf (p : String) (j : BVal) : (Val.leaf (.out p) (.bv j)).WF := by
  intro h
  cases h with
  | leaf _ _ hn _ => exact hn ⟨p, j, rfl, rfl⟩

theorem wf_bv_iff (j : BVal) : (Val.bv j).WF ↔ j.isJson = true := by
  constructor
  · intro h
    cases hj : j.isJson
    · exact absurd (BadBv.here j hj) h
    · rfl
  · intro hj h
    cases h with
    | here _ h' => rw [hj] at h' ; cases h'

theorem wf_ofList : ∀ (vs : List Val), (∀ v ∈ vs, v.WF) → (Val.ofList vs).WF
  | [], _ => by
    intro h; simp only [Val.ofList] at h
    cases h with
    | con _ _ v hm _ => simp at hm
  | v :: vs, h => by
    intro hb
    simp only [Val.ofList] at hb
    cases hb with
    | con _ _ w hm hw =>
      simp only [List.mem_cons] at hm
      rcases hm with rfl | rfl | hm
      · exact h w (by simp) hw
      · exact wf_ofList vs (fun x hx => h x (List.mem_cons_of_mem _ hx)) hw
      · simp at hm

end StandardElm.Eff
