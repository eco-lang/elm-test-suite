/-
  A Standard Definition of Elm? Mechanisation: flattening of commands and subscriptions (effects.tex,
  sec:effects-commands), plan step 4.

  Flat(c) is the multiset of leaf commands map(vn, ... map(v1, leaf(m, v)) ...) of c: a batch
  contributes the leaves of its components, a map maps each leaf of its command. It is given as a
  list in the order of the batches' components; the book's multiset is this list up to
  permutation.
-/
import StandardElmMech.Objects

namespace StandardElm.Eff
open StandardElm

mutual
  /-- Flat(c); `none` for a value that is not a command or subscription. -/
  def flat : Val → Option (List Val)
    | .batch cs => flatList cs
    | .mapE f c => (flat c).map (·.map (.mapE f))
    | .leaf m v => some [.leaf m v]
    | _ => none
  def flatList : List Val → Option (List Val)
    | [] => some []
    | c :: cs =>
      match flat c, flatList cs with
      | some a, some b => some (a ++ b)
      | _, _ => none
end

/-- The manager and argument of a leaf command map(vn, ... map(v1, leaf(m, v)) ...). -/
def leafCore : Val → Option (Mgr × Val)
  | .mapE _ c => leafCore c
  | .leaf m v => some (m, v)
  | _ => none

theorem leafCore_mapE_map {f : Val} {cs : List Val} (h : ∀ c ∈ cs, (leafCore c).isSome) :
    ∀ c ∈ cs.map (Val.mapE f), (leafCore c).isSome := by
  intro c hm
  simp only [List.mem_map] at hm
  obtain ⟨c0, h0, rfl⟩ := hm
  simpa [leafCore] using h c0 h0

mutual
  /-- Every member of Flat(c) is a leaf command, maps around a leaf. -/
  theorem flat_leaves : ∀ {c : Val} {cs : List Val}, flat c = some cs → ∀ c' ∈ cs, (leafCore c').isSome
    | .batch ds, cs, h => flatList_leaves (by simpa [flat] using h)
    | .mapE f c, cs, h => by
      simp only [flat] at h
      cases hc : flat c with
      | none => simp [hc] at h
      | some ds =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        subst h
        exact leafCore_mapE_map (flat_leaves hc)
    | .leaf m v, cs, h => by
      simp only [flat, Option.some.injEq] at h
      subst h
      simp [leafCore]
    | .unit, _, h | .sv _, _, h | .basApp _ _, _, h | .con _ _, _, h | .record _, _, h
    | .tuple _ _ _, _, h | .closure _ _ _ _, _, h | .prog _, _, h | .succeed _, _, h
    | .fail _, _, h | .andThen _ _, _, h | .onError _ _, _, h | .prim _ _, _, h | .pid _, _, h
    | .bv _, _, h => by simp [flat] at h
  theorem flatList_leaves : ∀ {ds : List Val} {cs : List Val}, flatList ds = some cs →
      ∀ c' ∈ cs, (leafCore c').isSome
    | [], cs, h => by simp [flatList] at h; subst h; simp
    | d :: ds, cs, h => by
      simp only [flatList] at h
      cases hd : flat d with
      | none => simp [hd] at h
      | some a =>
        cases hds : flatList ds with
        | none => simp [hd, hds] at h
        | some b =>
          simp only [hd, hds, Option.some.injEq] at h
          subst h
          intro c' hm
          rcases List.mem_append.mp hm with hm | hm
          · exact flat_leaves hd c' hm
          · exact flatList_leaves hds c' hm
end

/-- Cmd.none, and a batch of nones, flatten to the empty multiset. -/
theorem flat_none : flat (.batch []) = some [] ∧ flat (.batch [.batch [], .batch []]) = some [] := by
  simp [flat, flatList]

end StandardElm.Eff
