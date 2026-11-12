/-
  A Standard Definition of Elm? Mechanisation: the canonical grouping of definitions, plan step 8
  (section 3.3, finding B4). The book's derived forms of a `let` and of a module group the
  definitions into the classes of mutual reachability of "refers to" and order the groups so that
  each comes after the groups it refers to (sec:appendix-derived-forms-let); among the orders the
  book allows, `components` picks one: among the groups ready to be placed, the one with the least
  member first. Derived.lean's `letDefs` and the module form (Mod/Program.lean) use it; step 8's
  `deriveLet` and `deriveTopDecs` too. `ValidNumbering` is the book's relation.
-/
import StandardElmMech.Src.Graph

namespace StandardElm.Src.Grouping
open StandardElm.Src.Graph

/-- The members reachable from each node in zero or more steps, computed once. -/
def reachTable (n : Nat) (refers : Nat → Nat → Bool) : List (List Nat) :=
  (List.range n).map fun a => a :: plusSet n refers a

def reachIn (table : List (List Nat)) (a b : Nat) : Bool := (table.getD a []).contains b

/-- The classes of mutual reachability, each sorted, in the order of their least members. -/
def classes (n : Nat) (refers : Nat → Nat → Bool) : List (List Nat) :=
  let t := reachTable n refers
  (List.range n).foldl (fun acc a =>
    if acc.any (fun cmp => cmp.contains a) then acc
    else acc ++ [(List.range n).filter (fun b => reachIn t a b && reachIn t b a)]) []

/-- A group may be placed when every member refers only to members of the group or of the groups
    already placed. -/
def ready (n : Nat) (refers : Nat → Nat → Bool) (placed : List (List Nat)) (cmp : List Nat) : Bool :=
  cmp.all fun a => (List.range n).all fun b =>
    !(refers a b) || cmp.contains b || placed.any (fun p => p.contains b)

def place (n : Nat) (refers : Nat → Nat → Bool) : Nat → List (List Nat) → List (List Nat) → List (List Nat)
  | 0, placed, _ => placed
  | k + 1, placed, todo =>
    match todo.find? (ready n refers placed) with
    | some cmp => place n refers k (placed ++ [cmp]) (todo.filter (· != cmp))
    | none => placed

/-- The components of the graph on `0 .. n-1` whose edges are `refers`, each as its members in
    increasing order, listed so that a component comes after every component it refers to; among
    the components that may be placed next, the one with the least member comes first. -/
def components (n : Nat) (refers : Nat → Nat → Bool) : List (List Nat) :=
  place n refers (n + 1) [] (classes n refers)

/-- The book's relation (sec:appendix-derived-forms-let): `cs` partitions `0 .. n-1` into the
    classes of mutual reachability, each class sorted, and whenever a member of `cs[a]` refers to
    a member of `cs[b]` with `b ≠ a`, then `b < a`. -/
def ValidNumbering (n : Nat) (refers : Nat → Nat → Bool) (cs : List (List Nat)) : Prop :=
  (cs.flatten.Perm (List.range n)) ∧
  (∀ c ∈ cs, c.Pairwise (· < ·) ∧ c ≠ []) ∧
  (∀ c ∈ cs, ∀ i ∈ c, ∀ j < n, (Reach n refers i j ∧ Reach n refers j i) ↔ j ∈ c) ∧
  (∀ a b (ha : a < cs.length) (hb : b < cs.length), a ≠ b →
      (∃ i ∈ cs[a], ∃ j ∈ cs[b], refers i j = true) → b < a)

end StandardElm.Src.Grouping
