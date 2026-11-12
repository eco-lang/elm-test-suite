/-
  A Standard Definition of Elm? Mechanisation: finite maps for the static semantics, plan step 9.

  A finite map A ⇀ B (sec:static-core-compound) is an association list; a key is looked up at its
  first occurrence. `f + g`, f modified by g, is g followed by the pairs of f whose keys g does not
  bind, so a map built only by modification has each key once. Every function is structurally
  recursive, so that the kernel reduces it.
-/

namespace StandardElm.Stat

abbrev FMap (K V : Type) := List (K × V)

namespace FMap

variable {K V : Type} [DecidableEq K]

def find? : FMap K V → K → Option V
  | [], _ => none
  | (k', v) :: r, k => if k' = k then some v else find? r k

def keys (f : FMap K V) : List K := f.map (·.1)
def vals (f : FMap K V) : List V := f.map (·.2)

def mem (f : FMap K V) (k : K) : Bool := (f.find? k).isSome

/-- f + g (sec:static-core-compound). -/
def modify (f g : FMap K V) : FMap K V :=
  g ++ f.filter fun p => !decide (p.1 ∈ g.keys)

/-- VE_1 + ... + VE_n, from the left. -/
def plusAll (fs : List (FMap K V)) : FMap K V := fs.foldl modify []

def mapV {W : Type} (f : FMap K V) (g : V → W) : FMap K W := f.map fun p => (p.1, g p.2)

/-- f ⊆ g as sets of pairs, on the keys of f (first occurrences). -/
def Sub [DecidableEq V] (f g : FMap K V) : Prop := ∀ k v, f.find? k = some v → g.find? k = some v

@[simp] theorem find?_nil (k : K) : find? ([] : FMap K V) k = none := rfl

theorem find?_cons (k k' : K) (v : V) (r : FMap K V) :
    find? ((k', v) :: r) k = if k' = k then some v else find? r k := rfl

theorem find?_append (f g : FMap K V) (k : K) :
    find? (f ++ g) k = (find? f k).or (find? g k) := by
  induction f with
  | nil => simp [find?]
  | cons p r ih =>
    obtain ⟨k', v⟩ := p
    simp only [List.cons_append, find?]
    split <;> simp [ih]

theorem find?_filter_not (f : FMap K V) (ks : List K) (k : K) (hk : k ∉ ks) :
    find? (f.filter fun p => !decide (p.1 ∈ ks)) k = find? f k := by
  induction f with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k', v⟩ := p
    rw [List.filter_cons]
    by_cases hc : k' ∈ ks
    · have : k' ≠ k := fun e => hk (e ▸ hc)
      simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, find?, this]
    · simp only [hc, decide_false, Bool.not_false, ↓reduceIte, find?, ih]

theorem find?_isSome_iff (f : FMap K V) (k : K) : (find? f k).isSome ↔ k ∈ f.keys := by
  induction f with
  | nil => simp [find?, keys]
  | cons p r ih =>
    obtain ⟨k', v⟩ := p
    simp only [find?, keys, List.map_cons, List.mem_cons]
    split
    · rename_i h; subst h; simp
    · rename_i h; simp only [keys] at ih; rw [ih]; constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm h
        · exact e

theorem find?_modify (f g : FMap K V) (k : K) :
    find? (modify f g) k = (find? g k).or (find? f k) := by
  unfold modify
  rw [find?_append]
  cases hg : find? g k with
  | some v => simp
  | none =>
    have : k ∉ g.keys := fun h => by
      have := (find?_isSome_iff g k).mpr h; rw [hg] at this; cases this
    simpa using find?_filter_not f g.keys k this

end FMap

end StandardElm.Stat
