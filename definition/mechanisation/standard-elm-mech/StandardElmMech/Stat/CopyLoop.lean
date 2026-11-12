/-
  A Standard Definition of Elm? Mechanisation: the copy loop of number specialisation, plan step 10
  (Theorems, "Copy names and the copy loop").

  sec:dynamic-core-numbers: a declaration with k number variables is replaced by its default copy
  and one copy for each other assignment at which the program uses it; "uses" is read as requested
  by the scope or by a copy already made (A59, A87). `copyLoop` (Specialise.lean) computes that set
  by rounds. Proved here: its result contains the initial assignments and is closed under the
  requests of its copies, and it is the least such set (`copyLoop_least`); with fuel 2^k + 1 it
  does not run out of fuel unless a translation fails (`copyLoop_fuel`); it makes at most 2^k copies
  (`copies_le_pow`, the book's finiteness remark).
-/
import StandardElmMech.Stat.Specialise

namespace StandardElm.Stat

/-! ## Assignments -/

theorem length_flatMap_two {α β : Type} (f g : α → β) :
    ∀ l : List α, (l.flatMap fun a => [f a, g a]).length = 2 * l.length
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      length_flatMap_two f g l]
    omega

theorem allAssignments_length (k : Nat) : (allAssignments k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [allAssignments]
    have := length_flatMap_two (fun a : Assignment => Num.float :: a) (fun a => Num.int :: a) (allAssignments k)
    rw [this, ih, Nat.pow_succ]
    omega

theorem allAssignments_mem_length : ∀ (k : Nat) (a : Assignment), a ∈ allAssignments k → a.length = k
  | 0, a, h => by simp [allAssignments] at h; subst h; rfl
  | k + 1, a, h => by
    simp only [allAssignments, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨b, hb, rfl | rfl⟩ := h <;> simp [allAssignments_mem_length k b hb]

theorem allAssignments_complete : ∀ (a : Assignment), a ∈ allAssignments a.length
  | [] => by simp [allAssignments]
  | n :: a => by
    simp only [List.length_cons, allAssignments, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨a, allAssignments_complete a, by cases n <;> simp⟩

/-- Distinct assignments of length k are at most 2^k. -/
theorem length_le_pow {k : Nat} {l : List Assignment} (hn : l.Nodup) (hk : ∀ a ∈ l, a.length = k) :
    l.length ≤ 2 ^ k := by
  rw [← allAssignments_length k]
  apply hn.length_le_of_subset
  intro a ha
  have := allAssignments_complete a
  rwa [hk a ha] at this

/-! ## `dedupFirst` -/

theorem mem_dedupFirst {α : Type} [DecidableEq α] : ∀ {l : List α} {x : α}, x ∈ dedupFirst l ↔ x ∈ l
  | [], _ => by simp [dedupFirst]
  | y :: ys, x => by
    simp only [dedupFirst, List.mem_cons, List.mem_filter, mem_dedupFirst, decide_eq_true_eq]
    by_cases h : x = y <;> simp [h]

theorem nodup_dedupFirst {α : Type} [DecidableEq α] : ∀ (l : List α), (dedupFirst l).Nodup
  | [] => List.nodup_nil
  | y :: ys => by
    simp only [dedupFirst]
    refine List.nodup_cons.mpr ⟨?_, (nodup_dedupFirst ys).filter _⟩
    simp

/-! ## `translateAll` -/

theorem translateAll_ok {tr : Assignment → Except SpecError (Spec (List D.Def))} :
    ∀ {l : List Assignment} {rs}, translateAll tr l = .ok rs →
      rs.map (·.1) = l ∧ ∀ p ∈ rs, tr p.1 = .ok p.2
  | [], rs, h => by simp only [translateAll, Except.ok.injEq] at h; subst h; simp
  | a :: as, rs, h => by
    simp only [translateAll, bind, Except.bind] at h
    cases ha : tr a with
    | error e => rw [ha] at h; cases h
    | ok s =>
      rw [ha] at h
      simp only at h
      cases hr : translateAll tr as with
      | error e => rw [hr] at h; cases h
      | ok rest =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := translateAll_ok hr
        refine ⟨by simp [h1], ?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ha
        · exact h2 p hp

theorem translateAll_error {tr : Assignment → Except SpecError (Spec (List D.Def))} :
    ∀ {l : List Assignment} {e}, translateAll tr l = .error e → ∃ a ∈ l, tr a = .error e
  | [], e, h => by simp [translateAll] at h
  | a :: as, e, h => by
    simp only [translateAll, bind, Except.bind] at h
    cases ha : tr a with
    | error e' => rw [ha] at h; cases h; exact ⟨a, List.mem_cons_self, ha⟩
    | ok s =>
      rw [ha] at h
      simp only at h
      cases hr : translateAll tr as with
      | error e' =>
        rw [hr] at h; cases h
        obtain ⟨b, hb, hb'⟩ := translateAll_error hr
        exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩
      | ok rest => rw [hr] at h; cases h

/-! ## One round -/

/-- The assignments a round translates. -/
def todoOf (pending : List Assignment) (made : List (Assignment × List D.Def)) : List Assignment :=
  dedupFirst (pending.filter fun a => !(made.any (·.1 == a)))

theorem mem_todoOf {pending : List Assignment} {made : List (Assignment × List D.Def)} {a : Assignment} :
    a ∈ todoOf pending made ↔ a ∈ pending ∧ a ∉ made.map (·.1) := by
  simp only [todoOf, mem_dedupFirst, List.mem_filter, List.mem_map, Bool.not_eq_true',
    List.any_eq_false, beq_iff_eq, Prod.exists, exists_and_right, exists_eq_right, not_exists]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun x hx => h2 _ hx rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun p hp e => h2 p.2 (e ▸ hp)⟩

/-- The copies made after a round. -/
def addMade (made : List (Assignment × List D.Def)) (rs : List (Assignment × Spec (List D.Def))) :
    List (Assignment × List D.Def) :=
  made ++ rs.map fun (a, s) => (a, s.out)

/-- A round: stop when nothing is to be translated, else translate and recur. -/
theorem copyLoop_succ (gid : Nat) (tr : Assignment → Except SpecError (Spec (List D.Def))) (fuel : Nat)
    (pending : List Assignment) (made : List (Assignment × List D.Def)) (out : List Req) :
    copyLoop gid tr (fuel + 1) pending made out =
      if todoOf pending made = [] then .ok (made, out)
      else match translateAll tr (todoOf pending made) with
        | .error e => .error e
        | .ok rs =>
          copyLoop gid tr fuel (((rs.flatMap (·.2.reqs)).filter (·.1 == gid)).map (·.2))
            (addMade made rs) (out ++ (rs.flatMap (·.2.reqs)).filter (·.1 != gid)) := by
  rw [copyLoop]
  unfold todoOf
  cases h : dedupFirst (pending.filter fun a => !(made.any (·.1 == a))) with
  | nil => rfl
  | cons a l =>
    simp only [List.cons_ne_nil, ↓reduceIte]
    simp only [bind, Except.bind, addMade]
    cases translateAll tr (a :: l) <;> rfl

/-- The requests on group `gid` of the copy at assignment `a`, when it translates. -/
def ReqsOn (gid : Nat) (tr : Assignment → Except SpecError (Spec (List D.Def))) (a b : Assignment) : Prop :=
  ∃ s, tr a = .ok s ∧ ∃ r ∈ s.reqs, r.1 = gid ∧ r.2 = b

/-- `M` contains the requests on `gid` of the copies at its assignments. -/
def Closed (gid : Nat) (tr : Assignment → Except SpecError (Spec (List D.Def))) (M : List Assignment) : Prop :=
  ∀ a ∈ M, ∀ b, ReqsOn gid tr a b → b ∈ M

theorem mem_next_pending {gid : Nat} {rs : List (Assignment × Spec (List D.Def))} {b : Assignment} :
    b ∈ ((rs.flatMap (·.2.reqs)).filter (·.1 == gid)).map (·.2) ↔ ∃ p ∈ rs, ∃ r ∈ p.2.reqs, r.1 = gid ∧ r.2 = b := by
  simp only [List.mem_map, List.mem_filter, List.mem_flatMap, beq_iff_eq]
  constructor
  · rintro ⟨r, ⟨⟨p, hp, hr⟩, hg⟩, rfl⟩; exact ⟨p, hp, r, hr, hg, rfl⟩
  · rintro ⟨p, hp, r, hr, hg, rfl⟩; exact ⟨r, ⟨⟨p, hp, hr⟩, hg⟩, rfl⟩

/-! ## The invariant -/

theorem keys_append (made : List (Assignment × List D.Def)) (rs : List (Assignment × Spec (List D.Def))) :
    (addMade made rs).map (·.1) = made.map (·.1) ++ rs.map (·.1) := by
  simp [addMade, Function.comp_def]

/-- What the loop returns: every pending and made assignment is made; the made ones are the least
    set closed under requests above the pending and made ones; and they are closed when the made
    ones' requests are pending or made. -/
theorem copyLoop_inv {gid : Nat} {tr : Assignment → Except SpecError (Spec (List D.Def))} :
    ∀ (fuel : Nat) (pending : List Assignment) (made : List (Assignment × List D.Def)) (out : List Req)
      (madeF : List (Assignment × List D.Def)) (outF : List Req),
    copyLoop gid tr fuel pending made out = .ok (madeF, outF) →
      (∀ a, a ∈ pending ∨ a ∈ made.map (·.1) → a ∈ madeF.map (·.1)) ∧
      (∀ M : List Assignment, (∀ a, a ∈ pending ∨ a ∈ made.map (·.1) → a ∈ M) → Closed gid tr M →
        ∀ a ∈ madeF.map (·.1), a ∈ M) ∧
      ((∀ a ∈ made.map (·.1), ∀ b, ReqsOn gid tr a b → b ∈ pending ∨ b ∈ made.map (·.1)) →
        Closed gid tr (madeF.map (·.1)))
  | 0, _, _, _, _, _, h => by simp [copyLoop] at h
  | fuel + 1, pending, made, out, madeF, outF, h => by
    rw [copyLoop_succ] at h
    by_cases ht : todoOf pending made = []
    · simp only [ht, ↓reduceIte] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp : ∀ a ∈ pending, a ∈ made.map (·.1) := by
        intro a ha
        refine Classical.byContradiction fun hn => ?_
        have : a ∈ todoOf pending made := mem_todoOf.mpr ⟨ha, hn⟩
        rw [ht] at this; cases this
      refine ⟨?_, ?_, ?_⟩
      · rintro a (ha | ha)
        · exact hp a ha
        · exact ha
      · intro M hM _ a ha; exact hM a (.inr ha)
      · intro hc a ha b hb
        rcases hc a ha b hb with hb | hb
        · exact hp b hb
        · exact hb
    · simp only [ht, ↓reduceIte] at h
      cases htr : translateAll tr (todoOf pending made) with
      | error e => rw [htr] at h; cases h
      | ok rs =>
        rw [htr] at h
        simp only at h
        obtain ⟨hkeys, hrs⟩ := translateAll_ok htr
        obtain ⟨ih1, ih2, ih3⟩ := copyLoop_inv fuel _ _ _ madeF outF h
        rw [keys_append, hkeys] at ih1 ih2 ih3
        have hpend : ∀ a ∈ pending, a ∈ made.map (·.1) ++ todoOf pending made := by
          intro a ha
          by_cases hm : a ∈ made.map (·.1)
          · exact List.mem_append_left _ hm
          · exact List.mem_append_right _ (mem_todoOf.mpr ⟨ha, hm⟩)
        refine ⟨?_, ?_, ?_⟩
        · rintro a (ha | ha)
          · exact ih1 a (.inr (hpend a ha))
          · exact ih1 a (.inr (List.mem_append_left _ ha))
        · intro M hM hC
          apply ih2 M _ hC
          rintro a (ha | ha)
          · obtain ⟨p, hp, r, hr, hg, rfl⟩ := (mem_next_pending (gid := gid)).mp ha
            have hp1 : p.1 ∈ todoOf pending made := by rw [← hkeys]; exact List.mem_map_of_mem hp
            exact hC p.1 (hM p.1 (.inl (mem_todoOf.mp hp1).1)) r.2 ⟨p.2, hrs p hp, r, hr, hg, rfl⟩
          · rcases List.mem_append.mp ha with ha | ha
            · exact hM a (.inr ha)
            · exact hM a (.inl (mem_todoOf.mp ha).1)
        · intro hc
          apply ih3
          intro a ha b hb
          rcases List.mem_append.mp ha with ha | ha
          · rcases hc a ha b hb with hb' | hb'
            · exact .inr (hpend b hb')
            · exact .inr (List.mem_append_left _ hb')
          · left
            obtain ⟨s, hs, r, hr, hg, rfl⟩ := hb
            rw [← hkeys] at ha
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
            have : s = p.2 := by rw [hrs p hp] at hs; cases hs; rfl
            subst this
            exact (mem_next_pending (gid := gid)).mpr ⟨p, hp, r, hr, hg, rfl⟩

/-- The copies made: the least set of assignments that contains the initial ones and is closed
    under the requests of the copies it contains (sec:dynamic-core-numbers, A59, A87). -/
theorem copyLoop_least {gid : Nat} {tr : Assignment → Except SpecError (Spec (List D.Def))} {fuel : Nat}
    {init : List Assignment} {made : List (Assignment × List D.Def)} {out : List Req}
    (h : copyLoop gid tr fuel init [] [] = .ok (made, out)) :
    (∀ a ∈ init, a ∈ made.map (·.1)) ∧
    (∀ a ∈ made.map (·.1), ∀ s, tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2 ∈ made.map (·.1)) ∧
    (∀ M : List Assignment, (∀ a ∈ init, a ∈ M) →
       (∀ a ∈ M, ∀ s, tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2 ∈ M) →
       ∀ a ∈ made.map (·.1), a ∈ M) := by
  obtain ⟨h1, h2, h3⟩ := copyLoop_inv fuel init [] [] made out h
  refine ⟨fun a ha => h1 a (.inl ha), ?_, ?_⟩
  · have hc := h3 (by intro a ha; simp at ha)
    intro a ha s hs r hr hg
    exact hc a ha r.2 ⟨s, hs, r, hr, hg, rfl⟩
  · intro M hM hC
    apply h2 M
    · rintro a (ha | ha)
      · exact hM a ha
      · simp at ha
    · rintro a ha b ⟨s, hs, r, hr, hg, rfl⟩
      exact hC a ha s hs r hr hg

/-! ## Fuel and the number of copies -/

/-- The loop's invariant on lengths: made assignments are distinct and of length k. -/
theorem copyLoop_lengths {gid k : Nat} {tr : Assignment → Except SpecError (Spec (List D.Def))}
    (htr : ∀ a s, a.length = k → tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2.length = k) :
    ∀ (fuel : Nat) (pending : List Assignment) (made : List (Assignment × List D.Def)) (out : List Req),
    (∀ a ∈ pending, a.length = k) → (∀ a ∈ made.map (·.1), a.length = k) → (made.map (·.1)).Nodup →
      (made.length + fuel > 2 ^ k → copyLoop gid tr fuel pending made out ≠ .error .copyFuel ∨
        ∃ a e, tr a = .error e) ∧
      (∀ madeF outF, copyLoop gid tr fuel pending made out = .ok (madeF, outF) →
        (∀ a ∈ madeF.map (·.1), a.length = k) ∧ (madeF.map (·.1)).Nodup)
  | 0, _, made, _, _, hm, hn => by
    refine ⟨fun hgt => ?_, fun _ _ h => by simp [copyLoop] at h⟩
    have := length_le_pow hn hm
    simp at this; omega
  | fuel + 1, pending, made, out, hp, hm, hn => by
    rw [copyLoop_succ]
    by_cases ht : todoOf pending made = []
    · simp only [ht, ↓reduceIte]
      refine ⟨fun _ => .inl (by simp), fun madeF outF h => ?_⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hm, hn⟩
    · simp only [ht, ↓reduceIte]
      cases htr' : translateAll tr (todoOf pending made) with
      | error e =>
        obtain ⟨a, -, ha⟩ := translateAll_error htr'
        exact ⟨fun _ => .inr ⟨a, e, ha⟩, fun _ _ h => by cases h⟩
      | ok rs =>
        simp only
        obtain ⟨hkeys, hrs⟩ := translateAll_ok htr'
        have hm' : ∀ a ∈ (addMade made rs).map (·.1), a.length = k := by
          rw [keys_append, hkeys]
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hm a ha
          · exact hp a (mem_todoOf.mp ha).1
        have hn' : ((addMade made rs).map (·.1)).Nodup := by
          rw [keys_append, hkeys]
          refine List.nodup_append.mpr ⟨hn, nodup_dedupFirst _, ?_⟩
          intro a ha b hb e
          subst e
          exact (mem_todoOf.mp hb).2 ha
        have hp' : ∀ b ∈ ((rs.flatMap (·.2.reqs)).filter (·.1 == gid)).map (·.2), b.length = k := by
          intro b hb
          obtain ⟨p, hpm, r, hr, hg, rfl⟩ := (mem_next_pending (gid := gid)).mp hb
          have hp1 : p.1 ∈ todoOf pending made := by rw [← hkeys]; exact List.mem_map_of_mem hpm
          exact htr p.1 p.2 (hp p.1 (mem_todoOf.mp hp1).1) (hrs p hpm) r hr hg
        obtain ⟨ih1, ih2⟩ := copyLoop_lengths htr fuel _ _ (out ++ (rs.flatMap (·.2.reqs)).filter (·.1 != gid)) hp' hm' hn'
        refine ⟨fun hgt => ih1 ?_, ih2⟩
        have hlen : rs.length ≥ 1 := by
          cases rs with
          | nil => simp at hkeys; exact absurd hkeys ht
          | cons _ _ => simp
        simp only [addMade, List.length_append, List.length_map]
        omega

/-- With fuel 2^k + 1 the loop does not run out of fuel unless a translation fails. -/
theorem copyLoop_fuel {gid k : Nat} {tr : Assignment → Except SpecError (Spec (List D.Def))}
    {init : List Assignment} (hk : ∀ a ∈ init, a.length = k)
    (htr : ∀ a s, a.length = k → tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2.length = k) :
    copyLoop gid tr (2 ^ k + 1) init [] [] ≠ .error .copyFuel ∨ ∃ a e, tr a = .error e :=
  (copyLoop_lengths htr (2 ^ k + 1) init [] [] hk (by simp) List.nodup_nil).1 (by simp)

/-- At most 2^k copies (the book's finiteness remark), and distinct. -/
theorem copies_le_pow {gid k : Nat} {tr : Assignment → Except SpecError (Spec (List D.Def))}
    {fuel : Nat} {init : List Assignment} {made : List (Assignment × List D.Def)} {out : List Req}
    (h : copyLoop gid tr fuel init [] [] = .ok (made, out)) (hk : ∀ a ∈ init, a.length = k)
    (htr : ∀ a s, a.length = k → tr a = .ok s → ∀ r ∈ s.reqs, r.1 = gid → r.2.length = k) :
    (made.map (·.1)).Nodup ∧ made.length ≤ 2 ^ k := by
  obtain ⟨hl, hn⟩ := (copyLoop_lengths htr fuel init [] [] hk (by simp) List.nodup_nil).2 made out h
  refine ⟨hn, ?_⟩
  have := length_le_pow hn hl
  simpa using this

end StandardElm.Stat
