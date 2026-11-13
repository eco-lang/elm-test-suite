/-
  A Standard Definition of Elm? Mechanisation: the generalisation lemma L3 of plan step 11 with
  rows (milestone (d), section 8), for the closure of a group (A93's `closGroup`, through
  `canon`'s renumbering), for substitutions of type and row variables (Closure.lean for `RSub`).

  Step 9's canonical form renumbers the bound variables (type or row) to `bnd 0, bnd 1, ...`
  (`renumber`); read through the bridge (WDBridge.lean), it is `rsb` of a renaming
  (`canon_eqD`, `renumber_img`). `closE_relD` is L3: `T (Clos_A τ) ≻ Clos_A' (T τ)` when the free
  variables of `T A` are in `A'`, and `closE_schWD`: a closure is a scheme W can hold.
-/
import StandardElmMech.Stat.Complete.WDState

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## `renumber` as a renaming -/

/-- The `bnd` variable of index `k` of the sort (and class) of `v`. -/
def bndV (k : Nat) : BVar → BVar
  | .ty a => .ty (.bnd k a.cls)
  | .row _ => .row (.bnd k)

theorem bndV_isBnd (k : Nat) (v : BVar) : (bndV k v).isBnd = true := by
  cases v <;> rfl

theorem renumber_img : ∀ (i : Nat) (vs : List BVar) (v : BVar),
    (renumber true i vs).1.toR.img v = if v ∈ vs then vty (bndV (i + vs.idxOf v) v) else vty v
  | _, [], v => by
    simp only [renumber, List.not_mem_nil, if_false]
    cases v <;> rfl
  | i, .ty a :: vs, v => by
    have ih := renumber_img (i + 1) vs v
    simp only [renumber, ↓reduceIte] at ih ⊢
    by_cases e : v = .ty a
    · subst e; simp [RSub.img, Subst.toR, FMap.find?, vty, bndV]
    · have hS : (Subst.toR { (renumber true (i + 1) vs).1 with
          ty := (a, Ty.var (TyVar.bnd i a.cls)) :: (renumber true (i + 1) vs).1.ty }).img v =
          (renumber true (i + 1) vs).1.toR.img v := by
        cases v with
        | ty b =>
          have : b ≠ a := fun h => e (by rw [h])
          simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
        | row _ => rfl
      rw [hS, ih]
      by_cases hm : v ∈ vs
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm), List.idxOf_cons, if_neg (by simpa using Ne.symm e)]
        congr 2; omega
      · rw [if_neg hm, if_neg (by simp [e, hm])]
  | i, .row e0 :: vs, v => by
    have ih := renumber_img (i + 1) vs v
    simp only [renumber] at ih ⊢
    by_cases e : v = .row e0
    · subst e; simp [RSub.img, Subst.toR, FMap.find?, vty, bndV]
    · have hS : (Subst.toR { (renumber true (i + 1) vs).1 with
          row := (e0, ([], some (RowVar.bnd i))) :: (renumber true (i + 1) vs).1.row }).img v =
          (renumber true (i + 1) vs).1.toR.img v := by
        cases v with
        | row b =>
          have : b ≠ e0 := fun h => e (by rw [h])
          simp [RSub.img, Subst.toR, FMap.find?, Ne.symm this]
        | ty _ => rfl
      rw [hS, ih]
      by_cases hm : v ∈ vs
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm), List.idxOf_cons, if_neg (by simpa using Ne.symm e)]
        congr 2; omega
      · rw [if_neg hm, if_neg (by simp [e, hm])]

theorem renumber_bound : ∀ (i : Nat) (vs : List BVar) (x : BVar), x ∈ (renumber true i vs).2 →
    ∃ j, ∃ hj : j < vs.length, x = bndV (i + j) vs[j]
  | _, [], x, h => by simp [renumber] at h
  | i, v :: vs, x, h => by
    have hx : x = bndV i v ∨ x ∈ (renumber true (i + 1) vs).2 := by
      cases v <;> simp only [renumber, List.mem_cons, ↓reduceIte] at h <;> rcases h with h | h
      all_goals first | exact .inl h | exact .inr h
    rcases hx with rfl | hx
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨j, hj, hx⟩ := renumber_bound (i + 1) vs x hx
      exact ⟨j + 1, by simp; omega, by rw [hx]; simp [show i + 1 + j = i + (j + 1) by omega]⟩

theorem renumber_mem : ∀ (i : Nat) (vs : List BVar) (v : BVar), v ∈ vs →
    bndV (i + vs.idxOf v) v ∈ (renumber true i vs).2
  | _, [], _, h => by cases h
  | i, w :: vs, v, h => by
    by_cases e : w = v
    · subst e; cases w <;> simp [renumber, bndV]
    · have hm : v ∈ vs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      have := renumber_mem (i + 1) vs v hm
      rw [List.idxOf_cons, if_neg (by simpa using e), show i + (vs.idxOf v + 1) = i + 1 + vs.idxOf v by omega]
      cases w <;> simp only [renumber, List.mem_cons] <;> exact .inr this

/-- The canonical form of a scheme, read as a renaming. -/
theorem canon_eqD (bs : List BVar) (body : Ty) :
    Scheme.canon ⟨bs, body⟩ = ⟨(renumber true 0 (canonVars bs body)).2,
      rsb (renumber true 0 (canonVars bs body)).1.toR body⟩ := by
  obtain ⟨h1, -, -⟩ := renumber_spec true 0 (canonVars bs body)
  obtain ⟨τ', hτ'⟩ := apply_isSome h1 body
  simp only [Scheme.canon, hτ', Option.getD_some, apply_eq_rsb _ _ _ hτ']

/-- The bound variable a `bnd` variable of a canonical form stands for. -/
def pickB (vs : List BVar) : BVar → Option BVar
  | .ty (.bnd j c) =>
    match vs[j]? with
    | some (.ty a) => if a.cls = c then some (.ty a) else none
    | _ => none
  | .row (.bnd j) =>
    match vs[j]? with
    | some (.row e) => some (.row e)
    | _ => none
  | _ => none

theorem pickB_inst {vs : List BVar} {v : BVar} (h : v ∈ vs) : pickB vs (bndV (0 + vs.idxOf v) v) = some v := by
  have hl := List.idxOf_lt_length_of_mem h
  have hg : vs[vs.idxOf v]? = some v := by
    rw [List.getElem?_eq_getElem hl, List.getElem_idxOf]
  cases v with
  | ty a => simp [pickB, bndV, hg]
  | row e => simp [pickB, bndV, hg]

theorem pickB_bound {vs : List BVar} {x : BVar} (h : x ∈ (renumber true 0 vs).2) :
    ∃ v ∈ vs, pickB vs x = some v ∧ (∀ a, v = .ty a → ∃ j, x = .ty (.bnd j a.cls)) ∧
      (∀ e, v = .row e → ∃ j, x = .row (.bnd j)) := by
  obtain ⟨j, hj, rfl⟩ := renumber_bound 0 vs x h
  have hg : vs[j]? = some vs[j] := List.getElem?_eq_getElem hj
  refine ⟨vs[j], List.getElem_mem hj, ?_, ?_, ?_⟩
  · cases hv : vs[j] with
    | ty a => simp [pickB, bndV, hg, hv]
    | row e => simp [pickB, bndV, hg, hv]
  · intro a ha; rw [ha]; exact ⟨0 + j, rfl⟩
  · intro e he; rw [he]; exact ⟨0 + j, rfl⟩

/-! ## The closure of a group's member -/

theorem closB_not_mem {A : List BVar} {VE : ValEnv} {τ : Ty} {v : BVar} (hv : v ∈ A) : v ∉ closB A VE (mono τ) := by
  simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL,
    decide_eq_false_iff_not, Bool.not_eq_true', not_or, not_and, List.mem_append]
  exact ⟨fun _ h => h hv, fun h => absurd hv h.2.2⟩

/-- A variable of `τ` (not `bnd`) outside the closure's bound list is in `A`. -/
theorem inA_of {A : List BVar} {VE : ValEnv} {τ : Ty} {c : BVar} (hc : c ∈ τ.vars) (hb : c.isBnd = false)
    (hn : c ∉ canonVars (closB A VE (mono τ)) τ) : c ∈ A := by
  rw [mem_canonVars_iff hc] at hn
  refine Classical.byContradiction fun hA' => ?_
  apply hn
  simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL,
    mem_tyvars_iff, decide_eq_false_iff_not, Bool.not_eq_true']
  exact .inl ⟨⟨hc, hb⟩, hA'⟩

/-- L3 for a member of a group: the closure in W's context is related to the closure of its
    image in the derivation's context. -/
theorem closE_relD {A A' : List BVar} {VE VE' : ValEnv} {τ : Ty} {T : RSub} {n : Nat}
    (hτ : OkTD n τ) (hTadm : RespR T)
    (hA : ∀ w ∈ A, w ∈ τ.vars → ∀ v ∈ (T.img w).tyvars, v ∈ A')
    (hNB : ∀ v ∈ (rsb T τ).vars, v.isBnd = false) :
    SchRelD T (closE A VE (mono τ)) (closE A' VE' (mono (rsb T τ))) := by
  unfold closE
  simp only [mono_body]
  rw [canon_eqD, canon_eqD]
  generalize hcv0 : canonVars (closB A VE (mono τ)) τ = cv0
  generalize hcv1 : canonVars (closB A' VE' (mono (rsb T τ))) (rsb T τ) = cv1
  have hR0 := renumber_img 0 cv0
  have hR1 := renumber_img 0 cv1
  -- the images under T of variables of τ in A are fixed by the derivation's renaming
  have hfix : ∀ c ∈ τ.vars, c ∈ A → ∀ v ∈ (T.img c).vars, v ∉ cv1 ∧ v.isBnd = false := by
    intro c hc hcA v hv
    have hnb : v.isBnd = false := hNB v ((mem_vars_rsb T τ v).mpr ⟨c, hc, hv⟩)
    have hA'v : v ∈ A' := hA c hcA hc v (mem_tyvars_iff.mpr ⟨hv, hnb⟩)
    refine ⟨fun hm => ?_, hnb⟩
    rw [← hcv1] at hm
    exact closB_not_mem hA'v (mem_canonVars hm)
  have inA : ∀ c ∈ τ.vars, c ∉ cv0 → c ∈ A := fun c hc hn =>
    inA_of hc (hτ c hc).1 (by rw [hcv0]; exact hn)
  refine ⟨?_, ?_⟩
  · -- FtvRelD
    intro w hw v hv
    simp only [Scheme.tyvars, diffL, List.mem_filter, mem_tyvars_iff, Bool.not_eq_true',
      decide_eq_false_iff_not] at hw ⊢
    obtain ⟨⟨hw1, hw2⟩, -⟩ := hw
    obtain ⟨c, hc, hwc⟩ := (mem_vars_rsb _ τ w).mp hw1
    rw [hR0] at hwc
    split at hwc
    · rw [vars_vty, List.mem_singleton] at hwc; subst hwc; rw [bndV_isBnd] at hw2; cases hw2
    · rename_i hn
      rw [vars_vty, List.mem_singleton] at hwc; subst hwc
      have hcA := inA w hc hn
      obtain ⟨hv1, hv2⟩ := mem_tyvars_iff.mp hv
      obtain ⟨hv3, -⟩ := hfix w hc hcA v hv1
      refine ⟨⟨(mem_vars_rsb _ _ v).mpr ⟨v, (mem_vars_rsb T τ v).mpr ⟨w, hc, hv1⟩, ?_⟩, hv2⟩, ?_⟩
      · rw [hR1, if_neg hv3, vars_vty]; exact List.mem_singleton_self _
      · intro hb
        obtain ⟨j, hj, hx⟩ := renumber_bound 0 cv1 v hb
        rw [hx, bndV_isBnd] at hv2; cases hv2
  · -- every instance of the image's closure is an instance of the closure under T
    intro t hg
    obtain ⟨g2, hr2, hout2, rfl⟩ := gen_rsb hg
    simp only at hout2 ⊢
    have hRN1 : RespR (renumber true 0 cv1).1.toR := respR_toR (renumber_respectsC 0 cv1)
    let h : RSub := rcomp (rcomp g2 (renumber true 0 cv1).1.toR) T
    have hh : RespR h := respR_rcomp hTadm (respR_rcomp hRN1 hr2)
    -- on the variables in A, h is T
    have hpost : ∀ c ∈ τ.vars, c ∈ A → h.img c = T.img c := by
      intro c hc hcA
      simp only [h, img_rcomp, ← rsb_rsb]
      rw [rsb_eq_self (s := (renumber true 0 cv1).1.toR) fun v hv => by
        rw [hR1, if_neg (hfix c hc hcA v hv).1]]
      exact rsb_eq_self fun v hv => hout2 v fun hb => by
        obtain ⟨j, hj, hx⟩ := renumber_bound 0 cv1 v hb
        have := (hfix c hc hcA v hv).2; rw [hx, bndV_isBnd] at this; cases this
    let f : BVar → Ty := fun b => match pickB cv0 b with
      | some v => h.img v
      | none => vty b
    have hf : ∀ e, ∃ ρ tl, f (.row e) = .record ρ tl := fun e => by
      simp only [f]; split
      · rename_i v hv
        cases v with
        | row e' => exact img_row_record h e'
        | ty a =>
          exfalso
          rcases e with (_ | _ | j) <;> simp only [pickB, reduceCtorEq] at hv
          split at hv <;> cases hv
      · exact ⟨[], some e, rfl⟩
    have hT : ∀ w, (ofImg f).img w = f w := ofImg_img hf
    refine ⟨ofImg f, fun a ha => ?_, ?_⟩
    · obtain ⟨v, hv, hp, hk, hk'⟩ := pickB_bound ha
      show Adm a.cls (f (.ty a))
      simp only [f, hp]
      cases v with
      | ty b =>
        obtain ⟨j, hj⟩ := hk b rfl
        injection hj with hj; subst hj
        exact hh b
      | row e => obtain ⟨j, hj⟩ := hk' e rfl; cases hj
    · rw [rsb_rsb, rsb_rsb, rsb_rsb]
      apply rsb_congr
      intro c hc
      simp only [img_rcomp]
      rw [hR0]
      split
      · rename_i hm
        rw [rsb_vty, extS_img, if_pos (renumber_mem 0 cv0 c hm), hT]
        simp only [f, pickB_inst hm, h, img_rcomp]
      · rename_i hm
        rw [rsb_vty, extS_img, if_neg]
        · have := hpost c hc (inA c hc hm); simp only [h, img_rcomp] at this; exact this
        · intro hb
          obtain ⟨j, hj, hx⟩ := renumber_bound 0 cv0 c hb
          have := (hτ c hc).1; rw [hx, bndV_isBnd] at this; cases this

/-- The closure of a member is a scheme W can put in its context. -/
theorem closE_schWD {A : List BVar} {VE : ValEnv} {τ : Ty} {n : Nat} (hτ : OkTD n τ) :
    SchWD n (closE A VE (mono τ)) := by
  unfold closE
  simp only [mono_body]
  rw [canon_eqD]
  refine ⟨fun v hv => by obtain ⟨j, hj, hx⟩ := renumber_bound 0 _ v hv; rw [hx]; exact bndV_isBnd _ _, fun v hv hb => ?_⟩
  obtain ⟨c, hc, hv'⟩ := (mem_vars_rsb _ τ v).mp hv
  rw [renumber_img] at hv'
  split at hv'
  · rename_i hm
    rw [vars_vty, List.mem_singleton] at hv'; subst hv'
    exact absurd (renumber_mem 0 _ c hm) hb
  · rw [vars_vty, List.mem_singleton] at hv'; subst hv'
    exact hτ _ hc

end StandardElm.Stat.Complete
