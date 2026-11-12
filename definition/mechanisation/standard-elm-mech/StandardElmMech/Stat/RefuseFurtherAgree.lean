/-
  A Standard Definition of Elm? Mechanisation: refusals by the further restrictions, part 1 (plan
  step 9, milestone 9d, "head forcing"). The verdict of the pattern decider does not depend on the
  type the patterns are judged at, among the types at which they fit with forced heads.

  `fitsB tbl τ p`: every constructor pattern in p stands at a constructed type (not a literal one)
  whose constructors are, by name, those of the first type in the table that has the pattern's
  constructor (`sibs`), and its arguments fit the argument types the table gives. Constants do not
  fit (the deciders of RefuseFurther.lean treat them apart). `useful_agree`: Maranget's algorithm
  gives the same answer at two column types at which the same rows fit. `con_fits`: a constructor
  pattern that the checker types by a scheme of a constructor the table agrees with (`schemeOKB`)
  fits at the type the checker gives it.
-/
import StandardElmMech.Stat.Refusals

namespace StandardElm.Stat.RFurther

/-! ## Fitting patterns -/

/-- The constructor names of the first type of the table that has a constructor k. -/
def sibs (tbl : ConTable) (k : String) : List String :=
  ((tbl.find? (fun e => e.2.any (·.1 == k))).map (fun e => e.2.map (·.1))).getD []

mutual
def fitsB (tbl : ConTable) : Ty → PatN → Bool
  | _, .wild => true
  | _, .den _ => false
  | τ, .con k args =>
    (litKind τ).isNone && decide ((ctorsAt tbl τ).map (·.1) = sibs tbl k) &&
    (match argTys tbl τ k with
     | some as => fitsListB tbl as args
     | none => false)
def fitsListB (tbl : ConTable) : List Ty → List PatN → Bool
  | [], [] => true
  | τ :: τs, p :: ps => fitsB tbl τ p && fitsListB tbl τs ps
  | _, _ => false
end

theorem fitsB_con {tbl : ConTable} {τ : Ty} {k : String} {args : List PatN} (h : fitsB tbl τ (.con k args) = true) :
    litKind τ = none ∧ (ctorsAt tbl τ).map (·.1) = sibs tbl k ∧
      ∃ as, argTys tbl τ k = some as ∧ fitsListB tbl as args = true := by
  simp only [fitsB, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i as has; exact ⟨as, has, h3⟩
  · cases h3

theorem fitsB_of {tbl : ConTable} {τ : Ty} {k : String} {args : List PatN} {as : List Ty}
    (h1 : litKind τ = none) (h2 : (ctorsAt tbl τ).map (·.1) = sibs tbl k) (h3 : argTys tbl τ k = some as)
    (h4 : fitsListB tbl as args = true) : fitsB tbl τ (.con k args) = true := by
  simp [fitsB, h1, h2, h3, h4]

theorem fitsB_den {tbl : ConTable} {τ : Ty} {d : Den} : fitsB tbl τ (.den d) = false := by simp [fitsB]

theorem fitsListB_cons {tbl : ConTable} {τ : Ty} {τs : List Ty} {p : PatN} {ps : List PatN} :
    fitsListB tbl (τ :: τs) (p :: ps) = (fitsB tbl τ p && fitsListB tbl τs ps) := by simp [fitsListB]

theorem fitsListB_length {tbl : ConTable} : ∀ {τs : List Ty} {ps : List PatN}, fitsListB tbl τs ps = true →
    τs.length = ps.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [fitsListB, Bool.and_eq_true] at h
    simp [fitsListB_length h.2]
  | [], _ :: _, h => by simp [fitsListB] at h
  | _ :: _, [], h => by simp [fitsListB] at h

theorem fitsListB_append {tbl : ConTable} : ∀ {τs1 τs2 : List Ty} {ps1 ps2 : List PatN},
    fitsListB tbl τs1 ps1 = true → fitsListB tbl τs2 ps2 = true → fitsListB tbl (τs1 ++ τs2) (ps1 ++ ps2) = true
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, h1, h2 => by
    simp only [fitsListB, Bool.and_eq_true, List.cons_append] at h1 ⊢
    exact ⟨h1.1, fitsListB_append h1.2 h2⟩
  | [], _, _ :: _, _, h1, _ => by simp [fitsListB] at h1
  | _ :: _, _, [], _, h1, _ => by simp [fitsListB] at h1

theorem fitsListB_wilds {tbl : ConTable} : ∀ (τs : List Ty), fitsListB tbl τs (List.replicate τs.length .wild) = true
  | [] => rfl
  | _ :: τs => by simp [List.replicate, fitsListB, fitsB, fitsListB_wilds τs]

mutual
theorem ptyped_of_fits (tbl : ConTable) : ∀ (τ : Ty) (p : PatN), fitsB tbl τ p = true → PTyped tbl τ p
  | _, .wild, _ => by simp [PTyped]
  | _, .den _, h => by simp [fitsB] at h
  | τ, .con k args, h => by
    obtain ⟨h1, _, as, has, hargs⟩ := fitsB_con h
    simp only [PTyped]
    exact ⟨by simp [h1], as, has, ptypedList_of_fits tbl as args hargs⟩
theorem ptypedList_of_fits (tbl : ConTable) : ∀ (τs : List Ty) (ps : List PatN), fitsListB tbl τs ps = true →
    PTypedList tbl τs ps
  | [], [], _ => by simp [PTypedList]
  | τ :: τs, p :: ps, h => by
    simp only [fitsListB, Bool.and_eq_true] at h
    simp only [PTypedList]
    exact ⟨ptyped_of_fits tbl τ p h.1, ptypedList_of_fits tbl τs ps h.2⟩
  | [], _ :: _, h => by simp [fitsListB] at h
  | _ :: _, [], h => by simp [fitsListB] at h
end

/-! ## Rows after specialisation and in the default matrix -/

theorem spec_fits {tbl : ConTable} {τ : Ty} {τr : List Ty} {k : String} {as : List Ty}
    (has : argTys tbl τ k = some as) : ∀ (P : List (List PatN)), (∀ r ∈ P, fitsListB tbl (τ :: τr) r = true) →
    ∀ r ∈ specializeCon k as.length P, fitsListB tbl (as ++ τr) r = true
  | [], _, r, hr => by simp [specializeCon] at hr
  | r0 :: P, hP, r, hr => by
    have ih := spec_fits has P (fun r h => hP r (List.mem_cons_of_mem _ h))
    have h0 := hP r0 List.mem_cons_self
    match r0, hr, h0 with
    | .wild :: rest, hr, h0 =>
      simp only [specializeCon, List.mem_cons] at hr
      simp only [fitsListB, Bool.and_eq_true] at h0
      rcases hr with rfl | hr
      · exact fitsListB_append (fitsListB_wilds as) h0.2
      · exact ih r hr
    | .con k' args :: rest, hr, h0 =>
      simp only [specializeCon] at hr
      split at hr
      · rename_i hk
        subst hk
        simp only [fitsListB, Bool.and_eq_true] at h0
        rcases List.mem_cons.mp hr with rfl | hr
        · obtain ⟨_, _, as', has', hargs⟩ := fitsB_con h0.1
          rw [has] at has'
          cases has'
          exact fitsListB_append hargs h0.2
        · exact ih r hr
      · exact ih r hr
    | .den _ :: _, hr, _ => exact ih r (by simpa [specializeCon] using hr)
    | [], hr, _ => exact ih r (by simpa [specializeCon] using hr)

theorem default_fits {tbl : ConTable} {τ : Ty} {τr : List Ty} : ∀ (P : List (List PatN)),
    (∀ r ∈ P, fitsListB tbl (τ :: τr) r = true) → ∀ r ∈ defaultM P, fitsListB tbl τr r = true
  | [], _, r, hr => by simp [defaultM] at hr
  | r0 :: P, hP, r, hr => by
    have ih := default_fits P (fun r h => hP r (List.mem_cons_of_mem _ h))
    have h0 := hP r0 List.mem_cons_self
    match r0, hr, h0 with
    | .wild :: rest, hr, h0 =>
      simp only [defaultM, List.mem_cons] at hr
      simp only [fitsListB, Bool.and_eq_true] at h0
      rcases hr with rfl | hr
      · exact h0.2
      · exact ih r hr
    | .den _ :: _, hr, _ => exact ih r (by simpa [defaultM] using hr)
    | .con _ _ :: _, hr, _ => exact ih r (by simpa [defaultM] using hr)
    | [], hr, _ => exact ih r (by simpa [defaultM] using hr)

/-! ## A column of wildcards -/

theorem missingDen_nil (kind : Nat) : ∃ d, missingDen kind [] = some d := by
  rcases kind with _ | _ | kind
  · simp [missingDen, litCandidate, intMin, intMax]
  · simp [missingDen, litCandidate]
  · simp [missingDen, litCandidate]

/-- When no row has a constructor or a constant at the head, a wildcard goes to the default matrix,
    whatever the column's type. -/
theorem useful_allwild {tbl : ConTable} {mode : Mode} {f : Nat} {τ : Ty} {τr : List Ty} {P : List (List PatN)}
    {qs : List PatN} (hc : headCons P = []) (hd : headDens P = []) :
    useful tbl mode (f + 1) (τ :: τr) P (.wild :: qs) = useful tbl mode f τr (defaultM P) qs := by
  simp only [useful, List.headD_cons, List.tail_cons, hc, hd]
  cases hl : litKind τ with
  | some kind =>
    cases mode with
    | exh => rfl
    | irr =>
      obtain ⟨d, hd'⟩ := missingDen_nil kind
      simp only [hd']
  | none =>
    simp only
    cases ctorsAt tbl τ <;> simp

/-! ## Agreement -/

theorem anyOpt_congr {α : Type} {g g0 : α → Option Bool} (key : α → String) :
    ∀ (cs cs0 : List α), cs.map key = cs0.map key →
    (∀ c ∈ cs, ∀ c0 ∈ cs0, key c = key c0 → g c = g0 c0) → useful.anyOpt cs g = useful.anyOpt cs0 g0
  | [], [], _, _ => rfl
  | c :: cs, c0 :: cs0, hk, hg => by
    simp only [List.map_cons, List.cons.injEq] at hk
    have e := hg c List.mem_cons_self c0 List.mem_cons_self hk.1
    have ih := anyOpt_congr key cs cs0 hk.2
      (fun x hx y hy he => hg x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) he)
    simp only [useful.anyOpt, e, ih]
  | [], _ :: _, hk, _ => by simp at hk
  | _ :: _, [], hk, _ => by simp at hk

theorem cond_names {tbl : ConTable} {τ τ0 : Ty} (hs : List String)
    (hn : (ctorsAt tbl τ).map (·.1) = (ctorsAt tbl τ0).map (·.1)) :
    (!(ctorsAt tbl τ).isEmpty && (ctorsAt tbl τ).all (fun c => hs.contains c.1)) =
    (!(ctorsAt tbl τ0).isEmpty && (ctorsAt tbl τ0).all (fun c => hs.contains c.1)) := by
  have e1 : ∀ l : List (String × List Ty), l.isEmpty = (l.map (·.1)).isEmpty := by intro l; cases l <;> rfl
  have e2 : ∀ l : List (String × List Ty), l.all (fun c => hs.contains c.1) = (l.map (·.1)).all hs.contains := by
    intro l; simp [List.all_map, Function.comp_def]
  rw [e1, e2, e1 (ctorsAt tbl τ0), e2 (ctorsAt tbl τ0), hn]

/-- Maranget's algorithm gives the same answer at two lists of column types at which the vector and
    every row fit. -/
theorem useful_agree (tbl : ConTable) (mode : Mode) : ∀ (f : Nat) (τs τs0 : List Ty) (P : List (List PatN))
    (q : List PatN), fitsListB tbl τs q = true → fitsListB tbl τs0 q = true →
    (∀ r ∈ P, fitsListB tbl τs r = true ∧ fitsListB tbl τs0 r = true) →
    useful tbl mode f τs P q = useful tbl mode f τs0 P q := by
  intro f
  induction f with
  | zero => intros; simp [useful]
  | succ f ih =>
    intro τs τs0 P q hq hq0 hP
    match q, τs, τs0, hq, hq0 with
    | [], _, _, _, _ => simp [useful]
    | _ :: _, [], _, hq, _ => simp [fitsListB] at hq
    | _ :: _, _ :: _, [], _, hq0 => simp [fitsListB] at hq0
    | p :: qs, τ :: τr, τ0 :: τr0, hq, hq0 =>
      simp only [fitsListB, Bool.and_eq_true] at hq hq0
      match p, hq, hq0 with
      | .den _, hq, _ => simp [fitsB] at hq
      | .con k args, hq, hq0 =>
        obtain ⟨_, _, as, has, hargs⟩ := fitsB_con hq.1
        obtain ⟨_, _, as0, has0, hargs0⟩ := fitsB_con hq0.1
        have hl : args.length = as.length := (fitsListB_length hargs).symm
        have hl0 : args.length = as0.length := (fitsListB_length hargs0).symm
        simp only [useful, List.headD_cons, List.tail_cons, has, has0]
        apply ih _ _ _ _ (fitsListB_append hargs hq.2) (fitsListB_append hargs0 hq0.2)
        intro r hr
        refine ⟨spec_fits has P (fun r h => (hP r h).1) r (hl ▸ hr),
          spec_fits has0 P (fun r h => (hP r h).2) r (hl0 ▸ hr)⟩
      | .wild, hq, hq0 =>
        by_cases hc : ∃ r ∈ P, ∃ k args rest, r = PatN.con k args :: rest
        · obtain ⟨r, hr, k, args, rest, rfl⟩ := hc
          have h1 := (hP _ hr).1
          have h2 := (hP _ hr).2
          simp only [fitsListB, Bool.and_eq_true] at h1 h2
          obtain ⟨hl, hn, _⟩ := fitsB_con h1.1
          obtain ⟨hl0, hn0, _⟩ := fitsB_con h2.1
          have hnn := hn.trans hn0.symm
          simp only [useful, List.headD_cons, List.tail_cons, hl, hl0]
          have hcn := cond_names (headCons P) hnn
          by_cases hc1 : (!(ctorsAt tbl τ).isEmpty && (ctorsAt tbl τ).all fun c => (headCons P).contains c.fst) = true
          · have hc2 := hcn ▸ hc1
            simp only [hc1, hc2, ite_true]
            have hcond := hc2
            simp only [Bool.and_eq_true, List.all_eq_true] at hcond
            apply anyOpt_congr (·.1) _ _ hnn
            intro c hcm c0 hcm0 hk
            obtain ⟨k', as'⟩ := c
            obtain ⟨k0, as0'⟩ := c0
            simp only at hk
            subst hk
            have ha : argTys tbl τ k' = some as' := ctorsAt_argTys hcm
            have ha0 : argTys tbl τ0 k' = some as0' := ctorsAt_argTys hcm0
            have hin : k' ∈ headCons P := by
              have := hcond.2 (k', as0') hcm0
              simpa using this
            -- a row with head k' gives both lengths
            have hlen : as'.length = as0'.length := by
              unfold headCons at hin
              rw [mem_dedupL] at hin
              obtain ⟨r', hr', hk'⟩ := List.mem_filterMap.mp hin
              match r', hr', hk' with
              | .con k'' args' :: rest', hr', hk' =>
                simp only [Option.some.injEq] at hk'
                subst hk'
                have g1 := (hP _ hr').1
                have g2 := (hP _ hr').2
                simp only [fitsListB, Bool.and_eq_true] at g1 g2
                obtain ⟨_, _, b1, hb1, hf1⟩ := fitsB_con g1.1
                obtain ⟨_, _, b2, hb2, hf2⟩ := fitsB_con g2.1
                rw [ha] at hb1; cases hb1
                rw [ha0] at hb2; cases hb2
                rw [fitsListB_length hf1, fitsListB_length hf2]
              | [], _, hk' => simp at hk'
              | .wild :: _, _, hk' => simp at hk'
              | .den _ :: _, _, hk' => simp at hk'
            simp only
            rw [← hlen]
            apply ih
            · exact fitsListB_append (fitsListB_wilds as') hq.2
            · rw [hlen]; exact fitsListB_append (fitsListB_wilds as0') hq0.2
            · intro r hr
              refine ⟨spec_fits ha P (fun r h => (hP r h).1) r hr, ?_⟩
              rw [hlen] at hr
              exact spec_fits ha0 P (fun r h => (hP r h).2) r hr
          · have hc2 : ¬ (!(ctorsAt tbl τ0).isEmpty && (ctorsAt tbl τ0).all fun c => (headCons P).contains c.fst) = true :=
              fun h => hc1 (hcn ▸ h)
            simp only [hc1, hc2]
            apply ih _ _ _ _ hq.2 hq0.2
            intro r hr
            exact ⟨default_fits P (fun r h => (hP r h).1) r hr, default_fits P (fun r h => (hP r h).2) r hr⟩
        · have hrows : ∀ r ∈ P, ∃ rest, r = .wild :: rest := by
            intro r hr
            have h1 := (hP r hr).1
            match r, hr, h1 with
            | .wild :: rest, _, _ => exact ⟨rest, rfl⟩
            | .con k args :: rest, hr, _ => exact absurd ⟨_, hr, k, args, rest, rfl⟩ hc
            | .den _ :: _, _, h1 => simp [fitsListB, fitsB] at h1
            | [], _, h1 => simp [fitsListB] at h1
          have hhc : headCons P = [] := by
            unfold headCons
            rw [List.filterMap_eq_nil_iff.mpr]
            · rfl
            · intro r hr
              obtain ⟨rest, rfl⟩ := hrows r hr
              rfl
          have hhd : headDens P = [] := by
            unfold headDens
            rw [List.filterMap_eq_nil_iff.mpr]
            · rfl
            · intro r hr
              obtain ⟨rest, rfl⟩ := hrows r hr
              rfl
          rw [useful_allwild hhc hhd, useful_allwild hhc hhd]
          apply ih _ _ _ _ hq.2 hq0.2
          intro r hr
          exact ⟨default_fits P (fun r h => (hP r h).1) r hr, default_fits P (fun r h => (hP r h).2) r hr⟩

/-! ## Constructor schemes the table agrees with -/

/-- The type variables of a list of bound variables, when it has no row variable. -/
def tyVarsOf : List BVar → Option (List TyVar)
  | [] => some []
  | .ty a :: vs => (tyVarsOf vs).map (a :: ·)
  | .row _ :: _ => none

/-- The scheme σ of constructor k is ∀α(n).τ(m) → (α(n)) t for distinct α(n), the table's entry for k
    under t is that, every constructor of t has the result (α(n)) t, t is not a literal type, and
    the first type of the table with a constructor k is t. -/
def schemeOKB (tbl : ConTable) (k : String) (σ : Scheme) : Bool :=
  match tyVarsOf σ.bound, splitCon σ.body with
  | some vs, (as, .con ys t) =>
    decide (ys = vs.map Ty.var) && decide vs.Nodup &&
    decide ((tbl.ctors t).find? (·.1 == k) = some (k, as, .con ys t)) &&
    (tbl.ctors t).all (fun c => decide (c.2.2 = .con ys t)) &&
    decide (sibs tbl k = (tbl.ctors t).map (·.1)) &&
    (litKind (.con ys t)).isNone
  | _, _ => false

theorem tyVarsOf_spec : ∀ {bs : List BVar} {vs : List TyVar}, tyVarsOf bs = some vs → bs = vs.map BVar.ty
  | [], vs, h => by simp [tyVarsOf] at h; subst h; rfl
  | .ty a :: bs, vs, h => by
    simp only [tyVarsOf] at h
    cases hb : tyVarsOf bs with
    | none => rw [hb] at h; cases h
    | some vs' =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp [tyVarsOf_spec hb]
  | .row _ :: _, _, h => by simp [tyVarsOf] at h

theorem splitCon_spec : ∀ (τ : Ty) {as : List Ty} {r : Ty}, splitCon τ = (as, r) → τ = arrows as r
  | .fn a b, as, r, h => by
    simp only [splitCon] at h
    cases hb : splitCon b with
    | mk as' r' =>
      rw [hb] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [arrows, splitCon_spec b hb]
  | .var _, as, r, h => by simp only [splitCon, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | .record _ _, as, r, h => by simp only [splitCon, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | .con _ _, as, r, h => by simp only [splitCon, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem bindSubst_ty : ∀ {vs : List TyVar} {ts : List Ty} {S : Subst}, bindSubst (vs.map BVar.ty) ts = some S →
    S.row = [] ∧ S.ty = vs.zip ts ∧ vs.length = ts.length
  | [], [], S, h => by simp [bindSubst] at h; subst h; simp [Subst.id]
  | a :: vs, t :: ts, S, h => by
    simp only [List.map_cons, bindSubst] at h
    cases hb : bindSubst (vs.map BVar.ty) ts with
    | none => rw [hb] at h; cases h
    | some S' =>
      rw [hb] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2, h3⟩ := bindSubst_ty hb
      simp [h1, h2, h3]
  | [], _ :: _, _, h => by simp [bindSubst] at h
  | _ :: _, [], _, h => by simp [bindSubst] at h

theorem bindSubst_length : ∀ {vs : List BVar} {ts : List Ty} {S : Subst}, bindSubst vs ts = some S →
    vs.length = ts.length
  | [], [], _, _ => rfl
  | .ty _ :: vs, _ :: ts, S, h => by
    simp only [bindSubst] at h
    cases hb : bindSubst vs ts with
    | none => rw [hb] at h; cases h
    | some _ => simp [bindSubst_length hb]
  | .row _ :: vs, τ :: ts, S, h => by
    match τ, h with
    | .record _ _, h =>
      simp only [bindSubst] at h
      cases hb : bindSubst vs ts with
      | none => rw [hb] at h; cases h
      | some _ => simp [bindSubst_length hb]
    | .var _, h => simp [bindSubst] at h
    | .fn _ _, h => simp [bindSubst] at h
    | .con _ _, h => simp [bindSubst] at h
  | [], _ :: _, _, h => by simp [bindSubst] at h
  | .ty _ :: _, [], _, h => by simp [bindSubst] at h
  | .row _ :: _, [], _, h => by simp [bindSubst] at h

mutual
theorem apply_total (S : Subst) (hS : S.row = []) : ∀ τ : Ty, ∃ τ', S.apply τ = some τ'
  | .var _ => by simp [Subst.apply]
  | .record ρ none => by
    obtain ⟨ρ', h⟩ := applyRow_total S hS ρ
    simp [Subst.apply, h]
  | .record ρ (some e) => by
    obtain ⟨ρ', h⟩ := applyRow_total S hS ρ
    simp [Subst.apply, h, hS]
  | .fn a b => by
    obtain ⟨a', ha⟩ := apply_total S hS a
    obtain ⟨b', hb⟩ := apply_total S hS b
    simp [Subst.apply, ha, hb]
  | .con ts _ => by
    obtain ⟨ts', h⟩ := applyList_total S hS ts
    simp [Subst.apply, h]
theorem applyRow_total (S : Subst) (hS : S.row = []) : ∀ ρ : Row, ∃ ρ', S.applyRow ρ = some ρ'
  | [] => by simp [Subst.applyRow]
  | (_, τ) :: rest => by
    obtain ⟨τ', h1⟩ := apply_total S hS τ
    obtain ⟨r', h2⟩ := applyRow_total S hS rest
    simp [Subst.applyRow, h1, h2]
theorem applyList_total (S : Subst) (hS : S.row = []) : ∀ ts : List Ty, ∃ ts', S.applyList ts = some ts'
  | [] => by simp [Subst.applyList]
  | τ :: rest => by
    obtain ⟨τ', h1⟩ := apply_total S hS τ
    obtain ⟨r', h2⟩ := applyList_total S hS rest
    simp [Subst.applyList, h1, h2]
end

theorem mapM_total (S : Subst) (hS : S.row = []) : ∀ as : List Ty, ∃ bs, as.mapM S.apply = some bs
  | [] => ⟨[], rfl⟩
  | a :: as => by
    obtain ⟨a', ha⟩ := apply_total S hS a
    obtain ⟨bs, hbs⟩ := mapM_total S hS as
    exact ⟨a' :: bs, by simp [List.mapM_cons, ha, hbs]⟩

theorem applyList_vars_cons {a : TyVar} {t : Ty} {L : FMap TyVar Ty} {R : FMap RowVar (Row × Option RowVar)} :
    ∀ {bs : List TyVar}, a ∉ bs →
    Subst.applyList ⟨(a, t) :: L, R⟩ (bs.map Ty.var) = Subst.applyList ⟨L, R⟩ (bs.map Ty.var)
  | [], _ => rfl
  | b :: bs, h => by
    simp only [List.mem_cons, not_or] at h
    have ih := applyList_vars_cons (t := t) (L := L) (R := R) h.2
    have hab : a ≠ b := h.1
    simp only [List.map_cons, Subst.applyList, Subst.apply, FMap.find?, hab, ↓reduceIte, ih]

theorem applyList_vars {R : FMap RowVar (Row × Option RowVar)} : ∀ {vs : List TyVar} {ts : List Ty},
    vs.Nodup → vs.length = ts.length → Subst.applyList ⟨vs.zip ts, R⟩ (vs.map Ty.var) = some ts
  | [], [], _, _ => rfl
  | a :: vs, t :: ts, hnd, hl => by
    simp only [List.nodup_cons] at hnd
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.zip_cons_cons, List.map_cons, Subst.applyList]
    rw [applyList_vars_cons hnd.1, applyList_vars hnd.2 hl]
    simp [Subst.apply, FMap.find?]
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem apply_con {S : Subst} {ys : List Ty} {t : TyName} {τ : Ty} (h : S.apply (.con ys t) = some τ) :
    ∃ ys', τ = .con ys' t ∧ S.applyList ys = some ys' := by
  simp only [Subst.apply] at h
  split at h
  · rename_i ys' hys; simp only [Option.some.injEq] at h; exact ⟨ys', h.symm, hys⟩
  · cases h

theorem applyList_mapM {S : Subst} : ∀ {ts : List Ty} {ts' : List Ty}, S.applyList ts = some ts' →
    ts.mapM S.apply = some ts'
  | [], ts', h => by simp [Subst.applyList] at h; subst h; rfl
  | τ :: ts, ts', h => by
    simp only [Subst.applyList] at h
    split at h
    · rename_i τ' r' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      simp [List.mapM_cons, h1, applyList_mapM h2]
    · cases h

theorem apply_arrows {S : Subst} {ys : List Ty} {t : TyName} : ∀ {as bs : List Ty} {τ : Ty},
    S.apply (arrows as (.con ys t)) = some (arrows bs τ) → isConTy τ = true →
    as.mapM S.apply = some bs ∧ S.apply (.con ys t) = some τ
  | [], bs, τ, h, hc => by
    obtain ⟨ys', he, _⟩ := apply_con h
    match bs, he with
    | [], he => simp only [arrows] at he h; exact ⟨rfl, h⟩
    | _ :: _, he => simp [arrows] at he
  | a :: as, bs, τ, h, hc => by
    simp only [arrows, Subst.apply] at h
    split at h
    · rename_i a' b' ha hb
      simp only [Option.some.injEq] at h
      match bs, h with
      | [], h => simp only [arrows] at h; subst h; simp [isConTy] at hc
      | b :: bs, h =>
        simp only [arrows, Ty.fn.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := apply_arrows hb hc
        exact ⟨by simp [List.mapM_cons, ha, h1], h2⟩
    · cases h

theorem filterMap_vars (g : Ty → Option BVar) (hg : ∀ a, g (.var a) = some (.ty a)) : ∀ (vs : List TyVar),
    (vs.map Ty.var).filterMap g = vs.map BVar.ty
  | [] => rfl
  | a :: vs => by simp [hg, filterMap_vars g hg vs]

theorem argTys_eq {tbl : ConTable} {t : TyName} {k : String} {as : List Ty} {vs : List TyVar} {inst : List Ty}
    {S : Subst} (hf : (tbl.ctors t).find? (·.1 == k) = some (k, as, .con (vs.map Ty.var) t))
    (hb : bindSubst (vs.map BVar.ty) inst = some S) :
    argTys tbl (.con inst t) k = as.mapM S.apply := by
  simp only [argTys, hf]
  rw [filterMap_vars _ (fun _ => rfl)]
  simp [hb]

theorem filterMap_names {α β : Type} {g : String × α → Option (String × β)} :
    ∀ (l : List (String × α)), (∀ c ∈ l, ∃ x, g c = some (c.1, x)) → (l.filterMap g).map (·.1) = l.map (·.1)
  | [], _ => rfl
  | c :: l, h => by
    obtain ⟨x, hx⟩ := h c List.mem_cons_self
    simp [hx, filterMap_names l (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/-- A constructor pattern typed by the scheme of a constructor the table agrees with fits. -/
theorem con_fits {tbl : ConTable} {k : String} {σ : Scheme} {inst : List Ty} {S : Subst} {argtys : List Ty}
    {τ : Ty} {args : List PatN} (hok : schemeOKB tbl k σ = true)
    (hb : bindSubst σ.bound inst = some S) (ha : S.apply σ.body = some (arrows argtys τ))
    (hc : isConTy τ = true) (hargs : fitsListB tbl argtys args = true) : fitsB tbl τ (.con k args) = true := by
  cases hv : tyVarsOf σ.bound with
  | none => simp [schemeOKB, hv] at hok
  | some vs =>
    cases hs : splitCon σ.body with
    | mk as r =>
      cases r with
      | var _ => simp [schemeOKB, hv, hs] at hok
      | record _ _ => simp [schemeOKB, hv, hs] at hok
      | fn _ _ => simp [schemeOKB, hv, hs] at hok
      | con ys t =>
        simp only [schemeOKB, hv, hs, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
        obtain ⟨⟨⟨⟨⟨hys, hnd⟩, hfind⟩, hall⟩, hsib⟩, hlit⟩ := hok
        subst hys
        have hbound := tyVarsOf_spec hv
        have hbody := splitCon_spec _ hs
        rw [hbound] at hb
        rw [hbody] at ha
        obtain ⟨hrow, hty, hlen⟩ := bindSubst_ty hb
        obtain ⟨hm, hcon⟩ := apply_arrows ha hc
        obtain ⟨ys', rfl, hys'⟩ := apply_con hcon
        have hS : S = ⟨vs.zip inst, S.row⟩ := by cases S; simp only at hty; simp [hty]
        have hinst : ys' = inst := by
          rw [hS, applyList_vars hnd hlen] at hys'
          exact (Option.some.inj hys').symm
        subst hinst
        apply fitsB_of (as := argtys)
        · cases ys' with
          | nil =>
            cases vs with
            | nil => simpa using hlit
            | cons _ _ => simp at hlen
          | cons _ _ => rfl
        · rw [hsib]
          unfold ctorsAt
          simp only
          apply filterMap_names
          intro c hcm
          have hex : ((tbl.ctors t).find? (·.1 == c.1)).isSome := by
            rw [List.find?_isSome]; exact ⟨c, hcm, by simp⟩
          obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hex
          have hc'm := List.mem_of_find?_eq_some hc'
          have hc'k : c'.1 = c.1 := by simpa using List.find?_some hc'
          have hres := hall c' hc'm
          obtain ⟨k', as', r'⟩ := c'
          simp only at hc'k hres
          subst hc'k hres
          obtain ⟨bs, hbs⟩ := mapM_total S hrow as'
          refine ⟨bs, ?_⟩
          rw [argTys_eq hc' hb, hbs]
          rfl
        · rw [argTys_eq hfind hb, hm]
        · exact hargs

end StandardElm.Stat.RFurther
