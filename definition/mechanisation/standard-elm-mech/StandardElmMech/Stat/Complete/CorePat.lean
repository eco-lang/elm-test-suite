/-
  A Standard Definition of Elm? Mechanisation: completeness of `coreGen` on patterns, plan step 11,
  milestone (a). For a checked annotated pattern and the valuation that reads the derivation's
  types at the pattern's nodes (`rdAtPat`), the pattern's constraints hold, its term evaluates to
  its type (normalised), and the variables it binds stand for their types.
-/
import StandardElmMech.Stat.Complete.CoreLemmas

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

variable {ν : Val}

/-! ## Helpers -/

theorem ev_tupleT (t1 t2 : T) (t3 : Option T) :
    (tupleT t1 t2 t3).ev ν = tupleTy (t1.ev ν) (t2.ev ν) (t3.map (T.ev ν)) := by
  cases t3 <;> rfl

theorem ev_arrowsT (t : T) : ∀ ts : List T, (arrowsT ts t).ev ν = arrows (ts.map (T.ev ν)) (t.ev ν)
  | [] => rfl
  | a :: as => by simp only [arrowsT, T.ev, ev_arrowsT t as, List.map_cons, arrows]

theorem hRec_cons {ρ : Row} (h : ρ ≠ []) (tl : Option RowVar) : hRec ρ tl = .record ρ tl := by
  cases tl with
  | none => rfl
  | some e =>
    cases e with
    | named s => cases ρ with
      | nil => exact absurd rfl h
      | cons _ _ => rfl
    | fresh _ => rfl
    | bnd _ => rfl


/-- Field constraints on a record type whose row contains the fields. -/
theorem has_ok (tr : T) (rT : List (Lab × T)) (ρ : Row) (τ : Ty) (hτ : tr.ev ν = hN τ)
    (hrow : T.evRow ν rT = hNRow ρ)
    (hsub : ∀ l τl, (l, τl) ∈ ρ → ∃ ρτ tl, τ = .record ρτ tl ∧ Row.lookup ρτ l = some τl) :
    Holds ν (rT.map fun f => .has tr f.1 f.2) := by
  intro c hc
  obtain ⟨⟨l, t⟩, hm, rfl⟩ := List.mem_map.mp hc
  have hm' : (l, t.ev ν) ∈ ρ.map (fun p => (p.1, hN p.2)) := by
    rw [← hNRow_eq, ← hrow, T.evRow_eq]
    exact List.mem_map.mpr ⟨(l, t), hm, rfl⟩
  obtain ⟨τl, hτl, hev⟩ := find?_of_mem_map hN ρ l _ hm'
  obtain ⟨ρτ, tl, rfl, hlook⟩ := hsub l τl hτl
  have hne : ρτ ≠ [] := by rintro rfl; simp [Row.lookup, FMap.find?] at hlook
  refine ⟨hNRow ρτ, tl, ?_, ?_⟩
  · rw [hτ]; simp only [hN]; exact hRec_cons (by rwa [Ne, hNRow_nil_iff]) tl
  · simp only [Row.lookup] at hlook ⊢
    rw [hNRow_eq, find?_map_val, hlook, ← hev]
    rfl

theorem sub_of_subB {ρ : Row} {τ : Ty} (hr : isRecordTy τ = true) (hs : Row.subB ρ (recordRow τ) = true) :
    ∀ l τl, (l, τl) ∈ ρ → ∃ ρτ tl, τ = .record ρτ tl ∧ Row.lookup ρτ l = some τl := by
  obtain ⟨ρτ, tl, rfl⟩ := isRecordTy_spec hr
  intro l τl hm
  exact ⟨ρτ, tl, rfl, (Row.subB_iff _ _).mp hs l τl hm⟩

theorem conLook {C : Ctx} {lc : LongId} {inst : List Ty} {τ' τ : Ty}
    (h : (match C.lookupVal lc with
      | some (σ, .c) => genAt σ inst τ' && isConTy τ
      | _ => false) = true) : ∃ σ, C.lookupVal lc = some (σ, .c) ∧ genAt σ inst τ' = true := by
  split at h
  · rename_i σ hl
    simp only [Bool.and_eq_true] at h
    exact ⟨σ, hl, h.1⟩
  · cases h

theorem lookGen {C : Ctx} {lv : LongId} {inst : List Ty} {τ : Ty}
    (h : (match C.lookupVal lv with
      | some (σ, _) => genAt σ inst τ
      | none => false) = true) : ∃ σ is, C.lookupVal lv = some (σ, is) ∧ genAt σ inst τ = true := by
  split at h
  · rename_i σ is hl; exact ⟨σ, is, hl, h⟩
  · cases h

theorem adm_num_of_lit {n : Nat} {τ : Ty} (h : genAt (typeOf (.int n)) [τ] τ = true) : Adm .num τ := by
  unfold genAt at h
  simp only [typeOf, bindSubst] at h
  simp only [Bool.and_eq_true] at h
  have := (Subst.respectsB_iff _).mp h.1
  exact this _ List.mem_cons_self

/-! ## The rows of record patterns -/

mutual
theorem prow_ok : (r : APatRow) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdPatRow r q) →
    T.evRow ν (prow p r.erase) = hNRow r.row
  | .field l τ rest, p, hr => by
    simp only [APatRow.erase, prow, APatRow.row, evRow_rmod]
    rw [prowOpt_ok rest (child 1 hr (fun q => rfl)), hNRow_modify, modify_eq_rmod]
    simp only [T.evRow, hNRow, T.ev, (slot hr (0))]
    rfl
theorem prowOpt_ok : (r : Option APatRow) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdPatRowOpt r q) →
    T.evRow ν (prowOpt p (APatRow.eraseOpt r)) = hNRow (APatRow.rowOpt r)
  | none, _, _ => rfl
  | some r, p, hr => by
    simp only [APatRow.eraseOpt, prowOpt, APatRow.rowOpt]
    exact prow_ok r hr
end

/-! ## The variables patterns bind -/

mutual
theorem penvAt_rel : (a : AAtPat) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdAtPat a q) →
    RelL ν (penvAt p a.erase) a.ve
  | .wild _, _, _ => RelL.nil
  | .scon _ _, _, _ => RelL.nil
  | .var x τ, p, hr => by
    simp only [AAtPat.erase, penvAt, AAtPat.ve]
    exact RelL.single (gok_mono_mv ((slot hr (0))))
  | .con _ _ _, _, _ => RelL.nil
  | .unit, _, _ => RelL.nil
  | .tuple p1 p2 p3, p, hr => by
    simp only [AAtPat.erase, penvAt, AAtPat.ve]
    exact RelL.modify (RelL.modify (penv_rel p1 (child 0 hr (fun q => rfl))) (penv_rel p2 (child 1 hr (fun q => rfl))))
      (penvOpt_rel p3 (child 2 hr (fun q => rfl)))
  | .nil _, _, _ => RelL.nil
  | .record row _, p, hr => by
    simp only [AAtPat.erase, penvAt, AAtPat.ve]
    exact penvRowOpt_rel row (child 1 hr (fun q => rfl))
  | .paren q0, p, hr => by
    simp only [AAtPat.erase, penvAt, AAtPat.ve]
    exact penv_rel q0 (child 0 hr (fun q => rfl))
theorem penvRow_rel : (r : APatRow) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdPatRow r q) →
    RelL ν (penvRow p r.erase) r.ve
  | .field l τ rest, p, hr => by
    simp only [APatRow.erase, penvRow, APatRow.ve]
    exact RelL.modify (RelL.single (gok_mono_mv ((slot hr (0))))) (penvRowOpt_rel rest (child 1 hr (fun q => rfl)))
theorem penvRowOpt_rel : (r : Option APatRow) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdPatRowOpt r q) →
    RelL ν (penvRowOpt p (APatRow.eraseOpt r)) (APatRow.veOpt r)
  | none, _, _ => RelL.nil
  | some r, p, hr => by
    simp only [APatRow.eraseOpt, penvRowOpt, APatRow.veOpt]
    exact penvRow_rel r hr
theorem penv_rel : (a : APat) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdPat a q) → RelL ν (penv p a.erase) a.ve
  | .atpat a, p, hr => by
    simp only [APat.erase, penv, APat.ve]
    exact penvAt_rel a (child 0 hr (fun q => rfl))
  | .con _ _ args _, p, hr => by
    simp only [APat.erase, penv, APat.ve]
    exact RelL.plusAll (penvList_rel args (child 2 hr (fun q => rfl)))
  | .cons p1 p2, p, hr => by
    simp only [APat.erase, penv, APat.ve]
    exact RelL.modify (penv_rel p1 (child 0 hr (fun q => rfl))) (penv_rel p2 (child 1 hr (fun q => rfl)))
  | .as q0 x, p, hr => by
    simp only [APat.erase, penv, APat.ve]
    exact RelL.modify (penv_rel q0 (child 0 hr (fun q => rfl))) (RelL.single (gok_mono_mv ((slot hr (1)))))
theorem penvOpt_rel : (a : Option APat) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdPatOpt a q) →
    RelL ν (penvOpt p (APat.eraseOpt a)) (APat.veOpt a)
  | none, _, _ => RelL.nil
  | some a, p, hr => by
    simp only [APat.eraseOpt, penvOpt, APat.veOpt]
    exact penv_rel a hr
theorem penvList_rel : (as : List AAtPat) → ∀ {p : Path}, (∀ q, ν (q.reverse ++ p) = rdAtPatList as q) →
    RelLs ν (penvList p (AAtPat.eraseList as)) (AAtPat.veList as)
  | [], _, _ => trivial
  | a :: as, p, hr => by
    simp only [AAtPat.eraseList, penvList, AAtPat.veList, RelLs]
    exact ⟨penvAt_rel a (child 0 hr (fun q => rfl)), penvList_rel as (child 1 hr (fun q => rfl))⟩
end

/-! ## The constraints of patterns -/

section pat
variable {f : TyName → TyName} {C : Ctx} {Γ : GCtx} (hS : Sim ν f Γ C)
include hS
set_option linter.unusedSectionVars false

mutual
theorem gAtPat_ok : (a : AAtPat) → ∀ {p : Path}, checkAtPat C a = true → (∀ q, ν (q.reverse ++ p) = rdAtPat a q) →
    Holds ν (gAtPat Γ p a.erase).2 ∧ (gAtPat Γ p a.erase).1.ev ν = hN a.ty
  | .wild τ, p, _, hr => ⟨Holds.nil, (slot hr (0))⟩
  | .scon sc τ, p, h, hr => by
    simp only [checkAtPat, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hg, hm⟩ := h
    refine ⟨Holds.nil, ?_⟩
    simp only [AAtPat.erase, gAtPat, AAtPat.ty]
    cases sc with
    | int n =>
      have hadm := adm_num_of_lit hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · simp only [patLitT, ev_ofTy, hN_tIntTy]
      · cases hadm
      · cases hadm
    | float m e => rw [genAt_mono hg]; simp only [patLitT, ev_ofTy, hN_tFloatTy]
    | char c => rw [genAt_mono hg]; simp only [patLitT, ev_ofTy, hN_tCharTy]
    | str s => rw [genAt_mono hg]; simp only [patLitT, ev_ofTy, hN_tStringTy]
  | .var x τ, p, _, hr => ⟨Holds.nil, (slot hr (0))⟩
  | .con lc inst τ, p, h, hr => by
    simp only [checkAtPat] at h
    obtain ⟨σ, hl, hg⟩ := conLook h
    exact occT_ok hS hl hg hr
  | .unit, p, _, _ => ⟨Holds.nil, by simp only [AAtPat.erase, gAtPat, AAtPat.ty, ev_ofTy, hN_tUnitTy]⟩
  | .tuple p1 p2 p3, p, h, hr => by
    simp only [checkAtPat, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨c1, e1⟩ := gPat_ok p1 h1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, e2⟩ := gPat_ok p2 h2 (child 1 hr (fun q => rfl))
    obtain ⟨c3, e3⟩ := gPatOpt_ok p3 h3 (child 2 hr (fun q => rfl))
    simp only [AAtPat.erase, gAtPat, AAtPat.ty]
    generalize gPat Γ (0 :: p) p1.erase = r1 at c1 e1 ⊢
    generalize gPat Γ (1 :: p) p2.erase = r2 at c2 e2 ⊢
    generalize gPatOpt Γ (2 :: p) (APat.eraseOpt p3) = r3 at c3 e3 ⊢
    obtain ⟨t1, cs1⟩ := r1
    obtain ⟨t2, cs2⟩ := r2
    obtain ⟨t3, cs3⟩ := r3
    simp only at c1 e1 c2 e2 c3 e3 ⊢
    refine ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c1, c2⟩, c3⟩, ?_⟩
    rw [ev_tupleT, e1, e2, e3, hN_tupleTy]
  | .nil τ, p, h, hr => by
    simp only [checkAtPat] at h
    obtain ⟨τ0, rfl⟩ := isListTy_spec h
    refine ⟨Holds.nil, ?_⟩
    simp only [AAtPat.erase, gAtPat, AAtPat.ty, T.ev, T.evList, (slot hr (0)), hN_listTy]
    rfl
  | .record row τ, p, h, hr => by
    simp only [checkAtPat, Bool.and_eq_true] at h
    obtain ⟨⟨_, hrec⟩, hsub⟩ := h
    simp only [AAtPat.erase, gAtPat, AAtPat.ty]
    refine ⟨?_, (slot hr (0))⟩
    exact has_ok _ _ _ τ ((slot hr (0))) (prowOpt_ok row (child 1 hr (fun q => rfl))) (sub_of_subB hrec hsub)
  | .paren q0, p, h, hr => by
    simp only [checkAtPat] at h
    simp only [AAtPat.erase, gAtPat, AAtPat.ty]
    exact gPat_ok q0 h (child 0 hr (fun q => rfl))
theorem gPat_ok : (a : APat) → ∀ {p : Path}, checkPat C a = true → (∀ q, ν (q.reverse ++ p) = rdPat a q) →
    Holds ν (gPat Γ p a.erase).2 ∧ (gPat Γ p a.erase).1.ev ν = hN a.ty
  | .atpat a, p, h, hr => by
    simp only [checkPat] at h
    simp only [APat.erase, gPat, APat.ty]
    exact gAtPat_ok a h (child 0 hr (fun q => rfl))
  | .con lc inst args τ, p, h, hr => by
    simp only [checkPat, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨σ, hl, hg⟩ := conLook h1
    obtain ⟨c0, e0⟩ := occT_ok hS hl hg (child 0 hr (fun q => rfl))
    obtain ⟨c1, e1⟩ := gAtPatList_ok args h2 (child 2 hr (fun q => rfl))
    simp only [APat.erase, gPat, APat.ty]
    generalize occT Γ lc (0 :: p) = r0 at c0 e0 ⊢
    generalize gAtPatList Γ (2 :: p) (AAtPat.eraseList args) = r1 at c1 e1 ⊢
    obtain ⟨tc, cs0⟩ := r0
    obtain ⟨ts, cs1⟩ := r1
    simp only at c0 e0 c1 e1 ⊢
    refine ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c0, c1⟩, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩, (slot hr (1))⟩
    simp only [Con.holds]
    rw [e0, ev_arrowsT, e1, hN_arrows]
    simp only [T.ev, (slot hr (1))]
    rfl
  | .cons p1 p2, p, h, hr => by
    simp only [checkPat, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨c1, e1⟩ := gPat_ok p1 h1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, e2⟩ := gPat_ok p2 h2 (child 1 hr (fun q => rfl))
    simp only [APat.erase, gPat, APat.ty]
    generalize gPat Γ (0 :: p) p1.erase = r1 at c1 e1 ⊢
    generalize gPat Γ (1 :: p) p2.erase = r2 at c2 e2 ⊢
    obtain ⟨t1, cs1⟩ := r1
    obtain ⟨t2, cs2⟩ := r2
    simp only at c1 e1 c2 e2 ⊢
    have hl : (T.con [t1] tList).ev ν = hN (listTy (APat.ty p1)) := by
      simp only [T.ev, T.evList, e1, hN_listTy]; rfl
    refine ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c1, c2⟩, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩, hl⟩
    simp only [Con.holds]
    rw [e2, h3, hl]
  | .as q0 x, p, h, hr => by
    simp only [checkPat] at h
    obtain ⟨c, e⟩ := gPat_ok q0 h (child 0 hr (fun q => rfl))
    simp only [APat.erase, gPat, APat.ty]
    generalize gPat Γ (0 :: p) q0.erase = r at c e ⊢
    obtain ⟨t, cs⟩ := r
    simp only at c e ⊢
    refine ⟨Holds.append.mpr ⟨c, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩, e⟩
    simp only [Con.holds, T.ev]
    rw [(slot hr (1)), e]
    rfl
theorem gPatOpt_ok : (a : Option APat) → ∀ {p : Path}, checkPatOpt C a = true → (∀ q, ν (q.reverse ++ p) = rdPatOpt a q) →
    Holds ν (gPatOpt Γ p (APat.eraseOpt a)).2 ∧ (gPatOpt Γ p (APat.eraseOpt a)).1.map (T.ev ν) = (APat.tyOpt a).map hN
  | none, _, _, _ => ⟨Holds.nil, rfl⟩
  | some a, p, h, hr => by
    simp only [checkPatOpt] at h
    obtain ⟨c, e⟩ := gPat_ok a h hr
    simp only [APat.eraseOpt, gPatOpt, APat.tyOpt]
    generalize gPat Γ p a.erase = r at c e ⊢
    obtain ⟨t, cs⟩ := r
    simp only at c e ⊢
    exact ⟨c, by simp only [Option.map_some, e]⟩
theorem gAtPatList_ok : (as : List AAtPat) → ∀ {p : Path}, checkAtPatList C as = true →
    (∀ q, ν (q.reverse ++ p) = rdAtPatList as q) →
    Holds ν (gAtPatList Γ p (AAtPat.eraseList as)).2 ∧
      (gAtPatList Γ p (AAtPat.eraseList as)).1.map (T.ev ν) = (AAtPat.tyList as).map hN
  | [], _, _, _ => ⟨Holds.nil, rfl⟩
  | a :: as, p, h, hr => by
    simp only [checkAtPatList, Bool.and_eq_true] at h
    obtain ⟨c1, e1⟩ := gAtPat_ok a h.1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, e2⟩ := gAtPatList_ok as h.2 (child 1 hr (fun q => rfl))
    simp only [AAtPat.eraseList, gAtPatList, AAtPat.tyList]
    generalize gAtPat Γ (0 :: p) a.erase = r1 at c1 e1 ⊢
    generalize gAtPatList Γ (1 :: p) (AAtPat.eraseList as) = r2 at c2 e2 ⊢
    obtain ⟨t, cs⟩ := r1
    obtain ⟨ts, css⟩ := r2
    simp only at c1 e1 c2 e2 ⊢
    exact ⟨Holds.append.mpr ⟨c1, c2⟩, by rw [List.map_cons, e1, e2]; rfl⟩
end

end pat

end StandardElm.Stat.Complete
