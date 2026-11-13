/-
  A Standard Definition of Elm? Mechanisation: L10 for patterns with records (plan step 11,
  milestone (d)): what W builds for a pattern is accepted by the checker under every later
  substitution `s` once a canonical `U` absorbing `s` is given.

  * A record pattern `{l1, ..., lk}` has type `⟨{li ↦ αi} | ε⟩`; the checker wants its row a
    sub-row of the record's: the image's merged row is sorted (canonical), so a lookup finds each
    field (`subB_mrg`).
  * A constructor pattern unifies its arguments' types one after the other with the
    constructor's argument types; these are not recorded, and their images need not be canonical
    in an arbitrary run (a lacks constraint of the scheme between two arguments, A23). They are
    canonical when the constructor's scheme has an instance at `U`'s image of the pattern
    (`CWPat`, given at the root by the derivation): `U` changed on the instance's variables is a
    canonical unifier of the pairs (`con_uprem`), and the unification of the pairs is then sound
    (`PostK.uargsD`).
-/
import StandardElmMech.Stat.Complete.WDSoundInst

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPatRow BPat BAtExp BExp BMatch BMRule BDec BValBind)

namespace WDS

/-! ## Constructor witnesses -/

/-- The constructor lookups of the root: schemes W can hold, from the root. -/
def LOk (n0 : Nat) (L : LongId → Option Scheme) : Prop := ∀ lv σ, L lv = some σ → SchWD n0 σ

mutual
def CWAtPat (L : LongId → Option Scheme) (U : RSub) : AAtPat → Prop
  | .tuple p1 p2 p3 => CWPat L U p1 ∧ CWPat L U p2 ∧ CWPatOpt L U p3
  | .paren p => CWPat L U p
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .unit | .nil _ | .record _ _ => True
def CWPat (L : LongId → Option Scheme) (U : RSub) : APat → Prop
  | .atpat a => CWAtPat L U a
  | .con lc _ args τ =>
    (∀ σ, L lc = some σ → ∃ ts', genAt σ ts' (arrows (rsbList U (AAtPat.tyList args)) (rsb U τ)) = true) ∧
      CWAtPats L U args
  | .cons p1 p2 => CWPat L U p1 ∧ CWPat L U p2
  | .as p _ => CWPat L U p
def CWPatOpt (L : LongId → Option Scheme) (U : RSub) : Option APat → Prop
  | none => True
  | some p => CWPat L U p
def CWAtPats (L : LongId → Option Scheme) (U : RSub) : List AAtPat → Prop
  | [] => True
  | a :: as => CWAtPat L U a ∧ CWAtPats L U as
end

/-! ## Records -/

theorem lookup_sorted {ρ : Row} (h : Sorted ρ) {x : Lab × Ty} (hx : x ∈ ρ) : Row.lookup ρ x.1 = some x.2 := by
  obtain ⟨t, ht⟩ := rowFind?_of_mem (mem_labs_of_mem hx)
  have hm := rowFind?_mem ht
  have := sorted_unique h hm hx rfl
  rw [show Row.lookup ρ x.1 = FMap.find? ρ x.1 from rfl, ht]
  exact congrArg some (congrArg Prod.snd this)

theorem subB_mrg {A X : Row} (h : Sorted (mrg A X)) : Row.subB A (mrg A X) = true := by
  simp only [Row.subB, List.all_eq_true]
  intro x hx
  rw [lookup_sorted h (mem_mrg.mpr (.inl hx))]
  simp

mutual
theorem checkPatRow_true (C : Ctx) : ∀ r : APatRow, checkPatRow C r = true
  | .field _ _ rest => by simp only [checkPatRow]; exact checkPatRowOpt_true C rest
theorem checkPatRowOpt_true (C : Ctx) : ∀ r : Option APatRow, checkPatRowOpt C r = true
  | none => rfl
  | some r => by simp only [checkPatRowOpt]; exact checkPatRow_true C r
end

/-- The record pattern's check: a canonical image of `⟨ρ | ε⟩` has `ρ`'s image as a sub-row. -/
theorem check_record {C : Ctx} {s : RSub} {ar : Option APatRow} {e : RowVar}
    (hc : cnB (rsb s (.record (APatRow.rowOpt ar) (some e))) = true) :
    checkAtPat C (rsbAtPat s (.record ar (.record (APatRow.rowOpt ar) (some e)))) = true := by
  simp only [rsbAtPat, checkAtPat, checkPatRowOpt_true, Bool.true_and, Bool.and_eq_true]
  have hs := (cnB_rsb_record.mp hc).1
  simp only [rsb, RSub.tl] at hs ⊢
  refine ⟨rfl, ?_⟩
  rw [← rsbRow_rowOpt]
  exact subB_mrg hs

/-- A row of a record pattern: fresh variables. -/
theorem wdPatRowOpt_sound (fuel n0 : Nat) {L : LongId → Option Scheme} {C : Ctx} :
    ∀ (r : Option BPatRow) (st : WDSt) (ar : Option APatRow) (st' : WDSt), SPre n0 L C st →
      wdPatRowOpt fuel (rigidFromD n0) r st = .ok ar st' → PostK n0 C st st' (tysPatRowOpt ar) (fun _ => True) []
  | none, st, ar, st', hp, h => by
    simp only [wdPatRowOpt] at h; obtain ⟨rfl, rfl⟩ := pure_okD h
    exact PostK.start hp
  | some (.field l rest), st, ar, st', hp, h => by
    simp only [wdPatRowOpt, wdPatRow] at h
    obtain ⟨a, st1, h1, h⟩ := wdbind_ok h
    obtain ⟨α, st2, h2, h3⟩ := wdbind_ok h1
    obtain ⟨rfl, rfl⟩ := freshVD_ok h2
    obtain ⟨r1, st3, h4, h5⟩ := wdbind_ok h3
    obtain ⟨rfl, rfl⟩ := pure_okD h5
    obtain ⟨rfl, rfl⟩ := pure_okD h
    have P1 := (PostK.start hp).fresh
    have P2 := wdPatRowOpt_sound fuel n0 rest _ r1 _ (hp.later P1.seg) h4
    refine (PostK.seqSame hp P1 P2).weaken (covSub fun τ hτ => ?_) fun _ _ _ => trivial
    simp only [tysPatRowOpt, tysPatRow, List.mem_cons] at hτ
    rcases hτ with rfl | h
    · simp
    · simp [h]

/-! ## Constructor patterns -/

theorem arrows_inj : ∀ {as bs : List Ty} {r r' : Ty}, as.length = bs.length → arrows as r = arrows bs r' →
    as = bs ∧ r = r'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | a :: as, b :: bs, r, r', hl, h => by
    simp only [arrows, Ty.fn.injEq] at h
    obtain ⟨h1, h2⟩ := arrows_inj (by simpa using hl) h.2
    exact ⟨by rw [h.1, h1], h2⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

theorem zip_rsbList {U T : RSub} : ∀ {l1 l2 : List Ty}, rsbList U l1 = rsbList T l2 →
    ∀ p ∈ l1.zip l2, rsb U p.1 = rsb T p.2
  | [], _, _, _, hp => by simp at hp
  | _ :: _, [], _, _, hp => by simp at hp
  | a :: l1, b :: l2, h, p, hp => by
    simp only [rsbList, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h.1
    · exact zip_rsbList h.2 p hp

/-- The canonical unifier of a constructor pattern's pairs: `U`, changed on the instance's
    variables to the instance the witness gives. -/
theorem con_uprem {n0 : Nat} {C : Ctx} {st st1 st2 : WDSt} {σ : Scheme} {τs argtys : List Ty} {r : Ty} {U : RSub}
    (hi : SInvW n0 st) (hθ1 : st1.θ = st.θ) (hn1 : st1.n = st.n + σ.bound.length)
    (hτb : rsb (instS st.n σ.bound) σ.body = arrows τs r) (hlen : τs.length = argtys.length)
    (hseg : SegD n0 (Reach (th st1) C st1.n) st1 st2) (hCold : ∀ c ∈ C.tyvars, newB st.n c = false)
    (hreach : ∀ τ ∈ argtys, ∀ b ∈ (rsb (th st2) τ).vars, Reach (th st1) C st1.n b)
    (hσ : SchWD st.n σ) (hσ0 : SchWD n0 σ)
    (hfx : FixR (rigidFromD n0) U) (hre : RespR U) (hab : AbsS U (th st2)) (hcn : CnL U argtys)
    (hw : ∃ ts', genAt σ ts' (arrows (rsbList U argtys) (rsb U r)) = true) :
    UPrem n0 st2 argtys τs := by
  obtain ⟨ts', hg⟩ := hw
  obtain ⟨g, hgr, hgout, hgτ⟩ := gen_rsb (gen_of_genAt hg)
  have hI : InstUnderD U σ (arrows (rsbList U argtys) (rsb U r)) := by
    refine ⟨g, fun a _ => hgr a, ?_⟩
    rw [hgτ]
    apply rsb_congr
    intro w hw
    rw [extS_img]
    split
    · rfl
    · rename_i hm
      rw [hgout w hm]
      exact (hfx w (rigid_of_oldD (hσ0.2 w hw hm).2)).symm
  obtain ⟨T, hag1, hag2, hcls, hT⟩ := inst_existsD hσ hI
  -- the instance's variables
  let Iv : BVar → Prop := fun v => newB st.n v = true ∧ newB st1.n v = false
  have notIv_reach : ∀ b, Reach (th st1) C st1.n b → ¬ Iv b := by
    rintro b (hb | ⟨c, hc, hb⟩) ⟨_, h2⟩
    · rw [hb] at h2; cases h2
    · rename_i h1
      have hθ : th st1 = th st := by simp only [th, hθ1]
      rw [hθ] at hb
      rcases img_old hi.inv.good c with e | ⟨-, ho⟩
      · rw [e, vars_vty, List.mem_singleton] at hb; subst hb; rw [hCold _ hc] at h1; cases h1
      · rw [ho b hb] at h1; cases h1
  have hθ1' : th st1 = th st := by simp only [th, hθ1]
  have fixIv : ∀ d, Iv d → (th st2).img d = vty d := by
    intro d hd
    have h1 : (th st1).img d = vty d := by rw [hθ1']; exact hi.unbound_new hd.1
    exact Classical.byContradiction fun hne => notIv_reach d (hseg.mv d h1 hne).1 hd
  have imgIv : ∀ d, ¬ Iv d → ∀ w ∈ ((th st2).img d).vars, ¬ Iv w := by
    intro d hd w hw
    rcases moves_var hseg.mv hseg.abs (by rw [hθ1']; exact hi.idem) d w hw with h | h
    · rw [hθ1'] at h
      rcases img_old hi.inv.good d with e | ⟨-, ho⟩
      · rw [e, vars_vty, List.mem_singleton] at h; subst h; exact hd
      · exact fun hw' => by have := hw'.1; rw [ho w h] at this; cases this
    · exact notIv_reach w h
  have agree : ∀ v, ¬ Iv v → T.img v = U.img v := by
    intro v hv
    cases e : newB st.n v
    · exact hag1 v e
    · refine hag2 v ?_
      cases e' : newB (st.n + σ.bound.length) v
      · exact absurd ⟨e, by rw [hn1]; exact e'⟩ hv
      · rfl
  have habT : AbsR T st2.θ := by
    intro w
    by_cases hw : Iv w
    · show rsb T ((th st2).img w) = T.img w
      rw [fixIv w hw, rsb_vty]
    · show rsb T ((th st2).img w) = T.img w
      rw [rsb_congr _ fun u hu => agree u (imgIv w hw u hu), hab w, agree w hw]
  have hfxT : FixR (rigidFromD n0) T := fun v hv => by
    rw [hag1 v (newB_mono hi.inv.le (by rw [rigidFromD_eq] at hv; simpa using hv))]; exact hfx v hv
  have hreT : RespR T := fun a => by
    by_cases e : T.t a = U.t a
    · rw [e]; exact hre a
    · exact hcls a e
  have hargT : ∀ τ ∈ argtys, rsb T τ = rsb U τ := by
    intro τ hτ
    rw [← absR_rsb habT, rsb_congr (s := T) (t := U) _ fun u hu => agree u (notIv_reach u (hreach τ hτ u hu)),
      absS_rsb hab]
  rw [hτb, arrows_sbD] at hT
  obtain ⟨hTs, -⟩ := arrows_inj (by rw [rsbList_length, rsbList_length, hlen]) hT
  refine ⟨hlen.symm, T, hfxT, hreT, habT, fun p hp => ?_⟩
  have hm := List.of_mem_zip hp
  have e2 : rsb T p.2 = rsb U p.1 := by
    have := zip_rsbList hTs.symm (p.1, p.2) (by
      have : (p.1, p.2) = p := rfl; rw [this]; exact hp)
    exact this.symm
  refine ⟨by rw [hargT p.1 hm.1, e2], by rw [hargT p.1 hm.1]; exact hcn p.1 hm.1⟩

end WDS

end StandardElm.Stat.Complete
