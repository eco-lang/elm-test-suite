/-
  A Standard Definition of Elm? Mechanisation: the conclusion of the induction for L10 (plan step
  11, milestone (b), section 8) and the ways its instances compose.

  For a call of W in context `C` from state `st` to `st'` (`PostK`):
  * the run is a segment moving only variables reachable from `C` or new (`Reach`);
  * the types it returns (`tys`) are W's types (`OkT`, `AnyT`), their images reachable;
  * the closures it took inside left constraints `K` (`KSeg`): the generalised variables are
    new, avoided by the images of the old variables and of the types returned;
  * every substitution `s` that fixes the rigid variables, absorbs the final one and respects the
    constraints satisfies `Chk` (for a phrase: the checker accepts `s` applied to the result).

  `PostK.seq` (a call after another), `PostK.fresh` (a fresh variable), `PostK.unify` (a `unify`
  step) and `PostK.weaken` build the conclusions of the cases of the induction.
-/
import StandardElmMech.Stat.Complete.WSoundBase

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

theorem mem_scheme_tyvars {v : BVar} {σ : Scheme} :
    v ∈ σ.tyvars ↔ v ∈ σ.body.vars ∧ v.isBnd = false ∧ v ∉ σ.bound := by
  simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
  exact and_assoc

theorem lookupVal_unq (C : Ctx) (x : String) : C.lookupVal ⟨none, x⟩ = FMap.find? C.E.VE x := rfl

theorem new_of_new {n m : Nat} (h : n ≤ m) {a : TyVar} (ha : a.isNew m = true) : a.isNew n = true := by
  cases e : a.isNew n
  · rw [isNew_mono h e] at ha; cases ha
  · rfl

/-! ## What a phrase can reach -/

/-- New, or a variable of the image of a free variable of the context. -/
def Reach (θ : FSub) (C : Ctx) (n : Nat) (b : TyVar) : Prop :=
  b.isNew n = true ∨ ∃ c, BVar.ty c ∈ C.tyvars ∧ TV b (θ c)

/-- The precondition of a call of W. -/
structure SPre (n0 : Nat) (C : Ctx) (st : WSt) : Prop where
  inv : SInv n0 st
  any : SAny n0 (lk st.θ)
  ctxW : CtxW st.n C
  rest : ∀ a, BVar.ty a ∈ restTv C → rigidFrom n0 a = true
  cany : ∀ c, BVar.ty c ∈ C.tyvars → AnyV n0 c

theorem SPre.old {n0 : Nat} {C : Ctx} {st : WSt} (h : SPre n0 C st) {c : TyVar} (hc : BVar.ty c ∈ C.tyvars) :
    c.isNew st.n = false := by
  rcases mem_ctx_tyvars.mp hc with hr | ⟨x, p, hf, hp⟩
  · have := h.rest c hr
    rw [rigidFrom_eq] at this
    exact isNew_mono h.inv.le (by simpa using this)
  · have hs := h.ctxW ⟨none, x⟩ p.1 p.2 (by rw [lookupVal_unq, hf])
    obtain ⟨h1, -, h3⟩ := mem_scheme_tyvars.mp hp
    obtain ⟨a, e, -, h4⟩ := hs.2 _ h1 h3
    cases e; exact h4

theorem reach_shrink {n0 : Nat} {C : Ctx} {st st1 : WSt} (hs : Seg n0 (Reach (lk st.θ) C st.n) st st1)
    (hi : SInv n0 st) {c b : TyVar} (hc : BVar.ty c ∈ C.tyvars) (hb : TV b (lk st1.θ c)) :
    Reach (lk st.θ) C st.n b :=
  (moves_var hs.mv hs.abs hi.good.idem c b hb).elim (fun h => .inr ⟨c, hc, h⟩) id

theorem reach_same {n0 : Nat} {C : Ctx} {st st1 : WSt} (hs : Seg n0 (Reach (lk st.θ) C st.n) st st1)
    (hi : SInv n0 st) : ∀ b, Reach (lk st1.θ) C st1.n b → Reach (lk st.θ) C st.n b := by
  rintro b (hb | ⟨c, hc, hb⟩)
  · exact .inl (new_of_new hs.le hb)
  · exact reach_shrink hs hi hc hb

theorem mem_plusVE_tyvars {v : BVar} {C : Ctx} {VE : ValEnv} (h : v ∈ (C.plusVE VE).tyvars) :
    v ∈ C.tyvars ∨ ∃ q ∈ VE, v ∈ q.2.1.tyvars := by
  rcases mem_ctx_tyvars.mp h with h | ⟨x, p, hf, hp⟩
  · exact .inl (mem_ctx_tyvars.mpr (.inl h))
  · simp only [Ctx.plusVE, FMap.find?_append] at hf
    cases h1 : FMap.find? VE x with
    | some p' =>
      rw [h1] at hf; simp only [Option.some_or, Option.some.injEq] at hf; subst hf
      exact .inr ⟨(x, p'), find?_mem h1, hp⟩
    | none =>
      rw [h1] at hf; simp only [Option.none_or] at hf
      exact .inl (mem_ctx_tyvars.mpr (.inr ⟨x, p, hf, hp⟩))

theorem reach_plusVE {n0 : Nat} {C : Ctx} {VE : ValEnv} {st st1 : WSt}
    (hs : Seg n0 (Reach (lk st.θ) C st.n) st st1) (hi : SInv n0 st)
    (hVE : ∀ q ∈ VE, ∀ b, TV b (sb (lk st1.θ) q.2.1.body) → Reach (lk st.θ) C st.n b) :
    ∀ b, Reach (lk st1.θ) (C.plusVE VE) st1.n b → Reach (lk st.θ) C st.n b := by
  rintro b (hb | ⟨c, hc, hb⟩)
  · exact .inl (new_of_new hs.le hb)
  · rcases mem_plusVE_tyvars hc with hc | ⟨q, hq, hcq⟩
    · exact reach_shrink hs hi hc hb
    · exact hVE q hq b (vars_sb_of _ _ c _ (mem_scheme_tyvars.mp hcq).1 hb)

theorem SPre.plusVE {n0 : Nat} {C : Ctx} {VE : ValEnv} {st st1 : WSt} (hp : SPre n0 C st) (hle : st.n ≤ st1.n)
    (hi : SInv n0 st1) (ha : SAny n0 (lk st1.θ))
    (hVE : ∀ q ∈ VE, SchW st1.n q.2.1 ∧ ∀ c, BVar.ty c ∈ q.2.1.tyvars → AnyV n0 c) : SPre n0 (C.plusVE VE) st1 :=
  ⟨hi, ha, (hp.ctxW.mono hle).plusVE fun q hq => (hVE q hq).1, hp.rest, fun c hc => by
    rcases mem_plusVE_tyvars hc with hc | ⟨q, hq, hcq⟩
    · exact hp.cany c hc
    · exact (hVE q hq).2 c hcq⟩

/-- A monotype W built, as a scheme of the context. -/
theorem monoEnt {n0 n : Nat} {q : String × (Scheme × IdStatus)} (hb : q.2.1.bound = []) (hok : OkT n q.2.1.body)
    (ha : AnyT n0 q.2.1.body) : SchW n q.2.1 ∧ ∀ c, BVar.ty c ∈ q.2.1.tyvars → AnyV n0 c := by
  obtain ⟨x, ⟨bd, body⟩, st⟩ := q
  simp only at hb hok ha ⊢; subst hb
  exact ⟨SchW_mono_scheme hok, fun c hc => ha c (mem_scheme_tyvars.mp hc).1⟩

/-! ## Constraints recorded at closures -/

abbrev ConW := List BVar × List Ty

/-- A variable generalised at the closure: in a type of the group, not free in the context. -/
def InG (k : ConW) (b : TyVar) : Prop := (∃ τ ∈ k.2, TV b τ) ∧ BVar.ty b ∉ k.1

/-- `s` neither binds a generalised variable nor puts one in the image of a free variable. -/
def DeadC (k : ConW) (s : FSub) : Prop :=
  ∀ b, InG k b → s b = .var b ∧ ∀ a, BVar.ty a ∈ k.1 → ¬ TV b (s a)

def DeadK (K : List ConW) (s : FSub) : Prop := ∀ k ∈ K, DeadC k s

def AvoidK (K : List ConW) (P : TyVar → Prop) : Prop := ∀ k ∈ K, ∀ b, InG k b → ¬ P b

theorem deadC_seg {k : ConW} {P : TyVar → Prop} {θ θ' : FSub} (hd : DeadC k θ) (hm : Moves P θ θ')
    (ha : Absorbs θ' θ) (hi : Idem θ) (hP : ∀ b, InG k b → ¬ P b) : DeadC k θ' := by
  intro b hb
  obtain ⟨h1, h2⟩ := hd b hb
  refine ⟨Classical.byContradiction fun h => hP b hb (hm b h1 h).1, fun a ha' hba => ?_⟩
  rcases moves_var hm ha hi a b hba with h | h
  · exact h2 a ha' h
  · exact hP b hb h

structure KSeg (K : List ConW) (st st' : WSt) : Prop where
  dead : DeadK K (lk st'.θ)
  zone : ∀ k ∈ K, ∀ b, InG k b → b.isNew st.n = true ∧ b.isNew st'.n = false
  old : ∀ k ∈ K, ∀ b, InG k b → ∀ a, a.isNew st.n = false → ¬ TV b (lk st'.θ a)

theorem KSeg.nil (st st' : WSt) : KSeg [] st st' :=
  ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

theorem KSeg.seg {n0 : Nat} {K : List ConW} {P : TyVar → Prop} {st st1 st2 : WSt} (h : KSeg K st st1)
    (hs : Seg n0 P st1 st2) (hi : SInv n0 st1) (hav : AvoidK K P) : KSeg K st st2 :=
  ⟨fun k hk => deadC_seg (h.dead k hk) hs.mv hs.abs hi.good.idem (hav k hk),
   fun k hk b hb => ⟨(h.zone k hk b hb).1, isNew_mono hs.le (h.zone k hk b hb).2⟩,
   fun k hk b hb a ha => avoid_seg (τ := .var a) hs.mv hs.abs hi.good.idem (h.old k hk b hb a ha) (hav k hk b hb)⟩

theorem KSeg.append {n0 : Nat} {K1 K2 : List ConW} {P : TyVar → Prop} {st st1 st2 : WSt}
    (h1 : KSeg K1 st st1) (hs : Seg n0 P st1 st2) (hi : SInv n0 st1) (hav : AvoidK K1 P) (h2 : KSeg K2 st1 st2)
    (hle : st.n ≤ st1.n) : KSeg (K2 ++ K1) st st2 := by
  have h1' := h1.seg hs hi hav
  refine ⟨fun k hk => ?_, fun k hk b hb => ?_, fun k hk b hb a ha => ?_⟩
  · rcases List.mem_append.mp hk with hk | hk
    · exact h2.dead k hk
    · exact h1'.dead k hk
  · rcases List.mem_append.mp hk with hk | hk
    · exact ⟨new_of_new hle (h2.zone k hk b hb).1, (h2.zone k hk b hb).2⟩
    · exact h1'.zone k hk b hb
  · rcases List.mem_append.mp hk with hk | hk
    · exact h2.old k hk b hb a (isNew_mono hle ha)
    · exact h1'.old k hk b hb a ha

theorem KSeg.avoid_old {K : List ConW} {st st' : WSt} (h : KSeg K st st') {τ : Ty} (hτ : OkT st.n τ) :
    ∀ k ∈ K, ∀ b, InG k b → ¬ TV b (sb (lk st'.θ) τ) := by
  intro k hk b hb hbt
  obtain ⟨a, ha, hba⟩ := tyvar_sb hbt
  obtain ⟨a', e, -, hold⟩ := hτ _ ha
  cases e
  exact h.old k hk b hb a hold hba

theorem avoid_same {n0 : Nat} {C : Ctx} {st st1 : WSt} {K : List ConW} (hp : SPre n0 C st) (hk : KSeg K st st1) :
    AvoidK K (Reach (lk st1.θ) C st1.n) := by
  rintro k hkK b hb (h | ⟨c, hc, h⟩)
  · rw [(hk.zone k hkK b hb).2] at h; cases h
  · exact hk.old k hkK b hb c (hp.old hc) h

theorem avoid_plusVE {n0 : Nat} {C : Ctx} {VE : ValEnv} {st st1 : WSt} {K : List ConW} (hp : SPre n0 C st)
    (hk : KSeg K st st1) (hVE : ∀ q ∈ VE, ∀ k ∈ K, ∀ b, InG k b → ¬ TV b (sb (lk st1.θ) q.2.1.body)) :
    AvoidK K (Reach (lk st1.θ) (C.plusVE VE) st1.n) := by
  rintro k hkK b hb (h | ⟨c, hc, h⟩)
  · rw [(hk.zone k hkK b hb).2] at h; cases h
  · rcases mem_plusVE_tyvars hc with hc | ⟨q, hq, hcq⟩
    · exact hk.old k hkK b hb c (hp.old hc) h
    · exact hVE q hq k hkK b hb (vars_sb_of _ _ c _ (mem_scheme_tyvars.mp hcq).1 h)

/-! ## The conclusion -/

/-- The substitutions the conclusion is about: fixing the rigid variables (`bnd` among them),
    putting no `bnd` variable in an image, and respecting classes. -/
structure SOk (n0 : Nat) (s : FSub) : Prop where
  fix : FixesR (rigidFrom n0) s
  img : ∀ a, a.isBndT = false → ∀ v ∈ (s a).vars, ∃ b, v = .ty b ∧ b.isBndT = false
  resp : RespC s

/-- Every variable of the types of `l` is a variable of a type of `l'`. -/
def Cov (l l' : List Ty) : Prop := ∀ τ ∈ l, ∀ v ∈ τ.vars, ∃ τ' ∈ l', v ∈ τ'.vars

structure PostK (n0 : Nat) (C : Ctx) (st st' : WSt) (tys : List Ty) (Chk : FSub → Prop) (K : List ConW) : Prop where
  seg : Seg n0 (Reach (lk st.θ) C st.n) st st'
  okT : ∀ τ ∈ tys, OkT st'.n τ ∧ AnyT n0 τ
  reach : ∀ τ ∈ tys, ∀ b, TV b (sb (lk st'.θ) τ) → Reach (lk st.θ) C st.n b
  ks : KSeg K st st'
  tyav : ∀ τ ∈ tys, ∀ k ∈ K, ∀ b, InG k b → ¬ TV b (sb (lk st'.θ) τ)
  chk : ∀ s, SOk n0 s → Absorbs s (lk st'.θ) → DeadK K s → Chk s

def Post (n0 : Nat) (C : Ctx) (st st' : WSt) (tys : List Ty) (Chk : FSub → Prop) : Prop :=
  ∃ K, PostK n0 C st st' tys Chk K

theorem PostK.weaken {n0 : Nat} {C : Ctx} {st st' : WSt} {tys tys' : List Ty} {Chk Chk' : FSub → Prop}
    {K : List ConW} (h : PostK n0 C st st' tys Chk K) (hc : Cov tys' tys) (hC : ∀ s, SOk n0 s → Chk s → Chk' s) :
    PostK n0 C st st' tys' Chk' K := by
  refine ⟨h.seg, fun τ hτ => ⟨fun v hv => ?_, fun b hb => ?_⟩, fun τ hτ b hb => ?_, h.ks,
    fun τ hτ k hk b hb hbt => ?_, fun s h1 h2 h3 => hC s h1 (h.chk s h1 h2 h3)⟩
  · obtain ⟨τ', h1, h2⟩ := hc τ hτ v hv; exact (h.okT τ' h1).1 v h2
  · obtain ⟨τ', h1, h2⟩ := hc τ hτ _ hb; exact (h.okT τ' h1).2 b h2
  · obtain ⟨a, ha, hba⟩ := tyvar_sb hb
    obtain ⟨τ', h1, h2⟩ := hc τ hτ _ ha
    exact h.reach τ' h1 b (vars_sb_of _ _ a _ h2 hba)
  · obtain ⟨a, ha, hba⟩ := tyvar_sb hbt
    obtain ⟨τ', h1, h2⟩ := hc τ hτ _ ha
    exact h.tyav τ' h1 k hk b hb (vars_sb_of _ _ a _ h2 hba)

theorem PostK.seq {n0 : Nat} {C C' : Ctx} {st st1 st2 : WSt} {tys1 tys2 : List Ty} {Chk1 Chk2 : FSub → Prop}
    {K1 K2 : List ConW} (h1 : PostK n0 C st st1 tys1 Chk1 K1) (h2 : PostK n0 C' st1 st2 tys2 Chk2 K2)
    (hR : ∀ b, Reach (lk st1.θ) C' st1.n b → Reach (lk st.θ) C st.n b)
    (hA : AvoidK K1 (Reach (lk st1.θ) C' st1.n)) :
    PostK n0 C st st2 (tys1 ++ tys2) (fun s => Chk1 s ∧ Chk2 s) (K2 ++ K1) := by
  have hi1 := h1.seg.inv
  refine ⟨h1.seg.trans (h2.seg.mono hR), fun τ hτ => ?_, fun τ hτ b hb => ?_,
    h1.ks.append h2.seg hi1 hA h2.ks h1.seg.le, fun τ hτ k hk b hb => ?_, fun s hs ha hd => ?_⟩
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact ⟨(h1.okT τ hτ).1.mono h2.seg.le, (h1.okT τ hτ).2⟩
    · exact h2.okT τ hτ
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact (moves_ty' h2.seg.mv h2.seg.abs hi1.good.idem τ b hb).elim (h1.reach τ hτ b) (hR b)
    · exact hR b (h2.reach τ hτ b hb)
  · rcases List.mem_append.mp hτ with hτ | hτ <;> rcases List.mem_append.mp hk with hk | hk
    · exact h2.ks.avoid_old (h1.okT τ hτ).1 k hk b hb
    · exact avoid_seg h2.seg.mv h2.seg.abs hi1.good.idem (h1.tyav τ hτ k hk b hb) (hA k hk b hb)
    · exact h2.tyav τ hτ k hk b hb
    · exact fun ht => hA k hk b hb (h2.reach τ hτ b ht)
  · have hd1 : DeadK K1 s := fun k hk => hd k (List.mem_append_right _ hk)
    have hd2 : DeadK K2 s := fun k hk => hd k (List.mem_append_left _ hk)
    exact ⟨h1.chk s hs (absorbs_trans ha h2.seg.abs) hd1, h2.chk s hs ha hd2⟩

theorem lk_fresh_self {n0 : Nat} {st : WSt} {c : Cls} (hi : SInv n0 st) :
    lk st.θ (.fresh st.n c) = .var (.fresh st.n c) := by
  rcases hi.ok (.fresh st.n c) with e | ⟨e, -⟩
  · exact e
  · simp [TyVar.isNew] at e

theorem PostK.freshC {n0 : Nat} {C : Ctx} {st st1 : WSt} {tys : List Ty} {Chk : FSub → Prop} {K : List ConW}
    (c : Cls) (h : PostK n0 C st st1 tys Chk K) :
    PostK n0 C st { st1 with n := st1.n + 1 } (tys ++ [.var (.fresh st1.n c)]) Chk K := by
  have hi1 := h.seg.inv
  have hfix := lk_fresh_self (c := c) hi1
  refine ⟨h.seg.trans (seg_fresh hi1 h.seg.any), fun τ hτ => ?_, fun τ hτ b hb => ?_,
    ⟨h.ks.dead, fun k hk b hb => ⟨(h.ks.zone k hk b hb).1, isNew_mono (Nat.le_succ _) (h.ks.zone k hk b hb).2⟩,
      h.ks.old⟩, fun τ hτ k hk b hb => ?_, h.chk⟩
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact ⟨(h.okT τ hτ).1.mono (Nat.le_succ _), (h.okT τ hτ).2⟩
    · simp only [List.mem_singleton] at hτ; subst hτ; exact ⟨okT_freshC, anyT_fresh _ _⟩
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact h.reach τ hτ b hb
    · simp only [List.mem_singleton] at hτ; subst hτ
      change TV b (lk st1.θ _) at hb
      rw [hfix] at hb; simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq] at hb; subst hb
      exact .inl (by simp [TyVar.isNew]; exact h.seg.le)
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact h.tyav τ hτ k hk b hb
    · simp only [List.mem_singleton] at hτ; subst hτ
      change ¬ TV b (lk st1.θ _); rw [hfix]
      simp only [TV, Ty.vars, List.mem_singleton, BVar.ty.injEq]
      rintro rfl
      have := (h.ks.zone k hk _ hb).2; simp [TyVar.isNew] at this

theorem PostK.fresh {n0 : Nat} {C : Ctx} {st st1 : WSt} {tys : List Ty} {Chk : FSub → Prop} {K : List ConW}
    (h : PostK n0 C st st1 tys Chk K) :
    PostK n0 C st { st1 with n := st1.n + 1 } (tys ++ [.var (.fresh st1.n .any)]) Chk K := h.freshC .any

theorem PostK.unify {fuel n0 : Nat} {C : Ctx} {st st2 st3 : WSt} {tys : List Ty} {Chk : FSub → Prop}
    {K : List ConW} {τ1 τ2 : Ty} {u : Unit} (h : PostK n0 C st st2 tys Chk K) (hc : Cov [τ1, τ2] tys)
    (hu : unifyW fuel (rigidFrom n0) τ1 τ2 st2 = .ok u st3) :
    PostK n0 C st st3 tys (fun s => Chk s ∧ sb s τ1 = sb s τ2) K := by
  have h' := h.weaken (tys' := [τ1, τ2]) hc (fun _ _ x => x)
  have hi2 := h.seg.inv
  have m1 : τ1 ∈ [τ1, τ2] := by simp
  have m2 : τ2 ∈ [τ1, τ2] := by simp
  obtain ⟨hs, hus⟩ := seg_unify hi2 h.seg.any (h'.okT τ1 m1).1 (h'.okT τ2 m2).1 (h'.okT τ1 m1).2 (h'.okT τ2 m2).2 hu
  have hP : ∀ b, (TV b (sb (lk st2.θ) τ1) ∨ TV b (sb (lk st2.θ) τ2) ∨ b.isNew st2.n = true) →
      Reach (lk st.θ) C st.n b := by
    rintro b (hb | hb | hb)
    · exact h'.reach τ1 m1 b hb
    · exact h'.reach τ2 m2 b hb
    · exact .inl (new_of_new h.seg.le hb)
  have hav : AvoidK K (fun b => TV b (sb (lk st2.θ) τ1) ∨ TV b (sb (lk st2.θ) τ2) ∨ b.isNew st2.n = true) := by
    rintro k hk b hb (h1 | h1 | h1)
    · exact h'.tyav τ1 m1 k hk b hb h1
    · exact h'.tyav τ2 m2 k hk b hb h1
    · rw [(h.ks.zone k hk b hb).2] at h1; cases h1
  exact ⟨h.seg.trans (hs.mono hP), fun τ hτ => ⟨(h.okT τ hτ).1.mono hs.le, (h.okT τ hτ).2⟩,
    fun τ hτ b hb => (moves_ty' hs.mv hs.abs hi2.good.idem τ b hb).elim (h.reach τ hτ b) (hP b),
    h.ks.seg hs hi2 hav,
    fun τ hτ k hk b hb => avoid_seg hs.mv hs.abs hi2.good.idem (h.tyav τ hτ k hk b hb) (hav k hk b hb),
    fun s h1 h2 h3 => ⟨h.chk s h1 (absorbs_trans h2 hs.abs) h3, hus s h2⟩⟩

theorem covSub {l l' : List Ty} (h : ∀ τ ∈ l, τ ∈ l') : Cov l l' := fun τ hτ v hv => ⟨τ, h τ hτ, hv⟩

theorem cov_refl (l : List Ty) : Cov l l := covSub fun _ h => h

theorem SPre.later {n0 : Nat} {C : Ctx} {st st1 : WSt} {P : TyVar → Prop} (hp : SPre n0 C st) (hs : Seg n0 P st st1) :
    SPre n0 C st1 := ⟨hs.inv, hs.any, hp.ctxW.mono hs.le, hp.rest, hp.cany⟩

/-- A call that changed nothing yet, with types built from the context and the state. -/
theorem PostK.now {n0 : Nat} {C : Ctx} {st : WSt} {tys : List Ty} {Chk : FSub → Prop} (hp : SPre n0 C st)
    (hok : ∀ τ ∈ tys, OkT st.n τ ∧ AnyT n0 τ)
    (hr : ∀ τ ∈ tys, ∀ b, TV b (sb (lk st.θ) τ) → Reach (lk st.θ) C st.n b)
    (hc : ∀ s, SOk n0 s → Absorbs s (lk st.θ) → Chk s) : PostK n0 C st st tys Chk [] :=
  ⟨Seg.refl hp.inv hp.any, hok, hr, KSeg.nil _ _, (fun _ _ _ h => nomatch h), fun s h1 h2 _ => hc s h1 h2⟩

theorem PostK.start {n0 : Nat} {C : Ctx} {st : WSt} (hp : SPre n0 C st) : PostK n0 C st st [] (fun _ => True) [] :=
  PostK.now hp (fun _ h => nomatch h) (fun _ h => nomatch h) fun _ _ _ => trivial

/-- A closed type, now. -/
theorem PostK.closed {n0 : Nat} {C : Ctx} {st : WSt} {τ : Ty} {Chk : FSub → Prop} (hp : SPre n0 C st)
    (hv : τ.vars = []) (hc : ∀ s, SOk n0 s → Chk s) : PostK n0 C st st [τ] Chk [] :=
  PostK.now hp (fun τ' h => by
      simp only [List.mem_singleton] at h; subst h; exact ⟨OkT_of_vars_nil hv, anyT_of_vars_nil hv⟩)
    (fun τ' h b hb => by
      simp only [List.mem_singleton] at h; subst h
      rw [sb_eq_self_iff.mpr fun a ha => by simp [hv] at ha] at hb; simp [TV, hv] at hb)
    fun s h1 _ => hc s h1

end StandardElm.Stat.Complete
