/-
  A Standard Definition of Elm? Mechanisation: the bookkeeping of L10 for W with records and rows
  (plan step 11, milestone (d)); WSoundBase.lean and WSoundPost.lean for `inferExpWD`, with
  substitutions of type and row variables (`RSub`) and variables of both sorts (`BVar`).

  * `SInvW`: W's state invariant `SInvD` and no `bnd` variable in an image (`NBθ`);
  * `SegD`: a segment of a run (counter, invariant, absorption, `MovesD`); a `unify` step is one,
    by the structure of the unification alone (`seg_unify`, from `rLoop_struct`), and its two
    types are unified by every later substitution once their images are canonical (A23);
  * `DeadC`: the constraint a closure records ("dead" variables: never bound nor put in the
    image of a free variable later), row variables included;
  * `PostK`: the conclusion of the induction, as for W, and the ways its instances compose.
-/
import StandardElmMech.Stat.Complete.WDSoundMgu
import StandardElmMech.Stat.Complete.WSound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

namespace WDS

/-- W's accumulated substitution. -/
abbrev th (st : WDSt) : RSub := toRS st.θ

theorem nb_of_new {n : Nat} {w : BVar} (h : newB n w = true) : w.isBnd = false := by
  rcases w with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [newB, BVar.isBnd, TyVar.isNew]

/-- No `bnd` variable in the image of a variable that is not `bnd`. -/
def NBθ (θ : RBnd) : Prop := ∀ v, v.isBnd = false → ∀ w ∈ ((toRS θ).img v).vars, w.isBnd = false

structure SInvW (n0 : Nat) (st : WDSt) : Prop where
  inv : SInvD n0 st
  nb : NBθ st.θ

theorem SInvW.fresh {n0 : Nat} {st : WDSt} (h : SInvW n0 st) : SInvW n0 { st with n := st.n + 1 } :=
  ⟨h.inv.fresh, h.nb⟩

theorem SInvW.mono {n0 : Nat} {st : WDSt} (h : SInvW n0 st) {m : Nat} (hm : st.n ≤ m) : SInvW n0 { st with n := m } :=
  ⟨h.inv.mono hm, h.nb⟩

theorem SInvW.idem {n0 : Nat} {st : WDSt} (h : SInvW n0 st) : IdemS (th st) := h.inv.good.idem

theorem SInvW.unbound_new {n0 : Nat} {st : WDSt} (h : SInvW n0 st) {v : BVar} (hv : newB st.n v = true) :
    (th st).img v = vty v := unbound_of_new h.inv.good hv

/-! ## Segments of a run -/

structure SegD (n0 : Nat) (P : BVar → Prop) (st st' : WDSt) : Prop where
  le : st.n ≤ st'.n
  inv : SInvW n0 st'
  abs : AbsS (th st') (th st)
  mv : MovesD P (th st) (th st')

theorem SegD.refl {n0 : Nat} {P : BVar → Prop} {st : WDSt} (hi : SInvW n0 st) : SegD n0 P st st :=
  ⟨Nat.le_refl _, hi, absS_self hi.idem, moves_refl _ _⟩

theorem SegD.trans {n0 : Nat} {P : BVar → Prop} {st st1 st2 : WDSt} (h1 : SegD n0 P st st1) (h2 : SegD n0 P st1 st2) :
    SegD n0 P st st2 :=
  ⟨Nat.le_trans h1.le h2.le, h2.inv, absS_trans h2.abs h1.abs, moves_trans h1.mv h2.mv h2.abs h1.inv.idem⟩

theorem SegD.mono {n0 : Nat} {P Q : BVar → Prop} {st st' : WDSt} (h : SegD n0 P st st') (hPQ : ∀ b, P b → Q b) :
    SegD n0 Q st st' := ⟨h.le, h.inv, h.abs, moves_mono h.mv hPQ⟩

theorem seg_fresh {n0 : Nat} {P : BVar → Prop} {st : WDSt} (hi : SInvW n0 st) : SegD n0 P st { st with n := st.n + 1 } :=
  ⟨Nat.le_succ _, hi.fresh, absS_self hi.idem, moves_refl _ _⟩

theorem seg_up {n0 : Nat} {P : BVar → Prop} {st : WDSt} (hi : SInvW n0 st) {m : Nat} (hm : st.n ≤ m) :
    SegD n0 P st { st with n := m } := ⟨hm, hi.mono hm, absS_self hi.idem, moves_refl _ _⟩

/-- `unify` in W's state: a segment moving only variables of the substituted equation and new
    ones; once the two images are canonical, every substitution absorbing the new one unifies
    the two types. -/
theorem seg_unify {fuel n0 : Nat} {τ1 τ2 : Ty} {st st' : WDSt} {u : Unit} (hi : SInvW n0 st)
    (hτ1 : OkTD st.n τ1) (hτ2 : OkTD st.n τ2) (h : unifyWD fuel (rigidFromD n0) τ1 τ2 st = .ok u st') :
    SegD n0 (fun b => b ∈ (rsb (th st) τ1).vars ∨ b ∈ (rsb (th st) τ2).vars ∨ newB st.n b = true) st st' ∧
      (cnB (rsb (th st) τ1) = true → cnB (rsb (th st) τ2) = true → ∀ s, AbsR s st'.θ → rsb s τ1 = rsb s τ2) := by
  have hu := h
  refine ⟨?_, fun c1 c2 s hs => ((unifyWD_ok (newFlexR_rigidFromD hi.inv.le) hi.inv.good hτ1.old hτ2.old c1 c2 hu).2.2.1
    s hs).1⟩
  unfold unifyWD at h
  split at h
  · rename_i θ' n' hl
    simp only [WDOut.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
    have hv1 := img_vars hi.inv.good hτ1.old
    have hv2 := img_vars hi.inv.good hτ2.old
    have hE : EOk st.θ st.n [(rsb (th st) τ1, rsb (th st) τ2)] := fun w hw => by
      simp only [bvars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hw
      rcases hw with hw | hw
      · exact hv1 w hw
      · exact hv2 w hw
    obtain ⟨g', hn, ha, hm⟩ := rLoop_struct (P := fun b => b ∈ (rsb (th st) τ1).vars ∨ b ∈ (rsb (th st) τ2).vars ∨
      newB st.n b = true) fuel _ _ _ _ _ _ hi.inv.good hE (fun w hw => by
        simp only [bvars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hw
        rcases hw with hw | hw
        · exact .inl hw
        · exact .inr (.inl hw)) (fun w hw => .inr (.inr hw)) hl
    have nbτ : ∀ τ, OkTD st.n τ → ∀ w ∈ (rsb (th st) τ).vars, w.isBnd = false := fun τ hτ w hw => by
      obtain ⟨u, hu, hwu⟩ := (mem_vars_rsb _ _ w).mp hw
      exact hi.nb u (hτ u hu).1 w hwu
    obtain ⟨-, -, -, hm2⟩ := rLoop_struct (P := fun b => b.isBnd = false) fuel _ _ _ _ _ _ hi.inv.good hE
      (fun w hw => by
        simp only [bvars, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hw
        rcases hw with hw | hw
        · exact nbτ τ1 hτ1 w hw
        · exact nbτ τ2 hτ2 w hw) (fun w hw => nb_of_new hw) hl
    refine ⟨hn, ⟨⟨Nat.le_trans hi.inv.le hn, g'⟩, fun d hd w hw => ?_⟩, ha, hm⟩
    rcases moves_var hm2 ha hi.idem d w hw with h1 | h1
    · exact hi.nb d hd w h1
    · exact h1
  · cases h
  · cases h

/-! ## What a phrase can reach -/

def Reach (θ : RSub) (C : Ctx) (n : Nat) (b : BVar) : Prop :=
  newB n b = true ∨ ∃ c ∈ C.tyvars, b ∈ (θ.img c).vars

theorem new_of_new {n m : Nat} (h : n ≤ m) {v : BVar} (hv : newB m v = true) : newB n v = true := by
  cases e : newB n v
  · rw [newB_mono h e] at hv; cases hv
  · rfl

/-- Constructor lookups of the context: those of the root (`L`). -/
def ConsOK (L : LongId → Option Scheme) (C : Ctx) : Prop :=
  ∀ lv σ, C.lookupVal lv = some (σ, .c) → L lv = some σ

/-- The precondition of a call of W. -/
structure SPre (n0 : Nat) (L : LongId → Option Scheme) (C : Ctx) (st : WDSt) : Prop where
  inv : SInvW n0 st
  ctxW : CtxWD st.n C
  rest : ∀ v ∈ restTv C, rigidFromD n0 v = true
  cons : ConsOK L C

theorem SPre.old {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} (h : SPre n0 L C st) {c : BVar}
    (hc : c ∈ C.tyvars) : newB st.n c = false := by
  rcases mem_ctx_tyvars.mp hc with hr | ⟨x, p, hf, hp⟩
  · have := h.rest c hr
    rw [rigidFromD_eq] at this
    exact newB_mono h.inv.inv.le (by simpa using this)
  · have hs := h.ctxW ⟨none, x⟩ p.1 p.2 (by rw [lookupVal_unq, hf])
    obtain ⟨h1, -, h3⟩ := mem_scheme_tyvars.mp hp
    exact (hs.2 _ h1 h3).2

theorem SPre.later {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st st1 : WDSt} {P : BVar → Prop}
    (hp : SPre n0 L C st) (hs : SegD n0 P st st1) : SPre n0 L C st1 :=
  ⟨hs.inv, hp.ctxW.mono hs.le, hp.rest, hp.cons⟩

theorem reach_shrink {n0 : Nat} {C : Ctx} {st st1 : WDSt} (hs : SegD n0 (Reach (th st) C st.n) st st1)
    (hi : SInvW n0 st) {c b : BVar} (hc : c ∈ C.tyvars) (hb : b ∈ ((th st1).img c).vars) : Reach (th st) C st.n b :=
  (moves_var hs.mv hs.abs hi.idem c b hb).elim (fun h => .inr ⟨c, hc, h⟩) id

theorem reach_same {n0 : Nat} {C : Ctx} {st st1 : WDSt} (hs : SegD n0 (Reach (th st) C st.n) st st1)
    (hi : SInvW n0 st) : ∀ b, Reach (th st1) C st1.n b → Reach (th st) C st.n b := by
  rintro b (hb | ⟨c, hc, hb⟩)
  · exact .inl (new_of_new hs.le hb)
  · exact reach_shrink hs hi hc hb

theorem reach_plusVE {n0 : Nat} {C : Ctx} {VE : ValEnv} {st st1 : WDSt}
    (hs : SegD n0 (Reach (th st) C st.n) st st1) (hi : SInvW n0 st)
    (hVE : ∀ q ∈ VE, ∀ b ∈ (rsb (th st1) q.2.1.body).vars, Reach (th st) C st.n b) :
    ∀ b, Reach (th st1) (C.plusVE VE) st1.n b → Reach (th st) C st.n b := by
  rintro b (hb | ⟨c, hc, hb⟩)
  · exact .inl (new_of_new hs.le hb)
  · rcases mem_plusVE_tyvars hc with hc | ⟨q, hq, hcq⟩
    · exact reach_shrink hs hi hc hb
    · exact hVE q hq b ((mem_vars_rsb _ _ b).mpr ⟨c, (mem_scheme_tyvars.mp hcq).1, hb⟩)

/-- Status `v` only. -/
def AllV (VE : ValEnv) : Prop := ∀ q ∈ VE, q.2.2 = .v

theorem consOK_plusVE {L : LongId → Option Scheme} {C : Ctx} {VE : ValEnv} (h : ConsOK L C) (hv : AllV VE) :
    ConsOK L (C.plusVE VE) := by
  intro lv σ hl
  rw [lookupVal_plusVE] at hl
  cases hq : lv.qual with
  | none =>
    rw [hq] at hl
    simp only at hl
    cases hf : FMap.find? VE lv.id with
    | none =>
      rw [hf] at hl; simp only [Option.none_or] at hl
      exact h lv σ (by simpa [Ctx.lookupVal, Env.lookupVal, hq] using hl)
    | some p =>
      rw [hf] at hl; simp only [Option.some_or, Option.some.injEq] at hl
      have := hv _ (find?_mem hf); rw [hl] at this; cases this
  | some m => rw [hq] at hl; exact h lv σ (by simpa [Ctx.lookupVal, Env.lookupVal, hq] using hl)

theorem SPre.plusVE {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {VE : ValEnv} {st st1 : WDSt}
    (hp : SPre n0 L C st) (hle : st.n ≤ st1.n) (hi : SInvW n0 st1) (hVE : ∀ q ∈ VE, SchWD st1.n q.2.1)
    (hv : AllV VE) : SPre n0 L (C.plusVE VE) st1 :=
  ⟨hi, CtxWD.plusVE (hp.ctxW.mono hle) hVE, hp.rest, consOK_plusVE hp.cons hv⟩

/-! ## Constraints recorded at closures -/

abbrev ConW := List BVar × List Ty

/-- A variable generalised at the closure: in a type of the group, not free in the context. -/
def InG (k : ConW) (b : BVar) : Prop := (∃ τ ∈ k.2, b ∈ τ.vars) ∧ b ∉ k.1

/-- `s` neither binds a generalised variable nor puts one in the image of a free variable. -/
def DeadC (k : ConW) (s : RSub) : Prop :=
  ∀ b, InG k b → s.img b = vty b ∧ ∀ a ∈ k.1, b ∉ (s.img a).vars

def DeadK (K : List ConW) (s : RSub) : Prop := ∀ k ∈ K, DeadC k s

def AvoidK (K : List ConW) (P : BVar → Prop) : Prop := ∀ k ∈ K, ∀ b, InG k b → ¬ P b

theorem avoid_seg {P : BVar → Prop} {θ θ' : RSub} (hm : MovesD P θ θ') (ha : AbsS θ' θ) (hi : IdemS θ)
    {τ : Ty} {b : BVar} (h1 : b ∉ (rsb θ τ).vars) (h2 : ¬ P b) : b ∉ (rsb θ' τ).vars := fun h =>
  (moves_ty' hm ha hi τ b h).elim h1 h2

theorem deadC_seg {k : ConW} {P : BVar → Prop} {θ θ' : RSub} (hd : DeadC k θ) (hm : MovesD P θ θ')
    (ha : AbsS θ' θ) (hi : IdemS θ) (hP : ∀ b, InG k b → ¬ P b) : DeadC k θ' := by
  intro b hb
  obtain ⟨h1, h2⟩ := hd b hb
  refine ⟨Classical.byContradiction fun h => hP b hb (hm b h1 h).1, fun a ha' hba => ?_⟩
  rcases moves_var hm ha hi a b hba with h | h
  · exact h2 a ha' h
  · exact hP b hb h

structure KSeg (K : List ConW) (st st' : WDSt) : Prop where
  dead : DeadK K (th st')
  zone : ∀ k ∈ K, ∀ b, InG k b → newB st.n b = true ∧ newB st'.n b = false
  old : ∀ k ∈ K, ∀ b, InG k b → ∀ a, newB st.n a = false → b ∉ ((th st').img a).vars

theorem KSeg.nil (st st' : WDSt) : KSeg [] st st' :=
  ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

theorem KSeg.seg {n0 : Nat} {K : List ConW} {P : BVar → Prop} {st st1 st2 : WDSt} (h : KSeg K st st1)
    (hs : SegD n0 P st1 st2) (hi : SInvW n0 st1) (hav : AvoidK K P) : KSeg K st st2 :=
  ⟨fun k hk => deadC_seg (h.dead k hk) hs.mv hs.abs hi.idem (hav k hk),
   fun k hk b hb => ⟨(h.zone k hk b hb).1, newB_mono hs.le (h.zone k hk b hb).2⟩,
   fun k hk b hb a ha => by
     have := avoid_seg (τ := vty a) hs.mv hs.abs hi.idem (by rw [rsb_vty]; exact h.old k hk b hb a ha) (hav k hk b hb)
     rwa [rsb_vty] at this⟩

theorem KSeg.append {n0 : Nat} {K1 K2 : List ConW} {P : BVar → Prop} {st st1 st2 : WDSt}
    (h1 : KSeg K1 st st1) (hs : SegD n0 P st1 st2) (hi : SInvW n0 st1) (hav : AvoidK K1 P) (h2 : KSeg K2 st1 st2)
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
    · exact h2.old k hk b hb a (newB_mono hle ha)
    · exact h1'.old k hk b hb a ha

theorem KSeg.avoid_old {K : List ConW} {st st' : WDSt} (h : KSeg K st st') {τ : Ty} (hτ : OkTD st.n τ) :
    ∀ k ∈ K, ∀ b, InG k b → b ∉ (rsb (th st') τ).vars := by
  intro k hk b hb hbt
  obtain ⟨a, ha, hba⟩ := (mem_vars_rsb _ _ b).mp hbt
  exact h.old k hk b hb a (hτ a ha).2 hba

theorem avoid_same {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st st1 : WDSt} {K : List ConW}
    (hp : SPre n0 L C st) (hk : KSeg K st st1) : AvoidK K (Reach (th st1) C st1.n) := by
  rintro k hkK b hb (h | ⟨c, hc, h⟩)
  · rw [(hk.zone k hkK b hb).2] at h; cases h
  · exact hk.old k hkK b hb c (hp.old hc) h

theorem avoid_plusVE {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {VE : ValEnv} {st st1 : WDSt}
    {K : List ConW} (hp : SPre n0 L C st) (hk : KSeg K st st1)
    (hVE : ∀ q ∈ VE, ∀ k ∈ K, ∀ b, InG k b → b ∉ (rsb (th st1) q.2.1.body).vars) :
    AvoidK K (Reach (th st1) (C.plusVE VE) st1.n) := by
  rintro k hkK b hb (h | ⟨c, hc, h⟩)
  · rw [(hk.zone k hkK b hb).2] at h; cases h
  · rcases mem_plusVE_tyvars hc with hc | ⟨q, hq, hcq⟩
    · exact hk.old k hkK b hb c (hp.old hc) h
    · exact hVE q hq k hkK b hb ((mem_vars_rsb _ _ b).mpr ⟨c, (mem_scheme_tyvars.mp hcq).1, h⟩)

/-! ## The conclusion -/

/-- The substitutions the conclusion is about: fixing the rigid variables (`bnd` among them),
    putting no `bnd` variable in an image, respecting classes. -/
structure SOk (n0 : Nat) (s : RSub) : Prop where
  fix : FixR (rigidFromD n0) s
  img : ∀ v, v.isBnd = false → ∀ w ∈ (s.img v).vars, w.isBnd = false
  resp : RespR s

theorem respR_toRS {R : RRigid} {n : Nat} {θ : RBnd} {E : Eqs} {X : List Ty} (g : GoodR R n θ E X) :
    RespR (toRS θ) := fun a => by
  show Adm a.cls ((FMap.find? θ (.ty a)).getD (.var a))
  cases hf : FMap.find? θ (.ty a) with
  | none => exact admC_self a
  | some τ => exact g.adm _ (rfind?_mem hf) a rfl

theorem SInvW.sok {n0 : Nat} {st : WDSt} (hi : SInvW n0 st) : SOk n0 (th st) :=
  ⟨fun v hv => goodR_fix hi.inv.good hv, hi.nb, respR_toRS hi.inv.good⟩

/-- Every variable of the types of `l` is a variable of a type of `l'`. -/
def Cov (l l' : List Ty) : Prop := ∀ τ ∈ l, ∀ v ∈ τ.vars, ∃ τ' ∈ l', v ∈ τ'.vars

structure PostK (n0 : Nat) (C : Ctx) (st st' : WDSt) (tys : List Ty) (Chk : RSub → Prop) (K : List ConW) : Prop where
  seg : SegD n0 (Reach (th st) C st.n) st st'
  okT : ∀ τ ∈ tys, OkTD st'.n τ
  reach : ∀ τ ∈ tys, ∀ b ∈ (rsb (th st') τ).vars, Reach (th st) C st.n b
  ks : KSeg K st st'
  tyav : ∀ τ ∈ tys, ∀ k ∈ K, ∀ b, InG k b → b ∉ (rsb (th st') τ).vars
  chk : ∀ s, SOk n0 s → AbsS s (th st') → DeadK K s → Chk s

def Post (n0 : Nat) (C : Ctx) (st st' : WDSt) (tys : List Ty) (Chk : RSub → Prop) : Prop :=
  ∃ K, PostK n0 C st st' tys Chk K

theorem vars_rsb_of {s : RSub} {τ : Ty} {a b : BVar} (ha : a ∈ τ.vars) (hb : b ∈ (s.img a).vars) :
    b ∈ (rsb s τ).vars := (mem_vars_rsb _ _ b).mpr ⟨a, ha, hb⟩

theorem PostK.weaken {n0 : Nat} {C : Ctx} {st st' : WDSt} {tys tys' : List Ty} {Chk Chk' : RSub → Prop}
    {K : List ConW} (h : PostK n0 C st st' tys Chk K) (hc : Cov tys' tys) (hC : ∀ s, SOk n0 s → Chk s → Chk' s) :
    PostK n0 C st st' tys' Chk' K := by
  refine ⟨h.seg, fun τ hτ v hv => ?_, fun τ hτ b hb => ?_, h.ks,
    fun τ hτ k hk b hb hbt => ?_, fun s h1 h2 h3 => hC s h1 (h.chk s h1 h2 h3)⟩
  · obtain ⟨τ', h1, h2⟩ := hc τ hτ v hv; exact h.okT τ' h1 v h2
  · obtain ⟨a, ha, hba⟩ := (mem_vars_rsb _ _ b).mp hb
    obtain ⟨τ', h1, h2⟩ := hc τ hτ _ ha
    exact h.reach τ' h1 b (vars_rsb_of h2 hba)
  · obtain ⟨a, ha, hba⟩ := (mem_vars_rsb _ _ b).mp hbt
    obtain ⟨τ', h1, h2⟩ := hc τ hτ _ ha
    exact h.tyav τ' h1 k hk b hb (vars_rsb_of h2 hba)

theorem PostK.seq {n0 : Nat} {C C' : Ctx} {st st1 st2 : WDSt} {tys1 tys2 : List Ty} {Chk1 Chk2 : RSub → Prop}
    {K1 K2 : List ConW} (h1 : PostK n0 C st st1 tys1 Chk1 K1) (h2 : PostK n0 C' st1 st2 tys2 Chk2 K2)
    (hR : ∀ b, Reach (th st1) C' st1.n b → Reach (th st) C st.n b)
    (hA : AvoidK K1 (Reach (th st1) C' st1.n)) :
    PostK n0 C st st2 (tys1 ++ tys2) (fun s => Chk1 s ∧ Chk2 s) (K2 ++ K1) := by
  have hi1 := h1.seg.inv
  refine ⟨h1.seg.trans (h2.seg.mono hR), fun τ hτ => ?_, fun τ hτ b hb => ?_,
    h1.ks.append h2.seg hi1 hA h2.ks h1.seg.le, fun τ hτ k hk b hb => ?_, fun s hs ha hd => ?_⟩
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact (h1.okT τ hτ).mono h2.seg.le
    · exact h2.okT τ hτ
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact (moves_ty' h2.seg.mv h2.seg.abs hi1.idem τ b hb).elim (h1.reach τ hτ b) (hR b)
    · exact hR b (h2.reach τ hτ b hb)
  · rcases List.mem_append.mp hτ with hτ | hτ <;> rcases List.mem_append.mp hk with hk | hk
    · exact h2.ks.avoid_old (h1.okT τ hτ) k hk b hb
    · exact avoid_seg h2.seg.mv h2.seg.abs hi1.idem (h1.tyav τ hτ k hk b hb) (hA k hk b hb)
    · exact h2.tyav τ hτ k hk b hb
    · exact fun ht => hA k hk b hb (h2.reach τ hτ b ht)
  · have hd1 : DeadK K1 s := fun k hk => hd k (List.mem_append_right _ hk)
    have hd2 : DeadK K2 s := fun k hk => hd k (List.mem_append_left _ hk)
    exact ⟨h1.chk s hs (absS_trans ha h2.seg.abs) hd1, h2.chk s hs ha hd2⟩

/-- A fresh variable `v` (type or row) added to the types returned. -/
theorem PostK.freshV {n0 : Nat} {C : Ctx} {st st1 : WDSt} {tys : List Ty} {Chk : RSub → Prop} {K : List ConW}
    (v : BVar) (hv : ∀ w ∈ (vty v).vars, newB st1.n w = true ∧ newB (st1.n + 1) w = false ∧ w.isBnd = false)
    (h : PostK n0 C st st1 tys Chk K) :
    PostK n0 C st { st1 with n := st1.n + 1 } (tys ++ [vty v]) Chk K := by
  have hi1 := h.seg.inv
  rw [vars_vty] at hv
  have hv' := hv v (List.mem_singleton_self _)
  have hfix : (th st1).img v = vty v := hi1.unbound_new hv'.1
  refine ⟨h.seg.trans (seg_fresh hi1), fun τ hτ => ?_, fun τ hτ b hb => ?_,
    ⟨h.ks.dead, fun k hk b hb => ⟨(h.ks.zone k hk b hb).1, newB_mono (Nat.le_succ _) (h.ks.zone k hk b hb).2⟩,
      h.ks.old⟩, fun τ hτ k hk b hb => ?_, h.chk⟩
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact (h.okT τ hτ).mono (Nat.le_succ _)
    · simp only [List.mem_singleton] at hτ; subst hτ
      intro w hw; rw [vars_vty, List.mem_singleton] at hw; subst hw; exact ⟨hv'.2.2, hv'.2.1⟩
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact h.reach τ hτ b hb
    · simp only [List.mem_singleton] at hτ; subst hτ
      change b ∈ (rsb (th st1) (vty v)).vars at hb
      rw [rsb_vty, hfix, vars_vty, List.mem_singleton] at hb; subst hb
      exact .inl (new_of_new h.seg.le hv'.1)
  · rcases List.mem_append.mp hτ with hτ | hτ
    · exact h.tyav τ hτ k hk b hb
    · simp only [List.mem_singleton] at hτ; subst hτ
      change b ∉ (rsb (th st1) (vty v)).vars
      rw [rsb_vty, hfix, vars_vty, List.mem_singleton]
      rintro rfl
      have := (h.ks.zone k hk _ hb).2; rw [hv'.1] at this; cases this

theorem fresh_ty_ok (n : Nat) (c : Cls) :
    ∀ w ∈ (vty (.ty (.fresh n c))).vars, newB n w = true ∧ newB (n + 1) w = false ∧ w.isBnd = false := by
  intro w hw; rw [vars_vty, List.mem_singleton] at hw; subst hw
  simp [newB, TyVar.isNew, BVar.isBnd]

theorem fresh_row_ok (n : Nat) :
    ∀ w ∈ (vty (.row (.fresh n))).vars, newB n w = true ∧ newB (n + 1) w = false ∧ w.isBnd = false := by
  intro w hw; rw [vars_vty, List.mem_singleton] at hw; subst hw
  simp [newB, BVar.isBnd]

theorem PostK.freshC {n0 : Nat} {C : Ctx} {st st1 : WDSt} {tys : List Ty} {Chk : RSub → Prop} {K : List ConW}
    (c : Cls) (h : PostK n0 C st st1 tys Chk K) :
    PostK n0 C st { st1 with n := st1.n + 1 } (tys ++ [.var (.fresh st1.n c)]) Chk K :=
  h.freshV (.ty (.fresh st1.n c)) (fresh_ty_ok _ _)

theorem PostK.fresh {n0 : Nat} {C : Ctx} {st st1 : WDSt} {tys : List Ty} {Chk : RSub → Prop} {K : List ConW}
    (h : PostK n0 C st st1 tys Chk K) :
    PostK n0 C st { st1 with n := st1.n + 1 } (tys ++ [.var (.fresh st1.n .any)]) Chk K := h.freshC .any

theorem PostK.freshRow {n0 : Nat} {C : Ctx} {st st1 : WDSt} {tys : List Ty} {Chk : RSub → Prop} {K : List ConW}
    (h : PostK n0 C st st1 tys Chk K) :
    PostK n0 C st { st1 with n := st1.n + 1 } (tys ++ [.record [] (some (.fresh st1.n))]) Chk K :=
  h.freshV (.row (.fresh st1.n)) (fresh_row_ok _)

/-- A `unify` step: once the two images are canonical at the step, every later substitution
    unifies the two types. -/
theorem PostK.unify {fuel n0 : Nat} {C : Ctx} {st st2 st3 : WDSt} {tys : List Ty} {Chk : RSub → Prop}
    {K : List ConW} {τ1 τ2 : Ty} {u : Unit} (h : PostK n0 C st st2 tys Chk K) (hc : Cov [τ1, τ2] tys)
    (hu : unifyWD fuel (rigidFromD n0) τ1 τ2 st2 = .ok u st3) :
    PostK n0 C st st3 tys (fun s => Chk s ∧ AbsS s (th st2) ∧ (cnB (rsb (th st2) τ1) = true →
      cnB (rsb (th st2) τ2) = true → rsb s τ1 = rsb s τ2)) K := by
  have h' := h.weaken (tys' := [τ1, τ2]) hc (fun _ _ x => x)
  have hi2 := h.seg.inv
  have m1 : τ1 ∈ [τ1, τ2] := by simp
  have m2 : τ2 ∈ [τ1, τ2] := by simp
  obtain ⟨hs, hus⟩ := seg_unify hi2 (h'.okT τ1 m1) (h'.okT τ2 m2) hu
  have hP : ∀ b, (b ∈ (rsb (th st2) τ1).vars ∨ b ∈ (rsb (th st2) τ2).vars ∨ newB st2.n b = true) →
      Reach (th st) C st.n b := by
    rintro b (hb | hb | hb)
    · exact h'.reach τ1 m1 b hb
    · exact h'.reach τ2 m2 b hb
    · exact .inl (new_of_new h.seg.le hb)
  have hav : AvoidK K (fun b => b ∈ (rsb (th st2) τ1).vars ∨ b ∈ (rsb (th st2) τ2).vars ∨ newB st2.n b = true) := by
    rintro k hk b hb (h1 | h1 | h1)
    · exact h'.tyav τ1 m1 k hk b hb h1
    · exact h'.tyav τ2 m2 k hk b hb h1
    · rw [(h.ks.zone k hk b hb).2] at h1; cases h1
  exact ⟨h.seg.trans (hs.mono hP), fun τ hτ => (h.okT τ hτ).mono hs.le,
    fun τ hτ b hb => (moves_ty' hs.mv hs.abs hi2.idem τ b hb).elim (h.reach τ hτ b) (hP b),
    h.ks.seg hs hi2 hav,
    fun τ hτ k hk b hb => avoid_seg hs.mv hs.abs hi2.idem (h.tyav τ hτ k hk b hb) (hav k hk b hb),
    fun s h1 h2 h3 => ⟨h.chk s h1 (absS_trans h2 hs.abs) h3, absS_trans h2 hs.abs, fun c1 c2 => hus c1 c2 s h2⟩⟩

theorem covSub {l l' : List Ty} (h : ∀ τ ∈ l, τ ∈ l') : Cov l l' := fun τ hτ v hv => ⟨τ, h τ hτ, hv⟩

theorem cov_refl (l : List Ty) : Cov l l := covSub fun _ h => h

/-- A call that changed nothing yet, with types built from the context and the state. -/
theorem PostK.now {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} {tys : List Ty} {Chk : RSub → Prop}
    (hp : SPre n0 L C st) (hok : ∀ τ ∈ tys, OkTD st.n τ)
    (hr : ∀ τ ∈ tys, ∀ b ∈ (rsb (th st) τ).vars, Reach (th st) C st.n b)
    (hc : ∀ s, SOk n0 s → AbsS s (th st) → Chk s) : PostK n0 C st st tys Chk [] :=
  ⟨SegD.refl hp.inv, hok, hr, KSeg.nil _ _, (fun _ _ _ h => nomatch h), fun s h1 h2 _ => hc s h1 h2⟩

theorem PostK.start {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} (hp : SPre n0 L C st) :
    PostK n0 C st st [] (fun _ => True) [] :=
  PostK.now hp (fun _ h => nomatch h) (fun _ h => nomatch h) fun _ _ _ => trivial

/-- A closed type, now. -/
theorem PostK.closed {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st : WDSt} {τ : Ty} {Chk : RSub → Prop}
    (hp : SPre n0 L C st) (hv : τ.vars = []) (hc : ∀ s, SOk n0 s → Chk s) : PostK n0 C st st [τ] Chk [] :=
  PostK.now hp (fun τ' h => by simp only [List.mem_singleton] at h; subst h; exact OkT_of_vars_nilD hv)
    (fun τ' h b hb => by
      simp only [List.mem_singleton] at h; subst h
      rw [rsb_closedD hv] at hb; simp [hv] at hb)
    fun s h1 _ => hc s h1

theorem PostK.withAbs {n0 : Nat} {C : Ctx} {st st1 : WDSt} {tys : List Ty} {Chk : RSub → Prop} {K : List ConW}
    (h : PostK n0 C st st1 tys Chk K) : PostK n0 C st st1 tys (fun s => Chk s ∧ AbsS s (th st1)) K :=
  { h with chk := fun s h1 h2 h3 => ⟨h.chk s h1 h2 h3, h2⟩ }

theorem PostK.seqSame {n0 : Nat} {L : LongId → Option Scheme} {C : Ctx} {st st1 st2 : WDSt} {tys1 tys2 : List Ty}
    {Chk1 Chk2 : RSub → Prop} {K1 K2 : List ConW} (hp : SPre n0 L C st) (h1 : PostK n0 C st st1 tys1 Chk1 K1)
    (h2 : PostK n0 C st1 st2 tys2 Chk2 K2) :
    PostK n0 C st st2 (tys1 ++ tys2) (fun s => Chk1 s ∧ Chk2 s) (K2 ++ K1) :=
  h1.seq h2 (reach_same h1.seg hp.inv) (avoid_same hp h1.ks)

end WDS

end StandardElm.Stat.Complete
