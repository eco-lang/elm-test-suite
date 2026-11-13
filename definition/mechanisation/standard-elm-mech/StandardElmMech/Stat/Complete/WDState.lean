/-
  A Standard Definition of Elm? Mechanisation: W's state invariant with rows, its instantiation
  as the most general instance (L2, bound row variables included), and the root context, for
  the main induction L11 of plan step 11, milestone (d) (WState.lean for `inferExpWD`).

  `SInvD n0 st`: the counter is at least the root's `n0`, and the accumulated substitution is
  good (MguR.lean's `GoodR` with no pending equation and an empty frame: idempotent, binding only
  flexible variables, type variables to admissible types of their classes, row variables to
  records, every variable involved below the counter). That the images of W's types under it
  have no `bnd` variable is not part of the invariant: where it is needed (the closure of a
  group), it follows from the derivation (`okT_theta`).
-/
import StandardElmMech.Stat.Complete.WDRel

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

structure SInvD (n0 : Nat) (st : WDSt) : Prop where
  le : n0 ≤ st.n
  good : GoodR (rigidFromD n0) st.n st.θ [] []

theorem SInvD.fresh {n0 : Nat} {st : WDSt} (h : SInvD n0 st) : SInvD n0 { st with n := st.n + 1 } :=
  ⟨Nat.le_succ_of_le h.le, goodR_mono h.good (Nat.le_succ _)⟩

theorem SInvD.mono {n0 : Nat} {st : WDSt} (h : SInvD n0 st) {m : Nat} (hm : st.n ≤ m) :
    SInvD n0 { st with n := m } :=
  ⟨Nat.le_trans h.le hm, goodR_mono h.good hm⟩

/-- The image of a variable under the accumulated substitution: itself, or (bound, so old) a type
    whose variables are old. -/
theorem img_old {R : RRigid} {n : Nat} {θ : RBnd} (g : GoodR R n θ [] []) (v : BVar) :
    (toRS θ).img v = vty v ∨ (newB n v = false ∧ ∀ w ∈ ((toRS θ).img v).vars, newB n w = false) := by
  rw [img_toRS g.rrec]
  cases hf : FMap.find? θ v with
  | none => exact .inl rfl
  | some σ => exact .inr (g.oldθ _ (rfind?_mem hf))

/-- A substitution that agrees with `s` on the old variables fixes the rigid ones and absorbs `θ`
    when `s` does. -/
theorem agree_okD {n0 n : Nat} (h0 : n0 ≤ n) {θ : RBnd} (g : GoodR (rigidFromD n0) n θ [] []) {s T : RSub}
    (hs : FixR (rigidFromD n0) s) (ha : AbsR s θ) (hT : ∀ v, newB n v = false → T.img v = s.img v) :
    FixR (rigidFromD n0) T ∧ AbsR T θ := by
  refine ⟨fun v hr => ?_, fun v => ?_⟩
  · have : newB n v = false := by
      cases e : newB n v
      · rfl
      · rw [not_rigid_of_newD h0 e] at hr; cases hr
    rw [hT v this, hs v hr]
  · rcases img_old g v with h1 | ⟨h1, h2⟩
    · rw [h1, rsb_vty]
    · rw [hT v h1, ← ha v]
      exact rsb_congr _ fun w hw => hT w (h2 w hw)

/-- Agreement on the old variables of a type gives the same image. -/
theorem rsb_agreeD {n : Nat} {τ : Ty} (hτ : ∀ w ∈ τ.vars, newB n w = false) {s T : RSub}
    (hT : ∀ v, newB n v = false → T.img v = s.img v) : rsb T τ = rsb s τ :=
  rsb_congr τ fun w hw => hT w (hτ w hw)

/-- A type with old variables has an image (under the accumulated substitution) with old
    variables; it has no `bnd` variable when a substitution fixing the `bnd` variables and
    absorbing the accumulated one maps it to a type without. -/
theorem okT_theta {n0 : Nat} {st : WDSt} (hi : SInvD n0 st) {τ : Ty} (hok : OkTD st.n τ) {T : RSub}
    (hfx : FixR (rigidFromD n0) T) (hab : AbsR T st.θ) (hnb : ∀ v ∈ (rsb T τ).vars, v.isBnd = false) :
    OkTD st.n (rsb (toRS st.θ) τ) := by
  intro v hv
  refine ⟨?_, (img_vars hi.good hok.old v hv).2⟩
  cases hb : v.isBnd with
  | false => rfl
  | true =>
    have hfix : T.img v = vty v := hfx v (rigidFromD_bnd n0 hb)
    have : v ∈ (rsb T (rsb (toRS st.θ) τ)).vars :=
      (mem_vars_rsb T _ v).mpr ⟨v, hv, by rw [hfix, vars_vty]; exact List.mem_singleton_self _⟩
    rw [absR_rsb hab] at this
    rw [hnb v this] at hb; cases hb

/-! ## Instantiation (L2) -/

/-- The fresh variable of index `k` of the sort (and class) of `v`. -/
def instVD (k : Nat) : BVar → BVar
  | .ty a => .ty (.fresh k a.cls)
  | .row _ => .row (.fresh k)

/-- W's instance list for bound variables `vs` from counter `n`. -/
def freshFromD : Nat → List BVar → List Ty
  | _, [] => []
  | n, v :: vs => vty (instVD n v) :: freshFromD (n + 1) vs

/-- The substitution W's instantiation applies: each bound variable to its fresh variable. -/
def instS (n : Nat) (vs : List BVar) : RSub :=
  ⟨fun a => if BVar.ty a ∈ vs then .var (.fresh (n + vs.idxOf (BVar.ty a)) a.cls) else .var a,
   fun e => if BVar.row e ∈ vs then ([], some (.fresh (n + vs.idxOf (BVar.row e)))) else ([], some e)⟩

theorem instS_img (n : Nat) (vs : List BVar) (v : BVar) :
    (instS n vs).img v = if v ∈ vs then vty (instVD (n + vs.idxOf v) v) else vty v := by
  cases v with
  | ty a => by_cases h : BVar.ty a ∈ vs <;> simp [RSub.img, instS, h, vty, instVD]
  | row e => by_cases h : BVar.row e ∈ vs <;> simp [RSub.img, instS, h, vty, instVD]

theorem instVarsD_ok : ∀ (vs : List BVar) (st st' : WDSt) (ts : List Ty), instVarsD vs st = .ok ts st' →
    ts = freshFromD st.n vs ∧ st'.θ = st.θ ∧ st'.n = st.n + vs.length
  | [], st, st', ts, h => by
    simp only [instVarsD, pure, WDOut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | .ty a :: vs, st, st', ts, h => by
    simp only [instVarsD, bind, WDM.bind, freshCD] at h
    cases hv : instVarsD vs { st with n := st.n + 1 } with
    | ok ts0 st0 =>
      rw [hv] at h; simp only [pure, WDOut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := instVarsD_ok vs _ _ _ hv
      refine ⟨by rw [h1]; rfl, h2, by rw [h3]; simp; omega⟩
    | fail => rw [hv] at h; cases h
    | unsupported => rw [hv] at h; cases h
    | outOfFuel => rw [hv] at h; cases h
  | .row e :: vs, st, st', ts, h => by
    simp only [instVarsD, bind, WDM.bind, freshRowD] at h
    cases hv : instVarsD vs { st with n := st.n + 1 } with
    | ok ts0 st0 =>
      rw [hv] at h; simp only [pure, WDOut.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := instVarsD_ok vs _ _ _ hv
      refine ⟨by rw [h1]; rfl, h2, by rw [h3]; simp; omega⟩
    | fail => rw [hv] at h; cases h
    | unsupported => rw [hv] at h; cases h
    | outOfFuel => rw [hv] at h; cases h

theorem bindSubst_fresh : ∀ (vs : List BVar) (n : Nat) (S : Subst), bindSubst vs (freshFromD n vs) = some S →
    ∀ v, S.toR.img v = (instS n vs).img v
  | [], n, S, h, v => by
    simp only [freshFromD, bindSubst, Option.some.injEq] at h; subst h
    rw [instS_img]; simp only [List.not_mem_nil, if_false]
    cases v <;> rfl
  | .ty a :: vs, n, S, h, v => by
    simp only [freshFromD, instVD, vty, bindSubst] at h
    cases hb : bindSubst vs (freshFromD (n + 1) vs) with
    | none => rw [hb] at h; cases h
    | some S' =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h
      have ih := bindSubst_fresh vs (n + 1) S' hb v
      rw [instS_img] at ih ⊢
      by_cases e : v = .ty a
      · subst e; simp [RSub.img, Subst.toR, FMap.find?, vty, instVD]
      · have hS : (Subst.toR { S' with ty := (a, Ty.var (TyVar.fresh n a.cls)) :: S'.ty }).img v = S'.toR.img v := by
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
  | .row e0 :: vs, n, S, h, v => by
    simp only [freshFromD, instVD, vty, bindSubst] at h
    cases hb : bindSubst vs (freshFromD (n + 1) vs) with
    | none => rw [hb] at h; cases h
    | some S' =>
      rw [hb] at h; simp only [Option.some.injEq] at h; subst h
      have ih := bindSubst_fresh vs (n + 1) S' hb v
      rw [instS_img] at ih ⊢
      by_cases e : v = .row e0
      · subst e; simp [RSub.img, Subst.toR, FMap.find?, vty, instVD]
      · have hS : (Subst.toR { S' with row := (e0, ([], some (RowVar.fresh n))) :: S'.row }).img v = S'.toR.img v := by
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

theorem instantiateD_ok {σ : Scheme} {st st' : WDSt} {ts : List Ty} {τ : Ty}
    (h : instantiateD σ st = .ok (ts, τ) st') :
    ts = freshFromD st.n σ.bound ∧ τ = rsb (instS st.n σ.bound) σ.body ∧ st'.θ = st.θ ∧
      st'.n = st.n + σ.bound.length := by
  unfold instantiateD at h
  simp only [bind, WDM.bind] at h
  cases hv : instVarsD σ.bound st with
  | ok ts0 st0 =>
    rw [hv] at h
    dsimp only at h
    obtain ⟨hts, hθ, hn⟩ := instVarsD_ok _ _ _ _ hv
    cases hb : bindSubst σ.bound ts0 with
    | none => rw [hb] at h; cases h
    | some S =>
      rw [hb] at h
      dsimp only at h
      cases ha : S.apply σ.body with
      | none => rw [ha] at h; cases h
      | some τ0 =>
        rw [ha] at h
        simp only [pure, WDOut.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        refine ⟨hts, ?_, hθ, hn⟩
        rw [apply_eq_rsb S _ _ ha]
        rw [hts] at hb
        exact rsb_congr _ fun w _ => bindSubst_fresh _ _ _ hb w
  | fail => rw [hv] at h; cases h
  | unsupported => rw [hv] at h; cases h
  | outOfFuel => rw [hv] at h; cases h

/-- The bound variable a fresh variable of W's instantiation stands for. -/
def pickD (n : Nat) (vs : List BVar) : BVar → Option BVar
  | .ty (.fresh k c) =>
    if n ≤ k then
      match vs[k - n]? with
      | some (.ty a) => if a.cls = c then some (.ty a) else none
      | _ => none
    else none
  | .row (.fresh k) =>
    if n ≤ k then
      match vs[k - n]? with
      | some (.row e) => some (.row e)
      | _ => none
    else none
  | _ => none

theorem pickD_old {n : Nat} {vs : List BVar} {w : BVar} (h : newB n w = false) : pickD n vs w = none := by
  match w, h with
  | .ty (.fresh k c), h =>
    simp only [newB, TyVar.isNew, decide_eq_false_iff_not] at h; simp only [pickD]; rw [if_neg h]
  | .row (.fresh k), h =>
    simp only [newB, decide_eq_false_iff_not] at h; simp only [pickD]; rw [if_neg h]
  | .ty (.named _), _ | .ty (.bnd _ _), _ | .row (.named _), _ | .row (.bnd _), _ => rfl

theorem pickD_new {n : Nat} {vs : List BVar} {w : BVar} (h : newB (n + vs.length) w = true) : pickD n vs w = none := by
  match w, h with
  | .ty (.fresh k c), h =>
    simp only [newB, TyVar.isNew, decide_eq_true_eq] at h; simp only [pickD]
    rw [if_pos (by omega), List.getElem?_eq_none (by omega)]
  | .row (.fresh k), h =>
    simp only [newB, decide_eq_true_eq] at h; simp only [pickD]
    rw [if_pos (by omega), List.getElem?_eq_none (by omega)]
  | .ty (.named _), _ | .ty (.bnd _ _), _ | .row (.named _), _ | .row (.bnd _), _ => rfl

theorem pickD_inst {n : Nat} {vs : List BVar} {v : BVar} (h : v ∈ vs) :
    pickD n vs (instVD (n + vs.idxOf v) v) = some v := by
  have hl := List.idxOf_lt_length_of_mem h
  have hg : vs[vs.idxOf v]? = some v := by
    rw [List.getElem?_eq_getElem hl, List.getElem_idxOf]
  cases v with
  | ty a => simp [pickD, instVD, hg]
  | row e => simp [pickD, instVD, hg]

theorem pickD_mem {n : Nat} {vs : List BVar} {w v : BVar} (h : pickD n vs w = some v) :
    v ∈ vs ∧ (∀ a, v = .ty a → ∃ k, w = .ty (.fresh k a.cls)) ∧ (∀ e, v = .row e → ∃ k, w = .row (.fresh k)) := by
  match w, h with
  | .ty (.fresh k c), h =>
    simp only [pickD] at h
    split at h
    · split at h
      · rename_i a hg
        split at h
        · rename_i hc; cases h
          exact ⟨List.mem_of_getElem? hg, fun b hb => by cases hb; exact ⟨k, by rw [hc]⟩, fun e he => by cases he⟩
        · cases h
      · cases h
    · cases h
  | .row (.fresh k), h =>
    simp only [pickD] at h
    split at h
    · split at h
      · rename_i e hg; cases h
        exact ⟨List.mem_of_getElem? hg, fun b hb => (nomatch hb), fun e' _ => ⟨k, rfl⟩⟩
      · cases h
    · cases h
  | .ty (.named _), h | .ty (.bnd _ _), h | .row (.named _), h | .row (.bnd _), h =>
    simp only [pickD, reduceCtorEq] at h

/-- A substitution given by its images (row variables to records). -/
def ofImg (f : BVar → Ty) : RSub := ⟨fun a => f (.ty a), fun e => rowOf (f (.row e))⟩

theorem ofImg_img {f : BVar → Ty} (hf : ∀ e, ∃ ρ tl, f (.row e) = .record ρ tl) (v : BVar) : (ofImg f).img v = f v := by
  cases v with
  | ty a => rfl
  | row e => obtain ⟨ρ, tl, h⟩ := hf e; simp [RSub.img, ofImg, h, rowOf]

theorem img_row_record (s : RSub) (e : RowVar) : ∃ ρ tl, s.img (.row e) = .record ρ tl := ⟨_, _, rfl⟩

/-- W's instance of a scheme is most general: every instance of `s σ` is an image of it, by a
    substitution agreeing with `s` outside W's new variables, and mapping each of them to an
    admissible type of its class. -/
theorem inst_existsD {n : Nat} {σ : Scheme} {s : RSub} {τ' : Ty} (hσ : SchWD n σ) (hi : InstUnderD s σ τ') :
    ∃ T : RSub, (∀ v, newB n v = false → T.img v = s.img v) ∧
      (∀ v, newB (n + σ.bound.length) v = true → T.img v = s.img v) ∧
      (∀ a, T.t a ≠ s.t a → Adm a.cls (T.t a)) ∧
      rsb T (rsb (instS n σ.bound) σ.body) = τ' := by
  obtain ⟨g, hg, rfl⟩ := hi
  let f : BVar → Ty := fun w => match pickD n σ.bound w with
    | some v => g.img v
    | none => s.img w
  have hf : ∀ e, ∃ ρ tl, f (.row e) = .record ρ tl := fun e => by
    simp only [f]; split
    · rename_i v hv
      obtain ⟨-, hk, -⟩ := pickD_mem hv
      cases v with
      | row e' => exact img_row_record g e'
      | ty a => obtain ⟨k, hk⟩ := hk a rfl; cases hk
    · exact img_row_record s e
  have hT : ∀ w, (ofImg f).img w = f w := ofImg_img hf
  refine ⟨ofImg f, fun v hv => ?_, fun v hv => ?_, fun a ha => ?_, ?_⟩
  · rw [hT]; simp only [f, pickD_old hv]
  · rw [hT]; simp only [f, pickD_new hv]
  · have e1 : (ofImg f).t a = f (.ty a) := rfl
    rw [e1] at ha ⊢
    simp only [f] at ha ⊢
    split at ha
    · rename_i v hv
      obtain ⟨hm, hk, hk'⟩ := pickD_mem hv
      cases v with
      | ty b =>
        obtain ⟨k, hk⟩ := hk b rfl
        injection hk with hk; subst hk
        exact hg b hm
      | row e => obtain ⟨k, hk⟩ := hk' e rfl; cases hk
    · exact absurd rfl ha
  · rw [rsb_rsb]
    apply rsb_congr
    intro w hw
    rw [img_rcomp, instS_img, extS_img]
    split
    · rename_i hm
      rw [rsb_vty, hT]; simp only [f, pickD_inst hm]
    · rename_i hm
      rw [rsb_vty, hT]
      simp only [f, pickD_old (hσ.2 w hw hm).2]

/-- W's instance is a type W builds. -/
theorem inst_okTD {n : Nat} {σ : Scheme} (hσ : SchWD n σ) :
    OkTD (n + σ.bound.length) (rsb (instS n σ.bound) σ.body) := by
  refine OkT_rsbD fun w hw => ?_
  rw [instS_img]
  split
  · rename_i hm
    have hl := List.idxOf_lt_length_of_mem hm
    cases w with
    | ty a => exact OkT_vtyD rfl (by simp [newB, instVD, TyVar.isNew]; omega)
    | row e => exact OkT_vtyD rfl (by simp [newB, instVD]; omega)
  · rename_i hm
    exact OkT_vtyD (hσ.2 w hw hm).1 (newB_mono (Nat.le_add_right _ _) (hσ.2 w hw hm).2)

theorem freshFromD_okT : ∀ (vs : List BVar) (m : Nat), ∀ t ∈ freshFromD m vs, OkTD (m + vs.length) t
  | [], _, _, h => by cases h
  | v :: vs, m, t, h => by
    simp only [freshFromD, List.mem_cons] at h
    rcases h with rfl | h
    · cases v with
      | ty a => exact OkT_vtyD rfl (by simp [newB, instVD, TyVar.isNew])
      | row e => exact OkT_vtyD rfl (by simp [newB, instVD])
    · have := freshFromD_okT vs (m + 1) t h
      rw [show m + (v :: vs).length = m + 1 + vs.length by simp; omega]; exact this

/-! ## The root context -/

theorem freshAboveD_aux : ∀ (l : List BVar) (m : Nat),
    m ≤ l.foldl (fun m v => match v with
      | .ty (.fresh k _) => max m (k + 1)
      | .row (.fresh k) => max m (k + 1)
      | _ => m) m ∧
    ∀ v ∈ l, newB (l.foldl (fun m v => match v with
      | .ty (.fresh k _) => max m (k + 1)
      | .row (.fresh k) => max m (k + 1)
      | _ => m) m) v = false
  | [], m => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | v :: l, m => by
    simp only [List.foldl_cons]
    have ih := freshAboveD_aux l
    constructor
    · refine Nat.le_trans ?_ (ih _).1
      split <;> omega
    · intro w hw
      rcases List.mem_cons.mp hw with e | hw
      · subst e
        have hle := (ih (match w with
          | .ty (.fresh k _) => max m (k + 1)
          | .row (.fresh k) => max m (k + 1)
          | _ => m)).1
        rcases w with ((_ | ⟨k, c⟩ | _) | (_ | k | _)) <;> simp only [newB, TyVar.isNew, decide_eq_false_iff_not] at hle ⊢ <;> omega
      · exact (ih _).2 w hw

theorem old_of_rootD {C0 : Ctx} {v : BVar} (h : v ∈ C0.tyvars) : newB (freshAboveD C0) v = false :=
  (freshAboveD_aux (C0.tyvars ++ veAllVars C0.E.VE) 0).2 v (List.mem_append_left _ h)

/-- A variable of a binding of the root context, shadowed or not, is not W's. -/
theorem old_of_root_veD {C0 : Ctx} {v : BVar} {p : String × (Scheme × IdStatus)} (hp : p ∈ C0.E.VE)
    (h : v ∈ p.2.1.body.vars) : newB (freshAboveD C0) v = false :=
  (freshAboveD_aux (C0.tyvars ++ veAllVars C0.E.VE) 0).2 v
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, h⟩))

theorem bnd_old {n : Nat} {v : BVar} (h : v.isBnd = true) : newB n v = false := by
  rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isBnd, newB, TyVar.isNew]

/-- The root context is related to itself under a substitution fixing the rigid variables. -/
theorem root_relD {C0 : Ctx} {s : RSub} (hs : FixR (rigidFromD (freshAboveD C0)) s) :
    CtxRelD (SchRelD s) (rigidFromD (freshAboveD C0)) C0 C0 := by
  refine ⟨rfl, rfl, rfl, rfl, fun x => ?_, fun v hv => rigid_of_oldD (old_of_rootD (mem_ctx_tyvars.mpr (.inl hv)))⟩
  cases hf : FMap.find? C0.E.VE x with
  | none => trivial
  | some p =>
    refine ⟨rfl, schRel_reflD fun w hw hb => ?_⟩
    apply hs
    cases hwb : w.isBnd with
    | true => exact rigidFromD_bnd _ hwb
    | false =>
      apply rigid_of_oldD
      apply old_of_rootD
      refine mem_ctx_tyvars.mpr (.inr ⟨x, p, hf, ?_⟩)
      simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not]
      exact ⟨⟨hw, hwb⟩, hb⟩

/-- The schemes of the root context are schemes W can put in its contexts. -/
theorem root_ctxWD {C0 : Ctx} (hC : RootOKD C0) : CtxWD (freshAboveD C0) C0 := by
  intro lv σ st hl
  obtain ⟨h1, h2⟩ := hC lv σ st hl
  refine ⟨h1, fun v hv hb => ⟨h2 v hv hb, old_of_rootD ?_⟩⟩
  have hfree : v ∈ σ.tyvars := by
    simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨⟨hv, h2 v hv hb⟩, hb⟩
  cases hq : lv.qual with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl
    exact mem_ctx_tyvars.mpr (.inr ⟨lv.id, (σ, st), hl, hfree⟩)
  | some m =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl
    cases hI : FMap.find? C0.E.QE m with
    | none => rw [hI] at hl; cases hl
    | some I =>
      rw [hI] at hl
      simp only [Option.bind_some] at hl
      refine mem_ctx_tyvars.mpr (.inl ?_)
      simp only [restTv, List.mem_append]
      left; left
      rw [mem_tyvarsBy]
      refine ⟨m, I, by simp, hI, ?_⟩
      simp only [IEnv.tyvars, List.mem_append]
      right
      exact mem_VE_tyvars.mpr ⟨lv.id, (σ, st), hl, hfree⟩

end StandardElm.Stat.Complete
