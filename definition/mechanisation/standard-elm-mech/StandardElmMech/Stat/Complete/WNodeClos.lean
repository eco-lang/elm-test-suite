/-
  A Standard Definition of Elm? Mechanisation: the closure clause of the node correspondence
  (plan step 11, milestone (b), section 9 and L3): at a declaration node, every instance of the
  derivation's closed scheme is an instance of `T` applied to W's closed scheme, in step 9's
  terms (`Gen`, with the classes respected), for the result of W (its closures generalise type
  variables of class any, or rigid variables `T` fixes).
-/
import StandardElmMech.Stat.Complete.WTheorems

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

theorem adm_self (a : TyVar) : Adm a.cls (.var a) := by
  cases h : a.cls with
  | any => exact .any _
  | num => exact .num_var a h
  | comp => exact .comp_var a (by simp [h, Cls.le])
  | app => exact .app_var a (by simp [h, Cls.le])
  | capp => exact .capp_var a h

theorem apply_var_adm {S : Subst} (hS : S.Respects) {b : TyVar} {t : Ty} (h : S.apply (.var b) = some t) :
    Adm b.cls t := by
  simp only [Subst.apply, Option.some.injEq] at h
  cases hf : FMap.find? S.ty b with
  | none => rw [hf] at h; subst h; exact adm_self b
  | some u => rw [hf] at h; subst h; exact hS _ (find?_mem hf)

theorem renumber_ty_vals : ∀ (i : Nat) (vs : List BVar), ∀ p ∈ (renumber true i vs).1.ty,
    ∃ j, p.2 = .var (.bnd j p.1.cls)
  | _, [], p, h => by simp [renumber, Subst.id] at h
  | i, .ty a :: vs, p, h => by
    simp only [renumber, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨i, by simp⟩
    · exact renumber_ty_vals (i + 1) vs p h
  | i, .row e :: vs, p, h => by
    simp only [renumber] at h
    exact renumber_ty_vals (i + 1) vs p h

theorem renumber_var (i : Nat) (vs : List BVar) (a : TyVar) :
    ∃ b, (renumber true i vs).1.apply (.var a) = some (.var b) ∧ b.cls = a.cls := by
  simp only [Subst.apply]
  cases hf : FMap.find? (renumber true i vs).1.ty a with
  | none => exact ⟨a, rfl, rfl⟩
  | some u =>
    obtain ⟨j, hj⟩ := renumber_ty_vals i vs _ (find?_mem hf)
    simp only at hj; subst hj
    exact ⟨_, rfl, rfl⟩

def rnB : Nat → List TyVar → List TyVar
  | _, [] => []
  | i, a :: as => .bnd i a.cls :: rnB (i + 1) as

theorem rnBs_eq : ∀ (i : Nat) (as : List TyVar), rnBs i as = (rnB i as).map BVar.ty
  | _, [] => rfl
  | i, a :: as => by simp [rnBs, rnB, rnBs_eq (i + 1) as]

theorem rnB_length : ∀ (i : Nat) (as : List TyVar), (rnB i as).length = as.length
  | _, [] => rfl
  | i, a :: as => by simp [rnB, rnB_length (i + 1) as]

theorem mem_rnB_zip {f : TyVar → Ty} : ∀ (i : Nat) (as : List TyVar), ∀ p ∈ (rnB i as).zip (as.map f),
    ∃ a ∈ as, p.1.cls = a.cls ∧ p.2 = f a
  | _, [], p, h => by simp [rnB] at h
  | i, a :: as, p, h => by
    simp only [rnB, List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, .head _, rfl, rfl⟩
    · obtain ⟨b, hb, h1, h2⟩ := mem_rnB_zip (i + 1) as p h
      exact ⟨b, .tail _ hb, h1, h2⟩

theorem lk_rnB_zip {f : TyVar → Ty} : ∀ (i : Nat) (as : List TyVar) (c : TyVar), c ∈ as →
    lk ((rnB i as).zip (as.map f)) (.bnd (i + as.idxOf c) c.cls) = f c
  | _, [], _, h => by cases h
  | i, b :: bs, c, h => by
    simp only [rnB, List.map_cons, List.zip_cons_cons, lk_cons]
    by_cases e : b = c
    · subst e; simp
    · rw [List.idxOf_cons, if_neg (show ¬ ((b == c) = true) by simpa using e)]
      have hm : c ∈ bs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      rw [if_neg (show ¬ (TyVar.bnd i b.cls = TyVar.bnd (i + (List.idxOf c bs + 1)) c.cls) by
        intro h; simp only [TyVar.bnd.injEq] at h; omega)]
      have := lk_rnB_zip (f := f) (i + 1) bs c hm
      rw [show i + (List.idxOf c bs + 1) = i + 1 + List.idxOf c bs by omega]; exact this

theorem lk_rnB_zip_nb {ts : List Ty} : ∀ (i : Nat) (as : List TyVar) (v : TyVar), v.isBndT = false →
    lk ((rnB i as).zip ts) v = .var v
  | _, [], _, _ => by simp [rnB, lk_nil]
  | i, a :: as, v, hv => by
    cases ts with
    | nil => simp [rnB, lk_nil]
    | cons t ts =>
      simp only [rnB, List.zip_cons_cons, lk_cons]
      rw [if_neg (by rintro rfl; simp [TyVar.isBndT] at hv)]
      exact lk_rnB_zip_nb (i + 1) as v hv

/-- The closure clause at a declaration node (section 9 with L3): for `T` that fixes the `bnd`
    variables and moves only variables of class any. -/
theorem closE_inst {A A' : List BVar} {VE VE' : ValEnv} {τ : Ty} {T : FSub} {n : Nat}
    (hτ : OkT n τ)
    (hA : ∀ a, BVar.ty a ∈ A → BVar.ty a ∈ τ.vars → ∀ v ∈ (T a).tyvars, v ∈ A')
    (hNB : ∀ v ∈ (sb T τ).vars, v.isBnd = false)
    (hbnd : ∀ i c, T (.bnd i c) = .var (.bnd i c)) (hcls : ∀ a, T a ≠ .var a → a.cls = .any) :
    ∀ t, Gen (closE A' VE' (mono (sb T τ))) t →
      Gen ⟨(closE A VE (mono τ)).bound, sb T (closE A VE (mono τ)).body⟩ t := by
  have hto : TyOnly τ := TyOnly.of_okT hτ
  obtain ⟨as, hcv, hc⟩ := canon_ty (body := τ) (closE_bound_ty (A := A) (VE := VE) hto)
  have inA : ∀ c, BVar.ty c ∈ τ.vars → c ∉ as → BVar.ty c ∈ A := by
    intro c hc hn
    have hnb : BVar.ty c ∉ List.map BVar.ty as := by simpa using hn
    rw [← hcv, mem_canonVars_iff hc] at hnb
    obtain ⟨c', e, hb, -⟩ := hτ _ hc
    injection e with e; subst e
    refine Classical.byContradiction fun hA' => ?_
    apply hnb
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL,
      mem_tyvars_iff, decide_eq_false_iff_not, Bool.not_eq_true']
    refine .inl ⟨⟨hc, ?_⟩, hA'⟩
    cases c <;> simp_all [BVar.isBnd, TyVar.isBndT]
  have hfix : ∀ c, BVar.ty c ∈ τ.vars → BVar.ty c ∈ A → ∀ v ∈ (T c).vars,
      v ∉ closB A' VE' (mono (sb T τ)) ∧ v.isBnd = false := by
    intro c hc hcA v hv
    have hnb : v.isBnd = false := hNB v (vars_sb_of T τ c v hc hv)
    have hA'v : v ∈ A' := hA c hcA hc v (mem_tyvars_iff.mpr ⟨hv, hnb⟩)
    refine ⟨?_, hnb⟩
    simp only [closB, mono_tyvars, mono_bound, List.nil_append, List.mem_append, diffL, List.mem_filter, mem_dedupL,
      decide_eq_false_iff_not, Bool.not_eq_true', not_or, not_and, List.mem_append]
    exact ⟨fun _ h => h hA'v, fun h => absurd hA'v h.2.2⟩
  intro t hg
  unfold closE at hg
  simp only [Scheme.canon, mono_body] at hg
  obtain ⟨h1, h2, h3⟩ := renumber_spec true 0 (canonVars (closB A' VE' (mono (sb T τ))) (sb T τ))
  have hrv := renumber_var 0 (canonVars (closB A' VE' (mono (sb T τ))) (sb T τ))
  generalize renumber true 0 (canonVars (closB A' VE' (mono (sb T τ))) (sb T τ)) = RN at hg h1 h2 h3 hrv
  obtain ⟨β, hβ⟩ := apply_isSome h1 (sb T τ)
  obtain ⟨ts, S2, hS2, hres, ht⟩ := hg
  rw [hβ, Option.getD_some] at ht
  obtain ⟨k1, k2⟩ := apply_sb _ T τ β hto hβ
  subst k2
  obtain ⟨k3, k4⟩ := apply_sb _ _ τ t hto ht
  subst k4
  have hpost : ∀ c, BVar.ty c ∈ τ.vars → BVar.ty c ∈ A → post S2 (post RN.1 T) c = T c := by
    intro c hc hcA
    have e1 : RN.1.apply (T c) = some (T c) := apply_fix _ _ fun v hv hd =>
      (hfix c hc hcA v hv).1 (mem_canonVars (h2 v hd))
    have e2 : S2.apply (T c) = some (T c) := apply_fix _ _ fun v hv hd => by
      have := h3 v (bindSubst_dom hS2 v hd)
      rw [(hfix c hc hcA v hv).2] at this; cases this
    simp only [post, e1, Option.getD_some, e2]
  -- the classes are respected
  have hadm : ∀ c, BVar.ty c ∈ τ.vars → Adm c.cls (post S2 (post RN.1 T) c) := by
    intro c hc
    by_cases hTc : T c = .var c
    · obtain ⟨b, hb, hbc⟩ := hrv c
      have e1 : post RN.1 T c = .var b := by simp [post, hTc, hb]
      have e2 := k3 c hc
      rw [e1] at e2
      rw [← hbc]; exact apply_var_adm hres e2
    · rw [hcls c hTc]; exact .any _
  let h := post S2 (post RN.1 T)
  unfold closE
  rw [mono_body, hc, rnBs_eq]
  rw [gen_tyBound]
  refine ⟨as.map (fun a => if BVar.ty a ∈ τ.vars then h a else .var a), by simp [rnB_length], ?_, ?_⟩
  · intro p hp
    obtain ⟨a, -, h1, h2⟩ := mem_rnB_zip 0 as p hp
    rw [h1, h2]
    split
    · rename_i ha; exact hadm a ha
    · exact adm_self a
  · rw [sb_sb, sb_sb]
    apply sb_congr
    intro c hcv
    simp only [comp]
    rw [lk_rnTy]
    split
    · rename_i hm
      have := lk_rnB_zip (f := fun a => if BVar.ty a ∈ τ.vars then h a else .var a) 0 as c hm
      show _ = sb _ (T _)
      rw [hbnd]; simp only [sb]; rw [this, if_pos hcv]
    · rename_i hm
      show _ = sb _ (T c)
      rw [sb_eq_self_iff.mpr fun v hv => lk_rnB_zip_nb 0 as v (by
        have := hNB _ (vars_sb_of T τ c _ hcv hv)
        cases v <;> simp_all [BVar.isBnd, TyVar.isBndT])]
      exact hpost c hcv (inA c hcv hm)

end StandardElm.Stat.Complete
