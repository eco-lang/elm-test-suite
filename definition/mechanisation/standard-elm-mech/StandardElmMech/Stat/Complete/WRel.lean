/-
  A Standard Definition of Elm? Mechanisation: the relation between W's context and the context
  of a derivation, for the main induction L11 of plan step 11 (milestone (b), section 8).

  W types a phrase in its own context `C` (schemes as W built them, not yet substituted); a
  derivation `a'` of the phrase is checked in a context `C'`. With `s` a substitution (the
  instance under construction), `C'` is *no more general* than `s C`:

  * `SchRel s σ σ'`: the free variables of `s σ` are free in `σ'` (`FtvRel`), and every instance
    of `σ'` is an instance of `s σ` (`InstUnder`: `σ`'s body with its bound variables replaced
    by anything, its free variables by their images under `s`) when `σ` binds only type
    variables of class any (W fails nothing on other schemes: it returns `unsupported`);
  * `CtxRel P R C C'`: the same type names, `U`, interfaces and type environment, related value
    environments (`VEMatch`: the same identifiers bound, with the same status, the schemes related
    by `P`), and the free variables outside the value environment rigid.

  Lemmas: free variables of a finite map (`mem_tyvarsBy`), lookups, the free variables of related
  contexts (`CtxRel.ftv`), extension (`CtxRel.plusVE`), the root context, and W's instantiation
  as the most general instance (L2: `inst_exists`).
-/
import StandardElmMech.Stat.Complete.WBasics

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## Instances under a substitution -/

/-- `g` on the bound variables of `σ`, `s` on the others. -/
def ext (σ : Scheme) (g s : FSub) : FSub := fun a => if BVar.ty a ∈ σ.bound then g a else s a

/-- `τ` is an instance of `s σ`. -/
def InstUnder (s : FSub) (σ : Scheme) (τ : Ty) : Prop := ∃ g : FSub, τ = sb (ext σ g s) σ.body

/-- The bound variables are type variables of class any (what W instantiates in F_b). -/
def AnyBound (σ : Scheme) : Prop := ∃ as : List TyVar, σ.bound = as.map BVar.ty ∧ ∀ a ∈ as, a.cls = .any

def FtvRel (s : FSub) (σ σ' : Scheme) : Prop :=
  ∀ a, BVar.ty a ∈ σ.tyvars → ∀ v ∈ (s a).tyvars, v ∈ σ'.tyvars

def SchRel (s : FSub) (σ σ' : Scheme) : Prop :=
  FtvRel s σ σ' ∧ (AnyBound σ → ∀ τ, Gen σ' τ → InstUnder s σ τ)

def OptRel (P : Scheme → Scheme → Prop) : Option (Scheme × IdStatus) → Option (Scheme × IdStatus) → Prop
  | none, none => True
  | some p, some p' => p.2 = p'.2 ∧ P p.1 p'.1
  | _, _ => False

def VEMatch (P : Scheme → Scheme → Prop) (VE VE' : ValEnv) : Prop :=
  ∀ x, OptRel P (FMap.find? VE x) (FMap.find? VE' x)

/-- The free variables of a context outside its value environment. -/
def restTv (C : Ctx) : List BVar := FMap.tyvarsBy IEnv.tyvars [] C.E.QE ++ TyEnv.tyvars C.E.TE ++ C.U

def CtxRel (P : Scheme → Scheme → Prop) (R : Rigid) (C C' : Ctx) : Prop :=
  C.T = C'.T ∧ C.U = C'.U ∧ C.E.QE = C'.E.QE ∧ C.E.TE = C'.E.TE ∧ VEMatch P C.E.VE C'.E.VE ∧
    ∀ a, BVar.ty a ∈ restTv C → R a = true

/-! ## Schemes W puts in its contexts -/

/-- Bound variables `bnd`; the free variables of the body type variables, not `bnd`, below `n`. -/
def SchW (n : Nat) (σ : Scheme) : Prop :=
  (∀ v ∈ σ.bound, v.isBnd = true) ∧
  ∀ v ∈ σ.body.vars, v ∉ σ.bound → ∃ a, v = .ty a ∧ a.isBndT = false ∧ a.isNew n = false

def CtxW (n : Nat) (C : Ctx) : Prop := ∀ lv σ st, C.lookupVal lv = some (σ, st) → SchW n σ

theorem SchW.mono {n m : Nat} (h : n ≤ m) {σ : Scheme} (hσ : SchW n σ) : SchW m σ :=
  ⟨hσ.1, fun v hv hb => by
    obtain ⟨a, e, h1, h2⟩ := hσ.2 v hv hb; exact ⟨a, e, h1, isNew_mono h h2⟩⟩

theorem CtxW.mono {n m : Nat} (h : n ≤ m) {C : Ctx} (hC : CtxW n C) : CtxW m C :=
  fun lv σ st hl => (hC lv σ st hl).mono h

theorem SchW_mono_scheme {n : Nat} {τ : Ty} (h : OkT n τ) : SchW n (mono τ) :=
  ⟨fun _ h => by simp [mono] at h, fun v hv _ => h v hv⟩

/-! ## Free variables of finite maps -/

theorem mem_tyvarsBy {K V : Type} [DecidableEq K] (f : V → List BVar) (v : BVar) :
    ∀ (l : FMap K V) (seen : List K),
      v ∈ FMap.tyvarsBy f seen l ↔ ∃ k val, k ∉ seen ∧ FMap.find? l k = some val ∧ v ∈ f val
  | [], seen => by simp [FMap.tyvarsBy]
  | (k, val) :: rest, seen => by
    simp only [FMap.tyvarsBy, List.mem_append, mem_tyvarsBy f v rest (k :: seen), FMap.find?]
    by_cases hc : (f val).isEmpty = true ∨ k ∈ seen
    · have hc' : ((f val).isEmpty || decide (k ∈ seen)) = true := by simpa using hc
      rw [if_pos hc']
      constructor
      · rintro (h | ⟨k', val', hk', hf, hv⟩)
        · cases h
        · exact ⟨k', val', fun h => hk' (.tail _ h), by
            rw [if_neg (fun e => hk' (by subst e; exact List.mem_cons_self))]; exact hf, hv⟩
      · rintro ⟨k', val', hk', hf, hv⟩
        right
        by_cases e : k = k'
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf; subst hf
          rcases hc with hc | hc
          · rw [List.isEmpty_iff] at hc; rw [hc] at hv; cases hv
          · exact absurd hc hk'
        · rw [if_neg e] at hf
          exact ⟨k', val', fun h => by
            rcases List.mem_cons.mp h with h | h
            · exact e h.symm
            · exact hk' h, hf, hv⟩
    · have hc' : ((f val).isEmpty || decide (k ∈ seen)) = false := by simpa using hc
      rw [if_neg (by simp [hc'])]
      have hks : k ∉ seen := fun h => hc (.inr h)
      constructor
      · rintro (h | ⟨k', val', hk', hf, hv⟩)
        · exact ⟨k, val, hks, by simp, h⟩
        · exact ⟨k', val', fun h => hk' (.tail _ h), by
            rw [if_neg (fun e => hk' (by subst e; exact List.mem_cons_self))]; exact hf, hv⟩
      · rintro ⟨k', val', hk', hf, hv⟩
        by_cases e : k = k'
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf; subst hf
          exact .inl hv
        · rw [if_neg e] at hf
          right
          exact ⟨k', val', fun h => by
            rcases List.mem_cons.mp h with h | h
            · exact e h.symm
            · exact hk' h, hf, hv⟩

theorem mem_VE_tyvars {v : BVar} {VE : ValEnv} :
    v ∈ ValEnv.tyvars VE ↔ ∃ x p, FMap.find? VE x = some p ∧ v ∈ p.1.tyvars := by
  unfold ValEnv.tyvars; rw [mem_tyvarsBy]; simp

theorem mem_ctx_tyvars {v : BVar} {C : Ctx} :
    v ∈ C.tyvars ↔ v ∈ restTv C ∨ ∃ x p, FMap.find? C.E.VE x = some p ∧ v ∈ p.1.tyvars := by
  simp only [Ctx.tyvars, Env.tyvars, restTv, List.mem_append, mem_VE_tyvars]
  constructor
  · rintro (((h | h) | h) | h)
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inr h
    · exact .inl (.inr h)
  · rintro ((((h | h)) | h) | h)
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inr h
    · exact .inl (.inr h)

theorem find?_mem {K V : Type} [DecidableEq K] : ∀ {l : FMap K V} {k : K} {v : V}, FMap.find? l k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (k', v') :: r, k, v, h => by
    simp only [FMap.find?] at h
    split at h
    · rename_i e; subst e; cases h; exact .head _
    · exact .tail _ (find?_mem h)

theorem find?_mapV {K V W : Type} [DecidableEq K] (g : V → W) : ∀ (l : FMap K V) (k : K),
    FMap.find? (FMap.mapV l g) k = (FMap.find? l k).map g
  | [], _ => rfl
  | (k', v) :: r, k => by
    simp only [FMap.mapV, List.map_cons, FMap.find?]
    split
    · rfl
    · exact find?_mapV g r k

theorem find?_sbVE (s : FSub) (VE : ValEnv) (x : String) :
    FMap.find? (sbVE s VE) x = (FMap.find? VE x).map fun p => (sbScheme s p.1, p.2) :=
  find?_mapV (fun q : Scheme × IdStatus => (sbScheme s q.1, q.2)) VE x

/-! ## Related contexts -/

theorem optRel_or {P : Scheme → Scheme → Prop} {a a' b b' : Option (Scheme × IdStatus)}
    (ha : OptRel P a a') (hb : OptRel P b b') : OptRel P (a.or b) (a'.or b') := by
  cases a <;> cases a' <;> simp_all [OptRel, Option.or]

theorem VEMatch.append {P : Scheme → Scheme → Prop} {A A' B B' : ValEnv} (hA : VEMatch P A A')
    (hB : VEMatch P B B') : VEMatch P (A ++ B) (A' ++ B') := fun x => by
  rw [FMap.find?_append, FMap.find?_append]; exact optRel_or (hA x) (hB x)

theorem CtxRel.plusVE {P : Scheme → Scheme → Prop} {R : Rigid} {C C' : Ctx} {VE VE' : ValEnv}
    (h : CtxRel P R C C') (hVE : VEMatch P VE VE') : CtxRel P R (C.plusVE VE) (C'.plusVE VE') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, hVE.append h5, h6⟩

theorem CtxRel.mono {P Q : Scheme → Scheme → Prop} {R : Rigid} {C C' : Ctx} (h : CtxRel P R C C')
    (hPQ : ∀ x σ st σ', FMap.find? C.E.VE x = some (σ, st) → P σ σ' → Q σ σ') : CtxRel Q R C C' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun x => ?_, h6⟩
  have := h5 x
  revert this
  cases hf : FMap.find? C.E.VE x <;> cases FMap.find? C'.E.VE x <;> simp only [OptRel, imp_self]
  rename_i p p'
  exact fun ⟨e, hp⟩ => ⟨e, hPQ x p.1 p.2 p'.1 hf hp⟩

theorem plusU_nil (C : Ctx) : C.plusU [] = C := by
  simp [Ctx.plusU, unionL, diffL]

/-- The free variables of `s C` are free in `C'`. -/
theorem CtxRel.ftv {P : Scheme → Scheme → Prop} {R : Rigid} {s : FSub} {C C' : Ctx}
    (h : CtxRel P R C C') (hP : ∀ σ σ', P σ σ' → FtvRel s σ σ') (hs : FixesR R s) :
    ∀ a, BVar.ty a ∈ C.tyvars → ∀ v ∈ (s a).tyvars, v ∈ C'.tyvars := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  intro a ha v hv
  rcases mem_ctx_tyvars.mp ha with ha | ⟨x, p, hf, hp⟩
  · rw [hs a (h6 a ha)] at hv
    simp only [Ty.tyvars, Ty.vars, List.mem_filter, List.mem_singleton] at hv
    rw [hv.1]
    exact mem_ctx_tyvars.mpr (.inl (by simpa [restTv, h2, h3, h4] using ha))
  · have := h5 x
    rw [hf] at this
    revert this
    cases hf' : FMap.find? C'.E.VE x with
    | none => simp [OptRel]
    | some p' =>
      intro ⟨_, hpp⟩
      exact mem_ctx_tyvars.mpr (.inr ⟨x, p', hf', hP _ _ hpp a hp v hv⟩)

/-! ## Lookups -/

theorem lookupVal_plusVE (C : Ctx) (VE : ValEnv) (lv : LongId) :
    (C.plusVE VE).lookupVal lv =
      match lv.qual with
      | none => (FMap.find? VE lv.id).or (FMap.find? C.E.VE lv.id)
      | some _ => C.lookupVal lv := by
  cases h : lv.qual <;> simp [Ctx.lookupVal, Env.lookupVal, Ctx.plusVE, h, FMap.find?_append]

/-- A scheme is related to itself under a substitution fixing its free variables. -/
theorem schRel_refl {s : FSub} {σ : Scheme}
    (hs : ∀ a, BVar.ty a ∈ σ.body.vars → BVar.ty a ∉ σ.bound → s a = .var a) : SchRel s σ σ := by
  refine ⟨?_, ?_⟩
  · intro a ha v hv
    have ha' : BVar.ty a ∈ σ.body.vars ∧ BVar.ty a ∉ σ.bound := by
      simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not] at ha
      exact ⟨ha.1.1, ha.2⟩
    rw [hs a ha'.1 ha'.2] at hv
    simp only [Ty.tyvars, Ty.vars, List.mem_filter, List.mem_singleton] at hv
    rw [hv.1]; exact ha
  · rintro ⟨as, hb, -⟩ τ hg
    have hσ : σ = ⟨as.map BVar.ty, σ.body⟩ := by cases σ; simp_all
    rw [hσ, gen_tyBound] at hg
    obtain ⟨ts, -, -, rfl⟩ := hg
    refine ⟨lk (as.zip ts), sb_congr _ fun a ha => ?_⟩
    simp only [ext, hb, List.mem_map, BVar.ty.injEq, exists_eq_right]
    split
    · rfl
    · rename_i hn
      rw [instance_of_fresh.lk_zip_not_mem hn, hs a ha (by rw [hb]; simpa using hn)]

/-- The lookup clause of related contexts. -/
theorem CtxRel.lookup {R : Rigid} {s : FSub} {C C' : Ctx} (h : CtxRel (SchRel s) R C C') (hs : FixesR R s)
    (hRb : ∀ i c, R (.bnd i c) = true)
    {lv : LongId} {σ' : Scheme} {st : IdStatus} (hl : C'.lookupVal lv = some (σ', st)) :
    ∃ σ, C.lookupVal lv = some (σ, st) ∧ SchRel s σ σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases hq : lv.qual with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl ⊢
    have := h5 lv.id
    rw [hl] at this
    revert this
    cases FMap.find? C.E.VE lv.id with
    | none => simp [OptRel]
    | some p => intro ⟨e, hp⟩; exact ⟨p.1, by cases p; simp_all, hp⟩
  | some m =>
    simp only [Ctx.lookupVal, Env.lookupVal, hq] at hl ⊢
    rw [h3]
    have qe_mem : ∀ (a : TyVar), a.isBndT = false → BVar.ty a ∈ σ'.body.vars → BVar.ty a ∉ σ'.bound →
        BVar.ty a ∈ restTv C := by
      intro a hab ha hb
      cases hI : FMap.find? C'.E.QE m with
      | none => rw [hI] at hl; cases hl
      | some I =>
        rw [hI] at hl
        simp only [Option.bind_some] at hl
        simp only [restTv, List.mem_append]
        left; left
        rw [mem_tyvarsBy]
        refine ⟨m, I, by simp, by rw [h3]; exact hI, ?_⟩
        simp only [IEnv.tyvars, List.mem_append]
        right
        rw [mem_VE_tyvars]
        refine ⟨lv.id, (σ', st), hl, ?_⟩
        simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
          decide_eq_false_iff_not]
        refine ⟨⟨ha, ?_⟩, hb⟩
        cases a <;> simp_all [BVar.isBnd, TyVar.isBndT]
    refine ⟨σ', hl, schRel_refl fun a ha hb => ?_⟩
    cases a with
    | bnd i c => exact hs _ (hRb i c)
    | named x => exact hs _ (h6 _ (qe_mem (TyVar.named x) rfl ha hb))
    | fresh k c => exact hs _ (h6 _ (qe_mem (TyVar.fresh k c) rfl ha hb))

end StandardElm.Stat.Complete
