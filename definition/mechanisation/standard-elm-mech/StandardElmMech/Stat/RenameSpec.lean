/-
  A Standard Definition of Elm? Mechanisation: specialisation is invariant under renamings, plan
  step 10 (Theorems, "The variables of a group and the invariance lemma", the mutual statement
  under `reduceProgram_rename`, with `reduceProgram_equiv` folded in).

  `RAtExp r D a a'` (and its companions for the other annotated phrases) says that `a'` is the
  image of `a` under the renaming `r` in everything specialisation reads: the types of constants,
  the instances at occurrences of variables, the value environments of declarations and of
  patterns, the types of bindings; the U' of an annotation only on the variables `D` (those of the
  derivation's types), and nothing of the types specialisation does not read (the instances of
  constructors and operators, the types of occurrences, the types inside patterns). Under it,
  every function of the mutual specialisation gives the same result, from renamed assignments of
  the enclosing copies, a related scope and a related context (`specExp_rename` and its
  companions).

  The references to the groups of other modules are renamed by those modules' renamings; they
  bind every variable of their declaration (`Member.bOutAll`), so the enclosing copies' assignment,
  which is renamed by this module's renaming, is never read for them.
-/
import StandardElmMech.Stat.RenameObjects

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## The relation -/

def AnnRel (r : Renaming) (D : BVar → Prop) : Option (Src.BTy × List BVar) → Option (Src.BTy × List BVar) → Prop
  | none, none => True
  | some (_, U), some (_, U') => ∀ v, D v → (v ∈ U ↔ r.bvar v ∈ U')
  | _, _ => False

mutual
inductive RAtExp (r : Renaming) (D : BVar → Prop) : AAtExp → AAtExp → Prop
  | scon (sc : Src.SLit) (τ : Ty) : RAtExp r D (.scon sc τ) (.scon sc (r.ty τ))
  | var (lv : LongId) (inst : List Ty) (τ τ' : Ty) : RAtExp r D (.var lv inst τ) (.var lv (r.tys inst) τ')
  | con (lc : LongId) (inst : List Ty) (τ : Ty) (inst' : List Ty) (τ' : Ty) :
      RAtExp r D (.con lc inst τ) (.con lc inst' τ')
  | op (o : Op) (inst : List Ty) (τ : Ty) (inst' : List Ty) (τ' : Ty) : RAtExp r D (.op o inst τ) (.op o inst' τ')
  | unit : RAtExp r D .unit .unit
  | tuple {e1 e2 : AExp} {e3 : Option AExp} {e1' e2' : AExp} {e3' : Option AExp} :
      RExp r D e1 e1' → RExp r D e2 e2' → RExpOpt r D e3 e3' → RAtExp r D (.tuple e1 e2 e3) (.tuple e1' e2' e3')
  | nil (τ τ' : Ty) : RAtExp r D (.nil τ) (.nil τ')
  | record {row row' : Option AExpRow} : RExpRowOpt r D row row' → RAtExp r D (.record row) (.record row')
  | update {x : Var} {inst : List Ty} {τ τ' : Ty} {row row' : AExpRow} :
      RExpRow r D row row' → RAtExp r D (.update x inst τ row) (.update x (r.tys inst) τ' row')
  | letE {VE : ValEnv} {vb vb' : AValBind} {e e' : AExp} :
      (∀ p ∈ VE, ∀ v ∈ p.2.1.tyvars, D v) → RValBind r D vb vb' → RExp r D e e' →
      RAtExp r D (.letE (.val VE vb) e) (.letE (.val (r.valEnv VE) vb') e')
  | paren {e e' : AExp} : RExp r D e e' → RAtExp r D (.paren e) (.paren e')
inductive RExpRow (r : Renaming) (D : BVar → Prop) : AExpRow → AExpRow → Prop
  | field {l : Lab} {e e' : AExp} {rest rest' : Option AExpRow} :
      RExp r D e e' → RExpRowOpt r D rest rest' → RExpRow r D (.field l e rest) (.field l e' rest')
inductive RExpRowOpt (r : Renaming) (D : BVar → Prop) : Option AExpRow → Option AExpRow → Prop
  | none : RExpRowOpt r D none none
  | some {row row' : AExpRow} : RExpRow r D row row' → RExpRowOpt r D (some row) (some row')
inductive RExp (r : Renaming) (D : BVar → Prop) : AExp → AExp → Prop
  | atexp {a a' : AAtExp} : RAtExp r D a a' → RExp r D (.atexp a) (.atexp a')
  | app {e e' : AExp} {a a' : AAtExp} : RExp r D e e' → RAtExp r D a a' → RExp r D (.app e a) (.app e' a')
  | lam {p p' : AAtPat} {e e' : AExp} : p'.erase = p.erase → p'.ve = r.valEnv p.ve → RExp r D e e' →
      RExp r D (.lam p e) (.lam p' e')
  | caseE {e e' : AExp} {m m' : AMatch} : RExp r D e e' → RMatch r D m m' → RExp r D (.caseE e m) (.caseE e' m')
inductive RExpOpt (r : Renaming) (D : BVar → Prop) : Option AExp → Option AExp → Prop
  | none : RExpOpt r D none none
  | some {e e' : AExp} : RExp r D e e' → RExpOpt r D (some e) (some e')
inductive RMatch (r : Renaming) (D : BVar → Prop) : AMatch → AMatch → Prop
  | mk {mr mr' : AMRule} {rest rest' : Option AMatch} :
      RMRule r D mr mr' → RMatchOpt r D rest rest' → RMatch r D (.mk mr rest) (.mk mr' rest')
inductive RMatchOpt (r : Renaming) (D : BVar → Prop) : Option AMatch → Option AMatch → Prop
  | none : RMatchOpt r D none none
  | some {m m' : AMatch} : RMatch r D m m' → RMatchOpt r D (some m) (some m')
inductive RMRule (r : Renaming) (D : BVar → Prop) : AMRule → AMRule → Prop
  | mk {p p' : APat} {e e' : AExp} : p'.erase = p.erase → p'.ve = r.valEnv p.ve → RExp r D e e' →
      RMRule r D (.mk p e) (.mk p' e')
inductive RValBind (r : Renaming) (D : BVar → Prop) : AValBind → AValBind → Prop
  | var {x : Var} {ann ann' : Option (Src.BTy × List BVar)} {τ : Ty} {e e' : AExp} {rest rest' : Option AValBind} :
      AnnRel r D ann ann' → (∀ v ∈ τ.vars, D v) → RExp r D e e' → RValBindOpt r D rest rest' →
      RValBind r D (.var x ann τ e rest) (.var x ann' (r.ty τ) e' rest')
  | pat {p p' : AAtPat} {e e' : AExp} : p'.erase = p.erase → p'.ve = r.valEnv p.ve →
      (∀ q ∈ p.ve, ∀ v ∈ q.2.1.body.vars, D v) → RExp r D e e' → RValBind r D (.pat p e) (.pat p' e')
inductive RValBindOpt (r : Renaming) (D : BVar → Prop) : Option AValBind → Option AValBind → Prop
  | none : RValBindOpt r D none none
  | some {vb vb' : AValBind} : RValBind r D vb vb' → RValBindOpt r D (some vb) (some vb')
end

/-! ## Scopes and contexts -/

def Renaming.ref (r : Renaming) : Ref → Ref
  | .plain => .plain
  | .group gid V body bv => .group gid (V.map r.tvApply) (r.ty body) (bv.map r.bvar)
  | .basis V body bv => .basis (V.map r.tvApply) (r.ty body) (bv.map r.bvar)

/-- Every variable of the declaration is bound at an occurrence: the reference does not read the
    enclosing copies. -/
def Ref.Closed : Ref → Prop
  | .plain => True
  | .group _ V _ bv => ∀ v ∈ V, BVar.ty v ∈ bv
  | .basis V _ bv => ∀ v ∈ V, BVar.ty v ∈ bv

def Renaming.binds (r : Renaming) (l : List (Var × Ref)) : List (Var × Ref) := l.map fun p => (p.1, r.ref p.2)

/-- The references of other modules: renamed by their own renamings, and closed. -/
def GlobRel : List ((ModId × Var) × Ref) → List ((ModId × Var) × Ref) → Prop
  | [], [] => True
  | e :: es, e' :: es' => e'.1 = e.1 ∧ (∃ r' : Renaming, r'.WF ∧ e'.2 = r'.ref e.2 ∧ e.2.Closed) ∧ GlobRel es es'
  | _, _ => False

structure ScopeRel (r : Renaming) (Γ Γ' : Scope) : Prop where
  locals : Γ'.locals = r.binds Γ.locals
  top : Γ'.top = r.binds Γ.top
  global : GlobRel Γ.global Γ'.global
  prov : Γ'.prov = Γ.prov

structure CtxRel (r : Renaming) (D : BVar → Prop) (L L' : Ctx) : Prop where
  ve : L'.E.VE = r.valEnv L.E.VE
  qe : L.E.QE = []
  qe' : L'.E.QE = []
  te : L.E.TE = []
  te' : L'.E.TE = []
  u : ∀ v, D v → (v ∈ L.U ↔ r.bvar v ∈ L'.U)

theorem CtxRel.tyvars {r : Renaming} (hr : r.WF) {D : BVar → Prop} {L L' : Ctx} (h : CtxRel r D L L') :
    ∀ v, D v → (v ∈ L.tyvars ↔ r.bvar v ∈ L'.tyvars) := by
  intro v hv
  simp only [Ctx.tyvars, Env.tyvars, h.qe, h.qe', h.te, h.te', h.ve, FMap.tyvarsBy, TyEnv.tyvars,
    List.nil_append, List.mem_append, valEnv_tyvars_rename hr, mem_map_inj hr.bvar_inj, h.u v hv]

theorem CtxRel.plusVE {r : Renaming} {D : BVar → Prop} {L L' : Ctx} (h : CtxRel r D L L') (VE : ValEnv) :
    CtxRel r D (L.plusVE VE) (L'.plusVE (r.valEnv VE)) :=
  ⟨by simp only [Ctx.plusVE, h.ve, Renaming.valEnv_append], h.qe, h.qe', h.te, h.te', h.u⟩

theorem mem_unionL {α : Type} [DecidableEq α] {x : α} {A B : List α} : x ∈ unionL A B ↔ x ∈ A ∨ x ∈ B := by
  simp only [unionL, List.mem_append, mem_diffL]
  by_cases h : x ∈ A <;> simp [h]

theorem CtxRel.plusU {r : Renaming} {D : BVar → Prop} {L L' : Ctx} (h : CtxRel r D L L') {U U' : List BVar}
    (hU : ∀ v, D v → (v ∈ U ↔ r.bvar v ∈ U')) : CtxRel r D (L.plusU U) (L'.plusU U') :=
  ⟨h.ve, h.qe, h.qe', h.te, h.te', fun v hv => by
    simp only [Ctx.plusU, mem_unionL, h.u v hv, hU v hv]⟩

theorem lookup_binds (r : Renaming) (x : Var) : ∀ l : List (Var × Ref),
    (r.binds l).lookup x = (l.lookup x).map r.ref
  | [] => rfl
  | (y, ref) :: rest => by
    simp only [Renaming.binds, List.map_cons, List.lookup]
    by_cases h : x = y
    · subst h; simp
    · have : (x == y) = false := beq_eq_false_iff_ne.mpr h
      simp only [this]; exact lookup_binds r x rest

theorem Renaming.binds_append (r : Renaming) (l l' : List (Var × Ref)) :
    r.binds (l ++ l') = r.binds l ++ r.binds l' := List.map_append ..

theorem ScopeRel.push {r : Renaming} {Γ Γ' : Scope} (h : ScopeRel r Γ Γ') (rs : List (Var × Ref)) :
    ScopeRel r (Γ.push rs) (Γ'.push (r.binds rs)) :=
  ⟨by simp only [Scope.push, h.locals, Renaming.binds_append], h.top, h.global, h.prov⟩

theorem ScopeRel.pushPlain {r : Renaming} {Γ Γ' : Scope} (h : ScopeRel r Γ Γ') (VE : ValEnv) :
    ScopeRel r (Γ.pushPlain VE) (Γ'.pushPlain (r.valEnv VE)) := by
  have : (r.valEnv VE).map (fun p => (p.1, Ref.plain)) = r.binds (VE.map fun p => (p.1, Ref.plain)) := by
    simp [Renaming.valEnv, Renaming.binds, Renaming.ref]
  unfold Scope.pushPlain; rw [this]; exact h.push _

/-- What a reference and its image are to each other. -/
def RefRel (r : Renaming) (ref ref' : Ref) : Prop :=
  ref' = r.ref ref ∨ ∃ r' : Renaming, r'.WF ∧ ref' = r'.ref ref ∧ ref.Closed

theorem GlobRel.any {g g' : List ((ModId × Var) × Ref)} (h : GlobRel g g') (x : Var) :
    g'.any (·.1.2 == x) = g.any (·.1.2 == x) := by
  induction g generalizing g' with
  | nil => cases g' with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons e es ih =>
    cases g' with
    | nil => exact h.elim
    | cons e' es' =>
      obtain ⟨h1, _, h3⟩ := h
      simp only [List.any_cons, h1, ih h3]

theorem GlobRel.lookup {r : Renaming} {g g' : List ((ModId × Var) × Ref)} (h : GlobRel g g') (k : ModId × Var) :
    RefRel r ((g.lookup k).getD .plain) ((g'.lookup k).getD .plain) := by
  induction g generalizing g' with
  | nil => cases g' with
    | nil => exact .inl rfl
    | cons _ _ => exact h.elim
  | cons e es ih =>
    obtain ⟨k1, ref⟩ := e
    cases g' with
    | nil => exact h.elim
    | cons e' es' =>
      obtain ⟨k1', ref'⟩ := e'
      obtain ⟨h1, ⟨r', hr', h2, hc⟩, h3⟩ := h
      simp only at h1 h2 hc
      rw [h1, h2]
      simp only [List.lookup]
      by_cases hk : k = k1
      · subst hk; simp only [beq_self_eq_true, Option.getD_some]; exact .inr ⟨r', hr', rfl, hc⟩
      · have : (k == k1) = false := beq_eq_false_iff_ne.mpr hk
        simp only [this]; exact ih h3

theorem ScopeRel.ref {r : Renaming} {Γ Γ' : Scope} (h : ScopeRel r Γ Γ') (lv : LongId) :
    RefRel r (Γ.ref lv) (Γ'.ref lv) := by
  have hg : ∀ q x, RefRel r (Γ.globalRef q x) (Γ'.globalRef q x) := by
    intro q x
    unfold Scope.globalRef
    rw [h.global.any x, h.prov]
    split
    · split
      · exact h.global.lookup _
      · exact .inl rfl
    · exact .inl rfl
  unfold Scope.ref
  split
  · rw [h.locals, lookup_binds]
    cases Γ.locals.lookup lv.id with
    | some ref => exact .inl rfl
    | none =>
      rw [h.top, lookup_binds]
      cases Γ.top.lookup lv.id with
      | some ref => exact .inl rfl
      | none => exact hg _ _
  · exact hg _ _

/-! ## Occurrences -/

theorem Renaming.tys_map (r : Renaming) (l : List Ty) : r.tys l = l.map r.ty := Renaming.tys_eq_map r l

theorem contains_eq_decide {α : Type} [DecidableEq α] (l : List α) (x : α) : l.contains x = decide (x ∈ l) :=
  List.elem_eq_mem x l

theorem contains_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β} (hf : ∀ a b, f a = f b → a = b)
    (l : List α) (x : α) : (l.map f).contains (f x) = l.contains x := by
  rw [contains_eq_decide, contains_eq_decide]
  exact decide_eq_decide.mpr (mem_map_inj hf)

theorem tyVarsSeq_contains {r : Renaming} (hr : r.WF) (τ : Ty) (v : TyVar) :
    (r.ty τ).tyVarsSeq.contains (r.tvApply v) = τ.tyVarsSeq.contains v := by
  rw [tyVarsSeq_rename]; exact contains_map_inj hr.tv_inj _ _

theorem bv_contains {r : Renaming} (hr : r.WF) (bv : List BVar) (v : TyVar) :
    (bv.map r.bvar).contains (.ty (r.tvApply v)) = bv.contains (.ty v) :=
  contains_map_inj (x := BVar.ty v) hr.bvar_inj bv

theorem lookup_zip_rename {r r' : Renaming} (hr' : r'.WF) (bv : List BVar) (inst : List Ty) (v : TyVar) :
    ((bv.map r'.bvar).zip (inst.map r.ty)).lookup (.ty (r'.tvApply v)) = ((bv.zip inst).lookup (.ty v)).map r.ty := by
  induction bv generalizing inst with
  | nil => rfl
  | cons b bs ih =>
    cases inst with
    | nil => rfl
    | cons τ ts =>
      simp only [List.map_cons, List.zip_cons_cons, List.lookup]
      by_cases hb : BVar.ty v = b
      · subst hb; simp [Renaming.bvar]
      · have hb' : BVar.ty (r'.tvApply v) ≠ r'.bvar b := fun e => hb (hr'.bvar_inj (.ty v) b e)
        have e1 : (BVar.ty (r'.tvApply v) == r'.bvar b) = false := beq_eq_false_iff_ne.mpr hb'
        have e2 : (BVar.ty v == b) = false := beq_eq_false_iff_ne.mpr hb
        simp only [e1, e2]; exact ih ts

theorem occNum_rename {r r' : Renaming} (hr : r.WF) (hr' : r'.WF) (ρ : NumEnv) (bv : List BVar) (body : Ty)
    (inst : List Ty) (v : TyVar) (hv : bv.contains (.ty v) = false → r'.tvApply v = r.tvApply v) :
    occNum (r.numEnv ρ) (bv.map r'.bvar) (r'.ty body).tyVarsSeq ((bv.map r'.bvar).zip (inst.map r.ty)) (r'.tvApply v) =
      occNum ρ bv body.tyVarsSeq (bv.zip inst) v := by
  unfold occNum
  rw [bv_contains hr' bv v, tyVarsSeq_contains hr' body v, lookup_zip_rename hr' bv inst v]
  split
  · split
    · cases (bv.zip inst).lookup (.ty v) with
      | none => rfl
      | some τ => simp only [Option.map_some, Option.bind_some, resolve_rename hr]
    · rfl
  · rename_i hc
    rw [hv (by simpa using hc)]
    have := resolve_rename hr ρ (.var v)
    simp only [Renaming.ty] at this
    rw [this]

theorem occNums_rename {r r' : Renaming} (hr : r.WF) (hr' : r'.WF) (ρ : NumEnv) (bv : List BVar) (body : Ty)
    (inst : List Ty) : ∀ (V : List TyVar), (∀ v ∈ V, bv.contains (.ty v) = false → r'.tvApply v = r.tvApply v) →
    occNums (r.numEnv ρ) (bv.map r'.bvar) (r'.ty body).tyVarsSeq ((bv.map r'.bvar).zip (inst.map r.ty)) (V.map r'.tvApply) =
      occNums ρ bv body.tyVarsSeq (bv.zip inst) V
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.map_cons, occNums]
    rw [occNum_rename hr hr' ρ bv body inst v (h v (List.mem_cons_self ..)),
      occNums_rename hr hr' ρ bv body inst vs (fun w hw => h w (List.mem_cons_of_mem _ hw))]

/-- `specOcc` after the lookup. -/
def occRefSpec (ρ : NumEnv) (ref : Ref) (lv : LongId) (inst : List Ty) : Except SpecError (LongId × List Req) :=
  match ref with
  | .plain => .ok (lv, [])
  | .group gid V body bv => do
    let a ← occAssignment ρ V bv body inst
    pure (⟨lv.qual, copyName lv.id a⟩, [(gid, a)])
  | .basis V body bv => do
    let a ← occAssignment ρ V bv body inst
    pure (⟨lv.qual, copyName lv.id a⟩, [])

theorem specOcc_eq (ρ : NumEnv) (Γ : Scope) (lv : LongId) (inst : List Ty) :
    specOcc ρ Γ lv inst = occRefSpec ρ (Γ.ref lv) lv inst := rfl

theorem RefRel.spec_occ {r : Renaming} (hr : r.WF) {ref ref' : Ref} (h : RefRel r ref ref') (ρ : NumEnv)
    (lv : LongId) (inst : List Ty) : occRefSpec (r.numEnv ρ) ref' lv (r.tys inst) = occRefSpec ρ ref lv inst := by
  have key : ∀ r' : Renaming, r'.WF → ∀ V bv body,
      (∀ v ∈ V, bv.contains (.ty v) = false → r'.tvApply v = r.tvApply v) →
      occAssignment (r.numEnv ρ) (V.map r'.tvApply) (bv.map r'.bvar) (r'.ty body) (r.tys inst) =
        occAssignment ρ V bv body inst := by
    intro r' hr' V bv body hV
    unfold occAssignment
    rw [Renaming.tys_map]
    exact occNums_rename hr hr' ρ bv body inst V hV
  have hcl : ∀ (V : List TyVar) (bv : List BVar), (∀ v ∈ V, BVar.ty v ∈ bv) → ∀ (r' : Renaming),
      ∀ v ∈ V, bv.contains (.ty v) = false → r'.tvApply v = r.tvApply v := by
    intro V bv hc r' v hv hn
    rw [contains_eq_decide, decide_eq_false_iff_not] at hn
    exact absurd (hc v hv) hn
  rcases h with rfl | ⟨r', hr', rfl, hc⟩
  · cases ref with
    | plain => rfl
    | group gid V body bv => simp only [Renaming.ref, occRefSpec]; rw [key r hr V bv body (fun _ _ _ => rfl)]
    | basis V body bv => simp only [Renaming.ref, occRefSpec]; rw [key r hr V bv body (fun _ _ _ => rfl)]
  · cases ref with
    | plain => rfl
    | group gid V body bv =>
      simp only [Renaming.ref, occRefSpec]; rw [key r' hr' V bv body (hcl V bv hc r')]
    | basis V body bv =>
      simp only [Renaming.ref, occRefSpec]; rw [key r' hr' V bv body (hcl V bv hc r')]

theorem specOcc_rename {r : Renaming} (hr : r.WF) {Γ Γ' : Scope} (h : ScopeRel r Γ Γ') (ρ : NumEnv)
    (lv : LongId) (inst : List Ty) : specOcc (r.numEnv ρ) Γ' lv (r.tys inst) = specOcc ρ Γ lv inst := by
  rw [specOcc_eq, specOcc_eq]
  exact (h.ref lv).spec_occ hr ρ lv inst

theorem specSCon_rename {r : Renaming} (hr : r.WF) (ρ : NumEnv) (sc : Src.SLit) (τ : Ty) :
    specSCon (r.numEnv ρ) sc (r.ty τ) = specSCon ρ sc τ := by
  cases sc <;> simp only [specSCon, resolve_rename hr]

/-! ## Patterns: specialisation reads only the bare pattern -/

mutual
theorem erAtPat_congr (a : Assignment) : (p : AAtPat) → ∀ p' : AAtPat, p'.erase = p.erase → erAtPat a p' = erAtPat a p
  | .wild _, p', h | .scon _ _, p', h | .var _ _, p', h | .con _ _ _, p', h | .unit, p', h | .nil _, p', h => by
    cases p' <;> simp [AAtPat.erase] at h <;> (try subst_vars) <;> rfl
  | .tuple p1 p2 p3, p', h => by
    cases p' <;> simp [AAtPat.erase] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only [erAtPat, erPat_congr a p1 _ h1, erPat_congr a p2 _ h2, erPatOpt_congr a p3 _ h3]
  | .record row _, p', h => by
    cases p' <;> simp [AAtPat.erase] at h
    simp only [erAtPat, erPatRowOpt_congr row _ h, firstLabel_congr row _ h]
  | .paren q, p', h => by
    cases p' <;> simp [AAtPat.erase] at h
    simp only [erAtPat, erPat_congr a q _ h]
theorem erPatRow_congr : (row : APatRow) → ∀ row' : APatRow, row'.erase = row.erase → erPatRow row' = erPatRow row
  | .field l _ rest, row', h => by
    cases row' with
    | field l' _ rest' =>
      simp [APatRow.erase] at h
      obtain ⟨h1, h2⟩ := h
      simp only [erPatRow, erPatRowOpt_congr rest _ h2, h1]
theorem erPatRowOpt_congr : (row : Option APatRow) → ∀ row' : Option APatRow,
    APatRow.eraseOpt row' = APatRow.eraseOpt row → erPatRowOpt row' = erPatRowOpt row
  | none, row', h => by cases row' <;> simp [APatRow.eraseOpt] at h; rfl
  | some row, row', h => by
    cases row' <;> simp [APatRow.eraseOpt] at h
    simp only [erPatRowOpt, erPatRow_congr row _ h]
theorem erPat_congr (a : Assignment) : (p : APat) → ∀ p' : APat, p'.erase = p.erase → erPat a p' = erPat a p
  | .atpat q, p', h => by
    cases p' <;> simp [APat.erase] at h
    simp only [erPat, erAtPat_congr a q _ h]
  | .con lc _ args _, p', h => by
    cases p' <;> simp [APat.erase] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [erPat, erAtPatList_congr a args _ h2]
  | .cons p1 p2, p', h => by
    cases p' <;> simp [APat.erase] at h
    obtain ⟨h1, h2⟩ := h
    simp only [erPat, erPat_congr a p1 _ h1, erPat_congr a p2 _ h2]
  | .as q x, p', h => by
    cases p' <;> simp [APat.erase] at h
    obtain ⟨h1, rfl⟩ := h
    simp only [erPat, erPat_congr a q _ h1]
theorem erPatOpt_congr (a : Assignment) : (p : Option APat) → ∀ p' : Option APat,
    APat.eraseOpt p' = APat.eraseOpt p → erPatOpt a p' = erPatOpt a p
  | none, p', h => by cases p' <;> simp [APat.eraseOpt] at h; rfl
  | some q, p', h => by
    cases p' <;> simp [APat.eraseOpt] at h
    simp only [erPatOpt, erPat_congr a q _ h]
theorem erAtPatList_congr (a : Assignment) : (ps : List AAtPat) → ∀ ps' : List AAtPat,
    AAtPat.eraseList ps' = AAtPat.eraseList ps → erAtPatList a ps' = erAtPatList a ps
  | [], ps', h => by cases ps' <;> simp [AAtPat.eraseList] at h; rfl
  | q :: qs, ps', h => by
    cases ps' <;> simp [AAtPat.eraseList] at h
    obtain ⟨h1, h2⟩ := h
    simp only [erAtPatList, erAtPat_congr a q _ h1, erAtPatList_congr a qs _ h2]
theorem firstLabel_congr : (row : Option APatRow) → ∀ row' : Option APatRow,
    APatRow.eraseOpt row' = APatRow.eraseOpt row → APatRow.firstLabel row' = APatRow.firstLabel row
  | none, row', h => by cases row' <;> simp [APatRow.eraseOpt] at h; rfl
  | some (.field l _ _), row', h => by
    cases row' with
    | none => simp [APatRow.eraseOpt] at h
    | some row' =>
      cases row' with
      | field l' _ _ =>
        simp [APatRow.eraseOpt, APatRow.erase] at h
        simp only [APatRow.firstLabel, h.1]
end

end StandardElm.Stat
