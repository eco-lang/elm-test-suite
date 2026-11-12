/-
  A Standard Definition of Elm? Mechanisation: the substitution algebra of milestone (b) of plan
  step 11 (section 8, L1; section 4, K1 to K3 and K10 restricted to type variables).

  A *functional substitution* `s : FSub` maps every type variable to a type; `sb s τ` replaces the
  type variables of `τ` simultaneously and leaves record rows' tails alone (fragment F_b has no
  row variable). It is total, so composition is function composition (`comp`), and its algebra
  (identity, composition, congruence on the variables that occur, the variables of an image,
  sizes for the occurs check) is proved once here. A substitution of step 9 (`Stat.Subst`) with
  no row binding is a functional one: `apply_ofBnd` (the bridge), so that every statement below
  about `sb` is one about step 9's `Subst.apply` on such substitutions.

  Finite substitutions are binding lists `Bnd` (as step 9's `Subst.ty`), read by `lk`.
-/
import StandardElmMech.Stat.Annotated

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-- A substitution on type variables, total. -/
abbrev FSub := TyVar → Ty

/-- The identity substitution. -/
def idS : FSub := fun a => .var a

mutual
def sb (s : FSub) : Ty → Ty
  | .var a => s a
  | .record ρ tl => .record (sbRow s ρ) tl
  | .fn a b => .fn (sb s a) (sb s b)
  | .con as t => .con (sbList s as) t
def sbRow (s : FSub) : Row → Row
  | [] => []
  | (l, τ) :: rest => (l, sb s τ) :: sbRow s rest
def sbList (s : FSub) : List Ty → List Ty
  | [] => []
  | τ :: rest => sb s τ :: sbList s rest
end

theorem sbList_eq (s : FSub) : ∀ l : List Ty, sbList s l = l.map (sb s)
  | [] => rfl
  | x :: r => by simp [sbList, sbList_eq s r]

theorem sbRow_eq (s : FSub) : ∀ l : Row, sbRow s l = l.map (fun p => (p.1, sb s p.2))
  | [] => rfl
  | (l, x) :: r => by simp [sbRow, sbRow_eq s r]

/-- `t ∘ s`: first `s`, then `t`. -/
def comp (t s : FSub) : FSub := fun a => sb t (s a)

/-- The substitution of one variable. -/
def upd (a : TyVar) (τ : Ty) : FSub := fun b => if b = a then τ else .var b

/-! ## Identity, composition, congruence -/

mutual
theorem sb_id : ∀ τ : Ty, sb idS τ = τ
  | .var _ => rfl
  | .record ρ tl => by simp only [sb, sbRow_id ρ]
  | .fn a b => by simp only [sb, sb_id a, sb_id b]
  | .con as t => by simp only [sb, sbList_id as]
theorem sbRow_id : ∀ ρ : Row, sbRow idS ρ = ρ
  | [] => rfl
  | (l, x) :: r => by simp only [sbRow, sb_id x, sbRow_id r]
theorem sbList_id : ∀ l : List Ty, sbList idS l = l
  | [] => rfl
  | x :: r => by simp only [sbList, sb_id x, sbList_id r]
end

mutual
/-- K10 for functional substitutions. -/
theorem sb_sb (s t : FSub) : ∀ τ : Ty, sb t (sb s τ) = sb (comp t s) τ
  | .var _ => rfl
  | .record ρ tl => by simp only [sb, sbRow_sb s t ρ]
  | .fn a b => by simp only [sb, sb_sb s t a, sb_sb s t b]
  | .con as c => by simp only [sb, sbList_sb s t as]
theorem sbRow_sb (s t : FSub) : ∀ ρ : Row, sbRow t (sbRow s ρ) = sbRow (comp t s) ρ
  | [] => rfl
  | (l, x) :: r => by simp only [sbRow, sb_sb s t x, sbRow_sb s t r]
theorem sbList_sb (s t : FSub) : ∀ l : List Ty, sbList t (sbList s l) = sbList (comp t s) l
  | [] => rfl
  | x :: r => by simp only [sbList, sb_sb s t x, sbList_sb s t r]
end

theorem comp_assoc (u t s : FSub) : comp u (comp t s) = comp (comp u t) s := by
  funext a; simp only [comp, sb_sb]

theorem comp_id (s : FSub) : comp s idS = s := rfl
theorem id_comp (s : FSub) : comp idS s = s := by funext a; simp only [comp, sb_id]

mutual
theorem sb_congr {s t : FSub} : ∀ τ : Ty, (∀ a, BVar.ty a ∈ τ.vars → s a = t a) → sb s τ = sb t τ
  | .var a, h => h a (by simp [Ty.vars])
  | .record ρ none, h => by
    simp only [sb, sbRow_congr ρ (fun a ha => h a (by simpa [Ty.vars] using ha))]
  | .record ρ (some _), h => by
    simp only [sb, sbRow_congr ρ (fun a ha => h a (by simp [Ty.vars, ha]))]
  | .fn a b, h => by
    simp only [sb, sb_congr a (fun x hx => h x (by simp [Ty.vars, hx])),
      sb_congr b (fun x hx => h x (by simp [Ty.vars, hx]))]
  | .con as _, h => by simp only [sb, sbList_congr as (fun a ha => h a (by simpa [Ty.vars] using ha))]
theorem sbRow_congr {s t : FSub} : ∀ ρ : Row, (∀ a, BVar.ty a ∈ Ty.rowVars ρ → s a = t a) →
    sbRow s ρ = sbRow t ρ
  | [], _ => rfl
  | (l, x) :: r, h => by
    simp only [sbRow, sb_congr x (fun a ha => h a (by simp [Ty.rowVars, ha])),
      sbRow_congr r (fun a ha => h a (by simp [Ty.rowVars, ha]))]
theorem sbList_congr {s t : FSub} : ∀ l : List Ty, (∀ a, BVar.ty a ∈ Ty.listVars l → s a = t a) →
    sbList s l = sbList t l
  | [], _ => rfl
  | x :: r, h => by
    simp only [sbList, sb_congr x (fun a ha => h a (by simp [Ty.listVars, ha])),
      sbList_congr r (fun a ha => h a (by simp [Ty.listVars, ha]))]
end

/-! ## The variables of an image -/

mutual
theorem vars_sb (s : FSub) : ∀ (τ : Ty) (v : BVar), v ∈ (sb s τ).vars →
    (∃ e, v = .row e ∧ v ∈ τ.vars) ∨ ∃ a, BVar.ty a ∈ τ.vars ∧ v ∈ (s a).vars
  | .var a, v, h => .inr ⟨a, by simp [Ty.vars], h⟩
  | .record ρ none, v, h => by
    simp only [sb, Ty.vars] at h ⊢
    exact vars_sbRow s ρ v h
  | .record ρ (some e), v, h => by
    simp only [sb, Ty.vars, List.mem_append, List.mem_singleton] at h ⊢
    rcases h with h | rfl
    · rcases vars_sbRow s ρ v h with ⟨e', rfl, h'⟩ | ⟨a, ha, h'⟩
      · exact .inl ⟨e', rfl, .inl h'⟩
      · exact .inr ⟨a, .inl ha, h'⟩
    · exact .inl ⟨e, rfl, .inr rfl⟩
  | .fn a b, v, h => by
    simp only [sb, Ty.vars, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases vars_sb s a v h with ⟨e', rfl, h'⟩ | ⟨x, hx, h'⟩
      · exact .inl ⟨e', rfl, .inl h'⟩
      · exact .inr ⟨x, .inl hx, h'⟩
    · rcases vars_sb s b v h with ⟨e', rfl, h'⟩ | ⟨x, hx, h'⟩
      · exact .inl ⟨e', rfl, .inr h'⟩
      · exact .inr ⟨x, .inr hx, h'⟩
  | .con as _, v, h => by
    simp only [sb, Ty.vars] at h ⊢
    exact vars_sbList s as v h
theorem vars_sbRow (s : FSub) : ∀ (ρ : Row) (v : BVar), v ∈ Ty.rowVars (sbRow s ρ) →
    (∃ e, v = .row e ∧ v ∈ Ty.rowVars ρ) ∨ ∃ a, BVar.ty a ∈ Ty.rowVars ρ ∧ v ∈ (s a).vars
  | [], _, h => by simp [sbRow, Ty.rowVars] at h
  | (l, x) :: r, v, h => by
    simp only [sbRow, Ty.rowVars, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases vars_sb s x v h with ⟨e', rfl, h'⟩ | ⟨y, hy, h'⟩
      · exact .inl ⟨e', rfl, .inl h'⟩
      · exact .inr ⟨y, .inl hy, h'⟩
    · rcases vars_sbRow s r v h with ⟨e', rfl, h'⟩ | ⟨y, hy, h'⟩
      · exact .inl ⟨e', rfl, .inr h'⟩
      · exact .inr ⟨y, .inr hy, h'⟩
theorem vars_sbList (s : FSub) : ∀ (l : List Ty) (v : BVar), v ∈ Ty.listVars (sbList s l) →
    (∃ e, v = .row e ∧ v ∈ Ty.listVars l) ∨ ∃ a, BVar.ty a ∈ Ty.listVars l ∧ v ∈ (s a).vars
  | [], _, h => by simp [sbList, Ty.listVars] at h
  | x :: r, v, h => by
    simp only [sbList, Ty.listVars, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases vars_sb s x v h with ⟨e', rfl, h'⟩ | ⟨y, hy, h'⟩
      · exact .inl ⟨e', rfl, .inl h'⟩
      · exact .inr ⟨y, .inl hy, h'⟩
    · rcases vars_sbList s r v h with ⟨e', rfl, h'⟩ | ⟨y, hy, h'⟩
      · exact .inl ⟨e', rfl, .inr h'⟩
      · exact .inr ⟨y, .inr hy, h'⟩
end

/-- The type variables of an image: images of the type variables. -/
theorem tyvar_sb {s : FSub} {τ : Ty} {b : TyVar} (h : BVar.ty b ∈ (sb s τ).vars) :
    ∃ a, BVar.ty a ∈ τ.vars ∧ BVar.ty b ∈ (s a).vars := by
  rcases vars_sb s τ _ h with ⟨_, h', _⟩ | h'
  · cases h'
  · exact h'

mutual
theorem vars_sb_of (s : FSub) : ∀ (τ : Ty) (a : TyVar) (v : BVar), BVar.ty a ∈ τ.vars → v ∈ (s a).vars →
    v ∈ (sb s τ).vars
  | .var b, a, v, ha, hv => by
    simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at ha; subst ha; exact hv
  | .record ρ none, a, v, ha, hv => by
    simp only [sb, Ty.vars] at ha ⊢; exact vars_sbRow_of s ρ a v ha hv
  | .record ρ (some e), a, v, ha, hv => by
    simp only [sb, Ty.vars, List.mem_append, List.mem_singleton] at ha ⊢
    rcases ha with ha | ha
    · exact .inl (vars_sbRow_of s ρ a v ha hv)
    · cases ha
  | .fn x y, a, v, ha, hv => by
    simp only [sb, Ty.vars, List.mem_append] at ha ⊢
    rcases ha with ha | ha
    · exact .inl (vars_sb_of s x a v ha hv)
    · exact .inr (vars_sb_of s y a v ha hv)
  | .con as _, a, v, ha, hv => by
    simp only [sb, Ty.vars] at ha ⊢; exact vars_sbList_of s as a v ha hv
theorem vars_sbRow_of (s : FSub) : ∀ (ρ : Row) (a : TyVar) (v : BVar), BVar.ty a ∈ Ty.rowVars ρ →
    v ∈ (s a).vars → v ∈ Ty.rowVars (sbRow s ρ)
  | [], _, _, ha, _ => by simp [Ty.rowVars] at ha
  | (l, x) :: r, a, v, ha, hv => by
    simp only [sbRow, Ty.rowVars, List.mem_append] at ha ⊢
    rcases ha with ha | ha
    · exact .inl (vars_sb_of s x a v ha hv)
    · exact .inr (vars_sbRow_of s r a v ha hv)
theorem vars_sbList_of (s : FSub) : ∀ (l : List Ty) (a : TyVar) (v : BVar), BVar.ty a ∈ Ty.listVars l →
    v ∈ (s a).vars → v ∈ Ty.listVars (sbList s l)
  | [], _, _, ha, _ => by simp [Ty.listVars] at ha
  | x :: r, a, v, ha, hv => by
    simp only [sbList, Ty.listVars, List.mem_append] at ha ⊢
    rcases ha with ha | ha
    · exact .inl (vars_sb_of s x a v ha hv)
    · exact .inr (vars_sbList_of s r a v ha hv)
end

/-- A variable occurs in its own type. -/
theorem mem_vars_var (a : TyVar) : BVar.ty a ∈ (Ty.var a).vars := by simp [Ty.vars]

mutual
theorem fixes_of_sb_eq {s : FSub} : ∀ (τ : Ty), sb s τ = τ → ∀ a, BVar.ty a ∈ τ.vars → s a = .var a
  | .var _, h, a, ha => by
    simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at ha; subst ha; exact h
  | .record ρ none, h, a, ha => by
    simp only [sb, Ty.record.injEq] at h
    simp only [Ty.vars] at ha; exact fixes_of_sbRow_eq ρ h.1 a ha
  | .record ρ (some _), h, a, ha => by
    simp only [sb, Ty.record.injEq] at h
    simp only [Ty.vars, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · exact fixes_of_sbRow_eq ρ h.1 a ha
    · cases ha
  | .fn x y, h, a, ha => by
    simp only [sb, Ty.fn.injEq] at h
    simp only [Ty.vars, List.mem_append] at ha
    rcases ha with ha | ha
    · exact fixes_of_sb_eq x h.1 a ha
    · exact fixes_of_sb_eq y h.2 a ha
  | .con as _, h, a, ha => by
    simp only [sb, Ty.con.injEq] at h
    simp only [Ty.vars] at ha; exact fixes_of_sbList_eq as h.1 a ha
theorem fixes_of_sbRow_eq {s : FSub} : ∀ (ρ : Row), sbRow s ρ = ρ → ∀ a, BVar.ty a ∈ Ty.rowVars ρ → s a = .var a
  | [], _, _, ha => by simp [Ty.rowVars] at ha
  | (l, x) :: r, h, a, ha => by
    simp only [sbRow, List.cons.injEq, Prod.mk.injEq, true_and] at h
    simp only [Ty.rowVars, List.mem_append] at ha
    rcases ha with ha | ha
    · exact fixes_of_sb_eq x h.1 a ha
    · exact fixes_of_sbRow_eq r h.2 a ha
theorem fixes_of_sbList_eq {s : FSub} : ∀ (l : List Ty), sbList s l = l → ∀ a, BVar.ty a ∈ Ty.listVars l → s a = .var a
  | [], _, _, ha => by simp [Ty.listVars] at ha
  | x :: r, h, a, ha => by
    simp only [sbList, List.cons.injEq] at h
    simp only [Ty.listVars, List.mem_append] at ha
    rcases ha with ha | ha
    · exact fixes_of_sb_eq x h.1 a ha
    · exact fixes_of_sbList_eq r h.2 a ha
end

/-- `sb s τ = τ` exactly when `s` fixes the type variables of `τ`. -/
theorem sb_eq_self_iff {s : FSub} {τ : Ty} : sb s τ = τ ↔ ∀ a, BVar.ty a ∈ τ.vars → s a = .var a :=
  ⟨fixes_of_sb_eq τ, fun h => by rw [sb_congr τ (t := idS) h, sb_id]⟩

/-! ## Sizes and the occurs check (K3) -/

mutual
def tsize : Ty → Nat
  | .var _ => 1
  | .record ρ _ => 1 + rsize ρ
  | .fn a b => 1 + tsize a + tsize b
  | .con as _ => 1 + lsize as
def rsize : Row → Nat
  | [] => 0
  | (_, τ) :: rest => tsize τ + rsize rest
def lsize : List Ty → Nat
  | [] => 0
  | τ :: rest => tsize τ + lsize rest
end

theorem tsize_pos : ∀ τ : Ty, 0 < tsize τ
  | .var _ => by simp [tsize]
  | .record _ _ => by simp only [tsize]; omega
  | .fn _ _ => by simp only [tsize]; omega
  | .con _ _ => by simp only [tsize]; omega

mutual
theorem size_le_sb (s : FSub) : ∀ (τ : Ty) (a : TyVar), BVar.ty a ∈ τ.vars → tsize (s a) ≤ tsize (sb s τ)
  | .var b, a, ha => by
    simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at ha; subst ha; exact Nat.le_refl _
  | .record ρ none, a, ha => by
    simp only [Ty.vars] at ha; have := size_lt_sbRow s ρ a ha; simp only [sb, tsize]; omega
  | .record ρ (some _), a, ha => by
    simp only [Ty.vars, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · have := size_lt_sbRow s ρ a ha; simp only [sb, tsize]; omega
    · cases ha
  | .fn x y, a, ha => by
    simp only [Ty.vars, List.mem_append] at ha
    simp only [sb, tsize]
    rcases ha with ha | ha
    · have := size_le_sb s x a ha; omega
    · have := size_le_sb s y a ha; omega
  | .con as _, a, ha => by
    simp only [Ty.vars] at ha; have := size_lt_sbList s as a ha; simp only [sb, tsize]; omega
theorem size_lt_sbRow (s : FSub) : ∀ (ρ : Row) (a : TyVar), BVar.ty a ∈ Ty.rowVars ρ →
    tsize (s a) < 1 + rsize (sbRow s ρ)
  | [], _, ha => by simp [Ty.rowVars] at ha
  | (_, x) :: r, a, ha => by
    simp only [Ty.rowVars, List.mem_append] at ha
    simp only [sbRow, rsize]
    rcases ha with ha | ha
    · have := size_le_sb s x a ha; omega
    · have := size_lt_sbRow s r a ha; omega
theorem size_lt_sbList (s : FSub) : ∀ (l : List Ty) (a : TyVar), BVar.ty a ∈ Ty.listVars l →
    tsize (s a) < 1 + lsize (sbList s l)
  | [], _, ha => by simp [Ty.listVars] at ha
  | x :: r, a, ha => by
    simp only [Ty.listVars, List.mem_append] at ha
    simp only [sbList, lsize]
    rcases ha with ha | ha
    · have := size_le_sb s x a ha; omega
    · have := size_lt_sbList s r a ha; omega
end

/-- K3: a variable never equals, under any substitution, a proper type it occurs in. -/
theorem occurs_ne (s : FSub) {a : TyVar} {τ : Ty} (h : BVar.ty a ∈ τ.vars) (hne : τ ≠ .var a) :
    s a ≠ sb s τ := by
  intro e
  have hs : tsize (s a) < tsize (sb s τ) := by
    match τ, h with
    | .var _, h =>
      simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at h; subst h; exact absurd rfl hne
    | .record ρ none, h =>
      simp only [Ty.vars] at h; have := size_lt_sbRow s ρ a h; simp only [sb, tsize]; omega
    | .record ρ (some _), h =>
      simp only [Ty.vars, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · have := size_lt_sbRow s ρ a h; simp only [sb, tsize]; omega
      · cases h
    | .fn x y, h =>
      simp only [Ty.vars, List.mem_append] at h
      simp only [sb, tsize]
      rcases h with h | h
      · have := size_le_sb s x a h; omega
      · have := size_le_sb s y a h; omega
    | .con as _, h =>
      simp only [Ty.vars] at h; have := size_lt_sbList s as a h; simp only [sb, tsize]; omega
  rw [e] at hs; exact Nat.lt_irrefl _ hs

/-! ## Single bindings (K2) -/

theorem upd_self (a : TyVar) (τ : Ty) : upd a τ a = τ := by simp [upd]
theorem upd_ne {a b : TyVar} (τ : Ty) (h : b ≠ a) : upd a τ b = .var b := by simp [upd, h]

/-- A binding changes nothing where its variable does not occur. -/
theorem sb_upd_of_not_mem {a : TyVar} {τ σ : Ty} (h : BVar.ty a ∉ σ.vars) : sb (upd a τ) σ = σ :=
  sb_eq_self_iff.mpr fun _ hb => upd_ne τ (fun e => h (e ▸ hb))

/-- K2: if `s a = sb s τ`, then `s` absorbs the binding `a ↦ τ`. -/
theorem comp_upd {s : FSub} {a : TyVar} {τ : Ty} (h : s a = sb s τ) : comp s (upd a τ) = s := by
  funext b
  by_cases hb : b = a
  · subst hb; simp only [comp, upd_self]; exact h.symm
  · simp only [comp, upd_ne τ hb]; rfl

/-- The variables of an image under a single binding. -/
theorem tyvar_sb_upd {a b : TyVar} {τ σ : Ty} (h : BVar.ty b ∈ (sb (upd a τ) σ).vars) :
    (BVar.ty b ∈ σ.vars ∧ b ≠ a) ∨ BVar.ty b ∈ τ.vars := by
  obtain ⟨c, hc, hb⟩ := tyvar_sb h
  by_cases hca : c = a
  · subst hca; rw [upd_self] at hb; exact .inr hb
  · rw [upd_ne τ hca] at hb
    simp only [Ty.vars, List.mem_singleton, BVar.ty.injEq] at hb; subst hb
    exact .inl ⟨hc, hca⟩

/-! ## Idempotence -/

/-- `s` is idempotent: no variable of an image is moved. -/
def Idem (s : FSub) : Prop := ∀ a b, BVar.ty b ∈ (s a).vars → s b = .var b

theorem Idem.comp_self {s : FSub} (h : Idem s) : comp s s = s := by
  funext a; exact sb_eq_self_iff.mpr (h a)

/-! ## Binding lists and the bridge to step 9's substitutions -/

/-- A finite substitution as a binding list (the first binding of a variable counts). -/
abbrev Bnd := List (TyVar × Ty)

def lk (θ : Bnd) (a : TyVar) : Ty := (FMap.find? θ a).getD (.var a)

theorem lk_nil (a : TyVar) : lk [] a = .var a := rfl

theorem lk_cons (θ : Bnd) (a b : TyVar) (τ : Ty) :
    lk ((a, τ) :: θ) b = if a = b then τ else lk θ b := by
  simp only [lk, FMap.find?]; split <;> rfl

theorem find?_mapSnd {K V W : Type} [DecidableEq K] (g : V → W) (k : K) :
    ∀ l : List (K × V), FMap.find? (l.map (fun p => (p.1, g p.2))) k = (FMap.find? l k).map g
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, FMap.find?]
    split <;> simp [find?_mapSnd g k rest]

/-- Step 9's substitution with these type bindings and no row binding. -/
def ofBnd (θ : Bnd) : Subst := ⟨θ, []⟩

mutual
/-- The bridge: step 9's `Subst.apply` of a substitution without row bindings is `sb`. -/
theorem apply_ofBnd (θ : Bnd) : ∀ τ : Ty, (ofBnd θ).apply τ = some (sb (lk θ) τ)
  | .var _ => rfl
  | .record ρ none => by simp only [Subst.apply, applyRow_ofBnd θ ρ, sb]
  | .record ρ (some e) => by
    have h := applyRow_ofBnd θ ρ
    simp only [ofBnd] at h
    simp only [Subst.apply, ofBnd, h, sb, FMap.find?_nil]
  | .fn a b => by simp only [Subst.apply, apply_ofBnd θ a, apply_ofBnd θ b, sb]
  | .con as t => by simp only [Subst.apply, applyList_ofBnd θ as, sb]
theorem applyRow_ofBnd (θ : Bnd) : ∀ ρ : Row, (ofBnd θ).applyRow ρ = some (sbRow (lk θ) ρ)
  | [] => rfl
  | (l, x) :: r => by simp only [Subst.applyRow, apply_ofBnd θ x, applyRow_ofBnd θ r, sbRow]
theorem applyList_ofBnd (θ : Bnd) : ∀ l : List Ty, (ofBnd θ).applyList l = some (sbList (lk θ) l)
  | [] => rfl
  | x :: r => by simp only [Subst.applyList, apply_ofBnd θ x, applyList_ofBnd θ r, sbList]
end

/-- The identity substitution of step 9 is defined everywhere and changes nothing. -/
theorem apply_id (τ : Ty) : Subst.id.apply τ = some τ := by
  have := apply_ofBnd [] τ
  simp only [ofBnd] at this
  rw [show (Subst.id : Subst) = ⟨[], []⟩ from rfl, this]
  congr 1
  exact (sb_congr τ (t := idS) (fun _ _ => rfl)).trans (sb_id τ)

end StandardElm.Stat.Complete
