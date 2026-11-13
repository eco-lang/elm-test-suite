/-
  A Standard Definition of Elm? Mechanisation: substitutions of type *and row* variables,
  milestone (d) of plan step 11 (section 1; section 8, K2, K3, K9 to K11 with rows).

  An `RSub` maps every type variable to a type and every row variable to a row with a tail (the
  record type `⟨ϱ | t⟩` it stands for). `rsb s τ` substitutes simultaneously; at a record
  `⟨ρ | ε⟩` the row of `s ε` is *merged* (`mrg`, RowAlg.lean) into the substituted `ρ`. The
  substitution is total, and its algebra holds for all types: identity (`rsb_rid`), composition
  (`rsb_rsb`, K10), congruence on the variables that occur (`rsb_congr`), the variables of an image
  (`mem_vars_rsb`), sizes and the occurs check through rows (`occurs_neR`, K3). A substitution of
  type variables only (FSubst.lean's `FSub`) is the special case `ofF` (`rsb_ofF`).

  *Definedness is canonicity (K9).* The book's substitution is undefined where a record would get
  a label twice (A23). Here such a substitution gives a row with a repeated label, which is not
  sorted; so "defined on `τ`, with a well-formed result" is `cnB (rsb s τ)` (every row of the image
  strictly sorted, `cnB`). `cn_rsb` gives it from canonical images of the variables and the lacks
  condition (`lacksOf e τ`: the labels of the rows that `e` extends in `τ`), and `lacks_of_cn`
  is the converse used by the lacks check of unification.

  Binding lists `RBnd` (keys type or row variables, a row variable bound to a record type) are
  read by `toRS`; a binding `v ↦ σ` composes (`toRS_bindR`).
-/
import StandardElmMech.Stat.Complete.RowAlg
import StandardElmMech.Stat.Complete.MguCls

namespace StandardElm.Stat.Complete
open StandardElm (Lab)
open StandardElm.Stat

/-! ## Substitutions -/

/-- A substitution of type variables (to types) and row variables (to a row and a tail). -/
structure RSub where
  t : TyVar → Ty
  r : RowVar → Row × Option RowVar

/-- The image of a record tail. -/
def RSub.tl (s : RSub) : Option RowVar → Row × Option RowVar
  | none => ([], none)
  | some e => s.r e

mutual
def rsb (s : RSub) : Ty → Ty
  | .var a => s.t a
  | .record ρ tl => .record (mrg (rsbRow s ρ) (s.tl tl).1) (s.tl tl).2
  | .fn a b => .fn (rsb s a) (rsb s b)
  | .con as c => .con (rsbList s as) c
def rsbRow (s : RSub) : Row → Row
  | [] => []
  | (l, τ) :: rest => (l, rsb s τ) :: rsbRow s rest
def rsbList (s : RSub) : List Ty → List Ty
  | [] => []
  | τ :: rest => rsb s τ :: rsbList s rest
end

theorem rsbRow_eq (s : RSub) : ∀ ρ : Row, rsbRow s ρ = mapV (rsb s) ρ
  | [] => rfl
  | (l, x) :: r => by rw [rsbRow, rsbRow_eq s r]; rfl

theorem rsbList_eq (s : RSub) : ∀ l : List Ty, rsbList s l = l.map (rsb s)
  | [] => rfl
  | x :: r => by simp [rsbList, rsbList_eq s r]

theorem rsbList_length (s : RSub) (l : List Ty) : (rsbList s l).length = l.length := by
  rw [rsbList_eq]; simp

theorem labs_rsbRow (s : RSub) (ρ : Row) : labs (rsbRow s ρ) = labs ρ := by
  rw [rsbRow_eq, labs_mapV]

theorem sorted_rsbRow_iff (s : RSub) {ρ : Row} : Sorted (rsbRow s ρ) ↔ Sorted ρ := by
  rw [rsbRow_eq, sorted_mapV_iff]

theorem mem_rsbRow {s : RSub} {ρ : Row} {x : Lab × Ty} : x ∈ rsbRow s ρ ↔ ∃ p ∈ ρ, x = (p.1, rsb s p.2) := by
  rw [rsbRow_eq, mem_mapV]

/-- The image of a row with a tail: `s ⟨ρ | tl⟩`. -/
def RSub.rx (s : RSub) (q : Row × Option RowVar) : Row × Option RowVar :=
  (mrg (rsbRow s q.1) (s.tl q.2).1, (s.tl q.2).2)

theorem rsb_record (s : RSub) (ρ : Row) (tl : Option RowVar) :
    rsb s (.record ρ tl) = .record (s.rx (ρ, tl)).1 (s.rx (ρ, tl)).2 := rfl

/-- `t ∘ s`. -/
def rcomp (t s : RSub) : RSub := ⟨fun a => rsb t (s.t a), fun e => t.rx (s.r e)⟩

def rid : RSub := ⟨fun a => .var a, fun e => ([], some e)⟩

/-- A substitution of type variables only. -/
def ofF (s : FSub) : RSub := ⟨s, fun e => ([], some e)⟩

theorem RSub.eq_of {s t : RSub} (h1 : ∀ a, s.t a = t.t a) (h2 : ∀ e, s.r e = t.r e) : s = t := by
  cases s; cases t; simp only [RSub.mk.injEq]; exact ⟨funext h1, funext h2⟩

theorem rid_tl (tl : Option RowVar) : rid.tl tl = ([], tl) := by cases tl <;> rfl

theorem ofF_tl (s : FSub) (tl : Option RowVar) : (ofF s).tl tl = ([], tl) := by cases tl <;> rfl

theorem rcomp_tl (t s : RSub) (tl : Option RowVar) : (rcomp t s).tl tl = t.rx (s.tl tl) := by
  cases tl <;> rfl

mutual
theorem rsb_rid : ∀ τ : Ty, rsb rid τ = τ
  | .var _ => rfl
  | .record ρ tl => by rw [rsb, rsbRow_rid ρ, rid_tl, mrg_nil_right]
  | .fn a b => by rw [rsb, rsb_rid a, rsb_rid b]
  | .con as c => by rw [rsb, rsbList_rid as]
theorem rsbRow_rid : ∀ ρ : Row, rsbRow rid ρ = ρ
  | [] => rfl
  | (l, x) :: r => by rw [rsbRow, rsb_rid x, rsbRow_rid r]
theorem rsbList_rid : ∀ l : List Ty, rsbList rid l = l
  | [] => rfl
  | x :: r => by rw [rsbList, rsb_rid x, rsbList_rid r]
end

mutual
/-- A substitution of type variables only is FSubst.lean's `sb`. -/
theorem rsb_ofF (s : FSub) : ∀ τ : Ty, rsb (ofF s) τ = sb s τ
  | .var _ => rfl
  | .record ρ tl => by rw [rsb, rsbRow_ofF s ρ, ofF_tl, mrg_nil_right]; rfl
  | .fn a b => by rw [rsb, rsb_ofF s a, rsb_ofF s b]; rfl
  | .con as c => by rw [rsb, rsbList_ofF s as]; rfl
theorem rsbRow_ofF (s : FSub) : ∀ ρ : Row, rsbRow (ofF s) ρ = sbRow s ρ
  | [] => rfl
  | (l, x) :: r => by rw [rsbRow, rsb_ofF s x, rsbRow_ofF s r]; rfl
theorem rsbList_ofF (s : FSub) : ∀ l : List Ty, rsbList (ofF s) l = sbList s l
  | [] => rfl
  | x :: r => by rw [rsbList, rsb_ofF s x, rsbList_ofF s r]; rfl
end

mutual
/-- K10 with rows. -/
theorem rsb_rsb (s t : RSub) : ∀ τ : Ty, rsb t (rsb s τ) = rsb (rcomp t s) τ
  | .var _ => rfl
  | .record ρ tl => by
    rw [rsb, rsb, rsb, rcomp_tl]
    simp only [RSub.rx]
    rw [rsbRow_eq t (mrg _ _), ← mrg_mapV, ← rsbRow_eq, ← rsbRow_eq, rsbRow_rsb s t ρ, mrg_assoc]
  | .fn a b => by rw [rsb, rsb, rsb, rsb_rsb s t a, rsb_rsb s t b]
  | .con as c => by rw [rsb, rsb, rsb, rsbList_rsb s t as]
theorem rsbRow_rsb (s t : RSub) : ∀ ρ : Row, rsbRow t (rsbRow s ρ) = rsbRow (rcomp t s) ρ
  | [] => rfl
  | (l, x) :: r => by rw [rsbRow, rsbRow, rsbRow, rsb_rsb s t x, rsbRow_rsb s t r]
theorem rsbList_rsb (s t : RSub) : ∀ l : List Ty, rsbList t (rsbList s l) = rsbList (rcomp t s) l
  | [] => rfl
  | x :: r => by rw [rsbList, rsbList, rsbList, rsb_rsb s t x, rsbList_rsb s t r]
end

theorem rx_rx (s t : RSub) (q : Row × Option RowVar) : t.rx (s.rx q) = (rcomp t s).rx q := by
  have := rsb_rsb s t (.record q.1 q.2)
  simp only [rsb_record, Ty.record.injEq] at this
  exact Prod.ext this.1 this.2

theorem rcomp_assoc (u t s : RSub) : rcomp u (rcomp t s) = rcomp (rcomp u t) s :=
  RSub.eq_of (fun a => rsb_rsb _ _ _) (fun e => rx_rx _ _ _)

theorem rx_rid (s : RSub) (e : RowVar) : s.rx ([], some e) = s.r e := by
  simp only [RSub.rx, rsbRow, mrg_nil_left]; rfl

theorem rcomp_rid (s : RSub) : rcomp s rid = s := RSub.eq_of (fun _ => rfl) (fun e => rx_rid s e)

theorem rid_rcomp (s : RSub) : rcomp rid s = s := by
  refine RSub.eq_of (fun a => rsb_rid _) (fun e => ?_)
  simp only [rcomp, RSub.rx, rsbRow_rid, rid_tl, mrg_nil_right]

/-! ## Variables as types; the image of a variable -/

/-- A variable as a type: a type variable, or the record `⟨∅ | ε⟩`. -/
def vty : BVar → Ty
  | .ty a => .var a
  | .row e => .record [] (some e)

def RSub.img (s : RSub) : BVar → Ty
  | .ty a => s.t a
  | .row e => .record (s.r e).1 (s.r e).2

theorem rsb_vty (s : RSub) : ∀ v, rsb s (vty v) = s.img v
  | .ty _ => rfl
  | .row _ => rfl

theorem img_rcomp (t s : RSub) : ∀ v, (rcomp t s).img v = rsb t (s.img v)
  | .ty _ => rfl
  | .row _ => rfl

theorem img_rid : ∀ v, rid.img v = vty v
  | .ty _ => rfl
  | .row _ => rfl

theorem RSub.eq_of_img {s t : RSub} (h : ∀ v, s.img v = t.img v) : s = t := by
  refine RSub.eq_of (fun a => h (.ty a)) (fun e => ?_)
  have := h (.row e)
  simp only [RSub.img, Ty.record.injEq] at this
  exact Prod.ext this.1 this.2

theorem vars_vty : ∀ v, (vty v).vars = [v]
  | .ty _ => rfl
  | .row _ => rfl

/-! ## The variables of a type and of an image -/

def tailVars : Option RowVar → List BVar
  | none => []
  | some e => [.row e]

theorem vars_record (ρ : Row) (tl : Option RowVar) : (Ty.record ρ tl).vars = Ty.rowVars ρ ++ tailVars tl := by
  cases tl <;> simp [Ty.vars, tailVars]

theorem mem_rowVarsR {v : BVar} : ∀ {ρ : Row}, v ∈ Ty.rowVars ρ ↔ ∃ p ∈ ρ, v ∈ p.2.vars
  | [] => by simp [Ty.rowVars]
  | (l, x) :: r => by
    simp only [Ty.rowVars, List.mem_append, List.mem_cons, mem_rowVarsR (ρ := r)]
    constructor
    · rintro (h | ⟨p, hp, h⟩)
      · exact ⟨(l, x), .inl rfl, h⟩
      · exact ⟨p, .inr hp, h⟩
    · rintro ⟨p, rfl | hp, h⟩
      · exact .inl h
      · exact .inr ⟨p, hp, h⟩

theorem mem_listVarsR {v : BVar} : ∀ {l : List Ty}, v ∈ Ty.listVars l ↔ ∃ τ ∈ l, v ∈ τ.vars
  | [] => by simp [Ty.listVars]
  | x :: r => by
    simp only [Ty.listVars, List.mem_append, List.mem_cons, mem_listVarsR (l := r)]
    constructor
    · rintro (h | ⟨p, hp, h⟩)
      · exact ⟨x, .inl rfl, h⟩
      · exact ⟨p, .inr hp, h⟩
    · rintro ⟨p, rfl | hp, h⟩
      · exact .inl h
      · exact .inr ⟨p, hp, h⟩

theorem rowVars_mrg {v : BVar} {a b : Row} : v ∈ Ty.rowVars (mrg a b) ↔ v ∈ Ty.rowVars a ∨ v ∈ Ty.rowVars b := by
  simp only [mem_rowVarsR, mem_mrg]
  constructor
  · rintro ⟨p, hp | hp, h⟩
    · exact .inl ⟨p, hp, h⟩
    · exact .inr ⟨p, hp, h⟩
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, .inl hp, h⟩
    · exact ⟨p, .inr hp, h⟩

theorem img_row_vars (s : RSub) (e : RowVar) (v : BVar) :
    v ∈ (s.img (.row e)).vars ↔ v ∈ Ty.rowVars (s.r e).1 ∨ v ∈ tailVars (s.r e).2 := by
  simp only [RSub.img, vars_record, List.mem_append]

theorem tl_vars (s : RSub) (tl : Option RowVar) (v : BVar) :
    (v ∈ Ty.rowVars (s.tl tl).1 ∨ v ∈ tailVars (s.tl tl).2) ↔ ∃ w ∈ tailVars tl, v ∈ (s.img w).vars := by
  cases tl with
  | none => simp [RSub.tl, Ty.rowVars, tailVars]
  | some e => simp [RSub.tl, tailVars, img_row_vars]

mutual
theorem mem_vars_rsb (s : RSub) : ∀ (τ : Ty) (v : BVar), v ∈ (rsb s τ).vars ↔ ∃ w ∈ τ.vars, v ∈ (s.img w).vars
  | .var a, v => by simp [rsb, Ty.vars, RSub.img]
  | .record ρ tl, v => by
    rw [rsb, vars_record, vars_record, List.mem_append, rowVars_mrg, or_assoc, tl_vars, mem_vars_rsbRow s ρ v]
    simp only [List.mem_append]
    constructor
    · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
      · exact ⟨w, .inl hw, h⟩
      · exact ⟨w, .inr hw, h⟩
    · rintro ⟨w, hw | hw, h⟩
      · exact .inl ⟨w, hw, h⟩
      · exact .inr ⟨w, hw, h⟩
  | .fn a b, v => by
    simp only [rsb, Ty.vars, List.mem_append, mem_vars_rsb s a v, mem_vars_rsb s b v]
    constructor
    · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
      · exact ⟨w, .inl hw, h⟩
      · exact ⟨w, .inr hw, h⟩
    · rintro ⟨w, hw | hw, h⟩
      · exact .inl ⟨w, hw, h⟩
      · exact .inr ⟨w, hw, h⟩
  | .con as c, v => by simp only [rsb, Ty.vars]; exact mem_vars_rsbList s as v
theorem mem_vars_rsbRow (s : RSub) : ∀ (ρ : Row) (v : BVar),
    v ∈ Ty.rowVars (rsbRow s ρ) ↔ ∃ w ∈ Ty.rowVars ρ, v ∈ (s.img w).vars
  | [], v => by simp [rsbRow, Ty.rowVars]
  | (l, x) :: r, v => by
    simp only [rsbRow, Ty.rowVars, List.mem_append, mem_vars_rsb s x v, mem_vars_rsbRow s r v]
    constructor
    · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
      · exact ⟨w, .inl hw, h⟩
      · exact ⟨w, .inr hw, h⟩
    · rintro ⟨w, hw | hw, h⟩
      · exact .inl ⟨w, hw, h⟩
      · exact .inr ⟨w, hw, h⟩
theorem mem_vars_rsbList (s : RSub) : ∀ (l : List Ty) (v : BVar),
    v ∈ Ty.listVars (rsbList s l) ↔ ∃ w ∈ Ty.listVars l, v ∈ (s.img w).vars
  | [], v => by simp [rsbList, Ty.listVars]
  | x :: r, v => by
    simp only [rsbList, Ty.listVars, List.mem_append, mem_vars_rsb s x v, mem_vars_rsbList s r v]
    constructor
    · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
      · exact ⟨w, .inl hw, h⟩
      · exact ⟨w, .inr hw, h⟩
    · rintro ⟨w, hw | hw, h⟩
      · exact .inl ⟨w, hw, h⟩
      · exact .inr ⟨w, hw, h⟩
end

/-! ## Congruence -/

mutual
theorem rsb_congr {s t : RSub} : ∀ τ : Ty, (∀ w ∈ τ.vars, s.img w = t.img w) → rsb s τ = rsb t τ
  | .var a, h => h (.ty a) (by simp [Ty.vars])
  | .record ρ tl, h => by
    have h1 := rsbRow_congr (s := s) (t := t) ρ fun w hw => h w (by rw [vars_record]; exact List.mem_append_left _ hw)
    have h2 : s.tl tl = t.tl tl := by
      cases tl with
      | none => rfl
      | some e =>
        have := h (.row e) (by rw [vars_record]; simp [tailVars])
        simp only [RSub.img, Ty.record.injEq] at this
        exact Prod.ext this.1 this.2
    rw [rsb, rsb, h1, h2]
  | .fn a b, h => by
    rw [rsb, rsb, rsb_congr a fun w hw => h w (by simp [Ty.vars, hw]),
      rsb_congr b fun w hw => h w (by simp [Ty.vars, hw])]
  | .con as c, h => by rw [rsb, rsb, rsbList_congr as fun w hw => h w (by simpa [Ty.vars] using hw)]
theorem rsbRow_congr {s t : RSub} : ∀ ρ : Row, (∀ w ∈ Ty.rowVars ρ, s.img w = t.img w) → rsbRow s ρ = rsbRow t ρ
  | [], _ => rfl
  | (l, x) :: r, h => by
    rw [rsbRow, rsbRow, rsb_congr x fun w hw => h w (by simp [Ty.rowVars, hw]),
      rsbRow_congr r fun w hw => h w (by simp [Ty.rowVars, hw])]
theorem rsbList_congr {s t : RSub} : ∀ l : List Ty, (∀ w ∈ Ty.listVars l, s.img w = t.img w) →
    rsbList s l = rsbList t l
  | [], _ => rfl
  | x :: r, h => by
    rw [rsbList, rsbList, rsb_congr x fun w hw => h w (by simp [Ty.listVars, hw]),
      rsbList_congr r fun w hw => h w (by simp [Ty.listVars, hw])]
end

theorem rsb_eq_self {s : RSub} {τ : Ty} (h : ∀ w ∈ τ.vars, s.img w = vty w) : rsb s τ = τ := by
  rw [rsb_congr (t := rid) τ fun w hw => by rw [h w hw, img_rid], rsb_rid]

theorem rx_congr {s t : RSub} {q : Row × Option RowVar} (h : ∀ w ∈ (Ty.record q.1 q.2).vars, s.img w = t.img w) :
    s.rx q = t.rx q := by
  have := rsb_congr (s := s) (t := t) (.record q.1 q.2) h
  simp only [rsb_record, Ty.record.injEq] at this
  exact Prod.ext this.1 this.2

/-! ## Sizes and the occurs check through rows (K3) -/

theorem rsize_rsbRow_le (s : RSub) : ∀ (ρ : Row) (l : Lab) (τ : Ty), (l, τ) ∈ ρ → tsize (rsb s τ) ≤ rsize (rsbRow s ρ)
  | [], _, _, h => nomatch h
  | (l', x) :: r, l, τ, h => by
    simp only [rsbRow, rsize]
    rcases List.mem_cons.mp h with h | h
    · cases h; omega
    · have := rsize_rsbRow_le s r l τ h; omega

mutual
theorem size_le_rsb (s : RSub) : ∀ (τ : Ty) (w : BVar), w ∈ τ.vars → tsize (s.img w) ≤ tsize (rsb s τ)
  | .var b, w, hw => by
    simp only [Ty.vars, List.mem_singleton] at hw; subst hw; exact Nat.le_refl _
  | .record ρ tl, w, hw => by
    rw [vars_record, List.mem_append] at hw
    rw [rsb, tsize, rsize_mrg]
    rcases hw with hw | hw
    · have := size_lt_rsbRow s ρ w hw; omega
    · cases tl with
      | none => cases hw
      | some e =>
        simp only [tailVars, List.mem_singleton] at hw; subst hw
        simp only [RSub.img, tsize, RSub.tl]; omega
  | .fn x y, w, hw => by
    simp only [Ty.vars, List.mem_append] at hw
    simp only [rsb, tsize]
    rcases hw with hw | hw
    · have := size_le_rsb s x w hw; omega
    · have := size_le_rsb s y w hw; omega
  | .con as _, w, hw => by
    simp only [Ty.vars] at hw; have := size_lt_rsbList s as w hw; simp only [rsb, tsize]; omega
theorem size_lt_rsbRow (s : RSub) : ∀ (ρ : Row) (w : BVar), w ∈ Ty.rowVars ρ →
    tsize (s.img w) < 1 + rsize (rsbRow s ρ)
  | [], _, hw => by simp [Ty.rowVars] at hw
  | (_, x) :: r, w, hw => by
    simp only [Ty.rowVars, List.mem_append] at hw
    simp only [rsbRow, rsize]
    rcases hw with hw | hw
    · have := size_le_rsb s x w hw; omega
    · have := size_lt_rsbRow s r w hw; omega
theorem size_lt_rsbList (s : RSub) : ∀ (l : List Ty) (w : BVar), w ∈ Ty.listVars l →
    tsize (s.img w) < 1 + lsize (rsbList s l)
  | [], _, hw => by simp [Ty.listVars] at hw
  | x :: r, w, hw => by
    simp only [Ty.listVars, List.mem_append] at hw
    simp only [rsbList, lsize]
    rcases hw with hw | hw
    · have := size_le_rsb s x w hw; omega
    · have := size_lt_rsbList s r w hw; omega
end

/-- The size of an image of a variable is below that of the image of every type it occurs in,
    other than the variable itself. -/
theorem size_lt_rsb (s : RSub) {τ : Ty} {w : BVar} (hw : w ∈ τ.vars) (hne : τ ≠ vty w) :
    tsize (s.img w) < tsize (rsb s τ) := by
  match τ, hw with
  | .var b, hw =>
    simp only [Ty.vars, List.mem_singleton] at hw; subst hw; exact absurd rfl hne
  | .record ρ tl, hw =>
    rw [vars_record, List.mem_append] at hw
    rw [rsb, tsize, rsize_mrg]
    rcases hw with hw | hw
    · have := size_lt_rsbRow s ρ w hw; omega
    · cases tl with
      | none => cases hw
      | some e =>
        simp only [tailVars, List.mem_singleton] at hw; subst hw
        have hρ : ρ ≠ [] := fun h => hne (by rw [h]; rfl)
        obtain ⟨⟨l, x⟩, r, rfl⟩ := List.exists_cons_of_ne_nil hρ
        have := tsize_pos (rsb s x)
        simp only [RSub.img, tsize, RSub.tl, rsbRow, rsize]; omega
  | .fn x y, hw =>
    simp only [Ty.vars, List.mem_append] at hw
    simp only [rsb, tsize]
    rcases hw with hw | hw
    · have := size_le_rsb s x w hw; omega
    · have := size_le_rsb s y w hw; omega
  | .con as _, hw =>
    simp only [Ty.vars] at hw; have := size_lt_rsbList s as w hw; simp only [rsb, tsize]; omega

/-- K3 with rows: a variable never equals, under any substitution, a proper type it occurs in. -/
theorem occurs_neR (s : RSub) {τ : Ty} {w : BVar} (hw : w ∈ τ.vars) (hne : τ ≠ vty w) :
    s.img w ≠ rsb s τ := fun e => by
  have := size_lt_rsb s hw hne; rw [e] at this; exact Nat.lt_irrefl _ this

/-! ## Canonical types (A23, K9) -/

/-! `cnB` (every row strictly sorted) is in Objects.lean. -/

theorem cnRowB_iff : ∀ {ρ : Row}, cnRowB ρ = true ↔ ∀ p ∈ ρ, cnB p.2 = true
  | [] => by simp [cnRowB]
  | (l, x) :: r => by
    simp only [cnRowB, Bool.and_eq_true, cnRowB_iff (ρ := r), List.mem_cons, forall_eq_or_imp]

theorem cnListB_iff : ∀ {l : List Ty}, cnListB l = true ↔ ∀ τ ∈ l, cnB τ = true
  | [] => by simp [cnListB]
  | x :: r => by
    simp only [cnListB, Bool.and_eq_true, cnListB_iff (l := r), List.mem_cons, forall_eq_or_imp]

theorem cnB_record {ρ : Row} {tl : Option RowVar} :
    cnB (.record ρ tl) = true ↔ Sorted ρ ∧ ∀ p ∈ ρ, cnB p.2 = true := by
  simp only [cnB, Bool.and_eq_true, rowSorted_iff, cnRowB_iff]

theorem cnB_vty : ∀ v, cnB (vty v) = true
  | .ty _ => rfl
  | .row _ => rfl

/-- The image of a record is canonical iff the merged row is sorted and its fields canonical. -/
theorem cnB_rsb_record {s : RSub} {ρ : Row} {tl : Option RowVar} :
    cnB (rsb s (.record ρ tl)) = true ↔
      Sorted (mrg (rsbRow s ρ) (s.tl tl).1) ∧ (∀ p ∈ ρ, cnB (rsb s p.2) = true) ∧
        ∀ p ∈ (s.tl tl).1, cnB p.2 = true := by
  rw [rsb, cnB_record]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun p hp => ?_, fun p hp => h2 p (mem_mrg.mpr (.inr hp))⟩
    exact h2 (p.1, rsb s p.2) (mem_mrg.mpr (.inl (mem_rsbRow.mpr ⟨p, hp, rfl⟩)))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun p hp => ?_⟩
    rcases mem_mrg.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := mem_rsbRow.mp hp; exact h2 q hq
    · exact h3 p hp

mutual
/-- `lacks_τ(e)`: the labels of the rows that `e` extends in `τ`. -/
def lacksOf (e : RowVar) : Ty → List Lab
  | .var _ => []
  | .record ρ tl => (if tl = some e then labs ρ else []) ++ lacksRow e ρ
  | .fn a b => lacksOf e a ++ lacksOf e b
  | .con as _ => lacksList e as
def lacksRow (e : RowVar) : Row → List Lab
  | [] => []
  | (_, τ) :: rest => lacksOf e τ ++ lacksRow e rest
def lacksList (e : RowVar) : List Ty → List Lab
  | [] => []
  | τ :: rest => lacksOf e τ ++ lacksList e rest
end

theorem mem_lacksRow {e : RowVar} {l : Lab} : ∀ {ρ : Row}, l ∈ lacksRow e ρ ↔ ∃ p ∈ ρ, l ∈ lacksOf e p.2
  | [] => by simp [lacksRow]
  | (l', x) :: r => by
    simp only [lacksRow, List.mem_append, mem_lacksRow (ρ := r), List.mem_cons, exists_eq_or_imp]

theorem mem_lacksList {e : RowVar} {l : Lab} : ∀ {ts : List Ty}, l ∈ lacksList e ts ↔ ∃ τ ∈ ts, l ∈ lacksOf e τ
  | [] => by simp [lacksList]
  | x :: r => by
    simp only [lacksList, List.mem_append, mem_lacksList (ts := r), List.mem_cons, exists_eq_or_imp]

mutual
/-- K9, one direction: a canonical image has every row `e` extends disjoint from the row of `s e`. -/
theorem lacks_of_cn {s : RSub} {e : RowVar} {l : Lab} : ∀ {τ : Ty}, cnB (rsb s τ) = true →
    l ∈ lacksOf e τ → l ∉ labs (s.r e).1
  | .var _, _, h => by simp [lacksOf] at h
  | .record ρ tl, hc, h => by
    obtain ⟨h1, h2, _⟩ := cnB_rsb_record.mp hc
    simp only [lacksOf, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i htl; subst htl
        obtain ⟨-, -, hd⟩ := sorted_of_mrg h1
        intro hl
        obtain ⟨τ1, hm1⟩ := mem_labs.mp h
        obtain ⟨τ2, hm2⟩ := mem_labs.mp hl
        exact hd _ (mem_rsbRow.mpr ⟨_, hm1, rfl⟩) _ hm2 rfl
      · cases h
    · exact lacks_of_cnRow h2 h
  | .fn a b, hc, h => by
    simp only [rsb, cnB, Bool.and_eq_true] at hc
    simp only [lacksOf, List.mem_append] at h
    rcases h with h | h
    · exact lacks_of_cn hc.1 h
    · exact lacks_of_cn hc.2 h
  | .con as _, hc, h => by
    simp only [rsb, cnB, cnListB_iff, rsbList_eq, List.mem_map] at hc
    simp only [lacksOf] at h
    exact lacks_of_cnList (fun τ hτ => hc _ ⟨τ, hτ, rfl⟩) h
theorem lacks_of_cnRow {s : RSub} {e : RowVar} {l : Lab} : ∀ {ρ : Row}, (∀ p ∈ ρ, cnB (rsb s p.2) = true) →
    l ∈ lacksRow e ρ → l ∉ labs (s.r e).1
  | [], _, h => by simp [lacksRow] at h
  | (l', x) :: r, hc, h => by
    simp only [lacksRow, List.mem_append] at h
    rcases h with h | h
    · exact lacks_of_cn (hc (l', x) (List.mem_cons_self ..)) h
    · exact lacks_of_cnRow (fun p hp => hc p (List.mem_cons_of_mem _ hp)) h
theorem lacks_of_cnList {s : RSub} {e : RowVar} {l : Lab} : ∀ {ts : List Ty}, (∀ τ ∈ ts, cnB (rsb s τ) = true) →
    l ∈ lacksList e ts → l ∉ labs (s.r e).1
  | [], _, h => by simp [lacksList] at h
  | x :: r, hc, h => by
    simp only [lacksList, List.mem_append] at h
    rcases h with h | h
    · exact lacks_of_cn (hc x (List.mem_cons_self ..)) h
    · exact lacks_of_cnList (fun p hp => hc p (List.mem_cons_of_mem _ hp)) h
end

mutual
/-- K9, the other direction: a canonical type, canonical images of its variables and the lacks
    condition give a canonical image. -/
theorem cn_rsb {s : RSub} : ∀ {τ : Ty}, cnB τ = true → (∀ w ∈ τ.vars, cnB (s.img w) = true) →
    (∀ e l, l ∈ lacksOf e τ → l ∉ labs (s.r e).1) → cnB (rsb s τ) = true
  | .var a, _, hv, _ => hv (.ty a) (by simp [Ty.vars])
  | .record ρ tl, hc, hv, hl => by
    have hs : Sorted ρ := (cnB_record.mp hc).1
    have hf : cnRowB ρ = true := by simp only [cnB, Bool.and_eq_true] at hc; exact hc.2
    have htl : Sorted (s.tl tl).1 ∧ ∀ p ∈ (s.tl tl).1, cnB p.2 = true := by
      cases tl with
      | none => exact ⟨sorted_nil, fun _ h => nomatch h⟩
      | some e =>
        have := hv (.row e) (by rw [vars_record]; simp [tailVars])
        simp only [RSub.img] at this
        exact cnB_record.mp this
    refine cnB_rsb_record.mpr ⟨sorted_mrg ((sorted_rsbRow_iff s).mpr hs) htl.1 ?_, ?_, htl.2⟩
    · intro x hx y hy hxy
      cases tl with
      | none => cases hy
      | some e =>
        obtain ⟨p, hp, rfl⟩ := mem_rsbRow.mp hx
        apply hl e p.1 (by simp only [lacksOf, if_pos rfl, List.mem_append]; exact .inl (mem_labs.mpr ⟨p.2, hp⟩))
        rw [hxy]; exact mem_labs.mpr ⟨y.2, hy⟩
    · exact cn_rsbRow hf (fun w hw => hv w (by rw [vars_record]; exact List.mem_append_left _ hw))
        (fun e l h => hl e l (by simp only [lacksOf, List.mem_append]; exact .inr h))
  | .fn a b, hc, hv, hl => by
    simp only [cnB, Bool.and_eq_true] at hc
    simp only [rsb, cnB, Bool.and_eq_true]
    exact ⟨cn_rsb hc.1 (fun w hw => hv w (by simp [Ty.vars, hw])) (fun e l h => hl e l (by simp [lacksOf, h])),
      cn_rsb hc.2 (fun w hw => hv w (by simp [Ty.vars, hw])) (fun e l h => hl e l (by simp [lacksOf, h]))⟩
  | .con as _, hc, hv, hl => by
    simp only [cnB] at hc
    simp only [rsb, cnB]
    exact cn_rsbList hc (fun w hw => hv w (by simpa [Ty.vars] using hw)) (fun e l h => hl e l (by simpa [lacksOf] using h))
theorem cn_rsbRow {s : RSub} : ∀ {ρ : Row}, cnRowB ρ = true → (∀ w ∈ Ty.rowVars ρ, cnB (s.img w) = true) →
    (∀ e l, l ∈ lacksRow e ρ → l ∉ labs (s.r e).1) → ∀ p ∈ ρ, cnB (rsb s p.2) = true
  | [], _, _, _, _, hp => nomatch hp
  | (l', x) :: r, hc, hv, hl, p, hp => by
    simp only [cnRowB, Bool.and_eq_true] at hc
    rcases List.mem_cons.mp hp with rfl | hp
    · exact cn_rsb hc.1 (fun w hw => hv w (by simp [Ty.rowVars, hw])) (fun e l h => hl e l (by simp [lacksRow, h]))
    · exact cn_rsbRow hc.2 (fun w hw => hv w (by simp [Ty.rowVars, hw])) (fun e l h => hl e l (by simp [lacksRow, h])) p hp
theorem cn_rsbList {s : RSub} : ∀ {ts : List Ty}, cnListB ts = true → (∀ w ∈ Ty.listVars ts, cnB (s.img w) = true) →
    (∀ e l, l ∈ lacksList e ts → l ∉ labs (s.r e).1) → cnListB (rsbList s ts) = true
  | [], _, _, _ => rfl
  | x :: r, hc, hv, hl => by
    simp only [cnListB, Bool.and_eq_true] at hc
    simp only [rsbList, cnListB, Bool.and_eq_true]
    exact ⟨cn_rsb hc.1 (fun w hw => hv w (by simp [Ty.listVars, hw])) (fun e l h => hl e l (by simp [lacksList, h])),
      cn_rsbList hc.2 (fun w hw => hv w (by simp [Ty.listVars, hw])) (fun e l h => hl e l (by simp [lacksList, h]))⟩
end

/-- A field of a canonical image has a canonical image. -/
theorem cn_field {s : RSub} {ρ : Row} {tl : Option RowVar} (h : cnB (rsb s (.record ρ tl)) = true)
    {p : Lab × Ty} (hp : p ∈ ρ) : cnB (rsb s p.2) = true :=
  (cnB_rsb_record.mp h).2.1 p hp

/-! ## Classes (K5, K11) -/

/-- `s` respects classes. -/
def RespR (s : RSub) : Prop := ∀ a, Adm a.cls (s.t a)

theorem respR_rid : RespR rid := fun a => admC_self a

mutual
theorem reqC_specR (s : RSub) : ∀ (k : Cls) (τ : Ty) (ps : List (TyVar × Cls)), reqC k τ = some ps →
    (Adm k (rsb s τ) ↔ ∀ p ∈ ps, Adm p.2 (s.t p.1))
  | .any, τ, ps, h => by
    simp only [reqC, Option.some.injEq] at h; subst h
    exact ⟨fun _ _ hp => absurd hp List.not_mem_nil, fun _ => Adm.any _⟩
  | .num, .var a, ps, h | .comp, .var a, ps, h | .app, .var a, ps, h | .capp, .var a, ps, h => by
    simp only [reqC, Option.some.injEq] at h; subst h
    simp [rsb]
  | .num, .fn _ _, _, h | .comp, .fn _ _, _, h | .app, .fn _ _, _, h | .capp, .fn _ _, _, h => by
    simp [reqC] at h
  | .num, .record _ _, _, h | .comp, .record _ _, _, h | .app, .record _ _, _, h
  | .capp, .record _ _, _, h => by simp [reqC] at h
  | .num, .con as t, ps, h | .comp, .con as t, ps, h | .app, .con as t, ps, h
  | .capp, .con as t, ps, h => by
    simp only [reqC] at h
    split at h
    · rename_i ks hks
      simp only [rsb]
      rw [admC_con_iff (by decide)]
      constructor
      · rintro ⟨ks', hks', hz⟩
        rw [hks] at hks'; cases hks'
        exact (reqL_specR s ks as ps h).mp hz
      · intro hp
        exact ⟨ks, hks, (reqL_specR s ks as ps h).mpr hp⟩
    · cases h
theorem reqL_specR (s : RSub) : ∀ (ks : List Cls) (as : List Ty) (ps : List (TyVar × Cls)), reqL ks as = some ps →
    (ZipAdmC (rsbList s as) ks ↔ ∀ p ∈ ps, Adm p.2 (s.t p.1))
  | [], [], ps, h => by
    simp only [reqL, Option.some.injEq] at h; subst h
    simp [rsbList, ZipAdmC]
  | k :: ks, τ :: ts, ps, h => by
    simp only [reqL] at h
    split at h
    · rename_i a b ha hb
      simp only [Option.some.injEq] at h; subst h
      simp only [rsbList, ZipAdmC, List.mem_append]
      rw [reqC_specR s k τ a ha, reqL_specR s ks ts b hb]
      exact ⟨fun ⟨h1, h2⟩ p hp => hp.elim (h1 p) (h2 p), fun h => ⟨fun p hp => h p (.inl hp), fun p hp => h p (.inr hp)⟩⟩
    · cases h
  | [], _ :: _, _, h => by simp [reqL] at h
  | _ :: _, [], _, h => by simp [reqL] at h
end

mutual
theorem reqC_noneR (s : RSub) : ∀ (k : Cls) (τ : Ty), reqC k τ = none → ¬ Adm k (rsb s τ)
  | .any, _, h => by simp [reqC] at h
  | .num, .var _, h | .comp, .var _, h | .app, .var _, h | .capp, .var _, h => by simp [reqC] at h
  | .num, .fn _ _, _ | .comp, .fn _ _, _ | .app, .fn _ _, _ | .capp, .fn _ _, _ => by
    simp only [rsb, admC_fn_iff]; decide
  | .num, .record _ _, _ | .comp, .record _ _, _ | .app, .record _ _, _ | .capp, .record _ _, _ => by
    simp only [rsb, admC_record_iff]; decide
  | .num, .con as t, h | .comp, .con as t, h | .app, .con as t, h | .capp, .con as t, h => by
    simp only [reqC] at h
    simp only [rsb]
    rw [admC_con_iff (by decide)]
    rintro ⟨ks, hks, hz⟩
    rw [hks] at h
    exact reqL_noneR s ks as h hz
theorem reqL_noneR (s : RSub) : ∀ (ks : List Cls) (as : List Ty), reqL ks as = none → ¬ ZipAdmC (rsbList s as) ks
  | [], [], h => by simp [reqL] at h
  | k :: ks, τ :: ts, h => by
    simp only [rsbList, ZipAdmC]
    rintro ⟨h1, h2⟩
    simp only [reqL] at h
    cases ha : reqC k τ with
    | none => exact reqC_noneR s k τ ha h1
    | some a =>
      cases hb : reqL ks ts with
      | none => exact reqL_noneR s ks ts hb h2
      | some b => rw [ha, hb] at h; cases h
  | [], _ :: _, _ => by simp [rsbList, ZipAdmC]
  | _ :: _, [], _ => by simp [rsbList, ZipAdmC]
end

/-- K11: admissibility is stable under a substitution respecting classes. -/
theorem admR_rsb {s : RSub} (hs : RespR s) {k : Cls} {τ : Ty} (h : Adm k τ) : Adm k (rsb s τ) := by
  cases hr : reqC k τ with
  | none =>
    exfalso; apply reqC_noneR rid k τ hr; rw [rsb_rid]; exact h
  | some ps =>
    rw [reqC_specR s k τ ps hr]
    have h' := (reqC_specR rid k τ ps hr).mp (by rw [rsb_rid]; exact h)
    intro p hp
    have hv := h' p hp
    obtain ⟨b, c⟩ := p
    have := admC_var_iff.mp hv
    exact adm_mono this (hs b)

theorem respR_rcomp {s t : RSub} (hs : RespR s) (ht : RespR t) : RespR (rcomp t s) := fun a => admR_rsb ht (hs a)

/-! ## Binding lists -/

/-- Bindings of type variables (to types) and row variables (to record types). -/
abbrev RBnd := List (BVar × Ty)

/-- The row and tail of a record type. -/
def rowOf : Ty → Row × Option RowVar
  | .record ρ tl => (ρ, tl)
  | _ => ([], none)

def toRS (θ : RBnd) : RSub :=
  ⟨fun a => (FMap.find? θ (.ty a)).getD (.var a),
   fun e => match FMap.find? θ (.row e) with
     | some τ => rowOf τ
     | none => ([], some e)⟩

/-- A binding list whose row variables are bound to record types. -/
def RowRec (θ : RBnd) : Prop := ∀ p ∈ θ, ∀ e, p.1 = .row e → ∃ ρ tl, p.2 = .record ρ tl

/-- The image of a variable is the type it is bound to. -/
def IsRec : BVar → Ty → Prop
  | .ty _, _ => True
  | .row _, τ => ∃ ρ tl, τ = .record ρ tl

theorem rfind?_mem {θ : RBnd} {v : BVar} {τ : Ty} : FMap.find? θ v = some τ → (v, τ) ∈ θ := by
  induction θ with
  | nil => intro h; cases h
  | cons p θ ih =>
    obtain ⟨k, x⟩ := p
    simp only [FMap.find?]
    split
    · rename_i hk; intro h; cases h; subst hk; exact List.mem_cons_self ..
    · intro h; exact List.mem_cons_of_mem _ (ih h)

theorem img_toRS {θ : RBnd} (hθ : RowRec θ) (v : BVar) : (toRS θ).img v = (FMap.find? θ v).getD (vty v) := by
  cases v with
  | ty a => rfl
  | row e =>
    simp only [RSub.img, toRS]
    cases hf : FMap.find? θ (.row e) with
    | none => rfl
    | some τ =>
      obtain ⟨ρ, tl, rfl⟩ := hθ _ (rfind?_mem hf) e rfl
      rfl

/-- The substitution of one variable. -/
def one (v : BVar) (σ : Ty) : RSub := toRS [(v, σ)]

theorem img_one_self {v : BVar} {σ : Ty} (h : IsRec v σ) : (one v σ).img v = σ := by
  cases v with
  | ty a => simp [one, toRS, RSub.img, FMap.find?]
  | row e =>
    obtain ⟨ρ, tl, rfl⟩ := h
    simp [one, toRS, RSub.img, FMap.find?, rowOf]

theorem img_one_ne {v w : BVar} (σ : Ty) (h : w ≠ v) : (one v σ).img w = vty w := by
  have hv : v ≠ w := fun e => h e.symm
  cases w with
  | ty a => simp [one, toRS, RSub.img, FMap.find?, hv, vty]
  | row e => simp [one, toRS, RSub.img, FMap.find?, hv, vty]

/-- Bind `v ↦ σ` on top of `θ`. -/
def bindR (v : BVar) (σ : Ty) (θ : RBnd) : RBnd := (v, σ) :: θ.map fun p => (p.1, rsb (one v σ) p.2)

theorem rsb_isRec {s : RSub} {ρ : Row} {tl : Option RowVar} : ∃ ρ' tl', rsb s (.record ρ tl) = .record ρ' tl' :=
  ⟨_, _, rfl⟩

theorem rowRec_bindR {v : BVar} {σ : Ty} {θ : RBnd} (hθ : RowRec θ) (hσ : IsRec v σ) : RowRec (bindR v σ θ) := by
  intro p hp e he
  rcases List.mem_cons.mp hp with rfl | hp
  · simp only at he; subst he; exact hσ
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨ρ, tl, h⟩ := hθ q hq e he
    simp only [h]; exact rsb_isRec

theorem find?_bindR (v : BVar) (σ : Ty) (θ : RBnd) (w : BVar) :
    FMap.find? (bindR v σ θ) w = if v = w then some σ else (FMap.find? θ w).map (rsb (one v σ)) := by
  simp only [bindR, FMap.find?]
  split
  · rfl
  · exact find?_mapSnd _ w θ

/-- A binding of an unbound variable composes. -/
theorem toRS_bindR {v : BVar} {σ : Ty} {θ : RBnd} (hθ : RowRec θ) (hσ : IsRec v σ)
    (hv : (toRS θ).img v = vty v) : toRS (bindR v σ θ) = rcomp (one v σ) (toRS θ) := by
  refine RSub.eq_of_img fun w => ?_
  rw [img_toRS (rowRec_bindR hθ hσ), img_rcomp, find?_bindR]
  by_cases hw : v = w
  · subst hw; rw [if_pos rfl, hv, rsb_vty, img_one_self hσ]; rfl
  · rw [if_neg hw, img_toRS hθ]
    cases hf : FMap.find? θ w with
    | none => simp only [Option.map_none, Option.getD_none]; rw [rsb_vty, img_one_ne σ (fun e => hw e.symm)]
    | some τ => rfl

end StandardElm.Stat.Complete
