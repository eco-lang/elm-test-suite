/-
  A Standard Definition of Elm? Mechanisation: the terms of the constraint language, plan step 11,
  milestone (a).

  A term is a type of Chapter 4 with *metavariables*: `meta q` stands for a type a derivation
  chooses at the node (or instance position) reached by the path `q` of the annotated module.
  The other type variables of a term are constants (rigid). A term has no flexible row variable:
  an open record whose extension a derivation chooses is a metavariable with `has` constraints
  (Unify.lean), so that the meaning of a constraint never depends on how step 9's substitution
  merges rows (deviation from the specification, recorded in Core.lean).

  A valuation `ν : Path → Ty` gives each metavariable a type; `T.ev ν` evaluates a term.
  `hN` is the normalisation the valuation read off a derivation applies (Core.lean): the record
  `{ | a }` of a named row variable alone is identified with the type variable `a`, so that the
  two sorts an annotation's variable may take in a derivation (r:s-ty-tyvar, r:s-ty-rowvar) give
  the same term.
-/
import StandardElmMech.Stat.Annotated

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

abbrev Path := List Nat

inductive T where
  | mv (q : Path)
  | var (a : TyVar)
  | record (row : List (Lab × T)) (tail : Option RowVar)
  | fn (a b : T)
  | con (args : List T) (t : TyName)
  deriving Repr, Inhabited

abbrev Val := Path → Ty

/-! ## Evaluation -/

mutual
def T.ev (ν : Val) : T → Ty
  | .mv q => ν q
  | .var a => .var a
  | .record ρ tl => .record (T.evRow ν ρ) tl
  | .fn a b => .fn (T.ev ν a) (T.ev ν b)
  | .con as t => .con (T.evList ν as) t
def T.evRow (ν : Val) : List (Lab × T) → Row
  | [] => []
  | (l, x) :: r => (l, T.ev ν x) :: T.evRow ν r
def T.evList (ν : Val) : List T → List Ty
  | [] => []
  | x :: r => T.ev ν x :: T.evList ν r
end

theorem T.evList_eq (ν : Val) : ∀ l : List T, T.evList ν l = l.map (T.ev ν)
  | [] => rfl
  | x :: r => by simp [T.evList, T.evList_eq ν r]

theorem T.evRow_eq (ν : Val) : ∀ l : List (Lab × T), T.evRow ν l = l.map (fun p => (p.1, T.ev ν p.2))
  | [] => rfl
  | (l, x) :: r => by simp [T.evRow, T.evRow_eq ν r]

/-! ## Embedding types -/

mutual
def ofTy : Ty → T
  | .var a => .var a
  | .record ρ tl => .record (ofRow ρ) tl
  | .fn a b => .fn (ofTy a) (ofTy b)
  | .con as t => .con (ofList as) t
def ofRow : Row → List (Lab × T)
  | [] => []
  | (l, x) :: r => (l, ofTy x) :: ofRow r
def ofList : List Ty → List T
  | [] => []
  | x :: r => ofTy x :: ofList r
end

mutual
theorem ev_ofTy (ν : Val) : ∀ τ : Ty, (ofTy τ).ev ν = τ
  | .var a => rfl
  | .record ρ tl => by simp only [ofTy, T.ev, ev_ofRow ν ρ]
  | .fn a b => by simp only [ofTy, T.ev, ev_ofTy ν a, ev_ofTy ν b]
  | .con as t => by simp only [ofTy, T.ev, ev_ofList ν as]
theorem ev_ofRow (ν : Val) : ∀ ρ : Row, T.evRow ν (ofRow ρ) = ρ
  | [] => rfl
  | (l, x) :: r => by simp only [ofRow, T.evRow, ev_ofTy ν x, ev_ofRow ν r]
theorem ev_ofList (ν : Val) : ∀ l : List Ty, T.evList ν (ofList l) = l
  | [] => rfl
  | x :: r => by simp only [ofList, T.evList, ev_ofTy ν x, ev_ofList ν r]
end

/-! ## Closed terms -/

mutual
/-- No metavariable and no type or row variable. -/
def T.closed : T → Bool
  | .mv _ => false
  | .var _ => false
  | .record ρ tl => tl.isNone && T.closedRow ρ
  | .fn a b => T.closed a && T.closed b
  | .con as _ => T.closedList as
def T.closedRow : List (Lab × T) → Bool
  | [] => true
  | (_, x) :: r => T.closed x && T.closedRow r
def T.closedList : List T → Bool
  | [] => true
  | x :: r => T.closed x && T.closedList r
end

mutual
theorem closed_vars (ν : Val) : ∀ t : T, t.closed = true → (t.ev ν).vars = []
  | .mv _, h => by simp [T.closed] at h
  | .var _, h => by simp [T.closed] at h
  | .record ρ tl, h => by
    simp only [T.closed, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨rfl, h⟩ := h
    simp only [T.ev, Ty.vars, closedRow_vars ν ρ h]
  | .fn a b, h => by
    simp only [T.closed, Bool.and_eq_true] at h
    simp only [T.ev, Ty.vars, closed_vars ν a h.1, closed_vars ν b h.2, List.append_nil]
  | .con as _, h => by
    simp only [T.closed] at h
    simp only [T.ev, Ty.vars, closedList_vars ν as h]
theorem closedRow_vars (ν : Val) : ∀ ρ : List (Lab × T), T.closedRow ρ = true → Ty.rowVars (T.evRow ν ρ) = []
  | [], _ => rfl
  | (_, x) :: r, h => by
    simp only [T.closedRow, Bool.and_eq_true] at h
    simp only [T.evRow, Ty.rowVars, closed_vars ν x h.1, closedRow_vars ν r h.2, List.append_nil]
theorem closedList_vars (ν : Val) : ∀ l : List T, T.closedList l = true → Ty.listVars (T.evList ν l) = []
  | [], _ => rfl
  | x :: r, h => by
    simp only [T.closedList, Bool.and_eq_true] at h
    simp only [T.evList, Ty.listVars, closed_vars ν x h.1, closedList_vars ν r h.2, List.append_nil]
end

/-! ## Metavariables: occurrence and substitution -/

mutual
def T.occ (q : Path) : T → Bool
  | .mv q' => q' == q
  | .var _ => false
  | .record ρ _ => T.occRow q ρ
  | .fn a b => T.occ q a || T.occ q b
  | .con as _ => T.occList q as
def T.occRow (q : Path) : List (Lab × T) → Bool
  | [] => false
  | (_, x) :: r => T.occ q x || T.occRow q r
def T.occList (q : Path) : List T → Bool
  | [] => false
  | x :: r => T.occ q x || T.occList q r
end

mutual
/-- t{s/q}. -/
def T.subst (q : Path) (s : T) : T → T
  | .mv q' => if q' = q then s else .mv q'
  | .var a => .var a
  | .record ρ tl => .record (T.substRow q s ρ) tl
  | .fn a b => .fn (T.subst q s a) (T.subst q s b)
  | .con as t => .con (T.substList q s as) t
def T.substRow (q : Path) (s : T) : List (Lab × T) → List (Lab × T)
  | [] => []
  | (l, x) :: r => (l, T.subst q s x) :: T.substRow q s r
def T.substList (q : Path) (s : T) : List T → List T
  | [] => []
  | x :: r => T.subst q s x :: T.substList q s r
end

section subst
variable {ν : Val} {q : Path} {s : T}

mutual
theorem ev_subst (h : ν q = s.ev ν) : ∀ t : T, (T.subst q s t).ev ν = t.ev ν
  | .mv q' => by
    simp only [T.subst]
    split
    · rename_i e; subst e; exact h.symm
    · rfl
  | .var a => rfl
  | .record ρ tl => by simp only [T.subst, T.ev, evRow_subst h ρ]
  | .fn a b => by simp only [T.subst, T.ev, ev_subst h a, ev_subst h b]
  | .con as t => by simp only [T.subst, T.ev, evList_subst h as]
theorem evRow_subst (h : ν q = s.ev ν) : ∀ ρ : List (Lab × T), T.evRow ν (T.substRow q s ρ) = T.evRow ν ρ
  | [] => rfl
  | (l, x) :: r => by simp only [T.substRow, T.evRow, ev_subst h x, evRow_subst h r]
theorem evList_subst (h : ν q = s.ev ν) : ∀ l : List T, T.evList ν (T.substList q s l) = T.evList ν l
  | [] => rfl
  | x :: r => by simp only [T.substList, T.evList, ev_subst h x, evList_subst h r]
end

end subst

/-! ## Sizes, and the occurs check (K3) -/

mutual
def tySize : Ty → Nat
  | .var _ => 1
  | .record ρ _ => 1 + rowSize ρ
  | .fn a b => 1 + tySize a + tySize b
  | .con as _ => 1 + listSize as
def rowSize : Row → Nat
  | [] => 0
  | (_, x) :: r => tySize x + rowSize r
def listSize : List Ty → Nat
  | [] => 0
  | x :: r => tySize x + listSize r
end

mutual
theorem occ_size (ν : Val) (q : Path) : ∀ t : T, t.occ q = true → tySize (ν q) ≤ tySize (t.ev ν)
  | .mv q', h => by
    simp only [T.occ, beq_iff_eq] at h; subst h; exact Nat.le_refl _
  | .var _, h => by simp [T.occ] at h
  | .record ρ _, h => by
    simp only [T.occ] at h
    have := occRow_size ν q ρ h
    simp only [T.ev, tySize]; omega
  | .fn a b, h => by
    simp only [T.occ, Bool.or_eq_true] at h
    simp only [T.ev, tySize]
    rcases h with h | h
    · have := occ_size ν q a h; omega
    · have := occ_size ν q b h; omega
  | .con as _, h => by
    simp only [T.occ] at h
    have := occList_size ν q as h
    simp only [T.ev, tySize]; omega
theorem occRow_size (ν : Val) (q : Path) : ∀ ρ : List (Lab × T), T.occRow q ρ = true →
    tySize (ν q) < 1 + rowSize (T.evRow ν ρ)
  | [], h => by simp [T.occRow] at h
  | (_, x) :: r, h => by
    simp only [T.occRow, Bool.or_eq_true] at h
    simp only [T.evRow, rowSize]
    rcases h with h | h
    · have := occ_size ν q x h; omega
    · have := occRow_size ν q r h; omega
theorem occList_size (ν : Val) (q : Path) : ∀ l : List T, T.occList q l = true →
    tySize (ν q) < 1 + listSize (T.evList ν l)
  | [], h => by simp [T.occList] at h
  | x :: r, h => by
    simp only [T.occList, Bool.or_eq_true] at h
    simp only [T.evList, listSize]
    rcases h with h | h
    · have := occ_size ν q x h; omega
    · have := occList_size ν q r h; omega
end

/-- K3: a metavariable never equals a proper term it occurs in. -/
theorem occurs_ne (ν : Val) (q : Path) (t : T) (h : t.occ q = true) (hm : ∀ q', t ≠ .mv q') :
    ν q ≠ t.ev ν := by
  intro e
  have hs : tySize (ν q) < tySize (t.ev ν) := by
    match t, h with
    | .mv q', _ => exact absurd rfl (hm q')
    | .var _, h => simp [T.occ] at h
    | .record ρ _, h => simp only [T.occ] at h; have := occRow_size ν q ρ h; simp only [T.ev, tySize]; omega
    | .fn a b, h =>
      simp only [T.occ, Bool.or_eq_true] at h
      simp only [T.ev, tySize]
      rcases h with h | h
      · have := occ_size ν q a h; omega
      · have := occ_size ν q b h; omega
    | .con as _, h => simp only [T.occ] at h; have := occList_size ν q as h; simp only [T.ev, tySize]; omega
  rw [e] at hs
  exact Nat.lt_irrefl _ hs

/-! ## The normalisation of a derivation's types -/

/-- The id every type name outside the initial basis's collapses to (RefuseTypes.lean's `Did`): a
    derivation chooses the names of a module's custom types, so the valuation forgets them. -/
def DidC : Nat := 1000

def gN (t : TyName) : TyName := if t ∈ T0 then t else ⟨DidC, t.arity⟩

theorem gN_of_mem {t : TyName} (h : t ∈ T0) : gN t = t := by simp [gN, h]

theorem gN_gN (t : TyName) : gN (gN t) = gN t := by
  unfold gN
  by_cases h : t ∈ T0
  · simp [h]
  · have : (⟨DidC, t.arity⟩ : TyName) ∉ T0 := by
      intro hm; simp [T0, DidC, tInt, tFloat, tChar, tString, tUnit, tList, tTuple2, tTuple3, tBool, tOrder,
        tNever, tMaybe, tResult, tArray, tBytes, tValue, tCmd, tSub, tTask, tProcessId, tProgram, tNode] at hm
    simp [h, this]

theorem gN_tInt : gN tInt = tInt := gN_of_mem (by decide)
theorem gN_tFloat : gN tFloat = tFloat := gN_of_mem (by decide)
theorem gN_tChar : gN tChar = tChar := gN_of_mem (by decide)
theorem gN_tString : gN tString = tString := gN_of_mem (by decide)
theorem gN_tUnit : gN tUnit = tUnit := gN_of_mem (by decide)
theorem gN_tList : gN tList = tList := gN_of_mem (by decide)
theorem gN_tTuple2 : gN tTuple2 = tTuple2 := gN_of_mem (by decide)
theorem gN_tTuple3 : gN tTuple3 = tTuple3 := gN_of_mem (by decide)

/-- `{ | a }` for a named row variable `a` alone is `a`. -/
def hRec (ρ : Row) (tl : Option RowVar) : Ty :=
  match tl with
  | none => .record ρ none
  | some (.named s) =>
    match ρ with
    | [] => .var (.named s)
    | f :: r => .record (f :: r) (some (.named s))
  | some (.fresh n) => .record ρ (some (.fresh n))
  | some (.bnd i) => .record ρ (some (.bnd i))

mutual
def hN : Ty → Ty
  | .var a => .var a
  | .record ρ tl => hRec (hNRow ρ) tl
  | .fn a b => .fn (hN a) (hN b)
  | .con as t => .con (hNList as) (gN t)
def hNRow : Row → Row
  | [] => []
  | (l, x) :: r => (l, hN x) :: hNRow r
def hNList : List Ty → List Ty
  | [] => []
  | x :: r => hN x :: hNList r
end

theorem hNList_eq : ∀ l : List Ty, hNList l = l.map hN
  | [] => rfl
  | x :: r => by simp [hNList, hNList_eq r]

theorem hNRow_eq : ∀ l : Row, hNRow l = l.map (fun p => (p.1, hN p.2))
  | [] => rfl
  | (l, x) :: r => by simp [hNRow, hNRow_eq r]

theorem hNRow_nil_iff (ρ : Row) : hNRow ρ = [] ↔ ρ = [] := by
  cases ρ <;> simp [hNRow]

/-- The term for a record whose fields are given: the normalised one. -/
def mkRec (ρ : List (Lab × T)) (tl : Option RowVar) : T :=
  match tl with
  | none => .record ρ none
  | some (.named s) =>
    match ρ with
    | [] => .var (.named s)
    | f :: r => .record (f :: r) (some (.named s))
  | some (.fresh n) => .record ρ (some (.fresh n))
  | some (.bnd i) => .record ρ (some (.bnd i))

theorem ev_mkRec (ν : Val) (ρ : List (Lab × T)) (tl : Option RowVar) :
    (mkRec ρ tl).ev ν = hRec (T.evRow ν ρ) tl := by
  cases tl with
  | none => rfl
  | some e =>
    cases e with
    | named s => cases ρ <;> rfl
    | fresh n => rfl
    | bnd i => rfl

theorem hN_tupleTy (τ1 τ2 : Ty) (τ3 : Option Ty) :
    hN (tupleTy τ1 τ2 τ3) = tupleTy (hN τ1) (hN τ2) (τ3.map hN) := by
  cases τ3 <;> simp [tupleTy, hN, hNList, gN_tTuple2, gN_tTuple3]

theorem hN_listTy (τ : Ty) : hN (listTy τ) = listTy (hN τ) := by
  simp [listTy, hN, hNList, gN_tList]

theorem hN_tIntTy : hN tIntTy = tIntTy := by simp [tIntTy, hN, hNList, gN_tInt]
theorem hN_tFloatTy : hN tFloatTy = tFloatTy := by simp [tFloatTy, hN, hNList, gN_tFloat]
theorem hN_tCharTy : hN tCharTy = tCharTy := by simp [tCharTy, hN, hNList, gN_tChar]
theorem hN_tStringTy : hN tStringTy = tStringTy := by simp [tStringTy, hN, hNList, gN_tString]
theorem hN_tUnitTy : hN tUnitTy = tUnitTy := by simp [tUnitTy, hN, hNList, gN_tUnit]

theorem hN_arrows (τ : Ty) : ∀ τs : List Ty, hN (arrows τs τ) = arrows (τs.map hN) (hN τ)
  | [] => rfl
  | a :: as => by simp [arrows, hN, hN_arrows τ as]

-- A normalised type with no variable comes from a type with no variable.
mutual
theorem vars_of_hN : ∀ τ : Ty, (hN τ).vars = [] → τ.vars = []
  | .var a, h => by simp [hN, Ty.vars] at h
  | .record ρ tl, h => by
    cases tl with
    | none => simp only [hN, hRec, Ty.vars] at h ⊢; exact rowVars_of_hN ρ h
    | some e =>
      exfalso
      cases e with
      | named s => simp only [hN, hRec] at h; split at h <;> simp [Ty.vars] at h
      | fresh n => simp [hN, hRec, Ty.vars] at h
      | bnd i => simp [hN, hRec, Ty.vars] at h
  | .fn a b, h => by
    simp only [hN, Ty.vars, List.append_eq_nil_iff] at h ⊢
    exact ⟨vars_of_hN a h.1, vars_of_hN b h.2⟩
  | .con as t, h => by
    simp only [hN, Ty.vars] at h ⊢
    exact listVars_of_hN as h
theorem rowVars_of_hN : ∀ ρ : Row, Ty.rowVars (hNRow ρ) = [] → Ty.rowVars ρ = []
  | [], _ => rfl
  | (l, x) :: r, h => by
    simp only [hNRow, Ty.rowVars, List.append_eq_nil_iff] at h ⊢
    exact ⟨vars_of_hN x h.1, rowVars_of_hN r h.2⟩
theorem listVars_of_hN : ∀ l : List Ty, Ty.listVars (hNList l) = [] → Ty.listVars l = []
  | [], _ => rfl
  | x :: r, h => by
    simp only [hNList, Ty.listVars, List.append_eq_nil_iff] at h ⊢
    exact ⟨vars_of_hN x h.1, listVars_of_hN r h.2⟩
end

/-- Normalisation keeps admissibility. -/
theorem adm_hN {k : Cls} {τ : Ty} (h : Adm k τ) : Adm k (hN τ) := by
  induction h with
  | any τ => exact .any _
  | num_int => rw [hN_tIntTy]; exact .num_int
  | num_float => rw [hN_tFloatTy]; exact .num_float
  | num_var a h => exact .num_var a h
  | comp_int => rw [hN_tIntTy]; exact .comp_int
  | comp_float => rw [hN_tFloatTy]; exact .comp_float
  | comp_char => rw [hN_tCharTy]; exact .comp_char
  | comp_string => rw [hN_tStringTy]; exact .comp_string
  | comp_var a h => exact .comp_var a h
  | comp_list τ _ ih => rw [hN_listTy]; exact .comp_list _ ih
  | comp_tuple2 τ1 τ2 _ _ ih1 ih2 => simp only [hN, hNList, gN_tTuple2]; exact .comp_tuple2 _ _ ih1 ih2
  | comp_tuple3 τ1 τ2 τ3 _ _ _ ih1 ih2 ih3 => simp only [hN, hNList, gN_tTuple3]; exact .comp_tuple3 _ _ _ ih1 ih2 ih3
  | app_string => rw [hN_tStringTy]; exact .app_string
  | app_list τ => rw [hN_listTy]; exact .app_list _
  | app_var a h => exact .app_var a h
  | capp_string => rw [hN_tStringTy]; exact .capp_string
  | capp_list τ _ ih => rw [hN_listTy]; exact .capp_list _ ih
  | capp_var a h => exact .capp_var a h

/-! ## Rows: modification over any values -/

/-- `Row.modifyF` over rows of any values (the decisions read the labels only). -/
def rmodF {α : Type} : Nat → List (Lab × α) → List (Lab × α) → List (Lab × α)
  | _, [], ρ' => ρ'
  | _, ρ, [] => ρ
  | 0, ρ, ρ' => ρ' ++ ρ
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 =>
    if l1 = l2 then (l2, τ2) :: rmodF f r1 r2
    else if labLt l1 l2 then (l1, τ1) :: rmodF f r1 ((l2, τ2) :: r2)
    else (l2, τ2) :: rmodF f ((l1, τ1) :: r1) r2

def rmod {α : Type} (ρ ρ' : List (Lab × α)) : List (Lab × α) := rmodF (ρ.length + ρ'.length) ρ ρ'

theorem rmodF_map {α β : Type} (g : α → β) : ∀ (n : Nat) (ρ ρ' : List (Lab × α)),
    (rmodF n ρ ρ').map (fun p => (p.1, g p.2)) =
      rmodF n (ρ.map (fun p => (p.1, g p.2))) (ρ'.map (fun p => (p.1, g p.2)))
  | n, [], ρ' => by cases n <;> simp [rmodF]
  | n, (l, τ) :: r, [] => by cases n <;> simp [rmodF]
  | 0, (l1, τ1) :: r1, (l2, τ2) :: r2 => by simp [rmodF]
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    simp only [rmodF, List.map_cons]
    split
    · simp [rmodF_map g n r1 r2]
    · split
      · have := rmodF_map g n r1 ((l2, τ2) :: r2); simp only [List.map_cons] at this; simp [this]
      · have := rmodF_map g n ((l1, τ1) :: r1) r2; simp only [List.map_cons] at this; simp [this]

theorem rmodF_eq : ∀ (n : Nat) (ρ ρ' : Row), Row.modifyF n ρ ρ' = rmodF n ρ ρ'
  | n, [], ρ' => by cases n <;> rfl
  | n, (l, τ) :: r, [] => by cases n <;> rfl
  | 0, (l1, τ1) :: r1, (l2, τ2) :: r2 => rfl
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    simp only [Row.modifyF, rmodF, rmodF_eq n]

theorem rmod_map {α β : Type} (g : α → β) (ρ ρ' : List (Lab × α)) :
    (rmod ρ ρ').map (fun p => (p.1, g p.2)) = rmod (ρ.map (fun p => (p.1, g p.2))) (ρ'.map (fun p => (p.1, g p.2))) := by
  unfold rmod; rw [rmodF_map]; simp

theorem modify_eq_rmod (ρ ρ' : Row) : Row.modify ρ ρ' = rmod ρ ρ' := rmodF_eq _ _ _

/-- The fields of a term row evaluated and normalised. -/
theorem evRow_rmod (ν : Val) (ρ ρ' : List (Lab × T)) :
    T.evRow ν (rmod ρ ρ') = rmod (T.evRow ν ρ) (T.evRow ν ρ') := by
  simp only [T.evRow_eq]; exact rmod_map _ ρ ρ'

theorem hNRow_modify (ρ ρ' : Row) : hNRow (Row.modify ρ ρ') = Row.modify (hNRow ρ) (hNRow ρ') := by
  simp only [hNRow_eq, modify_eq_rmod]; exact rmod_map _ ρ ρ'

/-! ## Lookups in rows -/

theorem find?_map_val {K V W : Type} [DecidableEq K] (g : V → W) (k : K) :
    ∀ l : List (K × V), FMap.find? (l.map (fun p => (p.1, g p.2))) k = (FMap.find? l k).map g
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, FMap.find?]
    split <;> simp [find?_map_val g k rest]

theorem find?_of_mem_map {α : Type} (g : α → Ty) (ρ : List (Lab × α)) (l : Lab) (y : Ty)
    (h : (l, y) ∈ ρ.map (fun p => (p.1, g p.2))) : ∃ x, (l, x) ∈ ρ ∧ g x = y := by
  obtain ⟨⟨l', x⟩, hm, e⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨x, hm, rfl⟩

end StandardElm.Stat.Complete
