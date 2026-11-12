/-
  A Standard Definition of Elm? Mechanisation: substitution and admissible types, plan step 9
  (section 2). sec:static-core-classes and sec:static-core-types of static-core.tex.

  A substitution {τ(k)/tyrowvar(k)} maps a type variable to a type and a row variable to a record
  type, given as its row and tail. `Subst.apply` is undefined (`none`) exactly when, where a row
  variable is replaced, the row it extends and the row it is replaced by share a label (A23).
-/
import StandardElmMech.Stat.Objects

namespace StandardElm.Stat

structure Subst where
  ty : FMap TyVar Ty
  row : FMap RowVar (Row × Option RowVar)
  deriving Repr, Inhabited

def Subst.id : Subst := ⟨[], []⟩

def Subst.dom (S : Subst) : List BVar := S.ty.map (fun p => .ty p.1) ++ S.row.map (fun p => .row p.1)

mutual
def Subst.apply (S : Subst) : Ty → Option Ty
  | .var a => some ((FMap.find? S.ty a).getD (.var a))
  | .record ρ none =>
    match Subst.applyRow S ρ with
    | some ρ' => some (.record ρ' none)
    | none => none
  | .record ρ (some e) =>
    match Subst.applyRow S ρ with
    | none => none
    | some ρ' =>
      match FMap.find? S.row e with
      | none => some (.record ρ' (some e))
      | some (ρ2, tl) =>
        match Row.merge ρ' ρ2 with
        | some ρ3 => some (.record ρ3 tl)
        | none => none
  | .fn a b =>
    match Subst.apply S a, Subst.apply S b with
    | some a', some b' => some (.fn a' b')
    | _, _ => none
  | .con as t =>
    match Subst.applyList S as with
    | some as' => some (.con as' t)
    | none => none
def Subst.applyRow (S : Subst) : Row → Option Row
  | [] => some []
  | (l, τ) :: rest =>
    match Subst.apply S τ, Subst.applyRow S rest with
    | some τ', some r' => some ((l, τ') :: r')
    | _, _ => none
def Subst.applyList (S : Subst) : List Ty → Option (List Ty)
  | [] => some []
  | τ :: rest =>
    match Subst.apply S τ, Subst.applyList S rest with
    | some τ', some r' => some (τ' :: r')
    | _, _ => none
end

/-- Defined on every type of a list. -/
def Subst.DefinedOn (S : Subst) (ts : List Ty) : Prop := ∀ τ ∈ ts, (S.apply τ).isSome

/-! ## Admissible types (fig:static-core-admissible) -/

/-- Adm κ; Adm comp is the least set satisfying its equation. -/
inductive Adm : Cls → Ty → Prop where
  | any (τ : Ty) : Adm .any τ
  | num_int : Adm .num tIntTy
  | num_float : Adm .num tFloatTy
  | num_var (a : TyVar) : a.cls = .num → Adm .num (.var a)
  | comp_int : Adm .comp tIntTy
  | comp_float : Adm .comp tFloatTy
  | comp_char : Adm .comp tCharTy
  | comp_string : Adm .comp tStringTy
  | comp_var (a : TyVar) : a.cls.le .comp = true → Adm .comp (.var a)
  | comp_list (τ : Ty) : Adm .comp τ → Adm .comp (listTy τ)
  | comp_tuple2 (τ1 τ2 : Ty) : Adm .comp τ1 → Adm .comp τ2 → Adm .comp (.con [τ1, τ2] tTuple2)
  | comp_tuple3 (τ1 τ2 τ3 : Ty) : Adm .comp τ1 → Adm .comp τ2 → Adm .comp τ3 →
      Adm .comp (.con [τ1, τ2, τ3] tTuple3)
  | app_string : Adm .app tStringTy
  | app_list (τ : Ty) : Adm .app (listTy τ)
  | app_var (a : TyVar) : a.cls.le .app = true → Adm .app (.var a)
  | capp_string : Adm .capp tStringTy
  | capp_list (τ : Ty) : Adm .comp τ → Adm .capp (listTy τ)
  | capp_var (a : TyVar) : a.cls = .capp → Adm .capp (.var a)

def admComp : Ty → Bool
  | .var a => a.cls.le .comp
  | .con [] t => t == tInt || t == tFloat || t == tChar || t == tString
  | .con [τ] t => t == tList && admComp τ
  | .con [τ1, τ2] t => t == tTuple2 && admComp τ1 && admComp τ2
  | .con [τ1, τ2, τ3] t => t == tTuple3 && admComp τ1 && admComp τ2 && admComp τ3
  | _ => false

def adm : Cls → Ty → Bool
  | .any, _ => true
  | .num, .var a => a.cls == .num
  | .num, τ => τ == tIntTy || τ == tFloatTy
  | .comp, τ => admComp τ
  | .app, .var a => a.cls.le .app
  | .app, .con [] t => t == tString
  | .app, .con [_] t => t == tList
  | .app, _ => false
  | .capp, .var a => a.cls == .capp
  | .capp, .con [] t => t == tString
  | .capp, .con [τ] t => t == tList && admComp τ
  | .capp, _ => false

theorem admComp_iff (τ : Ty) : admComp τ = true ↔ Adm .comp τ := by
  constructor
  · intro h
    match τ, h with
    | .var a, h => exact .comp_var a h
    | .con [] t, h =>
      simp only [admComp, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((h | h) | h) | h <;> subst h
      · exact .comp_int
      · exact .comp_float
      · exact .comp_char
      · exact .comp_string
    | .con [τ1] t, h =>
      simp only [admComp, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h1⟩ := h
      exact .comp_list _ ((admComp_iff τ1).mp h1)
    | .con [τ1, τ2] t, h =>
      simp only [admComp, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, h1⟩, h2⟩ := h
      exact .comp_tuple2 _ _ ((admComp_iff τ1).mp h1) ((admComp_iff τ2).mp h2)
    | .con [τ1, τ2, τ3] t, h =>
      simp only [admComp, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, h1⟩, h2⟩, h3⟩ := h
      exact .comp_tuple3 _ _ _ ((admComp_iff τ1).mp h1) ((admComp_iff τ2).mp h2) ((admComp_iff τ3).mp h3)
    | .record _ _, h => simp [admComp] at h
    | .fn _ _, h => simp [admComp] at h
    | .con (_ :: _ :: _ :: _ :: _) _, h => simp [admComp] at h
  · intro h
    cases h with
    | comp_int => rfl
    | comp_float => rfl
    | comp_char => rfl
    | comp_string => rfl
    | comp_var a h => exact h
    | comp_list τ h => simp only [admComp, listTy, beq_self_eq_true, Bool.true_and]; exact (admComp_iff τ).mpr h
    | comp_tuple2 τ1 τ2 h1 h2 =>
      simp only [admComp, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
      exact ⟨(admComp_iff τ1).mpr h1, (admComp_iff τ2).mpr h2⟩
    | comp_tuple3 τ1 τ2 τ3 h1 h2 h3 =>
      simp only [admComp, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
      exact ⟨⟨(admComp_iff τ1).mpr h1, (admComp_iff τ2).mpr h2⟩, (admComp_iff τ3).mpr h3⟩

theorem adm_iff (k : Cls) (τ : Ty) : adm k τ = true ↔ Adm k τ := by
  cases k with
  | any => exact ⟨fun _ => .any τ, fun _ => rfl⟩
  | comp => exact admComp_iff τ
  | num =>
    constructor
    · intro h
      match τ, h with
      | .var a, h => exact .num_var a (by simpa [adm] using h)
      | .record _ _, h => simp [adm, tIntTy, tFloatTy] at h
      | .fn _ _, h => simp [adm, tIntTy, tFloatTy] at h
      | .con as t, h =>
        simp only [adm, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h <;> rw [h]
        · exact .num_int
        · exact .num_float
    · intro h
      cases h with
      | num_int => rfl
      | num_float => rfl
      | num_var a h => simp [adm, h]
  | app =>
    constructor
    · intro h
      match τ, h with
      | .var a, h => exact .app_var a h
      | .con [] t, h => simp only [adm, beq_iff_eq] at h; subst h; exact .app_string
      | .con [τ1] t, h => simp only [adm, beq_iff_eq] at h; subst h; exact .app_list τ1
      | .record _ _, h => simp [adm] at h
      | .fn _ _, h => simp [adm] at h
      | .con (_ :: _ :: _) _, h => simp [adm] at h
    · intro h
      cases h with
      | app_string => rfl
      | app_list τ => rfl
      | app_var a h => exact h
  | capp =>
    constructor
    · intro h
      match τ, h with
      | .var a, h => exact .capp_var a (by simpa [adm] using h)
      | .con [] t, h => simp only [adm, beq_iff_eq] at h; subst h; exact .capp_string
      | .con [τ1] t, h =>
        simp only [adm, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, h1⟩ := h
        exact .capp_list τ1 ((admComp_iff τ1).mp h1)
      | .record _ _, h => simp [adm] at h
      | .fn _ _, h => simp [adm] at h
      | .con (_ :: _ :: _) _, h => simp [adm] at h
    · intro h
      cases h with
      | capp_string => rfl
      | capp_list τ h =>
        simp only [adm, listTy, beq_self_eq_true, Bool.true_and]; exact (admComp_iff τ).mpr h
      | capp_var a h => simp [adm, h]

instance (k : Cls) (τ : Ty) : Decidable (Adm k τ) := decidable_of_iff _ (adm_iff k τ)

/-- The substitution respects classes. -/
def Subst.Respects (S : Subst) : Prop := ∀ p ∈ S.ty, Adm p.1.cls p.2

def Subst.respectsB (S : Subst) : Bool := S.ty.all fun p => adm p.1.cls p.2

theorem Subst.respectsB_iff (S : Subst) : S.respectsB = true ↔ S.Respects := by
  simp [Subst.respectsB, Subst.Respects, List.all_eq_true, adm_iff]

instance (S : Subst) : Decidable S.Respects := decidable_of_iff _ S.respectsB_iff

/-! ## Group 1: classes -/

instance Cls.decForall (P : Cls → Prop) [DecidablePred P] : Decidable (∀ n, P n) :=
  decidable_of_iff (P .any ∧ P .num ∧ P .comp ∧ P .app ∧ P .capp) (by
    constructor
    · rintro ⟨a, b, c, d, e⟩ n; cases n <;> assumption
    · intro h; exact ⟨h _, h _, h _, h _, h _⟩)

theorem Cls.meet_spec (k k' m : Cls) :
    Cls.meet k k' = some m ↔
      (m.le k = true ∧ m.le k' = true ∧ ∀ n : Cls, n.le k = true → n.le k' = true → n.le m = true) := by
  cases k <;> cases k' <;> cases m <;> decide

theorem Cls.meet_none (k k' : Cls) : Cls.meet k k' = none ↔ ∀ n : Cls, ¬ (n.le k = true ∧ n.le k' = true) := by
  cases k <;> cases k' <;> decide

theorem Cls.le_trans (a b c : Cls) : a.le b = true → b.le c = true → a.le c = true := by
  cases a <;> cases b <;> cases c <;> decide

/-- The property of sec:static-core-types, first part: κ ≤ κ' gives Adm κ ⊆ Adm κ'. -/
theorem adm_mono {k k' : Cls} {τ : Ty} (hle : k.le k' = true) (h : Adm k τ) : Adm k' τ := by
  cases k' with
  | any => exact .any τ
  | num => cases k <;> simp [Cls.le] at hle; exact h
  | comp =>
    cases k with
    | any => simp [Cls.le] at hle
    | app => simp [Cls.le] at hle
    | comp => exact h
    | num =>
      cases h with
      | num_int => exact .comp_int
      | num_float => exact .comp_float
      | num_var a ha => exact .comp_var a (by simp [ha, Cls.le])
    | capp =>
      cases h with
      | capp_string => exact .comp_string
      | capp_list τ h => exact .comp_list τ h
      | capp_var a ha => exact .comp_var a (by simp [ha, Cls.le])
  | app =>
    cases k with
    | any | num | comp => simp [Cls.le] at hle
    | app => exact h
    | capp =>
      cases h with
      | capp_string => exact .app_string
      | capp_list τ _ => exact .app_list τ
      | capp_var a ha => exact .app_var a (by simp [ha, Cls.le])
  | capp => cases k <;> simp [Cls.le] at hle; exact h

end StandardElm.Stat
