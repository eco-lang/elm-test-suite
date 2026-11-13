/-
  A Standard Definition of Elm? Mechanisation: refusals by type expressions and by the type of
  `main`, plan step 9 (section 10, groups 7 and 8, milestone 9d).

  `typesFailB B sp`: some type expression of the first module (an alias, a constructor argument, a
  top-level annotation, a port) elaborates in no derivation. `mainFailB B sp`: the one module gives
  `main` a type that is neither a `Program` nor a `Node` type in every derivation. Both are
  unconditional: they quantify over every derivation, its generated type names, and the sorts of
  the new variables of its annotations.

  The method is a simulation. A derivation chooses the names of its custom types; collapsing every
  type name outside B.T to a name ⟨D, arity⟩ (`fcol`) maps every type a derivation computes to the
  type an abstract elaboration computes, in a context `A` built from the imports (collapsed) and
  the module's type declarations (custom types as ⟨D, k⟩, aliases elaborated in order). If a type
  expression elaborates in a derivation's context, its collapse elaborates in `A` (`elabTy_sim`);
  so a failure in `A` is a failure in every derivation. The sorts of the new variables of an
  annotation are enumerated (`assigns`).
-/
import StandardElmMech.Stat.Refusals

namespace StandardElm.Stat.RTypes
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  SLit BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule)

/-! ## Renaming type names -/

mutual
def mapTy (f : TyName → TyName) : Ty → Ty
  | .var a => .var a
  | .record ρ tl => .record (mapRow f ρ) tl
  | .fn a b => .fn (mapTy f a) (mapTy f b)
  | .con as t => .con (mapTys f as) (f t)
def mapRow (f : TyName → TyName) : Row → Row
  | [] => []
  | (l, τ) :: rest => (l, mapTy f τ) :: mapRow f rest
def mapTys (f : TyName → TyName) : List Ty → List Ty
  | [] => []
  | τ :: rest => mapTy f τ :: mapTys f rest
end

theorem mapTys_eq (f : TyName → TyName) : ∀ l : List Ty, mapTys f l = l.map (mapTy f)
  | [] => by simp [mapTys]
  | τ :: rest => by simp [mapTys, mapTys_eq f rest]

theorem mapRow_eq (f : TyName → TyName) : ∀ ρ : Row, mapRow f ρ = ρ.map (fun p => (p.1, mapTy f p.2))
  | [] => by simp [mapRow]
  | (l, τ) :: rest => by simp [mapRow, mapRow_eq f rest]

def mapFcn (f : TyName → TyName) (θ : TyFcn) : TyFcn := ⟨θ.params, mapTy f θ.body⟩

def mapSubst (f : TyName → TyName) (S : Subst) : Subst :=
  ⟨S.ty.map (fun p => (p.1, mapTy f p.2)), S.row.map (fun p => (p.1, (mapRow f p.2.1, p.2.2)))⟩

theorem find?_map_snd {K V W : Type} [DecidableEq K] (g : V → W) (k : K) :
    ∀ l : FMap K V, FMap.find? (l.map (fun p => (p.1, g p.2))) k = (FMap.find? l k).map g
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, FMap.find?]
    split <;> simp [find?_map_snd g k rest]

theorem find?_map_key {K V W : Type} [DecidableEq K] (h : K × V → W) (k : K) :
    ∀ l : FMap K V, FMap.find? (l.map (fun p => (p.1, h p))) k = (FMap.find? l k).map (fun v => h (k, v))
  | [] => rfl
  | (k', v) :: rest => by
    simp only [List.map_cons, FMap.find?]
    split
    · rename_i e; subst e; rfl
    · exact find?_map_key h k rest

/-- A map of the values of a row, keeping its labels. -/
def rowMap (g : Ty → Ty) (ρ : Row) : Row := ρ.map (fun p => (p.1, g p.2))

theorem mergeF_map (g : Ty → Ty) : ∀ (n : Nat) (ρ ρ' : Row),
    Row.mergeF n (rowMap g ρ) (rowMap g ρ') = (Row.mergeF n ρ ρ').map (rowMap g)
  | n, [], ρ' => by cases n <;> simp [rowMap, Row.mergeF]
  | n, (l, τ) :: r, [] => by cases n <;> simp [rowMap, Row.mergeF]
  | 0, (l1, τ1) :: r1, (l2, τ2) :: r2 => by simp [rowMap, Row.mergeF]
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    have ih1 := mergeF_map g n r1 ((l2, τ2) :: r2)
    have ih2 := mergeF_map g n ((l1, τ1) :: r1) r2
    simp only [rowMap, List.map_cons] at ih1 ih2 ⊢
    simp only [Row.mergeF]
    split
    · simp
    · split
      · rw [ih1]; cases Row.mergeF n r1 ((l2, τ2) :: r2) <;> simp [rowMap]
      · rw [ih2]; cases Row.mergeF n ((l1, τ1) :: r1) r2 <;> simp [rowMap]

theorem merge_map (g : Ty → Ty) (ρ ρ' : Row) :
    Row.merge (rowMap g ρ) (rowMap g ρ') = (Row.merge ρ ρ').map (rowMap g) := by
  unfold Row.merge
  have : (rowMap g ρ).length + (rowMap g ρ').length = ρ.length + ρ'.length := by simp [rowMap]
  rw [this, mergeF_map]

theorem modifyF_map (g : Ty → Ty) : ∀ (n : Nat) (ρ ρ' : Row),
    Row.modifyF n (rowMap g ρ) (rowMap g ρ') = rowMap g (Row.modifyF n ρ ρ')
  | n, [], ρ' => by cases n <;> simp [rowMap, Row.modifyF]
  | n, (l, τ) :: r, [] => by cases n <;> simp [rowMap, Row.modifyF]
  | 0, (l1, τ1) :: r1, (l2, τ2) :: r2 => by simp [rowMap, Row.modifyF]
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    have ih0 := modifyF_map g n r1 r2
    have ih1 := modifyF_map g n r1 ((l2, τ2) :: r2)
    have ih2 := modifyF_map g n ((l1, τ1) :: r1) r2
    simp only [rowMap, List.map_cons] at ih0 ih1 ih2 ⊢
    simp only [Row.modifyF]
    split
    · simp [ih0]
    · split
      · simp [ih1]
      · simp [ih2]

theorem modify_map (g : Ty → Ty) (ρ ρ' : Row) :
    Row.modify (rowMap g ρ) (rowMap g ρ') = rowMap g (Row.modify ρ ρ') := by
  unfold Row.modify
  have : (rowMap g ρ).length + (rowMap g ρ').length = ρ.length + ρ'.length := by simp [rowMap]
  rw [this, modifyF_map]

theorem mapRow_rowMap (f : TyName → TyName) (ρ : Row) : mapRow f ρ = rowMap (mapTy f) ρ := by
  rw [mapRow_eq]; rfl

mutual
theorem apply_map (f : TyName → TyName) (S : Subst) :
    ∀ τ : Ty, (mapSubst f S).apply (mapTy f τ) = (S.apply τ).map (mapTy f)
  | .var a => by
    simp only [mapTy, Subst.apply, mapSubst, Option.map_some]
    rw [find?_map_snd (mapTy f)]
    cases FMap.find? S.ty a <;> simp [mapTy]
  | .record ρ none => by
    simp only [mapTy, Subst.apply]
    rw [applyRow_map f S ρ]
    cases S.applyRow ρ <;> simp [mapTy]
  | .record ρ (some e) => by
    simp only [mapTy, Subst.apply]
    rw [applyRow_map f S ρ]
    cases S.applyRow ρ with
    | none => simp
    | some ρ' =>
      simp only [Option.map_some]
      have hf : FMap.find? (mapSubst f S).row e = (FMap.find? S.row e).map (fun p => (mapRow f p.1, p.2)) := by
        simp only [mapSubst]
        exact find?_map_snd (fun p => (mapRow f p.1, p.2)) e S.row
      rw [hf]
      cases FMap.find? S.row e with
      | none => simp [mapTy]
      | some p =>
        obtain ⟨ρ2, tl⟩ := p
        simp only [Option.map_some, mapRow_rowMap]
        rw [merge_map]
        cases Row.merge ρ' ρ2 <;> simp [mapTy, mapRow_rowMap]
  | .fn a b => by
    simp only [mapTy, Subst.apply]
    rw [apply_map f S a, apply_map f S b]
    cases S.apply a <;> cases S.apply b <;> simp [mapTy]
  | .con as t => by
    simp only [mapTy, Subst.apply]
    rw [applyList_map f S as]
    cases S.applyList as <;> simp [mapTy]
theorem applyRow_map (f : TyName → TyName) (S : Subst) :
    ∀ ρ : Row, (mapSubst f S).applyRow (mapRow f ρ) = (S.applyRow ρ).map (mapRow f)
  | [] => by simp [mapRow, Subst.applyRow]
  | (l, τ) :: rest => by
    simp only [mapRow, Subst.applyRow]
    rw [apply_map f S τ, applyRow_map f S rest]
    cases S.apply τ <;> cases S.applyRow rest <;> simp [mapRow]
theorem applyList_map (f : TyName → TyName) (S : Subst) :
    ∀ l : List Ty, (mapSubst f S).applyList (mapTys f l) = (S.applyList l).map (mapTys f)
  | [] => by simp [mapTys, Subst.applyList]
  | τ :: rest => by
    simp only [mapTys, Subst.applyList]
    rw [apply_map f S τ, applyList_map f S rest]
    cases S.apply τ <;> cases S.applyList rest <;> simp [mapTys]
end

theorem bindSubst_map (f : TyName → TyName) :
    ∀ (vs : List BVar) (ts : List Ty), bindSubst vs (mapTys f ts) = (bindSubst vs ts).map (mapSubst f)
  | [], [] => by simp [bindSubst, mapTys, mapSubst, Subst.id]
  | [], _ :: _ => by simp [bindSubst, mapTys]
  | _ :: _, [] => by simp [bindSubst, mapTys]
  | .ty a :: vs, τ :: ts => by
    simp only [bindSubst, mapTys]
    rw [bindSubst_map f vs ts]
    cases bindSubst vs ts <;> simp [mapSubst]
  | .row e :: vs, .record ρ tl :: ts => by
    simp only [bindSubst, mapTys, mapTy]
    rw [bindSubst_map f vs ts]
    cases bindSubst vs ts <;> simp [mapSubst]
  | .row e :: vs, .var a :: ts => by simp [bindSubst, mapTys, mapTy]
  | .row e :: vs, .fn a b :: ts => by simp [bindSubst, mapTys, mapTy]
  | .row e :: vs, .con as t :: ts => by simp [bindSubst, mapTys, mapTy]

theorem tyFcnApply_map (f : TyName → TyName) (θ : TyFcn) (ts : List Ty) :
    (mapFcn f θ).apply (mapTys f ts) = (θ.apply ts).map (mapTy f) := by
  unfold TyFcn.apply
  simp only [mapFcn]
  rw [bindSubst_map]
  cases bindSubst θ.params ts with
  | none => simp
  | some S => simp only [Option.map_some]; exact apply_map f S θ.body

theorem renumber_fixed (f : TyName → TyName) (k : Bool) :
    ∀ (i : Nat) (vs : List BVar), mapSubst f (renumber k i vs).1 = (renumber k i vs).1
  | _, [] => by simp [renumber, mapSubst, Subst.id]
  | i, .ty a :: vs => by
    have ih := renumber_fixed f k (i + 1) vs
    simp only [renumber]
    revert ih
    generalize renumber k (i + 1) vs = r
    obtain ⟨S, bs⟩ := r
    intro ih
    simp only [mapSubst] at ih ⊢
    obtain ⟨Sty, Srow⟩ := S
    simp only [Subst.mk.injEq] at ih
    simp [ih.1, ih.2, mapTy]
  | i, .row e :: vs => by
    have ih := renumber_fixed f k (i + 1) vs
    simp only [renumber]
    revert ih
    generalize renumber k (i + 1) vs = r
    obtain ⟨S, bs⟩ := r
    intro ih
    simp only [mapSubst] at ih ⊢
    obtain ⟨Sty, Srow⟩ := S
    simp only [Subst.mk.injEq] at ih
    simp [ih.1, ih.2, mapRow]

theorem canon_map (f : TyName → TyName) (θ : TyFcn) :
    mapFcn f (TyFcn.canon θ) = TyFcn.canon (mapFcn f θ) := by
  unfold TyFcn.canon
  simp only [mapFcn]
  have hfix := renumber_fixed f false 0 (dedupL θ.params)
  revert hfix
  generalize renumber false 0 (dedupL θ.params) = r
  obtain ⟨S, bs⟩ := r
  intro hfix
  simp only at hfix ⊢
  have := apply_map f S θ.body
  rw [hfix] at this
  rw [this]
  cases S.apply θ.body <;> simp

theorem toFcn_map (f : TyName → TyName) (t : TyName) (ha : (f t).arity = t.arity) :
    mapFcn f t.toFcn = (f t).toFcn := by
  simp only [mapFcn, TyName.toFcn, mapTy, mapTys_eq, List.map_map, ha]
  rfl

/-! ## Simulation of the elaboration of type expressions -/

/-- A lookup of `lc` in C is, collapsed by f, a lookup in A. -/
def LookSim (f : TyName → TyName) (C A : Ctx) (lc : LongId) : Prop :=
  ∀ θ VE, C.lookupTy lc = some (θ, VE) → ∃ VE', A.lookupTy lc = some (mapFcn f θ, VE')

/-- The named variables of two sets agree. -/
def UEq (U1 U2 : List BVar) : Prop :=
  ∀ s, (BVar.ty (.named s) ∈ U1 ↔ BVar.ty (.named s) ∈ U2) ∧ (BVar.row (.named s) ∈ U1 ↔ BVar.row (.named s) ∈ U2)

theorem mem_unionL {α : Type} [DecidableEq α] {x : α} {A B : List α} : x ∈ unionL A B ↔ x ∈ A ∨ x ∈ B := by
  unfold unionL diffL
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact .inl h
    · exact .inr h
  · rintro (h | h)
    · exact .inl h
    · by_cases hA : x ∈ A
      · exact .inl hA
      · exact .inr ⟨h, hA⟩

theorem UEq.plusU {U1 U2 : List BVar} (h : UEq U1 U2) (V : List BVar) : UEq (unionL U1 V) (unionL U2 V) := by
  intro s
  simp only [mem_unionL]
  exact ⟨or_congr_left (h s).1, or_congr_left (h s).2⟩

mutual
/-- The type constructors a type expression names. -/
def bTyCons : BTy → List LongId
  | .tyvar _ => []
  | .record row => bTyRowOptCons row
  | .openRecord _ row => bTyRowCons row
  | .unit => []
  | .tuple t1 t2 t3 => bTyCons t1 ++ bTyCons t2 ++ bTyOptCons t3
  | .con c args => c :: bTyListCons args
  | .fn t1 t2 => bTyCons t1 ++ bTyCons t2
  | .paren t => bTyCons t
def bTyRowCons : BTyRow → List LongId
  | .field _ t rest => bTyCons t ++ bTyRowOptCons rest
def bTyRowOptCons : Option BTyRow → List LongId
  | none => []
  | some r => bTyRowCons r
def bTyOptCons : Option BTy → List LongId
  | none => []
  | some t => bTyCons t
def bTyListCons : List BTy → List LongId
  | [] => []
  | t :: ts => bTyCons t ++ bTyListCons ts
end

/-- The built-in type names the elaboration of type expressions produces. -/
def FixesBuiltins (f : TyName → TyName) : Prop := f tUnit = tUnit ∧ f tTuple2 = tTuple2 ∧ f tTuple3 = tTuple3

theorem tupleTy_map (f : TyName → TyName) (hf : FixesBuiltins f) (τ1 τ2 : Ty) (τ3 : Option Ty) :
    mapTy f (tupleTy τ1 τ2 τ3) = tupleTy (mapTy f τ1) (mapTy f τ2) (τ3.map (mapTy f)) := by
  cases τ3 <;> simp [tupleTy, mapTy, mapTys, hf.2.1, hf.2.2]

theorem modify_single_map (f : TyName → TyName) (l : Lab) (τ : Ty) (ρ : Row) :
    Row.modify [(l, mapTy f τ)] (mapRow f ρ) = mapRow f (Row.modify [(l, τ)] ρ) := by
  have := modify_map (mapTy f) [(l, τ)] ρ
  simp only [rowMap, List.map_cons, List.map_nil] at this
  rw [mapRow_rowMap, mapRow_rowMap]
  exact this

section sim
set_option linter.unusedSectionVars false
variable (f : TyName → TyName) (hf : FixesBuiltins f) (C A : Ctx) (hU : UEq C.U A.U)
include hf hU

mutual
theorem elabTy_sim : ∀ (t : BTy) (τ : Ty), (∀ lc ∈ bTyCons t, LookSim f C A lc) →
    elabTy C t = some τ → elabTy A t = some (mapTy f τ)
  | .tyvar a, τ, _, h => by
    unfold elabTy at h ⊢
    have h1 := (hU a).1
    have h2 := (hU a).2
    by_cases ha : BVar.ty (.named a) ∈ C.U
    · rw [ite_eq_left ha] at h; cases h
      rw [ite_eq_left (h1.mp ha)]; rfl
    · rw [ite_eq_right ha] at h
      rw [ite_eq_right (fun h' => ha (h1.mpr h'))]
      by_cases hr : classOfName a = .any ∧ BVar.row (.named a) ∈ C.U
      · rw [ite_eq_left hr] at h; cases h
        rw [ite_eq_left ⟨hr.1, h2.mp hr.2⟩]; simp [mapTy, mapRow]
      · rw [ite_eq_right hr] at h; cases h
  | .record row, τ, hl, h => by
    unfold elabTy at h ⊢
    cases hr : elabTyRowOpt C row with
    | none => rw [hr] at h; cases h
    | some ρ =>
      rw [hr] at h; cases h
      rw [elabTyRowOpt_sim row ρ (by simpa [bTyCons] using hl) hr]
      simp [mapTy]
  | .openRecord r row, τ, hl, h => by
    unfold elabTy at h ⊢
    have h2 := (hU r).2
    by_cases hc : classOfName r = .any ∧ BVar.row (.named r) ∈ C.U
    · rw [ite_eq_left hc] at h
      rw [ite_eq_left ⟨hc.1, h2.mp hc.2⟩]
      cases hr : elabTyRow C row with
      | none => rw [hr] at h; cases h
      | some ρ =>
        rw [hr] at h; cases h
        rw [elabTyRow_sim row ρ (by simpa [bTyCons] using hl) hr]
        simp [mapTy]
    · rw [ite_eq_right hc] at h; cases h
  | .unit, τ, _, h => by
    unfold elabTy at h ⊢; cases h
    simp [tUnitTy, mapTy, mapTys, hf.1]
  | .tuple t1 t2 t3, τ, hl, h => by
    unfold elabTy at h ⊢
    simp only [bTyCons, List.mem_append] at hl
    cases h1 : elabTy C t1 with
    | none => rw [h1] at h; simp at h
    | some τ1 =>
      cases h2 : elabTy C t2 with
      | none => rw [h1, h2] at h; simp at h
      | some τ2 =>
        cases h3 : elabTyOpt C t3 with
        | none => rw [h1, h2, h3] at h; simp at h
        | some τ3 =>
          rw [h1, h2, h3] at h; cases h
          rw [elabTy_sim t1 τ1 (fun lc h => hl lc (.inl (.inl h))) h1,
            elabTy_sim t2 τ2 (fun lc h => hl lc (.inl (.inr h))) h2,
            elabTyOpt_sim t3 τ3 (fun lc h => hl lc (.inr h)) h3]
          simp [tupleTy_map f hf]
  | .con c args, τ, hl, h => by
    unfold elabTy at h ⊢
    simp only [bTyCons, List.mem_cons] at hl
    cases hc : C.lookupTy c with
    | none => rw [hc] at h; simp at h
    | some s =>
      obtain ⟨θ, VE⟩ := s
      cases ha : elabTyList C args with
      | none => rw [hc, ha] at h; simp at h
      | some τs =>
        rw [hc, ha] at h
        simp only at h
        obtain ⟨VE', hA⟩ := hl c (.inl rfl) θ VE hc
        rw [hA, elabTyList_sim args τs (fun lc h => hl lc (.inr h)) ha]
        simp only
        rw [tyFcnApply_map, h]; rfl
  | .fn t1 t2, τ, hl, h => by
    unfold elabTy at h ⊢
    simp only [bTyCons, List.mem_append] at hl
    cases h1 : elabTy C t1 with
    | none => rw [h1] at h; simp at h
    | some τ1 =>
      cases h2 : elabTy C t2 with
      | none => rw [h1, h2] at h; simp at h
      | some τ2 =>
        rw [h1, h2] at h; cases h
        rw [elabTy_sim t1 τ1 (fun lc h => hl lc (.inl h)) h1,
          elabTy_sim t2 τ2 (fun lc h => hl lc (.inr h)) h2]
        simp [mapTy]
  | .paren t, τ, hl, h => by
    unfold elabTy at h ⊢
    exact elabTy_sim t τ (by simpa [bTyCons] using hl) h
theorem elabTyRow_sim : ∀ (r : BTyRow) (ρ : Row), (∀ lc ∈ bTyRowCons r, LookSim f C A lc) →
    elabTyRow C r = some ρ → elabTyRow A r = some (mapRow f ρ)
  | .field l t rest, ρ, hl, h => by
    unfold elabTyRow at h ⊢
    simp only [bTyRowCons, List.mem_append] at hl
    cases h1 : elabTy C t with
    | none => rw [h1] at h; simp at h
    | some τ =>
      cases h2 : elabTyRowOpt C rest with
      | none => rw [h1, h2] at h; simp at h
      | some ρ' =>
        rw [h1, h2] at h; cases h
        rw [elabTy_sim t τ (fun lc h => hl lc (.inl h)) h1,
          elabTyRowOpt_sim rest ρ' (fun lc h => hl lc (.inr h)) h2]
        simp [modify_single_map]
theorem elabTyRowOpt_sim : ∀ (r : Option BTyRow) (ρ : Row), (∀ lc ∈ bTyRowOptCons r, LookSim f C A lc) →
    elabTyRowOpt C r = some ρ → elabTyRowOpt A r = some (mapRow f ρ)
  | none, ρ, _, h => by unfold elabTyRowOpt at h ⊢; cases h; rfl
  | some r, ρ, hl, h => by
    unfold elabTyRowOpt at h ⊢
    exact elabTyRow_sim r ρ (by simpa [bTyRowOptCons] using hl) h
theorem elabTyOpt_sim : ∀ (t : Option BTy) (τ : Option Ty), (∀ lc ∈ bTyOptCons t, LookSim f C A lc) →
    elabTyOpt C t = some τ → elabTyOpt A t = some (τ.map (mapTy f))
  | none, τ, _, h => by unfold elabTyOpt at h ⊢; cases h; rfl
  | some t, τ, hl, h => by
    unfold elabTyOpt at h ⊢
    cases h1 : elabTy C t with
    | none => rw [h1] at h; simp at h
    | some τ' =>
      rw [h1] at h; cases h
      rw [elabTy_sim t τ' (by simpa [bTyOptCons] using hl) h1]
      rfl
theorem elabTyList_sim : ∀ (ts : List BTy) (τs : List Ty), (∀ lc ∈ bTyListCons ts, LookSim f C A lc) →
    elabTyList C ts = some τs → elabTyList A ts = some (mapTys f τs)
  | [], τs, _, h => by unfold elabTyList at h ⊢; cases h; rfl
  | t :: ts, τs, hl, h => by
    unfold elabTyList at h ⊢
    simp only [bTyListCons, List.mem_append] at hl
    cases h1 : elabTy C t with
    | none => rw [h1] at h; simp at h
    | some τ =>
      cases h2 : elabTyList C ts with
      | none => rw [h1, h2] at h; simp at h
      | some τs' =>
        rw [h1, h2] at h; cases h
        rw [elabTy_sim t τ (fun lc h => hl lc (.inl h)) h1,
          elabTyList_sim ts τs' (fun lc h => hl lc (.inr h)) h2]
        simp [mapTys]
end

end sim

/-! ## Lookups in modified contexts -/

theorem lookupTy_none (C : Ctx) (c : String) : C.lookupTy ⟨none, c⟩ = C.E.TE.find? c := rfl

theorem lookupTy_oplusTE_none (C : Ctx) (TE : TyEnv) (c : String) :
    (C.oplusTE TE).lookupTy ⟨none, c⟩ = (TE.find? c).or (C.lookupTy ⟨none, c⟩) := by
  simp [Ctx.lookupTy, Env.lookupTy, Ctx.oplusTE, FMap.find?_modify]

theorem lookupTy_oplusTE_some (C : Ctx) (TE : TyEnv) (m c : String) :
    (C.oplusTE TE).lookupTy ⟨some m, c⟩ = C.lookupTy ⟨some m, c⟩ := rfl

theorem lookupTy_oplusE_none (C : Ctx) (E : Env) (c : String) :
    (C.oplusE E).lookupTy ⟨none, c⟩ = (E.TE.find? c).or (C.lookupTy ⟨none, c⟩) := by
  simp [Ctx.lookupTy, Env.lookupTy, Ctx.oplusE, Env.plus, FMap.find?_modify]

theorem lookupTy_oplusE_some (C : Ctx) (E : Env) (m c : String) :
    (C.oplusE E).lookupTy ⟨some m, c⟩ = ((E.QE.find? m).or (C.E.QE.find? m)).bind (fun I => I.TE.find? c) := by
  simp [Ctx.lookupTy, Env.lookupTy, Ctx.oplusE, Env.plus, FMap.find?_modify]

theorem lookupTy_some (C : Ctx) (m c : String) :
    C.lookupTy ⟨some m, c⟩ = (C.E.QE.find? m).bind (fun I => I.TE.find? c) := rfl

/-- Two contexts with the same lookups of type constructors. -/
def SameTy (C C' : Ctx) : Prop := ∀ lc, C.lookupTy lc = C'.lookupTy lc

theorem sameTy_oplusE_types (C : Ctx) (TE : TyEnv) (VE : ValEnv) : SameTy (C.oplusE ⟨[], TE, VE⟩) (C.oplusTE TE) := by
  rintro ⟨q, c⟩
  cases q with
  | none => rw [lookupTy_oplusE_none, lookupTy_oplusTE_none]
  | some m => rw [lookupTy_oplusE_some, lookupTy_oplusTE_some, lookupTy_some]; simp [FMap.find?]

theorem sameTy_oplusE_ofVE (C : Ctx) (VE : ValEnv) : SameTy (C.oplusE (Env.ofVE VE)) C := by
  rintro ⟨q, c⟩
  cases q with
  | none => rw [lookupTy_oplusE_none]; simp [Env.ofVE]
  | some m => rw [lookupTy_oplusE_some, lookupTy_some]; simp [Env.ofVE]

theorem sameTy_oplusE_plus (C : Ctx) (E1 E2 : Env) :
    SameTy (C.oplusE (E1.plus E2)) ((C.oplusE E1).oplusE E2) := by
  rintro ⟨q, c⟩
  cases q with
  | none =>
    rw [lookupTy_oplusE_none, lookupTy_oplusE_none, lookupTy_oplusE_none]
    simp [Env.plus, FMap.find?_modify, Option.or_assoc]
  | some m =>
    rw [lookupTy_oplusE_some, lookupTy_oplusE_some]
    simp [Env.plus, Ctx.oplusE, FMap.find?_modify, Option.or_assoc]

theorem lookSim_of_same {f : TyName → TyName} {C C' A : Ctx} (hs : SameTy C C') {lc : LongId}
    (h : LookSim f C' A lc) : LookSim f C A lc := by
  intro θ VE hl; rw [hs lc] at hl; exact h θ VE hl

theorem lookSim_plusU {f : TyName → TyName} {C A : Ctx} {lc : LongId} (U U' : List BVar)
    (h : LookSim f C A lc) : LookSim f (C.plusU U) (A.plusU U') lc := h

theorem lookSim_plusVE {f : TyName → TyName} {C A : Ctx} {lc : LongId} (VE : ValEnv)
    (h : LookSim f C A lc) : LookSim f (C.plusVE VE) A lc := h

/-! ## The abstract context -/

/-- The id of the type names that collapse the names outside the basis. -/
def Did : Nat := 1000

/-- Collapse every type name outside T to ⟨Did, arity⟩. -/
def fcol (T : List TyName) (t : TyName) : TyName := if t ∈ T then t else ⟨Did, t.arity⟩

/-- The basis type names the checks below compare with. -/
def fixedNames : List TyName :=
  [tInt, tFloat, tBool, tString, tBytes, tUnit, tValue, tList, tMaybe, tArray, tTuple2, tTuple3, tCmd, tSub,
    tProgram, tNode]

/-- What the proofs need of the collapse. -/
structure Col (B : SBasis) (f : TyName → TyName) : Prop where
  out : ∀ t, t ∉ B.T → f t = ⟨Did, t.arity⟩
  fixed : ∀ t ∈ fixedNames, f t = t

theorem col_fcol (B : SBasis) (h : fixedNames.all (· ∈ B.T) = true) : Col B (fcol B.T) where
  out t ht := by simp [fcol, ht]
  fixed t ht := by
    have := List.all_eq_true.mp h t ht
    simp only [decide_eq_true_eq] at this
    simp [fcol, this]

theorem Col.builtins {B : SBasis} {f : TyName → TyName} (h : Col B f) : FixesBuiltins f :=
  ⟨h.fixed _ (by simp [fixedNames]), h.fixed _ (by simp [fixedNames]), h.fixed _ (by simp [fixedNames])⟩

def mapStr (f : TyName → TyName) (s : TyStr) : TyStr := (mapFcn f s.1, [])

def baseTE (f : TyName → TyName) (C0 : Ctx) : TyEnv := C0.E.TE.map (fun p => (p.1, mapStr f p.2))

def baseQE (f : TyName → TyName) (C0 : Ctx) : FMap ModId IEnv :=
  C0.E.QE.map (fun p => (p.1, (⟨p.2.TE.map (fun q => (q.1, mapStr f q.2)), []⟩ : IEnv)))

/-- The imports' context collapsed, its type environment modified by L. -/
def absCtx (f : TyName → TyName) (C0 : Ctx) (L : TyEnv) : Ctx :=
  ⟨[], [], ⟨baseQE f C0, FMap.modify (baseTE f C0) L, []⟩⟩

/-- The variables of an alias's elaboration (elabTypBind). -/
def aliasVars (tb : BTypBind) : List BVar := seqVars tb.params (bTyExtNames tb.t)

def customsAbs : Option BDatBind → TyEnv
  | none => []
  | some d => d.map fun c => (c.1, ((⟨Did, c.2.1.length⟩ : TyName).toFcn, []))

/-- The aliases elaborated in order, each in the context of the earlier ones. -/
def aliasesAbs (f : TyName → TyName) (C0 : Ctx) : TyEnv → List BTypBind → TyEnv
  | L, [] => L
  | L, tb :: rest =>
    match elabTy ((absCtx f C0 L).plusU (aliasVars tb)) tb.t with
    | some τ => aliasesAbs f C0 (L ++ [(tb.c, (TyFcn.canon ⟨aliasVars tb, τ⟩, []))]) rest
    | none => aliasesAbs f C0 L rest

/-- The type declarations of a module's body: its first item, when that is one. -/
def typesPhrase : Option BTopDec → Option BDatBind × List BTypBind
  | some (.types db tbs) => (db, tbs)
  | some (.seq (.types db tbs) _) => (db, tbs)
  | _ => (none, [])

def localTE (f : TyName → TyName) (C0 : Ctx) (body : Option BTopDec) : TyEnv :=
  aliasesAbs f C0 (customsAbs (typesPhrase body).1) (typesPhrase body).2

/-- The local names are not bound by the imports. -/
def unboundB (C0 : Ctx) (L : TyEnv) : Bool := L.all fun p => (C0.lookupTy ⟨none, p.1⟩).isNone

/-- The invariant of a derivation's context C against the abstract context A. -/
structure Inv (B : SBasis) (f : TyName → TyName) (A C : Ctx) : Prop where
  look : ∀ lc, LookSim f C A lc
  U : C.U = []
  T : ∀ t, t ∈ B.T → t ∈ C.T

theorem Inv.same {B : SBasis} {f : TyName → TyName} {A C C' : Ctx} (h : Inv B f A C') (hs : SameTy C C')
    (hU : C.U = C'.U) (hT : ∀ t, t ∈ C'.T → t ∈ C.T) : Inv B f A C :=
  ⟨fun lc => lookSim_of_same hs (h.look lc), hU.trans h.U, fun t ht => hT t (h.T t ht)⟩

theorem T_oplusE (C : Ctx) (E : Env) : ∀ t, t ∈ C.T → t ∈ (C.oplusE E).T := by
  intro t ht; simp only [Ctx.oplusE]; exact mem_unionL.mpr (.inl ht)

theorem Inv.ofVE {B : SBasis} {f : TyName → TyName} {A C : Ctx} (h : Inv B f A C) (VE : ValEnv) :
    Inv B f A (C.oplusE (Env.ofVE VE)) :=
  ⟨fun lc => lookSim_of_same (sameTy_oplusE_ofVE C VE) (h.look lc), h.U, fun t ht => T_oplusE C _ t (h.T t ht)⟩

theorem inv_base (B : SBasis) (f : TyName → TyName) (C0 : Ctx) (L : TyEnv) (hU : C0.U = [])
    (hT : C0.T = B.T) (hL : unboundB C0 L = true) : Inv B f (absCtx f C0 L) C0 := by
  refine ⟨?_, hU, fun t ht => hT ▸ ht⟩
  rintro ⟨q, c⟩ θ VE hl
  cases q with
  | none =>
    rw [lookupTy_none] at hl
    refine ⟨[], ?_⟩
    simp only [absCtx, Ctx.lookupTy, Env.lookupTy, FMap.find?_modify]
    have hn : FMap.find? L c = none := by
      cases hc : FMap.find? L c with
      | none => rfl
      | some v =>
        exfalso
        have hk : c ∈ L.keys := (FMap.find?_isSome_iff L c).mp (by rw [hc]; rfl)
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
        have := List.all_eq_true.mp hL p hp
        rw [lookupTy_none, hl] at this
        cases this
    rw [hn]
    simp only [baseTE, Option.none_or]
    rw [find?_map_snd (mapStr f) c C0.E.TE, hl]
    rfl
  | some m =>
    rw [lookupTy_some] at hl
    refine ⟨[], ?_⟩
    simp only [absCtx, Ctx.lookupTy, Env.lookupTy, baseQE]
    rw [find?_map_snd (fun I : IEnv => (⟨I.TE.map (fun q => (q.1, mapStr f q.2)), []⟩ : IEnv)) m C0.E.QE]
    cases hm : FMap.find? C0.E.QE m with
    | none => rw [hm] at hl; cases hl
    | some I =>
      rw [hm] at hl
      simp only [Option.bind_some, Option.map_some] at hl ⊢
      rw [find?_map_snd (mapStr f) c I.TE, hl]
      rfl

/-! ## Sorts of the new variables of an annotation -/

/-- Every choice, for each name, of a type variable, a row variable, both, or neither. -/
def assigns : List String → List (List BVar)
  | [] => [[]]
  | s :: ss => (assigns ss).flatMap fun U =>
    [U, .ty (.named s) :: U, .row (.named s) :: U, .ty (.named s) :: .row (.named s) :: U]

def annCands (ty : BTy) : List (List BVar) := assigns (dedupL (bTyNames ty))

theorem assigns_cover (P Q : String → Prop) [DecidablePred P] [DecidablePred Q] :
    ∀ ns : List String, ∃ U ∈ assigns ns, ∀ s,
      (BVar.ty (.named s) ∈ U ↔ s ∈ ns ∧ P s) ∧ (BVar.row (.named s) ∈ U ↔ s ∈ ns ∧ Q s)
  | [] => ⟨[], by simp [assigns], by simp⟩
  | n :: ns => by
    obtain ⟨U0, hU0, h0⟩ := assigns_cover P Q ns
    have key : ∀ U ∈ [U0, .ty (.named n) :: U0, .row (.named n) :: U0, .ty (.named n) :: .row (.named n) :: U0],
        U ∈ assigns (n :: ns) := by
      intro U hU
      simp only [assigns, List.mem_flatMap]
      exact ⟨U0, hU0, hU⟩
    by_cases hp : P n <;> by_cases hq : Q n
    · refine ⟨_, key (.ty (.named n) :: .row (.named n) :: U0) (by simp), fun s => ?_⟩
      have := h0 s
      by_cases e : s = n
      · subst e; simp [hp, hq]
      · simp [e, this]
    · refine ⟨_, key (.ty (.named n) :: U0) (by simp), fun s => ?_⟩
      have := h0 s
      by_cases e : s = n
      · subst e; simp [hp, hq, this]
      · simp [e, this]
    · refine ⟨_, key (.row (.named n) :: U0) (by simp), fun s => ?_⟩
      have := h0 s
      by_cases e : s = n
      · subst e; simp [hp, hq, this]
      · simp [e, this]
    · refine ⟨_, key U0 (by simp), fun s => ?_⟩
      have := h0 s
      by_cases e : s = n
      · subst e; simp [hp, hq, this]
      · simp [e, this]

theorem names_of_newFor {U' : List BVar} {ty : BTy} (h : newForB U' ty [] = true) (v : BVar) (s : String)
    (hv : v ∈ U') (hs : v.name? = some s) : s ∈ bTyNames ty := by
  have hn : s ∈ namesU U' := List.mem_filterMap.mpr ⟨v, hv, hs⟩
  exact (((newFor_of_newForB h).2.1 s).mp hn).1

/-- Every U' an annotation may have agrees, on named variables, with a candidate. -/
theorem annCands_cover {U' : List BVar} {ty : BTy} (h : newForB U' ty [] = true) :
    ∃ U ∈ annCands ty, UEq U' U := by
  obtain ⟨U, hU, hc⟩ := assigns_cover (fun s => BVar.ty (.named s) ∈ U') (fun s => BVar.row (.named s) ∈ U')
    (dedupL (bTyNames ty))
  refine ⟨U, hU, fun s => ⟨?_, ?_⟩⟩
  · rw [(hc s).1, mem_dedupL]
    exact ⟨fun h' => ⟨names_of_newFor h _ s h' rfl, h'⟩, fun h' => h'.2⟩
  · rw [(hc s).2, mem_dedupL]
    exact ⟨fun h' => ⟨names_of_newFor h _ s h' rfl, h'⟩, fun h' => h'.2⟩

theorem uEq_unionL_nil (U V : List BVar) (h : UEq U V) : UEq (unionL [] U) (unionL [] V) :=
  fun s => ⟨by simp only [mem_unionL]; simp [(h s).1], by simp only [mem_unionL]; simp [(h s).2]⟩

theorem uEq_refl (U : List BVar) : UEq U U := fun _ => ⟨Iff.rfl, Iff.rfl⟩

/-! ## Type declarations -/

/-- No alias mentions itself or a later one (Appendix A's order, res:modules-alias-not-recursive). -/
def aliasOrderB : List BTypBind → Bool
  | [] => true
  | tb :: rest =>
    (bTyCons tb.t).all (fun lc => lc.qual.isSome || !((tb :: rest).any (fun tb' => tb'.c == lc.id))) &&
      aliasOrderB rest

def aliasElab (A : Ctx) (tb : BTypBind) : Option Ty := elabTy (A.plusU (aliasVars tb)) tb.t

/-- The alias elaborates in A to the type function A gives it. -/
def aliasOK (A : Ctx) (tb : BTypBind) : Bool :=
  match aliasElab A tb with
  | some τ => decide ((A.lookupTy ⟨none, tb.c⟩).map Prod.fst = some (TyFcn.canon ⟨aliasVars tb, τ⟩))
  | none => false

/-- Some alias does not elaborate in A, and every earlier one is as A has it. -/
def aliasesRefuted (A : Ctx) : List BTypBind → Bool
  | [] => false
  | tb :: rest => (aliasElab A tb).isNone || (aliasOK A tb && aliasesRefuted A rest)

def aliasesAllOK (A : Ctx) (tbs : List BTypBind) : Bool := tbs.all (aliasOK A)

/-- A gives each custom type the collapsed name of its arity. -/
def customsOK (A : Ctx) (db : Option BDatBind) : Bool :=
  (db.getD []).all fun c =>
    decide ((A.lookupTy ⟨none, c.1⟩).map Prod.fst = some (TyName.toFcn ⟨Did, c.2.1.length⟩))

/-- Every constructor's arguments elaborate in A. -/
def consOK (A : Ctx) (db : Option BDatBind) : Bool :=
  (db.getD []).all fun c => c.2.2.all fun k =>
    (elabTyList (A.plusU (seqVars c.2.1 (conBindExtNames c.2.2))) k.2).isSome

theorem typBind_shape (C : Ctx) (tb : BTypBind) (VE1 : ValEnv) (TE1 : TyEnv)
    (h : elabTypBind C tb = some (VE1, TE1)) :
    ∃ τ X, elabTy (C.plusU (aliasVars tb)) tb.t = some τ ∧ TE1 = [(tb.c, (TyFcn.canon ⟨aliasVars tb, τ⟩, X))] := by
  unfold elabTypBind at h
  cases hτ : elabTy (C.plusU (seqVars tb.params (bTyExtNames tb.t))) tb.t with
  | none => rw [hτ] at h; cases h
  | some τ =>
    rw [hτ] at h
    simp only at h
    refine ⟨τ, ?_⟩
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨_, hτ, h.2.symm⟩
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨_, hτ, h.2.symm⟩
          · cases h
        · cases h
      · cases h

theorem typBinds_fold (C : Ctx) : ∀ (seg : List BTypBind) (VEs : List ValEnv) (TEs : List TyEnv) (acc : TyEnv),
    elabTypBinds C seg = some (VEs, TEs) → (seg.map (·.c)).Nodup →
    (∀ k, k ∉ seg.map (·.c) → FMap.find? (TEs.foldl FMap.modify acc) k = FMap.find? acc k) ∧
    (∀ tb ∈ seg, ∃ τ X, elabTy (C.plusU (aliasVars tb)) tb.t = some τ ∧
      FMap.find? (TEs.foldl FMap.modify acc) tb.c = some (TyFcn.canon ⟨aliasVars tb, τ⟩, X))
  | [], VEs, TEs, acc, h, _ => by
    simp only [elabTypBinds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | tb :: rest, VEs, TEs, acc, h, hnd => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE1 TE1 VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨τ, X, hτ, rfl⟩ := typBind_shape C tb VE1 TE1 h1
      simp only [List.map_cons, List.nodup_cons] at hnd
      have ih := typBinds_fold C rest VEs' TEs' (FMap.modify acc [(tb.c, (TyFcn.canon ⟨aliasVars tb, τ⟩, X))]) h2 hnd.2
      simp only [List.foldl_cons]
      refine ⟨fun k hk => ?_, fun tb' htb' => ?_⟩
      · simp only [List.map_cons, List.mem_cons, not_or] at hk
        rw [ih.1 k hk.2, FMap.find?_modify]
        simp [FMap.find?, Ne.symm hk.1]
      · rcases List.mem_cons.mp htb' with rfl | hr
        · refine ⟨τ, X, hτ, ?_⟩
          rw [ih.1 _ hnd.1, FMap.find?_modify]
          simp [FMap.find?]
        · exact ih.2 tb' hr
    · cases h

theorem conBind_ok (C : Ctx) (τ : Ty) : ∀ (cb : BConBind) (VE : ValEnv), elabConBind C τ cb = some VE →
    ∀ y ∈ cb, (elabTyList C y.2).isSome = true
  | [], _, _ => by simp
  | (k, tys) :: rest, VE, h => by
    simp only [elabConBind] at h
    split at h
    · rename_i τs VE' h1 h2
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simp [h1]
      · exact conBind_ok C τ rest VE' h2 y hy
    · cases h

theorem datBind_facts (C : Ctx) (names : String → Option TyName) :
    ∀ (d : BDatBind) (VE' : ValEnv) (TE' : TyEnv), elabDatBind C names d = some (VE', TE') → (d.map (·.1)).Nodup →
    (∀ c, c ∉ d.map (·.1) → FMap.find? TE' c = none) ∧
    (∀ x ∈ d, ∃ (t : TyName) (VEc : ValEnv), FMap.find? TE' x.1 = some (t.toFcn, VEc) ∧ t.arity = x.2.1.length ∧
      ∀ y ∈ x.2.2, (elabTyList (C.plusU (seqVars x.2.1 (conBindExtNames x.2.2))) y.2).isSome = true)
  | [], VE', TE', h, _ => by
    simp only [elabDatBind, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [FMap.find?]
  | (c, ps, cb) :: rest, VE', TE', h, hnd => by
    simp only [elabDatBind] at h
    split at h
    · cases h
    · rename_i t _
      split at h
      · rename_i τs VE'' TE'' h1 h2
        split at h
        · rename_i VEc h3
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [List.map_cons, List.nodup_cons] at hnd
            have ih := datBind_facts C names rest VE'' TE'' h2 hnd.2
            refine ⟨fun k hk => ?_, fun x hx => ?_⟩
            · simp only [List.map_cons, List.mem_cons, not_or] at hk
              rw [FMap.find?_modify, ih.1 k hk.2]
              simp [FMap.find?, Ne.symm hk.1]
            · rcases List.mem_cons.mp hx with rfl | hx
              · refine ⟨t, closVE C.tyvars VEc, ?_, hc.2.1, conBind_ok _ _ cb VEc h3⟩
                rw [FMap.find?_modify, ih.1 c hnd.1]
                simp [FMap.find?]
              · obtain ⟨t', VEc', h1', h2', h3'⟩ := ih.2 x hx
                exact ⟨t', VEc', by rw [FMap.find?_modify, h1']; rfl, h2', h3'⟩
          · cases h
        · cases h
      · cases h

theorem find?_mem_vals {K V : Type} [DecidableEq K] (k : K) (v : V) :
    ∀ l : FMap K V, FMap.find? l k = some v → v ∈ FMap.vals l
  | [], h => by cases h
  | (k', v') :: rest, h => by
    simp only [FMap.find?] at h
    simp only [FMap.vals, List.map_cons, List.mem_cons]
    split at h
    · cases h; exact .inl rfl
    · exact .inr (find?_mem_vals k v rest h)

theorem name?_toFcn (t : TyName) : (TyName.toFcn t).name? = some t := by
  simp [TyFcn.name?, TyName.toFcn]

section types
set_option linter.unusedSectionVars false
variable {B : SBasis} {f : TyName → TyName} (hcol : Col B f) {A : Ctx} (hAU : A.U = [])
include hcol hAU

theorem aliases_inner {Cte : Ctx} (hCU : Cte.U = []) (post : List BTypBind) :
    ∀ todo : List BTypBind,
    (∀ lc : LongId, (lc.qual.isSome = true ∨ lc.id ∉ todo.map (·.c)) → LookSim f Cte A lc) →
    (∀ tb ∈ todo, ∃ τ X, elabTy (Cte.plusU (aliasVars tb)) tb.t = some τ ∧
      Cte.lookupTy ⟨none, tb.c⟩ = some (TyFcn.canon ⟨aliasVars tb, τ⟩, X)) →
    aliasOrderB (todo ++ post) = true →
    (aliasesRefuted A (todo ++ post) = true ∨ aliasesAllOK A (todo ++ post) = true) →
    (aliasesRefuted A (todo ++ post) = true → aliasesRefuted A post = true) ∧
    (aliasesAllOK A (todo ++ post) = true → aliasesAllOK A post = true) ∧ ∀ lc, LookSim f Cte A lc
  | [], hS, _, _, _ => ⟨id, id, fun lc => hS lc (.inr (by simp))⟩
  | tb :: rest, hS, hT, hord, hH => by
    simp only [List.cons_append] at hH hord ⊢
    obtain ⟨τ, X, he, hl⟩ := hT tb (List.mem_cons_self ..)
    simp only [aliasOrderB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hord
    have hsim : ∀ lc ∈ bTyCons tb.t, LookSim f (Cte.plusU (aliasVars tb)) (A.plusU (aliasVars tb)) lc := by
      intro lc hlc
      apply lookSim_plusU
      rcases hord.1 lc hlc with hq | hn
      · exact hS lc (.inl hq)
      · refine hS lc (.inr ?_)
        intro hm
        obtain ⟨tb', htb', he'⟩ := List.mem_map.mp hm
        have : tb' ∈ tb :: (rest ++ post) := by
          rcases List.mem_cons.mp htb' with rfl | h'
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ h')
        exact hn tb' this he'
    have hUeq : UEq (Cte.plusU (aliasVars tb)).U (A.plusU (aliasVars tb)).U := by
      simp only [Ctx.plusU, hCU, hAU]; exact uEq_refl _
    have hea := elabTy_sim f hcol.builtins _ _ hUeq tb.t τ hsim he
    have hel : aliasElab A tb = some (mapTy f τ) := hea
    have hok : aliasOK A tb = true ∧
        (aliasesRefuted A (tb :: (rest ++ post)) = true → aliasesRefuted A (rest ++ post) = true) ∧
        (aliasesAllOK A (tb :: (rest ++ post)) = true → aliasesAllOK A (rest ++ post) = true) := by
      simp only [aliasesRefuted, aliasesAllOK, List.all_cons, hel, Option.isNone_some, Bool.false_or,
        Bool.and_eq_true] at hH ⊢
      rcases hH with h | h
      · exact ⟨h.1, fun h' => h'.2, fun h' => h'.2⟩
      · exact ⟨h.1, fun h' => h'.2, fun h' => h'.2⟩
    have hlook : LookSim f Cte A ⟨none, tb.c⟩ := by
      intro θ VE hθ
      rw [hl] at hθ
      simp only [Option.some.injEq, Prod.mk.injEq] at hθ
      obtain ⟨rfl, rfl⟩ := hθ
      have h1 := hok.1
      simp only [aliasOK, hel, decide_eq_true_eq] at h1
      cases hA : A.lookupTy ⟨none, tb.c⟩ with
      | none => rw [hA] at h1; cases h1
      | some s =>
        rw [hA] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        refine ⟨s.2, ?_⟩
        rw [canon_map]
        have e : mapFcn f ⟨aliasVars tb, τ⟩ = ⟨aliasVars tb, mapTy f τ⟩ := rfl
        rw [e, ← h1]
    have ih := aliases_inner hCU post rest
      (fun lc hlc => by
        obtain ⟨q, c⟩ := lc
        rcases hlc with hq | hn
        · exact hS _ (.inl hq)
        · by_cases e : c = tb.c
          · cases q with
            | none => subst e; exact hlook
            | some m => exact hS _ (.inl rfl)
          · refine hS _ (.inr ?_)
            simp only [List.map_cons, List.mem_cons, not_or]
            exact ⟨e, hn⟩)
      (fun tb' h' => hT tb' (List.mem_cons_of_mem _ h')) hord.2
      (by
        rcases hH with h | h
        · exact .inl (hok.2.1 h)
        · exact .inr (hok.2.2 h))
    exact ⟨fun h => ih.1 (hok.2.1 h), fun h => ih.2.1 (hok.2.2 h), ih.2.2⟩

theorem leaf_core {C : Ctx} (hI : Inv B f A C) {TE TE' : TyEnv} {seg post : List BTypBind}
    {VEs : List ValEnv} {TEs : List TyEnv}
    (hb : elabTypBinds (C.oplusTE TE) seg = some (VEs, TEs))
    (hfind : ∀ c, FMap.find? TE c = (FMap.find? (FMap.plusAll TEs) c).or (FMap.find? TE' c))
    (hTE' : ∀ c θ VEc, FMap.find? TE' c = some (θ, VEc) → ∃ VE'', A.lookupTy ⟨none, c⟩ = some (mapFcn f θ, VE''))
    (hnd : (seg.map (·.c)).Nodup) (hord : aliasOrderB (seg ++ post) = true)
    (hH : aliasesRefuted A (seg ++ post) = true ∨ aliasesAllOK A (seg ++ post) = true) :
    (aliasesRefuted A (seg ++ post) = true → aliasesRefuted A post = true) ∧
    (aliasesAllOK A (seg ++ post) = true → aliasesAllOK A post = true) ∧ ∀ lc, LookSim f (C.oplusTE TE) A lc := by
  have hfold := typBinds_fold (C.oplusTE TE) seg VEs TEs [] hb hnd
  refine aliases_inner hcol hAU (Cte := C.oplusTE TE) hI.U post seg ?_ ?_ hord hH
  · rintro ⟨q, c⟩ hlc
    cases q with
    | some m =>
      intro θ VE h
      rw [lookupTy_oplusTE_some] at h
      exact hI.look _ θ VE h
    | none =>
      have hn : c ∉ seg.map (·.c) := by
        rcases hlc with h | h
        · cases h
        · exact h
      intro θ VE h
      rw [lookupTy_oplusTE_none, hfind] at h
      have hp : FMap.find? (FMap.plusAll TEs) c = none := by
        unfold FMap.plusAll; rw [hfold.1 c hn]; rfl
      rw [hp, Option.none_or] at h
      cases h' : FMap.find? TE' c with
      | some s =>
        rw [h'] at h
        simp only [Option.some_or, Option.some.injEq] at h
        subst h
        exact hTE' c θ VE h'
      | none =>
        rw [h', Option.none_or] at h
        exact hI.look _ θ VE h
  · intro tb htb
    obtain ⟨τ, X, hτ, hf⟩ := hfold.2 tb htb
    refine ⟨τ, X, hτ, ?_⟩
    rw [lookupTy_oplusTE_none, hfind]
    unfold FMap.plusAll
    rw [hf]
    rfl

theorem types_leaf {C : Ctx} (hI : Inv B f A C) {TE : TyEnv} {VE : ValEnv} {db' : Option BDatBind}
    {seg post : List BTypBind}
    (hnd : ((db'.getD []).map (·.1) ++ (seg ++ post).map (·.c)).Nodup)
    (hcu : customsOK A db' = true) (hord : aliasOrderB (seg ++ post) = true)
    (hH : aliasesRefuted A (seg ++ post) = true ∨ aliasesAllOK A (seg ++ post) = true)
    (h : checkTypes C TE VE db' seg = true) :
    (aliasesRefuted A (seg ++ post) = true → aliasesRefuted A post = true) ∧
    (aliasesAllOK A (seg ++ post) = true → aliasesAllOK A post = true) ∧
    (∀ lc, LookSim f (C.oplusTE TE) A lc) ∧ consOK A db' = true := by
  have hnd' := (List.nodup_append.mp hnd)
  have hseg : (seg.map (·.c)).Nodup := by
    have := hnd'.2.1
    rw [List.map_append] at this
    exact (List.nodup_append.mp this).1
  replace h := checkTypes_fix h
  unfold checkTypesFix at h
  cases db' with
  | none =>
    simp only at h
    split at h
    · rename_i VEs TEs hb
      simp only [decide_eq_true_eq] at h
      obtain ⟨_, rfl, _⟩ := h
      have := leaf_core hcol hAU hI (TE' := []) hb (fun c => by simp [FMap.find?]) (fun c θ VEc h => by cases h)
        hseg hord hH
      exact ⟨this.1, this.2.1, this.2.2, rfl⟩
    · cases h
  | some d =>
    simp only at h
    split at h
    · rename_i VE' TE' VEs TEs hd hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hnew, _, hTE, _⟩ := h
      have hdn : (d.map (·.1)).Nodup := hnd'.1
      have hfacts := datBind_facts _ _ d VE' TE' hd hdn
      have hTE' : ∀ c θ VEc, FMap.find? TE' c = some (θ, VEc) →
          ∃ VE'', A.lookupTy ⟨none, c⟩ = some (mapFcn f θ, VE'') := by
        intro c θ VEc hc
        have hcm : c ∈ d.map (·.1) := by
          by_cases hn : c ∈ d.map (·.1)
          · exact hn
          · rw [hfacts.1 c hn] at hc; cases hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcm
        obtain ⟨t, VEt, ht1, ht2, _⟩ := hfacts.2 x hx
        rw [ht1] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have htT : t ∉ C.T := namesNewB_spec C.T TE' hnew _ (find?_mem_vals _ _ TE' ht1) t (name?_toFcn t)
        have hft : f t = ⟨Did, t.arity⟩ := hcol.out t (fun hb => htT (hI.T t hb))
        have hcx := List.all_eq_true.mp hcu x hx
        simp only [decide_eq_true_eq] at hcx
        cases hA : A.lookupTy ⟨none, x.1⟩ with
        | none => rw [hA] at hcx; cases hcx
        | some s =>
          rw [hA] at hcx
          simp only [Option.map_some, Option.some.injEq] at hcx
          refine ⟨s.2, ?_⟩
          rw [toFcn_map f t (by rw [hft]), hft, ht2, ← hcx]
      have hfind : ∀ c, FMap.find? TE c = (FMap.find? (FMap.plusAll TEs) c).or (FMap.find? TE' c) := by
        intro c; rw [← hTE, FMap.find?_modify]
      have hc := leaf_core hcol hAU hI hb hfind hTE' hseg hord hH
      refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
      simp only [consOK, Option.getD_some, List.all_eq_true]
      intro x hx y hy
      obtain ⟨t, VEt, _, _, hcons⟩ := hfacts.2 x hx
      have hs := hcons y hy
      cases he : elabTyList ((C.oplusTE TE).plusU (seqVars x.2.1 (conBindExtNames x.2.2))) y.2 with
      | none => rw [he] at hs; cases hs
      | some τs =>
        have hUeq : UEq ((C.oplusTE TE).plusU (seqVars x.2.1 (conBindExtNames x.2.2))).U
            (A.plusU (seqVars x.2.1 (conBindExtNames x.2.2))).U := by
          simp only [Ctx.plusU, Ctx.oplusTE, hI.U, hAU]; exact uEq_refl _
        rw [elabTyList_sim f hcol.builtins _ _ hUeq y.2 τs (fun lc _ => lookSim_plusU _ _ (hc.2.2 lc)) he]
        rfl
    · cases h

end types

/-! ## Annotations and ports -/

def annFails (A : Ctx) (ty : BTy) : Bool := (annCands ty).all fun U => (elabTy (A.plusU U) ty).isNone

/-- Some annotation of the group elaborates in no derivation. -/
def vbRefuted (A : Ctx) : BValBind → Bool
  | .var _ ann _ rest =>
    (match ann with
     | some ty => annFails A ty
     | none => false) ||
    (match rest with
     | some r => vbRefuted A r
     | none => false)
  | .pat _ _ => false

theorem vbRefuted_var (A : Ctx) (x : Var) (oann : Option BTy) (e : BExp) (orest : Option BValBind) :
    vbRefuted A (.var x oann e orest) = ((oann.map (annFails A)).getD false || (orest.map (vbRefuted A)).getD false) := by
  cases oann <;> cases orest <;> simp [vbRefuted]

/-- The types r:sm-topdec-portout and r:sm-topdec-portin accept. -/
def portShapeB : Ty → Bool
  | .fn τ' (.con [.var α] t) =>
    (decide (t = tCmd) && portB τ') ||
    (match τ' with
     | .fn τ'' (.var α') => decide (t = tSub) && decide (α' = α) && portB τ''
     | _ => false)
  | _ => false

def portFails (A : Ctx) (ty : BTy) : Bool :=
  (annCands ty).all fun U =>
    match elabTy (A.plusU U) ty with
    | some τ => !portShapeB τ
    | none => true

mutual
theorem portB_map {f : TyName → TyName} (hfix : ∀ t ∈ fixedNames, f t = t) :
    ∀ τ, portB τ = true → portB (mapTy f τ) = true
  | .con [] t, h => by
    simp only [portB, Bool.or_eq_true, beq_iff_eq] at h
    have hf : f t = t := by
      apply hfix
      rcases h with ((((((h | h) | h) | h) | h) | h) | h) <;> subst h <;> simp [fixedNames]
    simp only [mapTy, mapTys, hf, portB, Bool.or_eq_true, beq_iff_eq]
    exact h
  | .con [τ] t, h => by
    simp only [portB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    have hf : f t = t := by
      apply hfix
      rcases h.1 with ((h | h) | h) <;> subst h <;> simp [fixedNames]
    simp only [mapTy, mapTys, hf, portB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    exact ⟨h.1, portB_map hfix τ h.2⟩
  | .con [τ1, τ2] t, h => by
    simp only [portB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h
    simp only [mapTy, mapTys, hfix tTuple2 (by simp [fixedNames]), portB, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨trivial, portB_map hfix τ1 h1⟩, portB_map hfix τ2 h2⟩
  | .con [τ1, τ2, τ3] t, h => by
    simp only [portB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, h1⟩, h2⟩, h3⟩ := h
    simp only [mapTy, mapTys, hfix tTuple3 (by simp [fixedNames]), portB, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨trivial, portB_map hfix τ1 h1⟩, portB_map hfix τ2 h2⟩, portB_map hfix τ3 h3⟩
  | .con (_ :: _ :: _ :: _ :: _) _, h => by simp [portB] at h
  | .record ρ none, h => by
    simp only [portB] at h
    simp only [mapTy, portB]
    exact portRowB_map hfix ρ h
  | .record _ (some _), h => by simp [portB] at h
  | .var _, h => by simp [portB] at h
  | .fn _ _, h => by simp [portB] at h
theorem portRowB_map {f : TyName → TyName} (hfix : ∀ t ∈ fixedNames, f t = t) :
    ∀ ρ, portRowB ρ = true → portRowB (mapRow f ρ) = true
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [portRowB, Bool.and_eq_true] at h
    simp only [mapRow, portRowB, Bool.and_eq_true]
    exact ⟨portB_map hfix τ h.1, portRowB_map hfix rest h.2⟩
end

theorem portShapeB_map {f : TyName → TyName} (hfix : ∀ t ∈ fixedNames, f t = t) (τ : Ty)
    (h : portShapeB τ = true) : portShapeB (mapTy f τ) = true := by
  unfold portShapeB at h
  split at h
  · rename_i τ' α t
    have hm : mapTy f (.fn τ' (.con [.var α] t)) = .fn (mapTy f τ') (.con [.var α] (f t)) := by
      simp [mapTy, mapTys]
    rw [hm]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, hp⟩ | h
    · simp [portShapeB, hfix tCmd (by simp [fixedNames]), portB_map hfix τ' hp]
    · split at h
      · rename_i τ'' α'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, rfl⟩, hp⟩ := h
        simp [portShapeB, mapTy, hfix tSub (by simp [fixedNames]), portB_map hfix τ'' hp]
      · cases h
  · cases h

theorem elabPort_shape {C : Ctx} {x : Var} {ty : BTy} {U : List BVar} {r : Env × PortEnv}
    (h : elabPort C x ty U = some r) :
    newForB U ty C.U = true ∧ (∃ τ, elabTy (C.plusU U) ty = some τ ∧ portShapeB τ = true) ∧
      ∃ s PE, r = (Env.ofVE [(x, s)], PE) := by
  unfold elabPort at h
  split at h
  · rename_i hn
    split at h
    · rename_i τ' α t he
      split at h
      · rename_i hc
        cases h
        exact ⟨hn, ⟨_, he, by simp [portShapeB, hc.1, hc.2]⟩, _, _, rfl⟩
      · split at h
        · rename_i τ'' α'
          split at h
          · rename_i hc
            cases h
            refine ⟨hn, ⟨_, he, ?_⟩, _, _, rfl⟩
            simp [portShapeB, hc.1, hc.2.1, hc.2.2]
          · cases h
        · cases h
    · cases h
  · cases h

section ann
set_option linter.unusedSectionVars false
variable {B : SBasis} {f : TyName → TyName} (hcol : Col B f) {A : Ctx} (hAU : A.U = [])
include hcol hAU

/-- An annotation elaborated in a derivation's context elaborates, collapsed, at a candidate. -/
theorem ann_sim {C' : Ctx} (hL : ∀ lc, LookSim f C' A lc) (hU : C'.U = []) {ty : BTy} {U' : List BVar}
    {τ : Ty} (hnew : newForB U' ty C'.U = true) (hel : elabTy (C'.plusU U') ty = some τ) :
    ∃ U ∈ annCands ty, elabTy (A.plusU U) ty = some (mapTy f τ) := by
  rw [hU] at hnew
  obtain ⟨U'', hU'', hUeq⟩ := annCands_cover hnew
  refine ⟨U'', hU'', ?_⟩
  exact elabTy_sim f hcol.builtins (C'.plusU U') (A.plusU U'')
    (by simp only [Ctx.plusU, hU, hAU]; exact uEq_unionL_nil _ _ hUeq) ty τ
    (fun lc _ => lookSim_plusU _ _ (hL lc)) hel

theorem vb_not_refuted {C' : Ctx} (hL : ∀ lc, LookSim f C' A lc) (hU : C'.U = []) :
    ∀ avb : AValBind, checkValBind C' avb = true → vbRefuted A avb.erase = false
  | .var x ann τ e rest, h => by
    simp only [checkValBind, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hann, _⟩, _⟩, hrest⟩ := h
    simp only [AValBind.erase, vbRefuted_var, Bool.or_eq_false_iff]
    constructor
    · cases ann with
      | none => rfl
      | some p =>
        obtain ⟨ty, U'⟩ := p
        simp only [Option.map_some]
        simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq] at hann
        obtain ⟨⟨hnew, hel⟩, _⟩ := hann
        obtain ⟨U'', hU'', hs⟩ := ann_sim hcol hAU hL hU hnew hel
        cases hc : annFails A ty with
        | false => rfl
        | true =>
          have := List.all_eq_true.mp hc U'' hU''
          simp [hs] at this
    · cases rest with
      | none => rfl
      | some r =>
        simp only [AValBind.eraseOpt, Option.map_some, Option.getD_some]
        exact vb_not_refuted hL hU r hrest
  | .pat _ _, _ => by simp [AValBind.erase, vbRefuted]

theorem port_not_fails {C : Ctx} (hI : Inv B f A C) {x : Var} {ty : BTy} {U : List BVar} {r : Env × PortEnv}
    (h : elabPort C x ty U = some r) : portFails A ty = false := by
  obtain ⟨hnew, ⟨τ, hel, hsh⟩, _⟩ := elabPort_shape h
  obtain ⟨U'', hU'', hs⟩ := ann_sim hcol hAU hI.look hI.U hnew hel
  cases hc : portFails A ty with
  | false => rfl
  | true =>
    have := List.all_eq_true.mp hc U'' hU''
    simp only [hs, Bool.not_eq_true'] at this
    rw [portShapeB_map hcol.fixed τ hsh] at this
    cases this

end ann

/-! ## The module's declarations -/

/-- The conditions on a type-declaration phrase the simulation needs. -/
def typesNodeOK (A : Ctx) (db : Option BDatBind) (tbs : List BTypBind) : Bool :=
  decide (((db.getD []).map (·.1) ++ tbs.map (·.c)).Nodup) && customsOK A db && aliasOrderB tbs

/-- Every derivation of the phrase keeps the invariant. -/
def preserves (A : Ctx) : BTopDec → Bool
  | .types db tbs => typesNodeOK A db tbs && aliasesAllOK A tbs
  | .value _ => true
  | .port _ _ => true
  | .seq d1 d2 => preserves A d1 && preserves A d2

/-- No derivation of the phrase checks. -/
def refTop (A : Ctx) : BTopDec → Bool
  | .types db tbs => typesNodeOK A db tbs && (aliasesRefuted A tbs || (aliasesAllOK A tbs && !consOK A db))
  | .value vb => vbRefuted A vb
  | .port _ ty => portFails A ty
  | .seq d1 d2 => refTop A d1 || (preserves A d1 && refTop A d2)

section chain
set_option linter.unusedSectionVars false
variable {B : SBasis} {f : TyName → TyName} (hcol : Col B f) {A : Ctx} (hAU : A.U = [])
include hcol hAU

theorem types_top {a : ATopDec} {C : Ctx} {E : Env} {PE : PortEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (he : a.erase = .types db tbs) (hI : Inv B f A C) (hn : typesNodeOK A db tbs = true)
    (hH : aliasesRefuted A tbs = true ∨ aliasesAllOK A tbs = true) (h : checkTopDec C a = some (E, PE)) :
    aliasesRefuted A tbs = false ∧ Inv B f A (C.oplusE E) ∧ consOK A db = true := by
  simp only [typesNodeOK, Bool.and_eq_true, decide_eq_true_eq] at hn
  cases a with
  | types TE VE db'' tbs'' =>
    simp only [ATopDec.erase, BTopDec.types.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl := types_leaf hcol hAU (post := []) hI (by simpa using hn.1.1) hn.1.2 (by simpa using hn.2)
        (by simpa using hH) hc
      refine ⟨?_, ⟨fun lc => lookSim_of_same (sameTy_oplusE_types C _ _) (hl.2.2.1 lc), hI.U,
        fun t ht => T_oplusE C _ t (hI.T t ht)⟩, hl.2.2.2⟩
      cases hr : aliasesRefuted A tbs'' with
      | false => rfl
      | true => have := hl.1 (by simpa using hr); simp [aliasesRefuted] at this
    · cases h
  | value _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at he

theorem pres : ∀ (a : ATopDec) (C : Ctx) (E : Env) (PE : PortEnv), Inv B f A C →
    preserves A a.erase = true → checkTopDec C a = some (E, PE) → Inv B f A (C.oplusE E)
  | .value VE vb, C, E, PE, hI, _, h => by
    simp only [checkTopDec] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hI.ofVE _
    · cases h
  | .types TE VE db tbs, C, E, PE, hI, hp, h => by
    simp only [ATopDec.erase, preserves, Bool.and_eq_true] at hp
    exact (types_top hcol hAU rfl hI hp.1 (.inr hp.2) h).2.1
  | .port x ty U, C, E, PE, hI, _, h => by
    obtain ⟨_, _, s, PE', hr⟩ := elabPort_shape h
    simp only [checkTopDec, hr] at h
    cases hr
    exact hI.ofVE _
  | .seq a1 a2, C, E, PE, hI, hp, h => by
    simp only [ATopDec.erase, preserves, Bool.and_eq_true] at hp
    simp only [checkTopDec] at h
    cases h1 : checkTopDec C a1 with
    | none => rw [h1] at h; simp at h
    | some r1 =>
      obtain ⟨E1, PE1⟩ := r1
      rw [h1] at h
      simp only at h
      cases h2 : checkTopDec (C.oplusE E1) a2 with
      | none => rw [h2] at h; simp at h
      | some r2 =>
        obtain ⟨E2, PE2⟩ := r2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih1 := pres a1 C E1 PE1 hI hp.1 h1
        have ih2 := pres a2 (C.oplusE E1) E2 PE2 ih1 hp.2 h2
        exact ⟨fun lc => lookSim_of_same (sameTy_oplusE_plus C E1 E2) (ih2.look lc), hI.U,
          fun t ht => T_oplusE C _ t (hI.T t ht)⟩

theorem ref : ∀ (a : ATopDec) (C : Ctx), Inv B f A C → refTop A a.erase = true → checkTopDec C a = none
  | .value VE vb, C, hI, hr => by
    simp only [ATopDec.erase, refTop] at hr
    simp only [checkTopDec]
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      have := vb_not_refuted hcol hAU (C' := C.plusVE VE) (fun lc => lookSim_plusVE VE (hI.look lc)) hI.U vb hc.1.1
      rw [hr] at this; cases this
    · rfl
  | .types TE VE db tbs, C, hI, hr => by
    cases h : checkTopDec C (.types TE VE db tbs) with
    | none => rfl
    | some r =>
      obtain ⟨E, PE⟩ := r
      simp only [ATopDec.erase, refTop, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hr
      have hH : aliasesRefuted A tbs = true ∨ aliasesAllOK A tbs = true := by
        rcases hr.2 with h' | h'
        · exact .inl h'
        · exact .inr h'.1
      have ht := types_top hcol hAU rfl hI hr.1 hH h
      rcases hr.2 with h' | h'
      · rw [ht.1] at h'; cases h'
      · rw [ht.2.2] at h'; cases h'.2
  | .port x ty U, C, hI, hr => by
    simp only [ATopDec.erase, refTop] at hr
    cases h : elabPort C x ty U with
    | none => simp [checkTopDec, h]
    | some r => rw [port_not_fails hcol hAU hI h] at hr; cases hr
  | .seq a1 a2, C, hI, hr => by
    simp only [ATopDec.erase, refTop, Bool.or_eq_true, Bool.and_eq_true] at hr
    simp only [checkTopDec]
    rcases hr with h1 | ⟨hp, h2⟩
    · rw [ref a1 C hI h1]
    · cases hc1 : checkTopDec C a1 with
      | none => rfl
      | some r1 =>
        obtain ⟨E1, PE1⟩ := r1
        simp only
        rw [ref a2 (C.oplusE E1) (pres hcol hAU a1 C E1 PE1 hI hp hc1) h2]

end chain

/-! ## The type of `main` -/

/-- A head no type of Chapter 9 has (a variable is not a head). -/
def badHeadB : Ty → Bool
  | .var _ => false
  | .con as t => !(decide (t = tProgram) && as.length == 3) && !(decide (t = tNode) && as.length == 1)
  | _ => true

theorem applyList_length (S : Subst) : ∀ (as as' : List Ty), S.applyList as = some as' → as'.length = as.length
  | [], as', h => by simp [Subst.applyList] at h; subst h; rfl
  | τ :: rest, as', h => by
    simp only [Subst.applyList] at h
    split at h
    · rename_i τ' r' _ h2
      cases h
      simp [applyList_length S rest r' h2]
    · cases h

theorem badHead_apply (S : Subst) (τ : Ty) (h : badHeadB τ = true) : badHeadB ((S.apply τ).getD τ) = true := by
  cases τ with
  | var a => simp [badHeadB] at h
  | fn a b =>
    simp only [Subst.apply]
    split <;> simp [badHeadB]
  | record ρ tl =>
    cases tl with
    | none => simp only [Subst.apply]; split <;> simp [badHeadB]
    | some e =>
      simp only [Subst.apply]
      split
      · simp [badHeadB]
      · split
        · simp [badHeadB]
        · split <;> simp [badHeadB]
  | con as t =>
    simp only [Subst.apply]
    split
    · rename_i as' h'
      simp only [Option.getD_some]
      simp only [badHeadB] at h ⊢
      rw [applyList_length S as as' h']
      exact h
    · simpa using h

theorem badHead_canon (σ : Scheme) (h : badHeadB σ.body = true) : badHeadB (Scheme.canon σ).body = true := by
  unfold Scheme.canon
  generalize renumber true 0 (canonVars σ.bound σ.body) = r
  obtain ⟨S, bs⟩ := r
  exact badHead_apply S σ.body h

theorem badHead_map {f : TyName → TyName} (hP : f tProgram = tProgram) (hN : f tNode = tNode) (τ : Ty)
    (h : badHeadB (mapTy f τ) = true) : badHeadB τ = true := by
  cases τ with
  | var a => simp [mapTy, badHeadB] at h
  | fn a b => rfl
  | record ρ tl => rfl
  | con as t =>
    simp only [mapTy, mapTys_eq, badHeadB, List.length_map, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    by_cases hp : t = tProgram
    · subst hp; rw [hP] at h; simpa using h
    · by_cases hn : t = tNode
      · subst hn; rw [hN] at h; simpa using h
      · simp [hp, hn]

theorem not_mainOK {E : Env} (h : ∃ σ st, FMap.find? E.VE "main" = some (σ, st) ∧ badHeadB σ.body = true) :
    ¬ MainOK E := by
  rintro ⟨σ, hf, hm⟩
  obtain ⟨σ', st, hf', hb⟩ := h
  rw [hf] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf'
  obtain ⟨rfl, _⟩ := hf'
  rcases hm with ⟨τ1, τ2, τ3, hb', _⟩ | ⟨τ, hd⟩
  · rw [hb'] at hb; simp [badHeadB] at hb
  · have key : ∀ S : Subst, (S.apply σ.body).getD σ.body ≠ .con [τ] tNode := fun S e => by
      have := badHead_apply S σ.body hb
      rw [e] at this
      simp [badHeadB] at this
    unfold dflt at hd
    exact key _ hd

mutual
/-- Every type a derivation gives the expression has a bad head: a lambda, `[]`, unit, a tuple, a
    record, through parentheses and `let`. -/
def forcedBad : BExp → Bool
  | .atexp a => forcedBadAt a
  | .lam _ _ => true
  | _ => false
def forcedBadAt : BAtExp → Bool
  | .nil => true
  | .unit => true
  | .tuple _ _ _ => true
  | .record _ => true
  | .paren e => forcedBad e
  | .letE _ e => forcedBad e
  | _ => false
end

mutual
theorem forcedBad_sound : ∀ (C : Ctx) (e : AExp), checkExpS C e = true → forcedBad e.erase = true →
    badHeadB e.ty = true
  | C, .atexp a, h, hf => by
    simp only [checkExpS] at h
    simp only [AExp.erase, forcedBad] at hf
    simp only [AExp.ty]
    exact forcedBadAt_sound C a h hf
  | _, .lam _ _, _, _ => by simp [AExp.ty, badHeadB]
  | _, .app _ _, _, hf => by simp [AExp.erase, forcedBad] at hf
  | _, .caseE _ _, _, hf => by simp [AExp.erase, forcedBad] at hf
theorem forcedBadAt_sound : ∀ (C : Ctx) (a : AAtExp), checkAtExp C a = true → forcedBadAt a.erase = true →
    badHeadB a.ty = true
  | _, .nil τ, h, _ => by
    simp only [checkAtExp] at h
    simp only [AAtExp.ty]
    unfold isListTy at h
    split at h
    · rename_i x t
      simp only [beq_iff_eq] at h
      subst h
      simp [badHeadB, tList, tProgram, tNode]
    · cases h
  | _, .unit, _, _ => by simp [AAtExp.ty, badHeadB, tUnitTy, tUnit, tProgram, tNode]
  | _, .tuple _ _ e3, _, _ => by
    simp only [AAtExp.ty]
    cases AExp.tyOpt e3 <;> simp [tupleTy, badHeadB, tTuple2, tTuple3, tProgram, tNode]
  | _, .record _, _, _ => by simp [AAtExp.ty, badHeadB]
  | C, .paren e, h, hf => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, forcedBadAt] at hf
    simp only [AAtExp.ty]
    exact forcedBad_sound C e h hf
  | C, .letE d e, h, hf => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [AAtExp.erase, forcedBadAt] at hf
    simp only [AAtExp.ty]
    exact forcedBad_sound _ e h.2 hf
  | _, .scon _ _, _, hf => by simp [AAtExp.erase, forcedBadAt] at hf
  | _, .var _ _ _, _, hf => by simp [AAtExp.erase, forcedBadAt] at hf
  | _, .con _ _ _, _, hf => by simp [AAtExp.erase, forcedBadAt] at hf
  | _, .op _ _ _, _, hf => by simp [AAtExp.erase, forcedBadAt] at hf
  | _, .update _ _ _ _, _, hf => by simp [AAtExp.erase, forcedBadAt] at hf
end

/-- Every type an annotation elaborates to, at every sort of its new variables, has a bad head. -/
def annHeadBad (A : Ctx) (ty : BTy) : Bool :=
  (annCands ty).all fun U =>
    match elabTy (A.plusU U) ty with
    | some τ => badHeadB τ
    | none => true

def vbNoMain : BValBind → Bool
  | .var x _ _ rest =>
    x != "main" &&
    (match rest with
     | some r => vbNoMain r
     | none => true)
  | .pat _ _ => false

/-- The group binds `main` once, with a bad head. -/
def vbMainBad (A : Ctx) : BValBind → Bool
  | .var x ann e rest =>
    (x == "main" &&
      (match rest with
       | some r => vbNoMain r
       | none => true) &&
      (match ann with
       | some ty => annHeadBad A ty
       | none => forcedBad e)) ||
    (x != "main" &&
      (match rest with
       | some r => vbMainBad A r
       | none => false))
  | .pat _ _ => false

theorem vbNoMain_var (x : Var) (oann : Option BTy) (e : BExp) (orest : Option BValBind) :
    vbNoMain (.var x oann e orest) = (x != "main" && (orest.map vbNoMain).getD true) := by
  cases orest <;> simp [vbNoMain]

theorem vbMainBad_var (A : Ctx) (x : Var) (oann : Option BTy) (e : BExp) (orest : Option BValBind) :
    vbMainBad A (.var x oann e orest) =
      ((x == "main" && (orest.map vbNoMain).getD true && (oann.map (annHeadBad A)).getD (forcedBad e)) ||
        (x != "main" && (orest.map (vbMainBad A)).getD false)) := by
  cases oann <;> cases orest <;> simp [vbMainBad]

def noMain : BTopDec → Bool
  | .value vb => vbNoMain vb
  | .port x _ => x != "main"
  | .types _ _ => false
  | .seq d1 d2 => noMain d1 && noMain d2

/-- Every derivation's environment binds `main` with a bad head. -/
def mainRef (A : Ctx) : BTopDec → Bool
  | .value vb => vbMainBad A vb
  | .seq d1 d2 => (preserves A d1 && mainRef A d2) || (mainRef A d1 && noMain d2)
  | _ => false

theorem ve_var (x : Var) (ann : Option (BTy × List BVar)) (τ : Ty) (e : AExp) (rest : Option AValBind) (k : String) :
    FMap.find? (AValBind.ve (.var x ann τ e rest)) k =
      ((rest.map AValBind.ve).getD [] |>.find? k).or
        (FMap.find? [(x, (if ann.isSome then annScheme (annU ann) τ else mono τ, IdStatus.v))] k) := by
  cases rest <;> simp [AValBind.ve, FMap.find?_modify]

theorem vb_noMain : ∀ avb : AValBind, vbNoMain avb.erase = true → FMap.find? avb.ve "main" = none
  | .var x ann τ e rest, h => by
    simp only [AValBind.erase, vbNoMain_var, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [ve_var]
    have hx : FMap.find? [(x, (if ann.isSome then annScheme (annU ann) τ else mono τ, IdStatus.v))] "main" = none := by
      simp [FMap.find?, h.1]
    rw [hx]
    cases rest with
    | none => rfl
    | some r =>
      simp only [AValBind.eraseOpt, Option.map_some, Option.getD_some] at h ⊢
      rw [vb_noMain r h.2]; rfl
  | .pat _ _, h => by simp [AValBind.erase, vbNoMain] at h

section main
set_option linter.unusedSectionVars false
variable {B : SBasis} {f : TyName → TyName} (hcol : Col B f) {A : Ctx} (hAU : A.U = [])
include hcol hAU

theorem vb_mainBad {C' : Ctx} (hL : ∀ lc, LookSim f C' A lc) (hU : C'.U = []) :
    ∀ avb : AValBind, checkValBind C' avb = true → vbMainBad A avb.erase = true →
      ∃ sch, FMap.find? avb.ve "main" = some (sch, .v) ∧ badHeadB sch.body = true
  | .var x ann τ e rest, h, hm => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hann, hexp⟩, hty⟩, hrest⟩ := h
    simp only [AValBind.erase, vbMainBad_var, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq] at hm
    rw [ve_var]
    rcases hm with ⟨⟨rfl, hnm⟩, hb⟩ | ⟨_, hr⟩
    · have hrn : ((rest.map AValBind.ve).getD [] |>.find? "main") = none := by
        cases rest with
        | none => rfl
        | some r =>
          simp only [AValBind.eraseOpt, Option.map_some, Option.getD_some] at hnm ⊢
          exact vb_noMain r hnm
      rw [hrn]
      simp only [FMap.find?, ite_true, Option.none_or]
      refine ⟨_, rfl, ?_⟩
      cases ann with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ite_false, mono]
        simp only [Option.map_none, Option.getD_none] at hb
        rw [← hty]
        exact forcedBad_sound _ e hexp hb
      | some p =>
        obtain ⟨ty, U'⟩ := p
        simp only [Option.isSome_some, ite_true, annScheme, annU]
        apply badHead_canon
        simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq] at hann
        obtain ⟨⟨hnew, hel⟩, _⟩ := hann
        obtain ⟨U'', hU'', hs⟩ := ann_sim hcol hAU hL hU hnew hel
        simp only [Option.map_some, Option.getD_some, annHeadBad, List.all_eq_true] at hb
        have := hb U'' hU''
        rw [hs] at this
        exact badHead_map (hcol.fixed _ (by simp [fixedNames])) (hcol.fixed _ (by simp [fixedNames])) τ this
    · cases rest with
      | none => simp [AValBind.eraseOpt] at hr
      | some r =>
        simp only [AValBind.eraseOpt, Option.map_some, Option.getD_some] at hr
        replace hrest : checkValBind C' r = true := hrest
        obtain ⟨sch, hs, hb⟩ := vb_mainBad hL hU r hrest hr
        refine ⟨sch, ?_, hb⟩
        simp [hs]
  | .pat _ _, _, hm => by simp [AValBind.erase, vbMainBad] at hm

theorem no_main : ∀ (a : ATopDec) (C : Ctx) (E : Env) (PE : PortEnv), noMain a.erase = true →
    checkTopDec C a = some (E, PE) → FMap.find? E.VE "main" = none
  | .value VE vb, C, E, PE, hn, h => by
    simp only [ATopDec.erase, noMain] at hn
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      replace hc := hc.1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Env.ofVE, closGroup, FMap.mapV]
      rw [find?_map_key, ← hc.2, vb_noMain vb hn]
      rfl
    · cases h
  | .types _ _ _ _, _, _, _, hn, _ => by simp [ATopDec.erase, noMain] at hn
  | .port x ty U, C, E, PE, hn, h => by
    simp only [ATopDec.erase, noMain, bne_iff_ne, ne_eq] at hn
    replace h : elabPort C x ty U = some (E, PE) := h
    obtain ⟨_, _, s, PE', hr⟩ := elabPort_shape h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp [Env.ofVE, FMap.find?, hn]
  | .seq a1 a2, C, E, PE, hn, h => by
    simp only [ATopDec.erase, noMain, Bool.and_eq_true] at hn
    simp only [checkTopDec] at h
    cases h1 : checkTopDec C a1 with
    | none => rw [h1] at h; simp at h
    | some r1 =>
      obtain ⟨E1, PE1⟩ := r1
      rw [h1] at h
      simp only at h
      cases h2 : checkTopDec (C.oplusE E1) a2 with
      | none => rw [h2] at h; simp at h
      | some r2 =>
        obtain ⟨E2, PE2⟩ := r2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Env.plus, FMap.find?_modify]
        rw [no_main a1 C E1 PE1 hn.1 h1, no_main a2 _ E2 PE2 hn.2 h2]
        rfl

theorem main_bad : ∀ (a : ATopDec) (C : Ctx) (E : Env) (PE : PortEnv), Inv B f A C →
    mainRef A a.erase = true → checkTopDec C a = some (E, PE) →
    ∃ σ st, FMap.find? E.VE "main" = some (σ, st) ∧ badHeadB σ.body = true
  | .value VE vb, C, E, PE, hI, hm, h => by
    simp only [ATopDec.erase, mainRef] at hm
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      replace hc := hc.1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨sch, hs, hb⟩ := vb_mainBad hcol hAU (C' := C.plusVE VE) (fun lc => lookSim_plusVE VE (hI.look lc))
        hI.U vb hc.1 hm
      simp only [Env.ofVE, closGroup, FMap.mapV]
      rw [find?_map_key, ← hc.2, hs]
      exact ⟨_, _, rfl, badHead_canon _ hb⟩
    · cases h
  | .types _ _ _ _, _, _, _, _, hm, _ => by simp [ATopDec.erase, mainRef] at hm
  | .port _ _ _, _, _, _, _, hm, _ => by simp [ATopDec.erase, mainRef] at hm
  | .seq a1 a2, C, E, PE, hI, hm, h => by
    simp only [ATopDec.erase, mainRef, Bool.or_eq_true, Bool.and_eq_true] at hm
    simp only [checkTopDec] at h
    cases h1 : checkTopDec C a1 with
    | none => rw [h1] at h; simp at h
    | some r1 =>
      obtain ⟨E1, PE1⟩ := r1
      rw [h1] at h
      simp only at h
      cases h2 : checkTopDec (C.oplusE E1) a2 with
      | none => rw [h2] at h; simp at h
      | some r2 =>
        obtain ⟨E2, PE2⟩ := r2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Env.plus, FMap.find?_modify]
        rcases hm with ⟨hp, hm2⟩ | ⟨hm1, hn2⟩
        · obtain ⟨σ, st, hs, hb⟩ := main_bad a2 (C.oplusE E1) E2 PE2 (pres hcol hAU a1 C E1 PE1 hI hp h1) hm2 h2
          exact ⟨σ, st, by rw [hs]; rfl, hb⟩
        · obtain ⟨σ, st, hs, hb⟩ := main_bad a1 C E1 PE1 hI hm1 h1
          exact ⟨σ, st, by rw [no_main hcol hAU a2 _ E2 PE2 hn2 h2, hs]; rfl, hb⟩

end main

theorem importCtx_UT {B : SBasis} {imps : List BImport} {C0 : Ctx} (h : importCtx B imps = some C0) :
    C0.U = [] ∧ C0.T = B.T := by
  unfold importCtx at h
  cases he : elabImports B π0 (defaultImports ++ imps) with
  | none => rw [he] at h; cases h
  | some π =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem resultIn_check {B : SBasis} {C : Ctx} {a : AModule} {B' : SBasis} {E : Env}
    (h : a.resultIn B C = some (B', E)) : ∃ PE, checkTopDecOpt C a.body = some (E, PE) := by
  unfold AModule.resultIn at h
  split at h
  · cases h
  · rename_i E' PE' hc
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨_, hc⟩

theorem body_erase {a : AModule} {m : BModule} {d : BTopDec} (he : a.erase = m) (hd : m.body = some d) :
    ∃ ad, a.body = some ad ∧ ad.erase = d := by
  have hb : a.body.map ATopDec.erase = some d := by rw [← hd, ← he]; rfl
  cases h : a.body with
  | none => rw [h] at hb; cases hb
  | some ad => rw [h] at hb; simp only [Option.map_some, Option.some.injEq] at hb; exact ⟨ad, rfl, hb⟩

theorem imports_erase {a : AModule} {m : BModule} (he : a.erase = m) : a.imports = m.imports := by
  rw [← he]; rfl

end StandardElm.Stat.RTypes

namespace StandardElm.Stat
open StandardElm.Stat.RTypes

/-- Some type expression of the first module (an alias, a constructor's argument, a top-level
    annotation, a port) elaborates in no derivation. -/
def typesFailB (B : SBasis) (sp : Src.SProgram) : Bool :=
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | m :: _ =>
    match importCtx B m.imports, m.body with
    | some C0, some d =>
      let L := localTE (fcol B.T) C0 (some d)
      fixedNames.all (· ∈ B.T) && unboundB C0 L && refTop (absCtx (fcol B.T) C0 L) d
    | _, _ => false
  | [] => false

theorem not_legal_of_typesFailB {B : SBasis} {sp : Src.SProgram} (h : typesFailB B sp = true) :
    ¬ LegalProgram B sp := by
  unfold typesFailB at h
  split at h
  · rename_i m rest hms
    split at h
    · rename_i C0 d hC hd
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hfix, hun⟩, hr⟩ := h
      refine not_legal_of_noDeriv hms ?_
      intro a he
      have hC' : importCtx B a.imports = some C0 := by rw [imports_erase he]; exact hC
      obtain ⟨ad, hb, had⟩ := body_erase he hd
      obtain ⟨hU, hT⟩ := importCtx_UT hC
      have hI := inv_base B (fcol B.T) C0 _ hU hT hun
      have hn := ref (col_fcol B hfix) rfl ad C0 hI (had ▸ hr)
      unfold checkModule
      rw [AModule.result_of_ctx hC']
      unfold AModule.resultIn
      simp [checkTopDecOpt, hb, hn]
    · cases h
  · cases h

/-- The one module gives `main` a type with a head other than `Program` and `Node` (a function, a
    record, another constructed type) in every derivation. -/
def mainFailB (B : SBasis) (sp : Src.SProgram) : Bool :=
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | [m] =>
    match importCtx B m.imports, m.body with
    | some C0, some d =>
      let L := localTE (fcol B.T) C0 (some d)
      fixedNames.all (· ∈ B.T) && unboundB C0 L && mainRef (absCtx (fcol B.T) C0 L) d
    | _, _ => false
  | _ => false

theorem not_legal_of_mainFailB {B : SBasis} {sp : Src.SProgram} (h : mainFailB B sp = true) :
    ¬ LegalProgram B sp := by
  unfold mainFailB at h
  split at h
  · rename_i m hms
    split at h
    · rename_i C0 d hC hd
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hfix, hun⟩, hr⟩ := h
      refine not_legal_of_main hms ?_
      intro a B' E he hres
      have hC' : importCtx B a.imports = some C0 := by rw [imports_erase he]; exact hC
      rw [AModule.result_of_ctx hC'] at hres
      obtain ⟨PE, hc⟩ := resultIn_check hres
      obtain ⟨ad, hb, had⟩ := body_erase he hd
      rw [hb] at hc
      obtain ⟨hU, hT⟩ := importCtx_UT hC
      have hI := inv_base B (fcol B.T) C0 _ hU hT hun
      exact not_mainOK (main_bad (col_fcol B hfix) rfl ad C0 E PE hI (had ▸ hr) hc)
    · cases h
  · cases h

end StandardElm.Stat
