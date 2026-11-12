/-
  A Standard Definition of Elm? Mechanisation: the module step (plan step 10), fourth part: a port's
  elaboration does not depend on the sorts its derivation gives the new variables (`elabPort_unique`).

  The skeleton of a type reads `{ | a }` (the empty record extending row variable `a`) as the type
  variable `a`. Two elaborations of one type expression in contexts with the same environment have
  the same skeleton, whatever variables and sorts their U holds; a port's payload type has no
  variable, so it is its own skeleton, and the rest of a port's type is fixed by the rule's shape.
-/
import StandardElmMech.Stat.ModuleStepTypes
import StandardElmMech.Stat.RefuseTypes

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow)

namespace Ports

def skelRec (ρ : Row) (tl : Option RowVar) : Ty :=
  match ρ, tl with
  | [], some (.named a) => .var (.named a)
  | ρ, tl => .record ρ tl

mutual
def skel : Ty → Ty
  | .var a => .var a
  | .record ρ tl => skelRec (skelRow ρ) tl
  | .fn a b => .fn (skel a) (skel b)
  | .con as t => .con (skelList as) t
def skelRow : Row → Row
  | [] => []
  | (l, τ) :: rest => (l, skel τ) :: skelRow rest
def skelList : List Ty → List Ty
  | [] => []
  | τ :: rest => skel τ :: skelList rest
end

theorem skelRow_eq : ∀ ρ : Row, skelRow ρ = RTypes.rowMap skel ρ
  | [] => rfl
  | (l, τ) :: rest => by simp [skelRow, RTypes.rowMap, skelRow_eq rest]

theorem skelList_eq : ∀ l : List Ty, skelList l = l.map skel
  | [] => rfl
  | τ :: rest => by simp [skelList, skelList_eq rest]

theorem skelRec_inj {r1 r2 : Row} {t1 t2 : Option RowVar} (h : skelRec r1 t1 = skelRec r2 t2) : r1 = r2 ∧ t1 = t2 := by
  unfold skelRec at h
  split at h <;> split at h <;> simp_all

theorem skel_tupleTy (τ1 τ2 : Ty) (τ3 : Option Ty) :
    skel (tupleTy τ1 τ2 τ3) = .con (skelList ((match τ3 with | none => [τ1, τ2] | some τ3 => [τ1, τ2, τ3]))) (match τ3 with | none => tTuple2 | some _ => tTuple3) := by
  cases τ3 <;> rfl

/-! ## Substitutions with the same skeleton -/

def SubstSk (S1 S2 : Subst) : Prop :=
  (∀ a, (FMap.find? S1.ty a).map skel = (FMap.find? S2.ty a).map skel) ∧
  (∀ e, (FMap.find? S1.row e).map (fun p => (skelRow p.1, p.2)) = (FMap.find? S2.row e).map (fun p => (skelRow p.1, p.2)))

mutual
theorem apply_skel {S1 S2 : Subst} (hS : SubstSk S1 S2) :
    (τ : Ty) → ∀ {x1 x2 : Ty}, S1.apply τ = some x1 → S2.apply τ = some x2 → skel x1 = skel x2
  | .var a, x1, x2, h1, h2 => by
    simp only [Subst.apply, Option.some.injEq] at h1 h2
    subst h1; subst h2
    have := hS.1 a
    cases e1 : FMap.find? S1.ty a <;> cases e2 : FMap.find? S2.ty a <;> rw [e1, e2] at this <;> simp_all
  | .record ρ none, x1, x2, h1, h2 => by
    simp only [Subst.apply] at h1 h2
    cases r1 : S1.applyRow ρ <;> rw [r1] at h1 <;> simp at h1
    cases r2 : S2.applyRow ρ <;> rw [r2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skel, applyRow_skel hS ρ r1 r2]
  | .record ρ (some e), x1, x2, h1, h2 => by
    simp only [Subst.apply] at h1 h2
    cases r1 : S1.applyRow ρ with
    | none => rw [r1] at h1; cases h1
    | some ρ1 =>
      cases r2 : S2.applyRow ρ with
      | none => rw [r2] at h2; cases h2
      | some ρ2 =>
        rw [r1] at h1; rw [r2] at h2; simp only at h1 h2
        have hr := applyRow_skel hS ρ r1 r2
        have he := hS.2 e
        cases f1 : FMap.find? S1.row e <;> cases f2 : FMap.find? S2.row e <;> rw [f1, f2] at he <;>
          simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at he
        · rw [f1] at h1; rw [f2] at h2
          simp only [Option.some.injEq] at h1 h2; subst h1; subst h2
          simp only [skel, hr]
        · rename_i p1 p2
          obtain ⟨ρa, tla⟩ := p1; obtain ⟨ρb, tlb⟩ := p2
          simp only at he
          obtain ⟨hρ, rfl⟩ := he
          rw [f1] at h1; rw [f2] at h2; simp only at h1 h2
          cases m1 : Row.merge ρ1 ρa with
          | none => rw [m1] at h1; cases h1
          | some ρ3 =>
            cases m2 : Row.merge ρ2 ρb with
            | none => rw [m2] at h2; cases h2
            | some ρ4 =>
              rw [m1] at h1; rw [m2] at h2
              simp only [Option.some.injEq] at h1 h2; subst h1; subst h2
              have k1 := RTypes.merge_map skel ρ1 ρa
              have k2 := RTypes.merge_map skel ρ2 ρb
              rw [← skelRow_eq, ← skelRow_eq, m1] at k1
              rw [← skelRow_eq, ← skelRow_eq, m2] at k2
              rw [hr, hρ, k2] at k1
              simp only [Option.map_some, Option.some.injEq] at k1
              simp only [skel, skelRow_eq, k1]
  | .fn a b, x1, x2, h1, h2 => by
    simp only [Subst.apply] at h1 h2
    cases a1 : S1.apply a <;> cases b1 : S1.apply b <;> rw [a1, b1] at h1 <;> simp at h1
    cases a2 : S2.apply a <;> cases b2 : S2.apply b <;> rw [a2, b2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skel, apply_skel hS a a1 a2, apply_skel hS b b1 b2]
  | .con as t, x1, x2, h1, h2 => by
    simp only [Subst.apply] at h1 h2
    cases l1 : S1.applyList as <;> rw [l1] at h1 <;> simp at h1
    cases l2 : S2.applyList as <;> rw [l2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skel, applyList_skel hS as l1 l2]
theorem applyRow_skel {S1 S2 : Subst} (hS : SubstSk S1 S2) :
    (ρ : Row) → ∀ {r1 r2 : Row}, S1.applyRow ρ = some r1 → S2.applyRow ρ = some r2 → skelRow r1 = skelRow r2
  | [], r1, r2, h1, h2 => by simp [Subst.applyRow] at h1 h2; subst h1; subst h2; rfl
  | (l, τ) :: rest, r1, r2, h1, h2 => by
    simp only [Subst.applyRow] at h1 h2
    cases a1 : S1.apply τ <;> cases b1 : S1.applyRow rest <;> rw [a1, b1] at h1 <;> simp at h1
    cases a2 : S2.apply τ <;> cases b2 : S2.applyRow rest <;> rw [a2, b2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skelRow, apply_skel hS τ a1 a2, applyRow_skel hS rest b1 b2]
theorem applyList_skel {S1 S2 : Subst} (hS : SubstSk S1 S2) :
    (l : List Ty) → ∀ {r1 r2 : List Ty}, S1.applyList l = some r1 → S2.applyList l = some r2 → skelList r1 = skelList r2
  | [], r1, r2, h1, h2 => by simp [Subst.applyList] at h1 h2; subst h1; subst h2; rfl
  | τ :: rest, r1, r2, h1, h2 => by
    simp only [Subst.applyList] at h1 h2
    cases a1 : S1.apply τ <;> cases b1 : S1.applyList rest <;> rw [a1, b1] at h1 <;> simp at h1
    cases a2 : S2.apply τ <;> cases b2 : S2.applyList rest <;> rw [a2, b2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skelList, apply_skel hS τ a1 a2, applyList_skel hS rest b1 b2]
end

theorem bindSubst_skel : ∀ (vs : List BVar) {ts1 ts2 : List Ty} {S1 S2 : Subst},
    bindSubst vs ts1 = some S1 → bindSubst vs ts2 = some S2 → skelList ts1 = skelList ts2 → SubstSk S1 S2
  | [], [], [], S1, S2, h1, h2, _ => by
    simp [bindSubst] at h1 h2; subst h1; subst h2
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .ty a :: vs, τ1 :: ts1, τ2 :: ts2, S1, S2, h1, h2, hs => by
    simp only [bindSubst] at h1 h2
    cases b1 : bindSubst vs ts1 <;> rw [b1] at h1 <;> simp at h1
    cases b2 : bindSubst vs ts2 <;> rw [b2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skelList, List.cons.injEq] at hs
    have ih := bindSubst_skel vs b1 b2 hs.2
    refine ⟨fun a' => ?_, ih.2⟩
    simp only [FMap.find?]
    split
    · simp [hs.1]
    · exact ih.1 a'
  | .row e :: vs, τ1 :: ts1, τ2 :: ts2, S1, S2, h1, h2, hs => by
    simp only [skelList, List.cons.injEq] at hs
    cases τ1 <;> simp [bindSubst] at h1
    cases τ2 <;> simp [bindSubst] at h2
    rename_i ρ1 tl1 ρ2 tl2
    cases b1 : bindSubst vs ts1 <;> rw [b1] at h1 <;> simp at h1
    cases b2 : bindSubst vs ts2 <;> rw [b2] at h2 <;> simp at h2
    subst h1; subst h2
    have ih := bindSubst_skel vs b1 b2 hs.2
    obtain ⟨hr, ht⟩ := skelRec_inj (by simpa [skel] using hs.1)
    refine ⟨ih.1, fun e' => ?_⟩
    simp only [FMap.find?]
    split
    · simp [hr, ht]
    · exact ih.2 e'
  | [], [], _ :: _, _, _, _, h2, _ | [], _ :: _, _, _, _, h1, _, _ => by simp [bindSubst] at *
  | .ty _ :: _, [], _, _, _, h1, _, _ => by simp [bindSubst] at h1
  | .row _ :: _, [], _, _, _, h1, _, _ => by simp [bindSubst] at h1
  | .ty _ :: _, _ :: _, [], _, _, _, h2, _ => by simp [bindSubst] at h2
  | .row _ :: _, _ :: _, [], _, _, _, h2, _ => by cases ‹Ty› <;> simp [bindSubst] at *

theorem tyFcn_apply_skel (θ : TyFcn) {ts1 ts2 : List Ty} {x1 x2 : Ty} (h1 : θ.apply ts1 = some x1) (h2 : θ.apply ts2 = some x2)
    (hs : skelList ts1 = skelList ts2) : skel x1 = skel x2 := by
  unfold TyFcn.apply at h1 h2
  cases b1 : bindSubst θ.params ts1 <;> rw [b1] at h1 <;> simp only at h1
  · cases h1
  cases b2 : bindSubst θ.params ts2 <;> rw [b2] at h2 <;> simp only at h2
  · cases h2
  exact apply_skel (bindSubst_skel _ b1 b2 hs) _ h1 h2

/-! ## Elaborations with the same environment have the same skeleton -/

mutual
theorem elabTy_skel {C C' : Ctx} (hE : C.E = C'.E) :
    (t : BTy) → ∀ {τ1 τ2 : Ty}, elabTy C t = some τ1 → elabTy C' t = some τ2 → skel τ1 = skel τ2
  | .tyvar a, τ1, τ2, h1, h2 => by
    have k : ∀ (D : Ctx) τ, elabTy D (.tyvar a) = some τ → skel τ = .var (.named a) := by
      intro D τ h
      unfold elabTy at h
      split at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · cases h
    rw [k C τ1 h1, k C' τ2 h2]
  | .record row, τ1, τ2, h1, h2 => by
    unfold elabTy at h1 h2
    cases r1 : elabTyRowOpt C row <;> rw [r1] at h1 <;> simp at h1
    cases r2 : elabTyRowOpt C' row <;> rw [r2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skel, elabTyRowOpt_skel hE row r1 r2]
  | .openRecord r row, τ1, τ2, h1, h2 => by
    unfold elabTy at h1 h2
    split at h1 <;> try cases h1
    split at h2 <;> try cases h2
    cases r1 : elabTyRow C row <;> rw [r1] at h1 <;> simp at h1
    cases r2 : elabTyRow C' row <;> rw [r2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skel, elabTyRow_skel hE row r1 r2]
  | .unit, τ1, τ2, h1, h2 => by
    unfold elabTy at h1 h2; cases h1; cases h2; rfl
  | .tuple t1 t2 t3, τ1, τ2, h1, h2 => by
    unfold elabTy at h1 h2
    cases a1 : elabTy C t1 <;> cases b1 : elabTy C t2 <;> cases c1 : elabTyOpt C t3 <;> rw [a1, b1, c1] at h1 <;>
      simp at h1
    cases a2 : elabTy C' t1 <;> cases b2 : elabTy C' t2 <;> cases c2 : elabTyOpt C' t3 <;> rw [a2, b2, c2] at h2 <;>
      simp at h2
    subst h1; subst h2
    have e1 := elabTy_skel hE t1 a1 a2
    have e2 := elabTy_skel hE t2 b1 b2
    have e3 := elabTyOpt_skel hE t3 c1 c2
    rename_i o1 _ _ o2
    cases o1 <;> cases o2 <;> simp at e3 <;> simp [tupleTy, skel, skelList, e1, e2, e3]
  | .con c args, τ1, τ2, h1, h2 => by
    unfold elabTy at h1 h2
    have hl : C'.lookupTy c = C.lookupTy c := by simp [Ctx.lookupTy, hE]
    rw [hl] at h2
    cases lc : C.lookupTy c with
    | none => rw [lc] at h1; cases h1
    | some s =>
      obtain ⟨θ, _⟩ := s
      rw [lc] at h1 h2
      cases a1 : elabTyList C args <;> rw [a1] at h1 <;> simp at h1
      cases a2 : elabTyList C' args <;> rw [a2] at h2 <;> simp at h2
      exact tyFcn_apply_skel θ h1 h2 (elabTyList_skel hE args a1 a2)
  | .fn t1 t2, τ1, τ2, h1, h2 => by
    unfold elabTy at h1 h2
    cases a1 : elabTy C t1 <;> cases b1 : elabTy C t2 <;> rw [a1, b1] at h1 <;> simp at h1
    cases a2 : elabTy C' t1 <;> cases b2 : elabTy C' t2 <;> rw [a2, b2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skel, elabTy_skel hE t1 a1 a2, elabTy_skel hE t2 b1 b2]
  | .paren t, τ1, τ2, h1, h2 => by
    unfold elabTy at h1 h2
    exact elabTy_skel hE t h1 h2
theorem elabTyRow_skel {C C' : Ctx} (hE : C.E = C'.E) :
    (r : BTyRow) → ∀ {ρ1 ρ2 : Row}, elabTyRow C r = some ρ1 → elabTyRow C' r = some ρ2 → skelRow ρ1 = skelRow ρ2
  | .field l t rest, ρ1, ρ2, h1, h2 => by
    unfold elabTyRow at h1 h2
    cases a1 : elabTy C t <;> cases b1 : elabTyRowOpt C rest <;> rw [a1, b1] at h1 <;> simp at h1
    cases a2 : elabTy C' t <;> cases b2 : elabTyRowOpt C' rest <;> rw [a2, b2] at h2 <;> simp at h2
    subst h1; subst h2
    have e1 := elabTy_skel hE t a1 a2
    have e2 := elabTyRowOpt_skel hE rest b1 b2
    rw [skelRow_eq, skelRow_eq, ← RTypes.modify_map, ← RTypes.modify_map, ← skelRow_eq, ← skelRow_eq,
      ← skelRow_eq, ← skelRow_eq, e2]
    simp [skelRow, e1]
theorem elabTyRowOpt_skel {C C' : Ctx} (hE : C.E = C'.E) :
    (r : Option BTyRow) → ∀ {ρ1 ρ2 : Row}, elabTyRowOpt C r = some ρ1 → elabTyRowOpt C' r = some ρ2 → skelRow ρ1 = skelRow ρ2
  | none, ρ1, ρ2, h1, h2 => by unfold elabTyRowOpt at h1 h2; cases h1; cases h2; rfl
  | some r, ρ1, ρ2, h1, h2 => by unfold elabTyRowOpt at h1 h2; exact elabTyRow_skel hE r h1 h2
theorem elabTyOpt_skel {C C' : Ctx} (hE : C.E = C'.E) :
    (t : Option BTy) → ∀ {o1 o2 : Option Ty}, elabTyOpt C t = some o1 → elabTyOpt C' t = some o2 → o1.map skel = o2.map skel
  | none, o1, o2, h1, h2 => by unfold elabTyOpt at h1 h2; cases h1; cases h2; rfl
  | some t, o1, o2, h1, h2 => by
    unfold elabTyOpt at h1 h2
    cases a1 : elabTy C t <;> rw [a1] at h1 <;> simp at h1
    cases a2 : elabTy C' t <;> rw [a2] at h2 <;> simp at h2
    subst h1; subst h2
    simp [elabTy_skel hE t a1 a2]
theorem elabTyList_skel {C C' : Ctx} (hE : C.E = C'.E) :
    (ts : List BTy) → ∀ {l1 l2 : List Ty}, elabTyList C ts = some l1 → elabTyList C' ts = some l2 → skelList l1 = skelList l2
  | [], l1, l2, h1, h2 => by unfold elabTyList at h1 h2; cases h1; cases h2; rfl
  | t :: ts, l1, l2, h1, h2 => by
    unfold elabTyList at h1 h2
    cases a1 : elabTy C t <;> cases b1 : elabTyList C ts <;> rw [a1, b1] at h1 <;> simp at h1
    cases a2 : elabTy C' t <;> cases b2 : elabTyList C' ts <;> rw [a2, b2] at h2 <;> simp at h2
    subst h1; subst h2
    simp only [skelList, elabTy_skel hE t a1 a2, elabTyList_skel hE ts b1 b2]
end

/-! ## Variable-free types are their own skeleton -/

mutual
theorem skel_novars : (τ : Ty) → τ.vars = [] → skel τ = τ
  | .var _, h => by simp [Ty.vars] at h
  | .record ρ none, h => by
    simp only [Ty.vars] at h
    simp only [skel, skelRow_novars ρ h]
    cases ρ <;> rfl
  | .record ρ (some _), h => by simp [Ty.vars] at h
  | .fn a b, h => by
    simp only [Ty.vars, List.append_eq_nil_iff] at h
    simp [skel, skel_novars a h.1, skel_novars b h.2]
  | .con as t, h => by simp only [Ty.vars] at h; simp [skel, skelList_novars as h]
theorem skelRow_novars : (ρ : Row) → Ty.rowVars ρ = [] → skelRow ρ = ρ
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [Ty.rowVars, List.append_eq_nil_iff] at h
    simp [skelRow, skel_novars τ h.1, skelRow_novars rest h.2]
theorem skelList_novars : (l : List Ty) → Ty.listVars l = [] → skelList l = l
  | [], _ => rfl
  | τ :: rest, h => by
    simp only [Ty.listVars, List.append_eq_nil_iff] at h
    simp [skelList, skel_novars τ h.1, skelList_novars rest h.2]
end

mutual
theorem skel_fix : (τ : Ty) → (skel τ).vars = [] → skel τ = τ
  | .var _, h => by simp [skel, Ty.vars] at h
  | .record ρ none, h => by
    simp only [skel] at h ⊢
    have hs : skelRec (skelRow ρ) none = .record (skelRow ρ) none := by unfold skelRec; split <;> simp_all
    rw [hs] at h ⊢
    simp only [Ty.vars] at h
    rw [skelRow_fix ρ h]
  | .record ρ (some e), h => by
    simp only [skel] at h
    exfalso
    unfold skelRec at h
    split at h <;> simp [Ty.vars] at h
  | .fn a b, h => by
    simp only [skel, Ty.vars, List.append_eq_nil_iff] at h
    simp [skel, skel_fix a h.1, skel_fix b h.2]
  | .con as t, h => by
    simp only [skel, Ty.vars] at h
    simp [skel, skelList_fix as h]
theorem skelRow_fix : (ρ : Row) → Ty.rowVars (skelRow ρ) = [] → skelRow ρ = ρ
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [skelRow, Ty.rowVars, List.append_eq_nil_iff] at h
    simp [skelRow, skel_fix τ h.1, skelRow_fix rest h.2]
theorem skelList_fix : (l : List Ty) → Ty.listVars (skelList l) = [] → skelList l = l
  | [], _ => rfl
  | τ :: rest, h => by
    simp only [skelList, Ty.listVars, List.append_eq_nil_iff] at h
    simp [skelList, skel_fix τ h.1, skelList_fix rest h.2]
end

theorem skel_eq_novars {τ τ' : Ty} (hv : τ.vars = []) (h : skel τ' = skel τ) : τ' = τ := by
  rw [skel_novars τ hv] at h
  have : (skel τ').vars = [] := by rw [h]; exact hv
  rw [← skel_fix τ' this, h]

mutual
theorem portB_vars : (τ : Ty) → portB τ = true → τ.vars = []
  | .con [] _, _ => rfl
  | .con [τ] _, h => by
    simp only [portB, Bool.and_eq_true] at h; simp [Ty.vars, Ty.listVars, portB_vars τ h.2]
  | .con [τ1, τ2] _, h => by
    simp only [portB, Bool.and_eq_true] at h
    simp [Ty.vars, Ty.listVars, portB_vars τ1 h.1.2, portB_vars τ2 h.2]
  | .con [τ1, τ2, τ3] _, h => by
    simp only [portB, Bool.and_eq_true] at h
    simp [Ty.vars, Ty.listVars, portB_vars τ1 h.1.1.2, portB_vars τ2 h.1.2, portB_vars τ3 h.2]
  | .con (_ :: _ :: _ :: _ :: _) _, h => by simp [portB] at h
  | .record ρ none, h => by simp only [portB] at h; simp [Ty.vars, portRowB_vars ρ h]
  | .record _ (some _), h => by simp [portB] at h
  | .var _, h => by simp [portB] at h
  | .fn _ _, h => by simp [portB] at h
theorem portRowB_vars : (ρ : Row) → portRowB ρ = true → Ty.rowVars ρ = []
  | [], _ => rfl
  | (_, τ) :: rest, h => by
    simp only [portRowB, Bool.and_eq_true] at h
    simp [Ty.rowVars, portB_vars τ h.1, portRowB_vars rest h.2]
end

/-! ## A port's elaboration -/

def outRes (C : Ctx) (x : Var) (τ' : Ty) (α : TyVar) (t : TyName) : Env × PortEnv :=
  (Env.ofVE [(x, (closScheme C.tyvars (mono (.fn τ' (.con [.var α] t))), .v))], [(x, (.out, τ'))])

def inRes (C : Ctx) (x : Var) (τ' τ'' : Ty) (α : TyVar) (t : TyName) : Env × PortEnv :=
  (Env.ofVE [(x, (closScheme C.tyvars (mono (.fn τ' (.con [.var α] t))), .v))], [(x, (.inn, τ''))])

theorem elabPort_cases {C : Ctx} {x : Var} {ty : BTy} {U : List BVar} {r : Env × PortEnv}
    (h : elabPort C x ty U = some r) : ∃ τ' α t, elabTy (C.plusU U) ty = some (.fn τ' (.con [.var α] t)) ∧
      ((t = tCmd ∧ portB τ' = true ∧ r = outRes C x τ' α t) ∨
       (¬(t = tCmd ∧ portB τ' = true) ∧ ∃ τ'', τ' = .fn τ'' (.var α) ∧ t = tSub ∧ portB τ'' = true ∧
          r = inRes C x τ' τ'' α t)) := by
  unfold elabPort at h
  split at h
  · split at h
    · rename_i τ' α t hτ
      refine ⟨τ', α, t, hτ, ?_⟩
      split at h
      · rename_i hc
        exact .inl ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
      · rename_i hc
        split at h
        · rename_i τ'' α'
          split at h
          · rename_i hc'
            obtain ⟨h1, rfl, h3⟩ := hc'
            exact .inr ⟨hc, τ'', rfl, h1, h3, (Option.some.inj h).symm⟩
          · cases h
        · cases h
    · cases h
  · cases h

/-- Two elaborations of a port that differ only in the sorts of its new variables agree. -/
theorem elabPort_unique {C : Ctx} {x : Var} {ty : BTy} {U U2 : List BVar} {r r2 : Env × PortEnv}
    (h : elabPort C x ty U = some r) (h2 : elabPort C x ty U2 = some r2) : r = r2 := by
  obtain ⟨τ1, α1, t1, e1, c1⟩ := elabPort_cases h
  obtain ⟨τ2, α2, t2, e2, c2⟩ := elabPort_cases h2
  have hs := elabTy_skel (C := C.plusU U) (C' := C.plusU U2) rfl ty e1 e2
  simp only [skel, skelList, Ty.fn.injEq, Ty.con.injEq, List.cons.injEq, Ty.var.injEq, and_true] at hs
  obtain ⟨hs, rfl, rfl⟩ := hs
  have key : portB τ1 = true → τ2 = τ1 := fun hp => skel_eq_novars (portB_vars _ hp) hs.symm
  have key' : portB τ2 = true → τ1 = τ2 := fun hp => skel_eq_novars (portB_vars _ hp) hs
  rcases c1 with ⟨ht1, hp1, rfl⟩ | ⟨hn1, τ1', rfl, ht1, hp1, rfl⟩ <;>
    rcases c2 with ⟨ht2, hp2, rfl⟩ | ⟨hn2, τ2', rfl, ht2, hp2, rfl⟩
  · rw [key hp1]
  · exact absurd ⟨ht1, by rw [key hp1]; exact hp1⟩ hn2
  · exact absurd ⟨ht2, by rw [key' hp2]; exact hp2⟩ hn1
  · simp only [skel, Ty.fn.injEq, and_true] at hs
    have : τ2' = τ1' := skel_eq_novars (portB_vars _ hp1) hs.symm
    subst this; rfl

end Ports

end StandardElm.Stat
