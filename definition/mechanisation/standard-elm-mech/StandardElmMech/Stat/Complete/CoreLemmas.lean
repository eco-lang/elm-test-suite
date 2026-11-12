/-
  A Standard Definition of Elm? Mechanisation: lemmas for the completeness of `coreGen`, plan step
  11, milestone (a): what a variable of the generator's context stands for in a derivation's
  context (`GOK`, `RelL`, `Sim`), occurrences (instantiation of a scheme), annotations (every
  choice of sorts is a candidate), closing a group.
-/
import StandardElmMech.Stat.Complete.CoreTmpl

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow)

variable {ν : Val}

/-! ## Substitutions on closed types -/

mutual
theorem apply_closed (S : Subst) : ∀ τ : Ty, τ.vars = [] → S.apply τ = some τ
  | .var _, h => by simp [Ty.vars] at h
  | .record ρ none, h => by
    simp only [Ty.vars] at h
    simp only [Subst.apply, applyRow_closed S ρ h]
  | .record ρ (some _), h => by simp [Ty.vars] at h
  | .fn a b, h => by
    simp only [Ty.vars, List.append_eq_nil_iff] at h
    simp only [Subst.apply, apply_closed S a h.1, apply_closed S b h.2]
  | .con as t, h => by
    simp only [Ty.vars] at h
    simp only [Subst.apply, applyList_closed S as h]
theorem applyRow_closed (S : Subst) : ∀ ρ : Row, Ty.rowVars ρ = [] → S.applyRow ρ = some ρ
  | [], _ => rfl
  | (l, x) :: r, h => by
    simp only [Ty.rowVars, List.append_eq_nil_iff] at h
    simp only [Subst.applyRow, apply_closed S x h.1, applyRow_closed S r h.2]
theorem applyList_closed (S : Subst) : ∀ l : List Ty, Ty.listVars l = [] → S.applyList l = some l
  | [], _ => rfl
  | x :: r, h => by
    simp only [Ty.listVars, List.append_eq_nil_iff] at h
    simp only [Subst.applyList, apply_closed S x h.1, applyList_closed S r h.2]
end

mutual
theorem apply_id : ∀ τ : Ty, Subst.id.apply τ = some τ
  | .var _ => rfl
  | .record ρ none => by simp only [Subst.apply, applyRow_id ρ]
  | .record ρ (some e) => by simp only [Subst.apply, applyRow_id ρ]; rfl
  | .fn a b => by simp only [Subst.apply, apply_id a, apply_id b]
  | .con as t => by simp only [Subst.apply, applyList_id as]
theorem applyRow_id : ∀ ρ : Row, Subst.id.applyRow ρ = some ρ
  | [] => rfl
  | (l, x) :: r => by simp only [Subst.applyRow, apply_id x, applyRow_id r]
theorem applyList_id : ∀ l : List Ty, Subst.id.applyList l = some l
  | [] => rfl
  | x :: r => by simp only [Subst.applyList, apply_id x, applyList_id r]
end

theorem genAt_mono {τ τ' : Ty} {inst : List Ty} (h : genAt (mono τ) inst τ' = true) : τ' = τ := by
  unfold genAt at h
  split at h
  · rename_i S hS
    cases inst with
    | nil =>
      simp only [mono, bindSubst, Option.some.injEq] at hS
      subst hS
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [apply_id] at h
      exact (Option.some.inj h.2).symm
    | cons _ _ => simp [mono, bindSubst] at hS
  · cases h

theorem genAt_closed {σ : Scheme} {τ' : Ty} {inst : List Ty} (hc : σ.body.vars = [])
    (h : genAt σ inst τ' = true) : τ' = σ.body := by
  unfold genAt at h
  split at h
  · rename_i S hS
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [apply_closed S _ hc] at h
    exact (Option.some.inj h.2).symm
  · cases h

theorem canon_closed (bs : List BVar) (τ : Ty) (hc : τ.vars = []) : (Scheme.canon ⟨bs, τ⟩).body = τ := by
  unfold Scheme.canon
  simp only [apply_closed _ τ hc, Option.getD_some]

theorem child {F G : Path → Ty} {p : Path} (i : Nat) (hr : ∀ q, ν (q.reverse ++ p) = F q)
    (hF : ∀ q, F (i :: q) = G q) : ∀ q, ν (q.reverse ++ (i :: p)) = G q :=
  fun q => by
    have := hr (i :: q)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
    exact this.trans (hF q)

/-! ## Shapes -/

mutual
/-- τ has the shape of the term t: the same function and constructed types, and the same type
    where t is closed. -/
def Shp (ν : Val) : T → Ty → Prop
  | .fn a b, τ =>
    if (T.fn a b).closed then τ = (T.fn a b).ev ν else ∃ τa τb, τ = .fn τa τb ∧ Shp ν a τa ∧ Shp ν b τb
  | .con as tn, τ =>
    if (T.con as tn).closed then τ = (T.con as tn).ev ν else ∃ τs, τ = .con τs tn ∧ ShpList ν as τs
  | .record ρ tl, τ => ((T.record ρ tl).closed = true → τ = (T.record ρ tl).ev ν) ∧
    (tl = none → ∃ ρ', τ = .record ρ' none ∧ ShpRow ν ρ ρ')
  | .mv _, _ => True
  | .var _, _ => True
def ShpList (ν : Val) : List T → List Ty → Prop
  | [], [] => True
  | a :: as, τ :: τs => Shp ν a τ ∧ ShpList ν as τs
  | _, _ => False
def ShpRow (ν : Val) : List (Lab × T) → Row → Prop
  | [], [] => True
  | (l, a) :: r, (l', τ) :: r' => l = l' ∧ Shp ν a τ ∧ ShpRow ν r r'
  | _, _ => False
end

mutual
theorem Shp_refl : ∀ t : T, Shp ν t (t.ev ν)
  | .fn a b => by
    simp only [Shp]
    split
    · first | rfl | trivial
    · exact ⟨_, _, rfl, Shp_refl a, Shp_refl b⟩
  | .con as tn => by
    simp only [Shp]
    split
    · first | rfl | trivial
    · exact ⟨_, rfl, ShpList_refl as⟩
  | .record ρ tl => ⟨fun _ => rfl, fun e => ⟨_, by subst e; rfl, ShpRow_refl ρ⟩⟩
  | .mv _ => trivial
  | .var _ => trivial
theorem ShpList_refl : ∀ l : List T, ShpList ν l (T.evList ν l)
  | [] => trivial
  | a :: as => ⟨Shp_refl a, ShpList_refl as⟩
theorem ShpRow_refl : ∀ l : List (Lab × T), ShpRow ν l (T.evRow ν l)
  | [] => trivial
  | (_, a) :: r => ⟨rfl, Shp_refl a, ShpRow_refl r⟩
end

theorem Shp_closed {t : T} {τ : Ty} (hc : t.closed = true) (h : Shp ν t τ) : τ = t.ev ν := by
  cases t with
  | fn a b => simp only [Shp, hc, ite_true] at h; exact h
  | con as tn => simp only [Shp, hc, ite_true] at h; exact h
  | record ρ tl => exact h.1 hc
  | mv _ => simp [T.closed] at hc
  | var _ => simp [T.closed] at hc

theorem closed_hN_apply {t : T} {τ0 τ1 : Ty} {S : Subst} (hc : t.closed = true) (h : hN τ0 = t.ev ν)
    (ha : S.apply τ0 = some τ1) : τ1 = τ0 := by
  have hv : τ0.vars = [] := vars_of_hN τ0 (h ▸ closed_vars ν t hc)
  rw [apply_closed S τ0 hv] at ha
  exact (Option.some.inj ha).symm

mutual
/-- A substitution keeps shapes. -/
theorem Shp_subst (S : Subst) : ∀ (t : T) (τ0 τ1 : Ty), Shp ν t (hN τ0) → S.apply τ0 = some τ1 → Shp ν t (hN τ1)
  | .fn a b, τ0, τ1, h, ha => by
    by_cases hc : (T.fn a b).closed = true
    · have := Shp_closed hc h
      rw [closed_hN_apply hc this ha]; exact h
    · simp only [Shp, hc] at h ⊢
      obtain ⟨τa, τb, e, h1, h2⟩ := h
      obtain ⟨x, y, rfl, rfl, rfl⟩ := hN_fn_inv e
      simp only [Subst.apply] at ha
      split at ha
      · rename_i x' y' hx hy
        cases ha
        exact ⟨_, _, rfl, Shp_subst S a x x' h1 hx, Shp_subst S b y y' h2 hy⟩
      · cases ha
  | .con as tn, τ0, τ1, h, ha => by
    by_cases hc : (T.con as tn).closed = true
    · have := Shp_closed hc h
      rw [closed_hN_apply hc this ha]; exact h
    · simp only [Shp, hc] at h ⊢
      obtain ⟨τs, e, h1⟩ := h
      obtain ⟨xs, t0, rfl, rfl, rfl⟩ := hN_con_inv e
      simp only [Subst.apply] at ha
      split at ha
      · rename_i xs' hx
        cases ha
        exact ⟨_, rfl, ShpList_subst S as xs xs' h1 hx⟩
      · cases ha
  | .record ρ tl, τ0, τ1, h, ha => by
    by_cases hc : (T.record ρ tl).closed = true
    · have := h.1 hc
      rw [closed_hN_apply hc this ha]; exact h
    · refine ⟨fun hc' => absurd hc' hc, fun e => ?_⟩
      obtain ⟨ρ', e', hrow⟩ := h.2 e
      obtain ⟨xs, rfl, rfl⟩ := hN_rec_inv e'
      simp only [Subst.apply] at ha
      split at ha
      · rename_i xs' hx
        cases ha
        exact ⟨_, rfl, ShpRow_subst S ρ xs xs' hrow hx⟩
      · cases ha
  | .mv _, _, _, _, _ => trivial
  | .var _, _, _, _, _ => trivial
theorem ShpRow_subst (S : Subst) : ∀ (ρ : List (Lab × T)) (xs xs' : Row), ShpRow ν ρ (hNRow xs) →
    S.applyRow xs = some xs' → ShpRow ν ρ (hNRow xs')
  | [], [], xs', _, ha => by simp only [Subst.applyRow, Option.some.injEq] at ha; subst ha; trivial
  | [], _ :: _, _, h, _ => by simp [hNRow, ShpRow] at h
  | _ :: _, [], _, h, _ => by simp [hNRow, ShpRow] at h
  | (l, a) :: r, (l', x) :: xs, xs', h, ha => by
    simp only [hNRow, ShpRow] at h
    simp only [Subst.applyRow] at ha
    split at ha
    · rename_i x' r' hx hr
      cases ha
      exact ⟨h.1, Shp_subst S a x x' h.2.1 hx, ShpRow_subst S r xs r' h.2.2 hr⟩
    · cases ha
theorem ShpList_subst (S : Subst) : ∀ (as : List T) (xs xs' : List Ty), ShpList ν as (hNList xs) →
    S.applyList xs = some xs' → ShpList ν as (hNList xs')
  | [], [], xs', _, ha => by simp only [Subst.applyList, Option.some.injEq] at ha; subst ha; trivial
  | [], _ :: _, _, h, _ => by simp [hNList, ShpList] at h
  | _ :: _, [], _, h, _ => by simp [hNList, ShpList] at h
  | a :: as, x :: xs, xs', h, ha => by
    simp only [hNList, ShpList] at h
    simp only [Subst.applyList] at ha
    split at ha
    · rename_i x' r' hx hr
      cases ha
      exact ⟨Shp_subst S a x x' h.1 hx, ShpList_subst S as xs r' h.2 hr⟩
    · cases ha
end

theorem Shp_canon {t : T} {τ : Ty} (bs : List BVar) (h : Shp ν t (hN τ)) :
    Shp ν t (hN (Scheme.canon ⟨bs, τ⟩).body) := by
  unfold Scheme.canon
  simp only
  cases ha : (renumber true 0 (canonVars bs τ)).1.apply τ with
  | none => simpa [ha] using h
  | some τ1 => simpa [ha] using Shp_subst _ t τ τ1 h ha

theorem Shp_gen {t : T} {σ : Scheme} {inst : List Ty} {τ : Ty} (h : Shp ν t (hN σ.body))
    (hg : genAt σ inst τ = true) : Shp ν t (hN τ) := by
  unfold genAt at hg
  split at hg
  · rename_i S _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact Shp_subst S t _ _ h hg.2
  · cases hg

theorem tyChild_fn0 (a b : Ty) : tyChild (.fn a b) 0 = a := rfl
theorem tyChild_fn1 (a b : Ty) : tyChild (.fn a b) 1 = b := rfl

mutual
/-- The copy `sc` evaluates to any type of the term's shape, under the valuation reading that
    type's parts. -/
theorem sc_ok : ∀ (t : T) (base : Path) (τ : Ty), Shp ν t τ → (∀ q, ν (q.reverse ++ base) = subAt τ q) →
    (sc base t).ev ν = τ
  | .fn a b, base, τ, h, hr => by
    simp only [sc]
    by_cases hc : (T.fn a b).closed = true
    · simp only [hc, ite_true]; exact (Shp_closed hc h).symm
    · simp only [Bool.not_eq_true] at hc
      simp only [Shp, hc, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨τa, τb, rfl, h1, h2⟩ := h
      have r0 : ∀ q, ν (q.reverse ++ (0 :: base)) = subAt τa q := fun q => by
        have := hr (0 :: q); simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
        exact this
      have r1 : ∀ q, ν (q.reverse ++ (1 :: base)) = subAt τb q := fun q => by
        have := hr (1 :: q); simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
        exact this
      simp only [T.ev, sc_ok a _ τa h1 r0, sc_ok b _ τb h2 r1]
  | .con as tn, base, τ, h, hr => by
    simp only [sc]
    by_cases hc : (T.con as tn).closed = true
    · simp only [hc, ite_true]; exact (Shp_closed hc h).symm
    · simp only [Bool.not_eq_true] at hc
      simp only [Shp, hc, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨τs, rfl, h1⟩ := h
      simp only [T.ev]
      rw [scList_ok as base 0 τs h1 (fun j q => by
        have := hr ((0 + j) :: q); simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
        rw [this]; simp [subAt, tyChild])]
  | .record ρ tl, base, τ, h, hr => by
    simp only [sc]
    by_cases hc : (T.record ρ tl).closed = true
    · simp only [hc, ite_true]; exact (h.1 hc).symm
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      cases tl with
      | none =>
        obtain ⟨ρ', rfl, hrow⟩ := h.2 rfl
        simp only [T.ev]
        rw [scRow_ok ρ base 0 ρ' hrow (fun j q => by
          have := hr ((0 + j) :: q); simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
          rw [this]; simp [subAt, tyChild])]
      | some _ => exact hr []
  | .mv _, base, τ, _, hr => hr []
  | .var _, base, τ, _, hr => hr []
theorem scList_ok : ∀ (as : List T) (base : Path) (i : Nat) (τs : List Ty), ShpList ν as τs →
    (∀ j q, ν (q.reverse ++ ((i + j) :: base)) = subAt (τs.getD j default) q) →
    T.evList ν (scList base i as) = τs
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, h, _ => by simp [ShpList] at h
  | _ :: _, _, _, [], h, _ => by simp [ShpList] at h
  | a :: as, base, i, τ :: τs, h, hr => by
    simp only [ShpList] at h
    simp only [scList, T.evList]
    rw [sc_ok a (i :: base) τ h.1 (fun q => by simpa using hr 0 q),
      scList_ok as base (i + 1) τs h.2 (fun j q => by
        have := hr (j + 1) q
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        simpa using this)]
theorem scRow_ok : ∀ (ρ : List (Lab × T)) (base : Path) (i : Nat) (ρ' : Row), ShpRow ν ρ ρ' →
    (∀ j q, ν (q.reverse ++ ((i + j) :: base)) = subAt ((ρ'.getD j default).2) q) →
    T.evRow ν (scRow base i ρ) = ρ'
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, h, _ => by simp [ShpRow] at h
  | _ :: _, _, _, [], h, _ => by simp [ShpRow] at h
  | (l, a) :: r, base, i, (l', τ) :: r', h, hr => by
    simp only [ShpRow] at h
    obtain ⟨rfl, h1, h2⟩ := h
    simp only [scRow, T.evRow]
    rw [sc_ok a (i :: base) τ h1 (fun q => by simpa using hr 0 q),
      scRow_ok r base (i + 1) r' h2 (fun j q => by
        have := hr (j + 1) q
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        simpa using this)]
end

/-! ## What the generator's variables stand for -/

def GOK (ν : Val) : GInfo → Scheme → Prop
  | .weak, _ => True
  | .sch σ, σd => σ = σd
  | .mono t, σd => (∀ inst τ, genAt σd inst τ = true → t.ev ν = hN τ) ∧ t.ev ν = hN σd.body
  | .shape t, σd => (∀ inst τ, genAt σd inst τ = true → Shp ν t (hN τ)) ∧ Shp ν t (hN σd.body)
  | .tmpl t K, σd => ∃ τ0, InstOf σd τ0 ∧ TmplOK t K τ0

/-- A generator entry against a derivation's entry: both absent, related, or a `weak` entry the
    derivation does not have (the derivation then looks further, `weak` stands for anything). -/
def RelOpt (ν : Val) : Option GInfo → Option (Scheme × IdStatus) → Prop
  | none, none => True
  | some g, some (σ, _) => GOK ν g σ
  | some .weak, none => True
  | _, _ => False

def RelL (ν : Val) (L : FMap Var GInfo) (VE : ValEnv) : Prop :=
  ∀ x, RelOpt ν (L.find? x) (VE.find? x)

theorem RelOpt.or {a1 a2 : Option GInfo} {b1 b2 : Option (Scheme × IdStatus)} (h1 : RelOpt ν a1 b1)
    (h2 : RelOpt ν a2 b2) : RelOpt ν (a1.or a2) (b1.or b2) := by
  cases a1 with
  | none =>
    cases b1 with
    | none => simpa using h2
    | some _ => exact h1.elim
  | some g =>
    cases b1 with
    | some v => simpa using h1
    | none =>
      cases g with
      | weak =>
        simp only [Option.some_or, Option.none_or]
        cases b2 with
        | none => trivial
        | some v => trivial
      | _ => exact h1.elim

theorem RelL.nil : RelL ν [] [] := fun _ => trivial

theorem RelL.single {x : Var} {g : GInfo} {σ : Scheme} {s : IdStatus} (h : GOK ν g σ) :
    RelL ν [(x, g)] [(x, (σ, s))] := by
  intro y
  simp only [FMap.find?]
  split
  · exact h
  · trivial

theorem RelL.modify {L1 L2 : FMap Var GInfo} {V1 V2 : ValEnv} (h1 : RelL ν L1 V1) (h2 : RelL ν L2 V2) :
    RelL ν (FMap.modify L1 L2) (FMap.modify V1 V2) := by
  intro x
  rw [FMap.find?_modify, FMap.find?_modify]
  exact RelOpt.or (h2 x) (h1 x)

theorem RelL.append {L1 L2 : FMap Var GInfo} {V1 V2 : ValEnv} (h1 : RelL ν L1 V1) (h2 : RelL ν L2 V2) :
    RelL ν (L1 ++ L2) (V1 ++ V2) := by
  intro x
  rw [FMap.find?_append, FMap.find?_append]
  exact RelOpt.or (h1 x) (h2 x)

/-- Pairwise related lists of environments. -/
def RelLs (ν : Val) : List (FMap Var GInfo) → List ValEnv → Prop
  | [], [] => True
  | L :: Ls, V :: Vs => RelL ν L V ∧ RelLs ν Ls Vs
  | _, _ => False

theorem RelL.foldl_modify : ∀ {Ls : List (FMap Var GInfo)} {Vs : List ValEnv} {L0 : FMap Var GInfo} {V0 : ValEnv},
    RelL ν L0 V0 → RelLs ν Ls Vs → RelL ν (Ls.foldl FMap.modify L0) (Vs.foldl FMap.modify V0)
  | [], [], _, _, h0, _ => h0
  | [], _ :: _, _, _, _, h => by simp [RelLs] at h
  | _ :: _, [], _, _, _, h => by simp [RelLs] at h
  | _ :: Ls, _ :: Vs, _, _, h0, h => RelL.foldl_modify (Ls := Ls) (Vs := Vs) (RelL.modify h0 h.1) h.2

theorem RelL.plusAll {Ls : List (FMap Var GInfo)} {Vs : List ValEnv} (h : RelLs ν Ls Vs) :
    RelL ν (FMap.plusAll Ls) (FMap.plusAll Vs) :=
  RelL.foldl_modify RelL.nil h

theorem find?_map_keep {K V W : Type} [DecidableEq K] (f : K × V → K × W) (hf : ∀ p, (f p).1 = p.1) (k : K) :
    ∀ l : List (K × V), FMap.find? (l.map f) k = (FMap.find? l k).map (fun v => (f (k, v)).2)
  | [] => rfl
  | (k', v) :: rest => by
    have e : f (k', v) = (k', (f (k', v)).2) := by
      cases h : f (k', v); simp only; have := hf (k', v); rw [h] at this; simp only at this; rw [this]
    simp only [List.map_cons, FMap.find?]
    rw [e]
    simp only
    split
    · rename_i hk; subst hk; rfl
    · exact find?_map_keep f hf k rest

theorem find?_mapV {K V W : Type} [DecidableEq K] (f : FMap K V) (g : V → W) (k : K) :
    FMap.find? (FMap.mapV f g) k = (FMap.find? f k).map g := find?_map_val g k f

theorem ev_resolveIn {sol : List Con} (hs : Holds ν sol) : ∀ t : T, (resolveIn sol t).ev ν = t.ev ν
  | .mv q => by
    simp only [resolveIn]
    cases h : boundOf q sol with
    | none => rfl
    | some t' => simp only [Option.getD_some, T.ev]; exact (boundOf_ev hs h).symm
  | .var _ => rfl
  | .record _ _ => rfl
  | .fn _ _ => rfl
  | .con _ _ => rfl

theorem RelL.close {L : FMap Var GInfo} {VE : ValEnv} {sol : List Con} (A : List BVar) (hs : Holds ν sol)
    (h : RelL ν L VE) : RelL ν (closeL sol L) (closGroup A VE) := by
  intro x
  unfold closeL closGroup
  rw [find?_map_val, find?_mapV]
  have hx := h x
  cases e1 : FMap.find? L x with
  | none =>
    cases e2 : FMap.find? VE x with
    | none => trivial
    | some v => rw [e1, e2] at hx; exact hx.elim
  | some g =>
    cases e2 : FMap.find? VE x with
    | none =>
      rw [e1, e2] at hx
      cases g with
      | weak => simp only [Option.map_some, Option.map_none, closeG]; trivial
      | _ => exact hx.elim
    | some v =>
      rw [e1, e2] at hx
      obtain ⟨σ, s⟩ := v
      simp only [Option.map_some] at hx ⊢
      cases g with
      | weak => trivial
      | sch _ => trivial
      | tmpl t K =>
        obtain ⟨τ0, h1, h2⟩ := hx
        exact ⟨τ0, instOf_close h1 _, h2⟩
      | shape t =>
        simp only [closeG]
        obtain ⟨_, h2⟩ := hx
        have hb := Shp_canon (σ.bound ++ diffL (dedupL σ.tyvars) A ++
          List.filter BVar.isNumTyVar (diffL (dedupL (ValEnv.tyvars VE)) (σ.tyvars ++ A))) h2
        exact ⟨fun inst τ hg => Shp_gen hb hg, hb⟩
      | mono t =>
        simp only [closeG]
        obtain ⟨_, h2⟩ := hx
        have he : (resolveIn sol t).ev ν = hN σ.body := (ev_resolveIn hs t).trans h2
        split
        · rename_i hc
          have hv : σ.body.vars = [] := vars_of_hN _ (he ▸ closed_vars ν _ hc)
          refine ⟨fun inst τ hg => ?_, ?_⟩
          · rw [genAt_closed (by rw [canon_closed _ _ hv]; exact hv) hg, canon_closed _ _ hv, he]
          · rw [canon_closed _ _ hv, he]
        · have hb := Shp_canon (σ.bound ++ diffL (dedupL σ.tyvars) A ++
            List.filter BVar.isNumTyVar (diffL (dedupL (ValEnv.tyvars VE)) (σ.tyvars ++ A)))
            (he ▸ Shp_refl (resolveIn sol t))
          have hsh : GOK ν (.shape (resolveIn sol t)) (Scheme.canon ⟨σ.bound ++ diffL (dedupL σ.tyvars) A ++
              List.filter BVar.isNumTyVar (diffL (dedupL (ValEnv.tyvars VE)) (σ.tyvars ++ A)), σ.body⟩) :=
            ⟨fun inst τ hg => Shp_gen hb hg, hb⟩
          revert he hsh
          generalize resolveIn sol t = t'
          intro he hsh
          split
          · rename_i q
            unfold mvInfo
            split
            · exact hsh
            · refine ⟨σ.body, instOf_canon _ _, tmplMv_ok fun k hk => ?_⟩
              have := hs _ (mem_clsOf hk)
              simp only [Con.holds, T.ev] at this he
              rw [← he]; exact this
          · exact hsh

/-! ## The simulation of a derivation's context -/

/-- The simulation of a context's type expressions by the abstract context (RefuseTypes.lean). -/
structure TySim (f : TyName → TyName) (C A : Ctx) : Prop where
  look : ∀ lc, RTypes.LookSim f C A lc
  fix : RTypes.FixesBuiltins f
  g : ∀ t, gN (f t) = gN t

theorem TySim.same {f : TyName → TyName} {C C' A : Ctx} (h : TySim f C A) (ht : ∀ lc, C'.lookupTy lc = C.lookupTy lc) :
    TySim f C' A :=
  ⟨fun lc θ VE hl => h.look lc θ VE (by rw [← ht lc]; exact hl), h.fix, h.g⟩

structure Sim (ν : Val) (f : TyName → TyName) (Γ : GCtx) (C : Ctx) : Prop where
  val : ∀ lv σ is, C.lookupVal lv = some (σ, is) → GOK ν (Γ.look lv) σ
  ty : TySim f C Γ.A

theorem Sim.base {f : TyName → TyName} (C0 A : Ctx) (hT : TySim f C0 A) : Sim ν f ⟨[], C0, A⟩ C0 where
  val := by
    rintro ⟨q, x⟩ σ is h
    cases q with
    | none =>
      simp only [Ctx.lookupVal, Env.lookupVal] at h
      simp only [GCtx.look, FMap.find?, h]
      rfl
    | some m =>
      simp only [GCtx.look, h]
      rfl
  ty := hT

theorem Sim.extendV {f : TyName → TyName} {Γ : GCtx} {C C' : Ctx} {L : FMap Var GInfo} {VE : ValEnv}
    (hval : ∀ lv σ is, C.lookupVal lv = some (σ, is) → GOK ν (Γ.look lv) σ) (hR : RelL ν L VE)
    (hv : ∀ x, C'.lookupVal ⟨none, x⟩ = (VE.find? x).or (C.lookupVal ⟨none, x⟩))
    (hq : ∀ m x, C'.lookupVal ⟨some m, x⟩ = C.lookupVal ⟨some m, x⟩)
    (ht : TySim f C' Γ.A) : Sim ν f (Γ.add L) C' where
  val := by
    rintro ⟨q, x⟩ σ is h
    cases q with
    | none =>
      rw [hv] at h
      have hx := hR x
      have hlook : (Γ.add L).look ⟨none, x⟩ =
          match L.find? x with
          | some g => g
          | none => Γ.look ⟨none, x⟩ := by
        simp only [GCtx.look, GCtx.add, FMap.find?_append]
        cases L.find? x <;> rfl
      rw [hlook]
      cases e1 : FMap.find? L x with
      | none =>
        cases e2 : FMap.find? VE x with
        | none =>
          rw [e2, Option.none_or] at h
          exact hval _ σ is h
        | some v => rw [e1, e2] at hx; exact hx.elim
      | some g =>
        cases e2 : FMap.find? VE x with
        | none =>
          rw [e1, e2] at hx
          cases g with
          | weak => trivial
          | _ => exact hx.elim
        | some v =>
          rw [e1, e2] at hx
          rw [e2, Option.some_or] at h
          cases h
          exact hx
    | some m =>
      rw [hq] at h
      exact hval _ σ is h
  ty := ht

theorem Sim.extend {f : TyName → TyName} {Γ : GCtx} {C C' : Ctx} {L : FMap Var GInfo} {VE : ValEnv}
    (hS : Sim ν f Γ C) (hR : RelL ν L VE)
    (hv : ∀ x, C'.lookupVal ⟨none, x⟩ = (VE.find? x).or (C.lookupVal ⟨none, x⟩))
    (hq : ∀ m x, C'.lookupVal ⟨some m, x⟩ = C.lookupVal ⟨some m, x⟩)
    (ht : TySim f C' Γ.A) : Sim ν f (Γ.add L) C' :=
  Sim.extendV hS.val hR hv hq ht

/-- The values of the imports' context. -/
theorem valSim_base (C0 A : Ctx) : ∀ lv σ is, C0.lookupVal lv = some (σ, is) →
    GOK ν ((⟨[], C0, A⟩ : GCtx).look lv) σ := by
  rintro ⟨q, x⟩ σ is h
  cases q with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal] at h
    simp only [GCtx.look, FMap.find?, h]
    rfl
  | some m =>
    simp only [GCtx.look, h]
    rfl

theorem Sim.plusVE {f : TyName → TyName} {Γ : GCtx} {C : Ctx} {L : FMap Var GInfo} {VE : ValEnv}
    (hS : Sim ν f Γ C) (hR : RelL ν L VE) : Sim ν f (Γ.add L) (C.plusVE VE) :=
  hS.extend hR (fun x => by simp [Ctx.plusVE, Ctx.lookupVal, Env.lookupVal, FMap.find?_append])
    (fun _ _ => rfl) (hS.ty.same (fun _ => rfl))

theorem Sim.plusU {f : TyName → TyName} {Γ : GCtx} {C : Ctx} (hS : Sim ν f Γ C) (U : List BVar) :
    Sim ν f Γ (C.plusU U) :=
  ⟨hS.val, hS.ty.same (fun _ => rfl)⟩

theorem find?_modify_nil {K V : Type} [DecidableEq K] (f : FMap K V) (k : K) :
    FMap.find? (FMap.modify f []) k = FMap.find? f k := by
  rw [FMap.find?_modify]; rfl

/-- Adding an environment with no modules, given the values of the context. -/
theorem Sim.oplusEV {f : TyName → TyName} {Γ : GCtx} {C : Ctx} {L : FMap Var GInfo} {E : Env}
    (hval : ∀ lv σ is, C.lookupVal lv = some (σ, is) → GOK ν (Γ.look lv) σ) (hR : RelL ν L E.VE)
    (hQ : E.QE = []) (ht : TySim f (C.oplusE E) Γ.A) : Sim ν f (Γ.add L) (C.oplusE E) := by
  obtain ⟨QE, TE, VE⟩ := E
  simp only at hQ hR
  subst hQ
  refine Sim.extendV hval hR (fun x => ?_) (fun m x => ?_) ht
  · simp [Ctx.oplusE, Env.plus, Ctx.lookupVal, Env.lookupVal, FMap.find?_modify]
  · simp only [Ctx.oplusE, Env.plus, Ctx.lookupVal, Env.lookupVal, find?_modify_nil]

/-- Adding an environment with no types and no modules: value lookups extended, the rest kept. -/
theorem Sim.oplusE {f : TyName → TyName} {Γ : GCtx} {C : Ctx} {L : FMap Var GInfo} {E : Env}
    (hS : Sim ν f Γ C) (hR : RelL ν L E.VE) (hQ : E.QE = []) (ht : TySim f (C.oplusE E) Γ.A) :
    Sim ν f (Γ.add L) (C.oplusE E) := by
  obtain ⟨QE, TE, VE⟩ := E
  simp only at hQ hR
  subst hQ
  refine hS.extend hR (fun x => ?_) (fun m x => ?_) ht
  · simp [Ctx.oplusE, Env.plus, Ctx.lookupVal, Env.lookupVal, FMap.find?_modify]
  · simp only [Ctx.oplusE, Env.plus, Ctx.lookupVal, Env.lookupVal, find?_modify_nil]

theorem lookupTy_oplusE_ofVE (C : Ctx) (E : Env) (hQ : E.QE = []) (hT : E.TE = []) (lc : LongId) :
    (C.oplusE E).lookupTy lc = C.lookupTy lc := by
  obtain ⟨QE, TE, VE⟩ := E
  simp only at hQ hT
  subst hQ; subst hT
  obtain ⟨q, c⟩ := lc
  cases q <;> simp only [Ctx.oplusE, Env.plus, Ctx.lookupTy, Env.lookupTy, find?_modify_nil]

/-- A node's own metavariable. -/
theorem slot {F : Path → Ty} {p : Path} (hr : ∀ q, ν (q.reverse ++ p) = F q) (k : Nat) : ν (k :: p) = F [k] :=
  hr [k]

/-! ## Instantiation of a scheme -/

def NoRow (bs : List BVar) : Prop := ∀ v ∈ bs, ∀ e, v ≠ .row e

theorem noRow_of (σ : Scheme) (h : hasRowBound σ = false) : NoRow σ.bound := by
  intro v hv e he
  subst he
  have := List.any_eq_false.mp h _ hv
  simp at this

theorem bindSubst_facts : ∀ (bs : List BVar) (inst : List Ty) (S : Subst), NoRow bs →
    bindSubst bs inst = some S →
    S.row = [] ∧ ∀ a, FMap.find? S.ty a = (idxTy a bs).map (fun i => inst.getD i default)
  | [], [], S, _, h => by
    simp only [bindSubst, Option.some.injEq] at h; subst h; exact ⟨rfl, fun _ => rfl⟩
  | [], _ :: _, _, _, h => by simp [bindSubst] at h
  | .ty a :: vs, [], _, _, h => by simp [bindSubst] at h
  | .ty a :: vs, τ :: ts, S, hn, h => by
    simp only [bindSubst] at h
    cases e : bindSubst vs ts with
    | none => rw [e] at h; cases h
    | some S' =>
      rw [e] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hr, hf⟩ := bindSubst_facts vs ts S' (fun v hv => hn v (List.mem_cons_of_mem _ hv)) e
      refine ⟨hr, fun b => ?_⟩
      simp only [FMap.find?, idxTy]
      by_cases hab : a = b
      · subst hab; simp
      · have : (BVar.ty a = BVar.ty b) = False := by simp [hab]
        simp only [hab, ite_false, this, hf]
        cases idxTy b vs <;> simp
  | .row e :: vs, _, _, hn, _ => absurd rfl (hn _ List.mem_cons_self e)

theorem instCls_ok {p : Path} : ∀ (i : Nat) (bs : List BVar) (inst : List Ty) (S : Subst),
    bindSubst bs inst = some S → S.Respects →
    (∀ j, ν ((i + j + 1) :: p) = hN (inst.getD j default)) → Holds ν (instCls p i bs)
  | _, [], _, _, _, _, _ => Holds.nil
  | i, .ty a :: vs, [], _, h, _, _ => by simp [bindSubst] at h
  | i, .ty a :: vs, τ :: ts, S, h, hres, hν => by
    simp only [bindSubst] at h
    cases e : bindSubst vs ts with
    | none => rw [e] at h; cases h
    | some S' =>
      rw [e] at h
      simp only [Option.some.injEq] at h
      subst h
      refine Holds.cons.mpr ⟨?_, ?_⟩
      · simp only [Con.holds, T.ev]
        have := hν 0
        simp only [Nat.add_zero, List.getD_cons_zero] at this
        rw [this]
        exact adm_hN (hres (a, τ) List.mem_cons_self)
      · refine instCls_ok (i + 1) vs ts S' e (fun pr hp => hres pr (List.mem_cons_of_mem _ hp)) (fun j => ?_)
        have := hν (j + 1)
        simp only [List.getD_cons_succ] at this
        rw [show i + 1 + j + 1 = i + (j + 1) + 1 by omega]
        exact this
  | i, .row e :: vs, [], _, h, _, _ => by simp [bindSubst] at h
  | i, .row e :: vs, τ :: ts, S, h, hres, hν => by
    cases τ with
    | var _ => simp [bindSubst] at h
    | fn _ _ => simp [bindSubst] at h
    | con _ _ => simp [bindSubst] at h
    | record ρ tl =>
      simp only [bindSubst] at h
      cases e' : bindSubst vs ts with
      | none => rw [e'] at h; cases h
      | some S' =>
        rw [e'] at h
        simp only [Option.some.injEq] at h
        subst h
        refine instCls_ok (i + 1) vs ts S' e' hres (fun j => ?_)
        have := hν (j + 1)
        simp only [List.getD_cons_succ] at this
        rw [show i + 1 + j + 1 = i + (j + 1) + 1 by omega]
        exact this

section inst
set_option linter.unusedSectionVars false
variable {p : Path} {bs : List BVar} {g : Nat → Ty} {S : Subst}
  (hrow : S.row = []) (hty : ∀ a, FMap.find? S.ty a = (idxTy a bs).map g)
  (hν : ∀ i, ν ((i + 1) :: p) = hN (g i))
include hrow hty hν

mutual
theorem instT_ok : ∀ (τ τ' : Ty), S.apply τ = some τ' → (instT p bs τ).ev ν = hN τ'
  | .var a, τ', h => by
    simp only [Subst.apply, Option.some.injEq] at h
    subst h
    simp only [instT]
    rw [hty a]
    cases e : idxTy a bs with
    | none => simp [T.ev, hN]
    | some i => simp [T.ev, hν i]
  | .record ρ none, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i ρ' hr
      simp only [Option.some.injEq] at h
      subst h
      simp only [instT, ev_mkRec, hN, instRow_ok ρ ρ' hr]
    · cases h
  | .record ρ (some e), τ', h => by
    simp only [Subst.apply] at h
    split at h
    · cases h
    · rename_i ρ' hr
      simp only [hrow, FMap.find?, Option.some.injEq] at h
      subst h
      simp only [instT, ev_mkRec, hN, instRow_ok ρ ρ' hr]
  | .fn a b, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i a' b' ha hb
      simp only [Option.some.injEq] at h
      subst h
      simp only [instT, T.ev, hN, instT_ok a a' ha, instT_ok b b' hb]
    · cases h
  | .con as t, τ', h => by
    simp only [Subst.apply] at h
    split at h
    · rename_i as' ha
      simp only [Option.some.injEq] at h
      subst h
      simp only [instT, T.ev, hN, instList_ok as as' ha]
    · cases h
theorem instRow_ok : ∀ (ρ ρ' : Row), S.applyRow ρ = some ρ' → T.evRow ν (instRow p bs ρ) = hNRow ρ'
  | [], ρ', h => by simp only [Subst.applyRow, Option.some.injEq] at h; subst h; rfl
  | (l, x) :: r, ρ', h => by
    simp only [Subst.applyRow] at h
    split at h
    · rename_i x' r' hx hr
      simp only [Option.some.injEq] at h
      subst h
      simp only [instRow, T.evRow, hNRow, instT_ok x x' hx, instRow_ok r r' hr]
    · cases h
theorem instList_ok : ∀ (l l' : List Ty), S.applyList l = some l' → T.evList ν (instList p bs l) = hNList l'
  | [], l', h => by simp only [Subst.applyList, Option.some.injEq] at h; subst h; rfl
  | x :: r, l', h => by
    simp only [Subst.applyList] at h
    split at h
    · rename_i x' r' hx hr
      simp only [Option.some.injEq] at h
      subst h
      simp only [instList, T.evList, hNList, instT_ok x x' hx, instList_ok r r' hr]
    · cases h
end

end inst

/-- An occurrence of an exactly known scheme. -/
theorem schT_ok {p : Path} {σ : Scheme} {inst : List Ty} {τ : Ty} (hg : genAt σ inst τ = true)
    (hr : ∀ q, ν (q.reverse ++ p) = rdOcc inst τ q) : Holds ν (schT p σ).2 ∧ (schT p σ).1.ev ν = hN τ := by
  unfold schT
  split
  · exact ⟨Holds.nil, (slot hr (0))⟩
  · rename_i hrow
    simp only [Bool.not_eq_true] at hrow
    unfold genAt at hg
    split at hg
    · rename_i S hS
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨hres, happ⟩ := hg
      have hres' := (Subst.respectsB_iff S).mp hres
      obtain ⟨hrw, hty⟩ := bindSubst_facts σ.bound inst S (noRow_of σ hrow) hS
      have hν : ∀ i, ν ((i + 1) :: p) = hN (inst.getD i default) := fun i => (slot hr (i + 1))
      refine ⟨instCls_ok 0 σ.bound inst S hS hres' (fun j => ?_), instT_ok hrw hty hν _ _ happ⟩
      rw [Nat.zero_add]; exact hν j
    · cases hg

theorem occT_ok {f : TyName → TyName} {Γ : GCtx} {C : Ctx} {lv : LongId} {σ : Scheme} {is : IdStatus} {inst : List Ty} {τ : Ty}
    {p : Path} (hS : Sim ν f Γ C) (hl : C.lookupVal lv = some (σ, is)) (hg : genAt σ inst τ = true)
    (hr : ∀ q, ν (q.reverse ++ p) = rdOcc inst τ q) : Holds ν (occT Γ lv p).2 ∧ (occT Γ lv p).1.ev ν = hN τ := by
  have hok := hS.val lv σ is hl
  unfold occT
  split
  · exact ⟨Holds.nil, (slot hr (0))⟩
  · rename_i t ht
    rw [ht] at hok
    exact ⟨Holds.nil, hok.1 inst τ hg⟩
  · rename_i σ' ht
    rw [ht] at hok
    simp only [GOK] at hok
    subst hok
    exact schT_ok hg hr
  · rename_i t ht
    rw [ht] at hok
    refine ⟨Holds.nil, sc_ok t _ _ (hok.1 inst τ hg) ?_⟩
    have h0 := child (ν := ν) 0 hr (G := fun q => rdOcc inst τ (0 :: q)) (fun q => rfl)
    exact child 0 h0 (G := fun q => subAt (hN τ) q) (fun q => rfl)
  · rename_i t K ht
    rw [ht] at hok
    obtain ⟨τ0, hi, htm⟩ := hok
    obtain ⟨S, hS, hSa⟩ := instOf_gen hi hg
    obtain ⟨μ, he, hK⟩ := htm S τ hS hSa
    have h0 := child (ν := ν) 0 hr (G := fun q => rdOcc inst τ (0 :: q)) (fun q => rfl)
    exact occ_tmpl (child 0 h0 (G := fun q => subAt (hN τ) q) (fun q => rfl)) he hK

/-! ## Annotations -/

def Agree (C1 C2 : Ctx) (ns : List String) : Prop :=
  ∀ s ∈ ns, (BVar.ty (.named s) ∈ C1.U ↔ BVar.ty (.named s) ∈ C2.U) ∧
    (BVar.row (.named s) ∈ C1.U ↔ BVar.row (.named s) ∈ C2.U)

theorem Agree.sub {C1 C2 : Ctx} {ns ns' : List String} (h : Agree C1 C2 ns) (hs : ∀ s ∈ ns', s ∈ ns) :
    Agree C1 C2 ns' := fun s hm => h s (hs s hm)

section congr
set_option linter.unusedSectionVars false
variable {C1 C2 : Ctx} (hL : ∀ lc, C1.lookupTy lc = C2.lookupTy lc)
include hL

mutual
theorem elabTy_congr : ∀ t : BTy, Agree C1 C2 (bTyNames t) → elabTy C1 t = elabTy C2 t
  | .tyvar a, h => by
    have ha := h a (by simp [bTyNames])
    simp only [elabTy, ha.1, ha.2]
  | .record row, h => by
    cases row with
    | none => rfl
    | some r => simp only [elabTy, elabTyRowOpt, elabTyRow_congr r (by simpa [bTyNames] using h)]
  | .openRecord r row, h => by
    have ha := h r (by simp [bTyNames])
    simp only [elabTy, ha.2, elabTyRow_congr row (h.sub (fun s hs => by simp [bTyNames, hs]))]
  | .unit, _ => rfl
  | .tuple t1 t2 t3, h => by
    simp only [elabTy]
    rw [elabTy_congr t1 (h.sub (fun s hs => by cases t3 <;> simp [bTyNames, hs])),
      elabTy_congr t2 (h.sub (fun s hs => by cases t3 <;> simp [bTyNames, hs]))]
    cases t3 with
    | none => rfl
    | some t3 =>
      simp only [elabTyOpt]
      rw [elabTy_congr t3 (h.sub (fun s hs => by simp [bTyNames, hs]))]
  | .con c args, h => by
    simp only [elabTy, hL c, elabTyList_congr args (by simpa [bTyNames] using h)]
  | .fn t1 t2, h => by
    simp only [elabTy]
    rw [elabTy_congr t1 (h.sub (fun s hs => by simp [bTyNames, hs])),
      elabTy_congr t2 (h.sub (fun s hs => by simp [bTyNames, hs]))]
  | .paren t, h => by simp only [elabTy]; exact elabTy_congr t (by simpa [bTyNames] using h)
theorem elabTyRow_congr : ∀ r : BTyRow, Agree C1 C2 (bTyRowNames r) → elabTyRow C1 r = elabTyRow C2 r
  | .field l t none, h => by
    simp only [elabTyRow, elabTyRowOpt]
    rw [elabTy_congr t (by simpa [bTyRowNames] using h)]
  | .field l t (some rest), h => by
    simp only [elabTyRow, elabTyRowOpt]
    rw [elabTy_congr t (h.sub (fun s hs => by simp [bTyRowNames, hs])),
      elabTyRow_congr rest (h.sub (fun s hs => by simp [bTyRowNames, hs]))]
theorem elabTyList_congr : ∀ ts : List BTy, Agree C1 C2 (bTyListNames ts) → elabTyList C1 ts = elabTyList C2 ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [elabTyList]
    rw [elabTy_congr t (h.sub (fun s hs => by simp [bTyListNames, hs])),
      elabTyList_congr ts (h.sub (fun s hs => by simp [bTyListNames, hs]))]
end

end congr

mutual
theorem hN_mapTy {f : TyName → TyName} (hg : ∀ t, gN (f t) = gN t) : ∀ τ : Ty, hN (RTypes.mapTy f τ) = hN τ
  | .var _ => rfl
  | .record ρ tl => by simp only [RTypes.mapTy, hN, hNRow_mapRow hg ρ]
  | .fn a b => by simp only [RTypes.mapTy, hN, hN_mapTy hg a, hN_mapTy hg b]
  | .con as t => by simp only [RTypes.mapTy, hN, hNList_mapTys hg as, hg t]
theorem hNRow_mapRow {f : TyName → TyName} (hg : ∀ t, gN (f t) = gN t) : ∀ ρ : Row, hNRow (RTypes.mapRow f ρ) = hNRow ρ
  | [] => rfl
  | (l, x) :: r => by simp only [RTypes.mapRow, hNRow, hN_mapTy hg x, hNRow_mapRow hg r]
theorem hNList_mapTys {f : TyName → TyName} (hg : ∀ t, gN (f t) = gN t) : ∀ l : List Ty, hNList (RTypes.mapTys f l) = hNList l
  | [] => rfl
  | x :: r => by simp only [RTypes.mapTys, hNList, hN_mapTy hg x, hNList_mapTys hg r]
end

mutual
theorem vars_mapTy (f : TyName → TyName) : ∀ τ : Ty, (RTypes.mapTy f τ).vars = τ.vars
  | .var _ => rfl
  | .record ρ none => by simp only [RTypes.mapTy, Ty.vars, rowVars_mapRow f ρ]
  | .record ρ (some _) => by simp only [RTypes.mapTy, Ty.vars, rowVars_mapRow f ρ]
  | .fn a b => by simp only [RTypes.mapTy, Ty.vars, vars_mapTy f a, vars_mapTy f b]
  | .con as _ => by simp only [RTypes.mapTy, Ty.vars, listVars_mapTys f as]
theorem rowVars_mapRow (f : TyName → TyName) : ∀ ρ : Row, Ty.rowVars (RTypes.mapRow f ρ) = Ty.rowVars ρ
  | [] => rfl
  | (_, x) :: r => by simp only [RTypes.mapRow, Ty.rowVars, vars_mapTy f x, rowVars_mapRow f r]
theorem listVars_mapTys (f : TyName → TyName) : ∀ l : List Ty, Ty.listVars (RTypes.mapTys f l) = Ty.listVars l
  | [] => rfl
  | x :: r => by simp only [RTypes.mapTys, Ty.listVars, vars_mapTy f x, listVars_mapTys f r]
end

theorem labels_mapRow (f : TyName → TyName) (ρ : Row) : (RTypes.mapRow f ρ).map (·.1) = ρ.map (·.1) := by
  rw [RTypes.mapRow_eq]; simp

mutual
theorem recSorted_mapTy (f : TyName → TyName) : ∀ τ : Ty, recSorted (RTypes.mapTy f τ) = recSorted τ
  | .var _ => rfl
  | .record ρ tl => by
    simp only [RTypes.mapTy, recSorted, sortedB_labels (labels_mapRow f ρ), recSortedRow_mapRow f ρ]
  | .fn a b => by simp only [RTypes.mapTy, recSorted, recSorted_mapTy f a, recSorted_mapTy f b]
  | .con as _ => by simp only [RTypes.mapTy, recSorted, recSortedList_mapTys f as]
theorem recSortedRow_mapRow (f : TyName → TyName) : ∀ ρ : Row, recSortedRow (RTypes.mapRow f ρ) = recSortedRow ρ
  | [] => rfl
  | (_, x) :: r => by simp only [RTypes.mapRow, recSortedRow, recSorted_mapTy f x, recSortedRow_mapRow f r]
theorem recSortedList_mapTys (f : TyName → TyName) : ∀ l : List Ty, recSortedList (RTypes.mapTys f l) = recSortedList l
  | [] => rfl
  | x :: r => by simp only [RTypes.mapTys, recSortedList, recSorted_mapTy f x, recSortedList_mapTys f r]
end

theorem goodTmpl_mapTy (f : TyName → TyName) (τ : Ty) : goodTmpl (RTypes.mapTy f τ) = goodTmpl τ := by
  simp only [goodTmpl, vars_mapTy, recSorted_mapTy]

/-- The annotation's type in a derivation is, normalised, the one `annR` computes in the abstract
    context; and it has a template when `annGood` holds. -/
theorem annR_ok {f : TyName → TyName} {C A : Ctx} {ty : BTy} {τ : Ty} {r : Ty} (hT : TySim f C A)
    (he : elabTy C ty = some τ) (ha : annR A ty = some r) :
    r = hN τ ∧ (annGood A ty = true → goodTmpl τ = true) := by
  obtain ⟨U, hU, hc⟩ := RTypes.assigns_cover (fun s => BVar.ty (.named s) ∈ C.U) (fun s => BVar.row (.named s) ∈ C.U)
    (dedupL (bTyNames ty))
  have hag : Agree { C with U := U } C (bTyNames ty) := by
    intro s hs
    have hd : s ∈ dedupL (bTyNames ty) := mem_dedupL.mpr hs
    exact ⟨by simp only [(hc s).1, hd, true_and], by simp only [(hc s).2, hd, true_and]⟩
  have he' : elabTy { C with U := U } ty = some τ := by
    rw [elabTy_congr (C1 := { C with U := U }) (C2 := C) (fun lc => rfl) ty hag, he]
  have helab : elabTy { A with U := U } ty = some (RTypes.mapTy f τ) :=
    RTypes.elabTy_sim f hT.fix { C with U := U } { A with U := U } (RTypes.uEq_refl U) ty τ
      (fun lc _ => hT.look lc) he'
  have hmem : hN τ ∈ (RTypes.annCands ty).filterMap (fun U => (elabTy { A with U := U } ty).map hN) :=
    List.mem_filterMap.mpr ⟨U, hU, by rw [helab, Option.map_some, hN_mapTy hT.g]⟩
  refine ⟨?_, fun hg => ?_⟩
  · unfold annR at ha
    split at ha
    · cases ha
    · rename_i r' rest hl
      split at ha
      · rename_i hall
        simp only [Option.some.injEq] at ha
        subst ha
        rw [hl] at hmem
        rcases List.mem_cons.mp hmem with e | e
        · exact e.symm
        · have := List.all_eq_true.mp hall _ e
          simp only [beq_iff_eq] at this
          exact this.symm
      · cases ha
  · have := List.all_eq_true.mp hg U hU
    rw [helab] at this
    simpa [goodTmpl_mapTy] using this

theorem annT_ok {f : TyName → TyName} {C A : Ctx} {ty : BTy} {τ : Ty} {t : T} (hT : TySim f C A)
    (he : elabTy C ty = some τ) (ha : annT A ty = some t) : t.ev ν = hN τ := by
  unfold annT at ha
  cases hr : annR A ty with
  | none => rw [hr] at ha; cases ha
  | some r =>
    rw [hr] at ha
    simp only [Option.map_some, Option.some.injEq] at ha
    subst ha
    rw [ev_ofTy]
    exact (annR_ok hT he hr).1

/-- A value whose scheme is a canonical form of `τ` with a template. -/
theorem gok_tmpl {σ : Scheme} {τ : Ty} (hi : InstOf σ τ) (hg : goodTmpl τ = true) :
    GOK ν (tmplInfo (hN τ)) σ :=
  ⟨τ, hi, tmplInfo_ok hg⟩

/-- An annotated member whose annotation has a closed type. -/
theorem gok_ann {t : T} {τ : Ty} (U' : List BVar) (ht : t.ev ν = hN τ) (hc : t.closed = true) :
    GOK ν (.mono t) (annScheme U' τ) := by
  have hv : τ.vars = [] := vars_of_hN τ (ht ▸ closed_vars ν t hc)
  have hb : (annScheme U' τ).body = τ := canon_closed _ τ hv
  have hv' : (annScheme U' τ).body.vars = [] := by rw [hb]; exact hv
  refine ⟨fun inst τ' hg => ?_, by rw [hb, ht]⟩
  rw [genAt_closed hv' hg, hb, ht]

/-- An annotated member whose annotation has variables: its instances have the annotation's
    shape. -/
theorem gok_ann_shape {t : T} {τ : Ty} (U' : List BVar) (ht : t.ev ν = hN τ) :
    GOK ν (.shape t) (annScheme U' τ) := by
  have hb : Shp ν t (hN (annScheme U' τ).body) := Shp_canon _ (ht ▸ Shp_refl t)
  exact ⟨fun inst τ' hg => Shp_gen hb hg, hb⟩

theorem gok_mono_mv {p : Path} {τ : Ty} (h : ν p = hN τ) : GOK ν (.mono (.mv p)) (mono τ) :=
  ⟨fun inst τ' hg => by rw [genAt_mono hg]; exact h, h⟩

end StandardElm.Stat.Complete
