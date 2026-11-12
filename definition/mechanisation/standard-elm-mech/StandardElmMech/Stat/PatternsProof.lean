/-
  A Standard Definition of Elm? Mechanisation: the pattern decider is correct, plan step 9
  (section "Theorems", group 4, decision D12, A97, G2-12).

  `inhabited`: every type has an inhabitant (A97), by a canonical inhabitant built along positions.
  `useful_spec`: when the usefulness algorithm returns a result, it is the truth: q is useful with
  respect to P exactly when some vector of inhabitants of the column types is covered by q and by
  no row of P (Maranget), for patterns that fit the constructor table at their columns.
  `exhDec_sound` and `irrDec_sound` follow.
-/
import StandardElmMech.Stat.Further

namespace StandardElm.Stat

/-! ## Typed patterns -/

mutual
def PTyped (tbl : ConTable) : Ty → PatN → Prop
  | _, .wild => True
  | τ, .den d => litKind τ = some d.kind ∧ d.inRange = true
  | τ, .con k args => (litKind τ).isNone ∧ ∃ as, argTys tbl τ k = some as ∧ PTypedList tbl as args
def PTypedList (tbl : ConTable) : List Ty → List PatN → Prop
  | [], [] => True
  | τ :: τs, p :: ps => PTyped tbl τ p ∧ PTypedList tbl τs ps
  | _, _ => False
end

theorem PTypedList.length_eq {tbl : ConTable} : ∀ {τs : List Ty} {ps : List PatN}, PTypedList tbl τs ps → τs.length = ps.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [PTypedList] at h
    simp [PTypedList.length_eq h.2]
  | [], _ :: _, h => by simp [PTypedList] at h
  | _ :: _, [], h => by simp [PTypedList] at h

theorem PTypedList.append {tbl : ConTable} : ∀ {τs1 τs2 : List Ty} {ps1 ps2 : List PatN},
    PTypedList tbl τs1 ps1 → PTypedList tbl τs2 ps2 → PTypedList tbl (τs1 ++ τs2) (ps1 ++ ps2)
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, h1, h2 => by
    simp only [PTypedList, List.cons_append] at h1 ⊢
    exact ⟨h1.1, PTypedList.append h1.2 h2⟩
  | [], _, _ :: _, _, h1, _ => by simp [PTypedList] at h1
  | _ :: _, _, [], _, h1, _ => by simp [PTypedList] at h1

theorem PTypedList.wilds {tbl : ConTable} : ∀ (τs : List Ty), PTypedList tbl τs (List.replicate τs.length .wild)
  | [] => trivial
  | _ :: τs => ⟨trivial, PTypedList.wilds τs⟩

theorem PTypedList.split {tbl : ConTable} : ∀ {τs1 τs2 : List Ty} {ps : List PatN},
    PTypedList tbl (τs1 ++ τs2) ps → ∃ ps1 ps2, ps = ps1 ++ ps2 ∧ PTypedList tbl τs1 ps1 ∧ PTypedList tbl τs2 ps2
  | [], _, ps, h => ⟨[], ps, rfl, trivial, h⟩
  | τ :: τs1, τs2, p :: ps, h => by
    simp only [List.cons_append, PTypedList] at h
    obtain ⟨ps1, ps2, rfl, h1, h2⟩ := PTypedList.split h.2
    exact ⟨p :: ps1, ps2, rfl, ⟨h.1, h1⟩, h2⟩
  | _ :: _, _, [], h => by simp [PTypedList] at h

/-! ## Inhabitants: construction and decomposition -/

/-- The inhabitant whose root is constructor k with children cs. -/
def Inh.mkCon (k : String) (cs : List Inh) : Inh :=
  ⟨fun p => match p with
    | [] => some (.con k cs.length)
    | i :: p' => (cs[i]?).bind fun c => c.f p'⟩

/-- The inhabitant that is one node. -/
def Inh.leaf (n : INode) : Inh := ⟨fun p => match p with
  | [] => some n
  | _ :: _ => none⟩

theorem Inh.ext {h h' : Inh} (e : ∀ p, h.f p = h'.f p) : h = h' := by
  cases h; cases h'; simp only [Inh.mk.injEq]; funext p; exact e p

theorem mkCon_sub (k : String) (cs : List Inh) (i : Nat) (hi : i < cs.length) :
    (Inh.mkCon k cs).sub i = cs[i] := by
  apply Inh.ext; intro p
  simp [Inh.sub, Inh.mkCon, List.getElem?_eq_getElem hi]

/-- The children of a node of arity n. -/
def Inh.children (h : Inh) (n : Nat) : List Inh := (List.range n).map h.sub

theorem children_length (h : Inh) (n : Nat) : (h.children n).length = n := by simp [Inh.children]

theorem children_getElem (h : Inh) (n i : Nat) (hi : i < (h.children n).length) :
    (h.children n)[i] = h.sub i := by simp [Inh.children]

theorem decompose {h : Inh} {k : String} {m : Nat} (hroot : h.f [] = some (.con k m))
    (hnone : ∀ i p, m ≤ i → h.f (i :: p) = none) : h = Inh.mkCon k (h.children m) := by
  apply Inh.ext; intro p
  match p with
  | [] => simp [Inh.mkCon, hroot, children_length]
  | i :: p =>
    simp only [Inh.mkCon]
    by_cases hi : i < m
    · have : i < (h.children m).length := by rw [children_length]; exact hi
      rw [List.getElem?_eq_getElem this, children_getElem]
      rfl
    · rw [hnone i p (by omega)]
      have : (h.children m)[i]? = none := by
        rw [List.getElem?_eq_none_iff, children_length]; omega
      rw [this]; rfl

/-- The root of an inhabitant: a node given by a clause, nothing beyond its arity. -/
theorem IsInh.root {tbl : ConTable} {mode : Mode} {τ : Ty} {h : Inh} (hh : IsInh tbl mode τ h) :
    ∃ nd, h.f [] = some nd ∧ Clause tbl mode τ nd ∧ ∀ i p, nd.arity ≤ i → h.f (i :: p) = none := by
  obtain ⟨nd, h1, h2, h3, _⟩ := hh 1
  exact ⟨nd, h1, h2, h3⟩

theorem IsInh.child {tbl : ConTable} {mode : Mode} {τ : Ty} {h : Inh} (hh : IsInh tbl mode τ h)
    {k : String} {as : List Ty} (hroot : h.f [] = some (.con k as.length)) (has : argTys tbl τ k = some as)
    (i : Nat) (hi : i < as.length) : IsInh tbl mode as[i] (h.sub i) := by
  intro n
  obtain ⟨nd, h1, _, _, h4⟩ := hh (n + 1)
  rw [hroot] at h1
  cases h1
  exact h4 k as rfl has i hi

theorem isInh_mkCon {tbl : ConTable} {mode : Mode} {τ : Ty} {k : String} {as : List Ty} {cs : List Inh}
    (hlit : (litKind τ).isNone = true) (has : argTys tbl τ k = some as) (hlen : cs.length = as.length)
    (hch : ∀ i (hi : i < as.length), IsInh tbl mode as[i] (cs[i]'(by omega))) :
    IsInh tbl mode τ (Inh.mkCon k cs) := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    refine ⟨.con k cs.length, rfl, ⟨hlit, as, has, hlen.symm⟩, ?_, ?_⟩
    · intro i p hi
      simp only [INode.arity] at hi
      simp only [Inh.mkCon]
      rw [List.getElem?_eq_none_iff.mpr hi]; rfl
    · intro k' as' he has' i hi
      simp only [INode.con.injEq] at he
      obtain ⟨rfl, hl⟩ := he
      rw [has] at has'
      cases has'
      rw [mkCon_sub k cs i (by omega)]
      exact hch i hi n

theorem isInh_leaf {tbl : ConTable} {mode : Mode} {τ : Ty} {nd : INode} (hc : Clause tbl mode τ nd)
    (ha : nd.arity = 0) : IsInh tbl mode τ (Inh.leaf nd) := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    refine ⟨nd, rfl, hc, fun i p _ => rfl, ?_⟩
    intro k as he _ i hi
    subst he
    simp only [INode.arity] at ha
    omega

/-! ## A97: every type has an inhabitant -/

theorem ctorsAt_argTys {tbl : ConTable} {τ : Ty} {k : String} {as : List Ty} (h : (k, as) ∈ ctorsAt tbl τ) :
    argTys tbl τ k = some as := by
  unfold ctorsAt at h
  split at h
  · obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp h
    cases hca : argTys tbl _ c.1 with
    | none => rw [hca] at hc; cases hc
    | some as' =>
      rw [hca] at hc
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact hca
  · cases h

theorem argTys_ctorsAt {tbl : ConTable} {τ : Ty} {k : String} {as : List Ty} (h : argTys tbl τ k = some as) :
    (k, as) ∈ ctorsAt tbl τ := by
  unfold argTys at h
  split at h
  · rename_i args t
    split at h
    · rename_i k' as0 xs t' hf
      have hm := List.mem_of_find?_eq_some hf
      have hk := List.find?_some hf
      simp only [beq_iff_eq] at hk
      subst hk
      unfold ctorsAt
      refine List.mem_filterMap.mpr ⟨(k', as0, .con xs t'), hm, ?_⟩
      have : argTys tbl (.con args t) k' = some as := by
        unfold argTys; simp only [hf]; exact h
      simp [this]
    · cases h
  · cases h

/-- The canonical node at a type: a constant of a literal type, else the first constructor that
    applies, else a wildcard; with the argument types. -/
def canonNode (tbl : ConTable) (τ : Ty) : INode × List Ty :=
  match litKind τ with
  | some 0 => (.den (.int 0), [])
  | some 1 => (.den (.char 'a'), [])
  | some _ => (.den (.str ""), [])
  | none =>
    match ctorsAt tbl τ with
    | (k, as) :: _ => (.con k as.length, as)
    | [] => (.wild, [])

def canonAt (tbl : ConTable) (τ : Ty) : Pos → Option INode
  | [] => some (canonNode tbl τ).1
  | i :: p =>
    match (canonNode tbl τ).2[i]? with
    | some τi => canonAt tbl τi p
    | none => none

def canonInh (tbl : ConTable) (τ : Ty) : Inh := ⟨canonAt tbl τ⟩

theorem litKind_spec {τ : Ty} {k : Nat} (h : litKind τ = some k) : k = 0 ∨ k = 1 ∨ k = 2 := by
  unfold litKind at h
  split at h
  · split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · split at h
        · cases h; simp
        · cases h
  · cases h

theorem canonNode_clause (tbl : ConTable) (mode : Mode) (τ : Ty) :
    Clause tbl mode τ (canonNode tbl τ).1 ∧ (canonNode tbl τ).1.arity = (canonNode tbl τ).2.length ∧
    ∀ k as, (canonNode tbl τ).1 = .con k as.length → argTys tbl τ k = some as → (canonNode tbl τ).2 = as := by
  unfold canonNode
  cases hl : litKind τ with
  | some kd =>
    rcases litKind_spec hl with rfl | rfl | rfl
    · refine ⟨⟨by simp [hl, Den.kind], by decide⟩, rfl, by intro k as h; cases h⟩
    · refine ⟨⟨by simp [hl, Den.kind], rfl⟩, rfl, by intro k as h; cases h⟩
    · refine ⟨⟨by simp [hl, Den.kind], rfl⟩, rfl, by intro k as h; cases h⟩
  | none =>
    simp only
    cases hc : ctorsAt tbl τ with
    | nil => exact ⟨⟨by simp [hl], hc⟩, rfl, by intro k as h; cases h⟩
    | cons c rest =>
      obtain ⟨k, as⟩ := c
      have has := ctorsAt_argTys (hc ▸ List.mem_cons_self : (k, as) ∈ ctorsAt tbl τ)
      refine ⟨⟨by simp [hl], as, has, rfl⟩, rfl, ?_⟩
      intro k' as' he has'
      simp only [INode.con.injEq] at he
      obtain ⟨rfl, _⟩ := he
      rw [has] at has'
      exact Option.some.inj has'

theorem canonInh_sub (tbl : ConTable) (τ : Ty) (i : Nat) (hi : i < (canonNode tbl τ).2.length) :
    (canonInh tbl τ).sub i = canonInh tbl ((canonNode tbl τ).2[i]) := by
  apply Inh.ext; intro p
  simp [Inh.sub, canonInh, canonAt, List.getElem?_eq_getElem hi]

/-- A97: every type has an inhabitant, in both modes. -/
theorem inhabited (tbl : ConTable) (mode : Mode) : ∀ (τ : Ty), IsInh tbl mode τ (canonInh tbl τ) := by
  intro τ n
  induction n generalizing τ with
  | zero => trivial
  | succ n ih =>
    obtain ⟨hc, har, has⟩ := canonNode_clause tbl mode τ
    refine ⟨(canonNode tbl τ).1, rfl, hc, ?_, ?_⟩
    · intro i p hi
      simp only [canonInh, canonAt]
      rw [har] at hi
      rw [List.getElem?_eq_none_iff.mpr hi]
    · intro k as he has' i hi
      have e := has k as he has'
      subst e
      rw [canonInh_sub tbl τ i hi]
      exact ih _

/-! ## Rows of patterns and vectors of inhabitants -/

def RowCovers : List PatN → List Inh → Prop
  | [], [] => True
  | p :: ps, h :: hs => p.covers h ∧ RowCovers ps hs
  | _, _ => False

def WT (tbl : ConTable) (mode : Mode) : List Ty → List Inh → Prop
  | [], [] => True
  | τ :: τs, h :: hs => IsInh tbl mode τ h ∧ WT tbl mode τs hs
  | _, _ => False

/-- q is useful with respect to P at the column types τs (Maranget). -/
def Useful (tbl : ConTable) (mode : Mode) (τs : List Ty) (P : List (List PatN)) (q : List PatN) : Prop :=
  ∃ hs, WT tbl mode τs hs ∧ RowCovers q hs ∧ ∀ r ∈ P, ¬ RowCovers r hs

theorem RowCovers.length : ∀ {r : List PatN} {hs : List Inh}, RowCovers r hs → r.length = hs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [RowCovers] at h; simp [RowCovers.length h.2]
  | [], _ :: _, h => by simp [RowCovers] at h
  | _ :: _, [], h => by simp [RowCovers] at h

theorem RowCovers.append : ∀ {xs ys : List PatN} {hs1 hs2 : List Inh}, xs.length = hs1.length →
    (RowCovers (xs ++ ys) (hs1 ++ hs2) ↔ RowCovers xs hs1 ∧ RowCovers ys hs2)
  | [], _, [], _, _ => by simp [RowCovers]
  | x :: xs, ys, h :: hs1, hs2, hl => by
    simp only [List.cons_append, RowCovers, List.length_cons, Nat.add_right_cancel_iff] at hl ⊢
    rw [RowCovers.append hl]; exact and_assoc.symm
  | [], _, _ :: _, _, hl => by simp at hl
  | _ :: _, _, [], _, hl => by simp at hl

theorem RowCovers.wilds : ∀ (hs : List Inh), RowCovers (List.replicate hs.length .wild) hs
  | [] => trivial
  | _ :: hs => ⟨trivial, RowCovers.wilds hs⟩

theorem WT.length {tbl : ConTable} {mode : Mode} : ∀ {τs : List Ty} {hs : List Inh}, WT tbl mode τs hs → τs.length = hs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [WT] at h; simp [WT.length h.2]
  | [], _ :: _, h => by simp [WT] at h
  | _ :: _, [], h => by simp [WT] at h

theorem WT.append {tbl : ConTable} {mode : Mode} : ∀ {τs1 τs2 : List Ty} {hs1 hs2 : List Inh},
    WT tbl mode τs1 hs1 → WT tbl mode τs2 hs2 → WT tbl mode (τs1 ++ τs2) (hs1 ++ hs2)
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, h1, h2 => by
    simp only [WT, List.cons_append] at h1 ⊢
    exact ⟨h1.1, WT.append h1.2 h2⟩
  | [], _, _ :: _, _, h1, _ => by simp [WT] at h1
  | _ :: _, _, [], _, h1, _ => by simp [WT] at h1

theorem WT.split {tbl : ConTable} {mode : Mode} : ∀ {τs1 τs2 : List Ty} {hs : List Inh},
    WT tbl mode (τs1 ++ τs2) hs → ∃ hs1 hs2, hs = hs1 ++ hs2 ∧ WT tbl mode τs1 hs1 ∧ WT tbl mode τs2 hs2
  | [], _, hs, h => ⟨[], hs, rfl, trivial, h⟩
  | τ :: τs1, τs2, h :: hs, hw => by
    simp only [List.cons_append, WT] at hw
    obtain ⟨hs1, hs2, rfl, h1, h2⟩ := WT.split hw.2
    exact ⟨h :: hs1, hs2, rfl, ⟨hw.1, h1⟩, h2⟩
  | _ :: _, _, [], h => by simp [WT] at h

theorem WT.ofGet {tbl : ConTable} {mode : Mode} : ∀ {τs : List Ty} {hs : List Inh} (hl : τs.length = hs.length),
    (∀ i (hi : i < τs.length), IsInh tbl mode τs[i] (hs[i]'(by omega))) → WT tbl mode τs hs
  | [], [], _, _ => trivial
  | τ :: τs, h :: hs, hl, hi => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    exact ⟨hi 0 (by simp), WT.ofGet hl fun i h' => hi (i + 1) (by simp; omega)⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem WT.get {tbl : ConTable} {mode : Mode} : ∀ {τs : List Ty} {hs : List Inh}, WT tbl mode τs hs →
    ∀ i (hi : i < τs.length) (hi' : i < hs.length), IsInh tbl mode τs[i] hs[i]
  | [], [], _, i, hi, _ => by simp at hi
  | _ :: _, _ :: _, h, 0, _, _ => h.1
  | _ :: _, _ :: _, h, i + 1, hi, hi' => WT.get h.2 i (by simp at hi; omega) (by simp at hi'; omega)
  | [], _ :: _, h, _, _, _ => by simp [WT] at h
  | _ :: _, [], h, _, _, _ => by simp [WT] at h

theorem coversArgs_iff : ∀ (args : List PatN) (h : Inh) (i : Nat),
    PatN.coversArgs args h i ↔ RowCovers args ((List.range' i args.length).map h.sub)
  | [], _, _ => by simp [PatN.coversArgs, RowCovers]
  | p :: ps, h, i => by
    simp only [PatN.coversArgs, List.length_cons, List.range'_succ, List.map_cons, RowCovers]
    rw [coversArgs_iff ps h (i + 1)]

theorem covers_con_iff (k : String) (args : List PatN) (h : Inh) :
    (PatN.con k args).covers h ↔ h.f [] = some (.con k args.length) ∧ RowCovers args (h.children args.length) := by
  simp only [PatN.covers, Inh.children]
  rw [coversArgs_iff, List.range_eq_range']

theorem children_mkCon (k : String) (cs : List Inh) (n : Nat) (hl : n = cs.length) :
    (Inh.mkCon k cs).children n = cs := by
  apply List.ext_getElem
  · rw [children_length]; exact hl
  · intro i h1 h2
    rw [children_getElem, mkCon_sub k cs i h2]

theorem covers_mkCon_iff (k k' : String) (args : List PatN) (cs : List Inh) :
    (PatN.con k args).covers (Inh.mkCon k' cs) ↔ k = k' ∧ args.length = cs.length ∧ RowCovers args cs := by
  rw [covers_con_iff]
  have hroot : (Inh.mkCon k' cs).f [] = some (.con k' cs.length) := rfl
  rw [hroot]
  simp only [Option.some.injEq, INode.con.injEq]
  constructor
  · rintro ⟨⟨hk, hl⟩, hr⟩
    rw [children_mkCon k' cs _ hl.symm] at hr
    exact ⟨hk.symm, hl.symm, hr⟩
  · rintro ⟨hk, hl, hr⟩
    refine ⟨⟨hk.symm, hl.symm⟩, ?_⟩
    rw [children_mkCon k' cs _ hl]
    exact hr

theorem not_covers_leaf_con (k : String) (args : List PatN) (nd : INode) (hn : ∀ n, nd ≠ .con k n) :
    ¬ (PatN.con k args).covers (Inh.leaf nd) := by
  intro h
  simp only [PatN.covers, Inh.leaf, Option.some.injEq] at h
  exact hn _ h.1

theorem covers_leaf_den (d : Den) (nd : INode) : (PatN.den d).covers (Inh.leaf nd) ↔ nd = .den d := by
  simp [PatN.covers, Inh.leaf]

theorem not_covers_mkCon_den (d : Den) (k : String) (cs : List Inh) : ¬ (PatN.den d).covers (Inh.mkCon k cs) := by
  simp [PatN.covers, Inh.mkCon]

/-! ## Specialisation and the default matrix -/

theorem specializeCon_fwd (k : String) (cs : List Inh) (hr : List Inh) : ∀ (P : List (List PatN)),
    (∃ r ∈ P, RowCovers r (Inh.mkCon k cs :: hr)) → ∃ r' ∈ specializeCon k cs.length P, RowCovers r' (cs ++ hr)
  | [], ⟨_, hm, _⟩ => by cases hm
  | r :: P, ⟨r0, hm, hc⟩ => by
    rcases List.mem_cons.mp hm with rfl | hm
    · match r0, hc with
      | .wild :: rest, hc =>
        simp only [RowCovers] at hc
        refine ⟨List.replicate cs.length .wild ++ rest, by simp [specializeCon], ?_⟩
        rw [RowCovers.append (by simp)]
        exact ⟨RowCovers.wilds cs, hc.2⟩
      | .con k' args :: rest, hc =>
        simp only [RowCovers] at hc
        obtain ⟨hk, hl, hcs⟩ := (covers_mkCon_iff _ _ _ _).mp hc.1
        subst hk
        refine ⟨args ++ rest, by simp [specializeCon], ?_⟩
        rw [RowCovers.append hl]
        exact ⟨hcs, hc.2⟩
      | .den d :: rest, hc =>
        simp only [RowCovers] at hc
        exact absurd hc.1 (not_covers_mkCon_den d k cs)
      | [], hc => simp [RowCovers] at hc
    · obtain ⟨r', hm', hc'⟩ := specializeCon_fwd k cs hr P ⟨r0, hm, hc⟩
      refine ⟨r', ?_, hc'⟩
      match r with
      | .wild :: _ => simp only [specializeCon]; exact List.mem_cons_of_mem _ hm'
      | .con k' _ :: _ =>
        simp only [specializeCon]
        split
        · exact List.mem_cons_of_mem _ hm'
        · exact hm'
      | .den _ :: _ => simpa [specializeCon] using hm'
      | [] => simpa [specializeCon] using hm'

theorem specializeCon_bwd (k : String) (cs : List Inh) (hr : List Inh) : ∀ (P : List (List PatN)),
    (∀ r ∈ P, ∀ args rest, r = .con k args :: rest → args.length = cs.length) →
    (∃ r' ∈ specializeCon k cs.length P, RowCovers r' (cs ++ hr)) → ∃ r ∈ P, RowCovers r (Inh.mkCon k cs :: hr)
  | [], _, ⟨_, hm, _⟩ => by simp [specializeCon] at hm
  | r :: P, hP, ⟨r', hm, hc⟩ => by
    have ih0 : ∀ {r1 : List PatN}, r' ∈ specializeCon k cs.length P → ∃ r0 ∈ r1 :: P, RowCovers r0 (Inh.mkCon k cs :: hr) := fun h' =>
      let ⟨r0, h0, h1⟩ := specializeCon_bwd k cs hr P (fun r hr' => hP r (List.mem_cons_of_mem _ hr')) ⟨r', h', hc⟩
      ⟨r0, List.mem_cons_of_mem _ h0, h1⟩
    match r, hm with
    | .wild :: rest, hm =>
      simp only [specializeCon, List.mem_cons] at hm
      rcases hm with rfl | hm
      · rw [RowCovers.append (by simp)] at hc
        exact ⟨.wild :: rest, List.mem_cons_self, trivial, hc.2⟩
      · exact ih0 hm
    | .con k' args :: rest, hm =>
      simp only [specializeCon] at hm
      split at hm
      · rename_i hk
        subst hk
        rcases List.mem_cons.mp hm with rfl | hm
        · have hl := hP _ List.mem_cons_self args rest rfl
          rw [RowCovers.append hl] at hc
          exact ⟨_, List.mem_cons_self, (covers_mkCon_iff _ _ _ _).mpr ⟨rfl, hl, hc.1⟩, hc.2⟩
        · exact ih0 hm
      · exact ih0 hm
    | .den _ :: _, hm => exact ih0 (by simpa [specializeCon] using hm)
    | [], hm => exact ih0 (by simpa [specializeCon] using hm)

theorem specializeDen_fwd (d : Den) (hr : List Inh) : ∀ (P : List (List PatN)),
    (∃ r ∈ P, RowCovers r (Inh.leaf (.den d) :: hr)) → ∃ r' ∈ specializeDen d P, RowCovers r' hr
  | [], ⟨_, hm, _⟩ => by cases hm
  | r :: P, ⟨r0, hm, hc⟩ => by
    rcases List.mem_cons.mp hm with rfl | hm
    · match r0, hc with
      | .wild :: rest, hc => exact ⟨rest, by simp [specializeDen], hc.2⟩
      | .den d' :: rest, hc =>
        have e := (covers_leaf_den d' _).mp hc.1
        simp only [INode.den.injEq] at e
        subst e
        exact ⟨rest, by simp [specializeDen], hc.2⟩
      | .con k args :: rest, hc => exact absurd hc.1 (not_covers_leaf_con k args _ (by intro n h; cases h))
      | [], hc => simp [RowCovers] at hc
    · obtain ⟨r', hm', hc'⟩ := specializeDen_fwd d hr P ⟨r0, hm, hc⟩
      refine ⟨r', ?_, hc'⟩
      match r with
      | .wild :: _ => simp only [specializeDen]; exact List.mem_cons_of_mem _ hm'
      | .den d' :: _ =>
        simp only [specializeDen]
        split
        · exact List.mem_cons_of_mem _ hm'
        · exact hm'
      | .con _ _ :: _ => simpa [specializeDen] using hm'
      | [] => simpa [specializeDen] using hm'

theorem specializeDen_bwd (d : Den) (hr : List Inh) : ∀ (P : List (List PatN)),
    (∃ r' ∈ specializeDen d P, RowCovers r' hr) → ∃ r ∈ P, RowCovers r (Inh.leaf (.den d) :: hr)
  | [], ⟨_, hm, _⟩ => by simp [specializeDen] at hm
  | r :: P, ⟨r', hm, hc⟩ => by
    have ih0 : ∀ {r1 : List PatN}, r' ∈ specializeDen d P → ∃ r0 ∈ r1 :: P, RowCovers r0 (Inh.leaf (.den d) :: hr) := fun h' =>
      let ⟨r0, h0, h1⟩ := specializeDen_bwd d hr P ⟨r', h', hc⟩
      ⟨r0, List.mem_cons_of_mem _ h0, h1⟩
    match r, hm with
    | .wild :: rest, hm =>
      simp only [specializeDen, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨_, List.mem_cons_self, trivial, hc⟩
      · exact ih0 hm
    | .den d' :: rest, hm =>
      simp only [specializeDen] at hm
      split at hm
      · rename_i hd
        subst hd
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨_, List.mem_cons_self, (covers_leaf_den _ _).mpr rfl, hc⟩
        · exact ih0 hm
      · exact ih0 hm
    | .con _ _ :: _, hm => exact ih0 (by simpa [specializeDen] using hm)
    | [], hm => exact ih0 (by simpa [specializeDen] using hm)

/-- A row of the default matrix covers hr: its row of P covers h :: hr, whatever h. -/
theorem defaultM_bwd (h : Inh) (hr : List Inh) : ∀ (P : List (List PatN)),
    (∃ r' ∈ defaultM P, RowCovers r' hr) → ∃ r ∈ P, RowCovers r (h :: hr)
  | [], ⟨_, hm, _⟩ => by simp [defaultM] at hm
  | r :: P, ⟨r', hm, hc⟩ => by
    have ih0 : ∀ {r1 : List PatN}, r' ∈ defaultM P → ∃ r0 ∈ r1 :: P, RowCovers r0 (h :: hr) := fun h' =>
      let ⟨r0, h0, h1⟩ := defaultM_bwd h hr P ⟨r', h', hc⟩
      ⟨r0, List.mem_cons_of_mem _ h0, h1⟩
    match r, hm with
    | .wild :: rest, hm =>
      simp only [defaultM, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨_, List.mem_cons_self, trivial, hc⟩
      · exact ih0 hm
    | .den _ :: _, hm => exact ih0 (by simpa [defaultM] using hm)
    | .con _ _ :: _, hm => exact ih0 (by simpa [defaultM] using hm)
    | [], hm => exact ih0 (by simpa [defaultM] using hm)

/-- A row of P covering h :: hr whose first pattern is not a wildcard covers h by a head the node
    h does not match; so a row of the default matrix covers hr. -/
theorem defaultM_fwd (h : Inh) (hr : List Inh) : ∀ (P : List (List PatN)),
    (∀ r ∈ P, ∀ p rest, r = p :: rest → p.isWild = false → ¬ p.covers h) →
    (∃ r ∈ P, RowCovers r (h :: hr)) → ∃ r' ∈ defaultM P, RowCovers r' hr
  | [], _, ⟨_, hm, _⟩ => by cases hm
  | r :: P, hP, ⟨r0, hm, hc⟩ => by
    rcases List.mem_cons.mp hm with rfl | hm
    · match r0, hc with
      | .wild :: rest, hc => exact ⟨rest, by simp [defaultM], hc.2⟩
      | .den d :: rest, hc => exact absurd hc.1 (hP _ List.mem_cons_self _ rest rfl rfl)
      | .con k args :: rest, hc => exact absurd hc.1 (hP _ List.mem_cons_self _ rest rfl rfl)
      | [], hc => simp [RowCovers] at hc
    · obtain ⟨r', hm', hc'⟩ := defaultM_fwd h hr P (fun r hr' => hP r (List.mem_cons_of_mem _ hr')) ⟨r0, hm, hc⟩
      refine ⟨r', ?_, hc'⟩
      match r with
      | .wild :: _ => simp only [defaultM]; exact List.mem_cons_of_mem _ hm'
      | .den _ :: _ => simpa [defaultM] using hm'
      | .con _ _ :: _ => simpa [defaultM] using hm'
      | [] => simpa [defaultM] using hm'

/-! ## Small facts the induction uses -/

theorem anyOpt_true {α : Type} {g : α → Option Bool} : ∀ {xs : List α}, useful.anyOpt xs g = some true →
    ∃ x ∈ xs, g x = some true
  | [], h => by simp [useful.anyOpt] at h
  | x :: xs, h => by
    simp only [useful.anyOpt] at h
    split at h
    · rename_i hx; exact ⟨x, List.mem_cons_self, hx⟩
    · obtain ⟨y, hy, hgy⟩ := anyOpt_true h; exact ⟨y, List.mem_cons_of_mem _ hy, hgy⟩
    · cases h

theorem anyOpt_false {α : Type} {g : α → Option Bool} : ∀ {xs : List α}, useful.anyOpt xs g = some false →
    ∀ x ∈ xs, g x = some false
  | [], _, _, hx => by cases hx
  | x :: xs, h, y, hy => by
    simp only [useful.anyOpt] at h
    split at h
    · cases h
    · rename_i hx
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact anyOpt_false h y hy
    · cases h

theorem mem_dedupL {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ dedupL l ↔ x ∈ l
  | [] => by simp [dedupL]
  | y :: l => by
    simp only [dedupL, List.mem_cons, List.mem_filter, mem_dedupL, decide_eq_true_eq, ne_eq]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact .inl h
      · exact .inr h
    · rintro (h | h)
      · exact .inl h
      · by_cases e : x = y
        · exact .inl e
        · exact .inr ⟨h, e⟩

theorem mem_headCons {P : List (List PatN)} {k : String} {args : List PatN} {rest : List PatN}
    (h : (PatN.con k args :: rest) ∈ P) : k ∈ headCons P := by
  unfold headCons
  rw [mem_dedupL]
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem mem_headDens {P : List (List PatN)} {d : Den} {rest : List PatN}
    (h : (PatN.den d :: rest) ∈ P) : d ∈ headDens P := by
  unfold headDens
  rw [mem_dedupL]
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem litCandidate_spec {kind i : Nat} {d : Den} (hk : kind = 0 ∨ kind = 1 ∨ kind = 2)
    (h : litCandidate kind i = some d) : d.kind = kind ∧ d.inRange = true := by
  rcases hk with rfl | rfl | rfl
  · simp only [litCandidate] at h
    split at h
    · rename_i hle
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, ?_⟩
      simp only [Den.inRange, decide_eq_true_eq]
      exact ⟨by omega, hle⟩
    · cases h
  · simp only [litCandidate] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    · cases h
  · simp only [litCandidate, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem missingDen_spec {kind : Nat} {ds : List Den} {d : Den} (hk : kind = 0 ∨ kind = 1 ∨ kind = 2)
    (h : missingDen kind ds = some d) : d ∉ ds ∧ d.kind = kind ∧ d.inRange = true := by
  unfold missingDen at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hm
  refine ⟨fun hd => ?_, litCandidate_spec hk hi⟩
  simp at hp
  exact hp hd

theorem ptyped_den {tbl : ConTable} {τ : Ty} {d : Den} (h : PTyped tbl τ (.den d)) :
    litKind τ = some d.kind ∧ d.inRange = true := by simpa [PTyped] using h

theorem ptyped_con {tbl : ConTable} {τ : Ty} {k : String} {args : List PatN} (h : PTyped tbl τ (.con k args)) :
    (litKind τ).isNone ∧ ∃ as, argTys tbl τ k = some as ∧ PTypedList tbl as args := by
  simpa [PTyped] using h

theorem specializeCon_typed {tbl : ConTable} {τ : Ty} {τr : List Ty} {k : String} {as : List Ty}
    (has : argTys tbl τ k = some as) : ∀ (P : List (List PatN)), (∀ r ∈ P, PTypedList tbl (τ :: τr) r) →
    ∀ r ∈ specializeCon k as.length P, PTypedList tbl (as ++ τr) r
  | [], _, r, hr => by simp [specializeCon] at hr
  | r0 :: P, hP, r, hr => by
    have ih := specializeCon_typed has P (fun r h => hP r (List.mem_cons_of_mem _ h))
    have h0 := hP r0 List.mem_cons_self
    match r0, hr, h0 with
    | .wild :: rest, hr, h0 =>
      simp only [specializeCon, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact PTypedList.append (PTypedList.wilds as) h0.2
      · exact ih r hr
    | .con k' args :: rest, hr, h0 =>
      simp only [specializeCon] at hr
      split at hr
      · rename_i hk
        subst hk
        rcases List.mem_cons.mp hr with rfl | hr
        · obtain ⟨_, as', has', hargs⟩ := ptyped_con h0.1
          rw [has] at has'
          cases has'
          exact PTypedList.append hargs h0.2
        · exact ih r hr
      · exact ih r hr
    | .den _ :: _, hr, _ => exact ih r (by simpa [specializeCon] using hr)
    | [], hr, _ => exact ih r (by simpa [specializeCon] using hr)

theorem specializeDen_typed {tbl : ConTable} {τ : Ty} {τr : List Ty} (d : Den) : ∀ (P : List (List PatN)),
    (∀ r ∈ P, PTypedList tbl (τ :: τr) r) → ∀ r ∈ specializeDen d P, PTypedList tbl τr r
  | [], _, r, hr => by simp [specializeDen] at hr
  | r0 :: P, hP, r, hr => by
    have ih := specializeDen_typed d P (fun r h => hP r (List.mem_cons_of_mem _ h))
    have h0 := hP r0 List.mem_cons_self
    match r0, hr, h0 with
    | .wild :: rest, hr, h0 =>
      simp only [specializeDen, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact h0.2
      · exact ih r hr
    | .den d' :: rest, hr, h0 =>
      simp only [specializeDen] at hr
      split at hr
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact h0.2
        · exact ih r hr
      · exact ih r hr
    | .con _ _ :: _, hr, _ => exact ih r (by simpa [specializeDen] using hr)
    | [], hr, _ => exact ih r (by simpa [specializeDen] using hr)

theorem defaultM_typed {tbl : ConTable} {τ : Ty} {τr : List Ty} : ∀ (P : List (List PatN)),
    (∀ r ∈ P, PTypedList tbl (τ :: τr) r) → ∀ r ∈ defaultM P, PTypedList tbl τr r
  | [], _, r, hr => by simp [defaultM] at hr
  | r0 :: P, hP, r, hr => by
    have ih := defaultM_typed P (fun r h => hP r (List.mem_cons_of_mem _ h))
    have h0 := hP r0 List.mem_cons_self
    match r0, hr, h0 with
    | .wild :: rest, hr, h0 =>
      simp only [defaultM, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact h0.2
      · exact ih r hr
    | .den _ :: _, hr, _ => exact ih r (by simpa [defaultM] using hr)
    | .con _ _ :: _, hr, _ => exact ih r (by simpa [defaultM] using hr)
    | [], hr, _ => exact ih r (by simpa [defaultM] using hr)

/-- Rows typed at τ :: τr whose head is constructor k have as many arguments as k takes. -/
theorem con_rows_length {tbl : ConTable} {τ : Ty} {τr : List Ty} {k : String} {as : List Ty}
    (has : argTys tbl τ k = some as) {P : List (List PatN)} (hP : ∀ r ∈ P, PTypedList tbl (τ :: τr) r) :
    ∀ r ∈ P, ∀ args rest, r = .con k args :: rest → args.length = as.length := by
  intro r hr args rest he
  subst he
  obtain ⟨_, as', has', hargs⟩ := ptyped_con (hP _ hr).1
  rw [has] at has'
  cases has'
  exact (PTypedList.length_eq hargs).symm

/-! ## The three cases of a wildcard -/

theorem useful_default_fwd {tbl : ConTable} {mode : Mode} {τ : Ty} {τr : List Ty} {P : List (List PatN)}
    {qs : List PatN} : Useful tbl mode (τ :: τr) P (.wild :: qs) → Useful tbl mode τr (defaultM P) qs := by
  rintro ⟨hs, hw, hc, hn⟩
  match hs, hw, hc with
  | h :: hr, ⟨_, hwr⟩, ⟨_, hcr⟩ =>
    refine ⟨hr, hwr, hcr, fun r' hr' hc' => ?_⟩
    obtain ⟨r, hr0, hc0⟩ := defaultM_bwd h hr P ⟨r', hr', hc'⟩
    exact hn r hr0 hc0

theorem useful_default_bwd {tbl : ConTable} {mode : Mode} {τ : Ty} {τr : List Ty} {P : List (List PatN)}
    {qs : List PatN} (h0 : Inh) (hh0 : IsInh tbl mode τ h0)
    (hnot : ∀ r ∈ P, ∀ p rest, r = p :: rest → p.isWild = false → ¬ p.covers h0) :
    Useful tbl mode τr (defaultM P) qs → Useful tbl mode (τ :: τr) P (.wild :: qs) := by
  rintro ⟨hr, hwr, hcr, hn⟩
  refine ⟨h0 :: hr, ⟨hh0, hwr⟩, ⟨trivial, hcr⟩, fun r hr0 hc0 => ?_⟩
  obtain ⟨r', hr', hc'⟩ := defaultM_fwd h0 hr P hnot ⟨r, hr0, hc0⟩
  exact hn r' hr' hc'

/-- A constructor that applies at τ: a vector useful after specialising by it gives one for the
    wildcard. -/
theorem useful_of_spec {tbl : ConTable} {mode : Mode} {τ : Ty} {τr : List Ty} {P : List (List PatN)}
    {qs : List PatN} {k : String} {as : List Ty} (hlit : (litKind τ).isNone = true) (hc : (k, as) ∈ ctorsAt tbl τ) :
    Useful tbl mode (as ++ τr) (specializeCon k as.length P) (List.replicate as.length .wild ++ qs) →
    Useful tbl mode (τ :: τr) P (.wild :: qs) := by
  rintro ⟨hs', hw', hc', hn'⟩
  have has := ctorsAt_argTys hc
  obtain ⟨cs, hr, rfl, hwc, hwr⟩ := WT.split hw'
  have hcl : cs.length = as.length := (WT.length hwc).symm
  refine ⟨Inh.mkCon k cs :: hr, ⟨isInh_mkCon hlit has hcl (fun i hi => WT.get hwc i hi _), hwr⟩, ?_, ?_⟩
  · rw [RowCovers.append (by simp [hcl])] at hc'
    exact ⟨trivial, hc'.2⟩
  · intro r hr0 hcov
    obtain ⟨r', hr', hc''⟩ := specializeCon_fwd k cs hr P ⟨r, hr0, hcov⟩
    rw [hcl] at hr'
    exact hn' r' hr' hc''

/-- An inhabitant whose root is constructor k with argument types as, decomposed. -/
theorem useful_spec_of {tbl : ConTable} {mode : Mode} {τ : Ty} {τr : List Ty} {P : List (List PatN)}
    {qs : List PatN} {h : Inh} {hr : List Inh} {k : String} {as : List Ty}
    (hP : ∀ r ∈ P, PTypedList tbl (τ :: τr) r) (has : argTys tbl τ k = some as) (hh : IsInh tbl mode τ h)
    (hroot : h.f [] = some (.con k as.length)) (hwr : WT tbl mode τr hr)
    (hn : ∀ r ∈ P, ¬ RowCovers r (h :: hr)) (qa : List PatN) (hqa : RowCovers qa (h.children as.length))
    (hcr : RowCovers qs hr) :
    Useful tbl mode (as ++ τr) (specializeCon k as.length P) (qa ++ qs) := by
  obtain ⟨nd, hnd, _, hbeyond⟩ := hh.root
  rw [hroot] at hnd
  cases hnd
  have hdec := decompose hroot (fun i p hi => hbeyond i p hi)
  refine ⟨h.children as.length ++ hr, WT.append (WT.ofGet (by rw [children_length]) (fun i hi => ?_)) hwr, ?_, ?_⟩
  · rw [children_getElem]; exact hh.child hroot has i hi
  · rw [RowCovers.append (by rw [RowCovers.length hqa])]
    exact ⟨hqa, hcr⟩
  · intro r' hr' hcov
    have hP' := con_rows_length has hP
    rw [← children_length h as.length] at hr' hP'
    obtain ⟨r, hr0, hc0⟩ := specializeCon_bwd k (h.children as.length) hr P (by
      intro r hr0 args rest he; rw [children_length]; rw [children_length] at hP'; exact hP' r hr0 args rest he) ⟨r', hr', hcov⟩
    rw [← hdec] at hc0
    exact hn r hr0 hc0

theorem spec_of_useful {tbl : ConTable} {mode : Mode} {τ : Ty} {τr : List Ty} {P : List (List PatN)}
    {qs : List PatN} (hlit : litKind τ = none) (hne : ctorsAt tbl τ ≠ [])
    (hP : ∀ r ∈ P, PTypedList tbl (τ :: τr) r) :
    Useful tbl mode (τ :: τr) P (.wild :: qs) →
    ∃ c ∈ ctorsAt tbl τ, Useful tbl mode (c.2 ++ τr) (specializeCon c.1 c.2.length P)
      (List.replicate c.2.length .wild ++ qs) := by
  rintro ⟨hs, hw, hc, hn⟩
  match hs, hw, hc with
  | h :: hr, ⟨hh, hwr⟩, ⟨_, hcr⟩ =>
    obtain ⟨nd, hnd, hcl, _⟩ := hh.root
    match nd, hcl with
    | .den _, hcl => simp [Clause, hlit] at hcl
    | .other, hcl => simp [Clause, hlit] at hcl
    | .wild, hcl => exact absurd hcl.2 hne
    | .con k n, hcl =>
      obtain ⟨_, as, has, hl⟩ := hcl
      subst hl
      refine ⟨(k, as), argTys_ctorsAt has, ?_⟩
      exact useful_spec_of hP has hh hnd hwr hn _ (by
        have := RowCovers.wilds (h.children as.length); rwa [children_length] at this) hcr

/-! ## Usefulness is decided -/

theorem useful_spec (tbl : ConTable) (mode : Mode) : ∀ (f : Nat) (τs : List Ty) (P : List (List PatN))
    (q : List PatN) (b : Bool), useful tbl mode f τs P q = some b → PTypedList tbl τs q →
    (∀ r ∈ P, PTypedList tbl τs r) → (b = true ↔ Useful tbl mode τs P q) := by
  intro f
  induction f with
  | zero => intro τs P q b h; simp [useful] at h
  | succ f ih =>
    intro τs P q b h hq hP
    match q, τs, hq with
    | [], [], _ =>
      simp only [useful, Option.some.injEq] at h
      subst h
      constructor
      · intro hb
        refine ⟨[], trivial, trivial, ?_⟩
        intro r hr
        simp only [List.isEmpty_iff] at hb
        subst hb
        cases hr
      · rintro ⟨hs, hw, _, hn⟩
        match hs, hw with
        | [], _ =>
          cases P with
          | nil => rfl
          | cons r P =>
            exfalso
            have hr := hP r List.mem_cons_self
            match r, hr with
            | [], _ => exact hn [] List.mem_cons_self trivial
    | [], _ :: _, hq => simp [PTypedList] at hq
    | _ :: _, [], hq => simp [PTypedList] at hq
    | p :: qs, τ :: τr, hq =>
      obtain ⟨hp, hqs⟩ := hq
      match p, hp with
      | .con k args, hp =>
        obtain ⟨hlit, as, has, hargs⟩ := ptyped_con hp
        have hlen : args.length = as.length := (PTypedList.length_eq hargs).symm
        simp only [useful, List.headD_cons, List.tail_cons, has] at h
        rw [hlen] at h
        rw [ih _ _ _ _ h (PTypedList.append hargs hqs) (specializeCon_typed has P hP)]
        constructor
        · rintro ⟨hs', hw', hc', hn'⟩
          obtain ⟨cs, hr, rfl, hwc, hwr⟩ := WT.split hw'
          have hcl : cs.length = as.length := (WT.length hwc).symm
          refine ⟨Inh.mkCon k cs :: hr, ⟨isInh_mkCon hlit has hcl (fun i hi => WT.get hwc i hi _), hwr⟩, ?_, ?_⟩
          · rw [RowCovers.append (by omega)] at hc'
            exact ⟨(covers_mkCon_iff _ _ _ _).mpr ⟨rfl, by omega, hc'.1⟩, hc'.2⟩
          · intro r hr0 hcov
            obtain ⟨r', hr', hc''⟩ := specializeCon_fwd k cs hr P ⟨r, hr0, hcov⟩
            rw [hcl] at hr'
            exact hn' r' hr' hc''
        · rintro ⟨hs, hw, hc, hn⟩
          match hs, hw, hc with
          | h :: hr, ⟨hh, hwr⟩, ⟨hch, hcr⟩ =>
            obtain ⟨hroot, hargsc⟩ := (covers_con_iff _ _ _).mp hch
            rw [hlen] at hroot hargsc
            exact useful_spec_of hP has hh hroot hwr hn args hargsc hcr
      | .den d, hp =>
        obtain ⟨hlk, hin⟩ := ptyped_den hp
        simp only [useful, List.headD_cons, List.tail_cons] at h
        rw [ih _ _ _ _ h hqs (specializeDen_typed d P hP)]
        constructor
        · rintro ⟨hr, hwr, hcr, hn⟩
          refine ⟨Inh.leaf (.den d) :: hr, ⟨isInh_leaf ⟨hlk, hin⟩ rfl, hwr⟩, ⟨(covers_leaf_den _ _).mpr rfl, hcr⟩, ?_⟩
          intro r hr0 hc0
          obtain ⟨r', hr', hc'⟩ := specializeDen_fwd d hr P ⟨r, hr0, hc0⟩
          exact hn r' hr' hc'
        · rintro ⟨hs, hw, hc, hn⟩
          match hs, hw, hc with
          | h :: hr, ⟨hh, hwr⟩, ⟨hch, hcr⟩ =>
            have hroot : h.f [] = some (.den d) := hch
            obtain ⟨nd, hnd, _, hbeyond⟩ := hh.root
            rw [hroot] at hnd
            cases hnd
            have hleaf : h = Inh.leaf (.den d) := Inh.ext fun p => match p with
              | [] => hroot
              | i :: p => hbeyond i p (Nat.zero_le _)
            refine ⟨hr, hwr, hcr, ?_⟩
            intro r' hr' hc'
            obtain ⟨r, hr0, hc0⟩ := specializeDen_bwd d hr P ⟨r', hr', hc'⟩
            rw [← hleaf] at hc0
            exact hn r hr0 hc0
      | .wild, _ =>
        dsimp only [useful, List.headD_cons, List.tail_cons] at h
        cases hl : litKind τ with
        | some kind =>
          rw [hl] at h
          have hk := litKind_spec hl
          cases mode with
          | exh =>
            simp only at h
            rw [ih _ _ _ _ h hqs (defaultM_typed P hP)]
            refine ⟨useful_default_bwd (Inh.leaf .other) (isInh_leaf ⟨rfl, by simp [hl]⟩ rfl) ?_, useful_default_fwd⟩
            intro r _ p rest _ hw hcov
            match p with
            | .wild => simp [PatN.isWild] at hw
            | .den d => exact absurd ((covers_leaf_den _ _).mp hcov) (by intro e; cases e)
            | .con k args => exact not_covers_leaf_con k args _ (by intro n e; cases e) hcov
          | irr =>
            simp only at h
            cases hm : missingDen kind (headDens P) with
            | none => rw [hm] at h; cases h
            | some d0 =>
              rw [hm] at h
              simp only at h
              obtain ⟨hnot, hkd, hin⟩ := missingDen_spec hk hm
              rw [ih _ _ _ _ h hqs (defaultM_typed P hP)]
              refine ⟨useful_default_bwd (Inh.leaf (.den d0)) (isInh_leaf ⟨by rw [hl, hkd], hin⟩ rfl) ?_,
                useful_default_fwd⟩
              intro r hr p rest he hw hcov
              match p with
              | .wild => simp [PatN.isWild] at hw
              | .den d =>
                have e := (covers_leaf_den _ _).mp hcov
                simp only [INode.den.injEq] at e
                subst e
                subst he
                exact hnot (mem_headDens hr)
              | .con k args => exact not_covers_leaf_con k args _ (by intro n e; cases e) hcov
        | none =>
          rw [hl] at h
          simp only at h
          split at h
          · rename_i hcs
            simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hcs
            obtain ⟨hne, _⟩ := hcs
            have hlit : (litKind τ).isNone = true := by simp [hl]
            cases b with
            | true =>
              obtain ⟨c, hc, hgc⟩ := anyOpt_true h
              have hasc := ctorsAt_argTys hc
              have hu := (ih _ _ _ _ hgc (PTypedList.append (PTypedList.wilds c.2) hqs)
                (specializeCon_typed hasc P hP)).mp rfl
              exact ⟨fun _ => useful_of_spec hlit hc hu, fun _ => rfl⟩
            | false =>
              refine ⟨(fun e => by cases e), fun hu => ?_⟩
              obtain ⟨c, hc, hu'⟩ := spec_of_useful hl hne hP hu
              have hgc := anyOpt_false h c hc
              have hasc := ctorsAt_argTys hc
              exact absurd hu' (by
                intro hu''
                have := (ih _ _ _ _ hgc (PTypedList.append (PTypedList.wilds c.2) hqs)
                  (specializeCon_typed hasc P hP)).mpr hu''
                cases this)
          · rename_i hcs
            rw [ih _ _ _ _ h hqs (defaultM_typed P hP)]
            refine ⟨?_, useful_default_fwd⟩
            cases hcz : ctorsAt tbl τ with
            | nil =>
              refine useful_default_bwd (Inh.leaf .wild) (isInh_leaf ⟨by simp [hl], hcz⟩ rfl) ?_
              intro r _ p rest _ hw hcov
              match p with
              | .wild => simp [PatN.isWild] at hw
              | .den d => exact absurd ((covers_leaf_den _ _).mp hcov) (by intro e; cases e)
              | .con k args => exact not_covers_leaf_con k args _ (by intro n e; cases e) hcov
            | cons c0 rest0 =>
              rw [hcz] at hcs
              simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, List.all_eq_true] at hcs
              have hex : ∃ c ∈ ctorsAt tbl τ, (headCons P).contains c.1 = false := by
                rw [hcz]
                apply Classical.byContradiction
                intro hno
                apply hcs
                intro x hx
                cases hcx : (headCons P).contains x.1
                · exact absurd ⟨x, hx, hcx⟩ hno
                · rfl
              obtain ⟨c, hc, hnc⟩ := hex
              have hasc := ctorsAt_argTys hc
              let cs := c.2.map (canonInh tbl)
              have hcl : cs.length = c.2.length := by simp [cs]
              refine useful_default_bwd (Inh.mkCon c.1 cs)
                (isInh_mkCon (by simp [hl]) hasc hcl (fun i hi => by simp [cs]; exact inhabited tbl mode _)) ?_
              intro r hr p rest he hw hcov
              match p with
              | .wild => simp [PatN.isWild] at hw
              | .den d => exact not_covers_mkCon_den d _ _ hcov
              | .con k args =>
                obtain ⟨hk, _, _⟩ := (covers_mkCon_iff _ _ _ _).mp hcov
                subst hk
                subst he
                have := mem_headCons hr
                simp [List.contains_iff_mem, this] at hnc

/-! ## The deciders -/

theorem typedB_sound (tbl : ConTable) : ∀ (f : Nat) (τ : Ty) (p : PatN), PatN.typedB tbl f τ p = true → PTyped tbl τ p
  | 0, _, _, h => by simp [PatN.typedB] at h
  | _ + 1, _, .wild, _ => trivial
  | _ + 1, τ, .den d, h => by
    simp only [PatN.typedB, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, h.2⟩
  | f + 1, τ, .con k args, h => by
    simp only [PatN.typedB] at h
    split at h
    · rename_i as has
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨h.1.2, as, has, typedList_sound f as args h.2⟩
    · cases h
where
  typedList_sound : ∀ (f : Nat) (τs : List Ty) (ps : List PatN), PatN.typedB.typedList tbl f τs ps = true →
      PTypedList tbl τs ps
    | f, τ :: τs, p :: ps, h => by
      simp only [PatN.typedB.typedList, Bool.and_eq_true] at h
      exact ⟨typedB_sound tbl f τ p h.1, typedList_sound f τs ps h.2⟩
    | _, [], [], _ => trivial
    | _, [], _ :: _, h => by simp [PatN.typedB.typedList] at h
    | _, _ :: _, [], h => by simp [PatN.typedB.typedList] at h

/-- res:core-exhaustiveness, decided. -/
theorem exhDec_sound {tbl : ConTable} {τ : Ty} {ps : List PatN} (ht : ∀ p ∈ ps, PTyped tbl τ p)
    (h : exhDec tbl τ ps = true) : ExhProp tbl τ ps := by
  unfold exhDec at h
  simp only [beq_iff_eq] at h
  have hspec := useful_spec tbl .exh _ [τ] (ps.map ([·])) [.wild] false h ⟨trivial, trivial⟩ (by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact ⟨ht p hp, trivial⟩)
  intro hh hinh
  apply Classical.byContradiction
  intro hno
  have : Useful tbl .exh [τ] (ps.map ([·])) [.wild] := by
    refine ⟨[hh], ⟨hinh, trivial⟩, ⟨trivial, trivial⟩, ?_⟩
    intro r hr hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact hno ⟨p, hp, hc.1⟩
  cases hspec.mpr this

/-- res:core-irredundancy, decided. -/
theorem irrDec_sound {tbl : ConTable} {τ : Ty} {ps : List PatN} (ht : ∀ p ∈ ps, PTyped tbl τ p)
    (h : irrDec tbl τ ps = true) : IrrProp tbl τ ps := by
  intro j hj
  unfold irrDec at h
  have hjr := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [beq_iff_eq] at hjr
  have hget : ps.getD j .wild = ps[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [hget] at hjr
  have hspec := useful_spec tbl .irr _ [τ] ((ps.take j).map ([·])) [ps[j]] true hjr
    ⟨ht _ (List.getElem_mem hj), trivial⟩ (by
      intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact ⟨ht p (List.mem_of_mem_take hp), trivial⟩)
  obtain ⟨hs, hw, hc, hn⟩ := hspec.mp rfl
  match hs, hw, hc with
  | [hh], ⟨hinh, _⟩, ⟨hcj, _⟩ =>
    refine ⟨hh, hinh, hcj, fun i hi hci => ?_⟩
    apply hn [ps[i]] _ ⟨hci, trivial⟩
    apply List.mem_map.mpr
    refine ⟨ps[i], ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp⟩

theorem matchOKB_sound {tbl : ConTable} {τ : Ty} {ps : List PatN} (h : matchOKB tbl τ ps = true) :
    MatchOK tbl τ ps := by
  unfold matchOKB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨ht, he⟩, hi⟩ := h
  have ht' : ∀ p ∈ ps, PTyped tbl τ p := fun p hp => typedB_sound tbl _ τ p (ht p hp)
  exact ⟨exhDec_sound ht' he, irrDec_sound ht' hi⟩

theorem exhOneB_sound {tbl : ConTable} {τ : Ty} {p : PatN} (h : exhOneB tbl τ p = true) :
    ExhProp tbl τ [p] := by
  unfold exhOneB at h
  simp only [Bool.and_eq_true] at h
  exact exhDec_sound (fun q hq => by simp at hq; subst hq; exact typedB_sound tbl _ τ _ h.1) h.2

/-! ## The further restrictions of a derivation, decided -/

mutual
theorem furtherAtExpB_sound (tbl : ConTable) : (a : AAtExp) → furtherAtExpB tbl a = true → FurtherAtExp tbl a
  | .tuple e1 e2 e3, h => by
    simp only [furtherAtExpB, Bool.and_eq_true] at h
    exact ⟨furtherExpB_sound tbl e1 h.1.1, furtherExpB_sound tbl e2 h.1.2, furtherExpOptB_sound tbl e3 h.2⟩
  | .record row, h => by
    simp only [furtherAtExpB] at h
    exact furtherExpRowOptB_sound tbl row h
  | .update _ _ _ row, h => by
    simp only [furtherAtExpB] at h
    exact furtherExpRowB_sound tbl row h
  | .letE d e, h => by
    simp only [furtherAtExpB, Bool.and_eq_true] at h
    exact ⟨furtherDecB_sound tbl d h.1, furtherExpB_sound tbl e h.2⟩
  | .paren e, h => by
    simp only [furtherAtExpB] at h
    exact furtherExpB_sound tbl e h
  | .scon _ _, _ => trivial
  | .var _ _ _, _ => trivial
  | .con _ _ _, _ => trivial
  | .op _ _ _, _ => trivial
  | .unit, _ => trivial
  | .nil _, _ => trivial
theorem furtherExpRowB_sound (tbl : ConTable) : (r : AExpRow) → furtherExpRowB tbl r = true → FurtherExpRow tbl r
  | .field _ e rest, h => by
    simp only [furtherExpRowB, Bool.and_eq_true] at h
    exact ⟨furtherExpB_sound tbl e h.1, furtherExpRowOptB_sound tbl rest h.2⟩
theorem furtherExpRowOptB_sound (tbl : ConTable) : (r : Option AExpRow) → furtherExpRowOptB tbl r = true →
    FurtherExpRowOpt tbl r
  | none, _ => trivial
  | some r, h => furtherExpRowB_sound tbl r h
theorem furtherExpB_sound (tbl : ConTable) : (a : AExp) → furtherExpB tbl a = true → FurtherExp tbl a
  | .atexp a, h => by
    simp only [furtherExpB] at h
    exact furtherAtExpB_sound tbl a h
  | .app e a, h => by
    simp only [furtherExpB, Bool.and_eq_true] at h
    exact ⟨furtherExpB_sound tbl e h.1, furtherAtExpB_sound tbl a h.2⟩
  | .lam p e, h => by
    simp only [furtherExpB, Bool.and_eq_true] at h
    exact ⟨exhOneB_sound h.1, furtherExpB_sound tbl e h.2⟩
  | .caseE e m, h => by
    simp only [furtherExpB, Bool.and_eq_true] at h
    exact ⟨furtherExpB_sound tbl e h.1.1, matchOKB_sound h.1.2, furtherMatchB_sound tbl m h.2⟩
theorem furtherExpOptB_sound (tbl : ConTable) : (e : Option AExp) → furtherExpOptB tbl e = true → FurtherExpOpt tbl e
  | none, _ => trivial
  | some e, h => furtherExpB_sound tbl e h
theorem furtherMatchB_sound (tbl : ConTable) : (m : AMatch) → furtherMatchB tbl m = true → FurtherMatch tbl m
  | .mk (.mk _ e) rest, h => by
    simp only [furtherMatchB, Bool.and_eq_true] at h
    exact ⟨furtherExpB_sound tbl e h.1, furtherMatchOptB_sound tbl rest h.2⟩
theorem furtherMatchOptB_sound (tbl : ConTable) : (m : Option AMatch) → furtherMatchOptB tbl m = true →
    FurtherMatchOpt tbl m
  | none, _ => trivial
  | some m, h => furtherMatchB_sound tbl m h
theorem furtherDecB_sound (tbl : ConTable) : (d : ADec) → furtherDecB tbl d = true → FurtherDec tbl d
  | .val _ vb, h => by
    simp only [furtherDecB] at h
    exact furtherValBindB_sound tbl vb h
theorem furtherValBindB_sound (tbl : ConTable) : (vb : AValBind) → furtherValBindB tbl vb = true →
    FurtherValBind tbl vb
  | .var _ _ _ e rest, h => by
    simp only [furtherValBindB, Bool.and_eq_true] at h
    exact ⟨furtherExpB_sound tbl e h.1, furtherValBindOptB_sound tbl rest h.2⟩
  | .pat p e, h => by
    simp only [furtherValBindB, Bool.and_eq_true] at h
    exact ⟨exhOneB_sound h.1, furtherExpB_sound tbl e h.2⟩
theorem furtherValBindOptB_sound (tbl : ConTable) : (vb : Option AValBind) → furtherValBindOptB tbl vb = true →
    FurtherValBindOpt tbl vb
  | none, _ => trivial
  | some vb, h => furtherValBindB_sound tbl vb h
end

theorem furtherTopDecB_sound (tbl : ConTable) : (a : ATopDec) → furtherTopDecB tbl a = true → FurtherTopDec tbl a
  | .value _ vb, h => furtherValBindB_sound tbl vb h
  | .seq a1 a2, h => by
    simp only [furtherTopDecB, Bool.and_eq_true] at h
    exact ⟨furtherTopDecB_sound tbl a1 h.1, furtherTopDecB_sound tbl a2 h.2⟩
  | .types _ _ _ _, _ => trivial
  | .port _ _ _, _ => trivial

theorem furtherModInB_sound {B : SBasis} {E : Env} {a : AModule} (h : furtherModInB B E a = true) :
    FurtherModIn B E a := by
  unfold furtherModInB at h
  unfold FurtherModIn
  split at h
  · rename_i d hd; exact furtherTopDecB_sound _ d h
  · trivial

end StandardElm.Stat
