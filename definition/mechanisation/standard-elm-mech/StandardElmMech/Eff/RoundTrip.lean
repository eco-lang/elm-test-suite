/-
  A Standard Definition of Elm? Mechanisation: the round trip of encoding and decoding
  (effects.tex, sec:effects-ports, the third sentence of the property; A88's exceptions), plan
  step 4.

  `roundtrip`: a value of a canonical payload type that encodes to j decodes from j to itself, with
  the fields of each record in label order (`normVal`), except where A88 says otherwise (`NoExc`):
  a float component that is NaN, an infinity or -0, a `Just v` whose v encodes as null, an Int
  outside IntRange, or a record with a repeated label. One fact about Lean's floats is assumed,
  `FloatRoundTrip`: a finite float other than -0 is the float nearest its own exact value. Lean's
  Float is opaque to the kernel (its bits and `Float.ofScientific` are the C library's), so the
  fact cannot be proved, nor decided at one float (no lemma relates a float to its bits); it is a
  named hypothesis of `roundtrip` only, never an axiom. The exceptions are shown to be needed.
-/
import StandardElmMech.Eff.MkObj
import StandardElmMech.Eff.Normalise
import StandardElmMech.Show

namespace StandardElm.Eff
open StandardElm

/-- The one fact about Lean's Float the round trip needs: a finite float other than -0 is the
    nearest float to its own exact value. -/
def FloatRoundTrip : Prop :=
  ∀ (x : Float) (q : Rat), isNegZero x = false → floatToRat? x = some q → ratToFloat q = x

mutual
  /-- The exceptions of the property do not occur in v at τ: no float component is NaN, an
      infinity or -0; no `Just v'` at a Maybe position has a v' that encodes as null; every Int
      is in IntRange; and no record repeats a label. -/
  def NoExc : PTy → Val → Prop
    | .int, .sv (.int n) => intMin ≤ n ∧ n ≤ intMax
    | .float, .sv (.float x) => (floatToRat? x).isSome = true ∧ isNegZero x = false
    | .maybe τ, .con _ [v] => enc τ v ≠ some .null ∧ NoExc τ v
    | .list τ, v => ∀ vs, v.toList? = some vs → NoExcList τ vs
    | .array τ, .con _ [l] => ∀ vs, l.toList? = some vs → NoExcList τ vs
    | .tuple2 a b, .tuple v1 v2 _ => NoExc a v1 ∧ NoExc b v2
    | .tuple3 a b c, .tuple v1 v2 (some v3) => NoExc a v1 ∧ NoExc b v2 ∧ NoExc c v3
    | .record fs, .record r => (r.map (·.1)).Nodup ∧ NoExcFields fs r
    | _, _ => True
  def NoExcList (τ : PTy) : List Val → Prop
    | [] => True
    | v :: vs => NoExc τ v ∧ NoExcList τ vs
  def NoExcFields : PFields → List (String × Val) → Prop
    | .nil, _ => True
    | .cons l τ rest, r => (∀ v, fieldOf r l = some v → NoExc τ v) ∧ NoExcFields rest r
end

/-! ## Lists and their values -/

theorem toList?_some (l : Val) : ∀ {vs : List Val}, l.toList? = some vs → l = Val.ofList vs := by
  induction l using Val.toList?.induct with
  | case1 => intro vs h; simp [Val.toList?] at h; subst h; rfl
  | case2 c hc => intro vs h; simp [Val.toList?, hc] at h
  | case3 hd tl ih =>
    intro vs h
    simp only [Val.toList?, ite_true] at h
    cases ht : tl.toList? with
    | none => rw [ht] at h; cases h
    | some ts =>
      rw [ht] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      simp [Val.ofList, ih ht]
  | case4 c hd tl hc => intro vs h; simp [Val.toList?, hc] at h
  | case5 t h1 h2 =>
    intro vs h
    unfold Val.toList? at h
    split at h
    · exact absurd rfl (h1 _)
    · exact absurd rfl (h2 _ _ _)
    · cases h

theorem normVal_ofList : ∀ vs : List Val, normVal (Val.ofList vs) = Val.ofList (vs.map normVal)
  | [] => by simp [Val.ofList, normVal, normList]
  | v :: vs => by simp [Val.ofList, normVal, normList, normVal_ofList vs]

theorem mapM_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {r : List β} :
    (a :: l).mapM f = some r ↔ ∃ b bs, f a = some b ∧ l.mapM f = some bs ∧ r = b :: bs := by
  simp only [List.mapM_cons]
  cases h1 : f a with
  | none => simp
  | some b =>
    cases h2 : l.mapM f with
    | none => simp
    | some bs => simp [eq_comm]

theorem mapM_byteOf : ∀ (vs : List Val) (os : List Nat), vs.mapM byteOf? = some os →
    vs.map normVal = os.map (fun (o : Nat) => Val.int (o : Int)) ∧ ∀ o ∈ os, o < 256
  | [], os, h => by simp at h; subst h; simp
  | v :: vs, os, h => by
    obtain ⟨b, bs, h1, h2, rfl⟩ := mapM_cons_some.mp h
    obtain ⟨ih1, ih2⟩ := mapM_byteOf vs bs h2
    unfold byteOf? at h1
    split at h1
    · rename_i n
      split at h1
      · rename_i hn
        simp only [Option.some.injEq] at h1; subst h1
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, ih1]
          simp [normVal, Int.toNat_of_nonneg hn.1]
        · intro o ho
          simp only [List.mem_cons] at ho
          rcases ho with rfl | ho
          · omega
          · exact ih2 o ho
      · cases h1
    · cases h1

theorem keys_nodup_mem_eq {β : Type} : ∀ {l : List (String × β)} {a b : String × β},
    (l.map (·.1)).Nodup → a ∈ l → b ∈ l → a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: rest, a, b, hn, ha, hb, he => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at ha hb
    have notin : ∀ x ∈ rest, x.1 ≠ c.1 := fun x hx hx' => hn.1 (hx' ▸ List.mem_map_of_mem hx)
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd he.symm (notin b hb)
    · exact absurd he (notin a ha)
    · exact keys_nodup_mem_eq hn.2 ha hb he

/-- The decoded fields of a record value encoded at fs: each label of fs, in the type's order,
    with the normalised value of its field. -/
def decodedFields (fs : PFields) (r : List (String × Val)) : List (String × Val) :=
  fs.labels.map fun l => (l, normVal ((fieldOf r l).getD .unit))

theorem lookup_encFields_other {l : String} : ∀ {fs : PFields} {r : List (String × Val)} {o : BObj},
    encFields fs r = some o → l ∉ fs.labels → o.lookup l = none
  | .nil, _, o, h, _ => by simp [encFields] at h; subst h; rfl
  | .cons l' τ rest, r, o, h, hl => by
    simp only [PFields.labels, List.mem_cons, not_or] at hl
    simp only [encFields] at h
    split at h
    · split at h
      · rename_i jl orest _ _
        simp only [Option.some.injEq] at h; subst h
        have : (l' == l) = false := by simpa using Ne.symm hl.1
        simp only [BObj.lookup, this]
        exact lookup_encFields_other ‹_› hl.2
      · cases h
    · cases h

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 (List.mem_map_of_mem hm), nodup_of_map f h.2⟩

theorem normFields_eq : ∀ r : List (String × Val), normFields r = r.map fun p => (p.1, normVal p.2)
  | [] => rfl
  | (l, v) :: r => by simp [normFields, normFields_eq r]

theorem fieldOf_of_mem : ∀ {r : List (String × Val)} {l : String} {v : Val},
    (r.map (·.1)).Nodup → (l, v) ∈ r → fieldOf r l = some v
  | [], _, _, _, h => by simp at h
  | (k, w) :: r, l, v, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at h
    unfold fieldOf fmLookup
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
    · have hk : k ≠ l := fun he => hn.1 (he ▸ List.mem_map_of_mem (f := (·.1)) h)
      have : (k == l) = false := by simpa using hk
      simp only [this]
      exact fieldOf_of_mem hn.2 h

theorem fieldOf_some_mem : ∀ {r : List (String × Val)} {l : String} {v : Val},
    fieldOf r l = some v → (l, v) ∈ r
  | [], _, _, h => by simp [fieldOf, fmLookup] at h
  | (k, w) :: r, l, v, h => by
    unfold fieldOf fmLookup at h
    split at h
    · rename_i hk; simp at hk h; subst hk h; simp
    · exact List.mem_cons_of_mem _ (fieldOf_some_mem h)

theorem mem_keys_fieldOf {r : List (String × Val)} {l : String} (h : l ∈ r.map (·.1)) :
    ∃ v, fieldOf r l = some v := by
  induction r with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    unfold fieldOf fmLookup
    by_cases hk : k = l
    · subst hk; simp
    · have : (k == l) = false := by simpa using hk
      simp only [this]
      simp only [List.map_cons, List.mem_cons] at h
      exact ih (h.resolve_left (Ne.symm hk))

/-- With distinct labels, the fields of a record value whose labels are the type's, sorted by
    label and normalised, are the decoded fields. -/
theorem sortFields_eq (fs : PFields) (r : List (String × Val)) (hm : labelsMatch r fs = true)
    (hn : (r.map (·.1)).Nodup) (hinc : fs.labels.Pairwise (· < ·)) :
    decodedFields fs r = sortFields (normFields r) := by
  simp only [labelsMatch, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hm
  have hlnd : fs.labels.Nodup := hinc.imp fun {a b} h he => by subst he; exact String.lt_irrefl _ h
  let le : String × Val → String × Val → Bool := fun a b => decide (a.1 ≤ b.1)
  have hkeysL : (decodedFields fs r).map (·.1) = fs.labels := by simp [decodedFields, Function.comp_def]
  have hLnd : ((decodedFields fs r).map (·.1)).Nodup := by rw [hkeysL]; exact hlnd
  have hperm : (normFields r).Perm (decodedFields fs r) := by
    rw [normFields_eq]
    have nd1 : (r.map fun p => (p.1, normVal p.2)).Nodup := by
      have : ((r.map fun p => (p.1, normVal p.2)).map (·.1)).Nodup := by
        simpa [Function.comp_def] using hn
      exact nodup_of_map _ this
    have nd2 : (decodedFields fs r).Nodup := nodup_of_map _ hLnd
    apply (List.perm_ext_iff_of_nodup nd1 nd2).mpr
    intro x
    constructor
    · intro hx
      obtain ⟨⟨l, v⟩, hp, rfl⟩ := List.mem_map.mp hx
      have hl : l ∈ fs.labels := hm.1 l (List.mem_map_of_mem (f := (·.1)) hp)
      simp only [decodedFields, List.mem_map]
      exact ⟨l, hl, by simp [fieldOf_of_mem hn hp]⟩
    · intro hx
      simp only [decodedFields, List.mem_map] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨v, hv⟩ := mem_keys_fieldOf (hm.2 l hl)
      exact List.mem_map.mpr ⟨(l, v), fieldOf_some_mem hv, by simp [hv]⟩
  unfold sortFields
  apply List.Perm.eq_of_pairwise (le := fun a b => le a b = true)
  · intro a b ha hb hab hba
    have hab' : a.1 ≤ b.1 := of_decide_eq_true hab
    have hba' : b.1 ≤ a.1 := of_decide_eq_true hba
    have hb' : b ∈ decodedFields fs r := ((List.mergeSort_perm _ _).trans hperm).mem_iff.mp hb
    exact keys_nodup_mem_eq hLnd ha hb' (String.le_antisymm hab' hba')
  · have hp : (decodedFields fs r).map (·.1) |>.Pairwise (· < ·) := by rw [hkeysL]; exact hinc
    rw [List.pairwise_map] at hp
    exact hp.imp fun {a b} h => decide_eq_true (String.not_lt.mp (String.lt_asymm h))
  · exact List.pairwise_mergeSort (le := fun a b : String × Val => decide (a.1 ≤ b.1))
      (fun a b c hab hbc => decide_eq_true (String.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (fun a b => by
        rcases String.le_total a.1 b.1 with h | h <;> simp [h])
      _
  · exact hperm.symm.trans (List.mergeSort_perm _ _).symm

/-- Unfold `enc` at a hypothesis `enc τ v = some j` with τ a constructor, keeping the cases whose
    pattern matches. -/
macro "enc_cases " h:ident : tactic =>
  `(tactic| (unfold enc at $h:ident; split at $h:ident <;>
    first | contradiction | (simp at $h:ident; done) | skip) <;>
    (try simp only [Option.some.injEq] at $h:ident) <;> (try injections) <;> (try subst_vars))

mutual
  theorem rt (hF : FloatRoundTrip) : ∀ (τ : PTy) (v : Val) (j : BVal), τ.canonB = true →
      enc τ v = some j → NoExc τ v → dec τ j = some (normVal v)
    | .int, v, j, _, he, hx => by
      enc_cases he
      rename_i n
      simp only [NoExc] at hx
      simp [dec, Rat.den_intCast, Rat.num_intCast, hx.1, hx.2, normVal]
    | .float, v, j, _, he, hx => by
      enc_cases he
      rename_i x
      simp only [NoExc] at hx
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hx.1
      simp [Option.elim, hq, dec, floatToRat?_decimal hq, hF x q hx.2 hq, normVal]
    | .bool, v, j, _, he, hx => by
      enc_cases he
      rename_i c
      split at he
      · rename_i hc; simp at hc; subst hc; cases he; simp [dec, Val.bool, normVal, normList]
      · split at he
        · rename_i _ hc; simp at hc; subst hc; cases he; simp [dec, Val.bool, normVal, normList]
        · cases he
    | .string, v, j, _, he, hx => by
      enc_cases he
      simp [dec, normVal]
    | .unit, v, j, _, he, hx => by
      enc_cases he
      simp [dec, normVal]
    | .bytes, v, j, _, he, hx => by
      enc_cases he
      rename_i c l
      split at he
      · rename_i hc
        simp at hc; subst hc
        cases hl : l.toList? with
        | none => simp [hl] at he
        | some vs =>
          simp only [hl] at he
          cases ho : vs.mapM byteOf? with
          | none => simp [ho] at he
          | some os =>
            simp [ho] at he; subst he
            obtain ⟨h1, h2⟩ := mapM_byteOf vs os ho
            have hall : os.all (· < 256) = true := List.all_eq_true.mpr (fun o ho => decide_eq_true (h2 o ho))
            simp only [dec, hall, ite_true, normVal, normList, toList?_some l hl, normVal_ofList, h1]
      · cases he
    | .value, v, j, _, he, hx => by
      enc_cases he
      rename_i j'
      split at he
      · rename_i hj; cases he; simp [dec, hj, normVal]
      · cases he
    | .maybe τ, v, j, hτ, he, hx => by
      simp only [PTy.canonB] at hτ
      enc_cases he
      rename_i τ c args
      split at he
      · rename_i hc
        obtain ⟨hc1, rfl⟩ := hc
        simp at hc1; subst hc1; cases he
        simp [dec, normVal, normList]
      · split at he
        · rename_i _ hc
          simp at hc; subst hc
          match args, he, hx with
          | [w], he, hx =>
            simp only at he
            simp only [NoExc] at hx
            have hd : dec (.maybe τ) j = (dec τ j).map fun v => .con conJust [v] := by
              cases j with
              | null => exact absurd he hx.1
              | _ => rfl
            rw [hd, rt hF τ w j hτ he hx.2]
            simp [normVal, normList]
          | [], he, _ => cases he
          | _ :: _ :: _, he, _ => cases he
        · cases he
    | .list τ, v, j, hτ, he, hx => by
      simp only [PTy.canonB] at hτ
      simp only [enc] at he
      cases hl : v.toList? with
      | none => rw [hl] at he; cases he
      | some vs =>
        simp only [hl] at he
        cases hm : vs.mapM (enc τ) with
        | none => simp [hm] at he
        | some js =>
          simp only [hm, Option.map_some, Option.some.injEq] at he; subst he
          simp only [NoExc] at hx
          have hd := rtList hF τ hτ vs js hm (hx vs hl)
          simp only [dec, BArr.toList_ofList, hd, Option.map_some, toList?_some v hl, normVal_ofList]
    | .array τ, v, j, hτ, he, hx => by
      simp only [PTy.canonB] at hτ
      enc_cases he
      rename_i τ c l
      split at he
      · rename_i hc
        simp at hc; subst hc
        cases hl : l.toList? with
        | none => simp [hl] at he
        | some vs =>
          simp only [hl] at he
          cases hm : vs.mapM (enc τ) with
          | none => simp [hm] at he
          | some js =>
            simp only [hm, Option.map_some, Option.some.injEq] at he; subst he
            simp only [NoExc] at hx
            have hd := rtList hF τ hτ vs js hm (hx vs hl)
            simp only [dec, BArr.toList_ofList, hd, Option.map_some, normVal, normList,
              toList?_some l hl, normVal_ofList]
      · cases he
    | .tuple2 a b, v, j, hτ, he, hx => by
      simp only [PTy.canonB, Bool.and_eq_true] at hτ
      enc_cases he
      rename_i a b v1 v2
      split at he
      · rename_i j1 j2 h1 h2
        cases he
        simp only [NoExc] at hx
        simp [dec, rt hF a v1 j1 hτ.1 h1 hx.1, rt hF b v2 j2 hτ.2 h2 hx.2, normVal]
      · cases he
    | .tuple3 a b c, v, j, hτ, he, hx => by
      simp only [PTy.canonB, Bool.and_eq_true] at hτ
      enc_cases he
      rename_i a b c v1 v2 v3
      split at he
      · rename_i j1 j2 j3 h1 h2 h3
        cases he
        simp only [NoExc] at hx
        simp [dec, rt hF a v1 j1 hτ.1.1 h1 hx.1, rt hF b v2 j2 hτ.1.2 h2 hx.2.1,
          rt hF c v3 j3 hτ.2 h3 hx.2.2, normVal]
      · cases he
    | .record fs, v, j, hτ, he, hx => by
      simp only [PTy.canonB, Bool.and_eq_true] at hτ
      enc_cases he
      rename_i fs r
      split at he
      · rename_i hm
        cases ho : encFields fs r with
        | none => rw [ho] at he; cases he
        | some o =>
          rw [ho] at he; simp only [Option.map_some, Option.some.injEq] at he; subst he
          simp only [NoExc] at hx
          have hinc := (labelsIncreasing_iff fs).mp hτ.2
          have hnd : fs.labels.Nodup := hinc.imp fun {a b} h he => by subst he; exact String.lt_irrefl _ h
          have hdf := rtFields hF fs r o o hτ.1 hnd ho (fun _ _ => rfl) hx.2
          simp only [dec, hdf, Option.map_some, normVal]
          congr 2
          exact sortFields_eq fs r hm hx.1 hinc
      · cases he
  theorem rtList (hF : FloatRoundTrip) (τ : PTy) (hτ : τ.canonB = true) : ∀ (vs : List Val) (js : List BVal),
      vs.mapM (enc τ) = some js → NoExcList τ vs → js.mapM (dec τ) = some (vs.map normVal)
    | [], js, h, _ => by simp at h; subst h; rfl
    | v :: vs, js, h, hx => by
      obtain ⟨b, bs, h1, h2, rfl⟩ := mapM_cons_some.mp h
      simp only [NoExcList] at hx
      simp [List.mapM_cons, rt hF τ v b hτ h1 hx.1, rtList hF τ hτ vs bs h2 hx.2]
  theorem rtFields (hF : FloatRoundTrip) : ∀ (fs : PFields) (r : List (String × Val)) (o O : BObj),
      fs.canonB = true → fs.labels.Nodup → encFields fs r = some o →
      (∀ l ∈ fs.labels, O.lookup l = o.lookup l) → NoExcFields fs r →
      decFields fs O = some (decodedFields fs r)
    | .nil, _, _, _, _, _, _, _, _ => by simp [decFields, decodedFields, PFields.labels]
    | .cons l τ rest, r, o, O, hc, hn, he, hl, hx => by
      simp only [PFields.canonB, Bool.and_eq_true] at hc
      simp only [PFields.labels, List.nodup_cons] at hn
      simp only [NoExcFields] at hx
      simp only [encFields] at he
      split at he
      · rename_i v hv
        split at he
        · rename_i jl orest h1 h2
          simp only [Option.some.injEq] at he; subst he
          have hO : O.lookup l = some jl := by
            rw [hl l (by simp [PFields.labels])]; simp [BObj.lookup]
          have hrest : ∀ l' ∈ rest.labels, O.lookup l' = orest.lookup l' := by
            intro l' hl'
            rw [hl l' (by simp [PFields.labels, hl'])]
            have : (l == l') = false := by
              simp only [beq_eq_false_iff_ne]; intro he; exact hn.1 (he ▸ hl')
            simp [BObj.lookup, this]
          simp only [decFields, hO, rt hF τ v jl hc.1 h1 (hx.1 v hv),
            rtFields hF rest r orest O hc.2 hn.2 h2 hrest hx.2]
          simp [decodedFields, PFields.labels, hv]
        · cases he
      · cases he
end

/-- The round trip (sec:effects-ports, the property): a value of a canonical payload type that
    encodes to j decodes from j to itself with its records' fields in label order, unless one of
    the exceptions of A88 occurs in it; given the one fact about Lean's floats it uses. -/
theorem roundtrip {τ : PTy} {v : Val} {j : BVal} (hF : FloatRoundTrip) (hτ : τ.Canon)
    (he : Enc τ v j) (hx : NoExc τ v) : Dec τ j (normVal v) :=
  (dec_iff _ _ _).mpr (rt hF τ v j hτ ((enc_iff _ _ _).mp he) hx)

/-! ## The exceptions are needed -/

/-- A88: -0 encodes as 0, which decodes as +0: the round trip loses the sign. [native] (a float's
    bits) -/
theorem a88_roundtrip_negzero :
    enc .float (.sv (.float (-0.0))) = some (.num 0) ∧
    (dec .float (.num 0)).map (fun v => match v with | .sv (.float x) => isNegZero x | _ => true) = some false ∧
    isNegZero (-0.0) = true := by
  native_decide

/-- NaN encodes as null, which does not decode at Float. [native] (a float's bits) -/
theorem roundtrip_nan_fails : enc .float (.sv (.float fNaN)) = some .null ∧ dec .float .null = none := by
  native_decide

/-- `Just Nothing` at Maybe (Maybe Int) encodes as null, which decodes as Nothing. -/
theorem roundtrip_just_nothing :
    enc (.maybe (.maybe .int)) (.con conJust [.con conNothing []]) = some .null ∧
    dec (.maybe (.maybe .int)) .null = some (.con conNothing []) :=
  ⟨by decide +kernel, rfl⟩

end StandardElm.Eff
