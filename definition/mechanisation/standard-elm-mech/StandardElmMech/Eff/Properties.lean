/-
  A Standard Definition of Elm? Mechanisation: properties of Chapter 8 and the rulings A74, A76, A88
  and A92 (plan step 4).

  * APPLY of the effect values has at most one member (sec:effects-apply).
  * A74: the boundary is defined over JSON, with byte sequences (A92); Json.Encode.Value is JSON;
    non-finite floats encode as null.
  * A76: objects are unordered (the encoding of a record does not depend on the order of its
    fields); a missing key makes decoding fail.
  * A88: JSON numbers are exact, zero has no sign, a number too large for a float decodes to an
    infinity, Int decoding is exact within IntRange.
  * A92: byte sequences are not JSON; only a byte sequence decodes at Bytes; Value carries none.
-/
import StandardElmMech.Eff.EncDec

namespace StandardElm.Eff
open StandardElm

/-! ## APPLY of the effect values -/

/-- APPLY of an effect value has at most one member ("each set has exactly one member",
    sec:effects-apply, where it is defined). -/
theorem apply_effect_singleton {b : BasVal} {vs : List Val} (h : b.isEffect = true) :
    ∀ w w', Apply b vs w → Apply b vs w' → w = w' := by
  intro w w' h1 h2
  cases h1 <;> simp [BasVal.isEffect] at h <;> cases h2 <;> first | rfl | simp_all

/-! ## A74 -/

/-- A74: at the type Json.Encode.Value a value encodes exactly as the JSON value it holds. -/
theorem a74_value_enc {v : Val} {j : BVal} : Enc .value v j ↔ v = .bv j ∧ j.isJson = true := by
  rw [enc_iff]
  constructor
  · intro h
    cases v <;> simp [enc] at h
    obtain ⟨hj, rfl⟩ := h
    exact ⟨rfl, hj⟩
  · rintro ⟨rfl, hj⟩; simp [enc, hj]

/-- A74: a boundary value decodes at Json.Encode.Value exactly when it is JSON. -/
theorem a74_value_dec {j : BVal} : (∃ v, Dec .value j v) ↔ j.isJson = true := by
  constructor
  · rintro ⟨v, h⟩
    rw [dec_iff] at h
    simp only [dec] at h
    split at h
    · assumption
    · cases h
  · intro hj; exact ⟨.bv j, .r_e_dec_value j hj⟩

/-- A74: NaN and the infinities encode as null. A float's bits are the C library's (Lean's Float is
    opaque to the kernel), so this is proved by `native_decide`. [native] -/
theorem a74_nonfinite_null :
    Enc .float (.sv (.float fNaN)) .null ∧ Enc .float (.sv (.float fInf)) .null ∧
    Enc .float (.sv (.float (-fInf))) .null := by
  refine ⟨(enc_iff _ _ _).mpr ?_, (enc_iff _ _ _).mpr ?_, (enc_iff _ _ _).mpr ?_⟩ <;> native_decide

/-- A74: null decodes at Maybe Float as Nothing. -/
theorem a74_maybe_float_null : Dec (.maybe .float) .null (.con conNothing []) := .r_e_dec_nothing _

/-! ## A76 -/

theorem fmLookup_perm {β : Type} : ∀ {r r' : List (String × β)}, r.Perm r' → (r.map (·.1)).Nodup →
    ∀ l, fmLookup r l = fmLookup r' l := by
  intro r r' hp hnd l
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    obtain ⟨k, v⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [fmLookup]
    split
    · rfl
    · exact ih hnd.2
  | swap x y r =>
    obtain ⟨k1, v1⟩ := x; obtain ⟨k2, v2⟩ := y
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
    simp only [fmLookup]
    by_cases h1 : k1 = l <;> by_cases h2 : k2 = l
    · exact absurd (h2.trans h1.symm) hnd.1.1
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  | trans h1 _ ih1 ih2 => rw [ih1 hnd, ih2 (by rwa [← (h1.map _).nodup_iff])]

theorem labelsMatch_perm {r r' : List (String × Val)} (hp : r.Perm r') (fs : PFields) :
    labelsMatch r fs = labelsMatch r' fs := by
  unfold labelsMatch
  have hm : ∀ l, l ∈ r.map (·.1) ↔ l ∈ r'.map (·.1) := fun l => (hp.map _).mem_iff
  congr 1
  · exact Bool.eq_iff_iff.mpr (by
      simp only [List.all_eq_true]
      exact ⟨fun h x hx => h x ((hm x).mpr hx), fun h x hx => h x ((hm x).mp hx)⟩)
  · exact Bool.eq_iff_iff.mpr (by
      simp only [List.all_eq_true, List.contains_iff_mem]
      exact ⟨fun h x hx => (hm x).mp (h x hx), fun h x hx => (hm x).mpr (h x hx)⟩)

theorem encFields_perm {r r' : List (String × Val)} (hp : r.Perm r') (hnd : (r.map (·.1)).Nodup) :
    ∀ fs, encFields fs r = encFields fs r'
  | .nil => by simp [encFields]
  | .cons l τ rest => by
    simp only [encFields, fieldOf, fmLookup_perm hp hnd l, encFields_perm hp hnd rest]

/-- A76: objects are unordered: the encoding of a record value does not depend on the order in
    which its fields are held (its labels distinct, as evaluation makes them). -/
theorem a76_enc_record_perm {r r' : List (String × Val)} (hp : r.Perm r')
    (hnd : (r.map (·.1)).Nodup) (fs : PFields) :
    enc (.record fs) (.record r) = enc (.record fs) (.record r') := by
  simp only [enc, labelsMatch_perm hp fs, encFields_perm hp hnd fs]

theorem decFields_none {l : String} : ∀ {fs : PFields} {kvs : BObj}, l ∈ fs.labels →
    kvs.lookup l = none → decFields fs kvs = none
  | .nil, _, h, _ => by simp [PFields.labels] at h
  | .cons l' τ rest, kvs, h, hl => by
    simp only [PFields.labels, List.mem_cons] at h
    simp only [decFields]
    rcases h with rfl | h
    · simp [hl]
    · cases kvs.lookup l' with
      | none => rfl
      | some j =>
        simp only
        cases dec τ j with
        | none => rfl
        | some v => simp [decFields_none h hl]

/-- A76: decoding fails when a key of the record type is missing from the object. -/
theorem a76_dec_missing_key {fs : PFields} {kvs : BObj} {l : String} (h : l ∈ fs.labels)
    (hl : kvs.lookup l = none) : dec (.record fs) (.obj kvs) = none := by
  simp [dec, decFields_none h hl]

/-! ## A88 -/

/-- A88: -0 encodes as the JSON number 0: a JSON number has no sign apart from its value.
    [native] (a float's bits) -/
theorem a88_negzero_enc : Enc .float (.sv (.float (-0.0))) (.num 0) :=
  (enc_iff _ _ _).mpr (by native_decide)

/-- A88: the JSON number 0 decodes at Int as 0, and only so. -/
theorem a88_zero_dec_int {v : Val} : Dec .int (.num 0) v ↔ v = .int 0 := by
  rw [dec_iff]; simp [dec, intMin, intMax]; exact eq_comm

/-- A88: JSON numbers decode at Int exactly, within IntRange; an Int encodes as itself. -/
theorem a88_int_exact (n : Int) :
    Enc .int (.int n) (.num n) ∧ (intMin ≤ n → n ≤ intMax → Dec .int (.num n) (.int n)) :=
  ⟨.r_e_enc_int n, fun h1 h2 => by
    have := Dec.r_e_dec_int (n : Rat) (by simp) (by simpa using h1) (by simpa using h2)
    simpa using this⟩

/-- A88: 2^63 is outside IntRange, and 1.5 is no Int: neither decodes at Int. -/
theorem a88_int_range :
    (¬ ∃ v, Dec .int (.num (2 ^ 63)) v) ∧ (¬ ∃ v, Dec .int (.num (jnum 15 (-1))) v) := by
  have h1 : dec .int (.num (2 ^ 63)) = none := by decide +kernel
  have h2 : dec .int (.num (jnum 15 (-1))) = none := by decide +kernel
  refine ⟨fun ⟨v, h⟩ => ?_, fun ⟨v, h⟩ => ?_⟩
  · rw [dec_iff, h1] at h; cases h
  · rw [dec_iff, h2] at h; cases h

/-- A88: a JSON number beyond the floats decodes at Float as an infinity. [native] (the rounding
    of Float.ofScientific is the C library's) -/
theorem a88_huge_dec_float : (dec .float (.num (jnum 1 400))).isSome = true ∧
    (match dec .float (.num (jnum 1 400)) with
      | some (.sv (.float x)) => x.isInf
      | _ => false) = true := by
  native_decide

/-! ## A92 -/

/-- A92: a byte sequence is not JSON. -/
theorem a92_bytes_not_json (os : List Nat) : (BVal.bytes os).isJson = false := by simp [BVal.isJson]

/-- A92: only a byte sequence decodes at Bytes, as bin# of its bytes. -/
theorem a92_dec_bytes {j : BVal} {v : Val} : Dec .bytes j v ↔
    ∃ os, j = .bytes os ∧ (∀ o ∈ os, o < 256) ∧ v = binVal os := by
  constructor
  · intro h
    rw [dec_iff] at h
    cases j <;> simp [dec] at h
    rename_i os
    obtain ⟨hall, rfl⟩ := h
    exact ⟨os, rfl, hall, rfl⟩
  · rintro ⟨os, rfl, hos, rfl⟩; exact .r_e_dec_bytes os hos

/-- A92: a byte sequence does not decode at String. -/
theorem a92_bytes_not_string (os : List Nat) : ¬ ∃ v, Dec .string (.bytes os) v := by
  rintro ⟨v, h⟩; rw [dec_iff] at h; simp [dec] at h

/-- A92: a byte sequence does not decode at List Int. -/
theorem a92_bytes_not_list (os : List Nat) : ¬ ∃ v, Dec (.list .int) (.bytes os) v := by
  rintro ⟨v, h⟩; rw [dec_iff] at h; simp [dec] at h

/-- A92: a value of Json.Encode.Value carries no byte sequence. -/
theorem a92_value_no_bytes {v : Val} {j : BVal} (h : Enc .value v j) : j.isJson = true :=
  (a74_value_enc.mp h).2

/-- A92: a list of byte sequences encodes as an array of byte sequences. -/
theorem a92_bytes_nested :
    Enc (.list .bytes) (Val.ofList [binVal [1, 2]]) (.arr (.cons (.bytes [1, 2]) .nil)) :=
  (enc_iff _ _ _).mpr (by decide +kernel)

/-! ## Canonical payload types and boundary values (D7) -/

mutual
  /-- Canonical payload types: the fields of every record type strictly increasing by label. -/
  def PTy.canonB : PTy → Bool
    | .list τ | .maybe τ | .array τ => τ.canonB
    | .tuple2 a b => a.canonB && b.canonB
    | .tuple3 a b c => a.canonB && b.canonB && c.canonB
    | .record fs => fs.canonB && fs.labelsIncreasing
    | _ => true
  def PFields.canonB : PFields → Bool
    | .nil => true
    | .cons _ τ rest => τ.canonB && rest.canonB
  def PFields.labelsIncreasing : PFields → Bool
    | .nil => true
    | .cons _ _ .nil => true
    | .cons l _ (.cons l' τ' rest) => decide (l < l') && (PFields.cons l' τ' rest).labelsIncreasing
end

def PTy.Canon (τ : PTy) : Prop := τ.canonB = true

/-! ## Numbers: a float's exact value is decimal -/
theorem pow2_of_dvd : ∀ (k d : Nat), d ∣ 2 ^ k → ∃ j, d = 2 ^ j
  | 0, d, h => ⟨0, by simpa using Nat.eq_one_of_dvd_one h⟩
  | k + 1, d, h => by
    by_cases he : d % 2 = 0
    · obtain ⟨d', rfl⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by omega⟩
      have : d' ∣ 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2] at h
        exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h
      obtain ⟨j, rfl⟩ := pow2_of_dvd k d' this
      exact ⟨j + 1, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    · have hc : Nat.Coprime d 2 := by
        unfold Nat.Coprime
        rw [Nat.gcd_comm, Nat.gcd_rec, show d % 2 = 1 by omega]
        rfl
      rw [Nat.pow_succ] at h
      exact pow2_of_dvd k d (hc.dvd_of_dvd_mul_right h)

theorem stripFactor_pow2 : ∀ (j fuel : Nat), j ≤ fuel → stripFactor 2 fuel (2 ^ j) = 1
  | 0, 0, _ => rfl
  | 0, _ + 1, _ => by simp [stripFactor]
  | j + 1, fuel + 1, h => by
    simp only [stripFactor]
    have h2 : (2 : Nat) ^ (j + 1) % 2 = 0 := by rw [Nat.pow_succ]; simp
    have hne : (2 : Nat) ^ (j + 1) ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos _)
    have hc : (2 ≥ 2 ∧ (2 : Nat) ^ (j + 1) ≠ 0 ∧ (2 : Nat) ^ (j + 1) % 2 = 0) := ⟨by decide, hne, h2⟩
    split
    · rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
      exact stripFactor_pow2 j fuel (by omega)
    · exact absurd hc ‹_›

theorem stripFactor_one (p : Nat) : ∀ fuel, stripFactor p fuel 1 = 1
  | 0 => rfl
  | fuel + 1 => by
    simp only [stripFactor]
    split
    · rename_i h; obtain ⟨hp, _, hm⟩ := h; rw [Nat.mod_eq_of_lt (by omega)] at hm; cases hm
    · rfl

theorem isDecimal_of_den_dvd {q : Rat} {k : Nat} (h : q.den ∣ 2 ^ k) : isDecimal q = true := by
  obtain ⟨j, hj⟩ := pow2_of_dvd k q.den h
  have hjle : j ≤ 2 ^ j := Nat.le_of_lt (Nat.lt_two_pow_self)
  unfold isDecimal
  rw [hj, stripFactor_pow2 j _ hjle, stripFactor_one]
  rfl

theorem isDecimal_int (n : Int) : isDecimal (n : Rat) = true :=
  isDecimal_of_den_dvd (k := 0) (by simp)

theorem dyadic_den_dvd (m : Nat) (e : Int) : ∃ k, (dyadic m e).den ∣ 2 ^ k := by
  unfold dyadic
  split
  · exact ⟨0, by rw [Rat.den_natCast]; exact Nat.one_dvd _⟩
  · refine ⟨e.natAbs, ?_⟩
    rw [Rat.den_mkRat]
    split
    · simp
    · exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

theorem floatToRat?_decimal {x : Float} {q : Rat} (h : floatToRat? x = some q) : isDecimal q = true := by
  unfold floatToRat? at h
  simp only at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    split
    all_goals first
      | (obtain ⟨k, hk⟩ := dyadic_den_dvd _ _; exact isDecimal_of_den_dvd (k := k) (by rw [Rat.neg_den]; exact hk))
      | (obtain ⟨k, hk⟩ := dyadic_den_dvd _ _; exact isDecimal_of_den_dvd hk)

/-! ## Every value of a payload type has an encoding (sec:effects-ports, the property) -/

mutual
  /-- v is a value of the payload type τ: an Int value in IntRange at int, a float at float, ...,
      a record with exactly the type's labels, an `arr# l` with l a list of values of τ, a
      canonical JSON value at Value. Step 10 connects it to elaboration. -/
  inductive HasPTy : PTy → Val → Prop where
    | int (n : Int) : intMin ≤ n → n ≤ intMax → HasPTy .int (.int n)
    | float (x : Float) : HasPTy .float (.sv (.float x))
    | tru : HasPTy .bool (.con conTrue [])
    | fls : HasPTy .bool (.con conFalse [])
    | string (s : String) : HasPTy .string (.sv (.str s))
    | bytes (os : List Nat) : (∀ o ∈ os, o < 256) → HasPTy .bytes (binVal os)
    | unit : HasPTy .unit .unit
    | nothing (τ : PTy) : HasPTy (.maybe τ) (.con conNothing [])
    | just (τ : PTy) (v : Val) : HasPTy τ v → HasPTy (.maybe τ) (.con conJust [v])
    | list (τ : PTy) (vs : List Val) : HasPTyList τ vs → HasPTy (.list τ) (Val.ofList vs)
    | array (τ : PTy) (vs : List Val) : HasPTyList τ vs → HasPTy (.array τ) (.con conArr [Val.ofList vs])
    | tuple2 (a b : PTy) (v1 v2 : Val) : HasPTy a v1 → HasPTy b v2 → HasPTy (.tuple2 a b) (.tuple v1 v2 none)
    | tuple3 (a b c : PTy) (v1 v2 v3 : Val) : HasPTy a v1 → HasPTy b v2 → HasPTy c v3 →
        HasPTy (.tuple3 a b c) (.tuple v1 v2 (some v3))
    | record (fs : PFields) (r : List (String × Val)) : labelsMatch r fs = true → HasPTyFields fs r →
        HasPTy (.record fs) (.record r)
    | value (j : BVal) : j.isJson = true → j.canonB = true → HasPTy .value (.bv j)
  inductive HasPTyList : PTy → List Val → Prop where
    | nil (τ : PTy) : HasPTyList τ []
    | cons (τ : PTy) (v : Val) (vs : List Val) : HasPTy τ v → HasPTyList τ vs → HasPTyList τ (v :: vs)
  inductive HasPTyFields : PFields → List (String × Val) → Prop where
    | nil (r : List (String × Val)) : HasPTyFields .nil r
    | cons (l : String) (τ : PTy) (fs : PFields) (r : List (String × Val)) (v : Val) :
        fieldOf r l = some v → HasPTy τ v → HasPTyFields fs r → HasPTyFields (.cons l τ fs) r
end

/-- The keys of an object, in order. -/
def BObj.keys : BObj → List String
  | .nil => []
  | .cons k _ rest => k :: rest.keys

theorem keysIncreasing_of_labels : ∀ (fs : PFields) (kvs : BObj), kvs.keys = fs.labels →
    fs.labelsIncreasing = true → kvs.keysIncreasing = true
  | .nil, .nil, _, _ => rfl
  | .cons _ _ .nil, .cons _ _ .nil, _, _ => rfl
  | .cons l _ (.cons l' τ' rest), .cons k j (.cons k' j' kvs), hk, hl => by
    simp only [BObj.keys, PFields.labels, List.cons.injEq] at hk
    obtain ⟨rfl, rfl, hk⟩ := hk
    simp only [PFields.labelsIncreasing, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [BObj.keysIncreasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hl.1, keysIncreasing_of_labels (.cons k' τ' rest) (.cons k' j' kvs)
      (by simp [BObj.keys, PFields.labels, hk]) hl.2⟩
  | .nil, .cons _ _ _, hk, _ | .cons _ _ _, .nil, hk, _ => by simp [BObj.keys, PFields.labels] at hk
  | .cons _ _ .nil, .cons _ _ (.cons _ _ _), hk, _ => by simp [BObj.keys, PFields.labels] at hk
  | .cons _ _ (.cons _ _ _), .cons _ _ .nil, hk, _ => by simp [BObj.keys, PFields.labels] at hk

theorem canonB_ofList : ∀ (js : List BVal), (∀ j ∈ js, j.canonB = true) → (BArr.ofList js).canonB = true
  | [], _ => rfl
  | j :: js, h => by
    simp only [BArr.ofList, BArr.canonB, Bool.and_eq_true]
    exact ⟨h j (by simp), canonB_ofList js (fun j' hm => h j' (by simp [hm]))⟩

mutual
  theorem enc_total : ∀ {τ : PTy} {v : Val}, HasPTy τ v → τ.canonB = true →
      ∃ j, enc τ v = some j ∧ j.canonB = true
    | _, _, .int n _ _, _ => ⟨.num n, by simp [enc], by simp [BVal.canonB, isDecimal_int]⟩
    | _, _, .float x, _ => by
      cases hq : floatToRat? x with
      | none => exact ⟨.null, by simp [enc, hq], rfl⟩
      | some q => exact ⟨.num q, by simp [enc, hq], by simp [BVal.canonB, floatToRat?_decimal hq]⟩
    | _, _, .tru, _ => ⟨.tru, by simp [enc], rfl⟩
    | _, _, .fls, _ => ⟨.fls, by simp [enc, conFalse, conTrue], rfl⟩
    | _, _, .string s, _ => ⟨.str s, by simp [enc], rfl⟩
    | _, _, .bytes os h, _ => ⟨.bytes os, enc_binVal os h, by
        simp only [BVal.canonB, List.all_eq_true, decide_eq_true_eq]; exact h⟩
    | _, _, .unit, _ => ⟨.null, by simp [enc], rfl⟩
    | _, _, .nothing τ, _ => ⟨.null, by simp [enc], rfl⟩
    | _, _, .just τ v h, hc => by
      obtain ⟨j, hj, hcj⟩ := enc_total h (by simpa [PTy.canonB] using hc)
      exact ⟨j, by simp [enc, hj, conJust, conNothing], hcj⟩
    | _, _, .list τ vs h, hc => by
      obtain ⟨js, hjs, hcj⟩ := encList_total h (by simpa [PTy.canonB] using hc)
      exact ⟨.arr (BArr.ofList js), by simp [enc, toList?_ofList, hjs],
        by simpa [BVal.canonB] using canonB_ofList js hcj⟩
    | _, _, .array τ vs h, hc => by
      obtain ⟨js, hjs, hcj⟩ := encList_total h (by simpa [PTy.canonB] using hc)
      exact ⟨.arr (BArr.ofList js), by simp [enc, toList?_ofList, hjs],
        by simpa [BVal.canonB] using canonB_ofList js hcj⟩
    | _, _, .tuple2 a b v1 v2 h1 h2, hc => by
      simp only [PTy.canonB, Bool.and_eq_true] at hc
      obtain ⟨j1, e1, c1⟩ := enc_total h1 hc.1
      obtain ⟨j2, e2, c2⟩ := enc_total h2 hc.2
      exact ⟨.arr (.cons j1 (.cons j2 .nil)), by simp [enc, e1, e2], by simp [BVal.canonB, BArr.canonB, c1, c2]⟩
    | _, _, .tuple3 a b c v1 v2 v3 h1 h2 h3, hc => by
      simp only [PTy.canonB, Bool.and_eq_true] at hc
      obtain ⟨j1, e1, c1⟩ := enc_total h1 hc.1.1
      obtain ⟨j2, e2, c2⟩ := enc_total h2 hc.1.2
      obtain ⟨j3, e3, c3⟩ := enc_total h3 hc.2
      exact ⟨.arr (.cons j1 (.cons j2 (.cons j3 .nil))), by simp [enc, e1, e2, e3],
        by simp [BVal.canonB, BArr.canonB, c1, c2, c3]⟩
    | _, _, .record fs r hl h, hc => by
      simp only [PTy.canonB, Bool.and_eq_true] at hc
      obtain ⟨kvs, ek, ck, hk⟩ := encFields_total h hc.1
      exact ⟨.obj kvs, by simp [enc, hl, ek], by
        simp only [BVal.canonB, Bool.and_eq_true]
        exact ⟨ck, keysIncreasing_of_labels fs kvs hk hc.2⟩⟩
    | _, _, .value j hj hcj, _ => ⟨j, by simp [enc, hj], hcj⟩
  theorem encList_total : ∀ {τ : PTy} {vs : List Val}, HasPTyList τ vs → τ.canonB = true →
      ∃ js, vs.mapM (enc τ) = some js ∧ ∀ j ∈ js, j.canonB = true
    | _, _, .nil _, _ => ⟨[], rfl, by simp⟩
    | _, _, .cons τ v vs h hs, hc => by
      obtain ⟨j, e, c⟩ := enc_total h hc
      obtain ⟨js, es, cs⟩ := encList_total hs hc
      refine ⟨j :: js, by simp [List.mapM_cons, e, es], ?_⟩
      intro j' hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact c
      · exact cs j' hm
  theorem encFields_total : ∀ {fs : PFields} {r : List (String × Val)}, HasPTyFields fs r →
      fs.canonB = true → ∃ kvs, encFields fs r = some kvs ∧ kvs.canonB = true ∧ kvs.keys = fs.labels
    | _, _, .nil _, _ => ⟨.nil, by simp [encFields], rfl, rfl⟩
    | _, _, .cons l τ fs r v hf h hs, hc => by
      simp only [PFields.canonB, Bool.and_eq_true] at hc
      obtain ⟨j, e, c⟩ := enc_total h hc.1
      obtain ⟨kvs, es, cs, ks⟩ := encFields_total hs hc.2
      exact ⟨.cons l j kvs, by simp [encFields, hf, e, es], by simp [BObj.canonB, c, cs],
        by simp [BObj.keys, PFields.labels, ks]⟩
end

end StandardElm.Eff
