/-
  A Standard Definition of Elm? Mechanisation: the book's relations Enc_τ and Dec_τ (effects.tex,
  sec:effects-ports, the rules r:e-enc-* and r:e-dec-*), plan step 4.

  One constructor per rule, named from its label (15 encoding rules, 14 decoding rules); the
  sequences, options and record fields are auxiliary relations whose constructors are `seq_*` and
  `opt_*`. The array rules have the book's `AppVal` premise (APPLY of Array.toList and
  Array.fromList), which is why the relations come after Rules.lean. Neither relation has a logged
  twin (plan decision D4, as the plan's disposition of the step's first issue reads it): the only
  applications in them are of Array.toList and Array.fromList, which log nothing.

  `enc_iff` and `dec_iff` prove the relations equal to the functions of EncFn.lean (D8).
-/
import StandardElmMech.Rules
import StandardElmMech.InitialBasis
import StandardElmMech.Eff.EncFn

namespace StandardElm.Eff
open StandardElm

/-- (τ1, τ2 [, τ3]) as a payload type: the tuple rules cover both arities with an option, as
    `Val.tuple` does. -/
def tupleTy (τ1 τ2 : PTy) : Option PTy → PTy
  | none => .tuple2 τ1 τ2
  | some τ3 => .tuple3 τ1 τ2 τ3

/-- The elements of an array: j3 (if any) before the rest. -/
def BArr.prepend : Option BVal → BArr → BArr
  | none, rest => rest
  | some j, rest => .cons j rest

/-- A byte sequence as a value: bin# of the list of its bytes. -/
def binVal (os : List Nat) : Val := .con conBin [Val.ofList (os.map fun (o : Nat) => Val.int (o : Int))]

mutual
  /-- Enc_τ(v) = j. -/
  inductive Enc : PTy → Val → BVal → Prop where
    /-- r:e-enc-int -/
    | r_e_enc_int (n : Int) : Enc .int (.sv (.int n)) (.num n)
    /-- r:e-enc-float -/
    | r_e_enc_float (x : Float) (q : Rat) : floatToRat? x = some q → Enc .float (.sv (.float x)) (.num q)
    /-- r:e-enc-float-null -/
    | r_e_enc_float_null (x : Float) : floatToRat? x = none → Enc .float (.sv (.float x)) .null
    /-- r:e-enc-true -/
    | r_e_enc_true : Enc .bool (.con conTrue []) .tru
    /-- r:e-enc-false -/
    | r_e_enc_false : Enc .bool (.con conFalse []) .fls
    /-- r:e-enc-string -/
    | r_e_enc_string (s : String) : Enc .string (.sv (.str s)) (.str s)
    /-- r:e-enc-bytes -/
    | r_e_enc_bytes (os : List Nat) : (∀ o ∈ os, o < 256) → Enc .bytes (binVal os) (.bytes os)
    /-- r:e-enc-unit -/
    | r_e_enc_unit : Enc .unit .unit .null
    /-- r:e-enc-nothing -/
    | r_e_enc_nothing (τ : PTy) : Enc (.maybe τ) (.con conNothing []) .null
    /-- r:e-enc-just -/
    | r_e_enc_just (τ : PTy) (v : Val) (j : BVal) : Enc τ v j → Enc (.maybe τ) (.con conJust [v]) j
    /-- r:e-enc-list -/
    | r_e_enc_list (τ : PTy) (vs : List Val) (js : BArr) :
        EncSeq τ vs js → Enc (.list τ) (Val.ofList vs) (.arr js)
    /-- r:e-enc-array -/
    | r_e_enc_array (τ : PTy) (v v' : Val) (j : BVal) :
        AppVal (bas .arrayToList) v v' → Enc (.list τ) v' j → Enc (.array τ) v j
    /-- r:e-enc-tuple -/
    | r_e_enc_tuple (τ1 τ2 : PTy) (τ3 : Option PTy) (v1 v2 : Val) (v3 : Option Val) (j1 j2 : BVal)
        (j3 : Option BVal) :
        Enc τ1 v1 j1 → Enc τ2 v2 j2 → EncOpt τ3 v3 j3 →
        Enc (tupleTy τ1 τ2 τ3) (.tuple v1 v2 v3) (.arr (.cons j1 (.cons j2 (BArr.prepend j3 .nil))))
    /-- r:e-enc-record: Dom r = Dom ρ, the object's keys the type's labels, fieldwise -/
    | r_e_enc_record (fs : PFields) (r : List (String × Val)) (kvs : BObj) :
        labelsMatch r fs = true → EncFields fs r kvs → Enc (.record fs) (.record r) (.obj kvs)
    /-- r:e-enc-value -/
    | r_e_enc_value (j : BVal) : j.isJson = true → Enc .value (.bv j) j
  inductive EncSeq : PTy → List Val → BArr → Prop where
    | seq_nil (τ : PTy) : EncSeq τ [] .nil
    | seq_cons (τ : PTy) (v : Val) (vs : List Val) (j : BVal) (js : BArr) :
        Enc τ v j → EncSeq τ vs js → EncSeq τ (v :: vs) (.cons j js)
  inductive EncOpt : Option PTy → Option Val → Option BVal → Prop where
    | opt_none : EncOpt none none none
    | opt_some (τ : PTy) (v : Val) (j : BVal) : Enc τ v j → EncOpt (some τ) (some v) (some j)
  inductive EncFields : PFields → List (String × Val) → BObj → Prop where
    | seq_nil (r : List (String × Val)) : EncFields .nil r .nil
    | seq_cons (l : String) (τ : PTy) (fs : PFields) (r : List (String × Val)) (v : Val) (j : BVal)
        (kvs : BObj) :
        fieldOf r l = some v → Enc τ v j → EncFields fs r kvs → EncFields (.cons l τ fs) r (.cons l j kvs)
end

mutual
  /-- Dec_τ(j) = v. -/
  inductive Dec : PTy → BVal → Val → Prop where
    /-- r:e-dec-int -/
    | r_e_dec_int (q : Rat) : q.den = 1 → intMin ≤ q.num → q.num ≤ intMax → Dec .int (.num q) (.int q.num)
    /-- r:e-dec-float -/
    | r_e_dec_float (q : Rat) : isDecimal q = true → Dec .float (.num q) (.sv (.float (ratToFloat q)))
    /-- r:e-dec-true -/
    | r_e_dec_true : Dec .bool .tru (.con conTrue [])
    /-- r:e-dec-false -/
    | r_e_dec_false : Dec .bool .fls (.con conFalse [])
    /-- r:e-dec-string -/
    | r_e_dec_string (s : String) : Dec .string (.str s) (.sv (.str s))
    /-- r:e-dec-bytes -/
    | r_e_dec_bytes (os : List Nat) : (∀ o ∈ os, o < 256) → Dec .bytes (.bytes os) (binVal os)
    /-- r:e-dec-unit -/
    | r_e_dec_unit : Dec .unit .null .unit
    /-- r:e-dec-nothing -/
    | r_e_dec_nothing (τ : PTy) : Dec (.maybe τ) .null (.con conNothing [])
    /-- r:e-dec-just -/
    | r_e_dec_just (τ : PTy) (j : BVal) (v : Val) : j ≠ .null → Dec τ j v → Dec (.maybe τ) j (.con conJust [v])
    /-- r:e-dec-list -/
    | r_e_dec_list (τ : PTy) (js : BArr) (vs : List Val) :
        DecSeq τ js vs → Dec (.list τ) (.arr js) (Val.ofList vs)
    /-- r:e-dec-array -/
    | r_e_dec_array (τ : PTy) (j : BVal) (v v' : Val) :
        Dec (.list τ) j v → AppVal (bas .arrayFromList) v v' → Dec (.array τ) j v'
    /-- r:e-dec-tuple: further elements (`rest`) are ignored -/
    | r_e_dec_tuple (τ1 τ2 : PTy) (τ3 : Option PTy) (j1 j2 : BVal) (j3 : Option BVal) (rest : BArr)
        (v1 v2 : Val) (v3 : Option Val) :
        Dec τ1 j1 v1 → Dec τ2 j2 v2 → DecOpt τ3 j3 v3 → (τ3 = none → j3 = none) →
        Dec (tupleTy τ1 τ2 τ3) (.arr (.cons j1 (.cons j2 (BArr.prepend j3 rest)))) (.tuple v1 v2 v3)
    /-- r:e-dec-record: every label of the type is looked up; further keys are ignored -/
    | r_e_dec_record (fs : PFields) (kvs : BObj) (r : List (String × Val)) :
        DecFields fs kvs r → Dec (.record fs) (.obj kvs) (.record r)
    /-- r:e-dec-value -/
    | r_e_dec_value (j : BVal) : j.isJson = true → Dec .value j (.bv j)
  inductive DecSeq : PTy → BArr → List Val → Prop where
    | seq_nil (τ : PTy) : DecSeq τ .nil []
    | seq_cons (τ : PTy) (j : BVal) (js : BArr) (v : Val) (vs : List Val) :
        Dec τ j v → DecSeq τ js vs → DecSeq τ (.cons j js) (v :: vs)
  inductive DecOpt : Option PTy → Option BVal → Option Val → Prop where
    | opt_none : DecOpt none none none
    | opt_some (τ : PTy) (j : BVal) (v : Val) : Dec τ j v → DecOpt (some τ) (some j) (some v)
  inductive DecFields : PFields → BObj → List (String × Val) → Prop where
    | seq_nil (kvs : BObj) : DecFields .nil kvs []
    | seq_cons (l : String) (τ : PTy) (fs : PFields) (kvs : BObj) (j : BVal) (v : Val)
        (r : List (String × Val)) :
        kvs.lookup l = some j → Dec τ j v → DecFields fs kvs r → DecFields (.cons l τ fs) kvs ((l, v) :: r)
end

/-! ## The applications of the array rules -/

theorem appVal_arrayToList {v w : Val} : AppVal (bas .arrayToList) v w ↔ v = .con conArr [w] := by
  constructor
  · intro h
    cases h with
    | r_d_app_basic_partial _ _ _ h => simp [BasVal.arity] at h
    | r_d_app_basic_apply _ _ _ _ _ ha => cases ha; rfl
  · rintro rfl
    exact .r_d_app_basic_apply _ [] _ _ (by simp [BasVal.arity]) (.arrayToList_ _)

theorem appVal_arrayFromList {v w : Val} : AppVal (bas .arrayFromList) v w ↔ w = .con conArr [v] := by
  constructor
  · intro h
    cases h with
    | r_d_app_basic_partial _ _ _ h => simp [BasVal.arity] at h
    | r_d_app_basic_apply _ _ _ _ _ ha => cases ha; rfl
  · rintro rfl
    exact .r_d_app_basic_apply _ [] _ _ (by simp [BasVal.arity]) (.arrayFromList_ _)

/-! ## Lists and bytes -/

theorem toList?_ofList : ∀ vs : List Val, (Val.ofList vs).toList? = some vs
  | [] => by simp [Val.ofList, Val.toList?]
  | v :: vs => by simp [Val.ofList, Val.toList?, toList?_ofList vs]

theorem ofList_of_toList? : ∀ {v : Val} {vs : List Val}, v.toList? = some vs → v = Val.ofList vs
  | .con c [], vs, h => by
    simp only [Val.toList?] at h
    split at h
    · subst_vars; cases h; rfl
    · cases h
  | .con c [hd, tl], vs, h => by
    simp only [Val.toList?] at h
    split at h
    · subst_vars
      cases ht : tl.toList? with
      | none => simp [ht] at h
      | some ts =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        simp [Val.ofList, ofList_of_toList? ht]
    · cases h
  | .unit, _, h | .sv _, _, h | .basApp _ _, _, h | .record _, _, h | .tuple _ _ _, _, h
  | .closure _ _ _ _, _, h | .batch _, _, h | .mapE _ _, _, h | .prog _, _, h | .succeed _, _, h
  | .fail _, _, h | .andThen _ _, _, h | .onError _ _, _, h | .prim _ _, _, h | .pid _, _, h
  | .leaf _ _, _, h | .bv _, _, h => by simp [Val.toList?] at h
  | .con _ (_ :: _ :: _ :: _), _, h | .con _ [_], _, h => by simp [Val.toList?] at h

theorem byteOf?_int (o : Nat) (h : o < 256) : byteOf? (Val.int (o : Int)) = some o := by
  simp [byteOf?]; omega

theorem mapM_bytes : ∀ (os : List Nat), (∀ o ∈ os, o < 256) →
    (os.map fun (o : Nat) => Val.int (o : Int)).mapM byteOf? = some os
  | [], _ => rfl
  | o :: os, h => by
    simp only [List.map_cons, List.mapM_cons, byteOf?_int o (h o (by simp)),
      mapM_bytes os (fun o' hm => h o' (by simp [hm]))]
    rfl

theorem mapM_bytes_inv : ∀ {ls : List Val} {os : List Nat}, ls.mapM byteOf? = some os →
    ls = os.map (fun (o : Nat) => Val.int (o : Int)) ∧ ∀ o ∈ os, o < 256
  | [], os, h => by simp at h; subst h; simp
  | l :: ls, os, h => by
    simp only [List.mapM_cons] at h
    cases hb : byteOf? l with
    | none => simp [hb] at h
    | some o =>
      cases hr : ls.mapM byteOf? with
      | none => simp [hb, hr] at h
      | some os' =>
        simp only [hb, hr, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        obtain ⟨rfl, hall⟩ := mapM_bytes_inv hr
        unfold byteOf? at hb
        split at hb
        · rename_i n
          split at hb
          · rename_i hrange
            cases hb
            have hn : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg hrange.1
            refine ⟨?_, ?_⟩
            · simp only [List.map_cons, hn]
            · intro o' hm
              simp only [List.mem_cons] at hm
              rcases hm with rfl | hm
              · omega
              · exact hall o' hm
          · cases hb
        · cases hb

theorem mapM_bytes_comp : ∀ (os : List Nat), (∀ o ∈ os, o < 256) →
    os.mapM (byteOf? ∘ fun (o : Nat) => Val.int (o : Int)) = some os
  | [], _ => rfl
  | o :: os, h => by
    simp only [List.mapM_cons, Function.comp, byteOf?_int o (h o (by simp)),
      mapM_bytes_comp os (fun o' hm => h o' (by simp [hm]))]
    rfl

theorem enc_binVal (os : List Nat) (h : ∀ o ∈ os, o < 256) : enc .bytes (binVal os) = some (.bytes os) := by
  simp [binVal, enc, toList?_ofList, mapM_bytes_comp os h]

theorem BArr.ofList_toList : ∀ js : BArr, BArr.ofList js.toList = js
  | .nil => rfl
  | .cons j rest => by simp [BArr.toList, BArr.ofList, BArr.ofList_toList rest]

/-! ## The relations are the functions -/

mutual
  theorem Enc.toFn : ∀ {τ : PTy} {v : Val} {j : BVal}, Enc τ v j → enc τ v = some j
    | _, _, _, .r_e_enc_int _ => by simp [enc]
    | _, _, _, .r_e_enc_float _ _ h => by simp [enc, h]
    | _, _, _, .r_e_enc_float_null _ h => by simp [enc, h]
    | _, _, _, .r_e_enc_true => by simp [enc]
    | _, _, _, .r_e_enc_false => by simp [enc, conFalse, conTrue]
    | _, _, _, .r_e_enc_string _ => by simp [enc]
    | _, _, _, .r_e_enc_bytes os h => enc_binVal os h
    | _, _, _, .r_e_enc_unit => by simp [enc]
    | _, _, _, .r_e_enc_nothing _ => by simp [enc]
    | _, _, _, .r_e_enc_just _ _ _ h => by
      have ih := Enc.toFn h
      simp [enc, ih, conJust, conNothing]
    | _, _, _, .r_e_enc_list _ vs _ h => by
      have ih := EncSeq.toFn h
      simp only [enc]; rw [toList?_ofList]; simp [ih, BArr.ofList_toList]
    | _, _, _, .r_e_enc_array τ v v' j ha hl => by
      have ih := Enc.toFn hl
      rw [appVal_arrayToList] at ha; subst ha
      simp only [enc] at ih ⊢
      simpa using ih
    | _, _, _, .r_e_enc_tuple _ _ _ _ _ _ _ _ _ h1 h2 .opt_none => by
      have ih1 := Enc.toFn h1
      have ih2 := Enc.toFn h2
      simp [tupleTy, enc, ih1, ih2, BArr.prepend]
    | _, _, _, .r_e_enc_tuple _ _ _ _ _ _ _ _ _ h1 h2 (.opt_some _ _ _ h3) => by
      have ih1 := Enc.toFn h1
      have ih2 := Enc.toFn h2
      have ih3 := Enc.toFn h3
      simp [tupleTy, enc, ih1, ih2, ih3, BArr.prepend]
    | _, _, _, .r_e_enc_record _ _ _ hl hf => by
      have ih := EncFields.toFn hf
      simp [enc, hl, ih]
    | _, _, _, .r_e_enc_value _ h => by simp [enc, h]
  theorem EncSeq.toFn : ∀ {τ : PTy} {vs : List Val} {js : BArr}, EncSeq τ vs js →
      vs.mapM (enc τ) = some js.toList
    | _, _, _, .seq_nil _ => by simp [BArr.toList]
    | _, _, _, .seq_cons _ _ _ _ _ h hs => by
      have ih := Enc.toFn h
      have ihs := EncSeq.toFn hs
      simp [List.mapM_cons, ih, ihs, BArr.toList]
  theorem EncFields.toFn : ∀ {fs : PFields} {r : List (String × Val)} {kvs : BObj},
      EncFields fs r kvs → encFields fs r = some kvs
    | _, _, _, .seq_nil _ => by simp [encFields]
    | _, _, _, .seq_cons _ _ _ _ _ _ _ hl h hs => by
      have ih := Enc.toFn h
      have ihs := EncFields.toFn hs
      simp [encFields, hl, ih, ihs]
end

mutual
  theorem Dec.toFn : ∀ {τ : PTy} {j : BVal} {v : Val}, Dec τ j v → dec τ j = some v
    | _, _, _, .r_e_dec_int q h1 h2 h3 => by simp [dec, h1, h2, h3]
    | _, _, _, .r_e_dec_float q h => by simp [dec, h]
    | _, _, _, .r_e_dec_true => by simp [dec, Val.bool]
    | _, _, _, .r_e_dec_false => by simp [dec, Val.bool]
    | _, _, _, .r_e_dec_string _ => by simp [dec]
    | _, _, _, .r_e_dec_bytes os h => by
      have : os.all (· < 256) = true := List.all_eq_true.mpr (fun o hm => by simpa using h o hm)
      simp [dec, binVal, this]
    | _, _, _, .r_e_dec_unit => by simp [dec]
    | _, _, _, .r_e_dec_nothing _ => by simp [dec]
    | _, _, _, .r_e_dec_just τ j v hn h => by
      have ih := Dec.toFn h
      cases j with
      | null => exact absurd rfl hn
      | _ => simp [dec, ih]
    | _, _, _, .r_e_dec_list _ _ _ h => by
      have ih := DecSeq.toFn h
      simp [dec, ih]
    | _, _, _, .r_e_dec_array τ j v v' hl ha => by
      have ih := Dec.toFn hl
      rw [appVal_arrayFromList] at ha; subst ha
      cases j with
      | arr js =>
        simp only [dec] at ih ⊢
        cases hd : js.toList.mapM (dec τ) with
        | none => simp [hd] at ih
        | some vs => simp [hd] at ih ⊢; exact ih
      | _ => simp [dec] at ih
    | _, _, _, .r_e_dec_tuple _ _ _ _ _ _ _ _ _ _ h1 h2 .opt_none _ => by
      have ih1 := Dec.toFn h1
      have ih2 := Dec.toFn h2
      simp [tupleTy, dec, ih1, ih2, BArr.prepend]
    | _, _, _, .r_e_dec_tuple _ _ _ _ _ _ _ _ _ _ h1 h2 (.opt_some _ _ _ h3) _ => by
      have ih1 := Dec.toFn h1
      have ih2 := Dec.toFn h2
      have ih3 := Dec.toFn h3
      simp [tupleTy, dec, ih1, ih2, ih3, BArr.prepend]
    | _, _, _, .r_e_dec_record _ _ _ h => by
      have ih := DecFields.toFn h
      simp [dec, ih]
    | _, _, _, .r_e_dec_value _ h => by simp [dec, h]
  theorem DecSeq.toFn : ∀ {τ : PTy} {js : BArr} {vs : List Val}, DecSeq τ js vs →
      js.toList.mapM (dec τ) = some vs
    | _, _, _, .seq_nil _ => by simp [BArr.toList]
    | _, _, _, .seq_cons _ _ _ _ _ h hs => by
      have ih := Dec.toFn h
      have ihs := DecSeq.toFn hs
      simp [BArr.toList, List.mapM_cons, ih, ihs]
  theorem DecFields.toFn : ∀ {fs : PFields} {kvs : BObj} {r : List (String × Val)},
      DecFields fs kvs r → decFields fs kvs = some r
    | _, _, _, .seq_nil _ => by simp [decFields]
    | _, _, _, .seq_cons _ _ _ _ _ _ _ hl h hs => by
      have ih := Dec.toFn h
      have ihs := DecFields.toFn hs
      simp [decFields, hl, ih, ihs]
end

theorem encSeq_of_mapM {τ : PTy} (ih : ∀ v j, enc τ v = some j → Enc τ v j) :
    ∀ (vs : List Val) (js : List BVal), vs.mapM (enc τ) = some js → EncSeq τ vs (BArr.ofList js)
  | [], js, h => by simp at h; subst h; exact .seq_nil τ
  | v :: vs, js, h => by
    simp only [List.mapM_cons] at h
    cases hv : enc τ v with
    | none => simp [hv] at h
    | some j =>
      cases hvs : vs.mapM (enc τ) with
      | none => simp [hv, hvs] at h
      | some js' =>
        simp [hv, hvs] at h; subst h
        exact .seq_cons τ v vs j _ (ih v j hv) (encSeq_of_mapM ih vs js' hvs)

mutual
  theorem Enc.ofFn : ∀ (τ : PTy) (v : Val) (j : BVal), enc τ v = some j → Enc τ v j
    | .int, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i s; cases s <;> simp [enc] at h
      subst h; exact .r_e_enc_int _
    | .float, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i s; cases s <;> simp [enc] at h
      rename_i x
      cases hq : floatToRat? x with
      | none => simp [hq] at h; subst h; exact .r_e_enc_float_null x hq
      | some q => simp [hq] at h; subst h; exact .r_e_enc_float x q hq
    | .bool, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i c args
      cases args with
      | cons _ _ => simp [enc] at h
      | nil =>
        by_cases ht : c = conTrue
        · subst ht; simp [enc] at h; subst h; exact .r_e_enc_true
        · by_cases hf : c = conFalse
          · subst hf; simp [enc, conFalse, conTrue] at h; subst h; exact .r_e_enc_false
          · simp [enc, ht, hf] at h
    | .string, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i s; cases s <;> simp [enc] at h
      subst h; exact .r_e_enc_string _
    | .bytes, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i c args
      match args, h with
      | [l], h =>
        by_cases hc : c = conBin
        · subst hc
          simp only [enc, beq_self_eq_true, ite_true] at h
          cases hl : l.toList? with
          | none => simp [hl] at h
          | some ls =>
            cases hb : ls.mapM byteOf? with
            | none => simp [hl, hb] at h
            | some os =>
              simp [hl, hb] at h; subst h
              obtain ⟨rfl, hall⟩ := mapM_bytes_inv hb
              rw [ofList_of_toList? hl]
              exact .r_e_enc_bytes os hall
        · simp [enc, hc] at h
      | [], h => simp [enc] at h
      | _ :: _ :: _, h => simp [enc] at h
    | .unit, v, j, h => by
      cases v <;> simp [enc] at h
      subst h; exact .r_e_enc_unit
    | .maybe τ, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i c args
      by_cases hn : c = conNothing ∧ args = []
      · obtain ⟨rfl, rfl⟩ := hn; simp [enc] at h; subst h; exact .r_e_enc_nothing τ
      · by_cases hj : c = conJust
        · subst hj
          match args, h with
          | [w], h =>
            simp [enc, conJust, conNothing] at h
            exact .r_e_enc_just τ w j (Enc.ofFn τ w j h)
          | [], h => simp [enc, conJust, conNothing] at h
          | _ :: _ :: _, h => simp [enc, conJust, conNothing] at h
        · simp only [enc] at h
          split at h
          · rename_i hc; simp only [beq_iff_eq] at hc; exact absurd hc hn
          · split at h
            · rename_i hc; simp only [beq_iff_eq] at hc; exact absurd hc hj
            · cases h
    | .list τ, v, j, h => by
      simp only [enc] at h
      cases hv : v.toList? with
      | none => simp [hv] at h
      | some vs =>
        cases hm : vs.mapM (enc τ) with
        | none => simp [hv, hm] at h
        | some js =>
          simp [hv, hm] at h; subst h
          rw [ofList_of_toList? hv]
          exact .r_e_enc_list τ vs _ (encSeq_of_mapM (Enc.ofFn τ) vs js hm)
    | .array τ, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i c args
      match args, h with
      | [l], h =>
        by_cases hc : c = conArr
        · subst hc
          simp only [enc, beq_self_eq_true, ite_true] at h
          cases hv : l.toList? with
          | none => simp [hv] at h
          | some vs =>
            cases hm : vs.mapM (enc τ) with
            | none => simp [hv, hm] at h
            | some js =>
              simp [hv, hm] at h; subst h
              refine .r_e_enc_array τ _ l _ (appVal_arrayToList.mpr rfl) ?_
              rw [ofList_of_toList? hv]
              exact .r_e_enc_list τ vs _ (encSeq_of_mapM (Enc.ofFn τ) vs js hm)
        · simp [enc, hc] at h
      | [], h => simp [enc] at h
      | _ :: _ :: _, h => simp [enc] at h
    | .tuple2 τ1 τ2, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i v1 v2 v3
      cases v3 with
      | some _ => simp [enc] at h
      | none =>
        cases e1 : enc τ1 v1 with
        | none => simp [enc, e1] at h
        | some j1 =>
          cases e2 : enc τ2 v2 with
          | none => simp [enc, e1, e2] at h
          | some j2 =>
            simp [enc, e1, e2] at h; subst h
            exact .r_e_enc_tuple τ1 τ2 none v1 v2 none j1 j2 none (Enc.ofFn τ1 v1 j1 e1)
              (Enc.ofFn τ2 v2 j2 e2) .opt_none
    | .tuple3 τ1 τ2 τ3, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i v1 v2 v3
      cases v3 with
      | none => simp [enc] at h
      | some v3 =>
        cases e1 : enc τ1 v1 with
        | none => simp [enc, e1] at h
        | some j1 =>
          cases e2 : enc τ2 v2 with
          | none => simp [enc, e1, e2] at h
          | some j2 =>
            cases e3 : enc τ3 v3 with
            | none => simp [enc, e1, e2, e3] at h
            | some j3 =>
              simp [enc, e1, e2, e3] at h; subst h
              exact .r_e_enc_tuple τ1 τ2 (some τ3) v1 v2 (some v3) j1 j2 (some j3)
                (Enc.ofFn τ1 v1 j1 e1) (Enc.ofFn τ2 v2 j2 e2) (.opt_some τ3 v3 j3 (Enc.ofFn τ3 v3 j3 e3))
    | .record fs, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i r
      by_cases hl : labelsMatch r fs = true
      · simp only [enc, hl, ite_true] at h
        cases he : encFields fs r with
        | none => simp [he] at h
        | some kvs => simp [he] at h; subst h; exact .r_e_enc_record fs r kvs hl (EncFields.ofFn fs r kvs he)
      · simp [enc, hl] at h
    | .value, v, j, h => by
      cases v <;> try (simp [enc] at h; done)
      rename_i j'
      simp [enc] at h
      obtain ⟨hj, rfl⟩ := h
      exact .r_e_enc_value j' hj
  theorem EncFields.ofFn : ∀ (fs : PFields) (r : List (String × Val)) (kvs : BObj),
      encFields fs r = some kvs → EncFields fs r kvs
    | .nil, r, kvs, h => by simp [encFields] at h; subst h; exact .seq_nil r
    | .cons l τ rest, r, kvs, h => by
      simp only [encFields] at h
      cases hf : fieldOf r l with
      | none => simp [hf] at h
      | some v =>
        cases e : enc τ v with
        | none => simp [hf, e] at h
        | some j =>
          cases er : encFields rest r with
          | none => simp [hf, e, er] at h
          | some kvs1 =>
            simp [hf, e, er] at h; subst h
            exact .seq_cons l τ rest r v j kvs1 hf (Enc.ofFn τ v j e) (EncFields.ofFn rest r kvs1 er)
end

theorem decSeq_of_mapM {τ : PTy} (ih : ∀ j v, dec τ j = some v → Dec τ j v) :
    ∀ (js : BArr) (vs : List Val), js.toList.mapM (dec τ) = some vs → DecSeq τ js vs
  | .nil, vs, h => by simp [BArr.toList] at h; subst h; exact .seq_nil τ
  | .cons j js, vs, h => by
    simp only [BArr.toList, List.mapM_cons] at h
    cases hj : dec τ j with
    | none => simp [hj] at h
    | some v =>
      cases hjs : js.toList.mapM (dec τ) with
      | none => simp [hj, hjs] at h
      | some vs' =>
        simp [hj, hjs] at h; subst h
        exact .seq_cons τ j js v vs' (ih j v hj) (decSeq_of_mapM ih js vs' hjs)

mutual
  theorem Dec.ofFn : ∀ (τ : PTy) (j : BVal) (v : Val), dec τ j = some v → Dec τ j v
    | .int, j, v, h => by
      cases j <;> try (simp [dec] at h; done)
      rename_i q
      by_cases hq : q.den = 1 ∧ intMin ≤ q.num ∧ q.num ≤ intMax
      · obtain ⟨h1, h2, h3⟩ := hq
        simp [dec, h1, h2, h3] at h; subst h; exact .r_e_dec_int q h1 h2 h3
      · unfold dec at h; simp [hq] at h
    | .float, j, v, h => by
      cases j <;> try (simp [dec] at h; done)
      rename_i q
      by_cases hq : isDecimal q = true
      · simp [dec, hq] at h; subst h; exact .r_e_dec_float q hq
      · simp [dec, hq] at h
    | .bool, j, v, h => by
      cases j <;> simp [dec, Val.bool] at h
      · subst h; exact .r_e_dec_true
      · subst h; exact .r_e_dec_false
    | .string, j, v, h => by
      cases j <;> simp [dec] at h
      subst h; exact .r_e_dec_string _
    | .bytes, j, v, h => by
      cases j <;> try (simp [dec] at h; done)
      rename_i os
      by_cases ho : (os.all fun x => decide (x < 256)) = true
      · simp [dec, ho] at h; subst h
        exact .r_e_dec_bytes os (fun o hm => by simpa using List.all_eq_true.mp ho o hm)
      · unfold dec at h; simp [ho] at h
    | .unit, j, v, h => by
      cases j <;> simp [dec] at h
      subst h; exact .r_e_dec_unit
    | .maybe τ, j, v, h => by
      by_cases hn : j = .null
      · subst hn; simp [dec] at h; subst h; exact .r_e_dec_nothing τ
      · have h' : (dec τ j).map (fun w => Val.con conJust [w]) = some v := by
          cases j with
          | null => exact absurd rfl hn
          | _ => simpa only [dec] using h
        cases hd : dec τ j with
        | none => simp [hd] at h'
        | some w => simp [hd] at h'; subst h'; exact .r_e_dec_just τ j w hn (Dec.ofFn τ j w hd)
    | .list τ, j, v, h => by
      cases j <;> try (simp [dec] at h; done)
      rename_i js
      simp only [dec] at h
      cases hm : js.toList.mapM (dec τ) with
      | none => simp [hm] at h
      | some vs => simp [hm] at h; subst h; exact .r_e_dec_list τ js vs (decSeq_of_mapM (Dec.ofFn τ) js vs hm)
    | .array τ, j, v, h => by
      cases j <;> try (simp [dec] at h; done)
      rename_i js
      simp only [dec] at h
      cases hm : js.toList.mapM (dec τ) with
      | none => simp [hm] at h
      | some vs =>
        simp [hm] at h; subst h
        exact .r_e_dec_array τ (.arr js) (Val.ofList vs) _
          (.r_e_dec_list τ js vs (decSeq_of_mapM (Dec.ofFn τ) js vs hm)) (appVal_arrayFromList.mpr rfl)
    | .tuple2 τ1 τ2, j, v, h => by
      match j, h with
      | .arr (.cons j1 (.cons j2 rest)), h =>
        cases e1 : dec τ1 j1 with
        | none => simp [dec, e1] at h
        | some v1 =>
          cases e2 : dec τ2 j2 with
          | none => simp [dec, e1, e2] at h
          | some v2 =>
            simp [dec, e1, e2] at h; subst h
            exact .r_e_dec_tuple τ1 τ2 none j1 j2 none rest v1 v2 none (Dec.ofFn τ1 j1 v1 e1)
              (Dec.ofFn τ2 j2 v2 e2) .opt_none (fun _ => rfl)
      | .arr (.cons _ .nil), h | .arr .nil, h => simp [dec] at h
      | .null, h | .tru, h | .fls, h | .num _, h | .str _, h | .bytes _, h | .obj _, h => simp [dec] at h
    | .tuple3 τ1 τ2 τ3, j, v, h => by
      match j, h with
      | .arr (.cons j1 (.cons j2 (.cons j3 rest))), h =>
        cases e1 : dec τ1 j1 with
        | none => simp [dec, e1] at h
        | some v1 =>
          cases e2 : dec τ2 j2 with
          | none => simp [dec, e1, e2] at h
          | some v2 =>
            cases e3 : dec τ3 j3 with
            | none => simp [dec, e1, e2, e3] at h
            | some v3 =>
              simp [dec, e1, e2, e3] at h; subst h
              exact .r_e_dec_tuple τ1 τ2 (some τ3) j1 j2 (some j3) rest v1 v2 (some v3)
                (Dec.ofFn τ1 j1 v1 e1) (Dec.ofFn τ2 j2 v2 e2) (.opt_some τ3 j3 v3 (Dec.ofFn τ3 j3 v3 e3))
                (fun h => by cases h)
      | .arr (.cons _ (.cons _ .nil)), h | .arr (.cons _ .nil), h | .arr .nil, h => simp [dec] at h
      | .null, h | .tru, h | .fls, h | .num _, h | .str _, h | .bytes _, h | .obj _, h => simp [dec] at h
    | .record fs, j, v, h => by
      cases j <;> try (simp [dec] at h; done)
      rename_i kvs
      simp only [dec] at h
      cases hd : decFields fs kvs with
      | none => simp [hd] at h
      | some r => simp [hd] at h; subst h; exact .r_e_dec_record fs kvs r (DecFields.ofFn fs kvs r hd)
    | .value, j, v, h => by
      by_cases hj : j.isJson = true
      · simp [dec, hj] at h; subst h; exact .r_e_dec_value j hj
      · simp [dec, hj] at h
  theorem DecFields.ofFn : ∀ (fs : PFields) (kvs : BObj) (r : List (String × Val)),
      decFields fs kvs = some r → DecFields fs kvs r
    | .nil, kvs, r, h => by simp [decFields] at h; subst h; exact .seq_nil kvs
    | .cons l τ rest, kvs, r, h => by
      simp only [decFields] at h
      cases hl : kvs.lookup l with
      | none => simp [hl] at h
      | some j =>
        cases e : dec τ j with
        | none => simp [hl, e] at h
        | some v =>
          cases er : decFields rest kvs with
          | none => simp [hl, e, er] at h
          | some r1 =>
            simp [hl, e, er] at h; subst h
            exact .seq_cons l τ rest kvs j v r1 hl (Dec.ofFn τ j v e) (DecFields.ofFn rest kvs r1 er)
end

/-- The relation Enc is the function enc (D8). -/
theorem enc_iff (τ : PTy) (v : Val) (j : BVal) : Enc τ v j ↔ enc τ v = some j :=
  ⟨Enc.toFn, Enc.ofFn τ v j⟩

/-- The relation Dec is the function dec (D8). -/
theorem dec_iff (τ : PTy) (j : BVal) (v : Val) : Dec τ j v ↔ dec τ j = some v :=
  ⟨Dec.toFn, Dec.ofFn τ j v⟩

/-- Enc_τ is a partial function (sec:effects-ports, the property's first sentence). -/
theorem Enc.functional {τ : PTy} {v : Val} {j j' : BVal} (h : Enc τ v j) (h' : Enc τ v j') :
    j = j' := by
  rw [enc_iff] at h h'; rw [h] at h'; exact Option.some.inj h'

/-- Dec_τ is a partial function. -/
theorem Dec.functional {τ : PTy} {j : BVal} {v v' : Val} (h : Dec τ j v) (h' : Dec τ j v') :
    v = v' := by
  rw [dec_iff] at h h'; rw [h] at h'; exact Option.some.inj h'

end StandardElm.Eff
