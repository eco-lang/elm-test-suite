/-
  A Standard Definition of Elm? Mechanisation: Enc_τ and Dec_τ as structural functions (plan
  decision D8), plan step 4. The book's relations (effects.tex, sec:effects-ports, rules
  r:e-enc-* and r:e-dec-*) are in EncDec.lean, proved equal to these (`enc_iff`, `dec_iff`).

  Structural recursion on the payload type, mutual with the record fields (`PFields`). The two
  applications of the array rules are unfolded: APPLY(Array.toList, arr# v) = {v} and
  APPLY(Array.fromList, v) = {arr# v} evaluate no closure.
-/
import StandardElmMech.Objects

namespace StandardElm.Eff
open StandardElm

/-- A byte: an Int value from 0 to 255. -/
def byteOf? : Val → Option Nat
  | .sv (.int n) => if 0 ≤ n ∧ n ≤ 255 then some n.toNat else none
  | _ => none

/-- The value of a field of a record value. -/
def fieldOf (r : List (String × Val)) (l : String) : Option Val := fmLookup r l

/-- The labels of a record type's fields. -/
def PFields.labels : PFields → List String
  | .nil => []
  | .cons l _ rest => l :: rest.labels

/-- Dom r = Dom ρ: the record's labels are exactly the type's. -/
def labelsMatch (r : List (String × Val)) (fs : PFields) : Bool :=
  (r.map (·.1)).all (fs.labels.contains ·) && fs.labels.all (fun l => (r.map (·.1)).contains l)

mutual
  /-- Enc_τ(v) = j (sec:effects-ports, the encoding rules), as a partial function. Structural on the
      payload type: the elements of a list are encoded by `mapM` of `enc τ`. -/
  def enc : PTy → Val → Option BVal
    | .int, .sv (.int n) => some (.num n)
    | .float, .sv (.float x) => some ((floatToRat? x).elim .null .num)
    | .bool, .con c [] => if c == conTrue then some .tru else if c == conFalse then some .fls else none
    | .string, .sv (.str s) => some (.str s)
    | .bytes, .con c [l] =>
      if c == conBin then (l.toList? >>= (·.mapM byteOf?)).map .bytes else none
    | .unit, .unit => some .null
    | .maybe τ, .con c args =>
      if c == conNothing ∧ args = [] then some .null
      else if c == conJust then (match args with | [v] => enc τ v | _ => none) else none
    | .list τ, v =>
      match v.toList? with
      | some vs => (vs.mapM (enc τ)).map fun js => .arr (BArr.ofList js)
      | none => none
    | .array τ, .con c [l] =>
      if c == conArr then
        match l.toList? with
        | some vs => (vs.mapM (enc τ)).map fun js => .arr (BArr.ofList js)
        | none => none
      else none
    | .tuple2 τ1 τ2, .tuple v1 v2 none =>
      match enc τ1 v1, enc τ2 v2 with
      | some j1, some j2 => some (.arr (.cons j1 (.cons j2 .nil)))
      | _, _ => none
    | .tuple3 τ1 τ2 τ3, .tuple v1 v2 (some v3) =>
      match enc τ1 v1, enc τ2 v2, enc τ3 v3 with
      | some j1, some j2, some j3 => some (.arr (.cons j1 (.cons j2 (.cons j3 .nil))))
      | _, _, _ => none
    | .record fs, .record r =>
      if labelsMatch r fs then (encFields fs r).map .obj else none
    | .value, .bv j => if j.isJson then some j else none
    | _, _ => none
  /-- The fields of a record value, in the type's order. -/
  def encFields : PFields → List (String × Val) → Option BObj
    | .nil, _ => some .nil
    | .cons l τ rest, r =>
      match fieldOf r l with
      | some v =>
        match enc τ v, encFields rest r with
        | some j, some kvs => some (.cons l j kvs)
        | _, _ => none
      | none => none
end

/-- The elements of a list value, each at τ. -/
def encList (τ : PTy) (vs : List Val) : Option BArr := (vs.mapM (enc τ)).map BArr.ofList

/-- The value of an object at a key. -/
def BObj.lookup : BObj → String → Option BVal
  | .nil, _ => none
  | .cons k j rest, l => if k == l then some j else rest.lookup l

mutual
  /-- Dec_τ(j) = v (sec:effects-ports, the decoding rules), as a partial function. Structural on
      the payload type: the elements of an array are decoded by `mapM` of `dec τ`. -/
  def dec : PTy → BVal → Option Val
    | .int, .num q =>
      if q.den = 1 ∧ intMin ≤ q.num ∧ q.num ≤ intMax then some (.int q.num) else none
    | .float, .num q => if isDecimal q then some (.sv (.float (ratToFloat q))) else none
    | .bool, .tru => some (.bool true)
    | .bool, .fls => some (.bool false)
    | .string, .str s => some (.sv (.str s))
    | .bytes, .bytes os =>
      if os.all (· < 256) then some (.con conBin [Val.ofList (os.map (fun (o : Nat) => Val.int (o : Int)))]) else none
    | .unit, .null => some .unit
    | .maybe _, .null => some (.con conNothing [])
    | .maybe τ, j => (dec τ j).map fun v => .con conJust [v]
    | .list τ, .arr js => (js.toList.mapM (dec τ)).map Val.ofList
    | .array τ, .arr js => (js.toList.mapM (dec τ)).map fun vs => .con conArr [Val.ofList vs]
    | .tuple2 τ1 τ2, .arr (.cons j1 (.cons j2 _)) =>
      match dec τ1 j1, dec τ2 j2 with
      | some v1, some v2 => some (.tuple v1 v2 none)
      | _, _ => none
    | .tuple3 τ1 τ2 τ3, .arr (.cons j1 (.cons j2 (.cons j3 _))) =>
      match dec τ1 j1, dec τ2 j2, dec τ3 j3 with
      | some v1, some v2, some v3 => some (.tuple v1 v2 (some v3))
      | _, _, _ => none
    | .record fs, .obj kvs => (decFields fs kvs).map .record
    | .value, j => if j.isJson then some (.bv j) else none
    | _, _ => none
  /-- The fields of the type, each looked up in the object (further keys are ignored). -/
  def decFields : PFields → BObj → Option (List (String × Val))
    | .nil, _ => some []
    | .cons l τ rest, kvs =>
      match kvs.lookup l with
      | some j =>
        match dec τ j, decFields rest kvs with
        | some v, some r => some ((l, v) :: r)
        | _, _ => none
      | none => none
end

/-- The elements of an array, each at τ. -/
def decList (τ : PTy) (js : BArr) : Option (List Val) := js.toList.mapM (dec τ)

end StandardElm.Eff
