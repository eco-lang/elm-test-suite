/-
  A Standard Definition of Elm? Mechanisation: boundary values (effects.tex, Figure
  fig:effects-compound), plan step 4.

  BVal: null, true, false, JSON numbers, strings, byte sequences (A92), arrays and objects. JSON
  numbers are exact rationals (plan decision D6); objects are canonical, their keys strictly
  increasing (decision D7), and `BVal.mkObj` is the only way one is built outside `enc`. Arrays and
  objects hold their elements in the list types `BArr` and `BObj` of a mutual block, because Lean
  4.35 derives no `DecidableEq` for a type nested in `List` (as `PTy` and `PFields`).

  JVal, the JSON values, are the boundary values in which no byte sequence occurs (`isJson`).
-/
namespace StandardElm.Eff

mutual
  inductive BVal where
    | null | tru | fls
    /-- a JSON number, exact (D6) -/
    | num (q : Rat)
    | str (s : String)
    /-- a byte sequence (A92); each byte below 256 (`Canon`) -/
    | bytes (os : List Nat)
    | arr (js : BArr)
    /-- an object; keys strictly increasing (`Canon`) -/
    | obj (kvs : BObj)
  inductive BArr where
    | nil
    | cons (j : BVal) (rest : BArr)
  inductive BObj where
    | nil
    | cons (k : String) (j : BVal) (rest : BObj)
end

deriving instance Repr, DecidableEq for BVal, BArr, BObj
instance : Inhabited BVal := ⟨.null⟩

def BArr.ofList : List BVal → BArr
  | [] => .nil
  | j :: js => .cons j (BArr.ofList js)

def BArr.toList : BArr → List BVal
  | .nil => []
  | .cons j rest => j :: rest.toList

def BObj.ofList : List (String × BVal) → BObj
  | [] => .nil
  | (k, j) :: kvs => .cons k j (BObj.ofList kvs)

def BObj.toList : BObj → List (String × BVal)
  | .nil => []
  | .cons k j rest => (k, j) :: rest.toList

theorem BArr.toList_ofList : ∀ js : List BVal, (BArr.ofList js).toList = js
  | [] => rfl
  | j :: js => by simp [BArr.ofList, BArr.toList, BArr.toList_ofList js]

theorem BObj.toList_ofList : ∀ kvs : List (String × BVal), (BObj.ofList kvs).toList = kvs
  | [] => rfl
  | (k, j) :: kvs => by simp [BObj.ofList, BObj.toList, BObj.toList_ofList kvs]

/-- An array of the listed elements. -/
def BVal.array (js : List BVal) : BVal := .arr (BArr.ofList js)

/-- An object with the listed keys and values, in that order (`mkObj` sorts). -/
def BVal.object (kvs : List (String × BVal)) : BVal := .obj (BObj.ofList kvs)

/-! ## JSON numbers -/

/-- m × 10^e: the JSON number a numeral spells (effects.tex, sec:effects-simple). -/
def jnum (m e : Int) : Rat :=
  if 0 ≤ e then ((m * 10 ^ e.toNat : Int) : Rat) else mkRat m (10 ^ e.natAbs)

/-- n with every factor p removed, with fuel n (each division at least halves n). -/
def stripFactor (p : Nat) : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if p ≥ 2 ∧ n ≠ 0 ∧ n % p = 0 then stripFactor p fuel (n / p) else n

/-- q is a JSON number: its denominator has no prime factor other than 2 and 5. -/
def isDecimal (q : Rat) : Bool :=
  stripFactor 5 q.den (stripFactor 2 q.den q.den) == 1

/-- The number of times p divides n, with fuel n. -/
def countFactor (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if p ≥ 2 ∧ n ≠ 0 ∧ n % p = 0 then countFactor p fuel (n / p) + 1 else 0

/-! ## Canonical values and JSON values -/

mutual
  /-- Canonical boundary values, as a decider: numbers decimal, bytes below 256, object keys
      strictly increasing, recursively. -/
  def BVal.canonB : BVal → Bool
    | .num q => isDecimal q
    | .bytes os => os.all (· < 256)
    | .arr js => js.canonB
    | .obj kvs => kvs.canonB && kvs.keysIncreasing
    | _ => true
  def BArr.canonB : BArr → Bool
    | .nil => true
    | .cons j rest => j.canonB && rest.canonB
  def BObj.canonB : BObj → Bool
    | .nil => true
    | .cons _ j rest => j.canonB && rest.canonB
  /-- The keys strictly increasing (String `<`). -/
  def BObj.keysIncreasing : BObj → Bool
    | .nil => true
    | .cons _ _ .nil => true
    | .cons k _ (.cons k' j' rest) => decide (k < k') && (BObj.cons k' j' rest).keysIncreasing
end

/-- Canonical boundary values (D7). -/
def BVal.Canon (j : BVal) : Prop := j.canonB = true

mutual
  /-- JVal: the boundary values in which no byte sequence occurs. -/
  def BVal.isJson : BVal → Bool
    | .bytes _ => false
    | .arr js => js.isJson
    | .obj kvs => kvs.isJson
    | _ => true
  def BArr.isJson : BArr → Bool
    | .nil => true
    | .cons j rest => j.isJson && rest.isJson
  def BObj.isJson : BObj → Bool
    | .nil => true
    | .cons _ j rest => j.isJson && rest.isJson
end

/-- Of the bindings of one key, the last (as a JSON parser reads an object with a repeated key). -/
def dedupLastByKey (kvs : List (String × BVal)) : List (String × BVal) :=
  kvs.foldl (fun acc (k, j) => acc.filter (·.1 != k) ++ [(k, j)]) []

/-- Insert a binding into a list sorted by key (structural, so the kernel reduces it; `mergeSort`
    is defined by well-founded recursion, which it does not). -/
def insertByKey (b : String × BVal) : List (String × BVal) → List (String × BVal)
  | [] => [b]
  | c :: rest => if decide (b.1 ≤ c.1) then b :: c :: rest else c :: insertByKey b rest

/-- The normalising constructor of objects: sort by key, of duplicate keys the last wins. -/
def BVal.mkObj (kvs : List (String × BVal)) : BVal :=
  .object ((dedupLastByKey kvs).foldr insertByKey [])

/-! ## Floats and JSON numbers -/

/-- m × 2^e, exactly. -/
def dyadic (m : Nat) (e : Int) : Rat :=
  if 0 ≤ e then ((m * 2 ^ e.toNat : Nat) : Rat) else mkRat m (2 ^ e.natAbs)

/-- The exact value of a finite float, from its bits; `none` for NaN and the infinities. Both
    zeros give 0: a JSON number has no sign apart from its value (sec:effects-simple, A88). -/
def floatToRat? (x : Float) : Option Rat :=
  let b := x.toBits
  let ex := ((b >>> 52) &&& 0x7FF).toNat
  let fr := (b &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0x7FF then none else
  let (m, e) : Nat × Int := if ex == 0 then (fr, -1074) else (fr + 2 ^ 52, (ex : Int) - 1075)
  some (if b >>> 63 == 1 then -dyadic m e else dyadic m e)

/-- float(j): the float nearest a decimal rational, rounded as the value of a floating-point
    constant is (Rules.lean `valof`: `Float.ofScientific`). For q = num/den with
    den = 2^a 5^b, k = max a b and M = |num| * (10^k / den): Float.ofScientific M true k,
    negated when num < 0. float(0) is +0. -/
def ratToFloat (q : Rat) : Float :=
  let a := countFactor 2 q.den q.den
  let b := countFactor 5 q.den q.den
  let k := max a b
  let m := q.num.natAbs * (10 ^ k / q.den)
  let x := Float.ofScientific m true k
  if q.num < 0 then -x else x

/-- x is the negative zero. -/
def isNegZero (x : Float) : Bool := x.toBits == 0x8000000000000000

end StandardElm.Eff
