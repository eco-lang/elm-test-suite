/-
  A Standard Definition of Elm? Mechanisation, part 9.
  Printing values in the form the eco test suite's `-- CHECK:` lines use
  (the output of Debug.log), so that results compare as strings. This is a
  test harness, not part of the definition: Debug.toString lies outside it.
-/
import StandardElmMech.Objects

namespace StandardElm

/-- A string as Elm/JS's Debug.toString prints it (`_Debug_addSlashes`): a quote, backslash,
    newline, tab, carriage return, vertical tab and NUL escaped. -/
def showStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun ch =>
    if ch == '"' then "\\\"" else if ch == '\\' then "\\\\" else if ch == '\n' then "\\n"
    else if ch == '\t' then "\\t" else if ch == '\r' then "\\r" else if ch == '\x0b' then "\\v"
    else if ch == '\x00' then "\\0" else ch.toString) ++ "\""

/-! ## Floats as Elm prints them

Elm prints a float as JavaScript's `Number.prototype.toString` does: the
shortest decimal that reads back as the same float (the nearest of that
length), in positional notation for decimal exponents from -6 to 21 and in
exponent notation otherwise. Computed exactly, with integers: a finite float is
m * 2^e, and a decimal reads back as it when it lies in the float's rounding
interval (its ends included when m is even, ties going to even). -/

/-- A positive finite float as (m, e), its value m * 2^e, and whether its
    rounding interval is narrower below (a power of two above the least
    normal exponent). -/
def floatParts (x : Float) : Nat × Int × Bool :=
  let b := x.toBits
  let ex := ((b >>> 52) &&& 0x7FF).toNat
  let fr := (b &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0 then (fr, -1074, false) else (fr + 2 ^ 52, (ex : Int) - 1075, fr == 0 && ex > 1)

/-- a * 10^ka compared with b * 2^eb. -/
def cmpDecBin (a : Nat) (ka : Int) (b : Nat) (eb : Int) : Ordering :=
  compare (a * 10 ^ ka.toNat * 2 ^ (-eb).toNat) (b * 2 ^ eb.toNat * 10 ^ (-ka).toNat)

/-- Whether d * 10^k reads back as the positive float m * 2^e. -/
def readsBack (m : Nat) (e : Int) (narrow : Bool) (d : Nat) (k : Int) : Bool :=
  -- the interval's ends, in units of 2^(e-2)
  let lo := if narrow then 4 * m - 1 else 4 * m - 2
  let hi := 4 * m + 2
  let incl := m % 2 == 0
  let above := match cmpDecBin d k lo (e - 2) with
    | .gt => true | .eq => incl | .lt => false
  let below := match cmpDecBin d k hi (e - 2) with
    | .lt => true | .eq => incl | .gt => false
  above && below

def decDigits (n : Nat) : Nat := (toString n).length

/-- The shortest decimal d * 10^k that reads back as the positive float
    m * 2^e, the nearest of that length. -/
def shortestDecimal (m : Nat) (e : Int) (narrow : Bool) : Nat × Int :=
  -- the exact value as D * 10^q
  let (D, q) : Nat × Int := if e ≥ 0 then (m * 2 ^ e.toNat, 0) else (m * 5 ^ (-e).toNat, e)
  let L := decDigits D
  let rec go (p : Nat) (fuel : Nat) : Nat × Int :=
    match fuel with
    | 0 => (D, q)
    | fuel + 1 =>
      if p ≥ L then (D, q) else
      let drop := L - p
      let s := 10 ^ drop
      let lo := D / s
      let r := D % s
      let k := q + drop
      let (first, second) := if 2 * r ≥ s then (lo + 1, lo) else (lo, lo + 1)
      if readsBack m e narrow first k then (first, k)
      else if r != 0 && readsBack m e narrow second k then (second, k)
      else go (p + 1) fuel
  go 1 20

/-- The digits of d * 10^k with trailing zeros moved into the exponent. -/
def stripZeros (d : Nat) (k : Int) (fuel : Nat := 400) : Nat × Int :=
  match fuel with
  | 0 => (d, k)
  | fuel + 1 => if d != 0 && d % 10 == 0 then stripZeros (d / 10) (k + 1) fuel else (d, k)

/-- JavaScript's Number::toString for a positive finite float. -/
def showPositive (x : Float) : String :=
  let (m, e, narrow) := floatParts x
  let (d, k) := shortestDecimal m e narrow
  let (d, k) := stripZeros d k
  let s := toString d
  let len := s.length
  -- the value is 0.s * 10^n
  let n : Int := len + k
  let zeros (j : Int) := String.ofList (List.replicate j.toNat '0')
  if len ≤ n && n ≤ 21 then s ++ zeros (n - len)
  else if 0 < n && n ≤ 21 then
    String.ofList (s.toList.take n.toNat) ++ "." ++ String.ofList (s.toList.drop n.toNat)
  else if -6 < n && n ≤ 0 then "0." ++ zeros (-n) ++ s
  else
    let x := n - 1
    let mant := if len == 1 then s else
      String.ofList (s.toList.take 1) ++ "." ++ String.ofList (s.toList.drop 1)
    mant ++ "e" ++ (if x > 0 then "+" else "-") ++ toString x.natAbs

/-- Floats print as Elm's `Debug.log` prints them: `NaN`, `Infinity`,
    `-Infinity`, `0` for either zero, or the shortest decimal that reads back
    as the float, as JavaScript prints it. -/
def showFloat (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0 then "0"
  else if x.isInf then (if x > 0 then "Infinity" else "-Infinity")
  else if x < 0 then "-" ++ showPositive (-x)
  else showPositive x

mutual
  /-- A boundary value as JSON text: keys in canonical order, an integral number as the integer,
      any other by `showFloat` of its nearest float, a byte sequence as `<k bytes>` (A62: the
      printing of an effect value is implementation-dependent; this is Elm/JS's). -/
  def showBV : Eff.BVal → String
    | .null => "null"
    | .tru => "true"
    | .fls => "false"
    | .num q => if q.den == 1 then toString q.num else showFloat (Eff.ratToFloat q)
    | .str s => showStr s
    | .bytes os => "<" ++ toString os.length ++ " bytes>"
    | .arr js => "[" ++ ",".intercalate (showBArr js) ++ "]"
    | .obj kvs => "{" ++ ",".intercalate (showBObj kvs) ++ "}"
  def showBArr : Eff.BArr → List String
    | .nil => []
    | .cons j rest => showBV j :: showBArr rest
  def showBObj : Eff.BObj → List String
    | .nil => []
    | .cons k j rest => (showStr k ++ ":" ++ showBV j) :: showBObj rest
end

def isAtomicShow : Val → Bool
  | .con c args => args.isEmpty || c == conCons || c == conNil
  | _ => true

mutual
  def showVal : Val → String
    | .unit => "()"
    | .sv (.int n) => toString n
    | .sv (.float x) => showFloat x
    | .sv (.char ch) => "'" ++ ch.toString ++ "'"
    | .sv (.str s) => showStr s
    | .basApp .. => "<function>"
    | .closure .. => "<function>"
    | .con c args =>
      if args.length < c.arity then "<function>"
      else if c == conBin then
        match args with
        | [l] => match listElems l with
          | some es => "<" ++ toString es.length ++ " bytes>"
          | none => "<ill-formed bytes>"
        | _ => "<ill-formed bytes>"
      else if c == conArr then
        match args with
        | [l] => match listElems l with
          | some es => "Array.fromList [" ++ ",".intercalate es ++ "]"
          | none => "<ill-formed array>"
        | _ => "<ill-formed array>"
      else if c == conNil || c == conCons then
        match listElems (.con c args) with
        | some es => "[" ++ ",".intercalate es ++ "]"
        | none => "<ill-formed list>"
      else if args.isEmpty then c.name
      else c.name ++ String.join (showArgs args)
    | .record r =>
      if r.isEmpty then "{}"
      else "{ " ++ ", ".intercalate (showFields r) ++ " }"
    | .tuple a b none => "(" ++ showVal a ++ "," ++ showVal b ++ ")"
    | .tuple a b (some d) => "(" ++ showVal a ++ "," ++ showVal b ++ "," ++ showVal d ++ ")"
    -- effect values: what Elm/JS's Debug.toString prints for them
    | .batch _ => "<internals>"
    | .mapE _ _ => "<internals>"
    | .prog _ => "<internals>"
    | .succeed _ | .fail _ | .andThen _ _ | .onError _ _ | .prim _ _ | .pid _ | .leaf _ _ =>
      "<internals>"
    | .bv j => showBV j
  def showArgs : List Val → List String
    | [] => []
    | a :: rest =>
      (" " ++ (if isAtomicShow a then showVal a else "(" ++ showVal a ++ ")")) :: showArgs rest
  def showFields : List (String × Val) → List String
    | [] => []
    | (l, x) :: rest => (l ++ " = " ++ showVal x) :: showFields rest
  def listElems : Val → Option (List String)
    | .con c [] => if c == conNil then some [] else none
    | .con c [x, xs] =>
      if c == conCons then (listElems xs).map (fun es => showVal x :: es) else none
    | _ => none
end

/-- Records print with their fields in label order. -/
def sortFields (r : List (String × Val)) : List (String × Val) :=
  r.mergeSort (fun a b => decide (a.1 ≤ b.1))

mutual
  /-- Normalise records (sort fields) everywhere before printing. -/
  def normVal : Val → Val
    | .record r => .record (sortFields (normFields r))
    | .con c args => .con c (normList args)
    | .tuple a b none => .tuple (normVal a) (normVal b) none
    | .tuple a b (some d) => .tuple (normVal a) (normVal b) (some (normVal d))
    | x => x
  def normList : List Val → List Val
    | [] => []
    | x :: xs => normVal x :: normList xs
  def normFields : List (String × Val) → List (String × Val)
    | [] => []
    | (l, x) :: rest => (l, normVal x) :: normFields rest
end

def showElm (x : Val) : String := showVal (normVal x)

/-- As `showElm`, but a float zero prints with its sign, `+0` or `-0`: for
    the theorems about signed zeros (rulings A48 and A49). -/
def showElmSigned (x : Val) : String :=
  match x with
  | .sv (.float f) => if f == 0 then (if 1 / f > 0 then "+0" else "-0") else showElm x
  | _ => showElm x

end StandardElm
