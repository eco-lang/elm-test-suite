/-
  A Standard Definition of Elm? Mechanisation, part 3.
  The function APPLY of Appendix D (sec:appendix-dynamic-basis-apply) for the
  basic values of the fragment: Int arithmetic (fig:dynamic-basis-int),
  Float + - * / and negate (fig:dynamic-basis-float, the four basic
  operations only), equality (fig:dynamic-basis-eq), order
  (fig:dynamic-basis-order and the lt/le/gt/ge table), min and max (A48),
  clamp (A49), Booleans
  (sec:appendix-dynamic-basis-bool) and Debug.log / Debug.todo
  (sec:appendix-dynamic-basis-debug).

  APPLY(b, v1 ... vn) is a finite set of values. We give it twice:
  * `Apply b vs v`, an inductive relation meaning v is in APPLY(b, vs),
    one constructor per line of the book's displays;
  * `applySet b vs`, an executable list of the members, proved sound
    for `Apply` (`applySet_sound`).
  Eq (a subset of {True, False}) and cmp are functions, as in the book,
  defined by structural recursion on values.
-/
import StandardElmMech.Objects
import StandardElmMech.Show

set_option linter.unusedSimpArgs false

namespace StandardElm

/-! ## Function values and equality (fig:dynamic-basis-eq) -/

/-- Fun = Closure + BasApp + constructor values awaiting arguments. -/
def isFun : Val → Bool
  | .closure .. => true
  | .basApp .. => true
  | .con c args => decide (args.length < c.arity)
  | _ => false

/-- A subset of {True, False}: `t` says True is a member, `f` False. -/
structure BoolSet where
  t : Bool
  f : Bool
  deriving Repr, DecidableEq

def BoolSet.both : BoolSet := ⟨true, true⟩
def BoolSet.just (b : Bool) : BoolSet := ⟨b, !b⟩
/-- Clause 4: True if True for every component, False if False for some. -/
def BoolSet.conj (a b : BoolSet) : BoolSet := ⟨a.t && b.t, a.f || b.f⟩
def BoolSet.mem (b : Bool) (s : BoolSet) : Prop := if b then s.t = true else s.f = true

def recDomEq (r r' : List (String × Val)) : Bool :=
  (fmDom r).all (fun l => (fmDom r').contains l) && (fmDom r').all (fun l => (fmDom r).contains l)

mutual
  /-- Eq(v, v'), clauses 1 to 5 tried in order. -/
  def eqSet : Val → Val → BoolSet
    | v, v' =>
      if isFun v && isFun v' then BoolSet.both                             -- clause 1
      else match v, v' with
      | .sv (.float x), .sv (.float y) => BoolSet.just (x == y)            -- clause 2 (IEEE ==)
      | .sv (.int m), .sv (.int n) => BoolSet.just (m == n)                -- clause 3
      | .sv (.char c), .sv (.char c') => BoolSet.just (c == c')
      | .sv (.str s), .sv (.str s') => BoolSet.just (s == s')
      | .unit, .unit => BoolSet.just true
      | .tuple a b none, .tuple a' b' none =>                              -- clause 4: tuples
          (eqSet a a').conj (eqSet b b')
      | .tuple a b (some c), .tuple a' b' (some c') =>
          ((eqSet a a').conj (eqSet b b')).conj (eqSet c c')
      | .con c args, .con c' args' =>                                       -- clause 4: complete constructor values
          if c == c' && args.length == c.arity && args'.length == c'.arity
          then eqList args args' else BoolSet.just false
      | .record r, .record r' =>                                            -- clause 4: records, Dom r = Dom r'
          if recDomEq r r' then eqRec r r' else BoolSet.just false
      | _, _ => BoolSet.just false                                          -- clause 5
  def eqList : List Val → List Val → BoolSet
    | [], [] => BoolSet.just true
    | v :: vs, v' :: vs' => (eqSet v v').conj (eqList vs vs')
    | _, _ => BoolSet.just false
  def eqRec : List (String × Val) → List (String × Val) → BoolSet
    | [], _ => BoolSet.just true
    | (l, v) :: rest, r' =>
      match fmLookup r' l with
      | some v' => (eqSet v v').conj (eqRec rest r')
      | none => BoolSet.just false
end

/-! ## Order (fig:dynamic-basis-order) -/

def cmpInt (m n : Int) : Ordering := if m < n then .lt else if m = n then .eq else .gt

def cmpFloat (x y : Float) : Ordering :=
  if x.isNaN && y.isNaN then .eq
  else if x.isNaN then .gt
  else if y.isNaN then .lt
  else if x < y then .lt else if x == y then .eq else .gt

def cmpChars : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | c :: cs, c' :: cs' =>
    if c.toNat != c'.toNat then cmpInt c.toNat c'.toNat else cmpChars cs cs'

/-- Clause 4 of cmp on strings: first differing character, else length.
    For sequences of characters this is the lexicographic order above. -/
def cmpStr (s s' : String) : Ordering := cmpChars s.toList s'.toList

-- `o1.then o2` (Lean core): o2 if o1 is EQ, else o1.

mutual
  /-- cmp(v, v'), defined for comparable values of one type. -/
  def cmp : Val → Val → Option Ordering
    | .sv (.int m), .sv (.int n) => some (cmpInt m n)
    | .sv (.float x), .sv (.float y) => some (cmpFloat x y)
    | .sv (.char c), .sv (.char c') => some (cmpInt c.toNat c'.toNat)
    | .sv (.str s), .sv (.str s') => some (cmpStr s s')
    | .con c args, .con c' args' => cmpCon c args c' args'
    | .tuple a b c, .tuple a' b' c' =>
      match cmp a a', cmp b b', cmpOpt c c' with
      | some o1, some o2, some o3 => some (o1.then (o2.then o3))
      | _, _, _ => none
    | _, _ => none
  def cmpOpt : Option Val → Option Val → Option Ordering
    | none, none => some .eq
    | some v, some v' => cmp v v'
    | _, _ => none
  /-- Lists: [] < v1 :: v2; heads first, then tails. -/
  def cmpCon : Con → List Val → Con → List Val → Option Ordering
    | c, [], c', [] =>
      if c == conNil && c' == conNil then some .eq else none
    | c, [], c', [_, _] =>
      if c == conNil && c' == conCons then some .lt else none
    | c, [_, _], c', [] =>
      if c == conCons && c' == conNil then some .gt else none
    | c, [v1, v2], c', [v1', v2'] =>
      if c == conCons && c' == conCons then
        match cmp v1 v1', cmp v2 v2' with
        | some o1, some o2 => some (o1.then o2)
        | _, _ => none
      else none
    | _, _, _, _ => none
end

def Val.ofOrdering : Ordering → Val
  | .lt => .con conLT []
  | .eq => .con conEQ []
  | .gt => .con conGT []

def isFloat : Val → Bool
  | .sv (.float _) => true
  | _ => false

/-! ## min and max (sec:appendix-dynamic-basis-floatarith, sec:appendix-dynamic-basis-order; A48) -/

/-- x is the float -0. -/
def isNegZero (x : Float) : Bool := x == 0 && 1 / x < 0

/-- IEEE 754-2019 minimum: NaN if either argument is NaN; of two zeros, -0
    if either is -0; otherwise the smaller (the first when they are equal). -/
def fMinimum (x y : Float) : Float :=
  if x.isNaN then x else if y.isNaN then y
  else if x == 0 && y == 0 then (if isNegZero x then x else y)
  else if x ≤ y then x else y

/-- IEEE 754-2019 maximum: NaN if either argument is NaN; of two zeros, +0
    if either is +0; otherwise the larger (the first when they are equal). -/
def fMaximum (x y : Float) : Float :=
  if x.isNaN then x else if y.isNaN then y
  else if x == 0 && y == 0 then (if isNegZero x then y else x)
  else if y ≤ x then x else y

/-! ## clamp (sec:appendix-dynamic-basis-floatarith, sec:appendix-dynamic-basis-order; A49) -/

/-- At floats, clamp x y z (lower bound x, upper bound y, value z) is
    min (max z x) y with the IEEE 754-2019 minimum and maximum of A48. -/
def fClamp (x y z : Float) : Float := fMinimum (fMaximum z x) y

/-! ## Conversions, square root, powers, elementary functions
    (sec:appendix-dynamic-basis-conv, -floatarith, -elementary) -/

def fNaN : Float := 0 / 0
def fInf : Float := 1 / 0
/-- fl(pi), and fl(pi/2), fl(pi/4), fl(3pi/4), fl(e). -/
def fPi : Float := 3.141592653589793
def fHalfPi : Float := 1.5707963267948966
def fQuarterPi : Float := 0.7853981633974483
def fThreeQuarterPi : Float := 2.356194490192345
def fE : Float := 2.718281828459045

/-- sgn(x) for x not NaN: +1 for +0, +infinity and positive floats, -1 for -0,
    -infinity and negative ones. -/
def fSgn (x : Float) : Float := if x < 0 || (x == 0 && 1 / x < 0) then -1 else 1
def fIsInt (y : Float) : Bool := !y.isNaN && !y.isInf && y.floor == y
def fIsOdd (y : Float) : Bool := fIsInt y && (y / 2).floor != y / 2

/-- sat into the Int range [-2^63, 2^63 - 1]: Lean's `Float.toInt64` truncates
    towards zero and saturates into that range, giving 0 for NaN, so on an
    integral float or an infinity it is sat, and on NaN it gives the 0 that
    APPLY(b, NaN) is for each conversion b. -/
def satOfFloat (x : Float) : Int := x.toInt64.toInt

/-- fl(n): the float nearest an Int value. -/
def fToFloat (n : Int) : Float := Float.ofInt n
def fTruncate (x : Float) : Int := satOfFloat x
def fFloor (x : Float) : Int := satOfFloat x.floor
def fCeiling (x : Float) : Int := satOfFloat x.ceil
/-- sat(floor(x + 1/2)), the sum exact: x - floor x is exact for a finite
    float, so this rounds a half upward (round 2.5 is 3, round -2.5 is -2). -/
def fRound (x : Float) : Int :=
  let r := x.floor
  satOfFloat (if x - r ≥ 0.5 then r + 1 else r)

/-- APPLY(sqrt, x), fig:dynamic-basis-float, the first applicable line. -/
def fSqrt (x : Float) : Float :=
  if x.isNaN || x < 0 then fNaN
  else if x == 0 || x == fInf then x
  else x.sqrt

/-- APPLY(pow, x, y) at floats, fig:dynamic-basis-pow, the first applicable
    line; the last line, fl(x^y), is the implementation's (here the C
    library's) rounding of the real power, which the book allows (A65). -/
def fPow (x y : Float) : Float :=
  if y == 0 then 1
  else if x == 1 then 1
  else if x.isNaN || y.isNaN then fNaN
  else if x == 0 && y < 0 && fIsOdd y then fSgn x * fInf
  else if x == 0 && y < 0 then fInf
  else if x == 0 && y > 0 && fIsOdd y then x
  else if x == 0 && y > 0 then 0
  else if x == -1 && y.isInf then 1
  else if x.abs < 1 && y == fInf then 0
  else if x.abs > 1 && y == -fInf then 0
  else if x.abs > 1 && y == fInf then fInf
  else if x.abs < 1 && y == -fInf then fInf
  else if x == fInf && y < 0 then 0
  else if x == fInf && y > 0 then fInf
  else if x == -fInf && y < 0 && fIsOdd y then -(0 : Float)
  else if x == -fInf && y > 0 && fIsOdd y then -fInf
  else if x == -fInf && y < 0 then 0
  else if x == -fInf && y > 0 then fInf
  else if x < 0 && !fIsInt y then fNaN
  else Float.pow x y

/-- APPLY(b, x) for b among sin, cos, tan, asin, acos, atan,
    fig:dynamic-basis-elem; the last line, fl(f(x)), is the implementation's
    (the C library's) rounding, which the book allows. -/
def fElem (b : BasVal) (x : Float) : Float :=
  if x.isNaN then fNaN
  else if x == 0 && (b == .sin || b == .tan || b == .asin || b == .atan) then x
  else if x.isInf && (b == .sin || b == .cos || b == .tan) then fNaN
  else if x.abs > 1 && (b == .asin || b == .acos) then fNaN
  else if b == .atan && x.isInf then fSgn x * fHalfPi
  else match b with
    | .sin => x.sin | .cos => x.cos | .tan => x.tan
    | .asin => x.asin | .acos => x.acos | .atan => x.atan
    | _ => fNaN

/-- APPLY(atan2, y, x), fig:dynamic-basis-elem, the first applicable line. -/
def fAtan2 (y x : Float) : Float :=
  if x.isNaN || y.isNaN then fNaN
  else if y == 0 && (x > 0 || (x == 0 && fSgn x > 0)) then y
  else if y == 0 && (x < 0 || (x == 0 && fSgn x < 0)) then fSgn y * fPi
  else if x == 0 then fSgn y * fHalfPi
  else if y.isInf && !x.isInf then fSgn y * fHalfPi
  else if y.isInf && x == -fInf then fSgn y * fThreeQuarterPi
  else if y.isInf && x == fInf then fSgn y * fQuarterPi
  else if x == -fInf then fSgn y * fPi
  else if x == fInf then fSgn y * 0
  else Float.atan2 y x

/-! ## append, characters (sec:appendix-dynamic-basis-append,
    sec:appendix-dynamic-basis-chars) -/

/-- APPLY(append, v, v'): strings concatenated; at lists, `[]` gives v', and
    v1 :: v2 gives v1 :: v'' where APPLY(append, v2, v') = {v''}. -/
def appendVal : Val → Val → Option Val
  | .sv (.str s), .sv (.str s') => some (.sv (.str (s ++ s')))
  | .con c [], v => if c == conNil then some v else none
  | .con c [h, t], v => if c == conCons then (appendVal t v).map (fun t' => .con conCons [h, t']) else none
  | _, _ => none

/-- A Unicode scalar value: 0 to 0x10FFFF, surrogates excluded. -/
def isScalar (n : Int) : Bool := 0 ≤ n && n ≤ 0x10FFFF && !(0xD800 ≤ n && n ≤ 0xDFFF)

/-- other(n), the character `Char.fromCode` gives for an integer that is no
    Unicode scalar value: a parameter of the definition, which this encoding
    sets to U+FFFD (Lean's characters are Unicode scalar values only). -/
def otherChar (_n : Int) : Char := Char.ofNat 0xFFFD

def charFromCode (n : Int) : Char := if isScalar n then Char.ofNat n.toNat else otherChar n

/-- `pickFirst b v v'` is v if b, else v'. A definition, not an `if`, so that
    the proof of `applySet_sound` does not split on it. -/
def pickFirst (b : Bool) (v v' : Val) : Val := if b then v else v'

def isTrue : Val → Bool
  | .con c [] => c == conTrue
  | _ => false
def isFalse : Val → Bool
  | .con c [] => c == conFalse
  | _ => false

/-! ## The relation: v ∈ APPLY(b, vs) -/

/-- `Apply b vs v` : v ∈ APPLY(b, v1 ... vn). One constructor per line of the
    displays of Appendix D, named after the basic value and the case. -/
inductive Apply : BasVal → List Val → Val → Prop where
  -- fig:dynamic-basis-int
  | add_int (m n : Int) : Apply .add [.int m, .int n] (.int (norm (m + n)))
  | sub_int (m n : Int) : Apply .sub [.int m, .int n] (.int (norm (m - n)))
  | mul_int (m n : Int) : Apply .mul [.int m, .int n] (.int (norm (m * n)))
  | negate_int (n : Int) : Apply .negate [.int n] (.int (norm (-n)))
  | idiv_nz (m n : Int) : n ≠ 0 → Apply .idiv [.int m, .int n] (.int (norm (Int.tdiv m n)))
  | idiv_zero (m : Int) : Apply .idiv [.int m, .int 0] (.int 0)
  /-- modBy n m = m - n * floor(m / n); the first argument is the divisor. -/
  | modBy_nz (n m : Int) : n ≠ 0 → Apply .modBy [.int n, .int m] (.int (m - n * Int.fdiv m n))
  | modBy_zero (m : Int) : Apply .modBy [.int 0, .int m] (.int 0)
  /-- remainderBy n m = m - n * trunc(m / n). -/
  | remainderBy_nz (n m : Int) : n ≠ 0 → Apply .remainderBy [.int n, .int m] (.int (m - n * Int.tdiv m n))
  | remainderBy_zero (m : Int) : Apply .remainderBy [.int 0, .int m] (.int 0)
  | pow_nonneg (m n : Int) : 0 ≤ n → Apply .pow [.int m, .int n] (.int (norm (m ^ n.toNat)))
  | pow_neg_one (n : Int) : n < 0 → Apply .pow [.int 1, .int n] (.int 1)
  | pow_neg_minus_one (n : Int) : n < 0 → Apply .pow [.int (-1), .int n] (.int ((-1) ^ n.natAbs))
  | pow_neg_other (m n : Int) : n < 0 → m ≠ 1 → m ≠ -1 → Apply .pow [.int m, .int n] (.int 0)
  -- fig:dynamic-basis-float (the four operations and negation only; IEEE binary64 via Lean's Float)
  | add_float (x y : Float) : Apply .add [.sv (.float x), .sv (.float y)] (.sv (.float (x + y)))
  | sub_float (x y : Float) : Apply .sub [.sv (.float x), .sv (.float y)] (.sv (.float (x - y)))
  | mul_float (x y : Float) : Apply .mul [.sv (.float x), .sv (.float y)] (.sv (.float (x * y)))
  | fdiv_float (x y : Float) : Apply .fdiv [.sv (.float x), .sv (.float y)] (.sv (.float (x / y)))
  | negate_float (x : Float) : Apply .negate [.sv (.float x)] (.sv (.float (-x)))
  -- sec:appendix-dynamic-basis-eq
  | eq (v v' : Val) (b : Bool) : BoolSet.mem b (eqSet v v') → Apply .eq [v, v'] (.bool b)
  | neq_true (v v' : Val) : (eqSet v v').f = true → Apply .neq [v, v'] (.bool true)
  | neq_false (v v' : Val) : (eqSet v v').t = true → Apply .neq [v, v'] (.bool false)
  -- sec:appendix-dynamic-basis-order
  | compare (v v' : Val) (o : Ordering) : cmp v v' = some o → Apply .compare [v, v'] (.ofOrdering o)
  | lt_float (x y : Float) : Apply .lt [.sv (.float x), .sv (.float y)] (.bool (decide (x < y)))
  | le_float (x y : Float) : Apply .le [.sv (.float x), .sv (.float y)] (.bool (decide (x ≤ y)))
  | gt_float (x y : Float) : Apply .gt [.sv (.float x), .sv (.float y)] (.bool (decide (y < x)))
  | ge_float (x y : Float) : Apply .ge [.sv (.float x), .sv (.float y)] (.bool (decide (y ≤ x)))
  | lt_cmp (v v' : Val) (o : Ordering) : isFloat v = false → cmp v v' = some o →
      Apply .lt [v, v'] (.bool (o == .lt))
  | le_cmp (v v' : Val) (o : Ordering) : isFloat v = false → cmp v v' = some o →
      Apply .le [v, v'] (.bool (o != .gt))
  | gt_cmp (v v' : Val) (o : Ordering) : isFloat v = false → cmp v' v = some o →
      Apply .gt [v, v'] (.bool (o == .lt))
  | ge_cmp (v v' : Val) (o : Ordering) : isFloat v = false → cmp v' v = some o →
      Apply .ge [v, v'] (.bool (o != .gt))
  -- min and max (A48): IEEE minimum and maximum at floats; at every other
  -- comparable type the result of the elm/core text, v if lt v v' (resp.
  -- gt v v') is True, else v'
  | min_float (x y : Float) : Apply .min [.sv (.float x), .sv (.float y)] (.sv (.float (fMinimum x y)))
  | max_float (x y : Float) : Apply .max [.sv (.float x), .sv (.float y)] (.sv (.float (fMaximum x y)))
  | min_cmp (v v' : Val) (o : Ordering) : isFloat v = false → cmp v v' = some o →
      Apply .min [v, v'] (pickFirst (o == .lt) v v')
  | max_cmp (v v' : Val) (o : Ordering) : isFloat v = false → cmp v' v = some o →
      Apply .max [v, v'] (pickFirst (o == .lt) v v')
  -- clamp (A49): at floats min (max z x) y with the IEEE operations above;
  -- otherwise the result of the elm/core text,
  -- if lt v'' v then v else if gt v'' v' then v' else v'',
  -- where lt v'' v is cmp(v'', v) = LT and gt v'' v' is cmp(v', v'') = LT
  | clamp_float (x y z : Float) :
      Apply .clamp [.sv (.float x), .sv (.float y), .sv (.float z)] (.sv (.float (fClamp x y z)))
  | clamp_cmp (v v' v'' : Val) (o o' : Ordering) : isFloat v'' = false →
      cmp v'' v = some o → cmp v' v'' = some o' →
      Apply .clamp [v, v', v''] (pickFirst (o == .lt) v (pickFirst (o' == .lt) v' v''))
  -- sec:appendix-dynamic-basis-bool
  | not_true (v : Val) : isTrue v = true → Apply .not [v] (.bool false)
  | not_other (v : Val) : isTrue v = false → Apply .not [v] (.bool true)
  | and_ (v v' : Val) : Apply .and [v, v'] (.bool (isTrue v && isTrue v'))
  | or_ (v v' : Val) : Apply .or [v, v'] (.bool (!(isFalse v && isFalse v')))
  | xor_ (v v' : Val) : Apply .xor [v, v'] (.bool (isTrue v != isTrue v'))
  -- isNaN, isInfinite (sec:appendix-dynamic-basis-floatarith): True exactly
  -- when the float is NaN, or +infinity or -infinity
  | isNaN_ (x : Float) : Apply .isNaN [.sv (.float x)] (.bool x.isNaN)
  | isInfinite_ (x : Float) : Apply .isInfinite [.sv (.float x)] (.bool x.isInf)
  -- conversions (fig:dynamic-basis-conv)
  | toFloat_ (n : Int) : Apply .toFloat [.int n] (.sv (.float (fToFloat n)))
  | round_ (x : Float) : Apply .round [.sv (.float x)] (.int (fRound x))
  | floor_ (x : Float) : Apply .floor [.sv (.float x)] (.int (fFloor x))
  | ceiling_ (x : Float) : Apply .ceiling [.sv (.float x)] (.int (fCeiling x))
  | truncate_ (x : Float) : Apply .truncate [.sv (.float x)] (.int (fTruncate x))
  -- sqrt (fig:dynamic-basis-float), powers and elementary functions
  -- (fig:dynamic-basis-pow, fig:dynamic-basis-elem)
  | sqrt_ (x : Float) : Apply .sqrt [.sv (.float x)] (.sv (.float (fSqrt x)))
  | pow_float (x y : Float) : Apply .pow [.sv (.float x), .sv (.float y)] (.sv (.float (fPow x y)))
  | sin_ (x : Float) : Apply .sin [.sv (.float x)] (.sv (.float (fElem .sin x)))
  | cos_ (x : Float) : Apply .cos [.sv (.float x)] (.sv (.float (fElem .cos x)))
  | tan_ (x : Float) : Apply .tan [.sv (.float x)] (.sv (.float (fElem .tan x)))
  | asin_ (x : Float) : Apply .asin [.sv (.float x)] (.sv (.float (fElem .asin x)))
  | acos_ (x : Float) : Apply .acos [.sv (.float x)] (.sv (.float (fElem .acos x)))
  | atan_ (x : Float) : Apply .atan [.sv (.float x)] (.sv (.float (fElem .atan x)))
  | atan2_ (y x : Float) : Apply .atan2 [.sv (.float y), .sv (.float x)] (.sv (.float (fAtan2 y x)))
  -- append (sec:appendix-dynamic-basis-append), characters, Debug.toString
  | append_ (v v' w : Val) : appendVal v v' = some w → Apply .append [v, v'] w
  | toCode_ (c : Char) : Apply .charToCode [.sv (.char c)] (.int c.toNat)
  | fromCode_ (n : Int) : Apply .charFromCode [.int n] (.sv (.char (charFromCode n)))
  -- the string of Debug.toString is the implementation's: here as Elm prints
  | toString_ (v : Val) : Apply .debugToString [v] (.sv (.str (showElm v)))
  -- sec:appendix-dynamic-basis-debug; Debug.todo has no constructor: APPLY is empty
  | debugLog (s : String) (v : Val) : Apply .debugLog [.sv (.str s), v] v

/-! ## The executable set -/

def boolSetList (s : BoolSet) : List Val :=
  (if s.t then [Val.bool true] else []) ++ (if s.f then [Val.bool false] else [])

/-- The members of APPLY(b, vs), as a list. -/
def applySet : BasVal → List Val → List Val
  | .add, [.sv (.int m), .sv (.int n)] => [.int (norm (m + n))]
  | .sub, [.sv (.int m), .sv (.int n)] => [.int (norm (m - n))]
  | .mul, [.sv (.int m), .sv (.int n)] => [.int (norm (m * n))]
  | .negate, [.sv (.int n)] => [.int (norm (-n))]
  | .idiv, [.sv (.int m), .sv (.int n)] =>
      if n = 0 then [.int 0] else [.int (norm (Int.tdiv m n))]
  | .modBy, [.sv (.int n), .sv (.int m)] =>
      if n = 0 then [.int 0] else [.int (m - n * Int.fdiv m n)]
  | .remainderBy, [.sv (.int n), .sv (.int m)] =>
      if n = 0 then [.int 0] else [.int (m - n * Int.tdiv m n)]
  | .pow, [.sv (.int m), .sv (.int n)] =>
      if 0 ≤ n then [.int (norm (m ^ n.toNat))]
      else if m = 1 then [.int 1]
      else if m = -1 then [.int ((-1) ^ n.natAbs)]
      else [.int 0]
  | .add, [.sv (.float x), .sv (.float y)] => [.sv (.float (x + y))]
  | .sub, [.sv (.float x), .sv (.float y)] => [.sv (.float (x - y))]
  | .mul, [.sv (.float x), .sv (.float y)] => [.sv (.float (x * y))]
  | .fdiv, [.sv (.float x), .sv (.float y)] => [.sv (.float (x / y))]
  | .negate, [.sv (.float x)] => [.sv (.float (-x))]
  | .eq, [v, v'] => boolSetList (eqSet v v')
  | .neq, [v, v'] =>
      (if (eqSet v v').f then [Val.bool true] else []) ++ (if (eqSet v v').t then [Val.bool false] else [])
  | .compare, [v, v'] =>
      match cmp v v' with
      | some o => [.ofOrdering o]
      | none => []
  | .lt, [.sv (.float x), .sv (.float y)] => [.bool (decide (x < y))]
  | .le, [.sv (.float x), .sv (.float y)] => [.bool (decide (x ≤ y))]
  | .gt, [.sv (.float x), .sv (.float y)] => [.bool (decide (y < x))]
  | .ge, [.sv (.float x), .sv (.float y)] => [.bool (decide (y ≤ x))]
  | .lt, [v, v'] =>
      if isFloat v then [] else match cmp v v' with | some o => [.bool (o == .lt)] | none => []
  | .le, [v, v'] =>
      if isFloat v then [] else match cmp v v' with | some o => [.bool (o != .gt)] | none => []
  | .gt, [v, v'] =>
      if isFloat v then [] else match cmp v' v with | some o => [.bool (o == .lt)] | none => []
  | .ge, [v, v'] =>
      if isFloat v then [] else match cmp v' v with | some o => [.bool (o != .gt)] | none => []
  | .min, [.sv (.float x), .sv (.float y)] => [.sv (.float (fMinimum x y))]
  | .max, [.sv (.float x), .sv (.float y)] => [.sv (.float (fMaximum x y))]
  | .min, [v, v'] =>
      if isFloat v then [] else match cmp v v' with | some o => [pickFirst (o == .lt) v v'] | none => []
  | .max, [v, v'] =>
      if isFloat v then [] else match cmp v' v with | some o => [pickFirst (o == .lt) v v'] | none => []
  | .clamp, [.sv (.float x), .sv (.float y), .sv (.float z)] => [.sv (.float (fClamp x y z))]
  | .clamp, [v, v', v''] =>
      if isFloat v'' then [] else
      match cmp v'' v, cmp v' v'' with
      | some o, some o' => [pickFirst (o == .lt) v (pickFirst (o' == .lt) v' v'')]
      | _, _ => []
  | .not, [v] => if isTrue v then [.bool false] else [.bool true]
  | .and, [v, v'] => [.bool (isTrue v && isTrue v')]
  | .or, [v, v'] => [.bool (!(isFalse v && isFalse v'))]
  | .xor, [v, v'] => [.bool (isTrue v != isTrue v')]
  | .isNaN, [.sv (.float x)] => [.bool x.isNaN]
  | .isInfinite, [.sv (.float x)] => [.bool x.isInf]
  | .toFloat, [.sv (.int n)] => [.sv (.float (fToFloat n))]
  | .round, [.sv (.float x)] => [.int (fRound x)]
  | .floor, [.sv (.float x)] => [.int (fFloor x)]
  | .ceiling, [.sv (.float x)] => [.int (fCeiling x)]
  | .truncate, [.sv (.float x)] => [.int (fTruncate x)]
  | .sqrt, [.sv (.float x)] => [.sv (.float (fSqrt x))]
  | .pow, [.sv (.float x), .sv (.float y)] => [.sv (.float (fPow x y))]
  | .sin, [.sv (.float x)] => [.sv (.float (fElem .sin x))]
  | .cos, [.sv (.float x)] => [.sv (.float (fElem .cos x))]
  | .tan, [.sv (.float x)] => [.sv (.float (fElem .tan x))]
  | .asin, [.sv (.float x)] => [.sv (.float (fElem .asin x))]
  | .acos, [.sv (.float x)] => [.sv (.float (fElem .acos x))]
  | .atan, [.sv (.float x)] => [.sv (.float (fElem .atan x))]
  | .atan2, [.sv (.float y), .sv (.float x)] => [.sv (.float (fAtan2 y x))]
  | .append, [v, v'] => match appendVal v v' with | some w => [w] | none => []
  | .charToCode, [.sv (.char c)] => [.int c.toNat]
  | .charFromCode, [.sv (.int n)] => [.sv (.char (charFromCode n))]
  | .debugToString, [v] => [.sv (.str (showElm v))]
  | .debugLog, [.sv (.str _), v] => [v]
  | _, _ => []

/-- Every member of `applySet b vs` is in APPLY(b, vs). -/
theorem applySet_sound {b : BasVal} {vs : List Val} {v : Val} :
    v ∈ applySet b vs → Apply b vs v := by
  intro h
  unfold applySet at h
  split at h
  all_goals (try simp only [boolSetList] at h)
  all_goals (repeat' (first | (split at h) | (rw [List.mem_append] at h; rcases h with h | h)))
  all_goals (try simp only [List.mem_cons, List.not_mem_nil, or_false, false_or] at h)
  all_goals (try subst h)
  all_goals (try subst_vars)
  all_goals (try simp only [Bool.not_eq_true] at *)
  all_goals (first
    | (constructor <;> first | assumption | (simp only [BoolSet.mem, ite_true, ite_false, Bool.false_eq_true]; assumption) | omega)
    | skip)

end StandardElm
