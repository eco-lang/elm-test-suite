/-
  A Standard Definition of Elm? Mechanisation, part 9.
  Printing values in the form the eco test suite's `-- CHECK:` lines use
  (the output of Debug.log), so that results compare as strings. This is a
  test harness, not part of the definition: Debug.toString lies outside it.
-/
import StandardElmMech.Objects

namespace StandardElm

def showStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun ch =>
    if ch == '"' then "\\\"" else if ch == '\\' then "\\\\" else ch.toString) ++ "\""

/-- Floats print as the eco test helper `f` prints them: `NaN`, `+0`, `-0`,
    `Infinity`, `-Infinity`, or the number with no trailing zeros. -/
def showFloat (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0 then (if 1 / x > 0 then "+0" else "-0")
  else if x.isInf then (if x > 0 then "Infinity" else "-Infinity")
  else
    let s := toString x
    if s.contains '.' then
      let t := (s.toList.reverse.dropWhile (· == '0')).reverse
      let t := if t.getLast? == some '.' then t.dropLast else t
      String.ofList t
    else s

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

end StandardElm
