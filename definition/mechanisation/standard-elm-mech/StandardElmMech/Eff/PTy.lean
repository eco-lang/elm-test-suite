/-
  A Standard Definition of Elm? Mechanisation: payload types (plan step 2; their meaning, encoding and
  decoding, is step 4's).

  A port's basic value carries the payload type of the port (dynamic-modules.tex, the reduced syntax
  of ports; static-modules.tex, sec:static-modules-ports), and basic values come before values, so
  the payload types come first. A record's fields are sorted by label, without duplicates (the
  translator writes them so), so that equal types are equal terms.
-/
namespace StandardElm.Eff

mutual
  inductive PTy where
    | int | float | bool | string | bytes | unit
    /-- Json.Encode.Value -/
    | value
    | list (τ : PTy) | maybe (τ : PTy) | array (τ : PTy)
    | tuple2 (a b : PTy) | tuple3 (a b c : PTy)
    | record (fs : PFields)
  /-- The fields of a record payload type, sorted by label. A list of its own (not
      `List (String × PTy)`), so that equality of payload types is derived. -/
  inductive PFields where
    | nil
    | cons (l : String) (τ : PTy) (rest : PFields)
end

deriving instance Repr, DecidableEq for PTy, PFields

instance : Inhabited PTy := ⟨.unit⟩

def PFields.toList : PFields → List (String × PTy)
  | .nil => []
  | .cons l τ rest => (l, τ) :: rest.toList

end StandardElm.Eff
