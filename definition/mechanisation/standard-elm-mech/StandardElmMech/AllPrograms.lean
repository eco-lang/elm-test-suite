/-
  A Standard Definition of Elm? Mechanisation: every example program, for the
  executables. The test programs translated by definition/tools/src/Translate.elm
  (Generated/), then the partial hand translations of tests it refuses
  (`handPartial` in Examples.lean).
-/
import StandardElmMech.Generated.All
import StandardElmMech.Examples

namespace StandardElm

/-- The shards of examples, by name: the generated shards, then "Hand". -/
def exampleShards : List (String × List Program) :=
  generatedShards ++ (if handPartial.isEmpty then [] else [("Hand", handPartial)])

/-- Every example program. -/
def allPrograms : List Program :=
  exampleShards.foldr (fun s acc => s.2 ++ acc) []

end StandardElm
