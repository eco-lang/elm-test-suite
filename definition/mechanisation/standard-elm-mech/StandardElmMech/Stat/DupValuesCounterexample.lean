/-
  A Standard Definition of Elm? Mechanisation: a regression test of the reading of instances by
  specialisation (plan step 10, found 2026-11-12 while removing the instance lists from step 9's
  occurrence nodes).

  The program (one module, two top-level `x`: it breaks res:modules-values-distinct, which no
  theorem of step 10 assumes):

      module Main exposing (main)
      import Html exposing (text)
      x = 1
      f y = if x then y else y
      x = f 1 == f 2
      h y = y + (if x then 1 else 1)
      main = text (Debug.toString (h 1 // 2))

  The checker reads `x` in `h` as the second `x`, of scheme `∀number. Bool` (A93: its bound
  variable is vacuous), while specialisation's scope reads it as the first, `∀number. number`
  (`Scope.ref` takes the first top-level group that binds a name). The instance at that occurrence
  is a witness of `σ ≻ τ`, not a type of the sentence, so occurrence nodes no longer carry it: the
  inferred derivation `dA` (instance `fresh 4`) and `dA'` (instance `h`'s own variable, `fresh 6`)
  have the same nodes (`facts`, `nodes_eq`), and each is principal exactly when the other is.
  Specialisation once read the instance list: in the copy `h$Int` the occurrence became `x` with
  `dA` and `x$Int` with `dA'`, so `reduce_principal_unique` and `ident_of_spec'` were false with
  the new nodes. It now reads the instance off the occurrence's type (`Ty.readVar`): here the
  first `x`'s body `number` against `Bool`, which is not a number, in both derivations
  (`same`), as it would be for any two derivations with the same nodes.
-/
import StandardElmMech.Stat.EndToEnd
import StandardElmMech.Stat.TestBasis
import StandardElmMech.Stat.RenameSyntax

namespace StandardElm.Stat
open StandardElm.Src (prog mdl hdr imp val v qv i app bin pv)

namespace DupCE

def dupProg : Src.SProgram := Src.canonOrder <| prog "ce" "Dup" [
  mdl (hdr false "Main" (.items [.var "main"]))
    [imp "Html" none (some (.items [.var "text"]))]
    [val "x" none [] (i 1),
     val "f" none [pv "y"] (.ifte [(v "x", v "y")] (v "y")),
     val "x" none [] (bin "==" (app (v "f") [i 1]) (app (v "f") [i 2])),
     val "h" none [pv "y"] (bin "+" (v "y") (.paren (.ifte [(v "x", i 1)] (i 1)))),
     val "main" none [] (app (v "text")
       [.paren (app (qv "Debug" "toString") [.paren (bin "//" (app (v "h") [i 1]) (i 2))])])]]

/-- The program breaks res:modules-values-distinct. -/
theorem not_valuesDistinct : ∃ m ∈ dupProg.modules, ¬ Src.ValuesDistinct m := by
  refine ⟨_, List.mem_singleton_self _, by decide⟩

/-- The derivation the inference gives. -/
def dA : AProgram :=
  match inferProgram Btest (bareOf dupProg) with
  | .ok a => a
  | .error _ => []

/-- The instance at `x` in `h` (the vacuous `fresh 4`) set to `h`'s own variable (`fresh 6`). -/
def merge : Renaming := ⟨fun a => if a = .fresh 4 .num then .fresh 6 .num else a, id, []⟩

def dA' : AProgram := dA.rename merge

def m0 : AModule := dA.headD ⟨⟨false, "", .all⟩, [], none⟩
def m0' : AModule := dA'.headD ⟨⟨false, "", .all⟩, [], none⟩

set_option maxRecDepth 100000 in
/-- Both are derivations of the program, and generate no type name. -/
theorem facts : dA.length = 1 ∧ dA'.length = 1 ∧
    checkProgram Btest dA = true ∧ checkProgram Btest dA' = true ∧
    dA.map AModule.erase = (bareOf dupProg).modules ∧ dA'.map AModule.erase = (bareOf dupProg).modules ∧
    genNames Btest m0 = [] ∧ genNames Btest m0' = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Their nodes are equal. -/
theorem nodes_eq : (nodesModule Btest m0').map (fun n => (n.path, n.U, n.tys, n.schemes)) =
    (nodesModule Btest m0).map (fun n => (n.path, n.U, n.tys, n.schemes)) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Specialisation gives the same for both: no reduced program (`x`'s instance is not a number). -/
theorem same : (reduceProgram Btest dA).toOption = none ∧ (reduceProgram Btest dA').toOption = none := by
  decide +kernel

end DupCE

end StandardElm.Stat
