/-
  A Standard Definition of Elm? Mechanisation: a counterexample to the invariance lemma of plan
  step 10 (finding B1, `reduce_principal_unique`) as `Stat/Specialise.lean` stood before
  2026-11-12, kept as a regression test of the fix (`Member.bOutAll`): the two principal
  derivations below now give the same reduced program (`ce_equal`).

  The program (two modules):

      module M exposing (f, g)
      f : number -> number
      f x = if g then x else x
      g = f 1 == f 2

      module Main exposing (main)
      import Html exposing (text)
      import M exposing (g)
      k y = y + (if g then 1 else 1)
      main = text (Debug.toString (k 1 // 2))

  `f` and `g` form one group; its `number` variables are `[number]` (the U' of `f`'s annotation),
  and `g`'s scheme `Bool` does not bind it. An occurrence of `g` outside the group reaches
  `occNum`'s last branch, which reads `number` from the assignment of the enclosing copies, `ρ`;
  in `Main` that is the copy of `k`, whose `ρ` binds `k`'s own type variable. `ceA` is what the
  inference gives (k : fresh 5 -> fresh 5); `ceA'` is the same program derivation with module
  `Main`'s variable `fresh 5 num` renamed to `named "number"` (an injective, class-preserving
  renaming; `Main` has no annotation, so nothing else names that variable). Both are derivations
  of the program (`ce_progDeriv`), and the two module derivations of `Main` are instances of each
  other (the substitution is the renaming, resp. its inverse; `Main`'s nodes have empty U, and its
  closed schemes have no free variables), so either is principal exactly when the other is. Under
  D11 for this program (the inferred one is principal) both are principal program derivations, yet
  `reduceProgram` differs (`ce_differ`): in `ceA'` the occurrence of `g` in `k$Int` is captured by
  `k`'s variable and becomes `g$Int` (and `M` gains copies `f$Int`, `g$Int`); in `ceA` it is `g`.
  So `reduce_principal_unique`, `specOf_functional` and `ident_of_spec` are false for the current
  definitions.

  The same example refutes `mutualInstanceMod_renaming` with `Renaming.WF` as Rename.lean states it
  (`tv_named`): the only renaming taking `ceA` to `ceA'` moves a `named` variable.

  A fix (checked by running a modified copy of Specialise.lean/EndToEnd.lean on this program: the
  two reduced programs are then equal): outside its group, every variable of the group is bound at
  an occurrence (it is closed by `Clos`, or bound by a member's annotation), so a variable that the
  member's scheme does not mention is A93's vacuous case, Float; only inside the group does
  Choices, item 5 read the enclosing copy. In code: the references made for occurrences outside the
  group (`refOut` in `specAtExp`, `TopGroup.refsOut`, `ModInfo.globals`) carry
  `m.bOut ++ (V.filter fun v => !(m.bOut.contains (.ty v))).map .ty` instead of `m.bOut`.
-/
import StandardElmMech.Stat.EndToEnd
import StandardElmMech.Stat.TestBasis
import StandardElmMech.Stat.RenameSyntax

namespace StandardElm.Stat
open StandardElm.Src (prog mdl hdr imp val v qv i app bin tv pv)

namespace RenameCE

def ceProg : Src.SProgram := Src.canonOrder <| prog "ce" "CE" [
  mdl (hdr false "M" (.items [.var "f", .var "g"])) []
    [val "f" (some (.fn (tv "number") (tv "number"))) [pv "x"] (.ifte [(v "g", v "x")] (v "x")),
     val "g" none [] (bin "==" (app (v "f") [i 1]) (app (v "f") [i 2]))],
  mdl (hdr false "Main" (.items [.var "main"]))
    [imp "Html" none (some (.items [.var "text"])), imp "M" none (some (.items [.var "g"]))]
    [val "k" none [pv "y"] (bin "+" (v "y") (.paren (.ifte [(v "g", i 1)] (i 1)))),
     val "main" none [] (app (v "text")
       [.paren (app (qv "Debug" "toString") [.paren (bin "//" (app (v "k") [i 1]) (i 2))])])]]

/-- The derivation the inference gives. -/
def ceA : AProgram :=
  match inferProgram Btest (bareOf ceProg) with
  | .ok a => a
  | .error _ => []

/-- `fresh 5 num` (k's variable in `ceA`) and `named "number"` exchanged. -/
def ceSwap : Renaming :=
  ⟨fun a => if a = .fresh 5 .num then .named "number" else if a = .named "number" then .fresh 5 .num else a,
   id, []⟩

/-- The second module renamed. -/
def renameSecond (r : Renaming) : AProgram → AProgram
  | [m, n] => [m, n.rename r]
  | a => a

def ceA' : AProgram := renameSecond ceSwap ceA

theorem ceSwap_apply (a : TyVar) : ceSwap.tvApply a =
    if a = .fresh 5 .num then .named "number" else if a = .named "number" then .fresh 5 .num else a := rfl

theorem ceSwap_inj : ∀ a b, ceSwap.tvApply a = ceSwap.tvApply b → a = b := by
  intro a b h
  rw [ceSwap_apply, ceSwap_apply] at h
  by_cases ha1 : a = .fresh 5 .num <;> by_cases ha2 : a = .named "number" <;>
    by_cases hb1 : b = .fresh 5 .num <;> by_cases hb2 : b = .named "number" <;>
    simp only [ha1, ha2, hb1, hb2, ↓reduceIte] at h <;> first | exact h | (subst_vars; rfl) | cases h | skip
  all_goals simp_all

theorem ceSwap_cls : ∀ a, (ceSwap.tvApply a).cls = a.cls := by
  intro a
  rw [ceSwap_apply]
  by_cases ha1 : a = .fresh 5 .num
  · subst ha1; decide
  · by_cases ha2 : a = .named "number"
    · subst ha2; decide
    · simp only [ha1, ha2, ↓reduceIte]

theorem renameSecond_erase (r : Renaming) (a : AProgram) :
    (renameSecond r a).map AModule.erase = a.map AModule.erase := by
  match a with
  | [m, n] => simp only [renameSecond, List.map_cons, List.map_nil, AModule.erase_rename]
  | [] | [_] | _ :: _ :: _ :: _ => rfl

set_option maxRecDepth 100000 in
/-- Both check, in the bases they build from the test basis. -/
theorem ce_checks : checkProgram Btest ceA = true ∧ checkProgram Btest ceA' = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The inferred derivation is a derivation of the program. -/
theorem ce_erase : ceA.map AModule.erase = (bareOf ceProg).modules := by decide +kernel

theorem ce_progDeriv : ProgDeriv Btest (bareOf ceProg) ceA ∧ ProgDeriv Btest (bareOf ceProg) ceA' :=
  ⟨⟨ce_checks.1, ce_erase⟩, ⟨ce_checks.2, (renameSecond_erase ceSwap ceA).trans ce_erase⟩⟩

set_option maxRecDepth 100000 in
/-- With the fix, the two principal program derivations give the same reduced program. -/
theorem ce_equal : (reduceProgram Btest ceA).toOption = (reduceProgram Btest ceA').toOption := by
  decide +kernel

end RenameCE

end StandardElm.Stat
