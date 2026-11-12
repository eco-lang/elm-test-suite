/-
  A Standard Definition of Elm? Mechanisation: a counterexample to `ident_of_spec` (plan step 10,
  "The pipeline") and to `reduce_principal_unique` as the definitions stand on 2026-11-12: finding
  B6 (`r:sm-topdec-seq` splitting a type-declaration phrase gives a different environment) reaches
  the next module's basis, where `InstanceOfMod` does not look.

  The program (two modules):

      module M1 exposing (T(..))
      type T = T String
      type alias String = Int

      module Main exposing (main)
      import M1 exposing (T(..))
      main = Platform.worker
        { init = \fl -> let _ = T fl in ((), Cmd.none)
        , update = \_ m -> (m, Cmd.none)
        , subscriptions = \_ -> Sub.none }

  M1 has two shapes of derivation. The inference elaborates the type declarations whole
  (`r:sm-topdec-types`): the constructor's argument `String` is the local alias, so
  `T : Int -> T`. Splitting at the separator (`r:sm-topdec-seq`, step 9's `typesSplit`) elaborates
  the custom type first, in the basis, so `T : String -> T` (`m1_constructors`). Both check and
  erase to M1 (`ce_progDeriv`). Their nodes have no path in common (the whole shape has one node
  at `[]`, the split shape nodes at `[0]` and `[1]`, `m1_paths`), so each is an instance of the
  other with the identity substitution and the identity on the one generated name
  (`m1_mutual`), and M1 has no value declarations. Every derivation of M1 has one of these two
  shapes, with the type environment forced up to the generated name (the alias `String = Int` is
  not recursive, and the constructor's argument is elaborated in the context the shape gives), so
  both shapes are principal in `Btest`: the whole one by the same argument as `m1_mutual` against
  another whole one (the nodes at `[]` agree up to the name), the split one likewise.

  Main is derived in the basis M1 builds, which differs between the two shapes: `fl` is Int in one
  and String in the other, whatever the derivation of Main, so main's flags type is Int in one and
  String in the other. `ceA` (the inference's) and `ceA'` (M1 split, Main inferred in the basis that
  builds) are program derivations whose reduced programs differ (`ce_differ`: flags Int vs String),
  and `endToEnd Btest ceProg` succeeds with the first (`ce_endToEnd`). Under D11 for this program
  (Main's inferred derivation principal in the first basis) and the same claim for Main in the
  second basis (the derivation the inference gives there), both are principal program derivations,
  so `SpecOf Btest (bareOf ceProg)` holds of two different reduced programs and `ident_of_spec` is
  false for it.

  A single module would not do: a value declaration of M1 using `T` would have nodes at the same
  paths in both shapes with Int against String, so neither shape would be an instance of the other.
  The difference must pass through the basis of a later module, which `IsPrincipalMod` does not
  compare. Possible repairs (each changes an existing definition): give `typesSplit` a node at its
  own path carrying the environment it gives (so the two shapes are compared, and an incoherent
  module has no principal derivation, as step 11's plan says); or refuse `typesSplit` when its
  environment differs from the whole phrase's; or drop `typesSplit` (step 9's B6 reading).
-/
import StandardElmMech.Stat.EndToEnd
import StandardElmMech.Stat.TestBasis

namespace StandardElm.Stat
open StandardElm.Src (prog mdl hdr imp val v qv c app pv tc)

namespace SplitCE

def ceProg : Src.SProgram := Src.canonOrder <| prog "ce" "SplitCE" [
  mdl (hdr false "M1" (.items [.tyAll "T"])) []
    [.custom "T" [] [("T", [tc "String" []])], .alias "String" [] (tc "Int" [])],
  mdl (hdr false "Main" (.items [.var "main"]))
    [imp "M1" none (some (.items [.tyAll "T"]))]
    [val "main" none [] (app (qv "Platform" "worker") [.record [
      ("init", .lam [pv "fl"] (.letE [.pat .wild (app (c "T") [v "fl"])] (.tuple [.unit, qv "Cmd" "none"]))),
      ("update", .lam [.wild, pv "m"] (.tuple [v "m", qv "Cmd" "none"])),
      ("subscriptions", .lam [.wild] (qv "Sub" "none"))]])]]

/-- The derivation the inference gives (M1 whole). -/
def ceA : AProgram :=
  match inferProgram Btest (bareOf ceProg) with
  | .ok a => a
  | .error _ => []

/-- M1 derived with `r:sm-topdec-seq` splitting its type declarations after the custom type. -/
def m1Split : Option AModule := do
  let m1 ← (bareOf ceProg).modules.head?
  let C ← importCtx Btest m1.imports
  match m1.body with
  | some (.types db tbs) =>
    match inferTopDec C (1000 + Btest.T.length) (.types db []) with
    | .ok (a1, E1, _, b1) =>
      match inferTopDec (C.oplusE E1) b1 (.types none tbs) with
      | .ok (a2, _, _, _) => some ⟨m1.header, m1.imports, some (.typesSplit a1 a2)⟩
      | .error _ => none
    | .error _ => none
  | _ => none

/-- M1 split, and Main as the inference derives it in the basis the split M1 builds. -/
def ceA' : AProgram :=
  match m1Split, (bareOf ceProg).modules with
  | some a1, [_, m2] =>
    match a1.result Btest with
    | some (B1', _) =>
      match inferModule (Btest.plus B1') m2 with
      | .ok a2 => [a1, a2]
      | .error _ => []
    | none => []
  | _, _ => []

def m1W : AModule := ceA.headD ⟨⟨false, "", .all⟩, [], none⟩
def m1S : AModule := ceA'.headD ⟨⟨false, "", .all⟩, [], none⟩

/-- The type name M1 generates for `T` (the same in both derivations). -/
def tT : TyName := ⟨1022, 0⟩

set_option maxRecDepth 100000 in
/-- The pipeline succeeds on the program, with the inference's derivation. -/
theorem ce_endToEnd :
    (endToEnd Btest ceProg).toOption = (reduceProgram Btest ceA).toOption ∧
    ((reduceProgram Btest ceA).toOption.map (·.flagsType)) = some .int := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ce_checks : checkProgram Btest ceA = true ∧ checkProgram Btest ceA' = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ce_erase : ceA.map AModule.erase = (bareOf ceProg).modules ∧
    ceA'.map AModule.erase = (bareOf ceProg).modules := by
  decide +kernel

/-- Both are derivations of the program. -/
theorem ce_progDeriv : ProgDeriv Btest (bareOf ceProg) ceA ∧ ProgDeriv Btest (bareOf ceProg) ceA' :=
  ⟨⟨ce_checks.1, ce_erase.1⟩, ⟨ce_checks.2, ce_erase.2⟩⟩

set_option maxRecDepth 100000 in
/-- Their reduced programs differ: main's flags are Int in one and String in the other. -/
theorem ce_differ :
    ((reduceProgram Btest ceA).toOption.map (·.flagsType)) = some .int ∧
    ((reduceProgram Btest ceA').toOption.map (·.flagsType)) = some .string := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The constructor `T` takes Int in the whole derivation of M1 and String in the split one. -/
theorem m1_constructors :
    (m1W.result Btest).map (fun (_, E) => E.VE) = some [("T", (mono (.fn tIntTy (.con [] tT)), .c))] ∧
    (m1S.result Btest).map (fun (_, E) => E.VE) = some [("T", (mono (.fn tStringTy (.con [] tT)), .c))] := by
  decide +kernel

/-! ## The two derivations of M1 are instances of each other -/

theorem instanceNodes_of_paths {ns' ns : List Node}
    (hd : (ns.flatMap (·.tys)).all (fun τ => (Subst.id.apply τ).isSome) = true)
    (hp : ∀ p ∈ ns.map (·.path), p ∉ ns'.map (·.path)) : InstanceNodes [] ns' ns := by
  refine ⟨Subst.id, ?_, ?_, ?_, ?_⟩
  · intro p hp; simp [Subst.id] at hp
  · intro v hv; simp [Subst.dom, Subst.id] at hv
  · intro τ hτ; exact List.all_eq_true.mp hd τ hτ
  · intro n hn n' hn' e
    exact absurd (e ▸ List.mem_map_of_mem (f := (·.path)) hn') (hp _ (List.mem_map_of_mem (f := (·.path)) hn))

set_option maxRecDepth 100000 in
theorem m1_paths : (nodesModule Btest m1W).map (·.path) = [[]] ∧
    (nodesModule Btest m1S).map (·.path) = [[0], [1]] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem m1_genNames : genNames Btest m1W = [tT] ∧ genNames Btest m1S = [tT] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem m1_defined :
    (((nodesModule Btest m1W).map (Node.renameNames [(tT, tT)])).flatMap (·.tys)).all
      (fun τ => (Subst.id.apply τ).isSome) = true ∧
    (((nodesModule Btest m1S).map (Node.renameNames [(tT, tT)])).flatMap (·.tys)).all
      (fun τ => (Subst.id.apply τ).isSome) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem m1_erase : m1S.erase = m1W.erase := by decide +kernel

theorem bij_tT : Bijective [(tT, tT)] [tT] [tT] :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, by decide, by decide⟩

theorem renameNames_path (ρ : List (TyName × TyName)) (ns : List Node) :
    (ns.map (Node.renameNames ρ)).map (·.path) = ns.map (·.path) := by
  simp [Node.renameNames]

/-- Each derivation of M1 is an instance of the other. -/
theorem m1_mutual : InstanceOfMod Btest m1S m1W ∧ InstanceOfMod Btest m1W m1S := by
  obtain ⟨pW, pS⟩ := m1_paths
  obtain ⟨gW, gS⟩ := m1_genNames
  refine ⟨⟨m1_erase, [(tT, tT)], by rw [gW, gS]; exact bij_tT, instanceNodes_of_paths m1_defined.1 ?_⟩,
    ⟨m1_erase.symm, [(tT, tT)], by rw [gW, gS]; exact bij_tT, instanceNodes_of_paths m1_defined.2 ?_⟩⟩
  · rw [renameNames_path, pW, pS]; decide
  · rw [renameNames_path, pW, pS]; decide

end SplitCE

end StandardElm.Stat
