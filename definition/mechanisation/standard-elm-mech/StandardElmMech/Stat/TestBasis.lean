/-
  A Standard Definition of Elm? Mechanisation: the static half of the test basis, plan step 9
  (section 6, decision D2, G2-14). `B0stat` is the initial static basis of Appendix C; `Btest` adds
  the harness's `text` to Html (D2 (a)) and the core library values the tests use (D2 (b)).

  A library value enters its module's interface at the scheme its elm/core 1.0.5 (or elm/json
  1.1.3) annotation elaborates to (Generated/StaticLibrary.lean), in the context of the default
  imports and the module's own types. Every library module the tests use is in ME0, and its own
  types are ME0's (Array is tArray, Json.Encode.Value is tValue), so the library adds no type name.
-/
import StandardElmMech.Stat.Infer
import StandardElmMech.Generated.StaticLibrary
import StandardElmMech.Src.Derive

namespace StandardElm.Stat
open StandardElm (Var ModId)

def B0stat : SBasis := ⟨T0, ME0, []⟩

/-- D2 (a): ME0(Html) with `text : String -> Html msg`, that is ∀msg. String → msg Node. -/
def harnessHtml : IEnv :=
  { I_Html with VE := [("text", (⟨[.ty (.bnd 0 .any)], .fn tStringTy (.con [.var (.bnd 0 .any)] tNode)⟩, .v))] }

/-- The harness basis: B0 with the harness's Html. -/
def Bharness : SBasis := ⟨T0, FMap.modify ME0 [("Html", harnessHtml)], []⟩

/-- The context a library module's annotations elaborate in: the default imports, and the module's
    own types (its interface in ME0). -/
def libCtx (M : ModId) : Option Ctx :=
  (importCtx B0stat []).map fun C => C.oplusTE (((FMap.find? ME0 M).map (·.TE)).getD [])

/-- A library value at the scheme its annotation elaborates to: ∀U'.τ with U' the annotation's
    variables (G2-5). -/
def libValue (C : Ctx) (v : Var × Src.STy) : Option (String × (Scheme × IdStatus)) :=
  let ty := Src.deriveTy v.2
  let U' := annVars [] ty
  (elabTy (C.plusU U') ty).map fun τ => (v.1, (annScheme U' τ, .v))

/-- The interface of a library module: ME0's, with the library values added. -/
def libInterface (M : ModId) (vals : List (Var × Src.STy)) : IEnv :=
  let I0 := (FMap.find? ME0 M).getD IEnv.empty
  let C := (libCtx M).getD default
  { I0 with VE := FMap.modify I0.VE (vals.filterMap (libValue C)) }

def libInterfaces : ModEnv := libModules.map fun (M, vals) => (M, libInterface M vals)

/-- The modules of the library values. -/
def libModuleIds : List ModId := libModules.map (·.1)

/-- D2: the test basis. -/
def Btest : SBasis := ⟨T0, FMap.modify (FMap.modify ME0 [("Html", harnessHtml)]) libInterfaces, []⟩

end StandardElm.Stat
