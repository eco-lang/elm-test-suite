/-
  A Standard Definition of Elm? Mechanisation: the end-to-end pipeline, plan step 10 (Lean
  definitions, "The pipeline").

  From a source program: step 8's derived forms of its canonical order (`bareOf`), step 9's
  inference, its checker (each module in the basis the earlier ones build, run once: `progResults`),
  the side conditions of r:p-stat-* (`checksAll`), and the specialisation and erasure of the
  annotated program to Part I's reduced program (`reduceWith`). Every definition here is
  structurally recursive, so that `decide +kernel` runs `endToEnd`.
-/
import StandardElmMech.Stat.Specialise
import StandardElmMech.Stat.Legal

namespace StandardElm.Stat
open StandardElm (Var Lab ModId)
open StandardElm.Src (BImport BHeader BModule BProgram SProgram)

/-! ## The modules' results, computed once -/

/-- What r:sm-module gives each module, in the basis the earlier ones build (r:p-stat-module):
    the basis B_i, the module's B'_i and E_i; none when a module does not check. -/
def progResults (B : SBasis) : AProgram → Option (List (SBasis × SBasis × Env))
  | [] => some []
  | m :: rest =>
    match m.result B with
    | some (B', E) => (progResults (B.plus B') rest).map ((B, B', E) :: ·)
    | none => none

theorem progResults_isSome (B : SBasis) (a : AProgram) :
    (progResults B a).isSome = checkProgram B a := by
  unfold checkProgram
  induction a generalizing B with
  | nil => rfl
  | cons m rest ih =>
    simp only [progResults, AProgram.bases]
    split <;> simp_all [Option.isSome_map]

/-! ## The modules of the program, specialised -/

/-- What a module contributes before its specialised definitions are known. -/
structure ModInfo where
  header : BHeader
  imports : List BImport
  items : List TopItem
  groups : List TopGroup
  PE : PortEnv
  prov : ProvMap

/-- The modules with their top-level groups numbered from `n` (modules in order). -/
def modInfos : Nat → AProgram → List (SBasis × SBasis × Env) → List ModInfo
  | n, m :: ms, (Bi, B'i, _) :: rs =>
    let items := (m.body.map ATopDec.items).getD []
    let gs := topGroupsFrom n items
    let π := (elabImports Bi π0 (defaultImports ++ m.imports)).getD []
    ⟨m.header, m.imports, items, gs, B'i.PE, π⟩ :: modInfos (n + gs.length) ms rs
  | _, _, _ => []

/-- The references to the top-level groups with number variables of a module, from other modules. -/
def ModInfo.globals (mi : ModInfo) : List ((ModId × Var) × Ref) :=
  mi.groups.flatMap fun G =>
    if G.V.isEmpty then []
    else G.view.members.map fun m => ((mi.header.name, m.x), Ref.group G.gid G.V m.body (m.bOutAll G.V))

/-- The modules last to first, so that every request on module i is known before module i is
    specialised (a module imports only earlier modules, res:program-import-order). `glob` holds the
    references to the groups of the modules before the first of the list. -/
def specMods (B : SBasis) (T : Nat) (glob : List ((ModId × Var) × Ref)) :
    List ModInfo → Except SpecError (List (List (List (Assignment × List D.Def))) × List Req)
  | [] => .ok ([], [])
  | mi :: rest => do
    let (later, inc) ← specMods B T (glob ++ mi.globals) rest
    let Γ : Scope := ⟨[], mi.groups.flatMap TopGroup.refsOut, glob ++ basisRefs B, mi.prov⟩
    let (made, out) ← specTop Γ T mi.groups inc
    pure (made :: later, out)

/-- The copy table of a module: each copied top-level variable with the variables of its copies. -/
def ModInfo.copies (mi : ModInfo) (mades : List (List (Assignment × List D.Def))) :
    List (Var × List Var) :=
  (mi.groups.zip mades).flatMap fun (G, made) => copyTable G made

def lookupCopies (B : SBasis) (tables : List (ModId × List (Var × List Var))) (m : ModId) (x : Var) :
    Option (List Var) :=
  match tables.lookup m with
  | some t => t.lookup x
  | none => basisCopyNames B m x

def portsOf (PE : PortEnv) : List TopItem → Except SpecError (List (Var × Mod.Dir × Eff.PTy))
  | [] => .ok []
  | .port x :: rest => do
    let p ← match erasePort PE x with
      | some p => Except.ok p
      | none => Except.error SpecError.portType
    let ps ← portsOf PE rest
    pure (p :: ps)
  | _ :: rest => portsOf PE rest

/-- Custom types to their constructors with arities, aliases to their record labels in the order
    written (spec: `eraseTypeDecs`). -/
def eraseTypeDecs : List TopItem → List (Mod.TyCon × List Con) × List Mod.TypBind
  | [] => ([], [])
  | .types db tbs :: rest =>
    let (ts, as) := eraseTypeDecs rest
    (eraseDatBind db ++ ts, eraseTypBinds tbs ++ as)
  | _ :: rest => eraseTypeDecs rest

def BImport.toMod (copies : ModId → Var → Option (List Var)) (i : BImport) : Mod.Import :=
  ⟨i.mod, i.alias.getD i.mod, i.exposing.map (expandItems (copies i.mod))⟩

/-- A module of the reduced program, built by step 3's `Mod.Module.ofSource` from its specialised
    items (Choices, item 1): custom types and aliases by name, ports in order, the definitions of
    the copies of its top-level groups in group order. -/
def buildModule (B : SBasis) (tables : List (ModId × List (Var × List Var))) (mi : ModInfo)
    (mades : List (List (Assignment × List D.Def))) : Except SpecError Mod.Module := do
  let own := mi.copies mades
  let (types, aliases) := eraseTypeDecs mi.items
  let ports ← portsOf mi.PE mi.items
  let h : Mod.Header := ⟨mi.header.isPort, mi.header.name, expandItems (fun x => own.lookup x) mi.header.exposing⟩
  let imps := mi.imports.map (BImport.toMod (lookupCopies B tables))
  let defs := mades.flatMap emitCopies
  match Mod.Module.ofSource h imps (sortByName (·.1) types) (sortByName (·.tycon) aliases) ports defs with
  | some m => .ok m
  | none => .error (.noModule mi.header.name)

def buildModules (B : SBasis) : List (ModId × List (Var × List Var)) → List ModInfo →
    List (List (List (Assignment × List D.Def))) → Except SpecError (List Mod.Module)
  | tables, mi :: mis, md :: mds => do
    let m ← buildModule B tables mi md
    let ms ← buildModules B ((mi.header.name, mi.copies md) :: tables) mis mds
    pure (m :: ms)
  | _, _, _ => .ok []

/-- The program's modules, specialised and erased (spec: `specProgram`): the copies of every
    top-level group (modules last to first), then each module built with the copy tables of the
    modules before it. -/
def specProgram (B : SBasis) (a : AProgram) (rs : List (SBasis × SBasis × Env)) :
    Except SpecError (List Mod.Module) := do
  let mis := modInfos 0 a rs
  let T := (mis.map (·.groups.length)).sum
  let (mades, left) ← specMods B T [] mis
  unless left.isEmpty do throw (.unresolved "a request for a copy of no group")
  buildModules B [] mis mades

/-- The scheme of `main` in the last module's environment. -/
def mainScheme : List (SBasis × SBasis × Env) → Option Scheme
  | [] => none
  | [(_, _, E)] =>
    match E.VE.find? "main" with
    | some (σ, .v) => some σ
    | _ => none
  | _ :: rest => mainScheme rest

/-- Specialisation and erasure of a whole program, given the results of its modules: the reduced
    modules, the port environment they declare, the flags type and the kind. -/
def reduceWith (B : SBasis) (a : AProgram) (rs : List (SBasis × SBasis × Env)) :
    Except SpecError Mod.Reduced := do
  let ms ← specProgram B a rs
  match (mainScheme rs).bind mainKind with
  | some (k, flags) => pure (.ofModules ms flags k)
  | none => throw .mainShape

/-- Specialisation and erasure of a whole program (spec: `reduceProgram`); the basis is the one
    the program elaborates in. -/
def reduceProgram (B : SBasis) (a : AProgram) : Except SpecError Mod.Reduced :=
  match progResults B a with
  | some rs => reduceWith B a rs
  | none => .error (.unresolved "a module that does not check")

/-! ## The pipeline -/

inductive E2EError where
  | infer (e : String) | check | spec (e : SpecError)
  deriving DecidableEq, Repr

instance : DecidableEq (Except E2EError Mod.Reduced) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    if h : x = y then Decidable.isTrue (by rw [h]) else Decidable.isFalse (by intro e; cases e; exact h rfl)
  | .error x, .error y =>
    if h : x = y then Decidable.isTrue (by rw [h]) else Decidable.isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => Decidable.isFalse (by intro e; cases e)
  | .error _, .ok _ => Decidable.isFalse (by intro e; cases e)

/-- The side conditions of r:p-stat-* that the checker of modules does not check: the port names
    of each module distinct from the earlier modules' and from the platform's managers, and the
    scheme of the last module's `main` that of a worker or a view. -/
def checksAll (rs : List (SBasis × SBasis × Env)) : Bool :=
  rs.all (fun (Bi, B'i, _) => portsDisjointB Bi B'i) && ((mainScheme rs).bind mainKind).isSome

/-- The bare program of a source program: step 8's derived forms of its canonical order (the
    program on which step 9 states legality). -/
def bareOf (s : SProgram) : BProgram := Src.deriveProgram (Src.canonOrder s)

/-- derive (total, step 8), infer, check, reduce. -/
def endToEnd (B : SBasis) (s : SProgram) : Except E2EError Mod.Reduced := do
  let p := bareOf s
  let a ← (inferProgram B p).mapError .infer
  match progResults B a with
  | none => throw .check
  | some rs =>
    unless a.map AModule.erase == p.modules && checksAll rs do throw .check
    (reduceWith B a rs).mapError .spec

end StandardElm.Stat
