/-
  A Standard Definition of Elm? Mechanisation: algorithm W for modules and programs (milestone (f)
  of plan step 11, section 6, "Modules").

  * Imports, exposing lists and the header: step 9's deterministic functions (`importCtx`, and the
    final `checkModule`). Imports that do not elaborate give `unsupported`, not `fail`: they are
    step 9's deterministic refusal (`importsFailB`), and a test that needs a module outside the
    test basis (basis `outside`) is not a type error.
  * The type declarations (`r:sm-topdec-types`; ruling A98: they are one phrase at the head of the
    body, never split): `solveTypes` gives each custom type a new type name above every name of
    `T of C`, elaborates the aliases in Appendix A's order, each in the context of the custom types
    and the earlier aliases, then every alias and constructor in that context; the result is kept
    only when step 9's `checkTypes` accepts it (it is then a solution of the rule's premises) and
    the phrase is ordered (`typesOrdered`: what makes the solution unique up to the names).
  * The value declarations: the module's top-level groups are elaborated as one expression, the
    nested `let` of the groups in order (`bodyExp`): the context of a top-level group is its
    predecessor's extended by the closed environment of the predecessor, exactly as for a `let`
    body (`r:sm-topdec-seq` with `r:sm-topdec-value`, and `r:s-atexp-let` with `r:s-dec-group`).
    So W for the expression (`WE.inferExpWD`, milestone (e)) is W for the declarations, in the
    context the type declarations give, which has no free type variable.
  * A port `port x : ty` (milestone (g)) is elaborated as the annotated group `x : ty; x = x` in the
    nested `let` (`portVB`): its type is the annotation's, closed as the port rule closes it. Its
    node in the module is the port rule's, which no derivation can choose differently (`newForB`
    fixes U, and the type is the annotation's), so W keeps it only when the group's closed
    environment is the port rule's and the node's variables are `bnd` or named (`portsOKB`), which
    an instance must leave alone. When W fails on a module with a port, it answers `unsupported`:
    refutation is not claimed for such modules (no test needs it).

  `inferModuleW` returns the annotated module rebuilt from W's derivation of the expression
  (`unLet`), after step 9's checker accepts it (`internal` otherwise). `inferProgramW` runs the
  modules in order, each in the basis `r:p-stat-module` builds from the results of the earlier ones.
-/
import StandardElmMech.Stat.Complete.WE
import StandardElmMech.Stat.Ident

namespace StandardElm.Stat.Complete
namespace MW
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtExp BExp BDec BValBind BTopDec BModule BProgram BDatBind BTypBind)

/-! ## Type declarations -/

/-- The largest identity of a list of type names. -/
def maxTyId : List TyName → Nat
  | [] => 0
  | t :: ts => max t.id (maxTyId ts)

/-- The custom types with new names, above every name of `T` (their constructors not yet
    elaborated: type expressions read only the type function of a type name). -/
def custTE (T : List TyName) (d : BDatBind) : TyEnv :=
  (d.zipIdx).map fun (e, i) => (e.1, ((TyName.mk (maxTyId T + 1 + i) e.2.1.length).toFcn, []))

/-- The aliases in order, each elaborated in the context of what comes before it. -/
def solveAliases (C : Ctx) : TyEnv → List BTypBind → Option TyEnv
  | TE, [] => some TE
  | TE, tb :: tbs =>
    match elabTypBind (C.oplusTE TE) tb with
    | some (_, TE1) => solveAliases C (FMap.modify TE TE1) tbs
    | none => none

/-- r:sm-topdec-types by Appendix A's order (section 6): a candidate solution, which `typesW`
    keeps only if step 9's `checkTypes` accepts it. -/
def solveTypes (C : Ctx) (db : Option BDatBind) (tbs : List BTypBind) : Option (TyEnv × ValEnv) :=
  let TE0 := match db with
    | some d => custTE C.T d
    | none => []
  match solveAliases C TE0 tbs with
  | none => none
  | some TEa =>
    let Cte := C.oplusTE TEa
    match elabTypBinds Cte tbs with
    | none => none
    | some (VEs, TEs) =>
      match db with
      | none => some (FMap.plusAll TEs, FMap.plusAll VEs)
      | some d =>
        match elabDatBind Cte (namesOf TEa) d with
        | some (VE', TE') => some (FMap.modify TE' (FMap.plusAll TEs), FMap.modify VE' (FMap.plusAll VEs))
        | none => none

/-- Every variable of the types and schemes of a type declaration's node is `bnd` (the parameters of
    its type functions, the bound variables of its closed schemes). -/
def typesBndB (TE : TyEnv) (VE : ValEnv) : Bool :=
  (TE.map (·.2.1.body)).all (fun τ => τ.vars.all BVar.isBnd) &&
    (veSchemes VE).all fun σ => σ.body.vars.all BVar.isBnd

/-- The type declarations of a module in `C`: their environment, when `solveTypes` finds one that
    step 9's checker accepts, the phrase is ordered, and the node's variables are `bnd`. -/
def typesW (C : Ctx) (db : Option BDatBind) (tbs : List BTypBind) : Option (TyEnv × ValEnv) :=
  match solveTypes C db tbs with
  | some (TE, VE) =>
    if checkTypes C TE VE db tbs && typesOrdered db tbs && typesBndB TE VE then some (TE, VE) else none
  | none => none

/-- A body as its type declarations (at its head, Appendix A) and the rest. -/
def splitBody : BTopDec → Option (Option BDatBind × List BTypBind) × Option BTopDec
  | .types db tbs => (some (db, tbs), none)
  | .seq (.types db tbs) rest => (some (db, tbs), some rest)
  | .seq (.value vb) rest => (none, some (.seq (.value vb) rest))
  | .seq (.port x t) rest => (none, some (.seq (.port x t) rest))
  | .seq (.seq a b) rest => (none, some (.seq (.seq a b) rest))
  | .value vb => (none, some (.value vb))
  | .port x t => (none, some (.port x t))

/-! ## Value declarations as one expression -/

/-- A port as the annotated group `x : ty; x = x`. -/
def portVB (x : Var) (t : BTy) : BValBind := .var x (some t) (.atexp (.var ⟨none, x⟩)) none

/-- The top-level groups and ports `d1; ...; dn` as `let d1 in ... let dn in ()`; none for anything
    else (type declarations not at the head). -/
def bodyExp : BTopDec → Option BExp
  | .value vb => some (.atexp (.letE (.val vb) (.atexp .unit)))
  | .port x t => some (.atexp (.letE (.val (portVB x t)) (.atexp .unit)))
  | .seq (.value vb) rest => (bodyExp rest).map fun e => .atexp (.letE (.val vb) e)
  | .seq (.port x t) rest => (bodyExp rest).map fun e => .atexp (.letE (.val (portVB x t)) e)
  | _ => none

/-- A body with a port. -/
def hasPortB : BTopDec → Bool
  | .port _ _ => true
  | .seq a b => hasPortB a || hasPortB b
  | _ => false

/-- The declaration of a nested `let` and its body (a template for the encoding of ports). -/
def tmplDec : AExp → Option ADec
  | .atexp (.letE d _) => some d
  | _ => none

def tmplBody : AExp → AExp
  | .atexp (.letE _ e) => e
  | e => e

/-- The annotated nested `let` of annotated top-level groups and ports, a port's group taken from the
    template `t` (W's derivation). -/
def toExpA : ATopDec → AExp → Option AExp
  | .value VE vb, _ => some (.atexp (.letE (.val VE vb) (.atexp .unit)))
  | .port _ _ _, t => (tmplDec t).map fun d => .atexp (.letE d (.atexp .unit))
  | .seq (.value VE vb) rest, t => (toExpA rest (tmplBody t)).map fun e => .atexp (.letE (.val VE vb) e)
  | .seq (.port _ _ _) rest, t =>
    match tmplDec t with
    | some d => (toExpA rest (tmplBody t)).map fun e => .atexp (.letE d e)
    | none => none
  | _, _ => none

def isUnitE : AExp → Bool
  | .atexp .unit => true
  | _ => false

/-- The explicit variables of an annotated binding. -/
def annUOf : AValBind → List BVar
  | .var _ ann _ _ _ => annU ann
  | .pat _ _ => []

/-- The declarations of an annotated nested `let` (W's derivation of `bodyExp r`), read along `r`. -/
def unLet : BTopDec → AExp → Option ATopDec
  | .value _, .atexp (.letE (.val VE vb) e) => if isUnitE e then some (.value VE vb) else none
  | .port x t, .atexp (.letE (.val _ vb) e) => if isUnitE e then some (.port x t (annUOf vb)) else none
  | .seq (.value _) r, .atexp (.letE (.val VE vb) e) => (unLet r e).map (.seq (.value VE vb))
  | .seq (.port x t) r, .atexp (.letE (.val _ vb) e) => (unLet r e).map (.seq (.port x t (annUOf vb)))
  | _, _ => none

/-- A variable a substitution of an instance must leave alone: `bnd` or named. -/
def rigidB : BVar → Bool
  | .ty (.fresh _ _) | .row (.fresh _) => false
  | _ => true

/-- The variables of a port's node (r:sm-topdec-portout, r:sm-topdec-portin). -/
def portNodeVars (E : Env) (PE : PortEnv) (U : List BVar) : List BVar :=
  U ++ (PE.map (·.2.2)).flatMap Ty.vars ++ (veSchemes E.VE).flatMap (·.body.vars)

/-- W's group for the port `x : ty` is `x : ty; x = x`, its closed environment is the port rule's,
    and the port's node has `bnd` and named variables only. -/
def portOKB (Cp : Ctx) (x : Var) (ty : BTy) : Option ADec → Bool
  | some (.val VE (.var x' (some (ty', U)) _ (.atexp (.var lv _ _)) none)) =>
    decide (x' = x) && decide (ty' = ty) && decide (lv = ⟨none, x⟩) &&
      match elabPort Cp x ty U with
      | some (E, PE) => decide (closGroup [] VE = E.VE) && (portNodeVars E PE U).all rigidB
      | none => false
  | _ => false

/-- `portOKB` at every port of the body, against the template. -/
def portsOKB (Cp : Ctx) : BTopDec → AExp → Bool
  | .port x ty, t => portOKB Cp x ty (tmplDec t)
  | .seq (.port x ty) r, t => portOKB Cp x ty (tmplDec t) && portsOKB Cp r (tmplBody t)
  | .seq _ r, t => portsOKB Cp r (tmplBody t)
  | _, _ => true

/-- The variables of the ports' nodes, which the instance leaves alone. -/
def portsVars (Cp : Ctx) : ATopDec → List BVar
  | .port x ty U =>
    match elabPort Cp x ty U with
    | some (E, PE) => portNodeVars E PE U
    | none => []
  | .seq a b => portsVars Cp a ++ portsVars Cp b
  | _ => []

/-! ## The root context -/

/-- A scheme as `RootOKD` asks: its bound variables are `bnd`, its free ones are not. -/
def schemeOKB (σ : Scheme) : Bool :=
  σ.bound.all BVar.isBnd && σ.body.vars.all fun v => decide (v ∈ σ.bound) || !v.isBnd

/-- Every scheme a lookup can give is `schemeOKB` (decides `RootOKD`). -/
def rootOKB (C : Ctx) : Bool :=
  C.E.VE.all (fun p => schemeOKB p.2.1) && C.E.QE.all fun q => q.2.VE.all fun p => schemeOKB p.2.1

/-! ## Modules and programs -/

inductive MRes where
  | ok (a : AModule)
  | fail
  | unsupported
  | outOfFuel
  | internal

def MRes.isFail : MRes → Bool
  | .fail => true
  | _ => false

def MRes.isOk : MRes → Bool
  | .ok _ => true
  | _ => false

/-- The annotated body from the type declarations' node and the value declarations'. -/
def joinBody : Option ATopDec → Option ATopDec → Option ATopDec
  | some t, some v => some (.seq t v)
  | some t, none => some t
  | none, v => v

/-- Every type name at a node of a module's derivation is a name of the basis or one of the
    module's custom types. -/
def namesB (B : SBasis) (a : AModule) : Bool :=
  let ok : TyName → Bool := fun t => decide (t ∈ B.T) || decide (t ∈ genNames B a)
  (nodesModule B a).all fun n =>
    n.tys.all (fun τ => τ.tynames.all ok) && n.schemes.all fun σ => σ.body.tynames.all ok

/-- W's answer for an annotated module: accepted by step 9's checker, with the type names of its
    nodes known (`namesB`), or `internal`. -/
def finish (B : SBasis) (a : AModule) : MRes := if checkModule B a && namesB B a then .ok a else .internal

/-- The type declarations' node and the context of the value declarations. -/
def typesPart (C : Ctx) : Option (Option BDatBind × List BTypBind) → Option (Option ATopDec × Ctx)
  | none => some (none, C)
  | some (db, tbs) =>
    match typesW C db tbs with
    | some (TE, VE) => some (some (.types TE VE db tbs), C.oplusE ⟨[], TE, VE⟩)
    | none => none

/-- The value declarations and ports, in the context `C1` the type declarations give, by W for the
    nested `let`; the module rebuilt from W's derivation. -/
def valuesW (fuel : Nat) (B : SBasis) (m : BModule) (at? : Option ATopDec) (C1 : Ctx) :
    Option BTopDec → MRes
  | none => finish B ⟨m.header, m.imports, joinBody at? none⟩
  | some r =>
    match bodyExp r with
    | none => .unsupported
    | some e =>
      if rootOKB C1 then
        match WE.inferExpWD fuel C1 e with
        | .ok ae =>
          match unLet r ae with
          | some av =>
            if portsOKB C1 r ae then finish B ⟨m.header, m.imports, joinBody at? (some av)⟩ else .unsupported
          | none => .internal
        | .fail => if hasPortB r then .unsupported else .fail
        | .unsupported => .unsupported
        | .outOfFuel => .outOfFuel
        | .internal => .internal
      else .unsupported

/-- W for a module in a basis (r:sm-module). -/
def inferModuleW (fuel : Nat) (B : SBasis) (m : BModule) : MRes :=
  match importCtx B m.imports with
  | none => .unsupported
  | some C =>
    match m.body with
    | none => finish B ⟨m.header, m.imports, none⟩
    | some d =>
      match typesPart C (splitBody d).1 with
      | none => .unsupported
      | some (at?, C1) => valuesW fuel B m at? C1 (splitBody d).2

/-- What W gives a program. -/
inductive PRes where
  | ok (as : AProgram)
  | fail
  | other

/-- W for a program (r:p-stat-module): the modules in order, each in the basis the earlier ones
    build; the first module W does not elaborate decides the outcome. -/
def inferProgramW (fuel : Nat) : SBasis → List BModule → PRes
  | _, [] => .ok []
  | B, m :: ms =>
    match inferModuleW fuel B m with
    | .ok a =>
      match a.result B with
      | some (B', _) =>
        match inferProgramW fuel (B.plus B') ms with
        | .ok as => .ok (a :: as)
        | r => r
      | none => .other
    | .fail => .fail
    | _ => .other

/-- The fuel of W at the module level (W's own, `wdFuel`). -/
def wFuel : Nat := wdFuel

/-- Refutation by W: W fails on a module of the program, in the basis the earlier ones build. -/
def wRefutes (B : SBasis) (sp : Src.SProgram) : Bool :=
  match inferProgramW wFuel B (Src.deriveProgram (Src.canonOrder sp)).modules with
  | .fail => true
  | _ => false

end MW
end StandardElm.Stat.Complete
