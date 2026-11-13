/-
  A Standard Definition of Elm? Mechanisation: annotated phrases and the checker, plan step 9
  (section 7, decision D10).

  An annotated phrase is a bare phrase with the semantic objects of a derivation's sentences: the
  type at each leaf and binder (a constant, an occurrence, `[]`, a pattern variable, a wildcard, a
  record pattern), the instance (the types for the scheme's bound variables) at each occurrence of
  a variable, constructor or operator, the group's value environment before closure at each
  declaration, U' at each annotated binding, and, in modules, the type environment of the type
  declarations (with its generated type names) and the U of each port. (Step 9 also had a node
  for r:sm-topdec-seq splitting a type-declaration phrase; the book no longer allows that split,
  decision of 2026-11-12, option (c) of step 10's issue 9, so the node is gone.) The other types (of applications, lambdas, tuples, matches, rows and value
  environments of patterns) are computed from the nodes (`ty`, `ve`, `row`), so a certificate
  stores only what a derivation chooses. Imports, headers, type expressions and type declarations
  given their names are computed by Deterministic.lean.

  `checkExpS C a` checks at each node the premises of the one rule whose conclusion has the node's
  form; it is structurally recursive, so `decide +kernel` runs it. The checker `checkExp C a` asks
  besides that every type at a node of the derivation (`nodesExp`, the types of its sentences) be
  `Ty.okB`: its rows canonical, so that rows are the book's finite maps (A23: the substitution of a
  row variable then refuses every shared label), and no `bnd` variable free (those are the bound
  variables of canonical schemes, Objects.lean). A value declaration of a module is checked the
  same way. The derivations the checker accepts are then exactly the book's (with step 11's
  findings: the restrictions `NoFreeBndExp`, `CanonExp` of Complete/ are consequences of it).
  CheckSound.lean proves it sound.
-/
import StandardElmMech.Stat.Deterministic

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  SLit BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule)

/-! ## Annotated patterns -/

mutual
inductive AAtPat where
  | wild (τ : Ty)
  | scon (sc : SLit) (τ : Ty)
  | var (x : Var) (τ : Ty)
  | con (lc : LongId) (inst : List Ty) (τ : Ty)
  | unit
  | tuple (p1 p2 : APat) (p3 : Option APat)
  | nil (τ : Ty)
  | record (row : Option APatRow) (τ : Ty)
  | paren (p : APat)
inductive APatRow where
  | field (l : Lab) (τ : Ty) (rest : Option APatRow)
inductive APat where
  | atpat (a : AAtPat)
  | con (lc : LongId) (inst : List Ty) (args : List AAtPat) (τ : Ty)
  | cons (p1 p2 : APat)
  | as (p : APat) (x : Var)
end

instance : Inhabited APat := ⟨.atpat .unit⟩
instance : Inhabited AAtPat := ⟨.unit⟩

mutual
def AAtPat.erase : AAtPat → BAtPat
  | .wild _ => .wild
  | .scon sc _ => .scon sc
  | .var x _ => .var x
  | .con lc _ _ => .con lc
  | .unit => .unit
  | .tuple p1 p2 p3 => .tuple (APat.erase p1) (APat.erase p2) (APat.eraseOpt p3)
  | .nil _ => .nil
  | .record row _ => .record (APatRow.eraseOpt row)
  | .paren p => .paren (APat.erase p)
def APatRow.erase : APatRow → BPatRow
  | .field l _ rest => .field l (APatRow.eraseOpt rest)
def APatRow.eraseOpt : Option APatRow → Option BPatRow
  | none => none
  | some r => some (APatRow.erase r)
def APat.erase : APat → BPat
  | .atpat a => .atpat (AAtPat.erase a)
  | .con lc _ args _ => .con lc (AAtPat.eraseList args)
  | .cons p1 p2 => .cons (APat.erase p1) (APat.erase p2)
  | .as p x => .as (APat.erase p) x
def APat.eraseOpt : Option APat → Option BPat
  | none => none
  | some p => some (APat.erase p)
def AAtPat.eraseList : List AAtPat → List BAtPat
  | [] => []
  | a :: as => AAtPat.erase a :: AAtPat.eraseList as
end

mutual
def AAtPat.ty : AAtPat → Ty
  | .wild τ | .scon _ τ | .var _ τ | .con _ _ τ | .nil τ | .record _ τ => τ
  | .unit => tUnitTy
  | .tuple p1 p2 p3 => tupleTy (APat.ty p1) (APat.ty p2) (APat.tyOpt p3)
  | .paren p => APat.ty p
def APat.ty : APat → Ty
  | .atpat a => AAtPat.ty a
  | .con _ _ _ τ => τ
  | .cons p1 _ => listTy (APat.ty p1)
  | .as p _ => APat.ty p
def APat.tyOpt : Option APat → Option Ty
  | none => none
  | some p => some (APat.ty p)
end

def AAtPat.tyList : List AAtPat → List Ty
  | [] => []
  | a :: as => a.ty :: AAtPat.tyList as

mutual
def AAtPat.ve : AAtPat → ValEnv
  | .var x τ => [(x, (mono τ, .v))]
  | .tuple p1 p2 p3 => FMap.modify (FMap.modify (APat.ve p1) (APat.ve p2)) (APat.veOpt p3)
  | .record row _ => APatRow.veOpt row
  | .paren p => APat.ve p
  | _ => []
def APatRow.ve : APatRow → ValEnv
  | .field l τ rest => FMap.modify [(l, (mono τ, .v))] (APatRow.veOpt rest)
def APatRow.veOpt : Option APatRow → ValEnv
  | none => []
  | some r => APatRow.ve r
def APat.ve : APat → ValEnv
  | .atpat a => AAtPat.ve a
  | .con _ _ args _ => FMap.plusAll (AAtPat.veList args)
  | .cons p1 p2 => FMap.modify (APat.ve p1) (APat.ve p2)
  | .as p x => FMap.modify (APat.ve p) [(x, (mono (APat.ty p), .v))]
def APat.veOpt : Option APat → ValEnv
  | none => []
  | some p => APat.ve p
def AAtPat.veList : List AAtPat → List ValEnv
  | [] => []
  | a :: as => AAtPat.ve a :: AAtPat.veList as
end

mutual
def APatRow.row : APatRow → Row
  | .field l τ rest => Row.modify [(l, τ)] (APatRow.rowOpt rest)
def APatRow.rowOpt : Option APatRow → Row
  | none => []
  | some r => APatRow.row r
end

/-! ## Annotated expressions -/

mutual
inductive AAtExp where
  | scon (sc : SLit) (τ : Ty)
  | var (lv : LongId) (inst : List Ty) (τ : Ty)
  | con (lc : LongId) (inst : List Ty) (τ : Ty)
  | op (o : Op) (inst : List Ty) (τ : Ty)
  | unit
  | tuple (e1 e2 : AExp) (e3 : Option AExp)
  | nil (τ : Ty)
  | record (row : Option AExpRow)
  | update (x : Var) (inst : List Ty) (τ : Ty) (row : AExpRow)
  | letE (d : ADec) (e : AExp)
  | paren (e : AExp)
inductive AExpRow where
  | field (l : Lab) (e : AExp) (rest : Option AExpRow)
inductive AExp where
  | atexp (a : AAtExp)
  | app (e : AExp) (a : AAtExp)
  | lam (p : AAtPat) (e : AExp)
  | caseE (e : AExp) (m : AMatch)
inductive AMatch where
  | mk (mr : AMRule) (rest : Option AMatch)
inductive AMRule where
  | mk (p : APat) (e : AExp)
/-- A declaration: the group's value environment before closure, and its bindings. -/
inductive ADec where
  | val (VE : ValEnv) (vb : AValBind)
/-- `ann`: the annotation and its U'. -/
inductive AValBind where
  | var (x : Var) (ann : Option (BTy × List BVar)) (τ : Ty) (e : AExp) (rest : Option AValBind)
  | pat (p : AAtPat) (e : AExp)
end

instance : Inhabited AExp := ⟨.atexp .unit⟩
instance : Inhabited AAtExp := ⟨.unit⟩

mutual
def AAtExp.erase : AAtExp → BAtExp
  | .scon sc _ => .scon sc
  | .var lv _ _ => .var lv
  | .con lc _ _ => .con lc
  | .op o _ _ => .op o
  | .unit => .unit
  | .tuple e1 e2 e3 => .tuple (AExp.erase e1) (AExp.erase e2) (AExp.eraseOpt e3)
  | .nil _ => .nil
  | .record row => .record (AExpRow.eraseOpt row)
  | .update x _ _ row => .update x (AExpRow.erase row)
  | .letE d e => .letE (ADec.erase d) (AExp.erase e)
  | .paren e => .paren (AExp.erase e)
def AExpRow.erase : AExpRow → BExpRow
  | .field l e rest => .field l (AExp.erase e) (AExpRow.eraseOpt rest)
def AExpRow.eraseOpt : Option AExpRow → Option BExpRow
  | none => none
  | some r => some (AExpRow.erase r)
def AExp.erase : AExp → BExp
  | .atexp a => .atexp (AAtExp.erase a)
  | .app e a => .app (AExp.erase e) (AAtExp.erase a)
  | .lam p e => .lam p.erase (AExp.erase e)
  | .caseE e m => .caseE (AExp.erase e) (AMatch.erase m)
def AExp.eraseOpt : Option AExp → Option BExp
  | none => none
  | some e => some (AExp.erase e)
def AMatch.erase : AMatch → BMatch
  | .mk mr rest => .mk (AMRule.erase mr) (AMatch.eraseOpt rest)
def AMatch.eraseOpt : Option AMatch → Option BMatch
  | none => none
  | some m => some (AMatch.erase m)
def AMRule.erase : AMRule → BMRule
  | .mk p e => .mk p.erase (AExp.erase e)
def ADec.erase : ADec → BDec
  | .val _ vb => .val (AValBind.erase vb)
def AValBind.erase : AValBind → BValBind
  | .var x ann _ e rest => .var x (ann.map Prod.fst) (AExp.erase e) (AValBind.eraseOpt rest)
  | .pat p e => .pat p.erase (AExp.erase e)
def AValBind.eraseOpt : Option AValBind → Option BValBind
  | none => none
  | some vb => some (AValBind.erase vb)
end

/-- The codomain of a function type. -/
def Ty.cod : Ty → Ty
  | .fn _ τ => τ
  | τ => τ

mutual
def AAtExp.ty : AAtExp → Ty
  | .scon _ τ | .var _ _ τ | .con _ _ τ | .op _ _ τ | .nil τ | .update _ _ τ _ => τ
  | .unit => tUnitTy
  | .tuple e1 e2 e3 => tupleTy (AExp.ty e1) (AExp.ty e2) (AExp.tyOpt e3)
  | .record row => .record (AExpRow.rowOpt row) none
  | .letE _ e => AExp.ty e
  | .paren e => AExp.ty e
def AExpRow.row : AExpRow → Row
  | .field l e rest => Row.modify [(l, AExp.ty e)] (AExpRow.rowOpt rest)
def AExpRow.rowOpt : Option AExpRow → Row
  | none => []
  | some r => AExpRow.row r
def AExp.ty : AExp → Ty
  | .atexp a => AAtExp.ty a
  | .app e _ => (AExp.ty e).cod
  | .lam p e => .fn p.ty (AExp.ty e)
  | .caseE _ m => (AMatch.ty m).cod
def AExp.tyOpt : Option AExp → Option Ty
  | none => none
  | some e => some (AExp.ty e)
def AMatch.ty : AMatch → Ty
  | .mk mr _ => AMRule.ty mr
def AMRule.ty : AMRule → Ty
  | .mk p e => .fn p.ty (AExp.ty e)
end

def annU : Option (BTy × List BVar) → List BVar
  | none => []
  | some (_, U') => U'

/-- The value environment a value binding gives (its conclusion in r:s-valbind-var and r:s-valbind-pat). -/
def AValBind.ve : AValBind → ValEnv
  | .var x ann τ _ rest =>
    FMap.modify [(x, (if ann.isSome then annScheme (annU ann) τ else mono τ, .v))]
      (match rest with
       | none => []
       | some vb => AValBind.ve vb)
  | .pat p _ => p.ve

def AValBind.veOpt : Option AValBind → ValEnv
  | none => []
  | some vb => vb.ve

/-- What r:s-dec-group gives: the group's environment, closed. -/
def ADec.result (C : Ctx) : ADec → ValEnv
  | .val VE _ => closGroup C.tyvars VE

/-! ## Nodes -/

/-- A node of a derivation: the occurrence it is about (its path), the U of its context, and the
    types and type schemes of its sentence. At an occurrence of a variable, constructor or operator
    the sentence is `C ⊢ longvar ⇒ τ`: the instance chosen for the scheme's bound variables is a
    witness of the side condition `σ ≻ τ`, not a type of the sentence, and is not in the node
    (`Complete/InstCounter.lean`). -/
structure Node where
  path : List Nat
  U : List BVar
  tys : List Ty
  schemes : List Scheme
  deriving Inhabited

def veSchemes (VE : ValEnv) : List Scheme := VE.map (·.2.1)

mutual
def nodesAtPat (U : List BVar) (path : List Nat) : AAtPat → List Node
  | .tuple p1 p2 p3 => [⟨path, U, [tupleTy p1.ty p2.ty (APat.tyOpt p3)], veSchemes (AAtPat.tuple p1 p2 p3).ve⟩] ++
      nodesPat U (path ++ [0]) p1 ++ nodesPat U (path ++ [1]) p2 ++ nodesPatOpt U (path ++ [2]) p3
  | .record row τ => [⟨path, U, [τ], veSchemes (APatRow.veOpt row)⟩] ++ nodesPatRowOpt U (path ++ [0]) row
  | .paren p => [⟨path, U, [p.ty], veSchemes p.ve⟩] ++ nodesPat U (path ++ [0]) p
  | a => [⟨path, U, [a.ty] ++ a.ve.map (·.2.1.body), []⟩]
def nodesPatRow (U : List BVar) (path : List Nat) : APatRow → List Node
  | .field l τ rest => [⟨path, U, [τ] ++ (APatRow.row (.field l τ rest)).map (·.2), []⟩] ++ nodesPatRowOpt U (path ++ [0]) rest
def nodesPatRowOpt (U : List BVar) (path : List Nat) : Option APatRow → List Node
  | none => []
  | some r => nodesPatRow U path r
def nodesPat (U : List BVar) (path : List Nat) : APat → List Node
  | .atpat a => [⟨path, U, [a.ty], veSchemes a.ve⟩] ++ nodesAtPat U (path ++ [0]) a
  | .con lc inst args τ => [⟨path, U, [τ], veSchemes (APat.con lc inst args τ).ve⟩] ++
      nodesAtPats U path 0 args
  | .cons p1 p2 => [⟨path, U, [listTy p1.ty], veSchemes (APat.cons p1 p2).ve⟩] ++
      nodesPat U (path ++ [0]) p1 ++ nodesPat U (path ++ [1]) p2
  | .as p x => [⟨path, U, [p.ty], veSchemes (APat.as p x).ve⟩] ++ nodesPat U (path ++ [0]) p
def nodesPatOpt (U : List BVar) (path : List Nat) : Option APat → List Node
  | none => []
  | some p => nodesPat U path p
def nodesAtPats (U : List BVar) (path : List Nat) : Nat → List AAtPat → List Node
  | _, [] => []
  | i, a :: as => nodesAtPat U (path ++ [i]) a ++ nodesAtPats U path (i + 1) as
end

mutual
/-- The nodes of the derivation an annotated expression stands for, in context C, in preorder. -/
def nodesAtExp (C : Ctx) (path : List Nat) : AAtExp → List Node
  | .scon _ τ => [⟨path, C.U, [τ], []⟩]
  | .var _ _ τ => [⟨path, C.U, [τ], []⟩]
  | .con _ _ τ => [⟨path, C.U, [τ], []⟩]
  | .op _ _ τ => [⟨path, C.U, [τ], []⟩]
  | .unit => [⟨path, C.U, [tUnitTy], []⟩]
  | .tuple e1 e2 e3 => [⟨path, C.U, [(AAtExp.tuple e1 e2 e3).ty], []⟩] ++
      nodesExp C (path ++ [0]) e1 ++ nodesExp C (path ++ [1]) e2 ++ nodesExpOpt C (path ++ [2]) e3
  | .nil τ => [⟨path, C.U, [τ], []⟩]
  | .record row => [⟨path, C.U, [(AAtExp.record row).ty], []⟩] ++ nodesExpRowOpt C (path ++ [0]) row
  | .update _ _ τ row => [⟨path, C.U, [τ], []⟩] ++ nodesExpRow C (path ++ [0]) row
  | .letE d e => [⟨path, C.U, [e.ty], []⟩] ++ nodesDec C (path ++ [0]) d ++
      nodesExp (C.plusVE (d.result C)) (path ++ [1]) e
  | .paren e => [⟨path, C.U, [e.ty], []⟩] ++ nodesExp C (path ++ [0]) e
def nodesExpRow (C : Ctx) (path : List Nat) : AExpRow → List Node
  | .field l e rest => [⟨path, C.U, (AExpRow.field l e rest).row.map (·.2), []⟩] ++
      nodesExp C (path ++ [0]) e ++ nodesExpRowOpt C (path ++ [1]) rest
def nodesExpRowOpt (C : Ctx) (path : List Nat) : Option AExpRow → List Node
  | none => []
  | some r => nodesExpRow C path r
def nodesExp (C : Ctx) (path : List Nat) : AExp → List Node
  | .atexp a => [⟨path, C.U, [a.ty], []⟩] ++ nodesAtExp C (path ++ [0]) a
  | .app e a => [⟨path, C.U, [(AExp.app e a).ty], []⟩] ++ nodesExp C (path ++ [0]) e ++ nodesAtExp C (path ++ [1]) a
  | .lam p e => [⟨path, C.U, [(AExp.lam p e).ty], []⟩] ++ nodesAtPat C.U (path ++ [0]) p ++
      nodesExp (C.plusVE p.ve) (path ++ [1]) e
  | .caseE e m => [⟨path, C.U, [(AExp.caseE e m).ty], []⟩] ++ nodesExp C (path ++ [0]) e ++ nodesMatch C (path ++ [1]) m
def nodesExpOpt (C : Ctx) (path : List Nat) : Option AExp → List Node
  | none => []
  | some e => nodesExp C path e
def nodesMatch (C : Ctx) (path : List Nat) : AMatch → List Node
  | .mk (.mk p e) rest => [⟨path, C.U, [(AMRule.mk p e).ty], []⟩] ++ nodesPat C.U (path ++ [0]) p ++
      nodesExp (C.plusVE p.ve) (path ++ [1]) e ++ nodesMatchOpt C (path ++ [2]) rest
def nodesMatchOpt (C : Ctx) (path : List Nat) : Option AMatch → List Node
  | none => []
  | some m => nodesMatch C path m
def nodesDec (C : Ctx) (path : List Nat) : ADec → List Node
  | .val VE vb => [⟨path, C.U, [], veSchemes (closGroup C.tyvars VE)⟩] ++ nodesValBind (C.plusVE VE) (path ++ [0]) vb
def nodesValBind (C : Ctx) (path : List Nat) : AValBind → List Node
  | .var x ann τ e rest => [⟨path, C.U, [τ], veSchemes (AValBind.var x ann τ e rest).ve⟩] ++
      nodesExp (C.plusU (annU ann)) (path ++ [0]) e ++ nodesValBindOpt C (path ++ [1]) rest
  | .pat p e => [⟨path, C.U, [p.ty], veSchemes p.ve⟩] ++ nodesAtPat C.U (path ++ [0]) p ++ nodesExp C (path ++ [1]) e
def nodesValBindOpt (C : Ctx) (path : List Nat) : Option AValBind → List Node
  | none => []
  | some vb => nodesValBind C path vb
end

/-! ## The types at the nodes -/

/-- Every type at a node of a derivation is `Ty.okB`: its rows are canonical (finite maps) and it
    has no free `bnd` variable. -/
def nodesOkB (ns : List Node) : Bool := ns.all fun n => n.tys.all Ty.okB

/-! `okExpB a`: the types at the nodes of a derivation are all `Ty.okB`, the same check as
`nodesOkB (nodesExp C path a)` (`nodesOkB_nodesExp`) without building the nodes (whose paths would
cost space quadratic in the depth of the phrase). -/

mutual
def okAtPatB : AAtPat → Bool
  | .tuple p1 p2 p3 => (tupleTy p1.ty p2.ty (APat.tyOpt p3)).okB && okPatB p1 && okPatB p2 && okPatOptB p3
  | .record row τ => τ.okB && okPatRowOptB row
  | .paren p => p.ty.okB && okPatB p
  | .wild τ => τ.okB
  | .scon _ τ => τ.okB
  | .var _ τ => τ.okB
  | .con _ _ τ => τ.okB
  | .unit => tUnitTy.okB
  | .nil τ => τ.okB
def okPatRowB : APatRow → Bool
  | .field l τ rest => τ.okB && ((APatRow.row (.field l τ rest)).map (·.2)).all Ty.okB && okPatRowOptB rest
def okPatRowOptB : Option APatRow → Bool
  | none => true
  | some r => okPatRowB r
def okPatB : APat → Bool
  | .atpat a => a.ty.okB && okAtPatB a
  | .con _ _ args τ => τ.okB && okAtPatsB args
  | .cons p1 p2 => (listTy p1.ty).okB && okPatB p1 && okPatB p2
  | .as p _ => p.ty.okB && okPatB p
def okPatOptB : Option APat → Bool
  | none => true
  | some p => okPatB p
def okAtPatsB : List AAtPat → Bool
  | [] => true
  | a :: as => okAtPatB a && okAtPatsB as
end

mutual
def okAtExpB : AAtExp → Bool
  | .scon _ τ | .var _ _ τ | .con _ _ τ | .op _ _ τ | .nil τ => τ.okB
  | .unit => tUnitTy.okB
  | .tuple e1 e2 e3 => (AAtExp.tuple e1 e2 e3).ty.okB && okExpB e1 && okExpB e2 && okExpOptB e3
  | .record row => (AAtExp.record row).ty.okB && okExpRowOptB row
  | .update _ _ τ row => τ.okB && okExpRowB row
  | .letE d e => e.ty.okB && okDecB d && okExpB e
  | .paren e => e.ty.okB && okExpB e
def okExpRowB : AExpRow → Bool
  | .field l e rest => ((AExpRow.field l e rest).row.map (·.2)).all Ty.okB && okExpB e && okExpRowOptB rest
def okExpRowOptB : Option AExpRow → Bool
  | none => true
  | some r => okExpRowB r
def okExpB : AExp → Bool
  | .atexp a => a.ty.okB && okAtExpB a
  | .app e a => (AExp.app e a).ty.okB && okExpB e && okAtExpB a
  | .lam p e => (AExp.lam p e).ty.okB && okAtPatB p && okExpB e
  | .caseE e m => (AExp.caseE e m).ty.okB && okExpB e && okMatchB m
def okExpOptB : Option AExp → Bool
  | none => true
  | some e => okExpB e
def okMatchB : AMatch → Bool
  | .mk (.mk p e) rest => (AMRule.mk p e).ty.okB && okPatB p && okExpB e && okMatchOptB rest
def okMatchOptB : Option AMatch → Bool
  | none => true
  | some m => okMatchB m
def okDecB : ADec → Bool
  | .val _ vb => okValBindB vb
def okValBindB : AValBind → Bool
  | .var _ _ τ e rest => τ.okB && okExpB e && okValBindOptB rest
  | .pat p e => p.ty.okB && okAtPatB p && okExpB e
def okValBindOptB : Option AValBind → Bool
  | none => true
  | some vb => okValBindB vb
end

theorem nodesOkB_append (l1 l2 : List Node) : nodesOkB (l1 ++ l2) = (nodesOkB l1 && nodesOkB l2) := by
  simp [nodesOkB]

theorem nodesOkB_single (p : List Nat) (U : List BVar) (ts : List Ty) (ss : List Scheme) :
    nodesOkB [⟨p, U, ts, ss⟩] = ts.all Ty.okB := by
  simp [nodesOkB]

set_option hygiene false in
macro "nodes_ok_simp" : tactic => `(tactic| simp only [nodesOkB_append, nodesOkB_single, List.all_cons,
  List.all_nil, List.all_append, List.map_nil, List.map_cons, Bool.and_true, Bool.and_self, Bool.and_assoc])

mutual
theorem nodesOkB_nodesAtPat (U : List BVar) (path : List Nat) : ∀ p : AAtPat, nodesOkB (nodesAtPat U path p) = okAtPatB p
  | .wild _ | .scon _ _ | .con _ _ _ | .unit | .nil _ => by
    simp only [nodesAtPat, okAtPatB, AAtPat.ty, AAtPat.ve]; nodes_ok_simp
  | .var _ _ => by
    simp only [nodesAtPat, okAtPatB, AAtPat.ty, AAtPat.ve, mono]; nodes_ok_simp
  | .tuple p1 p2 p3 => by
    simp only [nodesAtPat, okAtPatB]; nodes_ok_simp
    rw [nodesOkB_nodesPat U _ p1, nodesOkB_nodesPat U _ p2, nodesOkB_nodesPatOpt U _ p3]
  | .record row τ => by
    simp only [nodesAtPat, okAtPatB]; nodes_ok_simp
    rw [nodesOkB_nodesPatRowOpt U _ row]
  | .paren p => by
    simp only [nodesAtPat, okAtPatB]; nodes_ok_simp
    rw [nodesOkB_nodesPat U _ p]
theorem nodesOkB_nodesPatRow (U : List BVar) (path : List Nat) : ∀ r : APatRow, nodesOkB (nodesPatRow U path r) = okPatRowB r
  | .field l τ rest => by
    simp only [nodesPatRow, okPatRowB]; nodes_ok_simp
    rw [nodesOkB_nodesPatRowOpt U _ rest]
theorem nodesOkB_nodesPatRowOpt (U : List BVar) (path : List Nat) : ∀ r : Option APatRow,
    nodesOkB (nodesPatRowOpt U path r) = okPatRowOptB r
  | none => rfl
  | some r => by simp only [nodesPatRowOpt, okPatRowOptB]; exact nodesOkB_nodesPatRow U path r
theorem nodesOkB_nodesPat (U : List BVar) (path : List Nat) : ∀ p : APat, nodesOkB (nodesPat U path p) = okPatB p
  | .atpat a => by
    simp only [nodesPat, okPatB]; nodes_ok_simp
    rw [nodesOkB_nodesAtPat U _ a]
  | .con _ _ args τ => by
    simp only [nodesPat, okPatB]; nodes_ok_simp
    rw [nodesOkB_nodesAtPats U path 0 args]
  | .cons p1 p2 => by
    simp only [nodesPat, okPatB]; nodes_ok_simp
    rw [nodesOkB_nodesPat U _ p1, nodesOkB_nodesPat U _ p2]
  | .as p _ => by
    simp only [nodesPat, okPatB]; nodes_ok_simp
    rw [nodesOkB_nodesPat U _ p]
theorem nodesOkB_nodesPatOpt (U : List BVar) (path : List Nat) : ∀ p : Option APat, nodesOkB (nodesPatOpt U path p) = okPatOptB p
  | none => rfl
  | some p => by simp only [nodesPatOpt, okPatOptB]; exact nodesOkB_nodesPat U path p
theorem nodesOkB_nodesAtPats (U : List BVar) (path : List Nat) : ∀ (i : Nat) (l : List AAtPat),
    nodesOkB (nodesAtPats U path i l) = okAtPatsB l
  | _, [] => rfl
  | i, a :: as => by
    simp only [nodesAtPats, okAtPatsB, nodesOkB_append]
    rw [nodesOkB_nodesAtPat U _ a, nodesOkB_nodesAtPats U path (i + 1) as]
end

mutual
theorem nodesOkB_nodesAtExp (C : Ctx) (path : List Nat) : ∀ a : AAtExp, nodesOkB (nodesAtExp C path a) = okAtExpB a
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .unit | .nil _ => by
    simp only [nodesAtExp, okAtExpB]; nodes_ok_simp
  | .tuple e1 e2 e3 => by
    simp only [nodesAtExp, okAtExpB]; nodes_ok_simp
    rw [nodesOkB_nodesExp C _ e1, nodesOkB_nodesExp C _ e2, nodesOkB_nodesExpOpt C _ e3]
  | .record row => by
    simp only [nodesAtExp, okAtExpB]; nodes_ok_simp
    rw [nodesOkB_nodesExpRowOpt C _ row]
  | .update _ _ τ row => by
    simp only [nodesAtExp, okAtExpB]; nodes_ok_simp
    rw [nodesOkB_nodesExpRow C _ row]
  | .letE d e => by
    simp only [nodesAtExp, okAtExpB]; nodes_ok_simp
    rw [nodesOkB_nodesDec C _ d, nodesOkB_nodesExp _ _ e]
  | .paren e => by
    simp only [nodesAtExp, okAtExpB]; nodes_ok_simp
    rw [nodesOkB_nodesExp C _ e]
theorem nodesOkB_nodesExpRow (C : Ctx) (path : List Nat) : ∀ r : AExpRow, nodesOkB (nodesExpRow C path r) = okExpRowB r
  | .field l e rest => by
    simp only [nodesExpRow, okExpRowB]; nodes_ok_simp
    rw [nodesOkB_nodesExp C _ e, nodesOkB_nodesExpRowOpt C _ rest]
theorem nodesOkB_nodesExpRowOpt (C : Ctx) (path : List Nat) : ∀ r : Option AExpRow,
    nodesOkB (nodesExpRowOpt C path r) = okExpRowOptB r
  | none => rfl
  | some r => by simp only [nodesExpRowOpt, okExpRowOptB]; exact nodesOkB_nodesExpRow C path r
theorem nodesOkB_nodesExp (C : Ctx) (path : List Nat) : ∀ e : AExp, nodesOkB (nodesExp C path e) = okExpB e
  | .atexp a => by
    simp only [nodesExp, okExpB]; nodes_ok_simp
    rw [nodesOkB_nodesAtExp C _ a]
  | .app e a => by
    simp only [nodesExp, okExpB]; nodes_ok_simp
    rw [nodesOkB_nodesExp C _ e, nodesOkB_nodesAtExp C _ a]
  | .lam p e => by
    simp only [nodesExp, okExpB]; nodes_ok_simp
    rw [nodesOkB_nodesAtPat C.U _ p, nodesOkB_nodesExp _ _ e]
  | .caseE e m => by
    simp only [nodesExp, okExpB]; nodes_ok_simp
    rw [nodesOkB_nodesExp C _ e, nodesOkB_nodesMatch C _ m]
theorem nodesOkB_nodesExpOpt (C : Ctx) (path : List Nat) : ∀ e : Option AExp, nodesOkB (nodesExpOpt C path e) = okExpOptB e
  | none => rfl
  | some e => by simp only [nodesExpOpt, okExpOptB]; exact nodesOkB_nodesExp C path e
theorem nodesOkB_nodesMatch (C : Ctx) (path : List Nat) : ∀ m : AMatch, nodesOkB (nodesMatch C path m) = okMatchB m
  | .mk (.mk p e) rest => by
    simp only [nodesMatch, okMatchB]; nodes_ok_simp
    rw [nodesOkB_nodesPat C.U _ p, nodesOkB_nodesExp _ _ e, nodesOkB_nodesMatchOpt C _ rest]
theorem nodesOkB_nodesMatchOpt (C : Ctx) (path : List Nat) : ∀ m : Option AMatch,
    nodesOkB (nodesMatchOpt C path m) = okMatchOptB m
  | none => rfl
  | some m => by simp only [nodesMatchOpt, okMatchOptB]; exact nodesOkB_nodesMatch C path m
theorem nodesOkB_nodesDec (C : Ctx) (path : List Nat) : ∀ d : ADec, nodesOkB (nodesDec C path d) = okDecB d
  | .val VE vb => by
    simp only [nodesDec, okDecB]; nodes_ok_simp
    rw [nodesOkB_nodesValBind _ _ vb]; simp
theorem nodesOkB_nodesValBind (C : Ctx) (path : List Nat) : ∀ vb : AValBind,
    nodesOkB (nodesValBind C path vb) = okValBindB vb
  | .var x ann τ e rest => by
    simp only [nodesValBind, okValBindB]; nodes_ok_simp
    rw [nodesOkB_nodesExp _ _ e, nodesOkB_nodesValBindOpt C _ rest]
  | .pat p e => by
    simp only [nodesValBind, okValBindB]; nodes_ok_simp
    rw [nodesOkB_nodesAtPat C.U _ p, nodesOkB_nodesExp C _ e]
theorem nodesOkB_nodesValBindOpt (C : Ctx) (path : List Nat) : ∀ vb : Option AValBind,
    nodesOkB (nodesValBindOpt C path vb) = okValBindOptB vb
  | none => rfl
  | some vb => by simp only [nodesValBindOpt, okValBindOptB]; exact nodesOkB_nodesValBind C path vb
end

/-! ## The checker -/

/-- The instance a constant records: its type, for an integer constant (∀α.α). -/
def litInst (sc : SLit) (τ : Ty) : List Ty :=
  match sc with
  | .int _ => [τ]
  | _ => []

def isConTy : Ty → Bool
  | .con _ _ => true
  | _ => false

def isListTy : Ty → Bool
  | .con [_] t => t == tList
  | _ => false

def isRecordTy : Ty → Bool
  | .record _ _ => true
  | _ => false

def recordRow : Ty → Row
  | .record ρ _ => ρ
  | _ => []

mutual
def checkAtPat (C : Ctx) : AAtPat → Bool
  | .wild _ => true
  | .scon sc τ => genAt (typeOf sc) (litInst sc τ) τ && decide (τ ∈ [tIntTy, tCharTy, tStringTy])
  | .var _ _ => true
  | .con lc inst τ =>
    match C.lookupVal lc with
    | some (σ, .c) => genAt σ inst τ && isConTy τ
    | _ => false
  | .unit => true
  | .tuple p1 p2 p3 => checkPat C p1 && checkPat C p2 && checkPatOpt C p3
  | .nil τ => isListTy τ
  | .record row τ => checkPatRowOpt C row && isRecordTy τ && (Row.subB (APatRow.rowOpt row) (recordRow τ))
  | .paren p => checkPat C p
def checkPatRow (C : Ctx) : APatRow → Bool
  | .field _ _ rest => checkPatRowOpt C rest
def checkPatRowOpt (C : Ctx) : Option APatRow → Bool
  | none => true
  | some r => checkPatRow C r
def checkPat (C : Ctx) : APat → Bool
  | .atpat a => checkAtPat C a
  | .con lc inst args τ =>
    (match C.lookupVal lc with
     | some (σ, .c) => genAt σ inst (arrows (AAtPat.tyList args) τ) && isConTy τ
     | _ => false) && checkAtPatList C args
  | .cons p1 p2 => checkPat C p1 && checkPat C p2 && decide (APat.ty p2 = listTy (APat.ty p1))
  | .as p _ => checkPat C p
def checkPatOpt (C : Ctx) : Option APat → Bool
  | none => true
  | some p => checkPat C p
def checkAtPatList (C : Ctx) : List AAtPat → Bool
  | [] => true
  | a :: as => checkAtPat C a && checkAtPatList C as
end

/-- The first option of r:s-valbind-var. -/
def checkAnn (C : Ctx) : Option (BTy × List BVar) → Ty → Bool
  | none, _ => true
  | some (ty, U'), τ =>
    newForB U' ty C.U && decide (elabTy (C.plusU U') ty = some τ) && U'.all (fun v => !decide (v ∈ C.tyvars))

mutual
def checkAtExp (C : Ctx) : AAtExp → Bool
  | .scon sc τ => genAt (typeOf sc) (litInst sc τ) τ
  | .var lv inst τ =>
    match C.lookupVal lv with
    | some (σ, _) => genAt σ inst τ
    | none => false
  | .con lc inst τ =>
    match C.lookupVal lc with
    | some (σ, _) => genAt σ inst τ
    | none => false
  | .op o inst τ =>
    match OTstat o with
    | some (σ, _) => genAt σ inst τ
    | none => false
  | .unit => true
  | .tuple e1 e2 e3 => checkExpS C e1 && checkExpS C e2 && checkExpOpt C e3
  | .nil τ => isListTy τ
  | .record row => checkExpRowOpt C row
  | .update x inst τ row =>
    (match C.lookupVal ⟨none, x⟩ with
     | some (σ, _) => genAt σ inst τ
     | none => false) &&
    isRecordTy τ && checkExpRow C row && Row.subB (AExpRow.row row) (recordRow τ)
  | .letE d e => checkDec C d && checkExpS (C.plusVE (d.result C)) e
  | .paren e => checkExpS C e
def checkExpRow (C : Ctx) : AExpRow → Bool
  | .field _ e rest => checkExpS C e && checkExpRowOpt C rest
def checkExpRowOpt (C : Ctx) : Option AExpRow → Bool
  | none => true
  | some r => checkExpRow C r
/-- The premises of the rules at each node (`checkExp` adds the conditions on the objects). -/
def checkExpS (C : Ctx) : AExp → Bool
  | .atexp a => checkAtExp C a
  | .app e a =>
    checkExpS C e && checkAtExp C a &&
      (match AExp.ty e with
       | .fn τ' _ => decide (τ' = AAtExp.ty a)
       | _ => false)
  | .lam p e => checkAtPat C p && checkExpS (C.plusVE p.ve) e
  | .caseE e m =>
    checkExpS C e && checkMatch C m &&
      (match AMatch.ty m with
       | .fn τ _ => decide (τ = AExp.ty e)
       | _ => false)
def checkExpOpt (C : Ctx) : Option AExp → Bool
  | none => true
  | some e => checkExpS C e
def checkMatch (C : Ctx) : AMatch → Bool
  | .mk mr rest => checkMRule C mr && checkMatchOptAt C (AMRule.ty mr) rest
/-- The rest of a match, every rule at type τ. -/
def checkMatchOptAt (C : Ctx) (τ : Ty) : Option AMatch → Bool
  | none => true
  | some m => checkMatch C m && decide (AMatch.ty m = τ)
def checkMRule (C : Ctx) : AMRule → Bool
  | .mk p e => checkPat C p && checkExpS (C.plusVE p.ve) e
def checkDec (C : Ctx) : ADec → Bool
  | .val VE vb => checkValBind (C.plusVE VE) vb && decide (vb.ve = VE)
def checkValBind (C : Ctx) : AValBind → Bool
  | .var _ ann τ e rest =>
    checkAnn C ann τ && checkExpS (C.plusU (annU ann)) e && decide (AExp.ty e = τ) && checkValBindOpt C rest
  | .pat p e => checkAtPat C p && checkExpS C e && decide (AExp.ty e = p.ty)
def checkValBindOpt (C : Ctx) : Option AValBind → Bool
  | none => true
  | some vb => checkValBind C vb
end


/-- The checker: the premises of the rules at each node (`checkExpS`), and every type at a node of
    the derivation `Ty.okB` (rows are finite maps; `bnd` variables are never free): `okExpB a` is
    `nodesOkB (nodesExp C path a)` for every `C` and `path` (`nodesOkB_nodesExp`). -/
def checkExp (C : Ctx) (a : AExp) : Bool := checkExpS C a && okExpB a

theorem checkExpS_of_checkExp {C : Ctx} {a : AExp} (h : checkExp C a = true) : checkExpS C a = true := by
  simp only [checkExp, Bool.and_eq_true] at h; exact h.1

theorem nodesOkB_iff (ns : List Node) : nodesOkB ns = true ↔ ∀ n ∈ ns, ∀ τ ∈ n.tys, Ty.okB τ = true := by
  simp [nodesOkB]

/-- At every node of a derivation the checker accepts, the types are `Ty.okB`. -/
theorem okB_of_checkExp {C : Ctx} {a : AExp} (h : checkExp C a = true) :
    ∀ n ∈ nodesExp C [] a, ∀ τ ∈ n.tys, Ty.okB τ = true := by
  simp only [checkExp, Bool.and_eq_true] at h; exact (nodesOkB_iff _).mp (by rw [nodesOkB_nodesExp]; exact h.2)

theorem checkExp_iff {C : Ctx} {a : AExp} :
    checkExp C a = true ↔ checkExpS C a = true ∧ ∀ n ∈ nodesExp C [] a, ∀ τ ∈ n.tys, Ty.okB τ = true := by
  simp only [checkExp, Bool.and_eq_true, ← nodesOkB_iff, nodesOkB_nodesExp]

/-! ## Modules -/

inductive ATopDec where
  | value (VE : ValEnv) (vb : AValBind)
  | types (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind)
  | port (x : Var) (ty : BTy) (U : List BVar)
  | seq (a1 a2 : ATopDec)

def ATopDec.erase : ATopDec → BTopDec
  | .value _ vb => .value vb.erase
  | .types _ _ db tbs => .types db tbs
  | .port x ty _ => .port x ty
  | .seq a1 a2 => .seq (ATopDec.erase a1) (ATopDec.erase a2)

structure AModule where
  header : BHeader
  imports : List BImport
  body : Option ATopDec

abbrev AProgram := List AModule

def AModule.erase (a : AModule) : BModule := ⟨a.header, a.imports, a.body.map ATopDec.erase⟩

def checkTopDec (C : Ctx) : ATopDec → Option (Env × PortEnv)
  | .value VE vb =>
    if checkValBind (C.plusVE VE) vb && decide (vb.ve = VE) && okValBindB vb then
      some (Env.ofVE (closGroup C.tyvars VE), [])
    else none
  | .types TE VE db tbs => if checkTypes C TE VE db tbs then some (⟨[], TE, VE⟩, []) else none
  | .port x ty U => elabPort C x ty U
  | .seq a1 a2 =>
    match checkTopDec C a1 with
    | some (E1, PE1) =>
      match checkTopDec (C.oplusE E1) a2 with
      | some (E2, PE2) => some (E1.plus E2, Env.plusPE PE1 PE2)
      | none => none
    | none => none

def checkTopDecOpt (C : Ctx) : Option ATopDec → Option (Env × PortEnv)
  | none => some (Env.empty, [])
  | some d => checkTopDec C d

/-- The context r:sm-module elaborates a module's declarations in. -/
def modCtx (B : SBasis) (π : ProvMap) : Ctx := ⟨B.T, [], envOf B.ME π⟩

/-- The context of a module's declarations, from its imports read after the default ones. -/
def importCtx (B : SBasis) (imps : List BImport) : Option Ctx :=
  (elabImports B π0 (defaultImports ++ imps)).map (modCtx B)

/-- What r:sm-module gives in the context C of the module's imports, when the certificate checks. -/
def AModule.resultIn (B : SBasis) (C : Ctx) (a : AModule) : Option (SBasis × Env) :=
  match checkTopDecOpt C a.body with
  | none => none
  | some (E, PE) =>
    match expose E a.header.exposing with
    | none => none
    | some I =>
      if a.header.name ∈ B.ME.keys then none
      else some (⟨diffL (dedupL E.tynames) B.T, [(a.header.name, I)], PE⟩, E)

/-- What r:sm-module gives, when the certificate checks: B' and E. -/
def AModule.result (B : SBasis) (a : AModule) : Option (SBasis × Env) :=
  match importCtx B a.imports with
  | none => none
  | some C => a.resultIn B C

theorem AModule.result_of_ctx {B : SBasis} {a : AModule} {C : Ctx} (h : importCtx B a.imports = some C) :
    a.result B = a.resultIn B C := by
  simp only [AModule.result, h]

def checkModule (B : SBasis) (a : AModule) : Bool := (a.result B).isSome

/-- The bases of r:p-stat-module: B₁ = B, B_{i+1} = B_i + B'_i; none when a module does not check. -/
def AProgram.bases (B : SBasis) : AProgram → Option (List SBasis)
  | [] => some []
  | a :: rest =>
    match a.result B with
    | some (B', _) => (AProgram.bases (B.plus B') rest).map (B :: ·)
    | none => none

/-- Every module checks in the basis the earlier ones build. -/
def checkProgram (B : SBasis) (a : AProgram) : Bool := (AProgram.bases B a).isSome

end StandardElm.Stat
