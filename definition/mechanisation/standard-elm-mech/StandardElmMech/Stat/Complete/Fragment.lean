/-
  A Standard Definition of Elm? Mechanisation: the features of a program and its fragment, plan
  step 11 ("Lean definitions", Fragments). Milestone (b) decides fragment F_b only.

  `featuresOf B p` reads the bare program and the schemes its occurrences reach in the context
  its first module's imports give (`importCtx`): an occurrence of a name that the module binds
  anywhere (top level, `let`, pattern) is local and reaches no imported scheme. A scheme reaches
  a class when it quantifies a type variable of class other than any (or a row variable, counted
  as records), and records when its body has a record type. Type expressions (annotations, type
  declarations, ports) reach classes through class-named type variables and records through
  record syntax and through the type functions they name.

  F_b (milestone (b)): one module, no integer constant (an integer constant's type is a class
  variable), no class, no record, no annotation with type variables, and no port. Type
  declarations are allowed. `InFragment .b B p` is decidable (`fragmentOf` computes it).
-/
import StandardElmMech.Stat.Complete.W

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  SLit BTopDec BModule BProgram BDatBind BTypBind)

/-! ## A summary of a phrase -/

/-- What a traversal of the bare syntax collects. -/
structure Summ where
  int : Bool := false
  hasRec : Bool := false
  occs : List LongId := []
  ops : List Op := []
  binders : List String := []
  tys : List BTy := []
  deriving Inhabited

def Summ.join (a b : Summ) : Summ :=
  ⟨a.int || b.int, a.hasRec || b.hasRec, a.occs ++ b.occs, a.ops ++ b.ops, a.binders ++ b.binders, a.tys ++ b.tys⟩

instance : Append Summ := ⟨Summ.join⟩

def litSumm : SLit → Summ
  | .int _ => { int := true }
  | _ => {}

mutual
def summAtPat : BAtPat → Summ
  | .wild => {}
  | .scon sc => litSumm sc
  | .var x => { binders := [x] }
  | .con lc => { occs := [lc] }
  | .unit => {}
  | .tuple p1 p2 p3 => summPat p1 ++ summPat p2 ++ summPatOpt p3
  | .nil => {}
  | .record row => { hasRec := true, binders := summPatRowOpt row }
  | .paren p => summPat p
def summPatRowOpt : Option BPatRow → List String
  | none => []
  | some (.field l rest) => l :: summPatRowOpt rest
def summPat : BPat → Summ
  | .atpat a => summAtPat a
  | .con lc args => { occs := [lc] } ++ summAtPats args
  | .cons p1 p2 => summPat p1 ++ summPat p2
  | .as p x => summPat p ++ { binders := [x] }
def summPatOpt : Option BPat → Summ
  | none => {}
  | some p => summPat p
def summAtPats : List BAtPat → Summ
  | [] => {}
  | a :: as => summAtPat a ++ summAtPats as
end

mutual
def summAtExp : BAtExp → Summ
  | .scon sc => litSumm sc
  | .var lv => { occs := [lv] }
  | .con lc => { occs := [lc] }
  | .op o => { ops := [o] }
  | .unit => {}
  | .tuple e1 e2 e3 => summExp e1 ++ summExp e2 ++ summExpOpt e3
  | .nil => {}
  | .record row => { hasRec := true } ++ summExpRowOpt row
  | .update x row => { hasRec := true, occs := [⟨none, x⟩] } ++ summExpRow row
  | .letE d e => summDec d ++ summExp e
  | .paren e => summExp e
def summExpRow : BExpRow → Summ
  | .field _ e rest => summExp e ++ summExpRowOpt rest
def summExpRowOpt : Option BExpRow → Summ
  | none => {}
  | some r => summExpRow r
def summExp : BExp → Summ
  | .atexp a => summAtExp a
  | .app e a => summExp e ++ summAtExp a
  | .lam p e => summAtPat p ++ summExp e
  | .caseE e m => summExp e ++ summMatch m
def summExpOpt : Option BExp → Summ
  | none => {}
  | some e => summExp e
def summMatch : BMatch → Summ
  | .mk mr rest => summMRule mr ++ summMatchOpt rest
def summMatchOpt : Option BMatch → Summ
  | none => {}
  | some m => summMatch m
def summMRule : BMRule → Summ
  | .mk p e => summPat p ++ summExp e
def summDec : BDec → Summ
  | .val vb => summValBind vb
def summValBind : BValBind → Summ
  | .var x ann e rest =>
    { binders := [x], tys := ann.toList } ++ summExp e ++ summValBindOpt rest
  | .pat p e => summAtPat p ++ summExp e
def summValBindOpt : Option BValBind → Summ
  | none => {}
  | some vb => summValBind vb
end

/-! ## Type expressions -/

mutual
/-- Record syntax in a type expression, and the type constructors it names. -/
def tyRec : BTy → Bool
  | .record _ | .openRecord _ _ => true
  | .tuple t1 t2 t3 => tyRec t1 || tyRec t2 || (match t3 with | none => false | some t => tyRec t)
  | .con _ args => tyRecList args
  | .fn t1 t2 => tyRec t1 || tyRec t2
  | .paren t => tyRec t
  | .tyvar _ | .unit => false
def tyRecList : List BTy → Bool
  | [] => false
  | t :: ts => tyRec t || tyRecList ts
end

mutual
def tyCons : BTy → List LongId
  | .con c args => c :: tyConsList args
  | .tuple t1 t2 t3 => tyCons t1 ++ tyCons t2 ++ (match t3 with | none => [] | some t => tyCons t)
  | .fn t1 t2 => tyCons t1 ++ tyCons t2
  | .paren t => tyCons t
  | _ => []
def tyConsList : List BTy → List LongId
  | [] => []
  | t :: ts => tyCons t ++ tyConsList ts
end

/-! ## Top-level declarations -/

/-- The summary of a module body; the type expressions of type declarations and ports, and the
    names they bind (value constructors, record aliases' constructors, local type names). -/
structure TopSumm where
  s : Summ
  declTys : List BTy
  localTyNames : List String
  ports : Bool

def summTop : BTopDec → TopSumm
  | .value vb => ⟨summValBind vb, [], [], false⟩
  | .types db tbs =>
    let cons := (db.getD []).flatMap fun d => d.2.2.map (·.1)
    let args := (db.getD []).flatMap fun d => d.2.2.flatMap (·.2)
    let params := (db.getD []).flatMap (·.2.1) ++ tbs.flatMap (·.params)
    ⟨{ binders := cons ++ tbs.map (·.c) }, args ++ tbs.map (·.t) ++ params.map BTy.tyvar,
      (db.getD []).map (·.1) ++ tbs.map (·.c), false⟩
  | .port _ t => ⟨{}, [t], [], true⟩
  | .seq d1 d2 =>
    let a := summTop d1
    let b := summTop d2
    ⟨a.s ++ b.s, a.declTys ++ b.declTys, a.localTyNames ++ b.localTyNames, a.ports || b.ports⟩

/-! ## Features and fragments -/

structure Features where
  intConst : Bool
  classVar : Bool
  records : Bool
  annVars : Bool
  ports : Bool
  modules : Bool
  deriving DecidableEq, Repr

/-- A scheme reaches a class (a bound type variable of class other than any). -/
def schemeClass (σ : Scheme) : Bool := σ.bound.any fun v => match v with
  | .ty a => a.cls != .any
  | .row _ => false

/-- A scheme reaches records (a bound row variable, or a record type in its body). -/
def schemeRec (σ : Scheme) : Bool :=
  (σ.bound.any fun v => match v with | .row _ => true | .ty _ => false) || tyHasRec σ.body
where
  tyHasRec (τ : Ty) : Bool := hasRec τ
  hasRec : Ty → Bool
    | .var _ => false
    | .record _ _ => true
    | .fn a b => hasRec a || hasRec b
    | .con as _ => as.attach.any fun ⟨t, _⟩ => hasRec t

def classNamed (s : String) : Bool := classOfName s != .any

/-- The features of a single-module program's first module in its import context. -/
def featuresOf (B : SBasis) (p : BProgram) : Features :=
  match p.modules with
  | [] => ⟨false, false, false, false, false, false⟩
  | m :: rest =>
    let ts : TopSumm := match m.body with
      | some d => summTop d
      | none => ⟨{}, [], [], false⟩
    let s := ts.s
    let C? := importCtx B m.imports
    let reach (lv : LongId) : Option Scheme :=
      if lv.qual.isNone && decide (lv.id ∈ s.binders) then none
      else C?.bind fun C => (C.lookupVal lv).map (·.1)
    let schemes := s.occs.filterMap reach ++ s.ops.filterMap fun o => (OTstat o).map (·.1)
    let allTys := s.tys ++ ts.declTys
    let tyFcnRec (c : LongId) : Bool :=
      if c.qual.isNone && decide (c.id ∈ ts.localTyNames) then false
      else match C?.bind fun C => C.lookupTy c with
        | some (θ, _) => schemeRec.hasRec θ.body
        | none => false
    ⟨s.int,
     schemes.any schemeClass || allTys.any (fun t => (Stat.bTyNames t).any classNamed),
     s.hasRec || schemes.any schemeRec || allTys.any tyRec || allTys.any (fun t => (tyCons t).any tyFcnRec),
     s.tys.any (fun t => !(Stat.bTyNames t).isEmpty),
     ts.ports,
     !rest.isEmpty⟩

inductive Fragment where
  | b | c | d | e | f
  deriving DecidableEq, Repr

def Fragment.rank : Fragment → Nat
  | .b => 0 | .c => 1 | .d => 2 | .e => 3 | .f => 4

/-- The least fragment of a program (section "Fragments"; ports count as F_f at milestone (b)). -/
def fragmentOf (B : SBasis) (p : BProgram) : Fragment :=
  let F := featuresOf B p
  if F.modules || F.ports then .f
  else if F.annVars then .e
  else if F.records then .d
  else if F.intConst || F.classVar then .c
  else .b

def InFragment (fr : Fragment) (B : SBasis) (p : BProgram) : Prop := (fragmentOf B p).rank ≤ fr.rank

instance (fr : Fragment) (B : SBasis) (p : BProgram) : Decidable (InFragment fr B p) := by
  unfold InFragment; infer_instance

end StandardElm.Stat.Complete
