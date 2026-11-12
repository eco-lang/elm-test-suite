/-
  A Standard Definition of Elm? Mechanisation: the derived forms of Appendix A as a function from
  the source syntax to the bare syntax, plan step 8 (section 3.2), with the canonical grouping of
  `let`s and modules (Src/Grouping.lean). The row functions are DerivedRows.lean's, generated from
  the same table as Derived.lean. The function is total: on a tree that breaks a syntactic
  restriction or the grammar (a tuple of four, an extension with no field, a destructuring in a
  group), it returns a fixed phrase; the theorems about it assume `SynOK`.

  "Refers to" is computed on the source, by free occurrences: Appendix A says that no equivalent
  form adds or removes a free occurrence of a variable, so the grouping is the same before and
  after the other rows.
-/
import StandardElmMech.Src.DerivedRows
import StandardElmMech.Src.Restrictions
import StandardElmMech.Src.Grouping

namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)

/-! ## Rows and small helpers -/

def tyRow : List (Lab × BTy) → Option BTyRow
  | [] => none
  | (l, t) :: rest => some (.field l t (tyRow rest))

def patRow : List Lab → Option BPatRow
  | [] => none
  | l :: rest => some (.field l (patRow rest))

def expRow : List (Lab × BExp) → Option BExpRow
  | [] => none
  | (l, e) :: rest => some (.field l e (expRow rest))

/-- An expression as an atomic expression: itself if atomic, else in parentheses (D.A). -/
def toAt : BExp → BAtExp
  | .atexp a => a
  | e => .paren e

def toAtP : BPat → BAtPat
  | .atpat a => a
  | p => .paren p

def matchOf : List (BPat × BExp) → BMatch
  | [] => .mk (.mk (.atpat .wild) (.atexp .unit)) none
  | [(p, e)] => .mk (.mk p e) none
  | (p, e) :: rest => .mk (.mk p e) (some (matchOf rest))

/-! ## Types and patterns -/

mutual
  def deriveTy : STy → BTy
    | .var a => .tyvar a
    | .con c args => .con c (deriveTys args)
    | .unit => .unit
    | .tuple [a, b] => .tuple (deriveTy a) (deriveTy b) none
    | .tuple [a, b, c] => .tuple (deriveTy a) (deriveTy b) (some (deriveTy c))
    | .tuple _ => .unit
    | .record fs => .record (tyRow (deriveTyFields fs))
    | .ext r fs =>
      match tyRow (deriveTyFields fs) with
      | some row => .openRecord r row
      | none => .openRecord r (.field "_" .unit none)
    | .fn a b => .fn (deriveTy a) (deriveTy b)
  def deriveTys : List STy → List BTy
    | [] => []
    | t :: ts => deriveTy t :: deriveTys ts
  def deriveTyFields : List (Lab × STy) → List (Lab × BTy)
    | [] => []
    | (l, t) :: fs => (l, deriveTy t) :: deriveTyFields fs
end

mutual
  def derivePat : SPat → BPat
    | .wild => .atpat .wild
    | .lit l => .atpat (.scon l)
    | .var x => .atpat (.var x)
    | .unit => .atpat .unit
    | .con k [] => .atpat (.con k)
    | .con k args => .con k ((derivePats args).map toAtP)
    | .tuple [a, b] => .atpat (.tuple (derivePat a) (derivePat b) none)
    | .tuple [a, b, c] => .atpat (.tuple (derivePat a) (derivePat b) (some (derivePat c)))
    | .tuple _ => .atpat .unit
    | .list [] => .atpat .nil
    | .list ps => .atpat (D.listP (derivePats ps))
    | .record ls => .atpat (.record (patRow ls))
    | .cons a b => .cons (derivePat a) (derivePat b)
    | .as p x => .as (derivePat p) x
    | .paren p => .atpat (.paren (derivePat p))
  def derivePats : List SPat → List BPat
    | [] => []
    | p :: ps => derivePat p :: derivePats ps
end

def deriveAtPat (p : SPat) : BAtPat := toAtP (derivePat p)

/-! ## Grouping -/

/-- The right-hand side's free occurrences of a definition, through its parameters. -/
def defOccursFree (x : Var) : SDef → Bool
  | .fn _ _ ps e => !((boundPats ps).contains x) && occursFree x e
  | .pat _ e => occursFree x e

/-- d_i refers to d_j: a variable d_j binds occurs free in d_i's right-hand side. -/
def letRefers (ds : List SDef) (i j : Nat) : Bool :=
  match ds[i]?, ds[j]? with
  | some di, some dj => dj.bound.any fun x => defOccursFree x di
  | _, _ => false

/-- The value binding of a component: its members' bindings joined by `and`. -/
def groupBind (bs : List BValBind) : List Nat → BValBind
  | [] => .pat .wild (.atexp .unit)
  | [a] => bs.getD a (.pat .wild (.atexp .unit))
  | a :: rest =>
    match bs.getD a (.pat .wild (.atexp .unit)) with
    | .var x ann e _ => .var x ann e (some (groupBind bs rest))
    | b => b

/-- df:let-grouping (n ≥ 2), and the bare `let valbind in exp` (n = 1). -/
def groupLet (ds : List SDef) (bs : List BValBind) (body : BExp) : BExp :=
  (Grouping.components ds.length (letRefers ds)).foldr
    (fun cmp acc => .atexp (.letE (.val (groupBind bs cmp)) acc)) body

/-! ## Expressions -/

mutual
  def deriveExp : SExp → BExp
    | .lit l => .atexp (.scon l)
    | .var x => .atexp (.var x)
    | .con k => .atexp (.con k)
    | .opVal o => .atexp (.op o)
    | .unit => .atexp .unit
    | .tuple [a, b] => .atexp (.tuple (deriveExp a) (deriveExp b) none)
    | .tuple [a, b, c] => .atexp (.tuple (deriveExp a) (deriveExp b) (some (deriveExp c)))
    | .tuple _ => .atexp .unit
    | .list [] => .atexp .nil
    | .list es => D.listE (deriveExps es)
    | .record fs => .atexp (.record (expRow (deriveFields fs)))
    | .update x fs =>
      match expRow (deriveFields fs) with
      | some row => .atexp (.update x row)
      | none => .atexp .unit
    | .accessor l => .atexp (D.accessor l)
    | .access e l => .atexp (D.access (toAt (deriveExp e)) l)
    | .neg e => .atexp (D.neg (toAt (deriveExp e)))
    | .paren e => .atexp (.paren (deriveExp e))
    | .app f args => (deriveExps args).foldl (fun acc a => .app acc (toAt a)) (deriveExp f)
    | .binop "&&" l r => D.andalso (deriveExp l) (deriveExp r)
    | .binop "||" l r => D.orelse (deriveExp l) (deriveExp r)
    | .binop o l r => D.bin o (deriveExp l) (deriveExp r)
    | .ifte arms e =>
      match deriveArms arms with
      | [(c, t)] => D.ifte c t (deriveExp e)
      | as => D.ifChain as (deriveExp e)
    | .lam [p] b => .lam (deriveAtPat p) (deriveExp b)
    | .lam ps b => D.lams (ps.map deriveAtPat) (deriveExp b)
    | .caseE e rules => .caseE (deriveExp e) (matchOf (deriveRules rules))
    | .letE ds b => groupLet ds (deriveDefs ds) (deriveExp b)
  def deriveExps : List SExp → List BExp
    | [] => []
    | e :: es => deriveExp e :: deriveExps es
  def deriveFields : List (Lab × SExp) → List (Lab × BExp)
    | [] => []
    | (l, e) :: fs => (l, deriveExp e) :: deriveFields fs
  def deriveArms : List (SExp × SExp) → List (BExp × BExp)
    | [] => []
    | (c, t) :: r => (deriveExp c, deriveExp t) :: deriveArms r
  def deriveRules : List (SPat × SExp) → List (BPat × BExp)
    | [] => []
    | (p, e) :: r => (derivePat p, deriveExp e) :: deriveRules r
  /-- df:function-binding: `x [: ty] p1 ... pm = e` gives `x [: ty] = \p1 ... pm -> e`. -/
  def deriveDefs : List SDef → List BValBind
    | [] => []
    | .fn x ann [] e :: r => .var x (ann.map deriveTy) (deriveExp e) none :: deriveDefs r
    | .fn x ann [p] e :: r => .var x (ann.map deriveTy) (.lam (deriveAtPat p) (deriveExp e)) none :: deriveDefs r
    | .fn x ann ps e :: r => .var x (ann.map deriveTy) (D.lams (ps.map deriveAtPat) (deriveExp e)) none :: deriveDefs r
    | .pat p e :: r => .pat (deriveAtPat p) (deriveExp e) :: deriveDefs r
end

def deriveDef (d : SDef) : BValBind := (deriveDefs [d]).headD (.pat .wild (.atexp .unit))

/-! ## Modules (sec:appendix-derived-forms-modules) -/

/-- The aliases mentioned in a type expression, unqualified. -/
def mentions (aliases : List (String × List String × STy)) (t : STy) (c : String) : Bool :=
  aliases.any (fun a => a.1 == c) && t.subs.any fun s => match s with
    | .con ⟨none, c'⟩ _ => c' == c
    | _ => false

/-- The aliases ordered so that each comes after every alias it mentions; among those that may
    come next, the one written first. -/
def aliasOrderAux (all : List (String × List String × STy)) :
    Nat → List (String × List String × STy) → List (String × List String × STy) → List (String × List String × STy)
  | 0, placed, rest => placed ++ rest
  | k + 1, placed, rest =>
    match rest.find? (fun a => all.all fun b => b.1 == a.1 || !(mentions all a.2.2 b.1) || placed.any (·.1 == b.1)) with
    | some a => aliasOrderAux all k (placed ++ [a]) (rest.filter (·.1 != a.1))
    | none => placed ++ rest

def aliasOrder (as : List (String × List String × STy)) : List (String × List String × STy) :=
  aliasOrderAux as as.length [] as

/-- The ports and definitions of a module, in order. -/
inductive TopVal where
  | port (x : Var) (t : STy)
  | val (d : SDef)

def TopVal.bound : TopVal → List Var
  | .port x _ => [x]
  | .val d => d.bound

def topRefers (vs : List TopVal) (i j : Nat) : Bool :=
  match vs[i]?, vs[j]? with
  | some (.val di), some vj => vj.bound.any fun x => defOccursFree x di
  | _, _ => false

def customsOf (ds : List STopDec) : List (String × List String × BConBind) :=
  ds.filterMap fun d => match d with
    | .custom c ps cs => some (c, ps, cs.map fun (k, ts) => (k, deriveTys ts))
    | _ => none

def aliasesOf (ds : List STopDec) : List (String × List String × STy) :=
  ds.filterMap fun d => match d with
    | .alias c ps t => some (c, ps, t)
    | _ => none

def topValsOf (ds : List STopDec) : List TopVal :=
  ds.filterMap fun d => match d with
    | .port x t => some (.port x t)
    | .value d => some (.val d)
    | _ => none

/-- The binding of each definition (none for a port). -/
def topBinds (vs : List TopVal) : List (Option BValBind) :=
  vs.map fun v => match v with
    | .val d => some (deriveDef d)
    | .port _ _ => none

/-- The module's declarations, given a numbering `cs` of its ports and definitions, an order of its
    aliases, and the bindings of its definitions (sec:appendix-derived-forms-modules). -/
def assemble (ds : List STopDec) (cs : List (List Nat)) (order : List (String × List String × STy))
    (bs : List (Option BValBind)) : Option BTopDec :=
  let customs := customsOf ds
  let vs := topValsOf ds
  let db : Option BDatBind := if customs.isEmpty then none else some customs
  let tbs : List BTypBind := order.map fun (c, ps, t) => ⟨c, ps, deriveTy t⟩
  let groups : List BTopDec := cs.filterMap fun cmp =>
    match cmp with
    | [a] => match vs[a]? with
      | some (.port x t) => some (.port x (deriveTy t))
      | some (.val _) => some (.value (groupBind (bs.map fun b => b.getD (.pat .wild (.atexp .unit))) cmp))
      | none => none
    | _ => some (.value (groupBind (bs.map fun b => b.getD (.pat .wild (.atexp .unit))) cmp))
  let items : List BTopDec := (if db.isNone && tbs.isEmpty then [] else [.types db tbs]) ++ groups
  items.foldr (fun d acc => match acc with
    | none => some d
    | some rest => some (.seq d rest)) none

/-- df:module-grouping, with the canonical choices. -/
def deriveTopDecs (ds : List STopDec) : Option BTopDec :=
  assemble ds (Grouping.components (topValsOf ds).length (topRefers (topValsOf ds)))
    (aliasOrder (aliasesOf ds)) (topBinds (topValsOf ds))

def deriveItem : SItem → BItem
  | .var x => .var x
  | .op o => .op o
  | .ty c => .ty c
  | .tyAll c => .tyAll c

def deriveExposing : SExposing → BExpList
  | .all => .all
  | .items is => .items (is.map deriveItem)

def deriveModule (m : SModule) : BModule :=
  { header := ⟨m.header.isPort, m.header.name, deriveExposing m.header.exposing⟩
    imports := m.imports.map fun i => ⟨i.mod, i.alias, i.exposing.map deriveExposing⟩
    body := deriveTopDecs m.decls }

def deriveProgram (p : SProgram) : BProgram := ⟨p.modules.map deriveModule⟩

end StandardElm.Src
