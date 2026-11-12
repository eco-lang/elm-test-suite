/-
  A Standard Definition of Elm? Mechanisation: occurrences in the source syntax, plan step 8
  (section 5.1): every expression, pattern and type-expression occurrence of a module, the `let`s,
  the variables a pattern binds, occurrences of a variable (anywhere, free, direct), and the binding
  sites of sec:syntax-core-restrictions with the variables bound around them. All structural, so
  that the kernel reduces them.
-/
import StandardElmMech.Src.Notation

namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)

/-! ## Subterms -/

mutual
  /-- The proper subexpressions of an expression, preorder (through definitions, rules, arms). -/
  def SExp.children : SExp → List SExp
    | .tuple es | .list es => childrenList es
    | .record fs | .update _ fs => childrenFields fs
    | .access e _ | .neg e | .paren e => e :: e.children
    | .app f as => (f :: f.children) ++ childrenList as
    | .binop _ l r => (l :: l.children) ++ (r :: r.children)
    | .ifte arms e => childrenArms arms ++ (e :: e.children)
    | .lam _ b => b :: b.children
    | .caseE e rs => (e :: e.children) ++ childrenRules rs
    | .letE ds b => childrenDefs ds ++ (b :: b.children)
    | _ => []
  def childrenList : List SExp → List SExp
    | [] => []
    | e :: es => (e :: e.children) ++ childrenList es
  def childrenFields : List (Lab × SExp) → List SExp
    | [] => []
    | (_, e) :: fs => (e :: e.children) ++ childrenFields fs
  def childrenArms : List (SExp × SExp) → List SExp
    | [] => []
    | (c, t) :: r => (c :: c.children) ++ (t :: t.children) ++ childrenArms r
  def childrenRules : List (SPat × SExp) → List SExp
    | [] => []
    | (_, e) :: r => (e :: e.children) ++ childrenRules r
  def childrenDefs : List SDef → List SExp
    | [] => []
    | .fn _ _ _ e :: r => (e :: e.children) ++ childrenDefs r
    | .pat _ e :: r => (e :: e.children) ++ childrenDefs r
end

/-- An expression and all its subexpressions. -/
def SExp.subs (e : SExp) : List SExp := e :: e.children

mutual
  def SPat.children : SPat → List SPat
    | .con _ ps | .tuple ps | .list ps => childrenPats ps
    | .cons a b => (a :: a.children) ++ (b :: b.children)
    | .as p _ | .paren p => p :: p.children
    | _ => []
  def childrenPats : List SPat → List SPat
    | [] => []
    | p :: ps => (p :: p.children) ++ childrenPats ps
end

def SPat.subs (p : SPat) : List SPat := p :: p.children

mutual
  def STy.children : STy → List STy
    | .con _ ts | .tuple ts => childrenTys ts
    | .record fs | .ext _ fs => childrenTyFields fs
    | .fn a b => (a :: a.children) ++ (b :: b.children)
    | _ => []
  def childrenTys : List STy → List STy
    | [] => []
    | t :: ts => (t :: t.children) ++ childrenTys ts
  def childrenTyFields : List (Lab × STy) → List STy
    | [] => []
    | (_, t) :: fs => (t :: t.children) ++ childrenTyFields fs
end

def STy.subs (t : STy) : List STy := t :: t.children

/-- The type variables of a type expression, extension variables included. -/
def STy.tyvars (t : STy) : List String :=
  t.subs.flatMap fun s => match s with
    | .var a => [a]
    | .ext r _ => [r]
    | _ => []

/-! ## The patterns and types an expression holds directly -/

/-- The patterns written directly in an expression (not in its subexpressions): a lambda's
    parameters, the patterns of a `case`'s rules, the parameters and destructuring patterns of a
    `let`'s definitions. -/
def SExp.ownPats : SExp → List SPat
  | .lam ps _ => ps
  | .caseE _ rs => rs.map (·.1)
  | .letE ds _ => ds.flatMap fun d => match d with
    | .fn _ _ ps _ => ps
    | .pat p _ => [p]
  | _ => []

/-- The annotations written directly in an expression (those of its `let`'s definitions). -/
def SExp.ownTys : SExp → List STy
  | .letE ds _ => ds.flatMap fun d => match d with
    | .fn _ (some t) _ _ => [t]
    | _ => []
  | _ => []

/-! ## A module's occurrences -/

/-- The expressions of a top-level declaration: the right-hand side of a value definition. -/
def STopDec.rhs : STopDec → List SExp
  | .value (.fn _ _ _ e) | .value (.pat _ e) => [e]
  | _ => []

/-- The patterns of a top-level declaration: a definition's parameters or destructuring pattern. -/
def STopDec.topPats : STopDec → List SPat
  | .value (.fn _ _ ps _) => ps
  | .value (.pat p _) => [p]
  | _ => []

/-- The type expressions of a top-level declaration. -/
def STopDec.topTys : STopDec → List STy
  | .value (.fn _ (some t) _ _) => [t]
  | .port _ t => [t]
  | .alias _ _ t => [t]
  | .custom _ _ cs => cs.flatMap (·.2)
  | _ => []

def SModule.exps (m : SModule) : List SExp := m.decls.flatMap fun d => d.rhs.flatMap SExp.subs

def SModule.pats (m : SModule) : List SPat :=
  (m.decls.flatMap STopDec.topPats ++ m.exps.flatMap SExp.ownPats).flatMap SPat.subs

def SModule.tys (m : SModule) : List STy :=
  (m.decls.flatMap STopDec.topTys ++ m.exps.flatMap SExp.ownTys).flatMap STy.subs

def SModule.lets (m : SModule) : List (List SDef) :=
  m.exps.filterMap fun e => match e with
    | .letE ds _ => some ds
    | _ => none

/-! ## Bound variables and occurrences -/

mutual
  /-- The variables a pattern binds, with multiplicity, in order: its variables, the labels of its
      record patterns, the variables after `as`. -/
  def SPat.bound : SPat → List Var
    | .var x => [x]
    | .record ls => ls
    | .as p x => p.bound ++ [x]
    | .con _ ps | .tuple ps | .list ps => boundPats ps
    | .cons a b => a.bound ++ b.bound
    | .paren p => p.bound
    | _ => []
  def boundPats : List SPat → List Var
    | [] => []
    | p :: ps => p.bound ++ boundPats ps
end

def SDef.bound : SDef → List Var
  | .fn x _ _ _ => [x]
  | .pat p _ => p.bound

/-- `x` occurs as an unqualified variable, or as the variable of an update, anywhere. -/
def occurs (x : Var) (e : SExp) : Bool :=
  e.subs.any fun s => match s with
    | .var ⟨none, y⟩ => y == x
    | .update y _ => y == x
    | _ => false

def occursDef (x : Var) : SDef → Bool
  | .fn _ _ _ e | .pat _ e => occurs x e

mutual
  /-- A free occurrence: unqualified, not within the scope of a binding of `x` made inside `e`. -/
  def occursFree (x : Var) : SExp → Bool
    | .var ⟨none, y⟩ => y == x
    | .update y fs => y == x || freeFields x fs
    | .tuple es | .list es => freeList x es
    | .record fs => freeFields x fs
    | .access e _ | .neg e | .paren e => occursFree x e
    | .app f as => occursFree x f || freeList x as
    | .binop _ l r => occursFree x l || occursFree x r
    | .ifte arms e => freeArms x arms || occursFree x e
    | .lam ps b => !((boundPats ps).contains x) && occursFree x b
    | .caseE e rs => occursFree x e || freeRules x rs
    | .letE ds b => !((ds.flatMap SDef.bound).contains x) && (freeDefs x ds || occursFree x b)
    | _ => false
  def freeList (x : Var) : List SExp → Bool
    | [] => false
    | e :: es => occursFree x e || freeList x es
  def freeFields (x : Var) : List (Lab × SExp) → Bool
    | [] => false
    | (_, e) :: fs => occursFree x e || freeFields x fs
  def freeArms (x : Var) : List (SExp × SExp) → Bool
    | [] => false
    | (c, t) :: r => occursFree x c || occursFree x t || freeArms x r
  def freeRules (x : Var) : List (SPat × SExp) → Bool
    | [] => false
    | (p, e) :: r => (!(p.bound.contains x) && occursFree x e) || freeRules x r
  def freeDefs (x : Var) : List SDef → Bool
    | [] => false
    | .fn _ _ ps e :: r => (!((boundPats ps).contains x) && occursFree x e) || freeDefs x r
    | .pat _ e :: r => occursFree x e || freeDefs x r
end

mutual
  /-- A direct occurrence (res:modules-value-recursion): free, and not within a lambda, nor within
      the right-hand side of a `let` definition with parameters. -/
  def occursDirect (x : Var) : SExp → Bool
    | .var ⟨none, y⟩ => y == x
    | .update y fs => y == x || directFields x fs
    | .tuple es | .list es => directList x es
    | .record fs => directFields x fs
    | .access e _ | .neg e | .paren e => occursDirect x e
    | .app f as => occursDirect x f || directList x as
    | .binop _ l r => occursDirect x l || occursDirect x r
    | .ifte arms e => directArms x arms || occursDirect x e
    | .lam _ _ => false
    | .caseE e rs => occursDirect x e || directRules x rs
    | .letE ds b => !((ds.flatMap SDef.bound).contains x) && (directDefs x ds || occursDirect x b)
    | _ => false
  def directList (x : Var) : List SExp → Bool
    | [] => false
    | e :: es => occursDirect x e || directList x es
  def directFields (x : Var) : List (Lab × SExp) → Bool
    | [] => false
    | (_, e) :: fs => occursDirect x e || directFields x fs
  def directArms (x : Var) : List (SExp × SExp) → Bool
    | [] => false
    | (c, t) :: r => occursDirect x c || occursDirect x t || directArms x r
  def directRules (x : Var) : List (SPat × SExp) → Bool
    | [] => false
    | (p, e) :: r => (!(p.bound.contains x) && occursDirect x e) || directRules x r
  def directDefs (x : Var) : List SDef → Bool
    | [] => false
    | .fn _ _ [] e :: r => occursDirect x e || directDefs x r
    | .fn _ _ (_ :: _) _ :: r => directDefs x r
    | .pat _ e :: r => occursDirect x e || directDefs x r
end

/-! ## Binding sites -/

/-- A binding site: the variables it binds (with multiplicity) and those bound by the sites in
    whose scope it lies. -/
structure Site where
  binds : List Var
  outer : List Var

mutual
  /-- The binding sites within an expression, under the variables `env` bound around it: a
      lambda's parameters; a function binding's parameters; a rule's pattern; the definitions of
      one `let` taken together (their destructuring patterns included). -/
  def sitesE (env : List Var) : SExp → List Site
    | .tuple es | .list es => sitesList env es
    | .record fs | .update _ fs => sitesFields env fs
    | .access e _ | .neg e | .paren e => sitesE env e
    | .app f as => sitesE env f ++ sitesList env as
    | .binop _ l r => sitesE env l ++ sitesE env r
    | .ifte arms e => sitesArms env arms ++ sitesE env e
    | .lam ps b => ⟨boundPats ps, env⟩ :: sitesE (env ++ boundPats ps) b
    | .caseE e rs => sitesE env e ++ sitesRules env rs
    | .letE ds b =>
      ⟨ds.flatMap SDef.bound, env⟩ ::
        (sitesDefs (env ++ ds.flatMap SDef.bound) ds ++ sitesE (env ++ ds.flatMap SDef.bound) b)
    | _ => []
  def sitesList (env : List Var) : List SExp → List Site
    | [] => []
    | e :: es => sitesE env e ++ sitesList env es
  def sitesFields (env : List Var) : List (Lab × SExp) → List Site
    | [] => []
    | (_, e) :: fs => sitesE env e ++ sitesFields env fs
  def sitesArms (env : List Var) : List (SExp × SExp) → List Site
    | [] => []
    | (c, t) :: r => sitesE env c ++ sitesE env t ++ sitesArms env r
  def sitesRules (env : List Var) : List (SPat × SExp) → List Site
    | [] => []
    | (p, e) :: r => ⟨p.bound, env⟩ :: (sitesE (env ++ p.bound) e ++ sitesRules env r)
  def sitesDefs (env : List Var) : List SDef → List Site
    | [] => []
    | .fn _ _ ps e :: r => ⟨boundPats ps, env⟩ :: (sitesE (env ++ boundPats ps) e ++ sitesDefs env r)
    | .pat _ e :: r => sitesE env e ++ sitesDefs env r
end

/-- The binding sites of a module: those of each top-level definition (its parameters, scope its
    right-hand side) and of their expressions. The top level itself is not a site of Chapter 2. -/
def SModule.sites (m : SModule) : List Site :=
  m.decls.flatMap fun d => match d with
    | .value (.fn _ _ ps e) => ⟨boundPats ps, []⟩ :: sitesE (boundPats ps) e
    | .value (.pat _ e) => sitesE [] e
    | _ => []

end StandardElm.Src
