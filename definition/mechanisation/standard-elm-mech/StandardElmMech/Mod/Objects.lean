/-
  A Standard Definition of Elm? Mechanisation: the objects of Chapter 7 (dynamic-modules.tex,
  sec:dynamic-modules-compound, sec:dynamic-modules-merge, sec:dynamic-modules-record,
  sec:dynamic-modules-groups), plan step 2: constructor environments, interfaces, module
  environments and bases, the merge of environments, the constructors of record aliases, and the
  thunk translation of top-level value groups.
-/
import StandardElmMech.Mod.Syntax
import StandardElmMech.Derived

namespace StandardElm.Mod
open StandardElm

abbrev ConEnv := List (TyCon × ValEnv)

/-- (RA, CE, VE), Figure fig:dynamic-modules-compound. RA is a finite set, kept as a list. -/
structure Interface where
  RA : List TyCon
  CE : ConEnv
  VE : ValEnv
  deriving Inhabited

abbrev ModEnv := List (ModId × Interface)
/-- A dynamic basis is a module environment. -/
abbrev Basis := ModEnv

def Interface.empty : Interface := ⟨[], [], []⟩
/-- "VE in Interface" = (∅, {}, VE). -/
def Interface.ofVE (VE : ValEnv) : Interface := ⟨[], [], VE⟩
/-- Modification component by component, the set by union. -/
def Interface.plus (I I' : Interface) : Interface :=
  ⟨I.RA ++ I'.RA, fmPlus I.CE I'.CE, fmPlus I.VE I'.VE⟩
/-- I1 + ... + In. -/
def Interface.sum (Is : List Interface) : Interface := Is.foldl Interface.plus .empty

/-- The merge E1 ⊕ E2 (sec:dynamic-modules-merge): a qualifier common to both gets
    QE1(m) + QE2(m), any other whichever of them is defined; VE1 + VE2. Where both bind a name,
    E2's binding is kept. -/
def mergeQE (q1 q2 : List (ModId × Env)) : List (ModId × Env) :=
  q2.map (fun (m, e2) => match fmLookup q1 m with
                         | some e1 => (m, e1.plusEnv e2)
                         | none => (m, e2))
  ++ q1.filter (fun (m, _) => !(q2.any (·.1 == m)))

def Env.merge (E1 E2 : Env) : Env := .mk (mergeQE E1.QE E2.QE) (fmPlus E1.VE E2.VE)

/-- The constructor of a record alias with labels ls (r:dm-typbind): the basic value
    record(l1 ... ln), or, for n = 0, the empty record itself, which is a value but no basic value
    (sec:dynamic-modules-record). -/
def recordCtor : List Lab → Val
  | [] => .record []
  | ls => .basApp (.record ls) []

/-! ## The thunk translation (sec:dynamic-modules-groups) -/

/-- The new variable x' of a group variable x. It begins with `#`, which no Elm identifier
    contains, so it occurs nowhere in the program. -/
def thunkVar (x : Var) : Var := "#" ++ x

/-- y (): the forcing of a thunk. -/
def forceExp (y : Var) : Exp := .app (.atexp (.var ⟨none, y⟩)) .unit

mutual
/-- ⟦·⟧ for the group whose variables are σ: each free occurrence of x ∈ σ becomes (x' ()), and an
    atomic expression { x | exprow } with x ∈ σ free becomes let x = x' () in { x | ⟦exprow⟧ }.
    Below a binder, σ loses the variables it binds, as `fvExp` treats binders. -/
def thunkAtExp (σ : List Var) : AtExp → AtExp
  | .var ⟨none, x⟩ => if σ.contains x then .paren (forceExp (thunkVar x)) else .var ⟨none, x⟩
  | .update x row =>
      if σ.contains x then
        .letE (.val (.var x (forceExp (thunkVar x)) none)) (.atexp (.update x (thunkExpRow σ row)))
      else .update x (thunkExpRow σ row)
  | .tuple e1 e2 e3 => .tuple (thunkExp σ e1) (thunkExp σ e2) (thunkExpOpt σ e3)
  | .record r => .record (thunkExpRowOpt σ r)
  | .letE (.val vb) e =>
      .letE (.val (thunkValBind (removeAll σ (boundValBind vb)) vb))
        (thunkExp (removeAll σ (boundValBind vb)) e)
  | .paren e => .paren (thunkExp σ e)
  | a => a
def thunkExpOpt (σ : List Var) : Option Exp → Option Exp
  | none => none
  | some e => some (thunkExp σ e)
def thunkExpRow (σ : List Var) : ExpRow → ExpRow
  | .field l e rest => .field l (thunkExp σ e) (thunkExpRowOpt σ rest)
def thunkExpRowOpt (σ : List Var) : Option ExpRow → Option ExpRow
  | none => none
  | some r => some (thunkExpRow σ r)
def thunkExp (σ : List Var) : Exp → Exp
  | .atexp a => .atexp (thunkAtExp σ a)
  | .app e a => .app (thunkExp σ e) (thunkAtExp σ a)
  | .lam p e => .lam p (thunkExp (removeAll σ (boundAtPat p)) e)
  | .caseE e m => .caseE (thunkExp σ e) (thunkMatch σ m)
def thunkMatch (σ : List Var) : Match → Match
  | .mk (.mk p e) rest => .mk (.mk p (thunkExp (removeAll σ (boundPat p)) e)) (thunkMatchOpt σ rest)
def thunkMatchOpt (σ : List Var) : Option Match → Option Match
  | none => none
  | some m => some (thunkMatch σ m)
/-- The right-hand sides of a value binding. -/
def thunkValBind (σ : List Var) : ValBind → ValBind
  | .var x e rest => .var x (thunkExp σ e) (thunkValBindOpt σ rest)
  | .pat p e => .pat p (thunkExp σ e)
def thunkValBindOpt (σ : List Var) : Option ValBind → Option ValBind
  | none => none
  | some vb => some (thunkValBind σ vb)
end

/-- ⟦valbind⟧ = x'1 = \_ -> ⟦exp1⟧ and ... and x'n = \_ -> ⟦expn⟧. -/
def thunkGroup (vb : List (Var × Exp)) : ValBind :=
  go (vb.map Prod.fst) vb
where
  go (σ : List Var) : List (Var × Exp) → ValBind
    | [] => .pat .wild (.atexp .unit)
    | [(x, e)] => .var (thunkVar x) (.lam .wild (thunkExp σ e)) none
    | (x, e) :: rest => .var (thunkVar x) (.lam .wild (thunkExp σ e)) (some (go σ rest))

end StandardElm.Mod
