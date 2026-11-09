/-
  A Standard Definition of Elm? Mechanisation, part 1.
  Bare Core abstract syntax after the reduced syntax of Chapter 6
  (sec:dynamic-core-reduced): no type annotations, no Ty or TyRow, and every
  integer constant already typed Int or Float by number specialisation
  (sec:dynamic-core-numbers).

  Grammar: Figures fig:core-grammar-expressions and fig:core-grammar-patterns
  of Chapter 2 (syntax-core). Each phrase class is one inductive type with one
  constructor per production; optional phrases [ ... ] are `Option` fields, so
  that each production stays one constructor and each rule one relation
  constructor.
-/

namespace StandardElm

/-- Var, Lab, ModId and the identifiers of constructors are spelt as strings.
    Constructors and variables are spelt differently (capital letter or not),
    so one string space serves both, as in the domain of a ValEnv. -/
abbrev Var := String
abbrev Lab := String
abbrev ModId := String
abbrev Ident := String

/-- Long identifiers: longvar and longcon. `qual = none` is an unqualified
    identifier; `qual = some m` is `m.id`, with `m` a (possibly dotted) ModId. -/
structure LongId where
  qual : Option ModId
  id : Ident
  deriving Repr, DecidableEq, BEq, Inhabited

/-- An operator opv, spelt as its symbol, e.g. "+" or "::". -/
abbrev Op := String

/-- Special constants scon, after number specialisation.
    `int n` is an integer constant whose occurrence has type Int,
    `intF n` an integer constant whose occurrence has type Float,
    `float m e` the floating-point constant m * 10^e, `char` and `str`
    character and string constants. Integer constants are unsigned in the
    source; `n` is the integer they spell (hexadecimal constants included). -/
inductive SCon where
  | int (n : Int)
  | intF (n : Nat)
  | float (m : Nat) (e : Int)
  | char (c : Char)
  | str (s : String)
  deriving Repr, Inhabited

mutual
  /-- AtExp: atomic expressions. -/
  inductive AtExp where
    | scon (sc : SCon)                              -- special constant
    | var (lv : LongId)                             -- value variable
    | con (lc : LongId)                             -- value constructor
    | op (o : Op)                                   -- operator value (opv)
    | unit                                          -- ()
    | tuple (e1 e2 : Exp) (e3 : Option Exp)         -- ( exp1 , exp2 [, exp3] )
    | nil                                           -- [ ]
    | record (row : Option ExpRow)                  -- { [exprow] }
    | update (x : Var) (row : ExpRow)               -- { var | exprow }
    | letE (d : Dec) (e : Exp)                      -- let dec in exp
    | paren (e : Exp)                               -- ( exp )
  /-- ExpRow: expression rows `lab = exp [, exprow]`. -/
  inductive ExpRow where
    | field (l : Lab) (e : Exp) (rest : Option ExpRow)
  /-- Exp: expressions. -/
  inductive Exp where
    | atexp (a : AtExp)                             -- atomic
    | app (e : Exp) (a : AtExp)                     -- application
    | lam (p : AtPat) (e : Exp)                     -- \ atpat -> exp
    | caseE (e : Exp) (m : Match)                   -- case exp of match
  /-- Match: `mrule [; match]`. -/
  inductive Match where
    | mk (mr : MRule) (rest : Option Match)
  /-- MRule: `pat -> exp`. -/
  inductive MRule where
    | mk (p : Pat) (e : Exp)
  /-- Dec: a value declaration `valbind`. -/
  inductive Dec where
    | val (vb : ValBind)
  /-- ValBind, reduced: `var = exp [and valbind]` or `atpat = exp`. -/
  inductive ValBind where
    | var (x : Var) (e : Exp) (rest : Option ValBind)
    | pat (p : AtPat) (e : Exp)
  /-- AtPat: atomic patterns. -/
  inductive AtPat where
    | wild                                          -- _
    | scon (sc : SCon)                              -- special constant
    | var (x : Var)                                 -- variable
    | con (lc : LongId)                             -- constructor
    | unit                                          -- ()
    | tuple (p1 p2 : Pat) (p3 : Option Pat)         -- ( pat1 , pat2 [, pat3] )
    | nil                                           -- [ ]
    | record (row : Option PatRow)                  -- { [patrow] }
    | paren (p : Pat)                               -- ( pat )
  /-- PatRow: `lab [, patrow]`. -/
  inductive PatRow where
    | field (l : Lab) (rest : Option PatRow)
  /-- Pat: patterns. -/
  inductive Pat where
    | atpat (a : AtPat)                             -- atomic
    | con (lc : LongId) (args : List AtPat)         -- longcon atpat1 ... atpatn (n >= 1)
    | cons (p1 p2 : Pat)                            -- pat1 :: pat2
    | as (p : Pat) (x : Var)                        -- pat as var
end

instance : Inhabited Exp := ⟨.atexp .unit⟩
instance : Inhabited AtPat := ⟨.wild⟩

end StandardElm
