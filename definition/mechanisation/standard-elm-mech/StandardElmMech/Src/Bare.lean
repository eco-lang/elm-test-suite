/-
  A Standard Definition of Elm? Mechanisation: the bare syntax, plan step 8 (section 2).

  The phrase classes of Chapters 2 and 3 after the derived forms of Appendix A, with type
  expressions and annotations kept and constants unspecialised: the reduced syntax of Syntax.lean
  (sec:dynamic-core-reduced) before number specialisation and type erasure. The constructor names
  are those of Syntax.lean, so that the generated row functions (DerivedRows.lean) are the same
  text over either set of types. The static rules of step 9 are stated on it.
-/
import StandardElmMech.Src.Syntax

namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)

mutual
  inductive BTy where
    | tyvar (a : String)
    | record (row : Option BTyRow)
    | openRecord (r : String) (row : BTyRow)
    | unit
    | tuple (t1 t2 : BTy) (t3 : Option BTy)
    | con (c : LongId) (args : List BTy)
    | fn (t1 t2 : BTy)
    | paren (t : BTy)
  inductive BTyRow where
    | field (l : Lab) (t : BTy) (rest : Option BTyRow)
end

mutual
  inductive BAtPat where
    | wild | scon (sc : SLit) | var (x : Var) | con (lc : LongId) | unit
    | tuple (p1 p2 : BPat) (p3 : Option BPat) | nil | record (row : Option BPatRow)
    | paren (p : BPat)
  inductive BPatRow where
    | field (l : Lab) (rest : Option BPatRow)
  inductive BPat where
    | atpat (a : BAtPat) | con (lc : LongId) (args : List BAtPat)
    | cons (p1 p2 : BPat) | as (p : BPat) (x : Var)
end

mutual
  inductive BAtExp where
    | scon (sc : SLit) | var (lv : LongId) | con (lc : LongId) | op (o : Op) | unit
    | tuple (e1 e2 : BExp) (e3 : Option BExp) | nil | record (row : Option BExpRow)
    | update (x : Var) (row : BExpRow) | letE (d : BDec) (e : BExp) | paren (e : BExp)
  inductive BExpRow where
    | field (l : Lab) (e : BExp) (rest : Option BExpRow)
  inductive BExp where
    | atexp (a : BAtExp) | app (e : BExp) (a : BAtExp) | lam (p : BAtPat) (e : BExp)
    | caseE (e : BExp) (m : BMatch)
  inductive BMatch where
    | mk (mr : BMRule) (rest : Option BMatch)
  inductive BMRule where
    | mk (p : BPat) (e : BExp)
  inductive BDec where
    | val (vb : BValBind)
  /-- `var [: ty] = exp [and valbind]` or `atpat = exp` (r:s-valbind-var, r:s-valbind-pat). -/
  inductive BValBind where
    | var (x : Var) (ann : Option BTy) (e : BExp) (rest : Option BValBind)
    | pat (p : BAtPat) (e : BExp)
end

instance : Inhabited BExp := ⟨.atexp .unit⟩
instance : Inhabited BAtExp := ⟨.unit⟩
instance : Inhabited BPat := ⟨.atpat .wild⟩
instance : Inhabited BAtPat := ⟨.wild⟩
instance : Inhabited BTy := ⟨.unit⟩

/-! ## Modules (Figures fig:grammar-modules and fig:grammar-top-level-declarations) -/

inductive BItem where | var (x : Var) | op (o : Op) | ty (c : String) | tyAll (c : String)
  deriving DecidableEq
inductive BExpList where | all | items (is : List BItem)
  deriving DecidableEq
structure BImport where
  mod : ModId
  alias : Option ModId
  exposing : Option BExpList
  deriving DecidableEq
/-- conbind: `con ty1 ... tyn [| conbind]`, as a list. -/
abbrev BConBind := List (String × List BTy)
/-- datbind: `tycon tyvarseq = conbind [and datbind]`, as a list. -/
abbrev BDatBind := List (String × List String × BConBind)
/-- typbind: `tycon tyvarseq = ty`. -/
structure BTypBind where
  c : String
  params : List String
  t : BTy
inductive BTopDec where
  /-- r:sm-topdec-value -/
  | value (vb : BValBind)
  /-- `[type datbind ;] type alias typbind1 ; ... ; type alias typbindl` (r:sm-topdec-types) -/
  | types (db : Option BDatBind) (tbs : List BTypBind)
  /-- r:sm-topdec-portout / -portin -/
  | port (x : Var) (t : BTy)
  /-- r:sm-topdec-seq -/
  | seq (d1 d2 : BTopDec)
structure BHeader where
  isPort : Bool
  name : ModId
  exposing : BExpList
structure BModule where
  header : BHeader
  imports : List BImport
  body : Option BTopDec
structure BProgram where
  modules : List BModule

end StandardElm.Src
