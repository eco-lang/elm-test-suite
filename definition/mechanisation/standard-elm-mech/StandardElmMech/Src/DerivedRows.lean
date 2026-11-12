/-
  A Standard Definition of Elm? Mechanisation: the row functions of Appendix A over the bare
  syntax, plan step 8 (section 3.1). The region between the markers is written by
  definition/tools/src/GenerateDerivedForms.elm from the same table as Derived.lean; its bodies are
  Derived.lean's, over the bare types.
-/
import StandardElmMech.Src.Bare

namespace StandardElm.Src.D
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src

def basicsTrue : LongId := ⟨some "Basics", "True"⟩
def basicsFalse : LongId := ⟨some "Basics", "False"⟩
def basicsNegate : LongId := ⟨some "Basics", "negate"⟩

-- BEGIN GENERATED derived forms (definition/tools/src/GenerateDerivedForms.elm); edit the table, not this
/-- Row "exp1 opv exp2" (df:infix): `(opv) (exp1) (exp2)`. -/
def bin (o : Op) (e1 : BExp) (e2 : BExp) : BExp :=
  .app (.app (.atexp (.op o)) (.paren e1)) (.paren e2)

/-- Row "if exp1 then exp2 else exp3" (df:if): `case exp1 of Basics.True -> (exp2) ; Basics.False -> exp3`. -/
def ifte (e1 : BExp) (e2 : BExp) (e3 : BExp) : BExp :=
  .caseE e1 (.mk (.mk (.atpat (.con basicsTrue)) (.atexp (.paren e2))) (some (.mk (.mk (.atpat (.con basicsFalse)) e3) none)))

/-- Row "\atpat1...atpatn -> exp" (df:lambda-params): `\atpat1 -> ... \atpatn -> exp (n >= 2)`. -/
def lams (ps : List BAtPat) (e : BExp) : BExp :=
  go ps
where
  go : List BAtPat → BExp
    | [] => e
    | x0 :: rest => .lam x0 (go rest)

/-- Row "-atexp" (df:negation): `(Basics.negate atexp)`. -/
def neg (a : BAtExp) : BAtExp :=
  .paren (.app (.atexp (.var basicsNegate)) a)

/-- Row ".lab" (df:field-accessor): `(\{ lab } -> lab)`. -/
def accessor (l : Lab) : BAtExp :=
  .paren (.lam (.record (some (.field l none))) (.atexp (.var ⟨none, l⟩)))

/-- Row "[pat1, ..., patn]" (df:list-pattern): `(pat1 :: (pat2 :: ... (patn :: [ ])...)) (n >= 1)`. -/
def listP (ps : List BPat) : BAtPat :=
  go ps
where
  go : List BPat → BAtPat
    | [] => .nil
    | x0 :: rest => .paren (.cons x0 (.atpat (go rest)))

/-- Row "if exp1 then exp'1 else if exp2 then exp'2 ... else if expn then exp'n else exp" (df:if-chain): `if exp1 then exp'1 else ( if exp2 then exp'2 else ( ... if expn then exp'n else exp )...) (n >= 2)`. -/
def ifChain (arms : List (BExp × BExp)) (e : BExp) : BExp :=
  go arms
where
  go : List (BExp × BExp) → BExp
    | [] => e
    | [(x0, x1)] => ifte x0 x1 e
    | (x0, x1) :: rest => ifte x0 x1 (.atexp (.paren (go rest)))

/-- Row "exp1 && exp2" (df:and): `if exp1 then exp2 else Basics.False`. -/
def andalso (e1 : BExp) (e2 : BExp) : BExp :=
  ifte e1 e2 (.atexp (.con basicsFalse))

/-- Row "exp1 || exp2" (df:or): `if exp1 then Basics.True else exp2`. -/
def orelse (e1 : BExp) (e2 : BExp) : BExp :=
  ifte e1 (.atexp (.con basicsTrue)) e2

/-- Row "[exp1, ..., expn]" (df:list): `(exp1 :: ... :: expn :: [ ]) (n >= 1)`. -/
def listE (es : List BExp) : BExp :=
  match es with
  | [] => .atexp .nil
  | _ => .atexp (.paren (go es))
where
  go : List BExp → BExp
    | [] => .atexp .nil
    | x0 :: rest => bin "::" x0 (go rest)

/-- Row "atexp.lab" (df:field-selection): `(.lab atexp)`. -/
def access (a : BAtExp) (l : Lab) : BAtExp :=
  .paren (.app (.atexp (accessor l)) a)
-- END GENERATED derived forms

end StandardElm.Src.D
