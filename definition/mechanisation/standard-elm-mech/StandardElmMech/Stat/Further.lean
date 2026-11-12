/-
  A Standard Definition of Elm? Mechanisation: the further restrictions of a derivation, plan
  step 9 (section 9, sec:static-core-further and sec:static-modules-further).

  The restrictions are judged at each match, each lambda and each destructuring binding of a
  derivation, at the types the derivation gives its patterns (`FurtherExp`); the decider
  (`furtherExpB`) runs the pattern decider of Patterns.lean there, with a check that the normalised
  patterns fit the constructor table at those types. PatternsProof.lean proves the decider sound.
-/
import StandardElmMech.Stat.Patterns

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-- A normalised pattern fits the constructor table at type τ. -/
def PatN.typedB (tbl : ConTable) : Nat → Ty → PatN → Bool
  | 0, _, _ => false
  | _ + 1, _, .wild => true
  | _ + 1, τ, .den d => litKind τ == some d.kind && d.inRange
  | f + 1, τ, .con k args =>
    match argTys tbl τ k with
    | some as => as.length == args.length && (litKind τ).isNone && typedList f as args
    | none => false
where
  typedList : Nat → List Ty → List PatN → Bool
    | f, τ :: τs, p :: ps => PatN.typedB tbl f τ p && typedList f τs ps
    | _, [], [] => true
    | _, _, _ => false

mutual
/-- The depth of a pattern (structural, so that the kernel reduces it). -/
def patDepth : PatN → Nat
  | .wild => 1
  | .den _ => 1
  | .con _ args => 1 + patDepthList args
def patDepthList : List PatN → Nat
  | [] => 0
  | p :: ps => max (patDepth p) (patDepthList ps)
end

/-- The patterns of a match, normalised. -/
def matchPats : AMatch → List PatN
  | .mk (.mk p _) rest =>
    normPat p :: (match rest with
      | none => []
      | some m => matchPats m)

/-- The restrictions at one match: exhaustive and irredundant at the scrutinee's type. -/
def MatchOK (tbl : ConTable) (τ : Ty) (ps : List PatN) : Prop := ExhProp tbl τ ps ∧ IrrProp tbl τ ps

def matchOKB (tbl : ConTable) (τ : Ty) (ps : List PatN) : Bool :=
  ps.all (fun p => p.typedB tbl (patDepth p + 1) τ) && exhDec tbl τ ps && irrDec tbl τ ps

def exhOneB (tbl : ConTable) (τ : Ty) (p : PatN) : Bool := p.typedB tbl (patDepth p + 1) τ && exhDec tbl τ [p]

mutual
def FurtherAtExp (tbl : ConTable) : AAtExp → Prop
  | .tuple e1 e2 e3 => FurtherExp tbl e1 ∧ FurtherExp tbl e2 ∧ FurtherExpOpt tbl e3
  | .record row => FurtherExpRowOpt tbl row
  | .update _ _ _ row => FurtherExpRow tbl row
  | .letE d e => FurtherDec tbl d ∧ FurtherExp tbl e
  | .paren e => FurtherExp tbl e
  | _ => True
def FurtherExpRow (tbl : ConTable) : AExpRow → Prop
  | .field _ e rest => FurtherExp tbl e ∧ FurtherExpRowOpt tbl rest
def FurtherExpRowOpt (tbl : ConTable) : Option AExpRow → Prop
  | none => True
  | some r => FurtherExpRow tbl r
def FurtherExp (tbl : ConTable) : AExp → Prop
  | .atexp a => FurtherAtExp tbl a
  | .app e a => FurtherExp tbl e ∧ FurtherAtExp tbl a
  | .lam p e => ExhProp tbl p.ty [normAtPat p] ∧ FurtherExp tbl e
  | .caseE e m => FurtherExp tbl e ∧ MatchOK tbl e.ty (matchPats m) ∧ FurtherMatch tbl m
def FurtherExpOpt (tbl : ConTable) : Option AExp → Prop
  | none => True
  | some e => FurtherExp tbl e
def FurtherMatch (tbl : ConTable) : AMatch → Prop
  | .mk (.mk _ e) rest => FurtherExp tbl e ∧ FurtherMatchOpt tbl rest
def FurtherMatchOpt (tbl : ConTable) : Option AMatch → Prop
  | none => True
  | some m => FurtherMatch tbl m
def FurtherDec (tbl : ConTable) : ADec → Prop
  | .val _ vb => FurtherValBind tbl vb
def FurtherValBind (tbl : ConTable) : AValBind → Prop
  | .var _ _ _ e rest => FurtherExp tbl e ∧ FurtherValBindOpt tbl rest
  | .pat p e => ExhProp tbl p.ty [normAtPat p] ∧ FurtherExp tbl e
def FurtherValBindOpt (tbl : ConTable) : Option AValBind → Prop
  | none => True
  | some vb => FurtherValBind tbl vb
end

mutual
def furtherAtExpB (tbl : ConTable) : AAtExp → Bool
  | .tuple e1 e2 e3 => furtherExpB tbl e1 && furtherExpB tbl e2 && furtherExpOptB tbl e3
  | .record row => furtherExpRowOptB tbl row
  | .update _ _ _ row => furtherExpRowB tbl row
  | .letE d e => furtherDecB tbl d && furtherExpB tbl e
  | .paren e => furtherExpB tbl e
  | _ => true
def furtherExpRowB (tbl : ConTable) : AExpRow → Bool
  | .field _ e rest => furtherExpB tbl e && furtherExpRowOptB tbl rest
def furtherExpRowOptB (tbl : ConTable) : Option AExpRow → Bool
  | none => true
  | some r => furtherExpRowB tbl r
def furtherExpB (tbl : ConTable) : AExp → Bool
  | .atexp a => furtherAtExpB tbl a
  | .app e a => furtherExpB tbl e && furtherAtExpB tbl a
  | .lam p e => exhOneB tbl p.ty (normAtPat p) && furtherExpB tbl e
  | .caseE e m => furtherExpB tbl e && matchOKB tbl e.ty (matchPats m) && furtherMatchB tbl m
def furtherExpOptB (tbl : ConTable) : Option AExp → Bool
  | none => true
  | some e => furtherExpB tbl e
def furtherMatchB (tbl : ConTable) : AMatch → Bool
  | .mk (.mk _ e) rest => furtherExpB tbl e && furtherMatchOptB tbl rest
def furtherMatchOptB (tbl : ConTable) : Option AMatch → Bool
  | none => true
  | some m => furtherMatchB tbl m
def furtherDecB (tbl : ConTable) : ADec → Bool
  | .val _ vb => furtherValBindB tbl vb
def furtherValBindB (tbl : ConTable) : AValBind → Bool
  | .var _ _ _ e rest => furtherExpB tbl e && furtherValBindOptB tbl rest
  | .pat p e => exhOneB tbl p.ty (normAtPat p) && furtherExpB tbl e
def furtherValBindOptB (tbl : ConTable) : Option AValBind → Bool
  | none => true
  | some vb => furtherValBindB tbl vb
end

/-! ## Modules (sec:static-modules-further) -/

def FurtherTopDec (tbl : ConTable) : ATopDec → Prop
  | .value _ vb => FurtherValBind tbl vb
  | .typesSplit a1 a2 | .seq a1 a2 => FurtherTopDec tbl a1 ∧ FurtherTopDec tbl a2
  | _ => True

def furtherTopDecB (tbl : ConTable) : ATopDec → Bool
  | .value _ vb => furtherValBindB tbl vb
  | .typesSplit a1 a2 | .seq a1 a2 => furtherTopDecB tbl a1 && furtherTopDecB tbl a2
  | _ => true

/-- The further restrictions of a module's derivation, with the constructors of the basis and of
    the module's own types. -/
def FurtherModIn (B : SBasis) (E : Env) (a : AModule) : Prop :=
  match a.body with
  | some d => FurtherTopDec (conTable B E) d
  | none => True

def furtherModInB (B : SBasis) (E : Env) (a : AModule) : Bool :=
  match a.body with
  | some d => furtherTopDecB (conTable B E) d
  | none => true

def FurtherMod (B : SBasis) (a : AModule) : Prop :=
  match a.result B with
  | some (_, E) => FurtherModIn B E a
  | none => False

end StandardElm.Stat
