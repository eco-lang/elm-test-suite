/-
  A Standard Definition of Elm? Mechanisation, part 5.
  An executable, fuel-bounded evaluator for the relations of Rules.lean.
  `none` means "no result within the fuel" or "no rule applies".

  APPLY gives a finite set; the evaluator is parameterised by a Boolean
  `ch` that chooses a member: `false` takes the first member of
  `applySet`, `true` the last. For function equality, where the set is
  {True, False}, the two choices give the two results of rule
  r:d-app-basic-apply.

  Soundness (`Sound.lean`): whatever the fuel and choice, a result of the
  evaluator is a result of the relation.

  Each function is written with explicit `match` on the results of its
  recursive calls, following the premises of the rule it implements.
-/
import StandardElmMech.Rules

namespace StandardElm

/-- Choose a member of a finite set given as a list. -/
def pick (ch : Bool) (l : List Val) : Option Val := if ch then l.getLast? else l.head?

/-- Decides v = val(scon) for the constants allowed in patterns (no floats). -/
def sconTest (v : Val) (sc : SCon) : Option Bool :=
  match sc, v with
  | .int n, .sv (.int m) => some (m == norm n)
  | .int _, _ => some false
  | .char c, .sv (.char c') => some (c' == c)
  | .char _, _ => some false
  | .str s, .sv (.str s') => some (s' == s)
  | .str _, _ => some false
  | _, _ => none

/-- Decides v = con for a constructor value with no arguments. -/
def conIs (v : Val) (c : Con) : Bool :=
  match v with
  | .con c' [] => c' == c
  | _ => false

/-- Classifies v for r:d-pat-con / r:d-pat-con-fail. -/
def conArgs (v : Val) (c : Con) (n : Nat) : Option (List Val) :=
  match v with
  | .con c' vs => if c' = c ∧ vs.length = n then some vs else none
  | _ => none

mutual

def evAtExp (ch : Bool) : Nat → Env → AtExp → Option Val
  | 0, _, _ => none
  | n+1, E, a =>
    match a with
    | .scon sc => some (valof sc)
    | .var lv => E.lookup lv
    | .con lc => E.lookup lc
    | .op o => OTdyn o
    | .unit => some .unit
    | .tuple e1 e2 e3 =>
      match evExp ch n E e1 with
      | some v1 =>
        match evExp ch n E e2 with
        | some v2 =>
          match evExpOpt ch n E e3 with
          | some v3 => some (.tuple v1 v2 v3)
          | none => none
        | none => none
      | none => none
    | .nil => some Val.nil
    | .record row =>
      match evExpRowOpt ch n E row with
      | some r => some (.record (fmPlus [] r))
      | none => none
    | .update x row =>
      match E.lookup ⟨none, x⟩ with
      | some (.record r) =>
        match evExpRow ch n E row with
        | some r' => some (.record (fmPlus r r'))
        | none => none
      | _ => none
    | .paren e => evExp ch n E e
    | .letE d e =>
      match evDec ch n E d with
      | some VE => evExp ch n (E.plusVE VE) e
      | none => none

def evExpOpt (ch : Bool) : Nat → Env → Option Exp → Option (Option Val)
  | 0, _, _ => none
  | _+1, _, none => some none
  | n+1, E, some e =>
    match evExp ch n E e with
    | some v => some (some v)
    | none => none

def evExpRow (ch : Bool) : Nat → Env → ExpRow → Option Record
  | 0, _, _ => none
  | n+1, E, .field l e rest =>
    match evExp ch n E e with
    | some v =>
      match evExpRowOpt ch n E rest with
      | some r => some (fmPlus [(l, v)] r)
      | none => none
    | none => none

def evExpRowOpt (ch : Bool) : Nat → Env → Option ExpRow → Option Record
  | 0, _, _ => none
  | _+1, _, none => some []
  | n+1, E, some row => evExpRow ch n E row

def evExp (ch : Bool) : Nat → Env → Exp → Option Val
  | 0, _, _ => none
  | n+1, E, e =>
    match e with
    | .atexp a => evAtExp ch n E a
    | .app e a =>
      match evExp ch n E e with
      | some v1 =>
        match evAtExp ch n E a with
        | some v2 => appVal ch n v1 v2
        | none => none
      | none => none
    | .lam p e => some (.closure p e E [])
    | .caseE e m =>
      match evExp ch n E e with
      | some v =>
        match evMatch ch n E v m with
        | some (.ok v') => some v'
        | _ => none
      | none => none

def appVal (ch : Bool) : Nat → Val → Val → Option Val
  | 0, _, _ => none
  | n+1, f, v =>
    match f with
    | .closure p e E VE =>
      match matchAtPat ch n (E.plusVE (recVE VE)) v p with
      | some (.ok VE') => evExp ch n ((E.plusVE (recVE VE)).plusVE VE') e
      | _ => none
    | .con c vs => some (.con c (vs ++ [v]))
    | .basApp b vs =>
      if vs.length + 1 < b.arity then some (.basApp b (vs ++ [v]))
      else if vs.length + 1 = b.arity then pick ch (applySet b (vs ++ [v]))
      else none
    | _ => none

def evMatch (ch : Bool) : Nat → Env → Val → Match → Option VF
  | 0, _, _, _ => none
  | n+1, E, v, .mk mr rest =>
    match evMRule ch n E v mr with
    | some (.ok v') => some (.ok v')
    | some .fail =>
      match rest with
      | none => some .fail
      | some m => evMatch ch n E v m
    | none => none

def evMRule (ch : Bool) : Nat → Env → Val → MRule → Option VF
  | 0, _, _, _ => none
  | n+1, E, v, .mk p e =>
    match matchPat ch n E v p with
    | some (.ok VE) =>
      match evExp ch n (E.plusVE VE) e with
      | some v' => some (.ok v')
      | none => none
    | some .fail => some .fail
    | none => none

def evDec (ch : Bool) : Nat → Env → Dec → Option ValEnv
  | 0, _, _ => none
  | n+1, E, .val vb =>
    match evValBind ch n E vb with
    | some VE => if isRecursive VE vb then some (recVE VE) else some VE
    | none => none

def evValBind (ch : Bool) : Nat → Env → ValBind → Option ValEnv
  | 0, _, _ => none
  | n+1, E, vb =>
    match vb with
    | .var x e rest =>
      match evExp ch n E e with
      | some v =>
        match evValBindOpt ch n E rest with
        | some VE => some (fmPlus [(x, v)] VE)
        | none => none
      | none => none
    | .pat p e =>
      match evExp ch n E e with
      | some v =>
        match matchAtPat ch n E v p with
        | some (.ok VE) => some VE
        | _ => none
      | none => none

def evValBindOpt (ch : Bool) : Nat → Env → Option ValBind → Option ValEnv
  | 0, _, _ => none
  | _+1, _, none => some []
  | n+1, E, some vb => evValBind ch n E vb

def matchAtPat (ch : Bool) : Nat → Env → Val → AtPat → Option VEF
  | 0, _, _, _ => none
  | n+1, E, v, a =>
    match a with
    | .wild => some (.ok [])
    | .scon sc =>
      match sconTest v sc with
      | some true => some (.ok [])
      | some false => some .fail
      | none => none
    | .var x => some (.ok [(x, v)])
    | .con lc =>
      match E.lookup lc with
      | some (.con c []) => if conIs v c then some (.ok []) else some .fail
      | _ => none
    | .unit =>
      match v with
      | .unit => some (.ok [])
      | _ => none
    | .tuple p1 p2 p3 =>
      match v with
      | .tuple v1 v2 v3 =>
        match matchPat ch n E v1 p1 with
        | some r1 =>
          match matchPat ch n E v2 p2 with
          | some r2 =>
            match matchPatOpt ch n E v3 p3 with
            | some r3 => some ((r1.plus r2).plus r3)
            | none => none
          | none => none
        | none => none
      | _ => none
    | .nil => if conIs v conNil then some (.ok []) else some .fail
    | .record row =>
      match v with
      | .record r =>
        match matchPatRowOpt ch n E r row with
        | some VE => some (.ok (fmPlus [] VE))
        | none => none
      | _ => none
    | .paren p => matchPat ch n E v p

def matchPatOpt (ch : Bool) : Nat → Env → Option Val → Option Pat → Option VEF
  | 0, _, _, _ => none
  | _+1, _, none, none => some (.ok [])
  | n+1, E, some v, some p => matchPat ch n E v p
  | _+1, _, _, _ => none

def matchPatRow (ch : Bool) : Nat → Env → Record → PatRow → Option ValEnv
  | 0, _, _, _ => none
  | n+1, E, r, .field l rest =>
    match fmLookup r l with
    | some v =>
      match matchPatRowOpt ch n E r rest with
      | some VE => some (fmPlus [(l, v)] VE)
      | none => none
    | none => none

def matchPatRowOpt (ch : Bool) : Nat → Env → Record → Option PatRow → Option ValEnv
  | 0, _, _, _ => none
  | _+1, _, _, none => some []
  | n+1, E, r, some row => matchPatRow ch n E r row

def matchPat (ch : Bool) : Nat → Env → Val → Pat → Option VEF
  | 0, _, _, _ => none
  | n+1, E, v, p =>
    match p with
    | .atpat a => matchAtPat ch n E v a
    | .con lc args =>
      match E.lookup lc with
      | some (.con c []) =>
        match conArgs v c args.length with
        | some vs => matchAtPats ch n E vs args
        | none => some .fail
      | _ => none
    | .cons p1 p2 =>
      match v with
      | .con c [v1, v2] =>
        if c = conCons then
          match matchPat ch n E v1 p1 with
          | some r1 =>
            match matchPat ch n E v2 p2 with
            | some r2 => some (r1.plus r2)
            | none => none
          | none => none
        else none
      | .con c [] => if c = conNil then some .fail else none
      | _ => none
    | .as p x =>
      match matchPat ch n E v p with
      | some r => some (r.plus (.ok [(x, v)]))
      | none => none

def matchAtPats (ch : Bool) : Nat → Env → List Val → List AtPat → Option VEF
  | 0, _, _, _ => none
  | _+1, _, [], [] => some (.ok [])
  | n+1, E, v :: vs, a :: as =>
    match matchAtPat ch n E v a with
    | some r =>
      match matchAtPats ch n E vs as with
      | some rs => some (r.plus rs)
      | none => none
    | none => none
  | _+1, _, _, _ => none

end

end StandardElm
