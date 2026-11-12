/-
  A Standard Definition of Elm? Mechanisation, part 5.
  An executable, fuel-bounded evaluator for the logged relations of RulesL.lean (plan decision D1).

  APPLY gives a finite set: one member, except function equality, which gives {True, False}, and
  Debug.todo, which gives none. The evaluator reads an oracle, a sequence of Booleans `o : Nat → Bool`,
  at an index it threads through: at the k-th member choice it reads `o k` (true: the last member,
  false: the first) and passes `k + 1` on. It returns a `Res`: the outcome (`value`, `stuck` when no
  rule applies, `outOfFuel`), the log so far (also on `stuck` and `outOfFuel`), and the index of the
  next unread choice.

  Soundness (Sound.lean): a value of the evaluator is a value of the logged relation, with its log,
  whatever the fuel and the oracle. Completeness (Complete.lean): every derivation is found by some
  oracle and fuel. Together they make "this phrase has no value" provable (`noValue_of_stuck`).

  Each function follows the premises of its rule in the order the rule writes them, with an explicit
  `match` on each recursive result, and builds the log in the syntactic shape of the logged
  constructor's conclusion, as the soundness proof needs.
-/
import StandardElmMech.RulesL

namespace StandardElm

/-- An oracle: the Boolean for the i-th member choice of APPLY in an evaluation (D1). -/
abbrev Oracle := Nat → Bool

def Oracle.const (b : Bool) : Oracle := fun _ => b
/-- The plan's "list of Booleans consumed one per choice": entry i, then false. -/
def Oracle.ofList (L : List Bool) : Oracle := fun i => L.getD i false

inductive Outcome (α : Type) where
  | value (a : α)
  /-- no rule applies (Debug.todo, a failed match of a lambda's pattern, a value of the wrong form) -/
  | stuck
  | outOfFuel
  deriving Repr, Inhabited

/-- A result: the outcome, the log so far, and the index of the next unread choice. -/
structure Res (α : Type) where
  out : Outcome α
  log : Log
  next : Nat
  deriving Inhabited

/-- Decides v = val(scon), for every special constant. -/
def sconTest (v : Val) (sc : SCon) : Bool :=
  match valof sc, v with
  | .sv s, .sv s' => decide (s' = s)
  | _, _ => false

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

def evAtExp (o : Oracle) : Nat → Env → AtExp → Nat → Res Val
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, a, k =>
    match a with
    | .scon sc => ⟨.value (valof sc), [], k⟩
    | .var lv =>
      match E.lookup lv with
      | some v => ⟨.value v, [], k⟩
      | none => ⟨.stuck, [], k⟩
    | .con lc =>
      match E.lookup lc with
      | some v => ⟨.value v, [], k⟩
      | none => ⟨.stuck, [], k⟩
    | .op op =>
      match OTdyn op with
      | some v => ⟨.value v, [], k⟩
      | none => ⟨.stuck, [], k⟩
    | .unit => ⟨.value .unit, [], k⟩
    | .tuple e1 e2 e3 =>
      match evExp o n E e1 k with
      | ⟨.value v1, l1, k1⟩ =>
        match evExp o n E e2 k1 with
        | ⟨.value v2, l2, k2⟩ =>
          match evExpOpt o n E e3 k2 with
          | ⟨.value v3, l3, k3⟩ => ⟨.value (.tuple v1 v2 v3), l1 ++ l2 ++ l3, k3⟩
          | ⟨.stuck, l3, k3⟩ => ⟨.stuck, l1 ++ l2 ++ l3, k3⟩
          | ⟨.outOfFuel, l3, k3⟩ => ⟨.outOfFuel, l1 ++ l2 ++ l3, k3⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .nil => ⟨.value Val.nil, [], k⟩
    | .record row =>
      match evExpRowOpt o n E row k with
      | ⟨.value r, l1, k1⟩ => ⟨.value (.record (fmPlus [] r)), l1, k1⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .update x row =>
      match E.lookup ⟨none, x⟩ with
      | some (.record r) =>
        match evExpRow o n E row k with
        | ⟨.value r', l1, k1⟩ => ⟨.value (.record (fmPlus r r')), l1, k1⟩
        | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
        | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
      | _ => ⟨.stuck, [], k⟩
    | .paren e => evExp o n E e k
    | .letE d e =>
      match evDec o n E d k with
      | ⟨.value VE, l1, k1⟩ =>
        match evExp o n (E.plusVE VE) e k1 with
        | ⟨.value x, l2, k2⟩ => ⟨.value x, l1 ++ l2, k2⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evExpOpt (o : Oracle) : Nat → Env → Option Exp → Nat → Res (Option Val)
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | _+1, _, none, k => ⟨.value none, [], k⟩
  | n+1, E, some e, k =>
    match evExp o n E e k with
    | ⟨.value v, l1, k1⟩ => ⟨.value (some v), l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evExpRow (o : Oracle) : Nat → Env → ExpRow → Nat → Res Record
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, .field l e rest, k =>
    match evExp o n E e k with
    | ⟨.value v, l1, k1⟩ =>
      match evExpRowOpt o n E rest k1 with
      | ⟨.value r, l2, k2⟩ => ⟨.value (fmPlus [(l, v)] r), l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evExpRowOpt (o : Oracle) : Nat → Env → Option ExpRow → Nat → Res Record
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | _+1, _, none, k => ⟨.value [], [], k⟩
  | n+1, E, some row, k =>
    match evExpRow o n E row k with
    | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evExp (o : Oracle) : Nat → Env → Exp → Nat → Res Val
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, e, k =>
    match e with
    | .atexp a =>
      match evAtExp o n E a k with
      | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .app e a =>
      match evExp o n E e k with
      | ⟨.value v1, l1, k1⟩ =>
        match evAtExp o n E a k1 with
        | ⟨.value v2, l2, k2⟩ =>
          match appVal o n v1 v2 k2 with
          | ⟨.value x, l3, k3⟩ => ⟨.value x, l1 ++ l2 ++ l3, k3⟩
          | ⟨.stuck, l3, k3⟩ => ⟨.stuck, l1 ++ l2 ++ l3, k3⟩
          | ⟨.outOfFuel, l3, k3⟩ => ⟨.outOfFuel, l1 ++ l2 ++ l3, k3⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .lam p e => ⟨.value (.closure p e E []), [], k⟩
    | .caseE e m =>
      match evExp o n E e k with
      | ⟨.value v, l1, k1⟩ =>
        match evMatch o n E v m k1 with
        | ⟨.value (.ok v'), l2, k2⟩ => ⟨.value v', l1 ++ l2, k2⟩
        | ⟨.value .fail, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def appVal (o : Oracle) : Nat → Val → Val → Nat → Res Val
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, f, v, k =>
    match f with
    | .closure p e E VE =>
      match matchAtPat o n (E.plusVE (recVE VE)) v p k with
      | ⟨.value (.ok VE'), l1, k1⟩ =>
        match evExp o n ((E.plusVE (recVE VE)).plusVE VE') e k1 with
        | ⟨.value x, l2, k2⟩ => ⟨.value x, l1 ++ l2, k2⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.value .fail, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .con c vs => ⟨.value (.con c (vs ++ [v])), [], k⟩
    | .basApp b vs =>
      if vs.length + 1 < b.arity then ⟨.value (.basApp b (vs ++ [v])), [], k⟩
      else if vs.length + 1 = b.arity then
        match applySet b (vs ++ [v]) with
        | [] => ⟨.stuck, [], k⟩
        | [w] => ⟨.value w, logEntry b (vs ++ [v]), k⟩
        | w :: w' :: _ => ⟨.value (if o k then w' else w), logEntry b (vs ++ [v]), k + 1⟩
      else ⟨.stuck, [], k⟩
    | _ => ⟨.stuck, [], k⟩

def evMatch (o : Oracle) : Nat → Env → Val → Match → Nat → Res VF
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, v, .mk mr rest, k =>
    match evMRule o n E v mr k with
    | ⟨.value (.ok v'), l1, k1⟩ => ⟨.value (.ok v'), l1, k1⟩
    | ⟨.value .fail, l1, k1⟩ =>
      match rest with
      | none => ⟨.value .fail, l1, k1⟩
      | some m =>
        match evMatch o n E v m k1 with
        | ⟨.value x, l2, k2⟩ => ⟨.value x, l1 ++ l2, k2⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evMRule (o : Oracle) : Nat → Env → Val → MRule → Nat → Res VF
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, v, .mk p e, k =>
    match matchPat o n E v p k with
    | ⟨.value (.ok VE), l1, k1⟩ =>
      match evExp o n (E.plusVE VE) e k1 with
      | ⟨.value v', l2, k2⟩ => ⟨.value (.ok v'), l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.value .fail, l1, k1⟩ => ⟨.value .fail, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evDec (o : Oracle) : Nat → Env → Dec → Nat → Res ValEnv
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, .val vb, k =>
    match evValBind o n E vb k with
    | ⟨.value VE, l1, k1⟩ =>
      if isRecursive VE vb then ⟨.value (recVE VE), l1, k1⟩ else ⟨.value VE, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evValBind (o : Oracle) : Nat → Env → ValBind → Nat → Res ValEnv
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, vb, k =>
    match vb with
    | .var x e rest =>
      match evExp o n E e k with
      | ⟨.value v, l1, k1⟩ =>
        match evValBindOpt o n E rest k1 with
        | ⟨.value VE, l2, k2⟩ => ⟨.value (fmPlus [(x, v)] VE), l1 ++ l2, k2⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .pat p e =>
      match evExp o n E e k with
      | ⟨.value v, l1, k1⟩ =>
        match matchAtPat o n E v p k1 with
        | ⟨.value (.ok VE), l2, k2⟩ => ⟨.value VE, l1 ++ l2, k2⟩
        | ⟨.value .fail, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
        | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evValBindOpt (o : Oracle) : Nat → Env → Option ValBind → Nat → Res ValEnv
  | 0, _, _, k => ⟨.outOfFuel, [], k⟩
  | _+1, _, none, k => ⟨.value [], [], k⟩
  | n+1, E, some vb, k =>
    match evValBind o n E vb k with
    | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def matchAtPat (o : Oracle) : Nat → Env → Val → AtPat → Nat → Res VEF
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, v, a, k =>
    match a with
    | .wild => ⟨.value (.ok []), [], k⟩
    | .scon sc => if sconTest v sc then ⟨.value (.ok []), [], k⟩ else ⟨.value .fail, [], k⟩
    | .var x => ⟨.value (.ok [(x, v)]), [], k⟩
    | .con lc =>
      match E.lookup lc with
      | some (.con c []) => if conIs v c then ⟨.value (.ok []), [], k⟩ else ⟨.value .fail, [], k⟩
      | _ => ⟨.stuck, [], k⟩
    | .unit =>
      match v with
      | .unit => ⟨.value (.ok []), [], k⟩
      | _ => ⟨.stuck, [], k⟩
    | .tuple p1 p2 p3 =>
      match v with
      | .tuple v1 v2 v3 =>
        match matchPat o n E v1 p1 k with
        | ⟨.value r1, l1, k1⟩ =>
          match matchPat o n E v2 p2 k1 with
          | ⟨.value r2, l2, k2⟩ =>
            match matchPatOpt o n E v3 p3 k2 with
            | ⟨.value r3, l3, k3⟩ => ⟨.value ((r1.plus r2).plus r3), l1 ++ l2 ++ l3, k3⟩
            | ⟨.stuck, l3, k3⟩ => ⟨.stuck, l1 ++ l2 ++ l3, k3⟩
            | ⟨.outOfFuel, l3, k3⟩ => ⟨.outOfFuel, l1 ++ l2 ++ l3, k3⟩
          | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
          | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
        | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
        | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
      | _ => ⟨.stuck, [], k⟩
    | .nil => if conIs v conNil then ⟨.value (.ok []), [], k⟩ else ⟨.value .fail, [], k⟩
    | .record row =>
      match v with
      | .record r =>
        match matchPatRowOpt o n E r row k with
        | ⟨.value VE, l1, k1⟩ => ⟨.value (.ok (fmPlus [] VE)), l1, k1⟩
        | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
        | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
      | _ => ⟨.stuck, [], k⟩
    | .paren p =>
      match matchPat o n E v p k with
      | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def matchPatOpt (o : Oracle) : Nat → Env → Option Val → Option Pat → Nat → Res VEF
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | _+1, _, none, none, k => ⟨.value (.ok []), [], k⟩
  | n+1, E, some v, some p, k =>
    match matchPat o n E v p k with
    | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
  | _+1, _, _, _, k => ⟨.stuck, [], k⟩

def matchPatRow (o : Oracle) : Nat → Env → Record → PatRow → Nat → Res ValEnv
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, r, .field l rest, k =>
    match fmLookup r l with
    | some v =>
      match matchPatRowOpt o n E r rest k with
      | ⟨.value VE, l1, k1⟩ => ⟨.value (fmPlus [(l, v)] VE), l1, k1⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | none => ⟨.stuck, [], k⟩

def matchPatRowOpt (o : Oracle) : Nat → Env → Record → Option PatRow → Nat → Res ValEnv
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | _+1, _, _, none, k => ⟨.value [], [], k⟩
  | n+1, E, r, some row, k =>
    match matchPatRow o n E r row k with
    | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def matchPat (o : Oracle) : Nat → Env → Val → Pat → Nat → Res VEF
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | n+1, E, v, p, k =>
    match p with
    | .atpat a =>
      match matchAtPat o n E v a k with
      | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
    | .con lc args =>
      match E.lookup lc with
      | some (.con c []) =>
        match conArgs v c args.length with
        | some vs =>
          match matchAtPats o n E vs args k with
          | ⟨.value x, l1, k1⟩ => ⟨.value x, l1, k1⟩
          | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
          | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
        | none => ⟨.value .fail, [], k⟩
      | _ => ⟨.stuck, [], k⟩
    | .cons p1 p2 =>
      match v with
      | .con c [v1, v2] =>
        if c = conCons then
          match matchPat o n E v1 p1 k with
          | ⟨.value r1, l1, k1⟩ =>
            match matchPat o n E v2 p2 k1 with
            | ⟨.value r2, l2, k2⟩ => ⟨.value (r1.plus r2), l1 ++ l2, k2⟩
            | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
            | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
          | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
          | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
        else ⟨.stuck, [], k⟩
      | .con c [] => if c = conNil then ⟨.value .fail, [], k⟩ else ⟨.stuck, [], k⟩
      | _ => ⟨.stuck, [], k⟩
    | .as p x =>
      match matchPat o n E v p k with
      | ⟨.value r, l1, k1⟩ => ⟨.value (r.plus (.ok [(x, v)])), l1, k1⟩
      | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
      | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def matchAtPats (o : Oracle) : Nat → Env → List Val → List AtPat → Nat → Res VEF
  | 0, _, _, _, k => ⟨.outOfFuel, [], k⟩
  | _+1, _, [], [], k => ⟨.value (.ok []), [], k⟩
  | n+1, E, v :: vs, a :: as, k =>
    match matchAtPat o n E v a k with
    | ⟨.value r, l1, k1⟩ =>
      match matchAtPats o n E vs as k1 with
      | ⟨.value rs, l2, k2⟩ => ⟨.value (r.plus rs), l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
  | _+1, _, _, _, k => ⟨.stuck, [], k⟩

end

end StandardElm
