/-
  A Standard Definition of Elm? Mechanisation: unification with classes, rows and rigid variables,
  plan step 9 (section 11). Not proved: the inference only produces certificates, which the
  checker (Annotated.lean, proved sound) decides.

  Inference variables are `TyVar.fresh n κ` and `RowVar.fresh n`, numbered densely from 0; their
  bindings are kept in arrays indexed by n. Named variables (the explicit variables of annotations
  and of type declarations) are rigid: never bound. A row variable records the labels it may not
  take (A23). Every function takes fuel and recurses on it or structurally.
-/
import StandardElmMech.Stat.Annotated

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

structure InfState where
  next : Nat := 0
  tsub : Array (Option Ty) := #[]
  rsub : Array (Option (Row × Option RowVar)) := #[]
  lacks : Array (List Lab) := #[]
  deriving Inhabited

abbrev Inf := StateT InfState (Except String)

def fuel0 : Nat := 1000000

def InfState.alloc (s : InfState) (ls : List Lab := []) : Nat × InfState :=
  (s.next, { s with next := s.next + 1, tsub := s.tsub.push none, rsub := s.rsub.push none, lacks := s.lacks.push ls })

def freshTy (c : Cls) : Inf Ty := do
  let (n, s) := (← get).alloc
  set s
  return .var (.fresh n c)

def freshRow (ls : List Lab := []) : Inf RowVar := do
  let (n, s) := (← get).alloc ls
  set s
  return .fresh n

def InfState.tget (s : InfState) (n : Nat) : Option Ty := (s.tsub[n]?).bind id
def InfState.rget (s : InfState) (n : Nat) : Option (Row × Option RowVar) := (s.rsub[n]?).bind id
def InfState.lget (s : InfState) (n : Nat) : List Lab := (s.lacks[n]?).getD []

def bindTy (n : Nat) (τ : Ty) : Inf Unit := modify fun s => { s with tsub := s.tsub.set! n (some τ) }
def bindRow (n : Nat) (r : Row × Option RowVar) : Inf Unit := modify fun s => { s with rsub := s.rsub.set! n (some r) }

/-- Apply the bindings throughout. -/
def zonk (s : InfState) : Nat → Ty → Ty
  | 0, τ => τ
  | f + 1, .var (.fresh n c) =>
    match s.tget n with
    | some τ => zonk s f τ
    | none => .var (.fresh n c)
  | _ + 1, .var a => .var a
  | f + 1, .record ρ tl =>
    let ρ' := ρ.map fun p => (p.1, zonk s f p.2)
    match tl with
    | some (.fresh n) =>
      match s.rget n with
      | some (ρ2, tl2) =>
        match zonk s f (.record ρ2 tl2) with
        | .record ρ3 tl3 => .record ((Row.merge ρ' ρ3).getD (Row.modify ρ' ρ3)) tl3
        | τ => τ
      | none => .record ρ' tl
    | _ => .record ρ' tl
  | f + 1, .fn a b => .fn (zonk s f a) (zonk s f b)
  | f + 1, .con as t => .con (as.map (zonk s f)) t

def zonkM (τ : Ty) : Inf Ty := return zonk (← get) fuel0 τ

/-- The head of a type: a type variable's binding followed. -/
def headOf (s : InfState) : Nat → Ty → Ty
  | 0, τ => τ
  | f + 1, .var (.fresh n c) =>
    match s.tget n with
    | some τ => headOf s f τ
    | none => .var (.fresh n c)
  | _, τ => τ

/-- A record type with its tail's bindings followed: all its fields and its last tail. -/
def recOf (s : InfState) : Nat → Row → Option RowVar → Row × Option RowVar
  | 0, ρ, tl => (ρ, tl)
  | f + 1, ρ, some (.fresh n) =>
    match s.rget n with
    | some (ρ2, tl2) => recOf s f ((Row.merge ρ ρ2).getD (Row.modify ρ ρ2)) tl2
    | none => (ρ, some (.fresh n))
  | _, ρ, tl => (ρ, tl)

/-- Two sorted rows: the pairs of types of their common labels, the fields only in the first, the
    fields only in the second; one pass. -/
def rowSplit : Nat → Row → Row → List (Ty × Ty) × Row × Row
  | _, [], ρ2 => ([], [], ρ2)
  | _, ρ1, [] => ([], ρ1, [])
  | 0, ρ1, ρ2 => ([], ρ1, ρ2)
  | f + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 =>
    if l1 = l2 then
      let (c, a, b) := rowSplit f r1 r2
      ((τ1, τ2) :: c, a, b)
    else if labLt l1 l2 then
      let (c, a, b) := rowSplit f r1 ((l2, τ2) :: r2)
      (c, (l1, τ1) :: a, b)
    else
      let (c, a, b) := rowSplit f ((l1, τ1) :: r1) r2
      (c, a, (l2, τ2) :: b)

def occursTy (s : InfState) (n : Nat) (τ : Ty) : Bool :=
  (zonk s fuel0 τ).vars.any fun v => match v with
    | .ty (.fresh m _) => m == n
    | _ => false

def occursRow (s : InfState) (n : Nat) (τ : Ty) : Bool :=
  (zonk s fuel0 τ).vars.any fun v => match v with
    | .row (.fresh m) => m == n
    | _ => false

mutual
/-- B3: refine τ so that it is admissible for κ, pushing classes into arguments. -/
def push : Nat → Cls → Ty → Inf Unit
  | 0, _, _ => throw "fuel"
  | f + 1, κ, τ0 => do
    let τ := headOf (← get) fuel0 τ0
    match κ, τ with
    | .any, _ => return ()
    | _, .var (.fresh n c) =>
      match c.meet κ with
      | none => throw s!"no common class"
      | some c' => if c' == c then return () else do
        let γ ← freshTy c'
        bindTy n γ
    | _, .var a => if a.cls.le κ then return () else throw s!"rigid variable of another class"
    | .num, .con [] t => if t == tInt || t == tFloat then return () else throw "not a number type"
    | .comp, .con [] t =>
      if t == tInt || t == tFloat || t == tChar || t == tString then return () else throw "not comparable"
    | .comp, .con [a] t => if t == tList then push f .comp a else throw "not comparable"
    | .comp, .con [a, b] t => if t == tTuple2 then do push f .comp a; push f .comp b else throw "not comparable"
    | .comp, .con [a, b, c] t =>
      if t == tTuple3 then do push f .comp a; push f .comp b; push f .comp c else throw "not comparable"
    | .app, .con [] t => if t == tString then return () else throw "not appendable"
    | .app, .con [_] t => if t == tList then return () else throw "not appendable"
    | .capp, .con [] t => if t == tString then return () else throw "not compappend"
    | .capp, .con [a] t => if t == tList then push f .comp a else throw "not compappend"
    | _, _ => throw "type not admissible for its class"

def unify : Nat → Ty → Ty → Inf Unit
  | 0, _, _ => throw "fuel"
  | f + 1, τ1, τ2 => do
    let s ← get
    let a := headOf s fuel0 τ1
    let b := headOf s fuel0 τ2
    match a, b with
    | .var (.fresh n c), .var (.fresh m d) =>
      if n == m then return () else
      match c.meet d with
      | none => throw "no common class"
      | some e =>
        if e == d then bindTy n b
        else if e == c then bindTy m a
        else do
          let γ ← freshTy e
          bindTy n γ
          bindTy m γ
    | .var (.fresh n c), .var r => if r.cls.le c then bindTy n (.var r) else throw "rigid variable"
    | .var r, .var (.fresh n c) => if r.cls.le c then bindTy n (.var r) else throw "rigid variable"
    | .var (.fresh n c), τ => bindVar f n c τ
    | τ, .var (.fresh n c) => bindVar f n c τ
    | .var r1, .var r2 => if r1 == r2 then return () else throw "rigid variables differ"
    | .con as t, .con bs t' =>
      if t == t' && as.length == bs.length then unifyList f as bs else throw "type names differ"
    | .fn a1 b1, .fn a2 b2 => do unify f a1 a2; unify f b1 b2
    | .record ρ1 t1, .record ρ2 t2 => unifyRec f ρ1 t1 ρ2 t2
    | _, _ => throw "types differ"

def bindVar : Nat → Nat → Cls → Ty → Inf Unit
  | 0, _, _, _ => throw "fuel"
  | f + 1, n, c, τ => do
    if occursTy (← get) n τ then throw "occurs check"
    push f c τ
    bindTy n τ

def unifyList : Nat → List Ty → List Ty → Inf Unit
  | 0, _, _ => throw "fuel"
  | f + 1, a :: as, b :: bs => do unify f a b; unifyList f as bs
  | _ + 1, _, _ => return ()

def unifyRec : Nat → Row → Option RowVar → Row → Option RowVar → Inf Unit
  | 0, _, _, _, _ => throw "fuel"
  | f + 1, ρ1, t1, ρ2, t2 => do
    let s ← get
    let (r1, e1) := recOf s fuel0 ρ1 t1
    let (r2, e2) := recOf s fuel0 ρ2 t2
    let (common, x1, x2) := rowSplit (r1.length + r2.length + 1) r1 r2
    for (a1, a2) in common do
      unify f a1 a2
    let labels := (r1 ++ x2).map (·.1)
    match e1, e2 with
    | none, none => if x1.isEmpty && x2.isEmpty then return () else throw "record fields differ"
    | none, some (.fresh m) =>
      if !x2.isEmpty then throw "record fields differ" else do
        let st ← get
        if x1.any (fun p => st.lget m |>.contains p.1) then throw "duplicate label"
        bindRow m (x1, none)
    | some (.fresh n), none =>
      if !x1.isEmpty then throw "record fields differ" else do
        let st ← get
        if x2.any (fun p => st.lget n |>.contains p.1) then throw "duplicate label"
        bindRow n (x2, none)
    | some (.fresh n), some (.fresh m) =>
      if n == m then
        if x1.isEmpty && x2.isEmpty then return () else throw "record fields differ"
      else do
        let st ← get
        if x2.any (fun p => st.lget n |>.contains p.1) || x1.any (fun p => st.lget m |>.contains p.1) then
          throw "duplicate label"
        let e3 ← freshRow (dedupL (st.lget n ++ st.lget m ++ labels))
        bindRow n (x2, some e3)
        bindRow m (x1, some e3)
    | some (.fresh n), some r =>
      if !x1.isEmpty then throw "rigid row variable" else do
        let st ← get
        if x2.any (fun p => st.lget n |>.contains p.1) then throw "duplicate label"
        bindRow n (x2, some r)
    | some r, some (.fresh m) =>
      if !x2.isEmpty then throw "rigid row variable" else do
        let st ← get
        if x1.any (fun p => st.lget m |>.contains p.1) then throw "duplicate label"
        bindRow m (x1, some r)
    | some r1', some r2' =>
      if r1' == r2' && x1.isEmpty && x2.isEmpty then return () else throw "rigid row variables differ"
    | some _, none | none, some _ => throw "rigid row variable"
end

def unifyM (τ1 τ2 : Ty) : Inf Unit := unify fuel0 τ1 τ2

end StandardElm.Stat
