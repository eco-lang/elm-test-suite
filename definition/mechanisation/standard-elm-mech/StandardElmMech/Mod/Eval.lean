/-
  A Standard Definition of Elm? Mechanisation: an executable evaluator for the rules of Chapter 7 and
  the dynamic rules of Chapter 9 for a program's modules, plan step 2.

  The parts that evaluate no expression (exposing items and lists, headers, imports, the bindings of
  types) are functions. The others thread the oracle, the log and the index of the next choice as
  the Core's evaluator does (Eval.lean), with the Core's fuel passed to every Core call; they recurse
  on syntax.
-/
import StandardElmMech.Mod.RulesL
import StandardElmMech.Eval

namespace StandardElm.Mod
open StandardElm StandardElm.Eff

def evExpItem (I : Interface) : ExpItem → Option Interface
  | .var x => (fmLookup I.VE x).map fun v => .ofVE [(x, v)]
  | .op _ => some .empty
  | .tycon t =>
      if t ∈ I.RA then (fmLookup I.VE t).map fun v => ⟨[t], [], [(t, v)]⟩
      else some ⟨[], if (fmLookup I.CE t).isSome then [(t, [])] else [], []⟩
  | .opened t => (fmLookup I.CE t).map fun VE => ⟨[], [(t, VE)], VE⟩

def evExpItems (I : Interface) : List ExpItem → Option (List Interface)
  | [] => some []
  | it :: is =>
    match evExpItem I it, evExpItems I is with
    | some I1, some Is => some (I1 :: Is)
    | _, _ => none

def evExpList (I : Interface) : ExpList → Option Interface
  | .all => some I
  | .items [] => none
  | .items is => (evExpItems I is).map Interface.sum

def evExpListOpt (I : Interface) : Option ExpList → Option (Option Interface)
  | none => some none
  | some el => (evExpList I el).map some

def evHeader (I : Interface) (h : Header) : Option (ModId × Interface) :=
  (evExpList I h.exposing).map fun I' => (h.modid, I')

def evImports (B : Basis) : List Import → Option Env
  | [] => some (.mk [] [])
  | ⟨m, q, el⟩ :: rest =>
    match fmLookup B m with
    | some I =>
      match evExpListOpt I el, evImports B rest with
      | some I', some E => some (Env.merge (.mk [(q, .mk [] I.VE)] (unqualified I')) E)
      | _, _ => none
    | none => none

mutual
def evConBind : ConBind → ValEnv
  | .mk c rest => fmPlus [(c.name, .con c [])] (evConBindOpt rest)
def evConBindOpt : Option ConBind → ValEnv
  | none => []
  | some cb => evConBind cb
end

mutual
def evDatBind : DatBind → ConEnv × ValEnv
  | .mk t cb rest =>
    let VE := evConBind cb
    let (CE', VE') := evDatBindOpt rest
    (fmPlus [(t, VE)] CE', fmPlus VE VE')
def evDatBindOpt : Option DatBind → ConEnv × ValEnv
  | none => ([], [])
  | some db => evDatBind db
end

def evTypBind (tb : TypBind) : List TyCon × ValEnv :=
  (match tb.labels with | none => [] | some _ => [tb.tycon],
   match tb.labels with | none => [] | some ls => [(tb.tycon, recordCtor ls)])

def evForces (o : Oracle) (n : Nat) (E : Env) : List Var → Nat → Res (List Val)
  | [], k => ⟨.value [], [], k⟩
  | y :: ys, k =>
    match evExp o n E (forceExp y) k with
    | ⟨.value v, l1, k1⟩ =>
      match evForces o n E ys k1 with
      | ⟨.value vs, l2, k2⟩ => ⟨.value (v :: vs), l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evTopDec (o : Oracle) (n : Nat) : Env → TopDec → Nat → Res Interface
  | E, .val vb, k =>
    if vb = [] then ⟨.stuck, [], k⟩ else
    match evValBind o n E (thunkGroup vb) k with
    | ⟨.value VE, l1, k1⟩ =>
      match evForces o n (E.plusVE (recVE VE)) (vb.map (thunkVar ∘ Prod.fst)) k1 with
      | ⟨.value vs, l2, k2⟩ => ⟨.value (.ofVE ((vb.map Prod.fst).zip vs)), l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
  | _, .type db, k => ⟨.value ⟨[], (evDatBind db).1, (evDatBind db).2⟩, [], k⟩
  | _, .alias tb, k => ⟨.value ⟨(evTypBind tb).1, [], (evTypBind tb).2⟩, [], k⟩
  | _, .port x .out τ, k => ⟨.value (.ofVE [(x, .basApp (.outport x τ) [])]), [], k⟩
  | _, .port x .inn τ, k => ⟨.value (.ofVE [(x, .basApp (.inport x τ) [])]), [], k⟩
  | E, .seq t1 t2, k =>
    match evTopDec o n E t1 k with
    | ⟨.value I1, l1, k1⟩ =>
      match evTopDec o n (E.plusVE I1.VE) t2 k1 with
      | ⟨.value I2, l2, k2⟩ => ⟨.value (Interface.plus I1 I2), l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

def evModule (o : Oracle) (n : Nat) (B : Basis) (m : Module) (k : Nat) : Res (Basis × ValEnv) :=
  match evImports B m.imports with
  | some E =>
    match evTopDec o n (E0base.plusEnv E) m.body k with
    | ⟨.value I, l1, k1⟩ =>
      match evHeader I m.header with
      | some (mid, I') => ⟨.value ([(mid, I')], I.VE), l1, k1⟩
      | none => ⟨.stuck, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
  | none => ⟨.stuck, [], k⟩

def evProgram (o : Oracle) (n : Nat) : Basis → List Module → Nat → Res Val
  | _, [], k => ⟨.stuck, [], k⟩
  | B, [m], k =>
    match evModule o n B m k with
    | ⟨.value (_, VE), l1, k1⟩ =>
      match fmLookup VE "main" with
      | some v => ⟨.value v, l1, k1⟩
      | none => ⟨.stuck, l1, k1⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩
  | B, m :: p, k =>
    match evModule o n B m k with
    | ⟨.value (B', _), l1, k1⟩ =>
      match evProgram o n (fmPlus B B') p k1 with
      | ⟨.value v, l2, k2⟩ => ⟨.value v, l1 ++ l2, k2⟩
      | ⟨.stuck, l2, k2⟩ => ⟨.stuck, l1 ++ l2, k2⟩
      | ⟨.outOfFuel, l2, k2⟩ => ⟨.outOfFuel, l1 ++ l2, k2⟩
    | ⟨.stuck, l1, k1⟩ => ⟨.stuck, l1, k1⟩
    | ⟨.outOfFuel, l1, k1⟩ => ⟨.outOfFuel, l1, k1⟩

end StandardElm.Mod
