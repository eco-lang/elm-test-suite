/-
  A Standard Definition of Elm? Mechanisation: type erasure, plan step 10 (Lean definitions,
  "Erasure, payload types, Dflt, main").

  The reduced syntax of Chapter 7 (sec:dynamic-modules-reduced) keeps of the type declarations only
  the constructors with their arities and the labels of record aliases, and of a port its direction
  and payload type, as elaboration records them (fig:static-modules-port, converted to Part I's
  `Eff.PTy`). The kind of `main` and the flags type of a worker are read from the scheme of `main`
  (r:p-stat-main-program, r:p-stat-main-view, with step 9's `dflt`).

  The custom types and the aliases of a module are listed by name (the order of `Dict`, which is
  the translator's): their order has no dynamic content, and one fixed order makes the comparison
  of reduced programs independent of it.
-/
import StandardElmMech.Stat.Program
import StandardElmMech.Mod.Reduced

namespace StandardElm.Stat
open StandardElm (Var Lab ModId)
open StandardElm.Src (BTy BTyRow BDatBind BTypBind)

/-! ## Payload types (fig:static-modules-port) -/

mutual
/-- A type of `Port` as a payload type; `none` exactly when `Port` fails. Rows are sorted by label,
    so a record's fields come out sorted (`Eff.PTy`'s convention). -/
def toPTy : Ty → Option Eff.PTy
  | .con [] t =>
    if t = tInt then some .int
    else if t = tFloat then some .float
    else if t = tBool then some .bool
    else if t = tString then some .string
    else if t = tBytes then some .bytes
    else if t = tUnit then some .unit
    else if t = tValue then some .value
    else none
  | .con [τ] t =>
    if t = tList then (toPTy τ).map .list
    else if t = tMaybe then (toPTy τ).map .maybe
    else if t = tArray then (toPTy τ).map .array
    else none
  | .con [τ1, τ2] t =>
    if t = tTuple2 then
      match toPTy τ1, toPTy τ2 with
      | some p1, some p2 => some (.tuple2 p1 p2)
      | _, _ => none
    else none
  | .con [τ1, τ2, τ3] t =>
    if t = tTuple3 then
      match toPTy τ1, toPTy τ2, toPTy τ3 with
      | some p1, some p2, some p3 => some (.tuple3 p1 p2 p3)
      | _, _, _ => none
    else none
  | .record ρ none => (toPFields ρ).map .record
  | _ => none
def toPFields : Row → Option Eff.PFields
  | [] => some .nil
  | (l, τ) :: rest =>
    match toPTy τ, toPFields rest with
    | some p, some r => some (.cons l p r)
    | _, _ => none
end

/-! ## The kind of `main` -/

/-- What r:p-stat-main-program and r:p-stat-main-view need of the scheme of main, as Part I
    records it: a worker with its flags type when σ's body is (τ1, τ2, τ3)Program with Port(τ1),
    taken before the default; a view when Dflt σ = τ Node. The flags type of a view is not read
    (step 5); it is `.unit` here and in the translator. -/
def mainKind (σ : Scheme) : Option (Mod.ProgKind × Eff.PTy) :=
  match σ.body with
  | .con [τ1, _, _] t =>
    if t = tProgram then (toPTy τ1).map (.worker, ·)
    else match dflt σ with
      | .con [_] t' => if t' = tNode then some (.view, .unit) else none
      | _ => none
  | _ => match dflt σ with
    | .con [_] t => if t = tNode then some (.view, .unit) else none
    | _ => none

/-! ## Type declarations -/

/-- The labels of a record type expression, in the order written. -/
def rowLabels : BTyRow → List Lab
  | .field l _ none => [l]
  | .field l _ (some rest) => l :: rowLabels rest

/-- r:dm-typbind's reading of an alias: the labels of a closed record alias, in the order written;
    `none` for any other alias (it binds no record constructor). -/
def aliasLabels : BTy → Option (List Lab)
  | .record none => some []
  | .record (some row) => some (rowLabels row)
  | _ => none

/-- Insertion by name (the order of labels, `labLt`). -/
def insertByName {α : Type} (key : α → String) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if labLt (key x) (key y) then x :: y :: ys else y :: insertByName key x ys

def sortByName {α : Type} (key : α → String) : List α → List α
  | [] => []
  | x :: xs => insertByName key x (sortByName key xs)

/-- The custom types of a datbind: each with its constructors and their arities. -/
def eraseDatBind (db : Option BDatBind) : List (Mod.TyCon × List Con) :=
  (db.getD []).map fun (c, _, cs) => (c, cs.map fun (k, ts) => ⟨k, ts.length⟩)

def eraseTypBinds (tbs : List BTypBind) : List Mod.TypBind :=
  tbs.map fun tb => ⟨tb.c, aliasLabels tb.t⟩

def Dir.toMod : Dir → Mod.Dir
  | .out => .out
  | .inn => .inn

/-- A port of the module's port environment as the reduced syntax writes it; `none` when it is not
    in PE or its payload type is not one of `Port`. -/
def erasePort (PE : PortEnv) (x : Var) : Option (Var × Mod.Dir × Eff.PTy) :=
  match PE.find? x with
  | some (d, τ) => (toPTy τ).map fun π => (x, d.toMod, π)
  | none => none

end StandardElm.Stat
