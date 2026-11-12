/-
  A Standard Definition of Elm? Mechanisation: short constructors of the source syntax, for the
  Generated files (plan step 8), and the canonical order of a program's modules (`canonOrder`):
  the modules in a topological order of their imports, ties by module name, the given main module
  last. The translator writes each program wrapped in `canonOrder`, so that the theorem about the
  set of modules and the one about the sequence agree.
-/
import StandardElmMech.Src.Syntax

namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)

def prog (project name : String) (ms : List SModule) : SProgram := ⟨project, name, ms⟩
def mdl (h : SHeader) (imps : List SImport) (ds : List STopDec) : SModule := ⟨h, imps, ds⟩
def hdr (isPort : Bool) (name : ModId) (ex : SExposing) : SHeader := ⟨isPort, name, ex⟩
def imp (m : ModId) (a : Option ModId) (ex : Option SExposing) : SImport := ⟨m, a, ex⟩

/-- A top-level value definition. -/
def val (x : Var) (ann : Option STy) (ps : List SPat) (e : SExp) : STopDec := .value (.fn x ann ps e)

/-! Expressions -/
def v (x : Var) : SExp := .var ⟨none, x⟩
def qv (m : ModId) (x : Var) : SExp := .var ⟨some m, x⟩
def c (k : String) : SExp := .con ⟨none, k⟩
def qc (m : ModId) (k : String) : SExp := .con ⟨some m, k⟩
def i (n : Nat) : SExp := .lit (.int n)
def fl (m : Nat) (e : Int) : SExp := .lit (.float m e)
def ch (x : Char) : SExp := .lit (.char x)
def str (s : String) : SExp := .lit (.str s)
def app (f : SExp) (args : List SExp) : SExp := .app f args
def bin (o : Op) (l r : SExp) : SExp := .binop o l r

/-! Patterns -/
def pv (x : Var) : SPat := .var x
def pc (k : String) (args : List SPat) : SPat := .con ⟨none, k⟩ args
def pqc (m : ModId) (k : String) (args : List SPat) : SPat := .con ⟨some m, k⟩ args

/-! Types -/
def tc (t : String) (args : List STy) : STy := .con ⟨none, t⟩ args
def tq (m : ModId) (t : String) (args : List STy) : STy := .con ⟨some m, t⟩ args
def tv (a : String) : STy := .var a

/-! The canonical order of modules -/

/-- The modules a module imports, by name. -/
def SModule.importNames (m : SModule) : List ModId := m.imports.map (·.mod)

/-- Among `rest`, the module with the least name that imports none of the others of `rest`. -/
def nextReady (rest : List SModule) : Option SModule :=
  let names := rest.map (·.header.name)
  let ready := rest.filter fun m => m.importNames.all fun n => !(names.contains n) || n == m.header.name
  ready.foldl (fun acc m => match acc with
    | none => some m
    | some a => if decide (m.header.name < a.header.name) then some m else some a) none

/-- Kahn's algorithm with fuel: a topological order of `rest` by imports, ties by name; on a
    cycle, the remaining modules in their given order. -/
def topoOrder : Nat → List SModule → List SModule
  | 0, rest => rest
  | n + 1, rest =>
    match nextReady rest with
    | some m => m :: topoOrder n (rest.filter fun x => x.header.name != m.header.name)
    | none => rest

/-- The canonical order: the modules but the main one in a topological order of imports (ties by
    module name), the given main module last. -/
def canonOrder (p : SProgram) : SProgram :=
  match p.modules.getLast? with
  | some main =>
    let others := p.modules.dropLast
    { p with modules := topoOrder others.length others ++ [main] }
  | none => p

end StandardElm.Src
