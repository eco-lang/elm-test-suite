/-
  A Standard Definition of Elm? Mechanisation: the reduced syntax of Modules (dynamic-modules.tex,
  sec:dynamic-modules-reduced), plan step 2.

  Type annotations, type-variable sequences and the types of constructor arguments are gone; a
  constructor carries its arity (in `Con`); a record alias keeps its labels in the order written; a
  port keeps its direction and payload type, as elaboration records them; `import M` is read
  `import M as M`; and the imports of a module are the default imports followed by the written
  ones. A top-level value group is a list of pairs (the rule needs its variables and right-hand
  sides apart).
-/
import StandardElmMech.Objects

namespace StandardElm.Mod
open StandardElm StandardElm.Eff

abbrev TyCon := String

inductive Dir where
  | out | inn
  deriving Repr, DecidableEq

inductive ExpItem where
  /-- var: a value or a port; after number specialisation one item per copy -/
  | var (x : Var)
  /-- (opv) -/
  | op (o : Op)
  /-- tycon -/
  | tycon (t : TyCon)
  /-- tycon(..) -/
  | opened (t : TyCon)
  deriving Repr, DecidableEq

inductive ExpList where
  /-- (..) -/
  | all
  /-- ( expitem1 , ... , expitemn ), n ≥ 1 -/
  | items (is : List ExpItem)
  deriving Repr, DecidableEq

structure Header where
  /-- the word `port`: no dynamic content (r:dm-header's comment) -/
  isPort : Bool
  modid : ModId
  exposing : ExpList
  deriving Repr

/-- import modid as qual [exposing explist]. -/
structure Import where
  modid : ModId
  qual : ModId
  exposing : Option ExpList
  deriving Repr

/-- con [| conbind]. -/
inductive ConBind where
  | mk (c : Con) (rest : Option ConBind)
  deriving Repr

/-- tycon = conbind [and datbind]. -/
inductive DatBind where
  | mk (t : TyCon) (cb : ConBind) (rest : Option DatBind)
  deriving Repr

/-- tycon [= {lab1, ..., labn}]: `some ls` for a record alias, its labels in the order written. -/
structure TypBind where
  tycon : TyCon
  labels : Option (List Lab)
  deriving Repr

inductive TopDec where
  /-- var1 = exp1 and ... and varn = expn, n ≥ 1 -/
  | val (vb : List (Var × Exp))
  /-- type datbind -/
  | type (db : DatBind)
  /-- type alias typbind -/
  | alias (tb : TypBind)
  /-- port var : (dir, τ) -/
  | port (x : Var) (d : Dir) (τ : PTy)
  /-- topdec1 ; topdec2 -/
  | seq (t1 t2 : TopDec)
  deriving Repr

structure Module where
  header : Header
  /-- the default imports followed by the written ones -/
  imports : List Import
  body : TopDec
  deriving Repr

/-- Figure fig:default-imports (syntax-modules.tex), in its order. -/
def defaultImports : List Import :=
  [ ⟨"Basics", "Basics", some .all⟩,
    ⟨"Debug", "Debug", none⟩,
    ⟨"List", "List", some (.items [.op "::"])⟩,
    ⟨"Maybe", "Maybe", some (.items [.opened "Maybe"])⟩,
    ⟨"Result", "Result", some (.items [.opened "Result"])⟩,
    ⟨"String", "String", some (.items [.tycon "String"])⟩,
    ⟨"Char", "Char", some (.items [.tycon "Char"])⟩,
    ⟨"Tuple", "Tuple", none⟩,
    ⟨"Platform", "Platform", some (.items [.tycon "Program"])⟩,
    ⟨"Platform.Cmd", "Cmd", some (.items [.tycon "Cmd"])⟩,
    ⟨"Platform.Sub", "Sub", some (.items [.tycon "Sub"])⟩ ]

/-- A module with the default imports before its written ones. -/
def Module.withDefaults (h : Header) (written : List Import) (body : TopDec) : Module :=
  ⟨h, defaultImports ++ written, body⟩

end StandardElm.Mod
