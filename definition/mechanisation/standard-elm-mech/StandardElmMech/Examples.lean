/-
  A Standard Definition of Elm? Mechanisation, part 10.
  The examples: the structure of a translated test program.

  The examples are the test programs of this repository's tests/ tagged elm-spec, translated into
  Lean by definition/tools/src/Translate.elm, which writes them to Generated/ (one file per shard of
  at most 40 programs). A program is its custom types and its top-level definitions, `main`
  included, in bare syntax built with the derived-form functions of Derived.lean; Mod/Program.lean
  makes the program's modules of them (plan step 3). Every integer constant is at Int or Float by
  the book's number specialisation, the translator making the copies of declarations used at both
  (a name with `$`, `incF$Float`). Its checks are its CHECK lines as written, each with the kind of
  the value the translator inferred for its label; Theorems.lean states them as statements about
  the log of the program's evaluation (decision D9).
-/
import StandardElmMech.Basis
import StandardElmMech.Show
import StandardElmMech.Mod.Syntax

namespace StandardElm
open StandardElm.D

/-- What a check's value is, from the translator's inference: the kernel can
    compare an Int, a string and a constructor without arguments; a float is
    compared as printed. `unknown` is a hand-written check, whose kind is read
    from its expected value (`kernelCheck?` in Theorems.lean). -/
inductive CheckKind where
  | unknown | int | float | string | char | data | function
  deriving Inhabited, BEq, Repr

/-- The directive of a CHECK line: CHECK and CHECK-DAG (D9 reads CHECK-DAG as CHECK), CHECK-NEXT,
    CHECK-SAME, CHECK-NOT (only in a test that stops with EXIT 1). -/
inductive LineKind where
  | check | next | same | not_
  deriving Inhabited, BEq, Repr

/-- A CHECK line of a test, as written, with the kind of the value logged under its label. -/
structure Check where
  line : LineKind := .check
  text : String
  kind : CheckKind := .unknown
  deriving Inhabited

/-- Whether the line's pattern has a regular expression, `{{...}}`. -/
def Check.isRegex (ck : Check) : Bool := (ck.text.splitOn "{{").length > 1

/-- The label of a line: the text before its first `": "`, or the whole text; a regular expression's
    line is its whole pattern. -/
def Check.label (ck : Check) : String :=
  if ck.isRegex then ck.text else
  match ck.text.splitOn ": " with
  | l :: _ :: _ => l
  | _ => ck.text

/-- The value a line states: the text after its first `": "`; "" for a label or a pattern. -/
def Check.expected (ck : Check) : String :=
  if ck.isRegex then "" else
  match ck.text.splitOn ": " with
  | _ :: rest@(_ :: _) => ": ".intercalate rest
  | _ => ""

/-- Whether the line names a label only (no `": "`). -/
def Check.labelOnly (ck : Check) : Bool := !ck.isRegex && (ck.text.splitOn ": ").length == 1

/-- A helper module of a test program (one it imports from its project's sources): its name and
    file, its header's exposing list and written imports, its custom types, aliases and top-level
    definitions, as for the main module below. -/
instance : Inhabited Mod.ExpList := ⟨.all⟩

structure ModSrc where
  name : String
  path : String
  exposing : Mod.ExpList
  imports : List Mod.Import := []
  types : List (String × List (String × Nat)) := []
  aliases : List (String × Option (List String)) := []
  ports : List (String × Mod.Dir × Eff.PTy) := []
  defs : List Def := []
  deriving Inhabited

structure Program where
  name : String
  /-- Where the implementation's result comes from. -/
  source : String := "tests/elm/src"
  /-- Whether the program uses a basic value whose result only the C library
      computes (`Float.floor`, the elementary functions, `Float.pow`, float
      printing), which the kernel cannot reduce: its checks are then decided
      by `native_decide` only. -/
  native : Bool := false
  /-- The main module's header's exposing list and its written imports. -/
  exposing : Mod.ExpList := .items [.var "main"]
  imports : List Mod.Import := [⟨"Html", "Html", some (.items [.var "text"])⟩]
  /-- The custom types, each with its constructors and their arities. -/
  types : List (String × List (String × Nat)) := []
  /-- The type aliases, each with the labels of its closed record in the order written, or `none`
      (the alias binds a record constructor only in the first case, r:dm-typbind). -/
  aliases : List (String × Option (List String)) := []
  /-- The ports, each with its direction and payload type (as elaboration records them). -/
  ports : List (String × Mod.Dir × Eff.PTy) := []
  /-- The top-level definitions, `main` included, in the order written. -/
  defs : List Def := []
  /-- The helper modules, in program order (each after the modules it imports). -/
  helpers : List ModSrc := []
  checks : List Check
  /-- false: the test expects the program to stop (EXIT 1 with CHECK-NOT lines). -/
  meaning : Bool := true
  deriving Inhabited

/-- A CHECK line written by the translator. -/
def chk (line : LineKind) (text : String) (kind : CheckKind) : Check :=
  { line := line, text := text, kind := kind }

/-! ## Shorthands -/
def T : Exp := c "True"
def F : Exp := c "False"
def eq (a b : Exp) := bin "==" a b
def lst (ns : List Int) : Exp := listE (ns.map i)

/-! ## Partial hand translations -/

/-- An integer constant at Float, after number specialisation. -/
def fI (n : Nat) : Exp := .atexp (.scon (.intF n))

/-- The float constant 0.5. -/
def fHalf : Exp := .atexp (.scon (.float 5 (-1)))


/-- Hand translations of tests the translator refuses but which can be
    translated in part. There are none at present: the last,
    StandardA48MinMaxNanTest, translates whole since isNaN is encoded. -/
def handPartial : List Program := []

end StandardElm
