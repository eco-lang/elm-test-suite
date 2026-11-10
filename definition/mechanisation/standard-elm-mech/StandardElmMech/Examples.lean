/-
  A Standard Definition of Elm? Mechanisation, part 10.
  The examples: the structure of a translated test program, and the partial
  hand translations.

  The examples are the test programs of this repository's tests/ tagged
  elm-spec, translated into Lean by definition/tools/src/Translate.elm, which
  writes them to Generated/ (one file per shard of at most 40 programs). Each
  `Check` is one `Debug.log "label" (exp)` of a program, in bare syntax built
  with the derived-form functions of Derived.lean, with the expected value
  copied from the program's `-- CHECK: label: value` line (`(no value)` for a
  `-- CHECK-NOT: label:` in a test that stops at Debug.todo) and the kind of
  that value, from the translator's inference. Every integer constant is at
  Int or Float by the book's number specialisation, the translator making the
  copies of declarations used at both (a name with `$`, `incF$Float`).

  A test the translator refuses, but whose checks the encoding can partly
  express, may be translated in part by hand here (`handPartial`).

  Top-level definitions of a module are placed in a `let` around the logged
  expression (grouped into components as for a let, which is what the module
  row of Appendix A does for definitions), and so are the other declarations
  of main's let; the custom types' constructors are bound in the environment.
  Both stand in for Chapter 7 (out of scope).
-/
import StandardElmMech.Basis
import StandardElmMech.Show

namespace StandardElm
open StandardElm.D

/-- What a check's value is, from the translator's inference: the kernel can
    compare an Int, a string and a constructor without arguments; a float is
    compared as printed. `unknown` is a hand-written check, whose kind is read
    from its expected value (`kernelCheck?` in Theorems.lean). -/
inductive CheckKind where
  | unknown | int | float | string | char | data | function
  deriving Inhabited, BEq, Repr

structure Check where
  label : String
  /-- The value of the CHECK line (the implementation's result). -/
  expected : String
  expr : Exp
  kind : CheckKind := .unknown
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
  cons : List (String × Nat) := []
  defs : List Def := []
  locals : List Def := []
  checks : List Check
  deriving Inhabited

/-- The phrase evaluated for a check: the program's definitions around
    `Debug.log "label" (exp)`. -/
def Program.phrase (p : Program) (ck : Check) : Exp :=
  letDefs p.defs (letDefs p.locals (debugLog ck.label ck.expr))

def Program.env (p : Program) : Env := E0with p.cons

def ck (label expected : String) (e : Exp) : Check :=
  { label := label, expected := expected, expr := e }

/-- A check written by the translator, with the kind of its value. -/
def ckk (label expected : String) (kind : CheckKind) (e : Exp) : Check :=
  { label := label, expected := expected, expr := e, kind := kind }

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
