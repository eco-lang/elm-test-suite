/-
  A Standard Definition of Elm? Mechanisation: test programs in module form, and their checks as
  statements about the log of the book's evaluation of the program (plan step 3, decisions D4, D9).

  A test is evaluated as the program it is: its modules in the reduced syntax of Chapter 7, the main
  module last, by r:p-dyn-module and r:p-dyn-main, in the test basis Btest (D2). Its checks are
  statements about the log of that evaluation (`ViewChecks`); a test that stops at Debug.todo is a
  program with no meaning (`NoMeaning`, D1).

  `Module.ofSource` applies Appendix A's derived form for modules (sec:appendix-derived-forms-modules)
  to a module's declarations as written; it stands for the derived form until step 8 proves one.
-/
import StandardElmMech.Mod.Complete
import StandardElmMech.Mod.ME0
import StandardElmMech.Checks

namespace StandardElm.Mod
open StandardElm StandardElm.D

/-- t1 = c11 | ... and t2 = ... ; each type has at least one constructor. -/
def conBindOf : List Con → Option ConBind
  | [] => none
  | c :: cs => some (.mk c (conBindOf cs))

def datBindOf : List (TyCon × List Con) → Option DatBind
  | [] => none
  | (t, cs) :: rest =>
    match conBindOf cs with
    | some cb => some (.mk t cb (datBindOf rest))
    | none => datBindOf rest

/-- `topdec1 ; ... ; topdecn`, nested to the right; n ≥ 1. -/
def TopDec.seqOf : List TopDec → Option TopDec
  | [] => none
  | [t] => some t
  | t :: ts => (TopDec.seqOf ts).map (.seq t)

/-- The value declaration of a component of a module's definitions. -/
def groupVal (ds : List Def) (comp : List Nat) : TopDec :=
  .val (comp.map fun i => match ds[i]! with
    | .fn x ps e => (x, lams ps e)
    | .pat _ e => ("", e))

/-- Appendix A's row for modules: the custom types as one group, then the aliases, then the ports
    and the definitions in components ordered by "refers to" (`components`). A port refers to
    nothing, so it is a component alone, and putting the ports before the definitions is one of
    the orders the row allows. -/
def Module.ofSource (h : Header) (written : List Import) (types : List (TyCon × List Con))
    (aliases : List TypBind) (ports : List (Var × Dir × Eff.PTy)) (ds : List Def) : Option Module :=
  let typeDec : List TopDec := match datBindOf types with
    | some db => [.type db]
    | none => []
  let aliasDecs := aliases.map TopDec.alias
  let portDecs := ports.map fun (x, d, τ) => TopDec.port x d τ
  let itemDecs := (components ds).map (groupVal ds)
  (TopDec.seqOf (typeDec ++ aliasDecs ++ portDecs ++ itemDecs)).map (.withDefaults h written)

instance : Inhabited Module := ⟨.withDefaults ⟨false, "Main", .all⟩ [] (.alias ⟨"A", none⟩)⟩

/-! ## A test program in module form -/

/-- The harness import of a view test: `import Html exposing (text)`. -/
def htmlImport : Import := ⟨"Html", "Html", some (.items [.var "text"])⟩

/-- The custom types of a module as the translator writes them, grouped by type. -/
def typesOf (ts : List (String × List (String × Nat))) : List (TyCon × List Con) :=
  ts.map fun (t, cs) => (t, cs.map fun (k, n) => ⟨k, n⟩)

def aliasesOf (as : List (String × Option (List String))) : List TypBind :=
  as.map fun (t, ls) => ⟨t, ls⟩

/-- A helper module of a test program. -/
def _root_.StandardElm.ModSrc.toModule (m : ModSrc) : Module :=
  (Module.ofSource ⟨!m.ports.isEmpty, m.name, m.exposing⟩ m.imports (typesOf m.types)
    (aliasesOf m.aliases) m.ports m.defs).getD default

/-- The main module of a translated test: its header and written imports, its custom types, its
    aliases and its top-level definitions, `main` included, as the test writes them. -/
def _root_.StandardElm.Program.mainModule (p : Program) : Module :=
  (Module.ofSource ⟨!p.ports.isEmpty, p.name, p.exposing⟩ p.imports (typesOf p.types)
    (aliasesOf p.aliases) p.ports p.defs).getD default

/-- The program of a test: its modules in program order, the main module last. -/
def _root_.StandardElm.Program.modules (p : Program) : List Module :=
  p.helpers.map ModSrc.toModule ++ [p.mainModule]

/-! ## The statements -/

/-- A view program: some derivation of the book's evaluation of the program, in basis B, has a log
    that meets every check. -/
def ViewChecks (B : Basis) (p : List Module) (cs : List LogCheck) : Prop :=
  ∃ v l, EvalProgramL B p v l ∧ ∀ c ∈ cs, c.Holds l

/-- The program has no meaning (r:p-dyn-main's comment: a top-level value with no value). -/
def NoMeaning (B : Basis) (p : List Module) : Prop := ¬ ∃ v, EvalProgram B p v

def viewChecksB (o : Oracle) (B : Basis) (p : List Module) (cs : List LogCheck) : Bool :=
  match evProgram o fuelT B p 0 with
  | ⟨.value _, l, _⟩ => cs.all (·.check l)
  | _ => false

def stuckB (B : Basis) (p : List Module) : Bool :=
  match evProgram (.const false) fuelT B p 0 with
  | ⟨.stuck, _, 0⟩ => true
  | _ => false

theorem viewChecks_sound {o : Oracle} {B : Basis} {p : List Module} {cs : List LogCheck} :
    viewChecksB o B p cs = true → ViewChecks B p cs := by
  unfold viewChecksB
  split
  · rename_i v l k h; intro hc
    exact ⟨v, l, evProgram_sound_l h, fun c hm => LogCheck.check_sound (List.all_eq_true.mp hc c hm)⟩
  · intro h; cases h

theorem noMeaning_sound {B : Basis} {p : List Module} : stuckB B p = true → NoMeaning B p := by
  unfold stuckB
  split
  · rename_i l h; intro _; exact noMeaning_of_stuck h
  · intro h; cases h

/-- When the evaluator reads no choice, the checks hold of every derivation's log, not only of some
    (from evProgram_unique_l): the existential of D9 is then also universal. -/
theorem viewChecks_every {o : Oracle} {B : Basis} {p : List Module} {cs : List LogCheck} {v : Val}
    {l : Log} (h : evProgram o fuelT B p 0 = ⟨.value v, l, 0⟩) (hc : cs.all (·.check l) = true) :
    ∀ v' l', EvalProgramL B p v' l' → ∀ c ∈ cs, c.Holds l' := by
  intro v' l' d c hm
  obtain ⟨_, rfl⟩ := evProgram_unique_l h v' l' d
  exact LogCheck.check_sound (List.all_eq_true.mp hc c hm)

end StandardElm.Mod
