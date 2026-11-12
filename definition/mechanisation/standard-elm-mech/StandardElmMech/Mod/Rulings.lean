/-
  A Standard Definition of Elm? Mechanisation: rulings of Chapter 7 and of Chapter 9's dynamic rules,
  on programs written by hand, plan step 2. Each statement is about the rules; the proofs run the
  evaluator (by the kernel) and use its soundness. [params] [harness] where Html.text occurs.
-/
import StandardElmMech.Mod.ME0
import StandardElmMech.Checks

namespace StandardElm.Mod
open StandardElm StandardElm.D

/-- The program evaluates, in the oracle's choices, to a value meeting `x`. -/
def programValueB (o : Oracle) (B : Basis) (p : List Module) (x : Expect) : Bool :=
  match evProgram o fuelT B p 0 with
  | ⟨.value v, _, _⟩ => x.check v
  | _ => false

theorem programValue_sound {o : Oracle} {B : Basis} {p : List Module} {x : Expect} :
    programValueB o B p x = true → ∃ v, EvalProgram B p v ∧ x.holds v := by
  unfold programValueB; split
  · rename_i v l k h; intro hx; exact ⟨v, evProgram_sound (by rw [h]), hx⟩
  · intro h; cases h

/-- A82: `main` need not be exposed. The module exposes only `other`; its `main` is still the
    program's value, taken from the module's own VE (r:p-dyn-main). [harness] [params] -/
def mA82 : Module :=
  .withDefaults ⟨false, "Main", .items [.var "other"]⟩ [⟨"Html", "Html", some (.items [.var "text"])⟩]
    (.seq (.val [("other", i 1)]) (.val [("main", .app (v "text") (strA "ok"))]))

theorem a82_main_not_exposed :
    ∃ w, EvalProgram (Btest []) [mA82] w ∧ (Expect.con "node#" [.str "ok"]).holds w :=
  programValue_sound (o := .const false) (by decide +kernel)

/-- A38: two modules, A binding a and x, B binding b and x. -/
def B38 : Basis := fmPlus (Btest []) [("A", .ofVE [("a", .int 1), ("x", .int 10)]),
                                      ("B", .ofVE [("b", .int 2), ("x", .int 20)])]

/-- A38: two imports that give the same qualifier merge under it (sec:dynamic-modules-merge). -/
theorem a38_shared_qualifier_merge :
    ∃ E, EvalImports B38 [⟨"A", "Q", none⟩, ⟨"B", "Q", none⟩] E ∧
         E.lookup ⟨some "Q", "a"⟩ = some (.int 1) ∧ E.lookup ⟨some "Q", "b"⟩ = some (.int 2) :=
  ⟨_, evImports_sound rfl, rfl, rfl⟩

/-- A38: where two imports expose the same name, the later import's binding is kept. -/
theorem a38_later_import_kept :
    ∃ E, EvalImports B38 [⟨"A", "A", some (.items [.var "x"])⟩, ⟨"B", "B", some (.items [.var "x"])⟩] E ∧
         E.lookup ⟨none, "x"⟩ = some (.int 20) :=
  ⟨_, evImports_sound rfl, rfl⟩

/-- A38: both imports expose x, the module never uses it, and the program has a meaning.
    [harness] [params] -/
theorem a38_ambiguous_unused :
    ∃ w, EvalProgram B38 [.withDefaults ⟨false, "Main", .items [.var "main"]⟩
        [⟨"A", "A", some (.items [.var "x"])⟩, ⟨"B", "B", some (.items [.var "x"])⟩,
         ⟨"Html", "Html", some (.items [.var "text"])⟩]
        (.val [("main", .app (v "text") (strA "ok"))])] w ∧ (Expect.con "node#" [.str "ok"]).holds w :=
  programValue_sound (o := .const false) (by decide +kernel)

/-- A28: a module A with `type Maybe = Just Int Int | Nothing`, exposing Maybe(..). -/
def VE_A28 : ValEnv := [("Just", .con ⟨"Just", 2⟩ []), ("Nothing", .con ⟨"Nothing", 0⟩ [])]
def I_A28 : Interface := ⟨[], [("Maybe", VE_A28)], VE_A28⟩

/-- A28: a written import replaces what a default import exposes: after
    `import A exposing (Maybe(..))`, `Just` is A's constructor, of arity 2. -/
theorem a28_written_import_replaces_default :
    ∃ E, EvalImports (fmPlus (Btest []) [("A", I_A28)])
           (defaultImports ++ [⟨"A", "A", some (.items [.opened "Maybe"])⟩]) E ∧
         E.lookup ⟨none, "Just"⟩ = some (.con ⟨"Just", 2⟩ []) :=
  ⟨_, evImports_sound rfl, rfl⟩

end StandardElm.Mod
