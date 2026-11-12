/-
  A Standard Definition of Elm? Mechanisation: the 27 syntactic restrictions decidable on a syntax
  tree (sec:syntax-core-restrictions, sec:syntax-modules-restrictions, sec:programs-syntax), plan
  step 8, section 5.

  Each restriction is a `Prop` stated as the book states it, over the source syntax; each is
  decidable by instances that the kernel reduces (lists, `Nodup`, bounded quantifiers, and
  `Graph.Plus` through its proved decider), so its decider is `decide`, and `decR_iff` is
  `decide_eq_true_iff`. `ModuleOK` is the conjunction of the 22 module restrictions, `ProgramOK`
  of the five program restrictions, `SynOK` of both. The nine restrictions about characters,
  tokens and layout (`res:core-escape-unicode`, ..., `res:modules-header`) are trusted to the
  parser ([parse]) and are not stated.
-/
import StandardElmMech.Src.Traverse
import StandardElmMech.Src.Graph

namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)

/-! ## Module facts -/

def SModule.vals (m : SModule) : List Var :=
  m.decls.flatMap fun d => match d with
    | .value d => d.bound
    | _ => []

def SModule.ports (m : SModule) : List Var :=
  m.decls.flatMap fun d => match d with
    | .port x _ => [x]
    | _ => []

def SModule.customs (m : SModule) : List String :=
  m.decls.flatMap fun d => match d with
    | .custom c _ _ => [c]
    | _ => []

def SModule.aliases (m : SModule) : List String :=
  m.decls.flatMap fun d => match d with
    | .alias c _ _ => [c]
    | _ => []

def SModule.ctors (m : SModule) : List String :=
  m.decls.flatMap fun d => match d with
    | .custom _ _ cs => cs.map (·.1)
    | _ => []

/-- The aliases whose body is a record type without extension variable (they bind a
    constructor). -/
def SModule.recAliases (m : SModule) : List String :=
  m.decls.flatMap fun d => match d with
    | .alias c _ (.record _) => [c]
    | _ => []

/-- The value declarations, in order. -/
def SModule.valueDecls (m : SModule) : List SDef :=
  m.decls.flatMap fun d => match d with
    | .value d => [d]
    | _ => []

/-- The aliases, with their bodies, in order. -/
def SModule.aliasDecls (m : SModule) : List (String × STy) :=
  m.decls.flatMap fun d => match d with
    | .alias c _ t => [(c, t)]
    | _ => []

/-- The 19 module identifiers of Dom ME0 (Appendix C, sec:appendix-static-basis-modenv). -/
def basisModuleIds : List ModId :=
  ["Basics", "List", "Maybe", "Result", "String", "Char", "Tuple", "Array", "Bytes", "Debug",
   "Platform", "Platform.Cmd", "Platform.Sub", "Task", "Process", "Json.Encode", "Json.Decode",
   "VirtualDom", "Html"]

/-- The modules the default imports name (Figure fig:default-imports). -/
def defaultImportMods : List ModId :=
  ["Basics", "Debug", "List", "Maybe", "Result", "String", "Char", "Tuple", "Platform",
   "Platform.Cmd", "Platform.Sub"]

/-- The managers of the platform: none ([params]). -/
def managersPlat : List Var := []

/-! ## Per-phrase conditions -/

def expLabelsOK : SExp → Prop
  | .record fs => (fs.map (·.1)).Nodup
  | .update _ fs => (fs.map (·.1)).Nodup
  | _ => True

instance : DecidablePred expLabelsOK := fun e => match e with
  | .record fs => inferInstanceAs (Decidable (fs.map (·.1)).Nodup)
  | .update _ fs => inferInstanceAs (Decidable (fs.map (·.1)).Nodup)
  | .lit _ | .var _ | .con _ | .opVal _ | .unit | .tuple _ | .list _ | .accessor _ | .access _ _
  | .neg _ | .paren _ | .app _ _ | .binop _ _ _ | .ifte _ _ | .lam _ _ | .caseE _ _ | .letE _ _ =>
    isTrue trivial

def patLabelsOK : SPat → Prop
  | .record ls => ls.Nodup
  | _ => True

instance : DecidablePred patLabelsOK := fun p => match p with
  | .record ls => inferInstanceAs (Decidable ls.Nodup)
  | .wild | .lit _ | .var _ | .unit | .con _ _ | .tuple _ | .list _ | .cons _ _ | .as _ _ | .paren _ =>
    isTrue trivial

def tyLabelsOK : STy → Prop
  | .record fs => (fs.map (·.1)).Nodup
  | .ext _ fs => (fs.map (·.1)).Nodup
  | _ => True

instance : DecidablePred tyLabelsOK := fun t => match t with
  | .record fs => inferInstanceAs (Decidable (fs.map (·.1)).Nodup)
  | .ext _ fs => inferInstanceAs (Decidable (fs.map (·.1)).Nodup)
  | .var _ | .con _ _ | .unit | .tuple _ | .fn _ _ => isTrue trivial

def updateFormOK : SExp → Prop
  | .update _ fs => fs ≠ []
  | _ => True

instance : DecidablePred updateFormOK := fun e => match e with
  | .update _ fs => inferInstanceAs (Decidable (fs ≠ []))
  | .lit _ | .var _ | .con _ | .opVal _ | .unit | .tuple _ | .list _ | .record _ | .accessor _
  | .access _ _ | .neg _ | .paren _ | .app _ _ | .binop _ _ _ | .ifte _ _ | .lam _ _ | .caseE _ _
  | .letE _ _ => isTrue trivial

def extFormOK : STy → Prop
  | .ext _ fs => fs ≠ []
  | _ => True

instance : DecidablePred extFormOK := fun t => match t with
  | .ext _ fs => inferInstanceAs (Decidable (fs ≠ []))
  | .var _ | .con _ _ | .unit | .tuple _ | .record _ | .fn _ _ => isTrue trivial

def SPat.IsFloat : SPat → Prop
  | .lit (.float _ _) => True
  | _ => False

instance : DecidablePred SPat.IsFloat := fun p => match p with
  | .lit (.float _ _) => isTrue trivial
  | .lit (.int _) | .lit (.char _) | .lit (.str _) | .wild | .var _ | .unit | .con _ _ | .tuple _
  | .list _ | .record _ | .cons _ _ | .as _ _ | .paren _ => isFalse id

/-- A definition with parameters (whose equivalent form is a lambda). -/
def SDef.HasParams : SDef → Prop
  | .fn _ _ (_ :: _) _ => True
  | _ => False

instance : DecidablePred SDef.HasParams := fun d => match d with
  | .fn _ _ (_ :: _) _ => isTrue trivial
  | .fn _ _ [] _ | .pat _ _ => isFalse id

def STopDec.IsPort : STopDec → Prop
  | .port _ _ => True
  | _ => False

instance : DecidablePred STopDec.IsPort := fun d => match d with
  | .port _ _ => isTrue trivial
  | .custom _ _ _ | .alias _ _ _ | .value _ => isFalse id

def STopDec.IsTopPat : STopDec → Prop
  | .value (.pat _ _) => True
  | _ => False

instance : DecidablePred STopDec.IsTopPat := fun d => match d with
  | .value (.pat _ _) => isTrue trivial
  | .value (.fn _ _ _ _) | .custom _ _ _ | .alias _ _ _ | .port _ _ => isFalse id

/-- The type-variable sequence of a type declaration (none for other declarations). -/
def STopDec.params : STopDec → List String
  | .custom _ ps _ | .alias _ ps _ => ps
  | _ => []

/-- The constructors of a custom type declaration. -/
def STopDec.ctorList : STopDec → List (String × List STy)
  | .custom _ _ cs => cs
  | _ => []

/-- The body of an alias declaration. -/
def STopDec.aliasBody : STopDec → List STy
  | .alias _ _ t => [t]
  | _ => []

def SItem.IsOp : SItem → Prop
  | .op _ => True
  | _ => False

instance : DecidablePred SItem.IsOp := fun it => match it with
  | .op _ => isTrue trivial
  | .var _ | .ty _ | .tyAll _ => isFalse id

def SItem.ident : SItem → String
  | .var x | .op x | .ty x | .tyAll x => x

/-- An item of the header names a declaration of the module of its kind. -/
def SItem.Declared (m : SModule) : SItem → Prop
  | .var x => x ∈ m.vals ++ m.ports
  | .ty c => c ∈ m.customs ++ m.aliases
  | .tyAll c => c ∈ m.customs
  | .op _ => True

instance (m : SModule) : DecidablePred (SItem.Declared m) := fun it => match it with
  | .var x => inferInstanceAs (Decidable (x ∈ m.vals ++ m.ports))
  | .ty c => inferInstanceAs (Decidable (c ∈ m.customs ++ m.aliases))
  | .tyAll c => inferInstanceAs (Decidable (c ∈ m.customs))
  | .op _ => isTrue trivial

def SExposing.items? : SExposing → List SItem
  | .all => []
  | .items is => is

def SImport.AliasOK (i : SImport) : Prop :=
  match i.alias with
  | some a => '.' ∉ a.toList
  | none => True

instance : DecidablePred SImport.AliasOK := fun i => match h : i.alias with
  | some a => decidable_of_iff ('.' ∉ a.toList) (by simp [SImport.AliasOK, h])
  | none => isTrue (by simp [SImport.AliasOK, h])

/-! ## The 22 module restrictions -/

/-- res:core-row-labels-distinct -/
def RowLabelsDistinct (m : SModule) : Prop :=
  (∀ e ∈ m.exps, expLabelsOK e) ∧ (∀ p ∈ m.pats, patLabelsOK p) ∧ (∀ t ∈ m.tys, tyLabelsOK t)

/-- res:core-record-update-form -/
def RecordUpdateForm (m : SModule) : Prop :=
  (∀ e ∈ m.exps, updateFormOK e) ∧ (∀ t ∈ m.tys, extFormOK t)

/-- res:core-binding-site-distinct -/
def BindingSiteDistinct (m : SModule) : Prop := ∀ s ∈ m.sites, s.binds.Nodup

/-- res:core-no-shadowing -/
def NoShadowing (m : SModule) : Prop := ∀ s ∈ m.sites, ∀ x ∈ s.binds, x ∉ s.outer

/-- res:core-no-float-pattern -/
def NoFloatPattern (m : SModule) : Prop := ∀ q ∈ m.pats, ¬ q.IsFloat

/-- "a variable that the second binds occurs in the first" -/
def letRefersOcc (ds : List SDef) (i j : Nat) : Bool :=
  match ds[i]?, ds[j]? with
  | some di, some dj => dj.bound.any fun x => occursDef x di
  | _, _ => false

/-- res:core-let-recursion: a definition of a `let` that refers to itself through the `let`'s
    definitions has parameters. -/
def LetRecursion (m : SModule) : Prop :=
  ∀ ds ∈ m.lets, ∀ i < ds.length, Graph.Plus ds.length (letRefersOcc ds) i i →
    ∀ d, ds[i]? = some d → d.HasParams

/-- res:modules-ports -/
def PortsInPortModule (m : SModule) : Prop := (∃ d ∈ m.decls, d.IsPort) ↔ m.header.isPort = true

/-- res:modules-import-alias -/
def ImportAlias (m : SModule) : Prop := ∀ i ∈ m.imports, i.AliasOK

/-- res:modules-basics-qualifier -/
def BasicsQualifier (m : SModule) : Prop := ∀ i ∈ m.imports, i.alias = some "Basics" → i.mod = "Basics"

/-- res:modules-no-operator-exposing -/
def NoOperatorExposing (m : SModule) : Prop := ∀ it ∈ m.header.exposing.items?, ¬ it.IsOp

/-- res:modules-header-exposing -/
def HeaderExposing (m : SModule) : Prop := ∀ it ∈ m.header.exposing.items?, it.Declared m

/-- res:modules-exposing-distinct -/
def ExposingDistinct (m : SModule) : Prop := (m.header.exposing.items?.map SItem.ident).Nodup

/-- res:modules-no-top-pattern -/
def NoTopPattern (m : SModule) : Prop := ∀ d ∈ m.decls, ¬ d.IsTopPat

/-- res:modules-values-distinct -/
def ValuesDistinct (m : SModule) : Prop := (m.vals ++ m.ports).Nodup

/-- res:modules-types-distinct -/
def TypesDistinct (m : SModule) : Prop := (m.customs ++ m.aliases).Nodup

/-- res:modules-constructors-distinct -/
def ConstructorsDistinct (m : SModule) : Prop := (m.ctors ++ m.recAliases).Nodup

/-- res:modules-no-shadowing: no variable bound within an expression is a top-level value or
    port. -/
def TopNoShadowing (m : SModule) : Prop := ∀ s ∈ m.sites, ∀ x ∈ s.binds, x ∉ m.vals ++ m.ports

/-- res:modules-tyvarseq-distinct -/
def TyVarSeqDistinct (m : SModule) : Prop := ∀ d ∈ m.decls, d.params.Nodup

/-- res:modules-custom-type-tyvars -/
def CustomTypeTyVars (m : SModule) : Prop :=
  ∀ d ∈ m.decls, ∀ c ∈ d.ctorList, ∀ t ∈ c.2, ∀ a ∈ t.tyvars, a ∈ d.params

/-- res:modules-alias-tyvars -/
def AliasTyVars (m : SModule) : Prop :=
  ∀ d ∈ m.decls, ∀ t ∈ d.aliasBody,
    (∀ a ∈ d.params, a ∈ t.tyvars) ∧ (∀ a ∈ t.tyvars, a ∈ d.params)

/-- Alias i refers to alias j if j's type constructor occurs, unqualified, in i's body. -/
def aliasRefers (m : SModule) (i j : Nat) : Bool :=
  match m.aliasDecls[i]?, m.aliasDecls[j]? with
  | some (_, t), some (c, _) => t.subs.any fun s => match s with
    | .con ⟨none, c'⟩ _ => c' == c
    | _ => false
  | _, _ => false

/-- res:modules-alias-not-recursive -/
def AliasNotRecursive (m : SModule) : Prop :=
  ∀ i < m.aliasDecls.length, ¬ Graph.Plus m.aliasDecls.length (aliasRefers m) i i

/-- Declaration i refers directly to declaration j: i has no parameters and a variable j binds
    occurs directly in its body. -/
def direct (m : SModule) (i j : Nat) : Bool :=
  match m.valueDecls[i]?, m.valueDecls[j]? with
  | some (.fn _ _ [] e), some dj => dj.bound.any fun x => occursDirect x e
  | some (.pat _ e), some dj => dj.bound.any fun x => occursDirect x e
  | _, _ => false

/-- res:modules-value-recursion -/
def ValueRecursion (m : SModule) : Prop :=
  ∀ i < m.valueDecls.length, ¬ Graph.Plus m.valueDecls.length (direct m) i i

/-! ## The five program restrictions -/

def SProgram.main? (p : SProgram) : Option SModule := p.modules.getLast?

/-- The definitions of the main module that bind `main`. -/
def mainDecls (m : SModule) : List SDef := m.valueDecls.filter fun d => d.bound.contains "main"

def MainDefOK : SDef → Prop
  | .fn x _ _ e => x = "main" ∧ occursFree "main" e = false
  | .pat _ _ => False

instance : DecidablePred MainDefOK := fun d => match d with
  | .fn x _ _ e => inferInstanceAs (Decidable (x = "main" ∧ occursFree "main" e = false))
  | .pat _ _ => isFalse id

def mainExpOK : SDef → Prop
  | .fn _ _ _ e => occursFree "main" e = false
  | .pat _ e => occursFree "main" e = false

instance : DecidablePred mainExpOK := fun d => match d with
  | .fn _ _ _ e => inferInstanceAs (Decidable (occursFree "main" e = false))
  | .pat _ e => inferInstanceAs (Decidable (occursFree "main" e = false))

/-- res:modules-program -/
def ModulesProgram (p : SProgram) : Prop :=
  (p.modules.flatMap SModule.ports).Nodup ∧ (∀ x ∈ p.modules.flatMap SModule.ports, x ∉ managersPlat) ∧
  (∀ m ∈ p.modules, m.header.name ∉ basisModuleIds) ∧
  (∀ m ∈ p.main?.toList, ∀ d ∈ mainDecls m, mainExpOK d)

/-- res:program-modules-distinct -/
def ModulesDistinct (p : SProgram) : Prop :=
  (p.modules.map (·.header.name)).Nodup ∧ ∀ m ∈ p.modules, m.header.name ∉ basisModuleIds

/-- res:program-import-order -/
def ImportOrder (p : SProgram) : Prop :=
  ∀ i < p.modules.length, ∀ m ∈ p.modules[i]?.toList,
    ∀ mod ∈ defaultImportMods ++ m.imports.map (·.mod),
      mod ∈ basisModuleIds ∨ ∃ j < i, (p.modules[j]?.map (·.header.name)) = some mod

/-- Module i imports module j. -/
def importsRel (p : SProgram) (i j : Nat) : Bool :=
  match p.modules[i]?, p.modules[j]? with
  | some mi, some mj => mi.imports.any fun imp => imp.mod == mj.header.name
  | _, _ => false

/-- res:program-modules-reachable -/
def ModulesReachable (p : SProgram) : Prop :=
  ∀ i < p.modules.length - 1, Graph.Reach p.modules.length (importsRel p) (p.modules.length - 1) i

/-- res:program-main -/
def ProgramMain (p : SProgram) : Prop :=
  ∀ m ∈ p.main?.toList, (mainDecls m).length = 1 ∧ ∀ d ∈ mainDecls m, MainDefOK d

/-! ## Conjunctions -/

def ModuleOK (m : SModule) : Prop :=
  RowLabelsDistinct m ∧ RecordUpdateForm m ∧ BindingSiteDistinct m ∧ NoShadowing m ∧
  NoFloatPattern m ∧ LetRecursion m ∧ PortsInPortModule m ∧ ImportAlias m ∧ BasicsQualifier m ∧
  NoOperatorExposing m ∧ HeaderExposing m ∧ ExposingDistinct m ∧ NoTopPattern m ∧
  ValuesDistinct m ∧ TypesDistinct m ∧ ConstructorsDistinct m ∧ TopNoShadowing m ∧
  TyVarSeqDistinct m ∧ CustomTypeTyVars m ∧ AliasTyVars m ∧ AliasNotRecursive m ∧ ValueRecursion m

def ProgramOK (p : SProgram) : Prop :=
  ModulesProgram p ∧ ModulesDistinct p ∧ ImportOrder p ∧ ModulesReachable p ∧ ProgramMain p

/-- The program meets the AST-decidable restrictions. -/
def SynOK (p : SProgram) : Prop := (∀ m ∈ p.modules, ModuleOK m) ∧ ProgramOK p

/-- The main module declares `main`: the text is a program, not a module tested alone. -/
def SProgram.HasMain (p : SProgram) : Prop := ∀ m ∈ p.main?.toList, mainDecls m ≠ []

/-- The restrictions of a text whose main module declares no `main` (a module tested alone, such
    as most compile-error tests): every restriction but res:program-main, which such a text breaks
    by having no `main`. -/
def ModulesSynOK (p : SProgram) : Prop :=
  (∀ m ∈ p.modules, ModuleOK m) ∧ ModulesProgram p ∧ ModulesDistinct p ∧ ImportOrder p ∧
    ModulesReachable p

/-- A module restriction holds of every module of the program. -/
def Holds (R : SModule → Prop) (p : SProgram) : Prop := ∀ m ∈ p.modules, R m

/-! ## Deciders -/

instance : DecidablePred RowLabelsDistinct := fun m => by unfold RowLabelsDistinct; infer_instance
instance : DecidablePred RecordUpdateForm := fun m => by unfold RecordUpdateForm; infer_instance
instance : DecidablePred BindingSiteDistinct := fun m => by unfold BindingSiteDistinct; infer_instance
instance : DecidablePred NoShadowing := fun m => by unfold NoShadowing; infer_instance
instance : DecidablePred NoFloatPattern := fun m => by unfold NoFloatPattern; infer_instance
instance : DecidablePred LetRecursion := fun m => by unfold LetRecursion; infer_instance
instance : DecidablePred PortsInPortModule := fun m => by unfold PortsInPortModule; infer_instance
instance : DecidablePred ImportAlias := fun m => by unfold ImportAlias; infer_instance
instance : DecidablePred BasicsQualifier := fun m => by unfold BasicsQualifier; infer_instance
instance : DecidablePred NoOperatorExposing := fun m => by unfold NoOperatorExposing; infer_instance
instance : DecidablePred HeaderExposing := fun m => by unfold HeaderExposing; infer_instance
instance : DecidablePred ExposingDistinct := fun m => by unfold ExposingDistinct; infer_instance
instance : DecidablePred NoTopPattern := fun m => by unfold NoTopPattern; infer_instance
instance : DecidablePred ValuesDistinct := fun m => by unfold ValuesDistinct; infer_instance
instance : DecidablePred TypesDistinct := fun m => by unfold TypesDistinct; infer_instance
instance : DecidablePred ConstructorsDistinct := fun m => by unfold ConstructorsDistinct; infer_instance
instance : DecidablePred TopNoShadowing := fun m => by unfold TopNoShadowing; infer_instance
instance : DecidablePred TyVarSeqDistinct := fun m => by unfold TyVarSeqDistinct; infer_instance
instance : DecidablePred CustomTypeTyVars := fun m => by unfold CustomTypeTyVars; infer_instance
instance : DecidablePred AliasTyVars := fun m => by unfold AliasTyVars; infer_instance
instance : DecidablePred AliasNotRecursive := fun m => by unfold AliasNotRecursive; infer_instance
instance : DecidablePred ValueRecursion := fun m => by unfold ValueRecursion; infer_instance
instance : DecidablePred ModulesProgram := fun p => by unfold ModulesProgram; infer_instance
instance : DecidablePred ModulesDistinct := fun p => by unfold ModulesDistinct; infer_instance
instance : DecidablePred ImportOrder := fun p => by unfold ImportOrder; infer_instance
instance : DecidablePred ModulesReachable := fun p => by unfold ModulesReachable; infer_instance
instance : DecidablePred ProgramMain := fun p => by unfold ProgramMain; infer_instance
instance : DecidablePred ModuleOK := fun m => by unfold ModuleOK; infer_instance
instance : DecidablePred ProgramOK := fun p => by unfold ProgramOK; infer_instance
instance : DecidablePred SynOK := fun p => by unfold SynOK; infer_instance
instance (R : SModule → Prop) [DecidablePred R] : DecidablePred (Holds R) := fun p => by
  unfold Holds; infer_instance

instance : DecidablePred SProgram.HasMain := fun p => by unfold SProgram.HasMain; infer_instance
instance : DecidablePred ModulesSynOK := fun p => by unfold ModulesSynOK; infer_instance

def decSynOK (p : SProgram) : Bool := decide (SynOK p)

theorem decSynOK_iff (p : SProgram) : decSynOK p = true ↔ SynOK p := decide_eq_true_iff

theorem synOK_of_dec {p : SProgram} (h : decSynOK p = true) : SynOK p := (decSynOK_iff p).mp h

theorem not_synOK_of_dec {p : SProgram} (h : decSynOK p = false) : ¬ SynOK p := by
  intro hs; rw [(decSynOK_iff p).mpr hs] at h; cases h

end StandardElm.Src
