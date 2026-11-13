/-
  A Standard Definition of Elm? Mechanisation: instances of derivations and principal derivations,
  plan step 9 (section 8). sec:static-core-principal and sec:static-modules-principal.

  A derivation is an annotated phrase that checks (D10: the checker is sound and, AdequacyNote,
  every derivation is one). Its nodes are the sentences about the occurrences of the phrase, each
  with its path in the phrase, the U of its context, and the types and type schemes of its
  sentence. D' is an instance of D when a substitution S that respects classes, moves no variable
  free in the root context and is defined on every type of D takes D's nodes to D''s: U to U by a
  renaming, types to types, and each scheme of D' is no more general than S applied to D's. A
  derivation is principal when every derivation of the phrase in the context is an instance of
  it. For modules, up to a bijection between the type names the two derivations generate.

  The book's properties `PrincipalExistsCore` and `PrincipalExistsMod` are definitions here; no
  theorem is stated under them (finding B6: the module property was false while r:sm-topdec-seq
  could split a type-declaration phrase; the book no longer allows that split, decision of
  2026-11-12, option (c) of step 10's issue 9, and the property is not proved here).
  Theorems are stated under `InferPrincipalFor B p`, decision D11.
-/
import StandardElmMech.Stat.Infer

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BExp BModule BProgram)

/-! ## Nodes

`Node` and the nodes of an expression's derivation (`nodesExp`) are in Annotated.lean: the
checker requires every type at a node to be `Ty.okB`. -/

/-- The nodes of a module's derivation: its top-level declarations' (the contexts as the checker
    computes them), with the environment and port types of each declaration. -/
def nodesTopDec (C : Ctx) (path : List Nat) : ATopDec → List Node
  | .value VE vb => [⟨path, C.U, [], veSchemes (closGroup C.tyvars VE)⟩] ++ nodesValBind (C.plusVE VE) (path ++ [0]) vb
  | .types TE VE _ _ => [⟨path, C.U, TE.map (·.2.1.body), veSchemes VE⟩]
  | .port x ty U => match elabPort C x ty U with
    | some (E, PE) => [⟨path, C.U ++ U, PE.map (·.2.2), veSchemes E.VE⟩]
    | none => []
  | .seq a1 a2 =>
    match checkTopDec C a1 with
    | some (E1, _) => [⟨path, C.U, [], []⟩] ++ nodesTopDec C (path ++ [0]) a1 ++ nodesTopDec (C.oplusE E1) (path ++ [1]) a2
    | none => []

def nodesModule (B : SBasis) (a : AModule) : List Node :=
  match importCtx B a.imports, a.body with
  | some C, some d => nodesTopDec C [] d
  | _, _ => []

/-! ## Substitutions on variables and schemes -/

/-- S takes the variable v to a variable. -/
def Subst.applyVar (S : Subst) (v : BVar) : Option BVar :=
  match v with
  | .ty a =>
    match S.apply (.var a) with
    | some (.var b) => some (.ty b)
    | _ => none
  | .row e =>
    match S.apply (.record [] (some e)) with
    | some (.record [] (some e')) => some (.row e')
    | _ => none

/-- S applied to a scheme: its bound variables are `bnd`, never in the domain of S. -/
def Subst.applyScheme (S : Subst) (σ : Scheme) : Option Scheme := (S.apply σ.body).map fun b => ⟨σ.bound, b⟩

/-- Two lists read as sets. -/
def SetEq {α : Type} (l l' : List α) : Prop := ∀ x, x ∈ l ↔ x ∈ l'

/-- The clauses of an instance at one pair of corresponding nodes. -/
def NodeInstance (S : Subst) (n n' : Node) : Prop :=
  (∃ vs, n.U.mapM S.applyVar = some vs ∧ SetEq vs n'.U) ∧
  n.tys.mapM S.apply = some n'.tys ∧
  n.schemes.length = n'.schemes.length ∧
  ∀ i (hi : i < n.schemes.length) (hi' : i < n'.schemes.length) τ,
    Gen n'.schemes[i] τ → ∃ σS, S.applyScheme n.schemes[i] = some σS ∧ Gen σS τ

/-- D' is an instance of D, both with nodes `ns'` and `ns`, in a context whose free variables are A0. -/
def InstanceNodes (A0 : List BVar) (ns' ns : List Node) : Prop :=
  ∃ S : Subst, S.Respects ∧ (∀ v ∈ S.dom, v ∉ A0) ∧
    S.DefinedOn (ns.flatMap (·.tys)) ∧
    ∀ n ∈ ns, ∀ n' ∈ ns', n.path = n'.path → NodeInstance S n n'

/-! ## The Core (sec:static-core-principal) -/

def InstanceOf (C0 : Ctx) (a' a : AExp) : Prop :=
  a'.erase = a.erase ∧ InstanceNodes C0.tyvars (nodesExp C0 [] a') (nodesExp C0 [] a)

def IsPrincipal (C0 : Ctx) (a : AExp) : Prop :=
  checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true → a'.erase = a.erase → InstanceOf C0 a' a

/-- sec:static-core-principal: every Core phrase that elaborates has a principal derivation. -/
def PrincipalExistsCore : Prop :=
  ∀ (C0 : Ctx) (e : BExp), (∃ τ, ElExp C0 e τ) → ∃ a, a.erase = e ∧ IsPrincipal C0 a

theorem principal_unique {C : Ctx} {a a' : AExp} (h : IsPrincipal C a) (h' : IsPrincipal C a')
    (he : a.erase = a'.erase) : InstanceOf C a a' ∧ InstanceOf C a' a :=
  ⟨h'.2 a h.1 he, h.2 a' h'.1 he.symm⟩

/-! ## Modules (sec:static-modules-principal) -/

/-- The type names a module's type declarations give its custom types (the `name?` of their type
    functions, `namesOf`). -/
def ATopDec.custNames : ATopDec → List TyName
  | .types TE _ db _ => (db.getD []).filterMap fun d => namesOf TE d.1
  | .seq a1 a2 => a1.custNames ++ a2.custNames
  | _ => []

/-- The type names a module's derivation chooses freely outside `T of B` (sec:static-modules-principal:
    r:sm-datbind and r:sm-topdec-types): the names of its custom types. Other type names of its
    environment are not chosen by the derivation, and are compared literally (a type name in no
    basis at a node the sentence leaves free is an instance, JunkCounterexample.lean). The result's
    `T'` (r:sm-module) is unchanged. -/
def genNames (B : SBasis) (a : AModule) : List TyName :=
  ((a.body.map ATopDec.custNames).getD []).filter fun t => !decide (t ∈ B.T)

/-- Renaming of type names by a finite map (the others unchanged). -/
def renameName (ρ : List (TyName × TyName)) (t : TyName) : TyName := ((ρ.find? (·.1 == t)).map (·.2)).getD t

mutual
def Ty.renameNames (ρ : List (TyName × TyName)) : Ty → Ty
  | .var a => .var a
  | .record r tl => .record (Ty.renameRow ρ r) tl
  | .fn a b => .fn (Ty.renameNames ρ a) (Ty.renameNames ρ b)
  | .con as t => .con (Ty.renameList ρ as) (renameName ρ t)
def Ty.renameRow (ρ : List (TyName × TyName)) : Row → Row
  | [] => []
  | (l, τ) :: rest => (l, Ty.renameNames ρ τ) :: Ty.renameRow ρ rest
def Ty.renameList (ρ : List (TyName × TyName)) : List Ty → List Ty
  | [] => []
  | τ :: rest => Ty.renameNames ρ τ :: Ty.renameList ρ rest
end

def Node.renameNames (ρ : List (TyName × TyName)) (n : Node) : Node :=
  { n with tys := n.tys.map (Ty.renameNames ρ),
           schemes := n.schemes.map fun σ => ⟨σ.bound, σ.body.renameNames ρ⟩ }

/-- ρ is a bijection from `dom` onto `ran`. -/
def Bijective (ρ : List (TyName × TyName)) (dom ran : List TyName) : Prop :=
  SetEq (ρ.map (·.1)) dom ∧ SetEq (ρ.map (·.2)) ran ∧ (ρ.map (·.1)).Nodup ∧ (ρ.map (·.2)).Nodup

/-- D' is an instance of D for a module: up to a bijection between the generated type names. -/
def InstanceOfMod (B : SBasis) (a' a : AModule) : Prop :=
  a'.erase = a.erase ∧
  ∃ ρ, Bijective ρ (genNames B a) (genNames B a') ∧
    InstanceNodes [] (nodesModule B a') ((nodesModule B a).map (Node.renameNames ρ))

/-- The types at the nodes of a module's value declarations have no `bnd` variable: those are the
    bound variables of canonical schemes and type functions, never free in a sentence (Objects.lean).
    The checker tests it (`Ty.okB` at every node of a value declaration), so every derivation it
    accepts has it (`Complete.noFreeBnd_of_checkModule`, and `Complete.isPrincipalMod_iff`: the
    restriction in `IsPrincipalMod` is no restriction). -/
def ATopDec.NoFreeBnd : ATopDec → Prop
  | .value _ vb => ∀ (C : Ctx) (path : List Nat), ∀ n ∈ nodesValBind C path vb, ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, v.isBnd = false
  | .types _ _ _ _ => True
  | .port _ _ _ => True
  | .seq a1 a2 => a1.NoFreeBnd ∧ a2.NoFreeBnd

def AModule.NoFreeBnd (a : AModule) : Prop := ∀ d, a.body = some d → d.NoFreeBnd

def IsPrincipalMod (B : SBasis) (a : AModule) : Prop :=
  checkModule B a = true ∧ a.NoFreeBnd ∧
    ∀ a', checkModule B a' = true → a'.NoFreeBnd → a'.erase = a.erase → InstanceOfMod B a' a

/-- sec:static-modules-principal (finding B6: false while r:sm-topdec-seq could split a
    type-declaration phrase, which the book no longer allows; not proved here). -/
def PrincipalExistsMod : Prop :=
  ∀ (B : SBasis) (m : BModule), (∃ B' E, ElModule B m B' E) → ∃ a, a.erase = m ∧ IsPrincipalMod B a

def PrincipalExists : Prop := PrincipalExistsCore ∧ PrincipalExistsMod

/-! ## Programs (D11) -/

/-- a is a derivation for the program p in B: module i of a is a derivation for module i of p in
    the basis the earlier ones build. -/
def ProgDeriv (B : SBasis) (p : BProgram) (a : AProgram) : Prop :=
  checkProgram B a = true ∧ a.map AModule.erase = p.modules

/-- Every module's derivation is principal in the basis the earlier ones build (finding B1). -/
def PrincipalProgDeriv (B : SBasis) (p : BProgram) (a : AProgram) : Prop :=
  ProgDeriv B p a ∧ ∃ Bs, AProgram.bases B a = some Bs ∧
    ∀ i (h : i < a.length) (h' : i < Bs.length), IsPrincipalMod Bs[i] a[i]

/-- D11: what the inference returns for the program p is principal. Step 11 proves it for every
    program whose modules are coherent (finding B6). -/
def InferPrincipalFor (B : SBasis) (p : BProgram) : Prop :=
  ∀ a, inferProgram B p = .ok a → checkProgram B a = true → PrincipalProgDeriv B p a

end StandardElm.Stat
