/-
  A Standard Definition of Elm? Mechanisation: the static semantics of Modules (static-modules.tex),
  plan step 9 (section 5): Expose, provider maps, env(ME, π), Port, and the 19 rules, one
  constructor each, named r_sm_<slug>, with a second constructor for r:sm-topdec-seq,
  `r_sm_topdec_seq_types`, which splits a type-declaration phrase at one of its separators (the
  bare syntax has one node for the phrase; the book lets r:sm-topdec-seq split it, comment on
  r:sm-topdec-types). 20 constructors for 19 labels.
-/
import StandardElmMech.Stat.Rules

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule)

set_option autoImplicit true

/-! ## Interfaces (sec:static-modules-interfaces) -/

/-- Dom E for an environment with empty QE: its type constructors and its values. -/
def IEnv.dom (I : IEnv) : List SmId := I.TE.keys.map .ty ++ I.VE.keys.map .val

def Env.toI (E : Env) : IEnv := ⟨E.TE, E.VE⟩

/-- VE_v: the bindings of status v. -/
def ValEnv.ofStatusV (VE : ValEnv) : ValEnv := VE.filter fun p => p.2.2 == .v

def exposeItem (E : Env) : BItem → Option IEnv
  | .var x => (E.VE.find? x).map fun b => ⟨[], [(x, b)]⟩
  | .op _ => none
  | .ty c => (E.TE.find? c).map fun s => ⟨[(c, s)], ValEnv.ofStatusV s.2⟩
  | .tyAll c => (E.TE.find? c).map fun s => ⟨[(c, s)], s.2⟩

def exposeItems (E : Env) : List BItem → Option IEnv
  | [] => some IEnv.empty
  | it :: rest =>
    match exposeItem E it, exposeItems E rest with
    | some I, some I' => some (I.plus I')
    | _, _ => none

/-- Expose(E, explist); none when an item is unbound (or is an operator). -/
def expose (E : Env) : BExpList → Option IEnv
  | .all => some E.toI
  | .items is => exposeItems E is

/-! ## Provider maps (sec:static-modules-providers) -/

/-- π ⊕_modid (N, N'). -/
def ProvMap.merge (π : ProvMap) (mid : ModId) (N N' : List SmLongId) : ProvMap :=
  let joined : ProvMap := (diffL (dedupL N') N).map fun l => (l, unionL ((π.find? l).getD []) [mid])
  let replaced : ProvMap := (dedupL N).map fun l => (l, [mid])
  FMap.modify π (replaced ++ joined)

/-- TE_modid(c) and VE_modid(x), with List's from E0 (sec:static-modules-providers). -/
def teFind (ME : ModEnv) (mid : ModId) (c : String) : Option TyStr :=
  (FMap.find? (((FMap.find? ME mid).map (·.TE)).getD []) c).or
    (if mid = "List" then FMap.find? E0.TE c else none)

def veFind (ME : ModEnv) (mid : ModId) (x : String) : Option (Scheme × IdStatus) :=
  (FMap.find? (((FMap.find? ME mid).map (·.VE)).getD []) x).or
    (if mid = "List" then FMap.find? E0.VE x else none)

/-- Add a binding to the interface of qualifier q in a qualified environment, creating it if absent. -/
def addQ (q : ModId) (f : IEnv → IEnv) : FMap ModId IEnv → FMap ModId IEnv
  | [] => [(q, f IEnv.empty)]
  | (q', I) :: rest => if q' = q then (q', f I) :: rest else (q', I) :: addQ q f rest

/-- One entry of a provider map, added to env(ME, π): an identifier with one provider is bound;
    every qualifier of the domain gets an interface, possibly empty. -/
def envStep (ME : ModEnv) (p : SmLongId × List ModId) (E : Env) : Env :=
  match p with
  | (⟨none, .ty c⟩, [mid]) =>
    match teFind ME mid c with
    | some s => { E with TE := (c, s) :: E.TE }
    | none => E
  | (⟨none, .val x⟩, [mid]) =>
    match veFind ME mid x with
    | some b => { E with VE := (x, b) :: E.VE }
    | none => E
  | (⟨some q, .ty c⟩, [mid]) =>
    match teFind ME mid c with
    | some s => { E with QE := addQ q (fun I => { I with TE := (c, s) :: I.TE }) E.QE }
    | none => { E with QE := addQ q id E.QE }
  | (⟨some q, .val x⟩, [mid]) =>
    match veFind ME mid x with
    | some b => { E with QE := addQ q (fun I => { I with VE := (x, b) :: I.VE }) E.QE }
    | none => { E with QE := addQ q id E.QE }
  | (⟨some q, _⟩, _) => { E with QE := addQ q id E.QE }
  | _ => E

/-- env(ME, π) (sec:static-modules-providers): an ambiguous identifier is bound in no component.
    The keys of π are distinct, so each identifier is bound at most once. -/
def envOf (ME : ModEnv) (π : ProvMap) : Env := π.foldr (envStep ME) Env.empty

/-- π0 = {List ↦ {List}, [] ↦ {List}, :: ↦ {List}}. -/
def π0 : ProvMap := [(⟨none, .ty "List"⟩, ["List"]), (⟨none, .val "[]"⟩, ["List"]), (⟨none, .val "::"⟩, ["List"])]

/-- modid''.Dom I. -/
def qualified (q : ModId) (I : IEnv) : List SmLongId := I.dom.map fun s => ⟨some q, s⟩

def unqualified (ns : List SmId) : List SmLongId := ns.map fun s => ⟨none, s⟩

/-! ## Port types (fig:static-modules-port) -/

inductive Port : Ty → Prop where
  | int : Port tIntTy
  | float : Port tFloatTy
  | bool : Port (.con [] tBool)
  | string : Port tStringTy
  | bytes : Port (.con [] tBytes)
  | unit : Port tUnitTy
  | value : Port (.con [] tValue)
  | list : Port τ → Port (listTy τ)
  | maybe : Port τ → Port (.con [τ] tMaybe)
  | array : Port τ → Port (.con [τ] tArray)
  | tuple2 : Port τ1 → Port τ2 → Port (.con [τ1, τ2] tTuple2)
  | tuple3 : Port τ1 → Port τ2 → Port τ3 → Port (.con [τ1, τ2, τ3] tTuple3)
  | record : (∀ l τ, (l, τ) ∈ ρ → Port τ) → Port (.record ρ none)

mutual
def portB : Ty → Bool
  | .con [] t => t == tInt || t == tFloat || t == tBool || t == tString || t == tBytes || t == tUnit || t == tValue
  | .con [τ] t => (t == tList || t == tMaybe || t == tArray) && portB τ
  | .con [τ1, τ2] t => t == tTuple2 && portB τ1 && portB τ2
  | .con [τ1, τ2, τ3] t => t == tTuple3 && portB τ1 && portB τ2 && portB τ3
  | .record ρ none => portRowB ρ
  | _ => false
def portRowB : Row → Bool
  | [] => true
  | (_, τ) :: rest => portB τ && portRowB rest
end

/-! ## Notation for phrases (sec:static-modules-rules) -/

mutual
/-- The names used as the extension variable of a record type expression. -/
def bTyExtNames : BTy → List String
  | .tyvar _ => []
  | .record none => []
  | .record (some row) => bTyRowExtNames row
  | .openRecord r row => r :: bTyRowExtNames row
  | .unit => []
  | .tuple t1 t2 none => bTyExtNames t1 ++ bTyExtNames t2
  | .tuple t1 t2 (some t3) => bTyExtNames t1 ++ bTyExtNames t2 ++ bTyExtNames t3
  | .con _ args => bTyListExtNames args
  | .fn t1 t2 => bTyExtNames t1 ++ bTyExtNames t2
  | .paren t => bTyExtNames t
def bTyRowExtNames : BTyRow → List String
  | .field _ t none => bTyExtNames t
  | .field _ t (some rest) => bTyExtNames t ++ bTyRowExtNames rest
def bTyListExtNames : List BTy → List String
  | [] => []
  | t :: ts => bTyExtNames t ++ bTyListExtNames ts
end

/-- tyvarseq = tyrowvar(k): a row variable for a name used as an extension variable in the
    phrase, a type variable otherwise. -/
def seqVars (ps : List String) (exts : List String) : List BVar :=
  ps.map fun a => if a ∈ exts then .row (.named a) else .ty (.named a)

def conBindExtNames (cb : BConBind) : List String := cb.flatMap fun k => bTyListExtNames k.2

/-- smlabs(ty): the labels of a record type expression, possibly in parentheses, in order. -/
def smlabs : BTy → Option (List Lab)
  | .record none => some []
  | .record (some row) => some (rowLabs row)
  | .paren t => smlabs t
  | _ => none
where
  rowLabs : BTyRow → List Lab
    | .field l _ none => [l]
    | .field l _ (some rest) => l :: rowLabs rest

/-- The types of the fields `ls` of a row, in that order. -/
def Row.lookupAll (ρ : Row) : List Lab → Option (List Ty)
  | [] => some []
  | l :: ls =>
    match Row.lookup ρ l, Row.lookupAll ρ ls with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none

/-- The type name a type function is, when it is one (Λα(k).α(k) t). -/
def TyFcn.name? (θ : TyFcn) : Option TyName :=
  match θ.body with
  | .con _ t => if θ = t.toFcn then some t else none
  | _ => none

def Env.plusPE (PE PE' : PortEnv) : PortEnv := FMap.modify PE PE'

/-! ## The rules (sec:static-modules-rules) -/

mutual
/-- modid, I ⊢ expitem ⇒ (N, N') -/
inductive ElItem : ModId × IEnv → BItem → List SmLongId × List SmLongId → Prop where
  /-- r:sm-item-var -/
  | r_sm_item_var : x ∈ I.VE.keys → ElItem (mid, I) (.var x) ([], [⟨none, .val x⟩])
  /-- r:sm-item-op -/
  | r_sm_item_op : o ∈ smops mid → ElItem (mid, I) (.op o) ([], [])
  /-- r:sm-item-type -/
  | r_sm_item_type : I.TE.find? c = some (θ, VE) →
      ElItem (mid, I) (.ty c) ([⟨none, .ty c⟩], (ValEnv.ofStatusV VE).keys.map fun k => ⟨none, .val k⟩)
  /-- r:sm-item-opentype -/
  | r_sm_item_opentype : I.TE.find? c = some (θ, VE) → (∃ k σ, VE.find? k = some (σ, .c)) →
      ElItem (mid, I) (.tyAll c) ([⟨none, .ty c⟩], (VE.keys.filter (· ∈ I.VE.keys)).map fun k => ⟨none, .val k⟩)
inductive ElItemList : ModId × IEnv → List BItem → List SmLongId × List SmLongId → Prop where
  | seq_nil : ElItemList mI [] ([], [])
  | seq_cons : ElItem mI it (N, N') → ElItemList mI rest (M, M') →
      ElItemList mI (it :: rest) (unionL N M, unionL N' M')
end

/-- modid, I ⊢ explist ⇒ (N, N') -/
inductive ElExpList : ModId × IEnv → BExpList → List SmLongId × List SmLongId → Prop where
  /-- r:sm-explist-all -/
  | r_sm_explist_all : ElExpList (mid, I) .all ([], unqualified I.dom)
  /-- r:sm-explist-items -/
  | r_sm_explist_items : ElItemList (mid, I) is NN → ElExpList (mid, I) (.items is) NN

inductive ElExpListOpt : ModId × IEnv → Option BExpList → Option (List SmLongId × List SmLongId) → Prop where
  | opt_none : ElExpListOpt mI none none
  | opt_some : ElExpList mI el NN → ElExpListOpt mI (some el) (some NN)

def mergeOpt (π : ProvMap) (mid : ModId) : Option (List SmLongId × List SmLongId) → ProvMap
  | none => π
  | some (N, N') => π.merge mid N N'

/-- B, π ⊢ imports ⇒ π' -/
inductive ElImports : SBasis → ProvMap → List BImport → ProvMap → Prop where
  /-- r:sm-imports-import -/
  | r_sm_imports_import : B.ME.find? i.mod = some I →
      ElExpListOpt (i.mod, I) i.exposing NN →
      ElImports B (mergeOpt (π.merge i.mod [] (qualified (i.alias.getD i.mod) I)) i.mod NN) is π' →
      ElImports B π (i :: is) π'
  /-- r:sm-imports-empty -/
  | r_sm_imports_empty : ElImports B π [] π

/-- E ⊢ header ⇒ (modid, I) -/
inductive ElHeader : Env → BHeader → ModId × IEnv → Prop where
  /-- r:sm-header -/
  | r_sm_header : expose E h.exposing = some I → ElHeader E h (h.name, I)

mutual
/-- C, τ ⊢ conbind ⇒ VE -/
inductive ElConBind : Ctx → Ty → BConBind → ValEnv → Prop where
  /-- r:sm-conbind -/
  | r_sm_conbind : ElTyList C tys τs → ElConBindOpt C τ rest VE →
      ElConBind C τ ((k, tys) :: rest) (FMap.modify [(k, (mono (arrows τs τ), .c))] VE)
inductive ElConBindOpt : Ctx → Ty → BConBind → ValEnv → Prop where
  | opt_none : ElConBindOpt C τ [] []
  | opt_some : ElConBind C τ (b :: bs) VE → ElConBindOpt C τ (b :: bs) VE
end

mutual
/-- C ⊢ datbind ⇒ VE, TE -/
inductive ElDatBind : Ctx → BDatBind → ValEnv → TyEnv → Prop where
  /-- r:sm-datbind -/
  | r_sm_datbind : seqVars ps (conBindExtNames cb) = vs →
      ElTyList (C.plusU vs) (ps.map .tyvar) τs →
      ElConBind (C.plusU vs) (.con τs t) cb VE → t.arity = ps.length →
      ElDatBindOpt C rest VE' TE' → (∀ s ∈ TE'.vals, s.1 ≠ t.toFcn) →
      ElDatBind C ((c, ps, cb) :: rest)
        (FMap.modify (closVE C.tyvars VE) VE') (FMap.modify [(c, (t.toFcn, closVE C.tyvars VE))] TE')
inductive ElDatBindOpt : Ctx → BDatBind → ValEnv → TyEnv → Prop where
  | opt_none : ElDatBindOpt C [] [] []
  | opt_some : ElDatBind C (d :: ds) VE TE → ElDatBindOpt C (d :: ds) VE TE
end

/-- C ⊢ typbind ⇒ VE, TE -/
inductive ElTypBind : Ctx → BTypBind → ValEnv → TyEnv → Prop where
  /-- r:sm-typbind -/
  | r_sm_typbind : seqVars tb.params (bTyExtNames tb.t) = vs → ElTy (C.plusU vs) tb.t τ →
      smlabs tb.t = none → ElTypBind C tb [] [(tb.c, (TyFcn.canon ⟨vs, τ⟩, []))]
  /-- r:sm-typbind-record -/
  | r_sm_typbind_record : seqVars tb.params (bTyExtNames tb.t) = vs → ElTy (C.plusU vs) tb.t τ →
      smlabs tb.t = some ls → τ = .record ρ none → Row.lookupAll ρ ls = some τs →
      ρ.length = ls.length →
      VE = closVE C.tyvars [(tb.c, (mono (arrows τs τ), .v))] →
      ElTypBind C tb VE [(tb.c, (TyFcn.canon ⟨vs, τ⟩, VE))]

inductive ElTypBindList : Ctx → List BTypBind → List ValEnv → List TyEnv → Prop where
  | seq_nil : ElTypBindList C [] [] []
  | seq_cons : ElTypBind C tb VE TE → ElTypBindList C tbs VEs TEs →
      ElTypBindList C (tb :: tbs) (VE :: VEs) (TE :: TEs)

/-- The premises of r:sm-topdec-types, TE occurring on both sides: `Cte` is C ⊕ TE. -/
inductive TypesOK : Ctx → Ctx → Option BDatBind → List BTypBind → TyEnv → ValEnv → Prop where
  | opt_none : tbs ≠ [] → ElTypBindList Cte tbs VEs TEs →
      TypesOK Cte C none tbs (FMap.plusAll TEs) (FMap.plusAll VEs)
  | opt_some : ElDatBind Cte d VE' TE' → (∀ s ∈ TE'.vals, ∀ t, s.1.name? = some t → t ∉ C.T) →
      d ≠ [] →
      ElTypBindList Cte tbs VEs TEs →
      TypesOK Cte C (some d) tbs (FMap.modify TE' (FMap.plusAll TEs)) (FMap.modify VE' (FMap.plusAll VEs))

/-- C ⊢ topdec ⇒ E, PE -/
inductive ElTopDec : Ctx → BTopDec → Env → PortEnv → Prop where
  /-- r:sm-topdec-value -/
  | r_sm_topdec_value : ElValBind (C.plusVE VE) vb VE →
      ElTopDec C (.value vb) (Env.ofVE (closGroup C.tyvars VE)) []
  /-- r:sm-topdec-types -/
  | r_sm_topdec_types : TypesOK (C.oplusTE TE) C db tbs TE VE →
      ElTopDec C (.types db tbs) ⟨[], TE, VE⟩ []
  /-- r:sm-topdec-portout -/
  | r_sm_topdec_portout : NewFor U ty C.U → ElTy (C.plusU U) ty τ →
      τ = .fn τ' (.con [.var α] tCmd) → Port τ' →
      ElTopDec C (.port x ty) (Env.ofVE [(x, (closScheme C.tyvars (mono τ), .v))]) [(x, (.out, τ'))]
  /-- r:sm-topdec-portin -/
  | r_sm_topdec_portin : NewFor U ty C.U → ElTy (C.plusU U) ty τ →
      τ = .fn (.fn τ' (.var α)) (.con [.var α] tSub) → Port τ' →
      ElTopDec C (.port x ty) (Env.ofVE [(x, (closScheme C.tyvars (mono τ), .v))]) [(x, (.inn, τ'))]
  /-- r:sm-topdec-seq -/
  | r_sm_topdec_seq : ElTopDec C d1 E1 PE1 → ElTopDec (C.oplusE E1) d2 E2 PE2 →
      ElTopDec C (.seq d1 d2) (E1.plus E2) (Env.plusPE PE1 PE2)
  /-- r:sm-topdec-seq, at a separator inside a type-declaration phrase. -/
  | r_sm_topdec_seq_types : (db.isSome ∨ tbs1 ≠ []) → tbs2 ≠ [] →
      ElTopDec C (.types db tbs1) E1 PE1 → ElTopDec (C.oplusE E1) (.types none tbs2) E2 PE2 →
      ElTopDec C (.types db (tbs1 ++ tbs2)) (E1.plus E2) (Env.plusPE PE1 PE2)

inductive ElTopDecOpt : Ctx → Option BTopDec → Env → PortEnv → Prop where
  | opt_none : ElTopDecOpt C none Env.empty []
  | opt_some : ElTopDec C d E PE → ElTopDecOpt C (some d) E PE

/-- B ⊢ module ⇒ B', E -/
inductive ElModule : SBasis → BModule → SBasis → Env → Prop where
  /-- r:sm-module -/
  | r_sm_module : ElImports B π0 (defaultImports ++ m.imports) π →
      ElTopDecOpt ⟨B.T, [], envOf B.ME π⟩ m.body E PE → ElHeader E m.header (mid, I) →
      mid ∉ B.ME.keys → ElModule B m ⟨diffL (dedupL E.tynames) B.T, [(mid, I)], PE⟩ E

end StandardElm.Stat
