/-
  A Standard Definition of Elm? Mechanisation: the inference rules of Chapter 7
  (dynamic-modules.tex, sec:dynamic-modules-rules) and the two dynamic rules of Chapter 9 for the
  modules of a program (programs.tex, r:p-dyn-module, r:p-dyn-main), plan step 2. One relation per
  judgement form, one constructor per rule, named after its label; small auxiliary relations for
  options and sequences (`opt_none`, `opt_some`, `seq_nil`, `seq_cons`), which are not rules.
-/
import StandardElmMech.Mod.Objects
import StandardElmMech.Rules

namespace StandardElm.Mod
open StandardElm StandardElm.Eff

/-- Exposing Items: I ⊢ expitem ⇒ I' -/
inductive EvalExpItem : Interface → ExpItem → Interface → Prop where
  /-- r:dm-expitem-var -/
  | r_dm_expitem_var (I : Interface) (x : Var) (v : Val) :
      fmLookup I.VE x = some v → EvalExpItem I (.var x) (.ofVE [(x, v)])
  /-- r:dm-expitem-op -/
  | r_dm_expitem_op (I : Interface) (o : Op) : EvalExpItem I (.op o) .empty
  /-- r:dm-expitem-alias: con = tycon, so the constructor is looked up by the tycon's spelling -/
  | r_dm_expitem_alias (I : Interface) (t : TyCon) (v : Val) :
      t ∈ I.RA → fmLookup I.VE t = some v → EvalExpItem I (.tycon t) ⟨[t], [], [(t, v)]⟩
  /-- r:dm-expitem-type -/
  | r_dm_expitem_type (I : Interface) (t : TyCon) (CE : ConEnv) :
      t ∉ I.RA → CE = (if (fmLookup I.CE t).isSome then [(t, [])] else []) →
      EvalExpItem I (.tycon t) ⟨[], CE, []⟩
  /-- r:dm-expitem-open -/
  | r_dm_expitem_open (I : Interface) (t : TyCon) (VE : ValEnv) :
      fmLookup I.CE t = some VE → EvalExpItem I (.opened t) ⟨[], [(t, VE)], VE⟩

inductive EvalExpItems : Interface → List ExpItem → List Interface → Prop where
  | seq_nil (I : Interface) : EvalExpItems I [] []
  | seq_cons (I : Interface) (it : ExpItem) (is : List ExpItem) (I1 : Interface) (Is : List Interface) :
      EvalExpItem I it I1 → EvalExpItems I is Is → EvalExpItems I (it :: is) (I1 :: Is)

/-- Exposing Lists: I ⊢ explist ⇒ I' -/
inductive EvalExpList : Interface → ExpList → Interface → Prop where
  /-- r:dm-explist-all -/
  | r_dm_explist_all (I : Interface) : EvalExpList I .all I
  /-- r:dm-explist-items -/
  | r_dm_explist_items (I : Interface) (is : List ExpItem) (Is : List Interface) :
      is ≠ [] → EvalExpItems I is Is → EvalExpList I (.items is) (Interface.sum Is)

inductive EvalExpListOpt : Interface → Option ExpList → Option Interface → Prop where
  | opt_none (I : Interface) : EvalExpListOpt I none none
  | opt_some (I : Interface) (el : ExpList) (I' : Interface) :
      EvalExpList I el I' → EvalExpListOpt I (some el) (some I')

/-- Headers: I ⊢ header ⇒ (modid, I') -/
inductive EvalHeader : Interface → Header → ModId → Interface → Prop where
  /-- r:dm-header -/
  | r_dm_header (I : Interface) (isPort : Bool) (m : ModId) (el : ExpList) (I' : Interface) :
      EvalExpList I el I' → EvalHeader I ⟨isPort, m, el⟩ m I'

/-- The unqualified part of an import: ∅ [+ VE of I']. -/
def unqualified : Option Interface → ValEnv
  | none => []
  | some I' => fmPlus [] I'.VE

/-- Imports: B ⊢ imports ⇒ E -/
inductive EvalImports : Basis → List Import → Env → Prop where
  /-- r:dm-imports-import -/
  | r_dm_imports_import (B : Basis) (m q : ModId) (el : Option ExpList) (rest : List Import)
      (I : Interface) (I' : Option Interface) (E : Env) :
      fmLookup B m = some I → EvalExpListOpt I el I' → EvalImports B rest E →
      EvalImports B (⟨m, q, el⟩ :: rest) (Env.merge (.mk [(q, .mk [] I.VE)] (unqualified I')) E)
  /-- r:dm-imports-empty -/
  | r_dm_imports_empty (B : Basis) : EvalImports B [] (.mk [] [])

mutual
/-- Constructor Bindings: ⊢ conbind ⇒ VE -/
inductive EvalConBind : ConBind → ValEnv → Prop where
  /-- r:dm-conbind -/
  | r_dm_conbind (c : Con) (rest : Option ConBind) (VE : ValEnv) :
      EvalConBindOpt rest VE → EvalConBind (.mk c rest) (fmPlus [(c.name, .con c [])] VE)
inductive EvalConBindOpt : Option ConBind → ValEnv → Prop where
  | opt_none : EvalConBindOpt none []
  | opt_some (cb : ConBind) (VE : ValEnv) : EvalConBind cb VE → EvalConBindOpt (some cb) VE
end

mutual
/-- Custom-type Bindings: ⊢ datbind ⇒ (CE, VE) -/
inductive EvalDatBind : DatBind → ConEnv → ValEnv → Prop where
  /-- r:dm-datbind -/
  | r_dm_datbind (t : TyCon) (cb : ConBind) (rest : Option DatBind) (VE : ValEnv) (CE' : ConEnv)
      (VE' : ValEnv) :
      EvalConBind cb VE → EvalDatBindOpt rest CE' VE' →
      EvalDatBind (.mk t cb rest) (fmPlus [(t, VE)] CE') (fmPlus VE VE')
inductive EvalDatBindOpt : Option DatBind → ConEnv → ValEnv → Prop where
  | opt_none : EvalDatBindOpt none [] []
  | opt_some (db : DatBind) (CE : ConEnv) (VE : ValEnv) :
      EvalDatBind db CE VE → EvalDatBindOpt (some db) CE VE
end

/-- Alias Bindings: ⊢ typbind ⇒ (RA, VE) -/
inductive EvalTypBind : TypBind → List TyCon → ValEnv → Prop where
  /-- r:dm-typbind -/
  | r_dm_typbind (t : TyCon) (ls : Option (List Lab)) :
      EvalTypBind ⟨t, ls⟩ (match ls with | none => [] | some _ => [t])
                          (match ls with | none => [] | some ls => [(t, recordCtor ls)])

/-- The premises E + Rec VE ⊢ x'1 () ⇒ v1 ... x'n () ⇒ vn of r:dm-topdec-val. -/
inductive EvalForces : Env → List Var → List Val → Prop where
  | seq_nil (E : Env) : EvalForces E [] []
  | seq_cons (E : Env) (y : Var) (ys : List Var) (v : Val) (vs : List Val) :
      EvalExp E (forceExp y) v → EvalForces E ys vs → EvalForces E (y :: ys) (v :: vs)

/-- Top-level Declarations: E ⊢ topdec ⇒ I -/
inductive EvalTopDec : Env → TopDec → Interface → Prop where
  /-- r:dm-topdec-val -/
  | r_dm_topdec_val (E : Env) (vb : List (Var × Exp)) (VE : ValEnv) (vs : List Val) :
      vb ≠ [] → EvalValBind E (thunkGroup vb) VE →
      EvalForces (E.plusVE (recVE VE)) (vb.map (thunkVar ∘ Prod.fst)) vs →
      EvalTopDec E (.val vb) (.ofVE ((vb.map Prod.fst).zip vs))
  /-- r:dm-topdec-type -/
  | r_dm_topdec_type (E : Env) (db : DatBind) (CE : ConEnv) (VE : ValEnv) :
      EvalDatBind db CE VE → EvalTopDec E (.type db) ⟨[], CE, VE⟩
  /-- r:dm-topdec-alias -/
  | r_dm_topdec_alias (E : Env) (tb : TypBind) (RA : List TyCon) (VE : ValEnv) :
      EvalTypBind tb RA VE → EvalTopDec E (.alias tb) ⟨RA, [], VE⟩
  /-- r:dm-topdec-port-out -/
  | r_dm_topdec_port_out (E : Env) (x : Var) (τ : PTy) :
      EvalTopDec E (.port x .out τ) (.ofVE [(x, .basApp (.outport x τ) [])])
  /-- r:dm-topdec-port-in -/
  | r_dm_topdec_port_in (E : Env) (x : Var) (τ : PTy) :
      EvalTopDec E (.port x .inn τ) (.ofVE [(x, .basApp (.inport x τ) [])])
  /-- r:dm-topdec-seq -/
  | r_dm_topdec_seq (E : Env) (t1 t2 : TopDec) (RA1 : List TyCon) (CE1 : ConEnv) (VE1 : ValEnv)
      (I2 : Interface) :
      EvalTopDec E t1 ⟨RA1, CE1, VE1⟩ → EvalTopDec (E.plusVE VE1) t2 I2 →
      EvalTopDec E (.seq t1 t2) (Interface.plus ⟨RA1, CE1, VE1⟩ I2)

/-- Modules: B ⊢ module ⇒ B', VE -/
inductive EvalModule : Basis → Module → Basis → ValEnv → Prop where
  /-- r:dm-module: E0 is the environment binding [] and :: (E0base) -/
  | r_dm_module (B : Basis) (h : Header) (is : List Import) (td : TopDec) (E : Env)
      (I : Interface) (m : ModId) (I' : Interface) :
      EvalImports B is E → EvalTopDec (E0base.plusEnv E) td I → EvalHeader I h m I' →
      EvalModule B ⟨h, is, td⟩ [(m, I')] I.VE

/-- Evaluation of the modules of a program: B ⊢ program ⇒ v (programs.tex) -/
inductive EvalProgram : Basis → List Module → Val → Prop where
  /-- r:p-dyn-module -/
  | r_p_dyn_module (B : Basis) (m : Module) (p : List Module) (B' : Basis) (VE : ValEnv) (v : Val) :
      EvalModule B m B' VE → EvalProgram (fmPlus B B') p v → p ≠ [] → EvalProgram B (m :: p) v
  /-- r:p-dyn-main -/
  | r_p_dyn_main (B : Basis) (m : Module) (B' : Basis) (VE : ValEnv) (v : Val) :
      EvalModule B m B' VE → fmLookup VE "main" = some v → EvalProgram B [m] v

end StandardElm.Mod
