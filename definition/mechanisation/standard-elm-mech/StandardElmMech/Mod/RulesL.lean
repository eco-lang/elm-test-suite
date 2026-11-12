/-
  A Standard Definition of Elm? Mechanisation: the logged twins of the relations of Chapter 7 and of
  the dynamic rules of Chapter 9 (plan decision D4), plan step 2.

  Only four relations have a rule with a premise that can log: `EvalForces` (a Core expression),
  `EvalTopDec` (through a value binding and the forcing of a group), `EvalModule` and `EvalProgram`.
  The others (imports, exposing lists and items, headers, the bindings of types) evaluate no
  expression and are used unchanged inside the logged rules. The log of a program is the logs of its
  modules in program order; within a module, the logs of its top-level declarations in the order of
  Appendix A's derived form for modules; within a group, the forcing of x'1 () ... x'n () in the
  order written.
-/
import StandardElmMech.Mod.Rules
import StandardElmMech.Forget

namespace StandardElm.Mod
open StandardElm StandardElm.Eff

inductive EvalForcesL : Env → List Var → List Val → Log → Prop where
  | seq_nil_l (E : Env) : EvalForcesL E [] [] []
  | seq_cons_l (E : Env) (y : Var) (ys : List Var) (v : Val) (vs : List Val) (l1 l2 : Log) :
      EvalExpL E (forceExp y) v l1 → EvalForcesL E ys vs l2 → EvalForcesL E (y :: ys) (v :: vs) (l1 ++ l2)

inductive EvalTopDecL : Env → TopDec → Interface → Log → Prop where
  /-- r:dm-topdec-val -/
  | r_dm_topdec_val_l (E : Env) (vb : List (Var × Exp)) (VE : ValEnv) (vs : List Val) (l1 l2 : Log) :
      vb ≠ [] → EvalValBindL E (thunkGroup vb) VE l1 →
      EvalForcesL (E.plusVE (recVE VE)) (vb.map (thunkVar ∘ Prod.fst)) vs l2 →
      EvalTopDecL E (.val vb) (.ofVE ((vb.map Prod.fst).zip vs)) (l1 ++ l2)
  /-- r:dm-topdec-type -/
  | r_dm_topdec_type_l (E : Env) (db : DatBind) (CE : ConEnv) (VE : ValEnv) :
      EvalDatBind db CE VE → EvalTopDecL E (.type db) ⟨[], CE, VE⟩ []
  /-- r:dm-topdec-alias -/
  | r_dm_topdec_alias_l (E : Env) (tb : TypBind) (RA : List TyCon) (VE : ValEnv) :
      EvalTypBind tb RA VE → EvalTopDecL E (.alias tb) ⟨RA, [], VE⟩ []
  /-- r:dm-topdec-port-out -/
  | r_dm_topdec_port_out_l (E : Env) (x : Var) (τ : PTy) :
      EvalTopDecL E (.port x .out τ) (.ofVE [(x, .basApp (.outport x τ) [])]) []
  /-- r:dm-topdec-port-in -/
  | r_dm_topdec_port_in_l (E : Env) (x : Var) (τ : PTy) :
      EvalTopDecL E (.port x .inn τ) (.ofVE [(x, .basApp (.inport x τ) [])]) []
  /-- r:dm-topdec-seq -/
  | r_dm_topdec_seq_l (E : Env) (t1 t2 : TopDec) (RA1 : List TyCon) (CE1 : ConEnv) (VE1 : ValEnv)
      (I2 : Interface) (l1 l2 : Log) :
      EvalTopDecL E t1 ⟨RA1, CE1, VE1⟩ l1 → EvalTopDecL (E.plusVE VE1) t2 I2 l2 →
      EvalTopDecL E (.seq t1 t2) (Interface.plus ⟨RA1, CE1, VE1⟩ I2) (l1 ++ l2)

inductive EvalModuleL : Basis → Module → Basis → ValEnv → Log → Prop where
  /-- r:dm-module -/
  | r_dm_module_l (B : Basis) (h : Header) (is : List Import) (td : TopDec) (E : Env)
      (I : Interface) (m : ModId) (I' : Interface) (l1 : Log) :
      EvalImports B is E → EvalTopDecL (E0base.plusEnv E) td I l1 → EvalHeader I h m I' →
      EvalModuleL B ⟨h, is, td⟩ [(m, I')] I.VE l1

inductive EvalProgramL : Basis → List Module → Val → Log → Prop where
  /-- r:p-dyn-module -/
  | r_p_dyn_module_l (B : Basis) (m : Module) (p : List Module) (B' : Basis) (VE : ValEnv) (v : Val)
      (l1 l2 : Log) :
      EvalModuleL B m B' VE l1 → EvalProgramL (fmPlus B B') p v l2 → p ≠ [] →
      EvalProgramL B (m :: p) v (l1 ++ l2)
  /-- r:p-dyn-main -/
  | r_p_dyn_main_l (B : Basis) (m : Module) (B' : Basis) (VE : ValEnv) (v : Val) (l1 : Log) :
      EvalModuleL B m B' VE l1 → fmLookup VE "main" = some v → EvalProgramL B [m] v l1

/-! ## Forget and lift -/

theorem EvalForcesL.forget : ∀ {E ys vs l}, EvalForcesL E ys vs l → EvalForces E ys vs
  | _, _, _, _, .seq_nil_l E => .seq_nil E
  | _, _, _, _, .seq_cons_l E y ys v vs _ _ h1 h2 => .seq_cons E y ys v vs h1.forget h2.forget

theorem EvalForces.lift : ∀ {E ys vs}, EvalForces E ys vs → ∃ l, EvalForcesL E ys vs l
  | _, _, _, .seq_nil E => ⟨_, .seq_nil_l E⟩
  | _, _, _, .seq_cons E y ys v vs h1 h2 =>
    let ⟨l1, h1'⟩ := EvalExp.lift h1
    let ⟨l2, h2'⟩ := EvalForces.lift h2
    ⟨_, .seq_cons_l E y ys v vs l1 l2 h1' h2'⟩

theorem EvalTopDecL.forget : ∀ {E td I l}, EvalTopDecL E td I l → EvalTopDec E td I
  | _, _, _, _, .r_dm_topdec_val_l E vb VE vs _ _ h0 h1 h2 =>
    .r_dm_topdec_val E vb VE vs h0 h1.forget h2.forget
  | _, _, _, _, .r_dm_topdec_type_l E db CE VE h => .r_dm_topdec_type E db CE VE h
  | _, _, _, _, .r_dm_topdec_alias_l E tb RA VE h => .r_dm_topdec_alias E tb RA VE h
  | _, _, _, _, .r_dm_topdec_port_out_l E x τ => .r_dm_topdec_port_out E x τ
  | _, _, _, _, .r_dm_topdec_port_in_l E x τ => .r_dm_topdec_port_in E x τ
  | _, _, _, _, .r_dm_topdec_seq_l E t1 t2 RA1 CE1 VE1 I2 _ _ h1 h2 =>
    .r_dm_topdec_seq E t1 t2 RA1 CE1 VE1 I2 h1.forget h2.forget

theorem EvalTopDec.lift : ∀ {E td I}, EvalTopDec E td I → ∃ l, EvalTopDecL E td I l
  | _, _, _, .r_dm_topdec_val E vb VE vs h0 h1 h2 =>
    let ⟨l1, h1'⟩ := EvalValBind.lift h1
    let ⟨l2, h2'⟩ := EvalForces.lift h2
    ⟨_, .r_dm_topdec_val_l E vb VE vs l1 l2 h0 h1' h2'⟩
  | _, _, _, .r_dm_topdec_type E db CE VE h => ⟨_, .r_dm_topdec_type_l E db CE VE h⟩
  | _, _, _, .r_dm_topdec_alias E tb RA VE h => ⟨_, .r_dm_topdec_alias_l E tb RA VE h⟩
  | _, _, _, .r_dm_topdec_port_out E x τ => ⟨_, .r_dm_topdec_port_out_l E x τ⟩
  | _, _, _, .r_dm_topdec_port_in E x τ => ⟨_, .r_dm_topdec_port_in_l E x τ⟩
  | _, _, _, .r_dm_topdec_seq E t1 t2 RA1 CE1 VE1 I2 h1 h2 =>
    let ⟨l1, h1'⟩ := EvalTopDec.lift h1
    let ⟨l2, h2'⟩ := EvalTopDec.lift h2
    ⟨_, .r_dm_topdec_seq_l E t1 t2 RA1 CE1 VE1 I2 l1 l2 h1' h2'⟩

theorem EvalModuleL.forget : ∀ {B m B' VE l}, EvalModuleL B m B' VE l → EvalModule B m B' VE
  | _, _, _, _, _, .r_dm_module_l B h is td E I mid I' _ h1 h2 h3 => .r_dm_module B h is td E I mid I' h1 h2.forget h3

theorem EvalModule.lift : ∀ {B m B' VE}, EvalModule B m B' VE → ∃ l, EvalModuleL B m B' VE l
  | _, _, _, _, .r_dm_module B h is td E I mid I' h1 h2 h3 =>
    let ⟨l, h2'⟩ := EvalTopDec.lift h2
    ⟨_, .r_dm_module_l B h is td E I mid I' l h1 h2' h3⟩

theorem EvalProgramL.forget : ∀ {B p v l}, EvalProgramL B p v l → EvalProgram B p v
  | _, _, _, _, .r_p_dyn_module_l B m p B' VE v _ _ h1 h2 h3 =>
    .r_p_dyn_module B m p B' VE v h1.forget h2.forget h3
  | _, _, _, _, .r_p_dyn_main_l B m B' VE v _ h1 h2 => .r_p_dyn_main B m B' VE v h1.forget h2

theorem EvalProgram.lift : ∀ {B p v}, EvalProgram B p v → ∃ l, EvalProgramL B p v l
  | _, _, _, .r_p_dyn_module B m p B' VE v h1 h2 h3 =>
    let ⟨l1, h1'⟩ := EvalModule.lift h1
    let ⟨l2, h2'⟩ := EvalProgram.lift h2
    ⟨_, .r_p_dyn_module_l B m p B' VE v l1 l2 h1' h2' h3⟩
  | _, _, _, .r_p_dyn_main B m B' VE v h1 h2 =>
    let ⟨l, h1'⟩ := EvalModule.lift h1
    ⟨_, .r_p_dyn_main_l B m B' VE v l h1' h2⟩

end StandardElm.Mod
