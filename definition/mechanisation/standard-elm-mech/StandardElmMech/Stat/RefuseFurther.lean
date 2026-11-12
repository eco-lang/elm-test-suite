/-
  A Standard Definition of Elm? Mechanisation: refusals by the further restrictions (plan step 9,
  milestone 9d, Group 5). `furtherFailB B sp` decides, for a program of one module without type
  declarations or ports, that no derivation of the module meets the further restrictions; the
  refusal is unconditional (every derivation, principal or not).

  The decider looks at the bare module: a match, a lambda or a destructuring binding (a *site*)
  whose patterns
  * are redundant whatever their type: a pattern is subsumed by an earlier one (`irrSubsB`); or
  * are not exhaustive at a reference type τ0 (read from the inference's derivation, which need not
    be trusted) at which they fit with forced heads (RefuseFurtherAgree.lean): every constructor
    pattern of the site is typed by its scheme in the module's context, which the constructor
    table agrees with (`cOK`), so in every derivation the patterns fit at the type the derivation
    gives them, and Maranget's algorithm answers the same there as at τ0 (`useful_agree`).

  Since the module declares no type, every derivation's environment has no type environment, so
  the constructor table of the further restrictions is the basis's (`conTable B Env.empty`).
-/
import StandardElmMech.Stat.RefuseFurtherAgree

namespace StandardElm.Stat.RFurther
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BAtPat BPat BPatRow BAtExp BExpRow BExp BMatch BMRule BDec BValBind BTopDec BModule)

/-! ## Bare patterns, normalised -/

mutual
def nAtPat : BAtPat → PatN
  | .wild | .var _ | .record _ => .wild
  | .scon sc => match denote sc with
    | some d => .den d
    | none => .wild
  | .con lc => .con lc.id []
  | .unit => .con "()" []
  | .tuple p1 p2 none => .con "(,)" [nPat p1, nPat p2]
  | .tuple p1 p2 (some p3) => .con "(,,)" [nPat p1, nPat p2, nPat p3]
  | .nil => .con "[]" []
  | .paren p => nPat p
def nPat : BPat → PatN
  | .atpat a => nAtPat a
  | .con lc args => .con lc.id (nAtPats args)
  | .cons p1 p2 => .con "::" [nPat p1, nPat p2]
  | .as p _ => nPat p
def nAtPats : List BAtPat → List PatN
  | [] => []
  | a :: as => nAtPat a :: nAtPats as
end

mutual
theorem norm_erase_at : ∀ a : AAtPat, normAtPat a = nAtPat a.erase
  | .wild _ => rfl
  | .var _ _ => rfl
  | .record _ _ => rfl
  | .scon _ _ => rfl
  | .con _ _ _ => rfl
  | .unit => rfl
  | .tuple p1 p2 none => by
    simp only [normAtPat, AAtPat.erase, APat.eraseOpt, nAtPat, norm_erase p1, norm_erase p2]
  | .tuple p1 p2 (some p3) => by
    simp only [normAtPat, AAtPat.erase, APat.eraseOpt, nAtPat, norm_erase p1, norm_erase p2, norm_erase p3]
  | .nil _ => rfl
  | .paren p => by simp only [normAtPat, AAtPat.erase, nAtPat, norm_erase p]
theorem norm_erase : ∀ p : APat, normPat p = nPat p.erase
  | .atpat a => by simp only [normPat, APat.erase, nPat, norm_erase_at a]
  | .con _ _ args _ => by simp only [normPat, APat.erase, nPat, norm_erase_list args]
  | .cons p1 p2 => by simp only [normPat, APat.erase, nPat, norm_erase p1, norm_erase p2]
  | .as p _ => by simp only [normPat, APat.erase, nPat, norm_erase p]
theorem norm_erase_list : ∀ as : List AAtPat, normAtPats as = nAtPats (AAtPat.eraseList as)
  | [] => rfl
  | a :: as => by simp only [normAtPats, AAtPat.eraseList, nAtPats, norm_erase_at a, norm_erase_list as]
end

/-! ## Constructor patterns whose schemes the table agrees with -/

def conOKB (tbl : ConTable) (C0 : Ctx) (lc : LongId) : Bool :=
  match C0.lookupVal lc with
  | some (σ, .c) => schemeOKB tbl lc.id σ
  | _ => false

mutual
def cOKAt (tbl : ConTable) (C0 : Ctx) : BAtPat → Bool
  | .scon sc => (denote sc).isNone
  | .con lc => conOKB tbl C0 lc
  | .tuple p1 p2 p3 => cOK tbl C0 p1 && cOK tbl C0 p2 && cOKOpt tbl C0 p3
  | .paren p => cOK tbl C0 p
  | _ => true
def cOK (tbl : ConTable) (C0 : Ctx) : BPat → Bool
  | .atpat a => cOKAt tbl C0 a
  | .con lc args => conOKB tbl C0 lc && cOKAtList tbl C0 args
  | .cons p1 p2 => cOK tbl C0 p1 && cOK tbl C0 p2
  | .as p _ => cOK tbl C0 p
def cOKOpt (tbl : ConTable) (C0 : Ctx) : Option BPat → Bool
  | none => true
  | some p => cOK tbl C0 p
def cOKAtList (tbl : ConTable) (C0 : Ctx) : List BAtPat → Bool
  | [] => true
  | a :: as => cOKAt tbl C0 a && cOKAtList tbl C0 as
end

def b0 : TyVar := .bnd 0 .any
def b1 : TyVar := .bnd 1 .any
def b2 : TyVar := .bnd 2 .any

def σUnit : Scheme := ⟨[], tUnitTy⟩
def σPair : Scheme := ⟨[.ty b0, .ty b1], arrows [.var b0, .var b1] (.con [.var b0, .var b1] tTuple2)⟩
def σTriple : Scheme :=
  ⟨[.ty b0, .ty b1, .ty b2], arrows [.var b0, .var b1, .var b2] (.con [.var b0, .var b1, .var b2] tTuple3)⟩
def σNil : Scheme := ⟨[.ty b0], listTy (.var b0)⟩
def σCons : Scheme := ⟨[.ty b0], arrows [.var b0, listTy (.var b0)] (listTy (.var b0))⟩

/-- The table agrees with the built-in constructors. -/
def builtinsOKB (tbl : ConTable) : Bool :=
  schemeOKB tbl "()" σUnit && schemeOKB tbl "(,)" σPair && schemeOKB tbl "(,,)" σTriple &&
    schemeOKB tbl "[]" σNil && schemeOKB tbl "::" σCons

section builtins
variable {tbl : ConTable} (hbi : builtinsOKB tbl = true)
include hbi

theorem fits_unit : fitsB tbl tUnitTy (.con "()" []) = true := by
  simp only [builtinsOKB, Bool.and_eq_true] at hbi
  exact con_fits (inst := []) (argtys := []) hbi.1.1.1.1 rfl rfl rfl rfl

theorem fits_pair {τ1 τ2 : Ty} {p1 p2 : PatN} (h1 : fitsB tbl τ1 p1 = true) (h2 : fitsB tbl τ2 p2 = true) :
    fitsB tbl (.con [τ1, τ2] tTuple2) (.con "(,)" [p1, p2]) = true := by
  simp only [builtinsOKB, Bool.and_eq_true] at hbi
  exact con_fits (inst := [τ1, τ2]) (argtys := [τ1, τ2]) hbi.1.1.1.2 rfl
    (by simp [σPair, b0, b1, arrows, Subst.apply, Subst.applyList, FMap.find?]) rfl
    (by simp [fitsListB, h1, h2])

theorem fits_triple {τ1 τ2 τ3 : Ty} {p1 p2 p3 : PatN} (h1 : fitsB tbl τ1 p1 = true) (h2 : fitsB tbl τ2 p2 = true)
    (h3 : fitsB tbl τ3 p3 = true) :
    fitsB tbl (.con [τ1, τ2, τ3] tTuple3) (.con "(,,)" [p1, p2, p3]) = true := by
  simp only [builtinsOKB, Bool.and_eq_true] at hbi
  exact con_fits (inst := [τ1, τ2, τ3]) (argtys := [τ1, τ2, τ3]) hbi.1.1.2 rfl
    (by simp [σTriple, b0, b1, b2, arrows, Subst.apply, Subst.applyList, FMap.find?]) rfl
    (by simp [fitsListB, h1, h2, h3])

theorem fits_nil (τ : Ty) : fitsB tbl (listTy τ) (.con "[]" []) = true := by
  simp only [builtinsOKB, Bool.and_eq_true] at hbi
  exact con_fits (inst := [τ]) (argtys := []) hbi.1.2 rfl
    (by simp [σNil, b0, arrows, listTy, Subst.apply, Subst.applyList, FMap.find?]) rfl rfl

theorem fits_cons {τ : Ty} {p1 p2 : PatN} (h1 : fitsB tbl τ p1 = true) (h2 : fitsB tbl (listTy τ) p2 = true) :
    fitsB tbl (listTy τ) (.con "::" [p1, p2]) = true := by
  simp only [builtinsOKB, Bool.and_eq_true] at hbi
  exact con_fits (inst := [τ]) (argtys := [τ, listTy τ]) hbi.2 rfl
    (by simp [σCons, b0, arrows, listTy, Subst.apply, Subst.applyList, FMap.find?]) rfl
    (by simp [fitsListB, h1, h2])

end builtins

/-! ## Contexts: the constructors of the module's context are never shadowed -/

/-- Every constructor C gives is C0's. -/
def CtxInv (C0 C : Ctx) : Prop := ∀ lc σ, C.lookupVal lc = some (σ, .c) → C0.lookupVal lc = some (σ, .c)

/-- A value environment of values only (no constructor). -/
def AllV (VE : ValEnv) : Prop := ∀ e ∈ VE, e.2.2 = IdStatus.v

theorem allV_nil : AllV [] := by intro e he; cases he

theorem allV_single {x : String} {σ : Scheme} : AllV [(x, (σ, .v))] := by
  intro e he; simp at he; subst he; rfl

theorem allV_modify {f g : ValEnv} (hf : AllV f) (hg : AllV g) : AllV (FMap.modify f g) := by
  intro e he
  simp only [FMap.modify, List.mem_append, List.mem_filter] at he
  rcases he with he | ⟨he, _⟩
  · exact hg e he
  · exact hf e he

theorem allV_plusAll : ∀ (fs : List ValEnv) (acc : ValEnv), AllV acc → (∀ f ∈ fs, AllV f) →
    AllV (fs.foldl FMap.modify acc)
  | [], _, hacc, _ => hacc
  | f :: fs, acc, hacc, hfs => by
    simp only [List.foldl_cons]
    exact allV_plusAll fs _ (allV_modify hacc (hfs f List.mem_cons_self))
      (fun g hg => hfs g (List.mem_cons_of_mem _ hg))

theorem allV_closGroup {A : List BVar} {VE : ValEnv} (h : AllV VE) : AllV (closGroup A VE) := by
  intro e he
  simp only [closGroup, FMap.mapV, List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  exact h p hp

theorem find?_mem {VE : ValEnv} {x : String} {b : Scheme × IdStatus} : FMap.find? VE x = some b → (x, b) ∈ VE := by
  induction VE with
  | nil => simp [FMap.find?]
  | cons p r ih =>
    obtain ⟨k, v⟩ := p
    simp only [FMap.find?]
    split
    · rename_i hk; intro h; cases h; subst hk; exact List.mem_cons_self
    · intro h; exact List.mem_cons_of_mem _ (ih h)

theorem ctxInv_refl (C0 : Ctx) : CtxInv C0 C0 := fun _ _ h => h

theorem ctxInv_plusVE {C0 C : Ctx} {VE : ValEnv} (hv : AllV VE) (h : CtxInv C0 C) : CtxInv C0 (C.plusVE VE) := by
  intro lc σ hl
  apply h lc σ
  simp only [Ctx.lookupVal, Env.lookupVal, Ctx.plusVE] at hl ⊢
  split at hl
  · rw [FMap.find?_append] at hl
    cases hf : FMap.find? VE lc.id with
    | none => rw [hf] at hl; simpa using hl
    | some b =>
      rw [hf] at hl
      simp only [Option.some_or, Option.some.injEq] at hl
      subst hl
      have := hv _ (find?_mem hf)
      cases this
  · exact hl

theorem ctxInv_plusU {C0 C : Ctx} {U : List BVar} (h : CtxInv C0 C) : CtxInv C0 (C.plusU U) := h

theorem ctxInv_oplusE {C0 C : Ctx} {E : Env} (hq : E.QE = []) (hv : AllV E.VE) (h : CtxInv C0 C) :
    CtxInv C0 (C.oplusE E) := by
  intro lc σ hl
  apply h lc σ
  simp only [Ctx.lookupVal, Env.lookupVal, Ctx.oplusE, Env.plus] at hl ⊢
  split at hl
  · rw [FMap.find?_modify] at hl
    cases hf : FMap.find? E.VE lc.id with
    | none => rw [hf] at hl; simpa using hl
    | some b =>
      rw [hf] at hl
      simp only [Option.some_or, Option.some.injEq] at hl
      subst hl
      have := hv _ (find?_mem hf)
      cases this
  · rw [FMap.find?_modify, hq] at hl
    simpa using hl

mutual
theorem allV_atpat : ∀ a : AAtPat, AllV a.ve
  | .wild _ => allV_nil
  | .scon _ _ => allV_nil
  | .var _ _ => allV_single
  | .con _ _ _ => allV_nil
  | .unit => allV_nil
  | .tuple p1 p2 p3 => allV_modify (allV_modify (allV_pat p1) (allV_pat p2)) (allV_patOpt p3)
  | .nil _ => allV_nil
  | .record row _ => allV_rowOpt row
  | .paren p => allV_pat p
theorem allV_row : ∀ r : APatRow, AllV r.ve
  | .field _ _ rest => allV_modify allV_single (allV_rowOpt rest)
theorem allV_rowOpt : ∀ r : Option APatRow, AllV (APatRow.veOpt r)
  | none => allV_nil
  | some r => allV_row r
theorem allV_pat : ∀ p : APat, AllV p.ve
  | .atpat a => allV_atpat a
  | .con _ _ args _ => allV_plusAll _ [] allV_nil (allV_list args)
  | .cons p1 p2 => allV_modify (allV_pat p1) (allV_pat p2)
  | .as p _ => allV_modify (allV_pat p) allV_single
theorem allV_patOpt : ∀ p : Option APat, AllV (APat.veOpt p)
  | none => allV_nil
  | some p => allV_pat p
theorem allV_list : ∀ as : List AAtPat, ∀ f ∈ AAtPat.veList as, AllV f
  | [], _, h => by cases h
  | a :: as, f, h => by
    simp only [AAtPat.veList, List.mem_cons] at h
    rcases h with rfl | h
    · exact allV_atpat a
    · exact allV_list as f h
end

theorem allV_vb : ∀ vb : AValBind, AllV vb.ve
  | .var _ _ _ _ none => allV_modify allV_single allV_nil
  | .var _ _ _ _ (some vb) => allV_modify allV_single (allV_vb vb)
  | .pat p _ => allV_atpat p

/-! ## Patterns the checker types fit -/

theorem genAt_spec {σ : Scheme} {ts : List Ty} {τ : Ty} (h : genAt σ ts τ = true) :
    ∃ S, bindSubst σ.bound ts = some S ∧ S.apply σ.body = some τ := by
  unfold genAt at h
  split at h
  · rename_i S hS
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨S, hS, h.2⟩
  · cases h

section fits
variable (tbl : ConTable) (C0 : Ctx) (hbi : builtinsOKB tbl = true)
include hbi
-- `fitsList` uses `hbi` through the mutual recursion, which the linter does not see.
set_option linter.unusedSectionVars false

mutual
theorem fitsAt : ∀ (a : AAtPat) (C : Ctx), CtxInv C0 C → checkAtPat C a = true → cOKAt tbl C0 a.erase = true →
    fitsB tbl a.ty (normAtPat a) = true
  | .wild _, _, _, _, _ => by simp [normAtPat, fitsB]
  | .var _ _, _, _, _, _ => by simp [normAtPat, fitsB]
  | .record _ _, _, _, _, _ => by simp [normAtPat, fitsB]
  | .scon sc _, _, _, _, hok => by
    simp only [AAtPat.erase, cOKAt, Option.isNone_iff_eq_none] at hok
    simp [normAtPat, hok, fitsB]
  | .con lc inst τ, C, hinv, hc, hok => by
    simp only [checkAtPat] at hc
    split at hc
    · rename_i σ hl
      simp only [Bool.and_eq_true] at hc
      have h0 := hinv lc σ hl
      simp only [AAtPat.erase, cOKAt, conOKB, h0] at hok
      obtain ⟨S, hb, ha⟩ := genAt_spec hc.1
      show fitsB tbl τ (.con lc.id []) = true
      exact con_fits (argtys := []) hok hb (by simpa [arrows] using ha) hc.2 rfl
    · cases hc
  | .unit, _, _, _, _ => fits_unit hbi
  | .tuple p1 p2 none, C, hinv, hc, hok => by
    simp only [checkAtPat, Bool.and_eq_true] at hc
    simp only [AAtPat.erase, APat.eraseOpt, cOKAt, Bool.and_eq_true] at hok
    simp only [AAtPat.ty, APat.tyOpt, tupleTy, normAtPat]
    exact fits_pair hbi (fitsPat p1 C hinv hc.1.1 hok.1.1) (fitsPat p2 C hinv hc.1.2 hok.1.2)
  | .tuple p1 p2 (some p3), C, hinv, hc, hok => by
    simp only [checkAtPat, checkPatOpt, Bool.and_eq_true] at hc
    simp only [AAtPat.erase, APat.eraseOpt, cOKAt, cOKOpt, Bool.and_eq_true] at hok
    simp only [AAtPat.ty, APat.tyOpt, tupleTy, normAtPat]
    exact fits_triple hbi (fitsPat p1 C hinv hc.1.1 hok.1.1) (fitsPat p2 C hinv hc.1.2 hok.1.2)
      (fitsPat p3 C hinv hc.2 hok.2)
  | .nil τ, _, _, hc, _ => by
    simp only [checkAtPat] at hc
    obtain ⟨τ0, rfl⟩ := isListTy_spec hc
    exact fits_nil hbi τ0
  | .paren p, C, hinv, hc, hok => by
    simp only [checkAtPat] at hc
    simp only [AAtPat.erase, cOKAt] at hok
    simp only [AAtPat.ty, normAtPat]
    exact fitsPat p C hinv hc hok
theorem fitsPat : ∀ (p : APat) (C : Ctx), CtxInv C0 C → checkPat C p = true → cOK tbl C0 p.erase = true →
    fitsB tbl p.ty (normPat p) = true
  | .atpat a, C, hinv, hc, hok => by
    simp only [checkPat] at hc
    simp only [APat.erase, cOK] at hok
    exact fitsAt a C hinv hc hok
  | .con lc inst args τ, C, hinv, hc, hok => by
    simp only [checkPat, Bool.and_eq_true] at hc
    obtain ⟨hc1, hc2⟩ := hc
    split at hc1
    · rename_i σ hl
      simp only [Bool.and_eq_true] at hc1
      have h0 := hinv lc σ hl
      simp only [APat.erase, cOK, conOKB, h0, Bool.and_eq_true] at hok
      obtain ⟨S, hb, ha⟩ := genAt_spec hc1.1
      exact con_fits hok.1 hb ha hc1.2 (fitsList args C hinv hc2 hok.2)
    · cases hc1
  | .cons p1 p2, C, hinv, hc, hok => by
    simp only [checkPat, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [APat.erase, cOK, Bool.and_eq_true] at hok
    obtain ⟨⟨hc1, hc2⟩, he⟩ := hc
    have f2 := fitsPat p2 C hinv hc2 hok.2
    rw [he] at f2
    simp only [APat.ty, normPat]
    exact fits_cons hbi (fitsPat p1 C hinv hc1 hok.1) f2
  | .as p _, C, hinv, hc, hok => by
    simp only [checkPat] at hc
    simp only [APat.erase, cOK] at hok
    simp only [APat.ty, normPat]
    exact fitsPat p C hinv hc hok
theorem fitsList : ∀ (as : List AAtPat) (C : Ctx), CtxInv C0 C → checkAtPatList C as = true →
    cOKAtList tbl C0 (AAtPat.eraseList as) = true → fitsListB tbl (AAtPat.tyList as) (normAtPats as) = true
  | [], _, _, _, _ => rfl
  | a :: as, C, hinv, hc, hok => by
    simp only [checkAtPatList, Bool.and_eq_true] at hc
    simp only [AAtPat.eraseList, cOKAtList, Bool.and_eq_true] at hok
    simp only [AAtPat.tyList, normAtPats, fitsListB, Bool.and_eq_true]
    exact ⟨fitsAt a C hinv hc.1 hok.1, fitsList as C hinv hc.2 hok.2⟩
end

end fits

/-! ## Sites -/

inductive SKind where
  | exh | case
  deriving DecidableEq

/-- A site of a bare phrase: a lambda or destructuring binding (exh) or a match (case), with its
    patterns. -/
structure BSite where
  kind : SKind
  pats : List BPat

def bMatchPats : BMatch → List BPat
  | .mk (.mk p _) rest => p :: (match rest with
    | none => []
    | some m => bMatchPats m)

mutual
def bsAtExp : BAtExp → List BSite
  | .tuple e1 e2 e3 => bsExp e1 ++ bsExp e2 ++ bsExpOpt e3
  | .record row => bsExpRowOpt row
  | .update _ row => bsExpRow row
  | .letE d e => bsDec d ++ bsExp e
  | .paren e => bsExp e
  | _ => []
def bsExpRow : BExpRow → List BSite
  | .field _ e rest => bsExp e ++ bsExpRowOpt rest
def bsExpRowOpt : Option BExpRow → List BSite
  | none => []
  | some r => bsExpRow r
def bsExp : BExp → List BSite
  | .atexp a => bsAtExp a
  | .app e a => bsExp e ++ bsAtExp a
  | .lam p e => ⟨.exh, [.atpat p]⟩ :: bsExp e
  | .caseE e m => ⟨.case, bMatchPats m⟩ :: (bsExp e ++ bsMatch m)
def bsExpOpt : Option BExp → List BSite
  | none => []
  | some e => bsExp e
def bsMatch : BMatch → List BSite
  | .mk (.mk _ e) rest => bsExp e ++ bsMatchOpt rest
def bsMatchOpt : Option BMatch → List BSite
  | none => []
  | some m => bsMatch m
def bsDec : BDec → List BSite
  | .val vb => bsValBind vb
def bsValBind : BValBind → List BSite
  | .var _ _ e rest => bsExp e ++ bsValBindOpt rest
  | .pat p e => ⟨.exh, [.atpat p]⟩ :: bsExp e
def bsValBindOpt : Option BValBind → List BSite
  | none => []
  | some vb => bsValBind vb
end

def noTypesB : BTopDec → Bool
  | .value _ => true
  | .seq d1 d2 => noTypesB d1 && noTypesB d2
  | _ => false

def bsTop : BTopDec → List BSite
  | .value vb => bsValBind vb
  | .seq d1 d2 => bsTop d1 ++ bsTop d2
  | _ => []

def matchAPats : AMatch → List APat
  | .mk (.mk p _) rest => p :: (match rest with
    | none => []
    | some m => matchAPats m)

theorem bMatchPats_erase : ∀ m : AMatch, bMatchPats m.erase = (matchAPats m).map APat.erase
  | .mk (.mk p e) none => by
    simp [AMatch.erase, AMRule.erase, AMatch.eraseOpt, bMatchPats, matchAPats]
  | .mk (.mk p e) (some m) => by
    simp [AMatch.erase, AMRule.erase, AMatch.eraseOpt, bMatchPats, matchAPats, bMatchPats_erase m]

theorem matchPats_eq : ∀ m : AMatch, matchPats m = (matchAPats m).map normPat
  | .mk (.mk p e) none => by simp [matchPats, matchAPats]
  | .mk (.mk p e) (some m) => by simp [matchPats, matchAPats, matchPats_eq m]

theorem checkMatch_pats {C : Ctx} : ∀ m : AMatch, checkMatch C m = true →
    ∀ p ∈ matchAPats m, checkPat C p = true ∧ ∃ ρ, AMatch.ty m = .fn p.ty ρ
  | .mk (.mk p e) rest, h, p', hp' => by
    simp only [checkMatch, checkMRule, Bool.and_eq_true] at h
    obtain ⟨⟨hp, _⟩, hrest⟩ := h
    unfold matchAPats at hp'
    rw [List.mem_cons] at hp'
    rcases hp' with rfl | hp'
    · exact ⟨hp, e.ty, rfl⟩
    · match rest, hrest, hp' with
      | some m, hrest, hp' =>
        simp only [checkMatchOptAt, Bool.and_eq_true, decide_eq_true_eq] at hrest
        obtain ⟨hc, hty⟩ := checkMatch_pats m hrest.1 p' hp'
        refine ⟨hc, ?_⟩
        obtain ⟨ρ, hρ⟩ := hty
        refine ⟨ρ, ?_⟩
        rw [← hρ, hrest.2]
        rfl
      | none, _, hp' => simp at hp'

/-- What a site's restriction says. -/
def Restr (tbl : ConTable) : SKind → Ty → List PatN → Prop
  | .exh, τ, ps => ExhProp tbl τ ps
  | .case, τ, ps => MatchOK tbl τ ps

/-- A site of the bare phrase in a derivation that meets the further restrictions: its patterns,
    annotated, check in a context whose constructors are C0's, at one type, where the restriction
    holds. -/
def SiteHolds (tbl : ConTable) (C0 : Ctx) (s : BSite) : Prop :=
  ∃ (C : Ctx) (τ : Ty) (aps : List APat), CtxInv C0 C ∧ aps.map APat.erase = s.pats ∧
    (∀ p ∈ aps, checkPat C p = true ∧ p.ty = τ) ∧ Restr tbl s.kind τ (aps.map normPat)

theorem site_atpat {tbl : ConTable} {C0 C : Ctx} {p : AAtPat} (hinv : CtxInv C0 C) (hc : checkAtPat C p = true)
    (hf : ExhProp tbl p.ty [normAtPat p]) : SiteHolds tbl C0 ⟨.exh, [.atpat p.erase]⟩ :=
  ⟨C, p.ty, [.atpat p], hinv, rfl, by simpa [checkPat, APat.ty] using hc, by simpa [Restr, normPat] using hf⟩

section sites
variable (tbl : ConTable) (C0 : Ctx)

mutual
theorem sAtExp : ∀ (a : AAtExp) (C : Ctx), CtxInv C0 C → checkAtExp C a = true → FurtherAtExp tbl a →
    ∀ s ∈ bsAtExp a.erase, SiteHolds tbl C0 s
  | .scon _ _, _, _, _, _, s, hs => by simp [AAtExp.erase, bsAtExp] at hs
  | .var _ _ _, _, _, _, _, s, hs => by simp [AAtExp.erase, bsAtExp] at hs
  | .con _ _ _, _, _, _, _, s, hs => by simp [AAtExp.erase, bsAtExp] at hs
  | .op _ _ _, _, _, _, _, s, hs => by simp [AAtExp.erase, bsAtExp] at hs
  | .unit, _, _, _, _, s, hs => by simp [AAtExp.erase, bsAtExp] at hs
  | .nil _, _, _, _, _, s, hs => by simp [AAtExp.erase, bsAtExp] at hs
  | .tuple e1 e2 e3, C, hinv, hc, hf, s, hs => by
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [FurtherAtExp] at hf
    simp only [AAtExp.erase, bsAtExp, List.mem_append] at hs
    rcases hs with (hs | hs) | hs
    · exact sExp e1 C hinv hc.1.1 hf.1 s hs
    · exact sExp e2 C hinv hc.1.2 hf.2.1 s hs
    · exact sExpOpt e3 C hinv hc.2 hf.2.2 s hs
  | .record row, C, hinv, hc, hf, s, hs => by
    simp only [checkAtExp] at hc
    simp only [FurtherAtExp] at hf
    simp only [AAtExp.erase, bsAtExp] at hs
    exact sRowOpt row C hinv hc hf s hs
  | .update _ _ _ row, C, hinv, hc, hf, s, hs => by
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [FurtherAtExp] at hf
    simp only [AAtExp.erase, bsAtExp] at hs
    exact sRow row C hinv hc.1.2 hf s hs
  | .letE d e, C, hinv, hc, hf, s, hs => by
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [FurtherAtExp] at hf
    simp only [AAtExp.erase, bsAtExp, List.mem_append] at hs
    rcases hs with hs | hs
    · exact sDec d C hinv hc.1 hf.1 s hs
    · have hv : AllV (d.result C) := by
        match d, hc with
        | .val VE vb, hc =>
          have h1 := hc.1
          simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at h1
          simp only [ADec.result]
          rw [← h1.2]
          exact allV_closGroup (allV_vb vb)
      exact sExp e _ (ctxInv_plusVE hv hinv) hc.2 hf.2 s hs
  | .paren e, C, hinv, hc, hf, s, hs => by
    simp only [checkAtExp] at hc
    simp only [FurtherAtExp] at hf
    simp only [AAtExp.erase, bsAtExp] at hs
    exact sExp e C hinv hc hf s hs
theorem sRow : ∀ (r : AExpRow) (C : Ctx), CtxInv C0 C → checkExpRow C r = true → FurtherExpRow tbl r →
    ∀ s ∈ bsExpRow r.erase, SiteHolds tbl C0 s
  | .field _ e rest, C, hinv, hc, hf, s, hs => by
    simp only [checkExpRow, Bool.and_eq_true] at hc
    simp only [FurtherExpRow] at hf
    simp only [AExpRow.erase, bsExpRow, List.mem_append] at hs
    rcases hs with hs | hs
    · exact sExp e C hinv hc.1 hf.1 s hs
    · exact sRowOpt rest C hinv hc.2 hf.2 s hs
theorem sRowOpt : ∀ (r : Option AExpRow) (C : Ctx), CtxInv C0 C → checkExpRowOpt C r = true →
    FurtherExpRowOpt tbl r → ∀ s ∈ bsExpRowOpt (AExpRow.eraseOpt r), SiteHolds tbl C0 s
  | none, _, _, _, _, s, hs => by simp [AExpRow.eraseOpt, bsExpRowOpt] at hs
  | some r, C, hinv, hc, hf, s, hs => by
    simp only [checkExpRowOpt] at hc
    simp only [FurtherExpRowOpt] at hf
    simp only [AExpRow.eraseOpt, bsExpRowOpt] at hs
    exact sRow r C hinv hc hf s hs
theorem sExp : ∀ (a : AExp) (C : Ctx), CtxInv C0 C → checkExp C a = true → FurtherExp tbl a →
    ∀ s ∈ bsExp a.erase, SiteHolds tbl C0 s
  | .atexp a, C, hinv, hc, hf, s, hs => by
    simp only [checkExp] at hc
    simp only [FurtherExp] at hf
    simp only [AExp.erase, bsExp] at hs
    exact sAtExp a C hinv hc hf s hs
  | .app e a, C, hinv, hc, hf, s, hs => by
    simp only [checkExp, Bool.and_eq_true] at hc
    simp only [FurtherExp] at hf
    simp only [AExp.erase, bsExp, List.mem_append] at hs
    rcases hs with hs | hs
    · exact sExp e C hinv hc.1.1 hf.1 s hs
    · exact sAtExp a C hinv hc.1.2 hf.2 s hs
  | .lam p e, C, hinv, hc, hf, s, hs => by
    simp only [checkExp, Bool.and_eq_true] at hc
    simp only [FurtherExp] at hf
    simp only [AExp.erase, bsExp, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact site_atpat hinv hc.1 hf.1
    · exact sExp e _ (ctxInv_plusVE (allV_atpat p) hinv) hc.2 hf.2 s hs
  | .caseE e m, C, hinv, hc, hf, s, hs => by
    simp only [checkExp, Bool.and_eq_true] at hc
    obtain ⟨⟨hce, hcm⟩, hty⟩ := hc
    simp only [FurtherExp] at hf
    simp only [AExp.erase, bsExp, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · refine ⟨C, e.ty, matchAPats m, hinv, (bMatchPats_erase m).symm, ?_, ?_⟩
      · intro p hp
        obtain ⟨hcp, ρ, hρ⟩ := checkMatch_pats m hcm p hp
        refine ⟨hcp, ?_⟩
        rw [hρ] at hty
        simpa using hty
      · simp only [Restr]
        rw [← matchPats_eq]
        exact hf.2.1
    · exact sExp e C hinv hce hf.1 s hs
    · exact sMatch m C hinv hcm hf.2.2 s hs
theorem sExpOpt : ∀ (e : Option AExp) (C : Ctx), CtxInv C0 C → checkExpOpt C e = true → FurtherExpOpt tbl e →
    ∀ s ∈ bsExpOpt (AExp.eraseOpt e), SiteHolds tbl C0 s
  | none, _, _, _, _, s, hs => by simp [AExp.eraseOpt, bsExpOpt] at hs
  | some e, C, hinv, hc, hf, s, hs => by
    simp only [checkExpOpt] at hc
    simp only [FurtherExpOpt] at hf
    simp only [AExp.eraseOpt, bsExpOpt] at hs
    exact sExp e C hinv hc hf s hs
theorem sMatch : ∀ (m : AMatch) (C : Ctx), CtxInv C0 C → checkMatch C m = true → FurtherMatch tbl m →
    ∀ s ∈ bsMatch m.erase, SiteHolds tbl C0 s
  | .mk (.mk p e) rest, C, hinv, hc, hf, s, hs => by
    simp only [checkMatch, checkMRule, Bool.and_eq_true] at hc
    simp only [FurtherMatch] at hf
    simp only [AMatch.erase, AMRule.erase, bsMatch, List.mem_append] at hs
    rcases hs with hs | hs
    · exact sExp e _ (ctxInv_plusVE (allV_pat p) hinv) hc.1.2 hf.1 s hs
    · exact sMatchOpt rest C _ hinv hc.2 hf.2 s hs
theorem sMatchOpt : ∀ (m : Option AMatch) (C : Ctx) (τ : Ty), CtxInv C0 C → checkMatchOptAt C τ m = true →
    FurtherMatchOpt tbl m → ∀ s ∈ bsMatchOpt (AMatch.eraseOpt m), SiteHolds tbl C0 s
  | none, _, _, _, _, _, s, hs => by simp [AMatch.eraseOpt, bsMatchOpt] at hs
  | some m, C, _, hinv, hc, hf, s, hs => by
    simp only [checkMatchOptAt, Bool.and_eq_true] at hc
    simp only [FurtherMatchOpt] at hf
    simp only [AMatch.eraseOpt, bsMatchOpt] at hs
    exact sMatch m C hinv hc.1 hf s hs
theorem sDec : ∀ (d : ADec) (C : Ctx), CtxInv C0 C → checkDec C d = true → FurtherDec tbl d →
    ∀ s ∈ bsDec d.erase, SiteHolds tbl C0 s
  | .val VE vb, C, hinv, hc, hf, s, hs => by
    simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [FurtherDec] at hf
    simp only [ADec.erase, bsDec] at hs
    have hv : AllV VE := hc.2 ▸ allV_vb vb
    exact sValBind vb _ (ctxInv_plusVE hv hinv) hc.1 hf s hs
theorem sValBind : ∀ (vb : AValBind) (C : Ctx), CtxInv C0 C → checkValBind C vb = true → FurtherValBind tbl vb →
    ∀ s ∈ bsValBind vb.erase, SiteHolds tbl C0 s
  | .var _ _ _ e rest, C, hinv, hc, hf, s, hs => by
    simp only [checkValBind, Bool.and_eq_true] at hc
    simp only [FurtherValBind] at hf
    simp only [AValBind.erase, bsValBind, List.mem_append] at hs
    rcases hs with hs | hs
    · exact sExp e _ (ctxInv_plusU hinv) hc.1.1.2 hf.1 s hs
    · exact sValBindOpt rest C hinv hc.2 hf.2 s hs
  | .pat p e, C, hinv, hc, hf, s, hs => by
    simp only [checkValBind, Bool.and_eq_true] at hc
    simp only [FurtherValBind] at hf
    simp only [AValBind.erase, bsValBind, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact site_atpat hinv hc.1.1 hf.1
    · exact sExp e C hinv hc.1.2 hf.2 s hs
theorem sValBindOpt : ∀ (vb : Option AValBind) (C : Ctx), CtxInv C0 C → checkValBindOpt C vb = true →
    FurtherValBindOpt tbl vb → ∀ s ∈ bsValBindOpt (AValBind.eraseOpt vb), SiteHolds tbl C0 s
  | none, _, _, _, _, s, hs => by simp [AValBind.eraseOpt, bsValBindOpt] at hs
  | some vb, C, hinv, hc, hf, s, hs => by
    simp only [checkValBindOpt] at hc
    simp only [FurtherValBindOpt] at hf
    simp only [AValBind.eraseOpt, bsValBindOpt] at hs
    exact sValBind vb C hinv hc hf s hs
end

/-- A declaration phrase without type declarations or ports: its environment has no type and no
    qualified environment, only values, and every site meets its restriction. -/
theorem sTop : ∀ (d : ATopDec) (C : Ctx) (E : Env) (PE : PortEnv), CtxInv C0 C → noTypesB d.erase = true →
    checkTopDec C d = some (E, PE) →
    (E.QE = [] ∧ E.TE = [] ∧ AllV E.VE) ∧ (FurtherTopDec tbl d → ∀ s ∈ bsTop d.erase, SiteHolds tbl C0 s)
  | .value VE vb, C, E, PE, hinv, _, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv : AllV VE := hc.2 ▸ allV_vb vb
      refine ⟨⟨rfl, rfl, allV_closGroup hv⟩, ?_⟩
      intro hf s hs
      simp only [FurtherTopDec] at hf
      simp only [ATopDec.erase, bsTop] at hs
      exact sValBind tbl C0 vb _ (ctxInv_plusVE hv hinv) hc.1 hf s hs
    · cases h
  | .types _ _ _ _, _, _, _, _, hn, _ => by simp [ATopDec.erase, noTypesB] at hn
  | .port _ _ _, _, _, _, _, hn, _ => by simp [ATopDec.erase, noTypesB] at hn
  | .typesSplit a1 a2, C, E, PE, _, hn, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hs
      obtain ⟨db, tbs1, tbs2, h1e, h2e, _, _⟩ := splitShape_spec hs
      have : (ATopDec.typesSplit a1 a2).erase = .types db (tbs1 ++ tbs2) := by
        simp only [ATopDec.erase, h1e, h2e]
      rw [this] at hn
      simp [noTypesB] at hn
    · cases h
  | .seq a1 a2, C, E, PE, hinv, hn, h => by
    simp only [ATopDec.erase, noTypesB, Bool.and_eq_true] at hn
    simp only [checkTopDec] at h
    split at h
    · rename_i E1 PE1 h1
      split at h
      · rename_i E2 PE2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨⟨q1, t1, v1⟩, s1⟩ := sTop a1 C E1 PE1 hinv hn.1 h1
        have hinv2 := ctxInv_oplusE q1 v1 hinv
        obtain ⟨⟨q2, t2, v2⟩, s2⟩ := sTop a2 _ E2 PE2 hinv2 hn.2 h2
        refine ⟨⟨?_, ?_, allV_modify v1 v2⟩, ?_⟩
        · simp [Env.plus, q1, q2, FMap.modify]
        · simp [Env.plus, t1, t2, FMap.modify]
        · intro hf s hs
          simp only [FurtherTopDec] at hf
          simp only [ATopDec.erase, bsTop, List.mem_append] at hs
          rcases hs with hs | hs
          · exact s1 hf.1 s hs
          · exact s2 hf.2 s hs
      · cases h
    · cases h

end sites

/-! ## Failing sites -/

mutual
/-- p subsumes q: every inhabitant q covers, p covers. -/
def subsB : PatN → PatN → Bool
  | .wild, _ => true
  | .den d, .den d' => decide (d = d')
  | .con k args, .con k' args' => k == k' && subsListB args args'
  | _, _ => false
def subsListB : List PatN → List PatN → Bool
  | [], [] => true
  | p :: ps, q :: qs => subsB p q && subsListB ps qs
  | _, _ => false
end

theorem subsListB_length : ∀ {ps qs : List PatN}, subsListB ps qs = true → ps.length = qs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [subsListB, Bool.and_eq_true] at h
    simp [subsListB_length h.2]
  | [], _ :: _, h => by simp [subsListB] at h
  | _ :: _, [], h => by simp [subsListB] at h

mutual
theorem subs_covers : ∀ (p q : PatN) (h : Inh), subsB p q = true → q.covers h → p.covers h
  | .wild, _, _, _, _ => by simp [PatN.covers]
  | .den d, .den d', h, hs, hc => by
    simp only [subsB, decide_eq_true_eq] at hs
    subst hs; exact hc
  | .con k args, .con k' args', h, hs, hc => by
    simp only [subsB, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨rfl, hs⟩ := hs
    simp only [PatN.covers] at hc ⊢
    rw [subsListB_length hs]
    exact ⟨hc.1, subsList_covers args args' h 0 hs hc.2⟩
  | .den _, .wild, _, hs, _ => by simp [subsB] at hs
  | .den _, .con _ _, _, hs, _ => by simp [subsB] at hs
  | .con _ _, .wild, _, hs, _ => by simp [subsB] at hs
  | .con _ _, .den _, _, hs, _ => by simp [subsB] at hs
theorem subsList_covers : ∀ (ps qs : List PatN) (h : Inh) (i : Nat), subsListB ps qs = true →
    PatN.coversArgs qs h i → PatN.coversArgs ps h i
  | [], [], _, _, _, _ => by simp [PatN.coversArgs]
  | p :: ps, q :: qs, h, i, hs, hc => by
    simp only [subsListB, Bool.and_eq_true] at hs
    simp only [PatN.coversArgs] at hc ⊢
    exact ⟨subs_covers p q _ hs.1 hc.1, subsList_covers ps qs h (i + 1) hs.2 hc.2⟩
  | [], _ :: _, _, _, hs, _ => by simp [subsListB] at hs
  | _ :: _, [], _, _, hs, _ => by simp [subsListB] at hs
end

/-- Some pattern is subsumed by an earlier one. -/
def irrSubsB (ps : List PatN) : Bool :=
  (List.range ps.length).any fun j => (List.range j).any fun i => subsB (ps.getD i .wild) (ps.getD j .wild)

theorem not_irr_of_subs {tbl : ConTable} {τ : Ty} {ps : List PatN} (h : irrSubsB ps = true) : ¬ IrrProp tbl τ ps := by
  intro hirr
  simp only [irrSubsB, List.any_eq_true, List.mem_range] at h
  obtain ⟨j, hj, i, hi, hs⟩ := h
  obtain ⟨hh, _, hcj, hn⟩ := hirr j hj
  have e1 : ps.getD i .wild = ps[i]'(by omega) := by simp [List.getD_eq_getElem?_getD, show i < ps.length by omega]
  have e2 : ps.getD j .wild = ps[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [e1, e2] at hs
  exact hn i hi (subs_covers _ _ hh hs hcj)

/-- A non-exhaustive vector of rows, decided at a type where they are typed. -/
theorem not_exh_of_useful {tbl : ConTable} {τ : Ty} {ps : List PatN} (hty : ∀ p ∈ ps, PTyped tbl τ p) (f : Nat)
    (hu : useful tbl .exh f [τ] (ps.map ([·])) [.wild] = some true) : ¬ ExhProp tbl τ ps := by
  intro hE
  have hspec := useful_spec tbl .exh f [τ] (ps.map ([·])) [.wild] true hu (by simp [PTypedList, PTyped]) (by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    simp only [PTypedList]
    exact ⟨hty p hp, trivial⟩)
  obtain ⟨hs, hw, _, hn⟩ := hspec.mp rfl
  match hs, hw with
  | [h], ⟨hinh, _⟩ =>
    obtain ⟨p, hp, hc⟩ := hE h hinh
    exact hn [p] (List.mem_map.mpr ⟨p, hp, rfl⟩) ⟨hc, trivial⟩

/-- The fuel the decider gives the usefulness algorithm (that of `exhDec`). -/
def exhFuel (ps : List PatN) : Nat := matSize (ps.map ([·])) [.wild] * 4 + 8

/-- At τ0 the patterns fit and are not exhaustive. -/
def exhFailAtB (tbl : ConTable) (ps : List PatN) (τ0 : Ty) : Bool :=
  ps.all (fitsB tbl τ0) && useful tbl .exh (exhFuel ps) [τ0] (ps.map ([·])) [.wild] == some true

/-- A site that fails in every derivation: redundant whatever the type, or with constructor patterns
    the table agrees with, not exhaustive at a reference type. -/
def siteFailB (tbl : ConTable) (C0 : Ctx) (τs0 : List Ty) (s : BSite) : Bool :=
  (decide (s.kind = .case) && irrSubsB (s.pats.map nPat)) ||
  (s.pats.all (cOK tbl C0) && τs0.any (exhFailAtB tbl (s.pats.map nPat)))

theorem siteFail_false {tbl : ConTable} {C0 : Ctx} {τs0 : List Ty} {s : BSite} (hbi : builtinsOKB tbl = true)
    (hfail : siteFailB tbl C0 τs0 s = true) (hs : SiteHolds tbl C0 s) : False := by
  obtain ⟨C, τ, aps, hinv, herase, hchk, hres⟩ := hs
  have hps : s.pats.map nPat = aps.map normPat := by
    rw [← herase, List.map_map]
    exact List.map_congr_left (fun p _ => (norm_erase p).symm)
  have hexh : ExhProp tbl τ (aps.map normPat) := by
    cases hk : s.kind
    · rw [hk] at hres; exact hres
    · rw [hk] at hres; exact hres.1
  simp only [siteFailB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true] at hfail
  rcases hfail with ⟨hk, hirr⟩ | ⟨hok, τ0, _, hτ0⟩
  · rw [hk] at hres
    rw [hps] at hirr
    exact not_irr_of_subs hirr hres.2
  · simp only [exhFailAtB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hτ0
    obtain ⟨hf0, hu⟩ := hτ0
    rw [hps] at hf0 hu
    have hfit : ∀ p ∈ aps.map normPat, fitsB tbl τ p = true := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨hcp, hpt⟩ := hchk p hp
      have hcok : cOK tbl C0 p.erase = true := hok _ (herase ▸ List.mem_map_of_mem hp)
      rw [← hpt]
      exact fitsPat tbl C0 hbi p C hinv hcp hcok
    have hagree := useful_agree tbl .exh (exhFuel (aps.map normPat)) [τ] [τ0] ((aps.map normPat).map ([·])) [.wild]
      (by simp [fitsListB, fitsB]) (by simp [fitsListB, fitsB]) (by
        intro r hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        simp [fitsListB, hfit q hq, hf0 q hq])
    rw [← hagree] at hu
    exact not_exh_of_useful (fun p hp => ptyped_of_fits tbl τ p (hfit p hp)) _ hu hexh

/-! ## The reference types: those the inference's derivation gives its sites -/

mutual
def tAtExp : AAtExp → List Ty
  | .tuple e1 e2 e3 => tExp e1 ++ tExp e2 ++ tExpOpt e3
  | .record row => tRowOpt row
  | .update _ _ _ row => tRow row
  | .letE d e => tDec d ++ tExp e
  | .paren e => tExp e
  | _ => []
def tRow : AExpRow → List Ty
  | .field _ e rest => tExp e ++ tRowOpt rest
def tRowOpt : Option AExpRow → List Ty
  | none => []
  | some r => tRow r
def tExp : AExp → List Ty
  | .atexp a => tAtExp a
  | .app e a => tExp e ++ tAtExp a
  | .lam p e => p.ty :: tExp e
  | .caseE e m => e.ty :: (tExp e ++ tMatch m)
def tExpOpt : Option AExp → List Ty
  | none => []
  | some e => tExp e
def tMatch : AMatch → List Ty
  | .mk (.mk _ e) rest => tExp e ++ tMatchOpt rest
def tMatchOpt : Option AMatch → List Ty
  | none => []
  | some m => tMatch m
def tDec : ADec → List Ty
  | .val _ vb => tValBind vb
def tValBind : AValBind → List Ty
  | .var _ _ _ e rest => tExp e ++ tValBindOpt rest
  | .pat p e => p.ty :: tExp e
def tValBindOpt : Option AValBind → List Ty
  | none => []
  | some vb => tValBind vb
end

def tTop : ATopDec → List Ty
  | .value _ vb => tValBind vb
  | .seq a1 a2 | .typesSplit a1 a2 => tTop a1 ++ tTop a2
  | _ => []

/-- The types the inference gives the sites of a module (no hypothesis about them is needed). -/
def refTys (B : SBasis) (C0 : Ctx) (m : BModule) : List Ty :=
  match inferModuleIn B C0 m with
  | .ok a0 =>
    match a0.body with
    | some d0 => tTop d0
    | none => []
  | .error _ => []

theorem resultIn_spec {B : SBasis} {C : Ctx} {a : AModule} {B' : SBasis} {E : Env}
    (h : a.resultIn B C = some (B', E)) : ∃ PE, checkTopDecOpt C a.body = some (E, PE) := by
  unfold AModule.resultIn at h
  split at h
  · cases h
  · rename_i E' PE hd
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨PE, hd⟩

/-- Every derivation of a module with a failing site fails the further restrictions. -/
theorem refute {B : SBasis} {m : BModule} {C0 : Ctx} {d : BTopDec} {s : BSite} {τs0 : List Ty}
    (hctx : importCtx B m.imports = some C0) (hbody : m.body = some d) (hnt : noTypesB d = true)
    (hbi : builtinsOKB (conTable B Env.empty) = true) (hs : s ∈ bsTop d)
    (hfail : siteFailB (conTable B Env.empty) C0 τs0 s = true)
    (a : AModule) (he : a.erase = m) (hck : checkModule B a = true) : ¬ FurtherMod B a := by
  have himp : a.imports = m.imports := by rw [← he]; rfl
  have hctxa : importCtx B a.imports = some C0 := himp ▸ hctx
  have hb : a.body.map ATopDec.erase = some d := by rw [← hbody, ← he]; rfl
  obtain ⟨d', hd', hde⟩ := Option.map_eq_some_iff.mp hb
  unfold checkModule at hck
  rw [AModule.result_of_ctx hctxa] at hck
  obtain ⟨⟨B', E⟩, hres⟩ := Option.isSome_iff_exists.mp hck
  obtain ⟨PE, hchk⟩ := resultIn_spec hres
  rw [hd'] at hchk
  simp only [checkTopDecOpt] at hchk
  intro hf
  unfold FurtherMod at hf
  rw [AModule.result_of_ctx hctxa, hres] at hf
  simp only [FurtherModIn, hd'] at hf
  obtain ⟨⟨hQE, hTE, _⟩, hsites⟩ :=
    sTop (conTable B E) C0 d' C0 E PE (ctxInv_refl C0) (hde ▸ hnt) hchk
  have htbl : conTable B E = conTable B Env.empty := by
    simp only [conTable, hQE, hTE]; rfl
  have := hsites hf s (hde ▸ hs)
  rw [htbl] at this
  exact siteFail_false hbi hfail this

end StandardElm.Stat.RFurther

namespace StandardElm.Stat
open StandardElm.Stat.RFurther

/-- The decider of refusals by the further restrictions: a program of one module, without type
    declarations or ports, with a site that fails in every derivation (RFurther.siteFailB). -/
def furtherFailB (B : SBasis) (sp : Src.SProgram) : Bool :=
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | [m] =>
    match importCtx B m.imports, m.body with
    | some C0, some d =>
      noTypesB d && builtinsOKB (conTable B Env.empty) &&
        (bsTop d).any (siteFailB (conTable B Env.empty) C0 (refTys B C0 m))
    | _, _ => false
  | _ => false

theorem not_legal_of_furtherFailB {B : SBasis} {sp : Src.SProgram} (h : furtherFailB B sp = true) :
    ¬ LegalProgram B sp := by
  unfold furtherFailB at h
  split at h
  · rename_i m hms
    split at h
    · rename_i C0 d hctx hbody
      simp only [Bool.and_eq_true, List.any_eq_true] at h
      obtain ⟨⟨hnt, hbi⟩, s, hs, hfail⟩ := h
      exact not_legal_of_further hms (fun a he hck => refute hctx hbody hnt hbi hs hfail a he hck)
    · cases h
  · cases h

end StandardElm.Stat
