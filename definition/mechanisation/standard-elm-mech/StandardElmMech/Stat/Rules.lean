/-
  A Standard Definition of Elm? Mechanisation: the inference rules of Chapter 4 (static-core.tex,
  sec:static-core-rules), plan step 9 (section 4). One relation constructor per rule, named
  r_s_<slug> after the rule's label r:s-<slug>, with "-" written "_": 45 in all. Options and
  sequences are small auxiliary relations whose constructors are not rules of the book (opt_none,
  opt_some, seq_nil, seq_cons), as for the dynamic rules.

  Judgement forms:
    C ⊢ ty ⇒ τ, C ⊢ tyrow ⇒ ρ                         ElTy, ElTyRow
    C ⊢ atpat ⇒ (VE, τ), C ⊢ patrow ⇒ (VE, ρ), ...    ElAtPat, ElPatRow, ElPat
    C ⊢ atexp ⇒ τ, ..., C ⊢ dec ⇒ VE, C ⊢ valbind ⇒ VE

  The phrases are those of the bare syntax (Src/Bare.lean): the derived forms of Appendix A have
  been applied, and type expressions and annotations are kept.
-/
import StandardElmMech.Generated.StaticBasis

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind SLit)

set_option autoImplicit true

mutual
/-- C ⊢ ty ⇒ τ -/
inductive ElTy : Ctx → BTy → Ty → Prop where
  /-- r:s-ty-tyvar -/
  | r_s_ty_tyvar : BVar.ty (.named a) ∈ C.U → ElTy C (.tyvar a) (.var (.named a))
  /-- r:s-ty-rowvar -/
  | r_s_ty_rowvar : classOfName a = .any → BVar.row (.named a) ∈ C.U →
      ElTy C (.tyvar a) (.record [] (some (.named a)))
  /-- r:s-ty-record -/
  | r_s_ty_record : ElTyRowOpt C row ρ → ElTy C (.record row) (.record ρ none)
  /-- r:s-ty-openrecord -/
  | r_s_ty_openrecord : classOfName r = .any → BVar.row (.named r) ∈ C.U → ElTyRow C row ρ →
      ElTy C (.openRecord r row) (.record ρ (some (.named r)))
  /-- r:s-ty-unit -/
  | r_s_ty_unit : ElTy C .unit tUnitTy
  /-- r:s-ty-tuple -/
  | r_s_ty_tuple : ElTy C t1 τ1 → ElTy C t2 τ2 → ElTyOpt C t3 τ3 →
      ElTy C (.tuple t1 t2 t3) (tupleTy τ1 τ2 τ3)
  /-- r:s-ty-con -/
  | r_s_ty_con : C.lookupTy c = some (θ, VE) → ElTyList C args τs → θ.apply τs = some τ →
      ElTy C (.con c args) τ
  /-- r:s-ty-fun -/
  | r_s_ty_fun : ElTy C t1 τ1 → ElTy C t2 τ2 → ElTy C (.fn t1 t2) (.fn τ1 τ2)
  /-- r:s-ty-paren -/
  | r_s_ty_paren : ElTy C t τ → ElTy C (.paren t) τ
/-- C ⊢ tyrow ⇒ ρ -/
inductive ElTyRow : Ctx → BTyRow → Row → Prop where
  /-- r:s-tyrow -/
  | r_s_tyrow : ElTy C t τ → ElTyRowOpt C rest ρ →
      ElTyRow C (.field l t rest) (Row.modify [(l, τ)] ρ)
inductive ElTyRowOpt : Ctx → Option BTyRow → Row → Prop where
  | opt_none : ElTyRowOpt C none []
  | opt_some : ElTyRow C row ρ → ElTyRowOpt C (some row) ρ
inductive ElTyOpt : Ctx → Option BTy → Option Ty → Prop where
  | opt_none : ElTyOpt C none none
  | opt_some : ElTy C t τ → ElTyOpt C (some t) (some τ)
inductive ElTyList : Ctx → List BTy → List Ty → Prop where
  | seq_nil : ElTyList C [] []
  | seq_cons : ElTy C t τ → ElTyList C ts τs → ElTyList C (t :: ts) (τ :: τs)
end

mutual
/-- C ⊢ atpat ⇒ (VE, τ) -/
inductive ElAtPat : Ctx → BAtPat → ValEnv → Ty → Prop where
  /-- r:s-atpat-wild -/
  | r_s_atpat_wild : ElAtPat C .wild [] τ
  /-- r:s-atpat-scon -/
  | r_s_atpat_scon : Gen (typeOf sc) τ → τ ∈ [tIntTy, tCharTy, tStringTy] →
      ElAtPat C (.scon sc) [] τ
  /-- r:s-atpat-var -/
  | r_s_atpat_var : ElAtPat C (.var x) [(x, (mono τ, .v))] τ
  /-- r:s-atpat-con -/
  | r_s_atpat_con : C.lookupVal lc = some (σ, .c) → Gen σ (.con τs t) →
      ElAtPat C (.con lc) [] (.con τs t)
  /-- r:s-atpat-unit -/
  | r_s_atpat_unit : ElAtPat C .unit [] tUnitTy
  /-- r:s-atpat-tuple -/
  | r_s_atpat_tuple : ElPat C p1 VE1 τ1 → ElPat C p2 VE2 τ2 → ElPatOpt C p3 VE3 τ3 →
      ElAtPat C (.tuple p1 p2 p3) (FMap.modify (FMap.modify VE1 VE2) VE3) (tupleTy τ1 τ2 τ3)
  /-- r:s-atpat-nil -/
  | r_s_atpat_nil : ElAtPat C .nil [] (listTy τ)
  /-- r:s-atpat-record -/
  | r_s_atpat_record : ElPatRowOpt C row VE ρ → τ = .record ρτ tl → Row.Sub ρ ρτ →
      ElAtPat C (.record row) VE τ
  /-- r:s-atpat-paren -/
  | r_s_atpat_paren : ElPat C p VE τ → ElAtPat C (.paren p) VE τ
/-- C ⊢ patrow ⇒ (VE, ρ); the variable is the one spelt as the label. -/
inductive ElPatRow : Ctx → BPatRow → ValEnv → Row → Prop where
  /-- r:s-patrow -/
  | r_s_patrow : ElPatRowOpt C rest VE ρ →
      ElPatRow C (.field l rest) (FMap.modify [(l, (mono τ, .v))] VE) (Row.modify [(l, τ)] ρ)
/-- C ⊢ pat ⇒ (VE, τ) -/
inductive ElPat : Ctx → BPat → ValEnv → Ty → Prop where
  /-- r:s-pat-atpat -/
  | r_s_pat_atpat : ElAtPat C a VE τ → ElPat C (.atpat a) VE τ
  /-- r:s-pat-con -/
  | r_s_pat_con : C.lookupVal lc = some (σ, .c) → Gen σ (arrows τs (.con τs' t)) →
      ElAtPatList C args VEs τs → ElPat C (.con lc args) (FMap.plusAll VEs) (.con τs' t)
  /-- r:s-pat-cons -/
  | r_s_pat_cons : ElPat C p1 VE1 τ → ElPat C p2 VE2 (listTy τ) →
      ElPat C (.cons p1 p2) (FMap.modify VE1 VE2) (listTy τ)
  /-- r:s-pat-as -/
  | r_s_pat_as : ElPat C p VE τ → ElPat C (.as p x) (FMap.modify VE [(x, (mono τ, .v))]) τ
inductive ElPatOpt : Ctx → Option BPat → ValEnv → Option Ty → Prop where
  | opt_none : ElPatOpt C none [] none
  | opt_some : ElPat C p VE τ → ElPatOpt C (some p) VE (some τ)
inductive ElPatRowOpt : Ctx → Option BPatRow → ValEnv → Row → Prop where
  | opt_none : ElPatRowOpt C none [] []
  | opt_some : ElPatRow C row VE ρ → ElPatRowOpt C (some row) VE ρ
inductive ElAtPatList : Ctx → List BAtPat → List ValEnv → List Ty → Prop where
  | seq_nil : ElAtPatList C [] [] []
  | seq_cons : ElAtPat C a VE τ → ElAtPatList C as VEs τs → ElAtPatList C (a :: as) (VE :: VEs) (τ :: τs)
end

/-- The first option of r:s-valbind-var: U' is new for ty in C, ty elaborates to τ in C + U', and
    U' ∩ tyvars C = ∅. -/
inductive AnnOK : Ctx → Option BTy → List BVar → Ty → Prop where
  | opt_none : AnnOK C none [] τ
  | opt_some : NewFor U' ty C.U → ElTy (C.plusU U') ty τ → (∀ v ∈ U', v ∉ C.tyvars) →
      AnnOK C (some ty) U' τ

mutual
/-- C ⊢ atexp ⇒ τ -/
inductive ElAtExp : Ctx → BAtExp → Ty → Prop where
  /-- r:s-atexp-scon -/
  | r_s_atexp_scon : Gen (typeOf sc) τ → ElAtExp C (.scon sc) τ
  /-- r:s-atexp-longvar -/
  | r_s_atexp_longvar : C.lookupVal lv = some (σ, is) → Gen σ τ → ElAtExp C (.var lv) τ
  /-- r:s-atexp-longcon -/
  | r_s_atexp_longcon : C.lookupVal lc = some (σ, is) → Gen σ τ → ElAtExp C (.con lc) τ
  /-- r:s-atexp-op -/
  | r_s_atexp_op : OTstat o = some (σ, is) → Gen σ τ → ElAtExp C (.op o) τ
  /-- r:s-atexp-unit -/
  | r_s_atexp_unit : ElAtExp C .unit tUnitTy
  /-- r:s-atexp-tuple -/
  | r_s_atexp_tuple : ElExp C e1 τ1 → ElExp C e2 τ2 → ElExpOpt C e3 τ3 →
      ElAtExp C (.tuple e1 e2 e3) (tupleTy τ1 τ2 τ3)
  /-- r:s-atexp-nil -/
  | r_s_atexp_nil : ElAtExp C .nil (listTy τ)
  /-- r:s-atexp-record -/
  | r_s_atexp_record : ElExpRowOpt C row ρ → ElAtExp C (.record row) (.record ρ none)
  /-- r:s-atexp-update -/
  | r_s_atexp_update : ElAtExp C (.var ⟨none, x⟩) τ → τ = .record ρτ tl → ElExpRow C row ρ →
      Row.Sub ρ ρτ → ElAtExp C (.update x row) τ
  /-- r:s-atexp-let -/
  | r_s_atexp_let : ElDec C d VE → ElExp (C.plusVE VE) e τ → ElAtExp C (.letE d e) τ
  /-- r:s-atexp-paren -/
  | r_s_atexp_paren : ElExp C e τ → ElAtExp C (.paren e) τ
/-- C ⊢ exprow ⇒ ρ -/
inductive ElExpRow : Ctx → BExpRow → Row → Prop where
  /-- r:s-exprow -/
  | r_s_exprow : ElExp C e τ → ElExpRowOpt C rest ρ →
      ElExpRow C (.field l e rest) (Row.modify [(l, τ)] ρ)
/-- C ⊢ exp ⇒ τ -/
inductive ElExp : Ctx → BExp → Ty → Prop where
  /-- r:s-exp-atexp -/
  | r_s_exp_atexp : ElAtExp C a τ → ElExp C (.atexp a) τ
  /-- r:s-exp-app -/
  | r_s_exp_app : ElExp C e (.fn τ' τ) → ElAtExp C a τ' → ElExp C (.app e a) τ
  /-- r:s-exp-lambda -/
  | r_s_exp_lambda : ElAtPat C p VE τ → ElExp (C.plusVE VE) e τ' → ElExp C (.lam p e) (.fn τ τ')
  /-- r:s-exp-case -/
  | r_s_exp_case : ElExp C e τ → ElMatch C m (.fn τ τ') → ElExp C (.caseE e m) τ'
/-- C ⊢ match ⇒ τ -/
inductive ElMatch : Ctx → BMatch → Ty → Prop where
  /-- r:s-match -/
  | r_s_match : ElMRule C mr τ → ElMatchOpt C rest τ → ElMatch C (.mk mr rest) τ
/-- C ⊢ mrule ⇒ τ -/
inductive ElMRule : Ctx → BMRule → Ty → Prop where
  /-- r:s-mrule -/
  | r_s_mrule : ElPat C p VE τ → ElExp (C.plusVE VE) e τ' → ElMRule C (.mk p e) (.fn τ τ')
/-- C ⊢ dec ⇒ VE -/
inductive ElDec : Ctx → BDec → ValEnv → Prop where
  /-- r:s-dec-group -/
  | r_s_dec_group : ElValBind (C.plusVE VE) vb VE → ElDec C (.val vb) (closGroup C.tyvars VE)
/-- C ⊢ valbind ⇒ VE -/
inductive ElValBind : Ctx → BValBind → ValEnv → Prop where
  /-- r:s-valbind-var -/
  | r_s_valbind_var : AnnOK C ann U' τ → ElExp (C.plusU U') e τ → ElValBindOpt C rest VE →
      ElValBind C (.var x ann e rest)
        (FMap.modify [(x, (if ann.isSome then annScheme U' τ else mono τ, .v))] VE)
  /-- r:s-valbind-pat -/
  | r_s_valbind_pat : ElAtPat C p VE τ → ElExp C e τ → ElValBind C (.pat p e) VE
inductive ElExpOpt : Ctx → Option BExp → Option Ty → Prop where
  | opt_none : ElExpOpt C none none
  | opt_some : ElExp C e τ → ElExpOpt C (some e) (some τ)
inductive ElExpRowOpt : Ctx → Option BExpRow → Row → Prop where
  | opt_none : ElExpRowOpt C none []
  | opt_some : ElExpRow C row ρ → ElExpRowOpt C (some row) ρ
inductive ElMatchOpt : Ctx → Option BMatch → Ty → Prop where
  | opt_none : ElMatchOpt C none τ
  | opt_some : ElMatch C m τ → ElMatchOpt C (some m) τ
inductive ElValBindOpt : Ctx → Option BValBind → ValEnv → Prop where
  | opt_none : ElValBindOpt C none []
  | opt_some : ElValBind C vb VE → ElValBindOpt C (some vb) VE
end

end StandardElm.Stat
