/-
  A Standard Definition of Elm? Mechanisation, part 4.
  The inference rules of Chapter 6 (dynamic-core.tex,
  sec:dynamic-core-rules), one relation constructor per numbered rule,
  named r_d_<slug> after the rule's label r:d-<slug>, with "-" written "_".

  Judgement forms:
    E ⊢ phrase ⇒ A           EvalAtExp, EvalExpRow, EvalExp, EvalDec, EvalValBind
    E, v ⊢ phrase ⇒ A        EvalMatch, EvalMRule, MatchAtPat, MatchPatRow, MatchPat
    v1 v2 ⇒ v                AppVal (application of values)

  The option convention (R6: the phrases in first options [ ] are all present
  or all absent) and the sequences "..." of r:d-pat-con are expressed by small
  auxiliary relations (`...Opt`, `MatchAtPats`), whose constructors are not
  rules of the book and are named opt_none / opt_some / seq_nil / seq_cons.
-/
import StandardElmMech.InitialBasis

namespace StandardElm

/-! ## Values of special constants (sec:dynamic-core-simple) -/

/-- val(scon). An integer constant at Int denotes norm(n); at Float the
    nearest float; a floating-point constant the nearest float. -/
def valof : SCon → Val
  | .int n => .int (norm n)
  | .intF n => .sv (.float (Float.ofNat n))
  | .float m e => .sv (.float (Float.ofScientific m (decide (e < 0)) e.natAbs))
  | .char c => .sv (.char c)
  | .str s => .sv (.str s)

/-! ## Operators

  An operator is looked up in no environment: its value is OT_dyn(opv), the
  dynamic operator table of Appendix D (InitialBasis.lean). -/

mutual

/-- Atomic Expressions: E ⊢ atexp ⇒ v -/
inductive EvalAtExp : Env → AtExp → Val → Prop where
  /-- r:d-atexp-scon -/
  | r_d_atexp_scon (E : Env) (sc : SCon) : EvalAtExp E (.scon sc) (valof sc)
  /-- r:d-atexp-var -/
  | r_d_atexp_var (E : Env) (lv : LongId) (v : Val) :
      E.lookup lv = some v → EvalAtExp E (.var lv) v
  /-- r:d-atexp-con -/
  | r_d_atexp_con (E : Env) (lc : LongId) (v : Val) :
      E.lookup lc = some v → EvalAtExp E (.con lc) v
  /-- r:d-atexp-op: (opv) ⇒ OT_dyn(opv). OT_dyn is a finite map, so the
      encoding states that opv is in its domain with value v. -/
  | r_d_atexp_op (E : Env) (o : Op) (v : Val) :
      OTdyn o = some v → EvalAtExp E (.op o) v
  /-- r:d-atexp-unit -/
  | r_d_atexp_unit (E : Env) : EvalAtExp E .unit .unit
  /-- r:d-atexp-tuple -/
  | r_d_atexp_tuple (E : Env) (e1 e2 : Exp) (e3 : Option Exp) (v1 v2 : Val) (v3 : Option Val) :
      EvalExp E e1 v1 → EvalExp E e2 v2 → EvalExpOpt E e3 v3 →
      EvalAtExp E (.tuple e1 e2 e3) (.tuple v1 v2 v3)
  /-- r:d-atexp-nil -/
  | r_d_atexp_nil (E : Env) : EvalAtExp E .nil Val.nil
  /-- r:d-atexp-record: { [exprow] } ⇒ ∅ [+ r] -/
  | r_d_atexp_record (E : Env) (row : Option ExpRow) (r : Record) :
      EvalExpRowOpt E row r → EvalAtExp E (.record row) (.record (fmPlus [] r))
  /-- r:d-atexp-update -/
  | r_d_atexp_update (E : Env) (x : Var) (row : ExpRow) (r r' : Record) :
      E.lookup ⟨none, x⟩ = some (.record r) → EvalExpRow E row r' →
      EvalAtExp E (.update x row) (.record (fmPlus r r'))
  /-- r:d-atexp-paren -/
  | r_d_atexp_paren (E : Env) (e : Exp) (v : Val) :
      EvalExp E e v → EvalAtExp E (.paren e) v
  /-- r:d-atexp-let -/
  | r_d_atexp_let (E : Env) (d : Dec) (e : Exp) (VE : ValEnv) (v : Val) :
      EvalDec E d VE → EvalExp (E.plusVE VE) e v → EvalAtExp E (.letE d e) v

/-- Expression Rows: E ⊢ exprow ⇒ r -/
inductive EvalExpRow : Env → ExpRow → Record → Prop where
  /-- r:d-exprow-field: lab = exp [, exprow] ⇒ {lab ↦ v} [+ r] -/
  | r_d_exprow_field (E : Env) (l : Lab) (e : Exp) (rest : Option ExpRow) (v : Val) (r : Record) :
      EvalExp E e v → EvalExpRowOpt E rest r →
      EvalExpRow E (.field l e rest) (fmPlus [(l, v)] r)

/-- Expressions: E ⊢ exp ⇒ v -/
inductive EvalExp : Env → Exp → Val → Prop where
  /-- r:d-exp-atexp -/
  | r_d_exp_atexp (E : Env) (a : AtExp) (v : Val) :
      EvalAtExp E a v → EvalExp E (.atexp a) v
  /-- r:d-exp-app -/
  | r_d_exp_app (E : Env) (e : Exp) (a : AtExp) (v1 v2 v : Val) :
      EvalExp E e v1 → EvalAtExp E a v2 → AppVal v1 v2 v → EvalExp E (.app e a) v
  /-- r:d-exp-lambda -/
  | r_d_exp_lambda (E : Env) (p : AtPat) (e : Exp) :
      EvalExp E (.lam p e) (.closure p e E [])
  /-- r:d-exp-case -/
  | r_d_exp_case (E : Env) (e : Exp) (m : Match) (v v' : Val) :
      EvalExp E e v → EvalMatch E v m (.ok v') → EvalExp E (.caseE e m) v'

/-- Application of Values: v1 v2 ⇒ v -/
inductive AppVal : Val → Val → Val → Prop where
  /-- r:d-app-closure -/
  | r_d_app_closure (p : AtPat) (e : Exp) (E : Env) (VE VE' : ValEnv) (v v' : Val) :
      MatchAtPat (E.plusVE (recVE VE)) v p (.ok VE') →
      EvalExp ((E.plusVE (recVE VE)).plusVE VE') e v' →
      AppVal (.closure p e E VE) v v'
  /-- r:d-app-con -/
  | r_d_app_con (c : Con) (vs : List Val) (v : Val) :
      AppVal (.con c vs) v (.con c (vs ++ [v]))
  /-- r:d-app-basic-partial -/
  | r_d_app_basic_partial (b : BasVal) (vs : List Val) (v : Val) :
      vs.length + 1 < b.arity → AppVal (.basApp b vs) v (.basApp b (vs ++ [v]))
  /-- r:d-app-basic-apply -/
  | r_d_app_basic_apply (b : BasVal) (vs : List Val) (v v' : Val) :
      vs.length + 1 = b.arity → Apply b (vs ++ [v]) v' → AppVal (.basApp b vs) v v'

/-- Matches: E, v ⊢ match ⇒ v'/FAIL -/
inductive EvalMatch : Env → Val → Match → VF → Prop where
  /-- r:d-match-first: mrule [; match] -/
  | r_d_match_first (E : Env) (v : Val) (mr : MRule) (rest : Option Match) (v' : Val) :
      EvalMRule E v mr (.ok v') → EvalMatch E v (.mk mr rest) (.ok v')
  /-- r:d-match-fail -/
  | r_d_match_fail (E : Env) (v : Val) (mr : MRule) :
      EvalMRule E v mr .fail → EvalMatch E v (.mk mr none) .fail
  /-- r:d-match-next -/
  | r_d_match_next (E : Env) (v : Val) (mr : MRule) (m : Match) (r : VF) :
      EvalMRule E v mr .fail → EvalMatch E v m r → EvalMatch E v (.mk mr (some m)) r

/-- Match Rules: E, v ⊢ mrule ⇒ v'/FAIL -/
inductive EvalMRule : Env → Val → MRule → VF → Prop where
  /-- r:d-mrule-match -/
  | r_d_mrule_match (E : Env) (v : Val) (p : Pat) (e : Exp) (VE : ValEnv) (v' : Val) :
      MatchPat E v p (.ok VE) → EvalExp (E.plusVE VE) e v' → EvalMRule E v (.mk p e) (.ok v')
  /-- r:d-mrule-fail -/
  | r_d_mrule_fail (E : Env) (v : Val) (p : Pat) (e : Exp) :
      MatchPat E v p .fail → EvalMRule E v (.mk p e) .fail

/-- Declarations: E ⊢ dec ⇒ VE -/
inductive EvalDec : Env → Dec → ValEnv → Prop where
  /-- r:d-dec-nonrec: Dom VE ∩ FV(valbind) = ∅ -/
  | r_d_dec_nonrec (E : Env) (vb : ValBind) (VE : ValEnv) :
      EvalValBind E vb VE → isRecursive VE vb = false → EvalDec E (.val vb) VE
  /-- r:d-dec-rec: Dom VE ∩ FV(valbind) ≠ ∅ -/
  | r_d_dec_rec (E : Env) (vb : ValBind) (VE : ValEnv) :
      EvalValBind E vb VE → isRecursive VE vb = true → EvalDec E (.val vb) (recVE VE)

/-- Value Bindings: E ⊢ valbind ⇒ VE -/
inductive EvalValBind : Env → ValBind → ValEnv → Prop where
  /-- r:d-valbind-var: var = exp [and valbind] ⇒ {var ↦ v} [+ VE] -/
  | r_d_valbind_var (E : Env) (x : Var) (e : Exp) (rest : Option ValBind) (v : Val) (VE : ValEnv) :
      EvalExp E e v → EvalValBindOpt E rest VE →
      EvalValBind E (.var x e rest) (fmPlus [(x, v)] VE)
  /-- r:d-valbind-pat -/
  | r_d_valbind_pat (E : Env) (p : AtPat) (e : Exp) (v : Val) (VE : ValEnv) :
      EvalExp E e v → MatchAtPat E v p (.ok VE) → EvalValBind E (.pat p e) VE

/-- Atomic Patterns: E, v ⊢ atpat ⇒ VE/FAIL -/
inductive MatchAtPat : Env → Val → AtPat → VEF → Prop where
  /-- r:d-atpat-wild -/
  | r_d_atpat_wild (E : Env) (v : Val) : MatchAtPat E v .wild (.ok [])
  /-- r:d-atpat-scon -/
  | r_d_atpat_scon (E : Env) (v : Val) (sc : SCon) :
      v = valof sc → MatchAtPat E v (.scon sc) (.ok [])
  /-- r:d-atpat-scon-fail -/
  | r_d_atpat_scon_fail (E : Env) (v : Val) (sc : SCon) :
      v ≠ valof sc → MatchAtPat E v (.scon sc) .fail
  /-- r:d-atpat-var -/
  | r_d_atpat_var (E : Env) (v : Val) (x : Var) : MatchAtPat E v (.var x) (.ok [(x, v)])
  /-- r:d-atpat-con -/
  | r_d_atpat_con (E : Env) (v : Val) (lc : LongId) (c : Con) :
      E.lookup lc = some (.con c []) → v = .con c [] → MatchAtPat E v (.con lc) (.ok [])
  /-- r:d-atpat-con-fail -/
  | r_d_atpat_con_fail (E : Env) (v : Val) (lc : LongId) (c : Con) :
      E.lookup lc = some (.con c []) → v ≠ .con c [] → MatchAtPat E v (.con lc) .fail
  /-- r:d-atpat-unit -/
  | r_d_atpat_unit (E : Env) : MatchAtPat E .unit .unit (.ok [])
  /-- r:d-atpat-tuple -/
  | r_d_atpat_tuple (E : Env) (v v1 v2 : Val) (v3 : Option Val) (p1 p2 : Pat) (p3 : Option Pat)
      (r1 r2 r3 : VEF) :
      v = .tuple v1 v2 v3 → MatchPat E v1 p1 r1 → MatchPat E v2 p2 r2 → MatchPatOpt E v3 p3 r3 →
      MatchAtPat E v (.tuple p1 p2 p3) ((r1.plus r2).plus r3)
  /-- r:d-atpat-nil -/
  | r_d_atpat_nil (E : Env) (v : Val) : v = Val.nil → MatchAtPat E v .nil (.ok [])
  /-- r:d-atpat-nil-fail -/
  | r_d_atpat_nil_fail (E : Env) (v : Val) : v ≠ Val.nil → MatchAtPat E v .nil .fail
  /-- r:d-atpat-record: { [patrow] } ⇒ ∅ [+ VE] -/
  | r_d_atpat_record (E : Env) (v : Val) (r : Record) (row : Option PatRow) (VE : ValEnv) :
      v = .record r → MatchPatRowOpt E r row VE → MatchAtPat E v (.record row) (.ok (fmPlus [] VE))
  /-- r:d-atpat-paren -/
  | r_d_atpat_paren (E : Env) (v : Val) (p : Pat) (r : VEF) :
      MatchPat E v p r → MatchAtPat E v (.paren p) r

/-- Pattern Rows: E, r ⊢ patrow ⇒ VE/FAIL -/
inductive MatchPatRow : Env → Record → PatRow → ValEnv → Prop where
  /-- r:d-patrow-field: lab [, patrow] ⇒ {lab ↦ r(lab)} [+ VE].
      r(lab) is written as the premise `fmLookup r lab = some v`. -/
  | r_d_patrow_field (E : Env) (r : Record) (l : Lab) (rest : Option PatRow) (v : Val) (VE : ValEnv) :
      fmLookup r l = some v → MatchPatRowOpt E r rest VE →
      MatchPatRow E r (.field l rest) (fmPlus [(l, v)] VE)

/-- Patterns: E, v ⊢ pat ⇒ VE/FAIL -/
inductive MatchPat : Env → Val → Pat → VEF → Prop where
  /-- r:d-pat-atpat -/
  | r_d_pat_atpat (E : Env) (v : Val) (a : AtPat) (r : VEF) :
      MatchAtPat E v a r → MatchPat E v (.atpat a) r
  /-- r:d-pat-con -/
  | r_d_pat_con (E : Env) (v : Val) (lc : LongId) (c : Con) (vs : List Val) (args : List AtPat) (r : VEF) :
      E.lookup lc = some (.con c []) → v = .con c vs → MatchAtPats E vs args r →
      MatchPat E v (.con lc args) r
  /-- r:d-pat-con-fail: v ∉ {con} × Val^n -/
  | r_d_pat_con_fail (E : Env) (v : Val) (lc : LongId) (c : Con) (args : List AtPat) :
      E.lookup lc = some (.con c []) → (¬ ∃ vs, v = .con c vs ∧ vs.length = args.length) →
      MatchPat E v (.con lc args) .fail
  /-- r:d-pat-cons -/
  | r_d_pat_cons (E : Env) (v v1 v2 : Val) (p1 p2 : Pat) (r1 r2 : VEF) :
      v = .cons v1 v2 → MatchPat E v1 p1 r1 → MatchPat E v2 p2 r2 →
      MatchPat E v (.cons p1 p2) (r1.plus r2)
  /-- r:d-pat-cons-fail -/
  | r_d_pat_cons_fail (E : Env) (v : Val) (p1 p2 : Pat) :
      v = Val.nil → MatchPat E v (.cons p1 p2) .fail
  /-- r:d-pat-as -/
  | r_d_pat_as (E : Env) (v : Val) (p : Pat) (x : Var) (r : VEF) :
      MatchPat E v p r → MatchPat E v (.as p x) (r.plus (.ok [(x, v)]))

-- Auxiliary relations: options and sequences (not book rules).

inductive EvalExpOpt : Env → Option Exp → Option Val → Prop where
  | opt_none (E : Env) : EvalExpOpt E none none
  | opt_some (E : Env) (e : Exp) (v : Val) : EvalExp E e v → EvalExpOpt E (some e) (some v)

inductive EvalExpRowOpt : Env → Option ExpRow → Record → Prop where
  | opt_none (E : Env) : EvalExpRowOpt E none []
  | opt_some (E : Env) (row : ExpRow) (r : Record) : EvalExpRow E row r → EvalExpRowOpt E (some row) r

inductive EvalValBindOpt : Env → Option ValBind → ValEnv → Prop where
  | opt_none (E : Env) : EvalValBindOpt E none []
  | opt_some (E : Env) (vb : ValBind) (VE : ValEnv) : EvalValBind E vb VE → EvalValBindOpt E (some vb) VE

inductive MatchPatOpt : Env → Option Val → Option Pat → VEF → Prop where
  | opt_none (E : Env) : MatchPatOpt E none none (.ok [])
  | opt_some (E : Env) (v : Val) (p : Pat) (r : VEF) : MatchPat E v p r → MatchPatOpt E (some v) (some p) r

inductive MatchPatRowOpt : Env → Record → Option PatRow → ValEnv → Prop where
  | opt_none (E : Env) (r : Record) : MatchPatRowOpt E r none []
  | opt_some (E : Env) (r : Record) (row : PatRow) (VE : ValEnv) :
      MatchPatRow E r row VE → MatchPatRowOpt E r (some row) VE

/-- E, v1 ... vn ⊢ atpat1 ... atpatn ⇒ VE1/FAIL + ... + VEn/FAIL -/
inductive MatchAtPats : Env → List Val → List AtPat → VEF → Prop where
  | seq_nil (E : Env) : MatchAtPats E [] [] (.ok [])
  | seq_cons (E : Env) (v : Val) (vs : List Val) (a : AtPat) (as : List AtPat) (r rs : VEF) :
      MatchAtPat E v a r → MatchAtPats E vs as rs → MatchAtPats E (v :: vs) (a :: as) (r.plus rs)

end

end StandardElm
