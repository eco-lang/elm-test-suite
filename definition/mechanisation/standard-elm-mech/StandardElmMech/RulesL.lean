/-
  A Standard Definition of Elm? Mechanisation: the logged relations (plan decision D4).

  `Debug.log` output is outside the definition (A62), and a derivation of a `Prop` relation cannot
  be inspected, so "the log of a derivation" is not a term. Beside each relation of Rules.lean there
  is here a relation with the same rules and one more index, the log: the entries `(s, v)` of the
  applications of Debug.log. Each constructor is the book's rule, named with `_l` appended, its
  conclusion's log the concatenation of its relation premises' logs in the order in which the rule
  writes its premises; `r_d_app_basic_apply_l` adds `logEntry b (vs ++ [v])`. Side conditions
  (lookups, equations, `isRecursive`, `Apply`) carry no log.

  That order is one of the orders of evaluation the book allows: the order in which the parts of a
  phrase are evaluated carries no meaning (A57, A58; appendix-implementation.tex,
  sec:appendix-implementation-order). It is not Elm/JS's for record fields, which Elm/JS evaluates
  by field name. So a statement about the order of log entries says that the book allows that
  order, not that it requires it.

  `forget` (a logged derivation gives a derivation of the book) and `lift` (every derivation of the
  book has a logged one) tie the two together; the log is defined by the logged relation, and the
  book's link to it is the value.
-/
import StandardElmMech.Rules

namespace StandardElm

mutual

inductive EvalAtExpL : Env → AtExp → Val → Log → Prop where
  /-- r:d-atexp-scon -/
  | r_d_atexp_scon_l (E : Env) (sc : SCon) : EvalAtExpL E (.scon sc) (valof sc) []
  /-- r:d-atexp-var -/
  | r_d_atexp_var_l (E : Env) (lv : LongId) (v : Val) :
      E.lookup lv = some v → EvalAtExpL E (.var lv) v []
  /-- r:d-atexp-con -/
  | r_d_atexp_con_l (E : Env) (lc : LongId) (v : Val) :
      E.lookup lc = some v → EvalAtExpL E (.con lc) v []
  /-- r:d-atexp-op -/
  | r_d_atexp_op_l (E : Env) (o : Op) (v : Val) :
      OTdyn o = some v → EvalAtExpL E (.op o) v []
  /-- r:d-atexp-unit -/
  | r_d_atexp_unit_l (E : Env) : EvalAtExpL E .unit .unit []
  /-- r:d-atexp-tuple -/
  | r_d_atexp_tuple_l (E : Env) (e1 e2 : Exp) (e3 : Option Exp) (v1 v2 : Val) (v3 : Option Val)
      (l1 l2 l3 : Log) :
      EvalExpL E e1 v1 l1 → EvalExpL E e2 v2 l2 → EvalExpOptL E e3 v3 l3 →
      EvalAtExpL E (.tuple e1 e2 e3) (.tuple v1 v2 v3) (l1 ++ l2 ++ l3)
  /-- r:d-atexp-nil -/
  | r_d_atexp_nil_l (E : Env) : EvalAtExpL E .nil Val.nil []
  /-- r:d-atexp-record -/
  | r_d_atexp_record_l (E : Env) (row : Option ExpRow) (r : Record) (l1 : Log) :
      EvalExpRowOptL E row r l1 → EvalAtExpL E (.record row) (.record (fmPlus [] r)) l1
  /-- r:d-atexp-update -/
  | r_d_atexp_update_l (E : Env) (x : Var) (row : ExpRow) (r r' : Record) (l1 : Log) :
      E.lookup ⟨none, x⟩ = some (.record r) → EvalExpRowL E row r' l1 →
      EvalAtExpL E (.update x row) (.record (fmPlus r r')) l1
  /-- r:d-atexp-paren -/
  | r_d_atexp_paren_l (E : Env) (e : Exp) (v : Val) (l1 : Log) :
      EvalExpL E e v l1 → EvalAtExpL E (.paren e) v l1
  /-- r:d-atexp-let -/
  | r_d_atexp_let_l (E : Env) (d : Dec) (e : Exp) (VE : ValEnv) (v : Val) (l1 l2 : Log) :
      EvalDecL E d VE l1 → EvalExpL (E.plusVE VE) e v l2 → EvalAtExpL E (.letE d e) v (l1 ++ l2)

inductive EvalExpRowL : Env → ExpRow → Record → Log → Prop where
  /-- r:d-exprow-field -/
  | r_d_exprow_field_l (E : Env) (l : Lab) (e : Exp) (rest : Option ExpRow) (v : Val) (r : Record)
      (l1 l2 : Log) :
      EvalExpL E e v l1 → EvalExpRowOptL E rest r l2 →
      EvalExpRowL E (.field l e rest) (fmPlus [(l, v)] r) (l1 ++ l2)

inductive EvalExpL : Env → Exp → Val → Log → Prop where
  /-- r:d-exp-atexp -/
  | r_d_exp_atexp_l (E : Env) (a : AtExp) (v : Val) (l1 : Log) :
      EvalAtExpL E a v l1 → EvalExpL E (.atexp a) v l1
  /-- r:d-exp-app -/
  | r_d_exp_app_l (E : Env) (e : Exp) (a : AtExp) (v1 v2 v : Val) (l1 l2 l3 : Log) :
      EvalExpL E e v1 l1 → EvalAtExpL E a v2 l2 → AppValL v1 v2 v l3 →
      EvalExpL E (.app e a) v (l1 ++ l2 ++ l3)
  /-- r:d-exp-lambda -/
  | r_d_exp_lambda_l (E : Env) (p : AtPat) (e : Exp) :
      EvalExpL E (.lam p e) (.closure p e E []) []
  /-- r:d-exp-case -/
  | r_d_exp_case_l (E : Env) (e : Exp) (m : Match) (v v' : Val) (l1 l2 : Log) :
      EvalExpL E e v l1 → EvalMatchL E v m (.ok v') l2 → EvalExpL E (.caseE e m) v' (l1 ++ l2)

inductive AppValL : Val → Val → Val → Log → Prop where
  /-- r:d-app-closure -/
  | r_d_app_closure_l (p : AtPat) (e : Exp) (E : Env) (VE VE' : ValEnv) (v v' : Val) (l1 l2 : Log) :
      MatchAtPatL (E.plusVE (recVE VE)) v p (.ok VE') l1 →
      EvalExpL ((E.plusVE (recVE VE)).plusVE VE') e v' l2 →
      AppValL (.closure p e E VE) v v' (l1 ++ l2)
  /-- r:d-app-con -/
  | r_d_app_con_l (c : Con) (vs : List Val) (v : Val) :
      AppValL (.con c vs) v (.con c (vs ++ [v])) []
  /-- r:d-app-basic-partial -/
  | r_d_app_basic_partial_l (b : BasVal) (vs : List Val) (v : Val) :
      vs.length + 1 < b.arity → AppValL (.basApp b vs) v (.basApp b (vs ++ [v])) []
  /-- r:d-app-basic-apply: the one rule that logs, at Debug.log -/
  | r_d_app_basic_apply_l (b : BasVal) (vs : List Val) (v v' : Val) :
      vs.length + 1 = b.arity → Apply b (vs ++ [v]) v' →
      AppValL (.basApp b vs) v v' (logEntry b (vs ++ [v]))

inductive EvalMatchL : Env → Val → Match → VF → Log → Prop where
  /-- r:d-match-first -/
  | r_d_match_first_l (E : Env) (v : Val) (mr : MRule) (rest : Option Match) (v' : Val) (l1 : Log) :
      EvalMRuleL E v mr (.ok v') l1 → EvalMatchL E v (.mk mr rest) (.ok v') l1
  /-- r:d-match-fail -/
  | r_d_match_fail_l (E : Env) (v : Val) (mr : MRule) (l1 : Log) :
      EvalMRuleL E v mr .fail l1 → EvalMatchL E v (.mk mr none) .fail l1
  /-- r:d-match-next -/
  | r_d_match_next_l (E : Env) (v : Val) (mr : MRule) (m : Match) (r : VF) (l1 l2 : Log) :
      EvalMRuleL E v mr .fail l1 → EvalMatchL E v m r l2 → EvalMatchL E v (.mk mr (some m)) r (l1 ++ l2)

inductive EvalMRuleL : Env → Val → MRule → VF → Log → Prop where
  /-- r:d-mrule-match -/
  | r_d_mrule_match_l (E : Env) (v : Val) (p : Pat) (e : Exp) (VE : ValEnv) (v' : Val) (l1 l2 : Log) :
      MatchPatL E v p (.ok VE) l1 → EvalExpL (E.plusVE VE) e v' l2 →
      EvalMRuleL E v (.mk p e) (.ok v') (l1 ++ l2)
  /-- r:d-mrule-fail -/
  | r_d_mrule_fail_l (E : Env) (v : Val) (p : Pat) (e : Exp) (l1 : Log) :
      MatchPatL E v p .fail l1 → EvalMRuleL E v (.mk p e) .fail l1

inductive EvalDecL : Env → Dec → ValEnv → Log → Prop where
  /-- r:d-dec-nonrec -/
  | r_d_dec_nonrec_l (E : Env) (vb : ValBind) (VE : ValEnv) (l1 : Log) :
      EvalValBindL E vb VE l1 → isRecursive VE vb = false → EvalDecL E (.val vb) VE l1
  /-- r:d-dec-rec -/
  | r_d_dec_rec_l (E : Env) (vb : ValBind) (VE : ValEnv) (l1 : Log) :
      EvalValBindL E vb VE l1 → isRecursive VE vb = true → EvalDecL E (.val vb) (recVE VE) l1

inductive EvalValBindL : Env → ValBind → ValEnv → Log → Prop where
  /-- r:d-valbind-var -/
  | r_d_valbind_var_l (E : Env) (x : Var) (e : Exp) (rest : Option ValBind) (v : Val) (VE : ValEnv)
      (l1 l2 : Log) :
      EvalExpL E e v l1 → EvalValBindOptL E rest VE l2 →
      EvalValBindL E (.var x e rest) (fmPlus [(x, v)] VE) (l1 ++ l2)
  /-- r:d-valbind-pat -/
  | r_d_valbind_pat_l (E : Env) (p : AtPat) (e : Exp) (v : Val) (VE : ValEnv) (l1 l2 : Log) :
      EvalExpL E e v l1 → MatchAtPatL E v p (.ok VE) l2 → EvalValBindL E (.pat p e) VE (l1 ++ l2)

inductive MatchAtPatL : Env → Val → AtPat → VEF → Log → Prop where
  /-- r:d-atpat-wild -/
  | r_d_atpat_wild_l (E : Env) (v : Val) : MatchAtPatL E v .wild (.ok []) []
  /-- r:d-atpat-scon -/
  | r_d_atpat_scon_l (E : Env) (v : Val) (sc : SCon) :
      v = valof sc → MatchAtPatL E v (.scon sc) (.ok []) []
  /-- r:d-atpat-scon-fail -/
  | r_d_atpat_scon_fail_l (E : Env) (v : Val) (sc : SCon) :
      v ≠ valof sc → MatchAtPatL E v (.scon sc) .fail []
  /-- r:d-atpat-var -/
  | r_d_atpat_var_l (E : Env) (v : Val) (x : Var) : MatchAtPatL E v (.var x) (.ok [(x, v)]) []
  /-- r:d-atpat-con -/
  | r_d_atpat_con_l (E : Env) (v : Val) (lc : LongId) (c : Con) :
      E.lookup lc = some (.con c []) → v = .con c [] → MatchAtPatL E v (.con lc) (.ok []) []
  /-- r:d-atpat-con-fail -/
  | r_d_atpat_con_fail_l (E : Env) (v : Val) (lc : LongId) (c : Con) :
      E.lookup lc = some (.con c []) → v ≠ .con c [] → MatchAtPatL E v (.con lc) .fail []
  /-- r:d-atpat-unit -/
  | r_d_atpat_unit_l (E : Env) : MatchAtPatL E .unit .unit (.ok []) []
  /-- r:d-atpat-tuple -/
  | r_d_atpat_tuple_l (E : Env) (v v1 v2 : Val) (v3 : Option Val) (p1 p2 : Pat) (p3 : Option Pat)
      (r1 r2 r3 : VEF) (l1 l2 l3 : Log) :
      v = .tuple v1 v2 v3 → MatchPatL E v1 p1 r1 l1 → MatchPatL E v2 p2 r2 l2 →
      MatchPatOptL E v3 p3 r3 l3 →
      MatchAtPatL E v (.tuple p1 p2 p3) ((r1.plus r2).plus r3) (l1 ++ l2 ++ l3)
  /-- r:d-atpat-nil -/
  | r_d_atpat_nil_l (E : Env) (v : Val) : v = Val.nil → MatchAtPatL E v .nil (.ok []) []
  /-- r:d-atpat-nil-fail -/
  | r_d_atpat_nil_fail_l (E : Env) (v : Val) : v ≠ Val.nil → MatchAtPatL E v .nil .fail []
  /-- r:d-atpat-record -/
  | r_d_atpat_record_l (E : Env) (v : Val) (r : Record) (row : Option PatRow) (VE : ValEnv) (l1 : Log) :
      v = .record r → MatchPatRowOptL E r row VE l1 → MatchAtPatL E v (.record row) (.ok (fmPlus [] VE)) l1
  /-- r:d-atpat-paren -/
  | r_d_atpat_paren_l (E : Env) (v : Val) (p : Pat) (r : VEF) (l1 : Log) :
      MatchPatL E v p r l1 → MatchAtPatL E v (.paren p) r l1

inductive MatchPatRowL : Env → Record → PatRow → ValEnv → Log → Prop where
  /-- r:d-patrow-field -/
  | r_d_patrow_field_l (E : Env) (r : Record) (l : Lab) (rest : Option PatRow) (v : Val) (VE : ValEnv)
      (l1 : Log) :
      fmLookup r l = some v → MatchPatRowOptL E r rest VE l1 →
      MatchPatRowL E r (.field l rest) (fmPlus [(l, v)] VE) l1

inductive MatchPatL : Env → Val → Pat → VEF → Log → Prop where
  /-- r:d-pat-atpat -/
  | r_d_pat_atpat_l (E : Env) (v : Val) (a : AtPat) (r : VEF) (l1 : Log) :
      MatchAtPatL E v a r l1 → MatchPatL E v (.atpat a) r l1
  /-- r:d-pat-con -/
  | r_d_pat_con_l (E : Env) (v : Val) (lc : LongId) (c : Con) (vs : List Val) (args : List AtPat)
      (r : VEF) (l1 : Log) :
      E.lookup lc = some (.con c []) → v = .con c vs → MatchAtPatsL E vs args r l1 →
      MatchPatL E v (.con lc args) r l1
  /-- r:d-pat-con-fail -/
  | r_d_pat_con_fail_l (E : Env) (v : Val) (lc : LongId) (c : Con) (args : List AtPat) :
      E.lookup lc = some (.con c []) → (¬ ∃ vs, v = .con c vs ∧ vs.length = args.length) →
      MatchPatL E v (.con lc args) .fail []
  /-- r:d-pat-cons -/
  | r_d_pat_cons_l (E : Env) (v v1 v2 : Val) (p1 p2 : Pat) (r1 r2 : VEF) (l1 l2 : Log) :
      v = .cons v1 v2 → MatchPatL E v1 p1 r1 l1 → MatchPatL E v2 p2 r2 l2 →
      MatchPatL E v (.cons p1 p2) (r1.plus r2) (l1 ++ l2)
  /-- r:d-pat-cons-fail -/
  | r_d_pat_cons_fail_l (E : Env) (v : Val) (p1 p2 : Pat) :
      v = Val.nil → MatchPatL E v (.cons p1 p2) .fail []
  /-- r:d-pat-as -/
  | r_d_pat_as_l (E : Env) (v : Val) (p : Pat) (x : Var) (r : VEF) (l1 : Log) :
      MatchPatL E v p r l1 → MatchPatL E v (.as p x) (r.plus (.ok [(x, v)])) l1

inductive EvalExpOptL : Env → Option Exp → Option Val → Log → Prop where
  | opt_none_l (E : Env) : EvalExpOptL E none none []
  | opt_some_l (E : Env) (e : Exp) (v : Val) (l1 : Log) :
      EvalExpL E e v l1 → EvalExpOptL E (some e) (some v) l1

inductive EvalExpRowOptL : Env → Option ExpRow → Record → Log → Prop where
  | opt_none_l (E : Env) : EvalExpRowOptL E none [] []
  | opt_some_l (E : Env) (row : ExpRow) (r : Record) (l1 : Log) :
      EvalExpRowL E row r l1 → EvalExpRowOptL E (some row) r l1

inductive EvalValBindOptL : Env → Option ValBind → ValEnv → Log → Prop where
  | opt_none_l (E : Env) : EvalValBindOptL E none [] []
  | opt_some_l (E : Env) (vb : ValBind) (VE : ValEnv) (l1 : Log) :
      EvalValBindL E vb VE l1 → EvalValBindOptL E (some vb) VE l1

inductive MatchPatOptL : Env → Option Val → Option Pat → VEF → Log → Prop where
  | opt_none_l (E : Env) : MatchPatOptL E none none (.ok []) []
  | opt_some_l (E : Env) (v : Val) (p : Pat) (r : VEF) (l1 : Log) :
      MatchPatL E v p r l1 → MatchPatOptL E (some v) (some p) r l1

inductive MatchPatRowOptL : Env → Record → Option PatRow → ValEnv → Log → Prop where
  | opt_none_l (E : Env) (r : Record) : MatchPatRowOptL E r none [] []
  | opt_some_l (E : Env) (r : Record) (row : PatRow) (VE : ValEnv) (l1 : Log) :
      MatchPatRowL E r row VE l1 → MatchPatRowOptL E r (some row) VE l1

inductive MatchAtPatsL : Env → List Val → List AtPat → VEF → Log → Prop where
  | seq_nil_l (E : Env) : MatchAtPatsL E [] [] (.ok []) []
  | seq_cons_l (E : Env) (v : Val) (vs : List Val) (a : AtPat) (as : List AtPat) (r rs : VEF)
      (l1 l2 : Log) :
      MatchAtPatL E v a r l1 → MatchAtPatsL E vs as rs l2 →
      MatchAtPatsL E (v :: vs) (a :: as) (r.plus rs) (l1 ++ l2)

end

end StandardElm
