/-
  A Standard Definition of Elm? Mechanisation: the statements of completeness and principality of
  W for fragment F_b, milestone (b) of plan step 11 (section 7), with the corrected instance
  relation, and the first lemmas of their proof (section 8: L2's instantiation, the state
  invariant (I1) along W).

  *The instance relation.* Step 9's occurrence nodes carry the instance list, which makes
  `PrincipalExistsCore` false (InstCounter.lean). Here an instance is taken with the instance
  lists left out (`stripExp`): the nodes are then the book's sentences, the type of each
  occurrence and of every other node, the U of its context and the schemes of its declarations.
  The derivations compared are those without free `bnd` variables (`NoFreeBndExp`, as step 9's
  `AModule.NoFreeBnd` for modules: `bnd` variables are the bound variables of canonical schemes,
  and a derivation that uses one free has its closure capture it).

  *The statements* (`WRefutation`, `WCompleteness`, `WPrincipality`) are propositions here. The
  main induction L11 is WComplete.lean (with WCompletePat.lean for patterns); `WRefutation` is
  proved in WTheorems.lean (`wRefutation`), with the first half of completeness
  (`inferExpW_ne_fail`) and L12 (`inferExpW_instance`: every derivation is the image of W's result
  by a substitution fixing the root context's variables, instance lists left out); the node-wise
  packaging of principality is WNodeRel*.lean (in progress). The root context must be well formed
  in the sense of `RootOK`, and the derivations considered have no free `bnd` variable.

  *Proved here:* `gen_tyBound` (σ ≻ τ for a scheme whose bound variables are type variables, as a
  substitution of them: the form every later lemma uses), `instantiate_ok` (W's instance is the
  scheme's body with the bound variables replaced by fresh variables, and every instance is a
  substitution instance of it, by a substitution that moves only W's new variables: L2,
  `instance_of_fresh`), and `unifyW_ok`, `unifyW_fail` (a `unify` of W in its state: the state
  stays good, and the solution correspondence of section 4 holds through the accumulated
  substitution). These are the lemmas the application, case and occurrence steps of L11 use.
-/
import StandardElmMech.Stat.Complete.W
import StandardElmMech.Stat.Principal

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## Instances without instance lists -/

mutual
def stripAtPat : AAtPat → AAtPat
  | .con lc _ τ => .con lc [] τ
  | .tuple p1 p2 p3 => .tuple (stripPat p1) (stripPat p2) (stripPatOpt p3)
  | .paren p => .paren (stripPat p)
  | a => a
def stripPat : APat → APat
  | .atpat a => .atpat (stripAtPat a)
  | .con lc _ args τ => .con lc [] (stripAtPats args) τ
  | .cons p1 p2 => .cons (stripPat p1) (stripPat p2)
  | .as p x => .as (stripPat p) x
def stripPatOpt : Option APat → Option APat
  | none => none
  | some p => some (stripPat p)
def stripAtPats : List AAtPat → List AAtPat
  | [] => []
  | a :: as => stripAtPat a :: stripAtPats as
end

mutual
def stripAtExp : AAtExp → AAtExp
  | .var lv _ τ => .var lv [] τ
  | .con lc _ τ => .con lc [] τ
  | .op o _ τ => .op o [] τ
  | .tuple e1 e2 e3 => .tuple (stripExp e1) (stripExp e2) (stripExpOpt e3)
  | .record row => .record (stripExpRowOpt row)
  | .update x _ τ row => .update x [] τ (stripExpRow row)
  | .letE d e => .letE (stripDec d) (stripExp e)
  | .paren e => .paren (stripExp e)
  | a => a
def stripExpRow : AExpRow → AExpRow
  | .field l e rest => .field l (stripExp e) (stripExpRowOpt rest)
def stripExpRowOpt : Option AExpRow → Option AExpRow
  | none => none
  | some r => some (stripExpRow r)
def stripExp : AExp → AExp
  | .atexp a => .atexp (stripAtExp a)
  | .app e a => .app (stripExp e) (stripAtExp a)
  | .lam p e => .lam (stripAtPat p) (stripExp e)
  | .caseE e m => .caseE (stripExp e) (stripMatch m)
def stripExpOpt : Option AExp → Option AExp
  | none => none
  | some e => some (stripExp e)
def stripMatch : AMatch → AMatch
  | .mk mr rest => .mk (stripMRule mr) (stripMatchOpt rest)
def stripMatchOpt : Option AMatch → Option AMatch
  | none => none
  | some m => some (stripMatch m)
def stripMRule : AMRule → AMRule
  | .mk p e => .mk (stripPat p) (stripExp e)
def stripDec : ADec → ADec
  | .val VE vb => .val VE (stripValBind vb)
def stripValBind : AValBind → AValBind
  | .var x ann τ e rest => .var x ann τ (stripExp e) (stripValBindOpt rest)
  | .pat p e => .pat (stripAtPat p) (stripExp e)
def stripValBindOpt : Option AValBind → Option AValBind
  | none => none
  | some vb => some (stripValBind vb)
end

/-- No node of the derivation has a free `bnd` variable in its types. -/
def NoFreeBndExp (C : Ctx) (a : AExp) : Prop :=
  ∀ n ∈ nodesExp C [] a, ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, v.isBnd = false

/-- `a'` is an instance of `a` (sec:static-core-principal), the instance lists left out. -/
def InstanceOfB (C0 : Ctx) (a' a : AExp) : Prop := InstanceOf C0 (stripExp a') (stripExp a)

def IsPrincipalB (C0 : Ctx) (a : AExp) : Prop :=
  checkExp C0 a = true ∧ ∀ a', checkExp C0 a' = true → NoFreeBndExp C0 a' → a'.erase = a.erase →
    InstanceOfB C0 a' a

/-- The root context is well formed for F_b: the bound variables of a scheme it binds are `bnd`
    (its canonical form) and the free ones are type variables, not `bnd` (no row variable is free in
    F_b). -/
def RootOK (C0 : Ctx) : Prop :=
  ∀ lv σ st, C0.lookupVal lv = some (σ, st) →
    (∀ v ∈ σ.bound, v.isBnd = true) ∧
    ∀ v ∈ σ.body.vars, v ∉ σ.bound → ∃ a, v = .ty a ∧ BVar.isBnd (.ty a) = false

/-! ## The statements (section 7, for F_b) -/

/-- Refutation: if W fails, no derivation without free `bnd` variables exists (with step 9's
    adequacy, `¬ ∃ τ, ElExp C0 e τ` for such derivations). The restriction is needed: a free
    `bnd` variable is captured by a later closure, and such a derivation can type a phrase that
    has no other derivation (`\y -> let f = \z -> y in (case f 'c' of 'x' -> 1, case f "s" of
    "x" -> 2)` with `y : bnd 0`: `f` closes to `∀ bnd 0. bnd 0 -> bnd 0`). -/
def WRefutation : Prop :=
  ∀ fuel C0 e, RootOK C0 → inferExpW fuel C0 e = .fail →
    ¬ ∃ a', checkExp C0 a' = true ∧ NoFreeBndExp C0 a' ∧ a'.erase = e

/-- Completeness: if a derivation exists, W neither fails nor returns `internal`, and for some
    fuel it does not run out (so it returns `ok`, or `unsupported` outside F_b). -/
def WCompleteness : Prop :=
  ∀ C0 e, RootOK C0 → (∃ a', checkExp C0 a' = true ∧ NoFreeBndExp C0 a' ∧ a'.erase = e) →
    (∀ fuel, inferExpW fuel C0 e ≠ .fail ∧ inferExpW fuel C0 e ≠ .internal) ∧
    ∃ fuel, inferExpW fuel C0 e ≠ .outOfFuel

/-- Principality: what W returns is principal (with the corrected instance relation). -/
def WPrincipality : Prop :=
  ∀ fuel C0 e a, RootOK C0 → inferExpW fuel C0 e = .ok a → IsPrincipalB C0 a

/-! ## Instances of schemes over type variables -/

theorem bindSubst_tys : ∀ {vs : List TyVar} {ts : List Ty} {S : Subst}, bindSubst (vs.map BVar.ty) ts = some S →
    S = ofBnd (vs.zip ts) ∧ vs.length = ts.length
  | [], [], S, h => by simp [bindSubst] at h; subst h; exact ⟨rfl, rfl⟩
  | a :: vs, t :: ts, S, h => by
    simp only [List.map_cons, bindSubst] at h
    cases hb : bindSubst (vs.map BVar.ty) ts with
    | none => rw [hb] at h; cases h
    | some S' =>
      rw [hb] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := bindSubst_tys hb
      subst h1
      simp [ofBnd, h2]
  | [], _ :: _, _, h => by simp [bindSubst] at h
  | _ :: _, [], _, h => by simp [bindSubst] at h

theorem bindSubst_of_length : ∀ {vs : List TyVar} {ts : List Ty}, vs.length = ts.length →
    bindSubst (vs.map BVar.ty) ts = some (ofBnd (vs.zip ts))
  | [], [], _ => rfl
  | a :: vs, t :: ts, h => by
    simp only [List.map_cons, bindSubst, bindSubst_of_length (by simpa using h : vs.length = ts.length)]
    rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- σ ≻ τ for a scheme whose bound variables are type variables: τ is the body under a binding of
    the bound variables to types of their classes. -/
theorem gen_tyBound {vs : List TyVar} {body τ : Ty} :
    Gen ⟨vs.map BVar.ty, body⟩ τ ↔
      ∃ ts : List Ty, vs.length = ts.length ∧ (∀ p ∈ vs.zip ts, Adm p.1.cls p.2) ∧ τ = sb (lk (vs.zip ts)) body := by
  constructor
  · rintro ⟨ts, S, hS, hr, ha⟩
    obtain ⟨rfl, hl⟩ := bindSubst_tys hS
    rw [apply_ofBnd, Option.some.injEq] at ha
    exact ⟨ts, hl, hr, ha.symm⟩
  · rintro ⟨ts, hl, hr, rfl⟩
    exact ⟨ts, ofBnd (vs.zip ts), bindSubst_of_length hl, hr, apply_ofBnd _ _⟩

/-! ## W's instantiation (L2) -/

/-- `n`, `n + 1`, ...: the fresh variables W gives `k` bound variables. -/
def freshFrom (n : Nat) : Nat → List Ty
  | 0 => []
  | k + 1 => .var (.fresh n .any) :: freshFrom (n + 1) k

theorem instVars_ok : ∀ (vs : List BVar) (st : WSt) (ts : List Ty) (st' : WSt),
    instVars vs st = .ok ts st' →
    (∃ as : List TyVar, vs = as.map BVar.ty ∧ ∀ a ∈ as, a.cls = .any) ∧
    ts = freshFrom st.n vs.length ∧ st'.θ = st.θ ∧ st'.n = st.n + vs.length
  | [], st, ts, st', h => by
    simp only [instVars, pure] at h; cases h
    exact ⟨⟨[], rfl, fun _ h => by cases h⟩, rfl, rfl, rfl⟩
  | .ty a :: rest, st, ts, st', h => by
    simp only [instVars] at h
    split at h
    · rename_i hc
      simp only [bind, WM.bind, freshV] at h
      cases hr : instVars rest { st with n := st.n + 1 } with
      | ok ts' st'' =>
        rw [hr] at h
        simp only [pure, WOut.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨⟨as, has, hcl⟩, hts, hθ, hn⟩ := instVars_ok rest _ ts' st'' hr
        refine ⟨⟨a :: as, by simp [has], ?_⟩, ?_, hθ, ?_⟩
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hc
          · exact hcl b hb
        · simp only [List.length_cons, freshFrom, hts]
        · simp only [hn, List.length_cons]; omega
      | fail => rw [hr] at h; cases h
      | unsupported => rw [hr] at h; cases h
      | outOfFuel => rw [hr] at h; cases h
    · cases h
  | .row _ :: _, _, _, _, h => by simp [instVars, wUnsupported] at h

theorem freshFrom_length : ∀ (n k : Nat), (freshFrom n k).length = k
  | _, 0 => rfl
  | n, k + 1 => by simp [freshFrom, freshFrom_length (n + 1) k]

/-- What W's instantiation returns: fresh variables for the bound ones, the body under them, the
    substitution unchanged, the counter past them. -/
theorem instantiate_ok {σ : Scheme} {st st' : WSt} {ts : List Ty} {τ : Ty}
    (h : instantiate σ st = .ok (ts, τ) st') :
    ∃ as : List TyVar, σ.bound = as.map BVar.ty ∧ (∀ a ∈ as, a.cls = .any) ∧
      ts = freshFrom st.n as.length ∧ τ = sb (lk (as.zip ts)) σ.body ∧ st'.θ = st.θ ∧
      st'.n = st.n + as.length := by
  unfold instantiate at h
  simp only [bind, WM.bind] at h
  cases hv : instVars σ.bound st with
  | ok ts0 st0 =>
    rw [hv] at h
    dsimp only at h
    obtain ⟨⟨as, has, hcl⟩, hts, hθ, hn⟩ := instVars_ok _ _ _ _ hv
    rw [has] at h
    have hl : as.length = ts0.length := by rw [hts, freshFrom_length, has, List.length_map]
    rw [bindSubst_of_length hl] at h
    dsimp only at h
    rw [apply_ofBnd] at h
    dsimp only at h
    simp only [pure, WOut.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨as, has, hcl, by rw [hts, has]; simp, rfl, hθ, by rw [hn, has]; simp⟩
  | fail => rw [hv] at h; cases h
  | unsupported => rw [hv] at h; cases h
  | outOfFuel => rw [hv] at h; cases h

/-- L2, most general instance: every instance of a scheme over type variables is a substitution
    instance of W's, by a substitution that is the identity outside W's fresh variables. -/
theorem instance_of_fresh {as : List TyVar} {body : Ty} {n : Nat} {ts' : List Ty}
    (hnd : as.Nodup) (hl : as.length = ts'.length)
    (hfree : ∀ a, BVar.ty a ∈ body.vars → a ∉ as → ∀ k c, a = .fresh k c → k < n) :
    ∃ g : FSub, (∀ a, (∀ k c, a = .fresh k c → k < n ∨ n + as.length ≤ k) → g a = .var a) ∧
      sb (lk (as.zip ts')) body = sb g (sb (lk (as.zip (freshFrom n as.length))) body) := by
  -- g maps the i-th fresh variable to the i-th type of ts'
  let g : FSub := fun a => match a with
    | .fresh k _ => if n ≤ k ∧ k < n + as.length then (ts'.getD (k - n) (.var a)) else .var a
    | a => .var a
  refine ⟨g, ?_, ?_⟩
  · intro a ha
    match a, ha with
    | .fresh k c, ha =>
      simp only [g]
      rcases ha k c rfl with h | h
      · rw [if_neg (by omega)]
      · rw [if_neg (by omega)]
    | .named _, _ => rfl
    | .bnd _ _, _ => rfl
  · rw [sb_sb]
    apply sb_congr
    intro a ha
    simp only [comp]
    by_cases hm : a ∈ as
    · -- the i-th bound variable
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
      have e1 : lk (as.zip ts') as[i] = ts'[i]'(by rw [← hl]; exact hi) := lk_zip_nodup hnd hl i hi
      have e2 : lk (as.zip (freshFrom n as.length)) as[i] = .var (.fresh (n + i) .any) := by
        rw [lk_zip_nodup hnd (freshFrom_length n as.length).symm i hi]
        exact freshFrom_get n as.length i (by rw [freshFrom_length]; exact hi)
      rw [e1, e2]
      simp only [sb, g]
      rw [if_pos (by omega)]
      simp only [Nat.add_sub_cancel_left]
      have hi2 : i < ts'.length := by rw [← hl]; exact hi
      simp [List.getD_eq_getElem?_getD, hi2]
    · rw [lk_zip_not_mem hm, lk_zip_not_mem hm]
      simp only [sb]
      match a, hfree a ha hm with
      | .fresh k c, hk => simp only [g]; rw [if_neg (by have := hk k c rfl; omega)]
      | .named _, _ => rfl
      | .bnd _ _, _ => rfl
where
  lk_zip_not_mem {as : List TyVar} {ts : List Ty} {a : TyVar} (hm : a ∉ as) : lk (as.zip ts) a = .var a := by
    induction as generalizing ts with
    | nil => rfl
    | cons b bs ih =>
      cases ts with
      | nil => rfl
      | cons t ts =>
        simp only [List.zip_cons_cons, lk_cons]
        rw [if_neg (by intro e; subst e; simp at hm)]
        exact ih (fun h => hm (List.mem_cons_of_mem _ h))
  lk_zip_nodup {as : List TyVar} {ts : List Ty} (hnd : as.Nodup) (hl : as.length = ts.length) :
      ∀ (i : Nat) (hi : i < as.length), lk (as.zip ts) as[i] = ts[i]'(by rw [← hl]; exact hi) := by
    induction as generalizing ts with
    | nil => intro i hi; cases hi
    | cons b bs ih =>
      cases ts with
      | nil => simp at hl
      | cons t ts =>
        intro i hi
        simp only [List.zip_cons_cons, lk_cons]
        cases i with
        | zero => simp
        | succ i =>
          have hnd' := List.nodup_cons.mp hnd
          have hi' : i < bs.length := by simpa using hi
          have hne : b ≠ bs[i]'hi' := fun e => hnd'.1 (e ▸ List.getElem_mem _)
          simp only [List.getElem_cons_succ]
          rw [if_neg hne]
          exact ih hnd'.2 (by simpa using hl) i (by simpa using hi)
  freshFrom_get : ∀ (n k i : Nat) (hi : i < (freshFrom n k).length),
      (freshFrom n k)[i] = .var (.fresh (n + i) .any)
    | _, 0, _, hi => by simp [freshFrom] at hi
    | n, k + 1, 0, _ => by simp [freshFrom]
    | n, k + 1, i + 1, hi => by
      simp only [freshFrom, List.getElem_cons_succ]
      rw [freshFrom_get (n + 1) k i (by simpa [freshFrom] using hi)]
      congr 2; omega

/-! ## W's unification step in the state (L9 inside W) -/

/-- An equation of types substituted by an idempotent `θ` is stable under `θ`. -/
theorem good_sb {R : Rigid} {θ : Bnd} (g : Good R θ []) (τ1 τ2 : Ty) :
    Good R θ [(sb (lk θ) τ1, sb (lk θ) τ2)] := by
  refine ⟨g.keys, g.idem, ?_⟩
  intro e he c hc
  simp only [List.mem_singleton] at he; subst he
  rcases hc with hc | hc
  · obtain ⟨d, _, hd⟩ := tyvar_sb hc; exact g.idem d c hd
  · obtain ⟨d, _, hd⟩ := tyvar_sb hc; exact g.idem d c hd

/-- A unifier that absorbs `θ` unifies the substituted equation iff it unifies the original. -/
theorem absorbs_sb {s : FSub} {θ : Bnd} (h : Absorbs s (lk θ)) (τ : Ty) : sb s (sb (lk θ) τ) = sb s τ := by
  rw [sb_sb]; congr 1; funext a; exact h a

/-- `unify` in W's state: the new substitution is good, the counter unchanged, and a substitution
    absorbs it exactly when it absorbs the old one and unifies the two types (section 6). -/
theorem unifyW_ok {fuel : Nat} {R : Rigid} {τ1 τ2 : Ty} {st st' : WSt} {u : Unit}
    (g : Good R st.θ []) (h : unifyW fuel R τ1 τ2 st = .ok u st') :
    Good R st'.θ [] ∧ st'.n = st.n ∧
      ∀ s, FixesR R s → (sb s τ1 = sb s τ2 ∧ Absorbs s (lk st.θ) ↔ Absorbs s (lk st'.θ)) := by
  unfold unifyW at h
  split at h
  · rename_i θ' hu
    simp only [WOut.ok.injEq] at h; obtain ⟨_, rfl⟩ := h
    obtain ⟨g', c⟩ := uLoop_ok fuel _ _ _ (good_sb g τ1 τ2) hu
    refine ⟨g', rfl, fun s hs => ?_⟩
    rw [← (c s hs).trans ⟨fun h => h.2, fun h => ⟨unifies_nil s, h⟩⟩]
    constructor
    · rintro ⟨he, ha⟩
      refine ⟨?_, ha⟩
      rw [unifies_cons]; exact ⟨by rw [absorbs_sb ha, absorbs_sb ha]; exact he, unifies_nil s⟩
    · rintro ⟨hu, ha⟩
      have := (unifies_cons.mp hu).1
      rw [absorbs_sb ha, absorbs_sb ha] at this
      exact ⟨this, ha⟩
  · cases h
  · cases h
  · cases h

/-- A failing `unify` in W's state: no substitution fixing the rigid variables and absorbing the
    current one unifies the two types (K1 to K3, K7 through the state). -/
theorem unifyW_fail {fuel : Nat} {R : Rigid} {τ1 τ2 : Ty} {st : WSt}
    (g : Good R st.θ []) (h : unifyW fuel R τ1 τ2 st = .fail) :
    ∀ s, FixesR R s → Absorbs s (lk st.θ) → sb s τ1 ≠ sb s τ2 := by
  unfold unifyW at h
  split at h
  · cases h
  · rename_i hu
    intro s hs ha he
    apply uLoop_fail fuel _ _ (good_sb g τ1 τ2) hu s hs
    refine ⟨?_, ha⟩
    rw [unifies_cons]; exact ⟨by rw [absorbs_sb ha, absorbs_sb ha]; exact he, unifies_nil s⟩
  · cases h
  · cases h

end StandardElm.Stat.Complete
