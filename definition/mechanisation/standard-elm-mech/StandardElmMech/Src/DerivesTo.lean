/-
  A Standard Definition of Elm? Mechanisation: the derived forms as the book states them, a
  relation, plan step 8 (section 3.3, finding B4). Appendix A fixes every equivalent form but two
  choices: the numbering of a `let`'s groups and of a module's ports and definitions (any that
  meets the book's relation, `ValidNumbering`), and the order of a module's aliases (any in which
  each comes after the aliases it mentions, `ValidAliasOrder`). `DerivesE e b` relates an
  expression to every bare expression the appendix allows; `DerivesTo m b` a module. The function
  `deriveModule` makes the canonical choices, and is one of them (`derive_derivesTo`, under the
  restrictions of the module). Step 9 states and proves that elaboration does not depend on the
  choice; until then theorems are about the canonical choice.
-/
import StandardElmMech.Src.AliasOrderProof

namespace StandardElm.Src
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src.Graph StandardElm.Src.Grouping

/-- The nest of `let`s of a numbering of a `let`'s definitions. -/
def groupLetWith (cs : List (List Nat)) (bs : List BValBind) (body : BExp) : BExp :=
  cs.foldr (fun cmp acc => .atexp (.letE (.val (groupBind bs cmp)) acc)) body

theorem groupLet_eq (ds : List SDef) (bs : List BValBind) (body : BExp) :
    groupLet ds bs body = groupLetWith (Grouping.components ds.length (letRefers ds)) bs body := rfl

mutual
  /-- An expression and the bare expressions Appendix A allows for it. -/
  inductive DerivesE : SExp → BExp → Prop where
    | lit (l : SLit) : DerivesE (.lit l) (.atexp (.scon l))
    | var (x : LongId) : DerivesE (.var x) (.atexp (.var x))
    | con (k : LongId) : DerivesE (.con k) (.atexp (.con k))
    | opVal (o : Op) : DerivesE (.opVal o) (.atexp (.op o))
    | unit : DerivesE .unit (.atexp .unit)
    | tuple2 {a b : SExp} {a' b' : BExp} : DerivesE a a' → DerivesE b b' →
        DerivesE (.tuple [a, b]) (.atexp (.tuple a' b' none))
    | tuple3 {a b c : SExp} {a' b' c' : BExp} : DerivesE a a' → DerivesE b b' → DerivesE c c' →
        DerivesE (.tuple [a, b, c]) (.atexp (.tuple a' b' (some c')))
    | tupleOther (es : List SExp) : es.length ≠ 2 → es.length ≠ 3 → DerivesE (.tuple es) (.atexp .unit)
    | nil : DerivesE (.list []) (.atexp .nil)
    | list {es : List SExp} {bs : List BExp} : es ≠ [] → DerivesEs es bs → DerivesE (.list es) (D.listE bs)
    | record {fs : List (Lab × SExp)} {gs : List (Lab × BExp)} : DerivesFs fs gs →
        DerivesE (.record fs) (.atexp (.record (expRow gs)))
    | update {x : Var} {fs : List (Lab × SExp)} {gs : List (Lab × BExp)} {row : BExpRow} :
        DerivesFs fs gs → expRow gs = some row → DerivesE (.update x fs) (.atexp (.update x row))
    | updateEmpty {x : Var} {fs : List (Lab × SExp)} {gs : List (Lab × BExp)} :
        DerivesFs fs gs → expRow gs = none → DerivesE (.update x fs) (.atexp .unit)
    | accessor (l : Lab) : DerivesE (.accessor l) (.atexp (D.accessor l))
    | access {e : SExp} {b : BExp} (l : Lab) : DerivesE e b → DerivesE (.access e l) (.atexp (D.access (toAt b) l))
    | neg {e : SExp} {b : BExp} : DerivesE e b → DerivesE (.neg e) (.atexp (D.neg (toAt b)))
    | paren {e : SExp} {b : BExp} : DerivesE e b → DerivesE (.paren e) (.atexp (.paren b))
    | app {f : SExp} {args : List SExp} {f' : BExp} {args' : List BExp} : DerivesE f f' → DerivesEs args args' →
        DerivesE (.app f args) (args'.foldl (fun acc a => .app acc (toAt a)) f')
    | andalso {l r : SExp} {l' r' : BExp} : DerivesE l l' → DerivesE r r' →
        DerivesE (.binop "&&" l r) (D.andalso l' r')
    | orelse {l r : SExp} {l' r' : BExp} : DerivesE l l' → DerivesE r r' →
        DerivesE (.binop "||" l r) (D.orelse l' r')
    | binop {o : Op} {l r : SExp} {l' r' : BExp} : o ≠ "&&" → o ≠ "||" → DerivesE l l' → DerivesE r r' →
        DerivesE (.binop o l r) (D.bin o l' r')
    | ifte1 {c t e : SExp} {c' t' e' : BExp} : DerivesE c c' → DerivesE t t' → DerivesE e e' →
        DerivesE (.ifte [(c, t)] e) (D.ifte c' t' e')
    | ifteN {arms : List (SExp × SExp)} {e : SExp} {as : List (BExp × BExp)} {e' : BExp} :
        DerivesAs arms as → as.length ≠ 1 → DerivesE e e' → DerivesE (.ifte arms e) (D.ifChain as e')
    | lam1 {p : SPat} {b : SExp} {b' : BExp} : DerivesE b b' → DerivesE (.lam [p] b) (.lam (deriveAtPat p) b')
    | lamN {ps : List SPat} {b : SExp} {b' : BExp} : ps.length ≠ 1 → DerivesE b b' →
        DerivesE (.lam ps b) (D.lams (ps.map deriveAtPat) b')
    | caseE {e : SExp} {rs : List (SPat × SExp)} {e' : BExp} {rs' : List (BPat × BExp)} :
        DerivesE e e' → DerivesRs rs rs' → DerivesE (.caseE e rs) (.caseE e' (matchOf rs'))
    /-- df:let-grouping, with any numbering the book allows. -/
    | letE {ds : List SDef} {b : SExp} {bs : List BValBind} {b' : BExp} (cs : List (List Nat)) :
        DerivesDs ds bs → DerivesE b b' → ValidNumbering ds.length (letRefers ds) cs →
        DerivesE (.letE ds b) (groupLetWith cs bs b')
  inductive DerivesEs : List SExp → List BExp → Prop where
    | nil : DerivesEs [] []
    | cons {e : SExp} {es : List SExp} {b : BExp} {bs : List BExp} :
        DerivesE e b → DerivesEs es bs → DerivesEs (e :: es) (b :: bs)
  inductive DerivesFs : List (Lab × SExp) → List (Lab × BExp) → Prop where
    | nil : DerivesFs [] []
    | cons {l : Lab} {e : SExp} {fs : List (Lab × SExp)} {b : BExp} {gs : List (Lab × BExp)} :
        DerivesE e b → DerivesFs fs gs → DerivesFs ((l, e) :: fs) ((l, b) :: gs)
  inductive DerivesAs : List (SExp × SExp) → List (BExp × BExp) → Prop where
    | nil : DerivesAs [] []
    | cons {c t : SExp} {r : List (SExp × SExp)} {c' t' : BExp} {r' : List (BExp × BExp)} :
        DerivesE c c' → DerivesE t t' → DerivesAs r r' → DerivesAs ((c, t) :: r) ((c', t') :: r')
  inductive DerivesRs : List (SPat × SExp) → List (BPat × BExp) → Prop where
    | nil : DerivesRs [] []
    | cons {p : SPat} {e : SExp} {r : List (SPat × SExp)} {e' : BExp} {r' : List (BPat × BExp)} :
        DerivesE e e' → DerivesRs r r' → DerivesRs ((p, e) :: r) ((derivePat p, e') :: r')
  /-- df:function-binding, definition by definition. -/
  inductive DerivesDs : List SDef → List BValBind → Prop where
    | nil : DerivesDs [] []
    | fn0 {x : Var} {ann : Option STy} {e : SExp} {r : List SDef} {e' : BExp} {r' : List BValBind} :
        DerivesE e e' → DerivesDs r r' →
        DerivesDs (.fn x ann [] e :: r) (.var x (ann.map deriveTy) e' none :: r')
    | fn1 {x : Var} {ann : Option STy} {p : SPat} {e : SExp} {r : List SDef} {e' : BExp} {r' : List BValBind} :
        DerivesE e e' → DerivesDs r r' →
        DerivesDs (.fn x ann [p] e :: r) (.var x (ann.map deriveTy) (.lam (deriveAtPat p) e') none :: r')
    | fnN {x : Var} {ann : Option STy} {ps : List SPat} {e : SExp} {r : List SDef} {e' : BExp}
        {r' : List BValBind} : ps.length ≥ 2 → DerivesE e e' → DerivesDs r r' →
        DerivesDs (.fn x ann ps e :: r) (.var x (ann.map deriveTy) (D.lams (ps.map deriveAtPat) e') none :: r')
    | pat {p : SPat} {e : SExp} {r : List SDef} {e' : BExp} {r' : List BValBind} :
        DerivesE e e' → DerivesDs r r' → DerivesDs (.pat p e :: r) (.pat (deriveAtPat p) e' :: r')
end

mutual
  theorem deriveExp_derives : ∀ e : SExp, DerivesE e (deriveExp e)
    | .lit l => .lit l
    | .var x => .var x
    | .con k => .con k
    | .opVal o => .opVal o
    | .unit => .unit
    | .tuple [a, b] => by simp only [deriveExp]; exact .tuple2 (deriveExp_derives a) (deriveExp_derives b)
    | .tuple [a, b, c] => by
      simp only [deriveExp]; exact .tuple3 (deriveExp_derives a) (deriveExp_derives b) (deriveExp_derives c)
    | .tuple [] => by simp only [deriveExp]; exact .tupleOther [] (by simp) (by simp)
    | .tuple [a] => by simp only [deriveExp]; exact .tupleOther [a] (by simp) (by simp)
    | .tuple (a :: b :: c :: d :: es) => by
      simp only [deriveExp]; exact .tupleOther _ (by simp) (by simp)
    | .list [] => by simp only [deriveExp]; exact .nil
    | .list (e :: es) => by
      simp only [deriveExp]; exact .list (by simp) (deriveExps_derives (e :: es))
    | .record fs => by simp only [deriveExp]; exact .record (deriveFields_derives fs)
    | .update x fs => by
      simp only [deriveExp]
      split
      · rename_i row h; exact .update (deriveFields_derives fs) h
      · rename_i h; exact .updateEmpty (deriveFields_derives fs) h
    | .accessor l => .accessor l
    | .access e l => by simp only [deriveExp]; exact .access l (deriveExp_derives e)
    | .neg e => by simp only [deriveExp]; exact .neg (deriveExp_derives e)
    | .paren e => by simp only [deriveExp]; exact .paren (deriveExp_derives e)
    | .app f args => by simp only [deriveExp]; exact .app (deriveExp_derives f) (deriveExps_derives args)
    | .binop o l r => by
      by_cases h1 : o = "&&"
      · subst h1; simp only [deriveExp]; exact .andalso (deriveExp_derives l) (deriveExp_derives r)
      by_cases h2 : o = "||"
      · subst h2; simp only [deriveExp]; exact .orelse (deriveExp_derives l) (deriveExp_derives r)
      have : deriveExp (.binop o l r) = D.bin o (deriveExp l) (deriveExp r) := by
        simp [deriveExp]
      rw [this]; exact .binop h1 h2 (deriveExp_derives l) (deriveExp_derives r)
    | .ifte arms e => by
      simp only [deriveExp]
      have ha := deriveArms_derives arms
      split
      · rename_i c t heq
        rw [heq] at ha
        cases ha with
        | cons hc ht hr =>
          cases hr
          exact .ifte1 hc ht (deriveExp_derives e)
      · rename_i hne
        refine .ifteN ha ?_ (deriveExp_derives e)
        intro hl
        cases hda : deriveArms arms with
        | nil => rw [hda] at hl; simp at hl
        | cons x rest =>
          cases rest with
          | nil => exact hne x.1 x.2 (by rw [hda])
          | cons y r => rw [hda] at hl; simp at hl
    | .lam [p] b => by simp only [deriveExp]; exact .lam1 (deriveExp_derives b)
    | .lam [] b => by simp only [deriveExp]; exact .lamN (by simp) (deriveExp_derives b)
    | .lam (p :: q :: ps) b => by simp only [deriveExp]; exact .lamN (by simp) (deriveExp_derives b)
    | .caseE e rules => by
      simp only [deriveExp]; exact .caseE (deriveExp_derives e) (deriveRules_derives rules)
    | .letE ds b => by
      simp only [deriveExp]
      rw [groupLet_eq]
      exact .letE _ (deriveDefs_derives ds) (deriveExp_derives b) (components_valid _ _)
  theorem deriveExps_derives : ∀ es : List SExp, DerivesEs es (deriveExps es)
    | [] => .nil
    | e :: es => .cons (deriveExp_derives e) (deriveExps_derives es)
  theorem deriveFields_derives : ∀ fs : List (Lab × SExp), DerivesFs fs (deriveFields fs)
    | [] => .nil
    | (_, e) :: fs => .cons (deriveExp_derives e) (deriveFields_derives fs)
  theorem deriveArms_derives : ∀ arms : List (SExp × SExp), DerivesAs arms (deriveArms arms)
    | [] => .nil
    | (c, t) :: r => .cons (deriveExp_derives c) (deriveExp_derives t) (deriveArms_derives r)
  theorem deriveRules_derives : ∀ rs : List (SPat × SExp), DerivesRs rs (deriveRules rs)
    | [] => .nil
    | (_, e) :: r => .cons (deriveExp_derives e) (deriveRules_derives r)
  theorem deriveDefs_derives : ∀ ds : List SDef, DerivesDs ds (deriveDefs ds)
    | [] => .nil
    | .fn _ _ [] e :: r => .fn0 (deriveExp_derives e) (deriveDefs_derives r)
    | .fn _ _ [_] e :: r => .fn1 (deriveExp_derives e) (deriveDefs_derives r)
    | .fn _ _ (_ :: _ :: _) e :: r => by
      simp only [deriveDefs]; exact .fnN (by simp) (deriveExp_derives e) (deriveDefs_derives r)
    | .pat _ e :: r => .pat (deriveExp_derives e) (deriveDefs_derives r)
end

/-! ## Modules -/

/-- Each definition of a module derived as the appendix allows; a port has no binding. -/
inductive TopBindsRel : List TopVal → List (Option BValBind) → Prop where
  | nil : TopBindsRel [] []
  | port {x : Var} {t : STy} {vs : List TopVal} {bs : List (Option BValBind)} :
      TopBindsRel vs bs → TopBindsRel (.port x t :: vs) (none :: bs)
  | val {d : SDef} {b : BValBind} {vs : List TopVal} {bs : List (Option BValBind)} :
      DerivesDs [d] [b] → TopBindsRel vs bs → TopBindsRel (.val d :: vs) (some b :: bs)

/-- A module and the bare modules Appendix A allows for it: any numbering of its ports and
    definitions the book's relation allows, any order of its aliases in which each comes after the
    aliases it mentions, and its definitions derived as the appendix allows. -/
def DerivesTo (m : SModule) (b : BModule) : Prop :=
  b.header = ⟨m.header.isPort, m.header.name, deriveExposing m.header.exposing⟩ ∧
  b.imports = m.imports.map (fun i => ⟨i.mod, i.alias, i.exposing.map deriveExposing⟩) ∧
  ∃ cs order bs, ValidNumbering (topValsOf m.decls).length (topRefers (topValsOf m.decls)) cs ∧
    ValidAliasOrder (aliasesOf m.decls) order ∧ TopBindsRel (topValsOf m.decls) bs ∧
    b.body = assemble m.decls cs order bs

theorem deriveDef_derives (d : SDef) : DerivesDs [d] [deriveDef d] := by
  have h := deriveDefs_derives [d]
  match d with
  | .fn _ _ [] _ => exact h
  | .fn _ _ [_] _ => exact h
  | .fn _ _ (_ :: _ :: _) _ => exact h
  | .pat _ _ => exact h

theorem topBinds_rel : ∀ vs : List TopVal, TopBindsRel vs (topBinds vs)
  | [] => .nil
  | .port _ _ :: vs => .port (topBinds_rel vs)
  | .val d :: vs => .val (deriveDef_derives d) (topBinds_rel vs)

theorem aliases_names : ∀ ds : List STopDec,
    (aliasesOf ds).map (·.1) = ds.flatMap fun d => match d with
      | .alias c _ _ => [c]
      | _ => []
  | [] => rfl
  | d :: ds => by
    have ih := aliases_names ds
    unfold aliasesOf at ih ⊢
    cases d <;> simp only [List.filterMap_cons, List.flatMap_cons, List.map_cons, List.nil_append,
      List.cons_append] <;> first | exact ih | (congr 1)

theorem aliasDecls_eq : ∀ ds : List STopDec,
    (ds.flatMap fun d => match d with
      | .alias c _ t => [(c, t)]
      | _ => []) = (aliasesOf ds).map (fun a => (a.1, a.2.2))
  | [] => rfl
  | d :: ds => by
    have ih := aliasDecls_eq ds
    unfold aliasesOf at ih ⊢
    cases d <;> simp only [List.filterMap_cons, List.flatMap_cons, List.map_cons, List.nil_append,
      List.cons_append] <;> first | exact ih | (congr 1)

theorem plus_congr {n : Nat} {r r' : Nat → Nat → Bool} (hr : ∀ a b, a < n → b < n → r a b = r' a b) :
    ∀ {i j}, Plus n r i j → Plus n r' i j := by
  intro i j h
  induction h with
  | step hi hj he => exact .step hi hj (by rw [← hr _ _ hi hj]; exact he)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Under the restrictions of the module, the function's choices are among those the appendix
    allows. -/
theorem derive_derivesTo (m : SModule) (h : ModuleOK m) : DerivesTo m (deriveModule m) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, htd, -, -, -, -, -, hanr, -⟩ := h
  have hnames : ((aliasesOf m.decls).map (·.1)).Nodup := by
    rw [aliases_names]
    exact (List.nodup_append.mp htd).2.1
  have hdecls : m.aliasDecls = (aliasesOf m.decls).map (fun a => (a.1, a.2.2)) := aliasDecls_eq m.decls
  have hlen : m.aliasDecls.length = (aliasesOf m.decls).length := by rw [hdecls]; simp
  have hrel : ∀ a b, a < (aliasesOf m.decls).length → b < (aliasesOf m.decls).length →
      mentionsIdx (aliasesOf m.decls) a b = aliasRefers m a b := by
    intro a b ha hb
    simp only [mentionsIdx, aliasRefers, hdecls, List.getElem?_map, List.getElem?_eq_getElem ha,
      List.getElem?_eq_getElem hb, Option.map_some, mentions]
    have : (aliasesOf m.decls).any (fun x => x.1 == (aliasesOf m.decls)[b].1) = true :=
      List.any_eq_true.mpr ⟨_, List.getElem_mem hb, by simp⟩
    simp only [this, Bool.true_and]
    congr 1
  have hacyc : ∀ i < (aliasesOf m.decls).length, ¬ Plus (aliasesOf m.decls).length (mentionsIdx (aliasesOf m.decls)) i i := by
    intro i hi hp
    have := plus_congr (r' := aliasRefers m) hrel hp
    rw [← hlen] at this
    exact hanr i (by rw [hlen]; exact hi) this
  refine ⟨rfl, rfl, _, _, _, components_valid _ _, aliasOrder_valid hnames hacyc, topBinds_rel _, rfl⟩

end StandardElm.Src
