/-
  A Standard Definition of Elm? Mechanisation: the module step (plan step 10), third part: type
  declarations. In a closed context, two type environments that both satisfy r:sm-topdec-types for
  one ordered phrase and give its custom types the same names are equal (`checkTypes_unique`):
  an alias reads only the type functions of the names it mentions, which are custom types (whose
  type functions their names fix) and earlier aliases. The names two module derivations give a
  custom type correspond by the instance at the type declaration's node (`custom_corr`).
-/
import StandardElmMech.Stat.ModuleStepClosed
import StandardElmMech.Stat.RefuseScope

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BDatBind BTypBind BConBind)

namespace Types

/-! ## Type expressions read only the type functions of the names they mention -/

/-- Two contexts that agree on what type expressions read. -/
def SameLook (C C' : Ctx) (P : LongId → Prop) : Prop :=
  C.U = C'.U ∧ ∀ c, P c → (C.lookupTy c).map (·.1) = (C'.lookupTy c).map (·.1)

theorem SameLook.mono {C C' : Ctx} {P Q : LongId → Prop} (h : SameLook C C' P) (hq : ∀ c, Q c → P c) :
    SameLook C C' Q := ⟨h.1, fun c hc => h.2 c (hq c hc)⟩

theorem SameLook.plusU {C C' : Ctx} {P : LongId → Prop} (h : SameLook C C' P) (U : List BVar) :
    SameLook (C.plusU U) (C'.plusU U) P := ⟨by simp [Ctx.plusU, h.1], fun c hc => h.2 c hc⟩

/-- The names of a type expression read as a predicate on long identifiers. -/
def mentions (l : List String) (c : LongId) : Prop := c.qual = none → c.id ∈ l

mutual
theorem elabTy_congr {C C' : Ctx} : (t : BTy) → SameLook C C' (mentions (bTyCons t)) → elabTy C t = elabTy C' t
  | .tyvar a, h => by simp only [elabTy, h.1]
  | .record row, h => by
    simp only [elabTy, elabTyRowOpt_congr row (h.mono fun c hc => by simpa [bTyCons] using hc)]
  | .openRecord r row, h => by
    simp only [elabTy, h.1, elabTyRow_congr row (h.mono fun c hc => by simpa [bTyCons] using hc)]
  | .unit, _ => rfl
  | .tuple t1 t2 t3, h => by
    simp only [elabTy,
      elabTy_congr t1 (h.mono fun c hc hq => by simp [bTyCons, hc hq]),
      elabTy_congr t2 (h.mono fun c hc hq => by simp [bTyCons, hc hq]),
      elabTyOpt_congr t3 (h.mono fun c hc hq => by simp [bTyCons, hc hq])]
  | .con c args, h => by
    have hl := h.2 c fun hq => by simp [bTyCons, hq]
    have ha := elabTyList_congr args (h.mono fun c hc hq => by simp [bTyCons, hc hq])
    simp only [elabTy, ha]
    rcases hc1 : C.lookupTy c with _ | ⟨θ, VEa⟩ <;> rcases hc2 : C'.lookupTy c with _ | ⟨θ', VEb⟩ <;>
      rw [hc1, hc2] at hl <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hl
    all_goals (try subst hl)
    all_goals (cases elabTyList C' args <;> rfl)
  | .fn t1 t2, h => by
    simp only [elabTy,
      elabTy_congr t1 (h.mono fun c hc hq => by simp [bTyCons, hc hq]),
      elabTy_congr t2 (h.mono fun c hc hq => by simp [bTyCons, hc hq])]
  | .paren t, h => by simp only [elabTy, elabTy_congr t (h.mono fun c hc => by simpa [bTyCons] using hc)]
theorem elabTyRow_congr {C C' : Ctx} : (r : BTyRow) → SameLook C C' (mentions (bTyRowCons r)) → elabTyRow C r = elabTyRow C' r
  | .field l t rest, h => by
    simp only [elabTyRow,
      elabTy_congr t (h.mono fun c hc hq => by simp [bTyRowCons, hc hq]),
      elabTyRowOpt_congr rest (h.mono fun c hc hq => by simp [bTyRowCons, hc hq])]
theorem elabTyRowOpt_congr {C C' : Ctx} : (r : Option BTyRow) → SameLook C C' (mentions (bTyRowOptCons r)) →
    elabTyRowOpt C r = elabTyRowOpt C' r
  | none, _ => rfl
  | some r, h => by simp only [elabTyRowOpt]; exact elabTyRow_congr r (h.mono fun c hc => by simpa [bTyRowOptCons] using hc)
theorem elabTyOpt_congr {C C' : Ctx} : (t : Option BTy) → SameLook C C' (mentions (bTyOptCons t)) →
    elabTyOpt C t = elabTyOpt C' t
  | none, _ => rfl
  | some t, h => by simp only [elabTyOpt, elabTy_congr t (h.mono fun c hc => by simpa [bTyOptCons] using hc)]
theorem elabTyList_congr {C C' : Ctx} : (ts : List BTy) → SameLook C C' (mentions (bTyListCons ts)) →
    elabTyList C ts = elabTyList C' ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [elabTyList,
      elabTy_congr t (h.mono fun c hc hq => by simp [bTyListCons, hc hq]),
      elabTyList_congr ts (h.mono fun c hc hq => by simp [bTyListCons, hc hq])]
end

/-- Contexts that agree on every lookup and on their free variables. -/
def SameAll (C C' : Ctx) : Prop := SameLook C C' (fun _ => True) ∧ C.tyvars = C'.tyvars

theorem SameAll.ty {C C' : Ctx} (h : SameAll C C') (U : List BVar) (t : BTy) :
    elabTy (C.plusU U) t = elabTy (C'.plusU U) t :=
  elabTy_congr t ((h.1.plusU U).mono fun _ _ => trivial)

theorem SameAll.tys {C C' : Ctx} (h : SameAll C C') (U : List BVar) (ts : List BTy) :
    elabTyList (C.plusU U) ts = elabTyList (C'.plusU U) ts :=
  elabTyList_congr ts ((h.1.plusU U).mono fun _ _ => trivial)

theorem elabConBind_congr {C C' : Ctx} (hU : ∀ ts, elabTyList C ts = elabTyList C' ts) (τ : Ty) :
    (cb : BConBind) → elabConBind C τ cb = elabConBind C' τ cb
  | [] => rfl
  | (k, tys) :: rest => by simp only [elabConBind, hU, elabConBind_congr hU τ rest]

theorem elabDatBind_congr {C C' : Ctx} (h : SameAll C C') {names names' : String → Option TyName} :
    (d : BDatBind) → (∀ e ∈ d, names e.1 = names' e.1) → elabDatBind C names d = elabDatBind C' names' d
  | [], _ => rfl
  | (c, ps, cb) :: rest, hn => by
    simp only [elabDatBind, hn _ (List.mem_cons_self ..), h.tys,
      elabConBind_congr (fun ts => h.tys _ ts), h.2,
      elabDatBind_congr h rest fun e he => hn e (List.mem_cons_of_mem _ he)]

theorem elabTypBind_congr {C C' : Ctx} (hU : ∀ U, elabTy (C.plusU U) = elabTy (C'.plusU U)) (hA : C.tyvars = C'.tyvars)
    (tb : BTypBind) : elabTypBind C tb = elabTypBind C' tb := by
  simp only [elabTypBind, hU, hA]

theorem elabTypBinds_congr {C C' : Ctx} (h : SameAll C C') : (tbs : List BTypBind) → elabTypBinds C tbs = elabTypBinds C' tbs
  | [] => rfl
  | tb :: tbs => by
    simp only [elabTypBinds, elabTypBind_congr (fun U => funext (h.ty U)) h.2 tb, elabTypBinds_congr h tbs]

/-! ## The structure of a checked type declaration -/

theorem elabTypBind_shape {C : Ctx} {tb : BTypBind} {VE : ValEnv} {TE : TyEnv} (h : elabTypBind C tb = some (VE, TE)) :
    ∃ s, TE = [(tb.c, s)] := by
  unfold elabTypBind at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨_, rfl⟩
    · split at h <;> try cases h
      split at h
      · split at h
        · cases h; exact ⟨_, rfl⟩
        · cases h
      · cases h

theorem elabTypBinds_shape {C : Ctx} : ∀ {tbs : List BTypBind} {VEs : List ValEnv} {TEs : List TyEnv},
    elabTypBinds C tbs = some (VEs, TEs) → ∀ g ∈ TEs, ∃ tb ∈ tbs, ∃ s, g = [(tb.c, s)]
  | [], _, _, h, g, hg => by simp [elabTypBinds] at h; obtain ⟨-, rfl⟩ := h; simp at hg
  | tb :: tbs, VEs, TEs, h, g, hg => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE TE VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rcases List.mem_cons.mp hg with rfl | hg
      · obtain ⟨s, rfl⟩ := elabTypBind_shape h1; exact ⟨tb, List.mem_cons_self .., s, rfl⟩
      · obtain ⟨tb', h', s, e⟩ := elabTypBinds_shape h2 g hg
        exact ⟨tb', List.mem_cons_of_mem _ h', s, e⟩
    · cases h

theorem find_foldl_none {k : String} : ∀ {acc : TyEnv} {fs : List TyEnv}, (∀ g ∈ fs, FMap.find? g k = none) →
    FMap.find? (fs.foldl FMap.modify acc) k = FMap.find? acc k
  | _, [], _ => rfl
  | acc, g :: gs, h => by
    simp only [List.foldl_cons]
    rw [find_foldl_none fun g' hg' => h g' (List.mem_cons_of_mem _ hg'), FMap.find?_modify,
      h g (List.mem_cons_self ..)]
    rfl

/-- An alias's entry in the type environment is what its elaboration gives. -/
theorem find_alias {C : Ctx} : ∀ {tbs : List BTypBind} {VEs : List ValEnv} {TEs : List TyEnv},
    elabTypBinds C tbs = some (VEs, TEs) → (tbs.map (·.c)).Nodup →
    ∀ tb ∈ tbs, ∃ VEt s, elabTypBind C tb = some (VEt, [(tb.c, s)]) ∧ ∀ acc, FMap.find? (TEs.foldl FMap.modify acc) tb.c = some s
  | [], _, _, _, _, tb, htb => by simp at htb
  | tb0 :: rest, VEs, TEs, h, hn, tb, htb => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE0 TE0 VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp htb with rfl | htb
      · obtain ⟨s, rfl⟩ := elabTypBind_shape h1
        refine ⟨VE0, s, h1, fun acc => ?_⟩
        simp only [List.foldl_cons]
        rw [find_foldl_none, FMap.find?_modify]
        · simp [FMap.find?]
        · intro g hg
          obtain ⟨tb', h', s', rfl⟩ := elabTypBinds_shape h2 g hg
          have : tb'.c ≠ tb.c := fun e => hn.1 (e ▸ List.mem_map_of_mem h')
          simp [FMap.find?, this]
      · obtain ⟨VEt, s, he, hf⟩ := find_alias h2 hn.2 tb htb
        exact ⟨VEt, s, he, fun acc => hf _⟩
    · cases h

theorem elabDatBind_keys {C : Ctx} {names : String → Option TyName} : ∀ {d : BDatBind} {VE' : ValEnv} {TE' : TyEnv},
    elabDatBind C names d = some (VE', TE') → ∀ p ∈ TE', p.1 ∈ d.map (·.1)
  | [], _, _, h, p, hp => by simp [elabDatBind] at h; obtain ⟨-, rfl⟩ := h; simp at hp
  | (c, ps, cb) :: rest, VE', TE', h, p, hp => by
    simp only [elabDatBind] at h
    split at h; · cases h
    split at h
    · rename_i τs VE1 TE1 h1 h2
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          rcases Closed.mem_modify hp with hp | hp
          · exact List.mem_cons_of_mem _ (elabDatBind_keys h2 p hp)
          · simp at hp; simp [hp]
        · cases h
      · cases h
    · cases h

theorem elabDatBind_names {C : Ctx} {names : String → Option TyName} : ∀ {d : BDatBind} {VE' : ValEnv} {TE' : TyEnv},
    elabDatBind C names d = some (VE', TE') → (d.map (·.1)).Nodup →
    ∀ e ∈ d, ∃ t, names e.1 = some t ∧ ∃ s ∈ TE'.vals, s.1 = t.toFcn
  | [], _, _, _, _, e, he => by simp at he
  | (c, ps, cb) :: rest, VE', TE', h, hn, e, he => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [elabDatBind] at h
    split at h; · cases h
    rename_i t ht
    split at h
    · rename_i τs VE1 TE1 h1 h2
      split at h
      · rename_i VEc _
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          rcases List.mem_cons.mp he with rfl | he
          · refine ⟨t, ht, (t.toFcn, closVE C.tyvars VEc), ?_, rfl⟩
            have hk : c ∉ FMap.keys TE1 := fun hk => by
              obtain ⟨p, hp, e⟩ := List.mem_map.mp hk
              exact hn.1 (e ▸ elabDatBind_keys h2 p hp)
            simp only [FMap.modify, FMap.vals, List.map_append, List.mem_append, List.mem_map]
            exact .inr ⟨_, List.mem_filter.mpr ⟨List.mem_singleton_self _, by simpa using hk⟩, rfl⟩
          · obtain ⟨t', ht', s, hs, e'⟩ := elabDatBind_names h2 hn.2 e he
            refine ⟨t', ht', s, ?_, e'⟩
            simp only [FMap.modify, FMap.vals, List.map_append, List.mem_append]
            exact .inl hs
        · cases h
      · cases h
    · cases h

/-! ## Uniqueness -/

theorem typesOrdered_dec {db : Option BDatBind} {tbs : List BTypBind} (h : typesOrdered db tbs = true) :
    ((db.getD []).map (·.1) ++ tbs.map (·.c)).Nodup ∧
      ∀ i j (hi : i < tbs.length) (hj : j < tbs.length), i ≤ j → tbs[j].c ∉ bTyCons tbs[i].t := by
  simp only [typesOrdered, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun i j hi hj hij hm => ?_⟩
  have hx : (tbs[i], i) ∈ tbs.zipIdx := by
    rw [List.mem_iff_getElem]; exact ⟨i, by simpa using hi, by simp [List.getElem_zipIdx]⟩
  have h2 := h.2 _ hx
  simp only [List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
  apply h2 tbs[j] _ hm
  rw [List.mem_iff_getElem]
  refine ⟨j - i, by simp; omega, ?_⟩
  simp only [List.getElem_drop]
  congr 1; omega

theorem namesOf_some {TE : TyEnv} {c : String} {t : TyName} (h : namesOf TE c = some t) :
    ∃ s, FMap.find? TE c = some s ∧ s.1 = t.toFcn := by
  unfold namesOf at h
  cases hf : FMap.find? TE c with
  | none => rw [hf] at h; cases h
  | some s =>
    rw [hf] at h
    simp only [Option.bind_some] at h
    refine ⟨s, rfl, ?_⟩
    unfold TyFcn.name? at h
    split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h

theorem lookupTy_oplusTE (C : Ctx) (TE : TyEnv) (U : List BVar) (c : LongId) :
    ((C.oplusTE TE).plusU U).lookupTy c =
      (match c.qual with | none => (FMap.find? TE c.id).or (FMap.find? C.E.TE c.id) | some _ => C.lookupTy c) := by
  cases h : c.qual <;> simp [Ctx.lookupTy, Env.lookupTy, Ctx.oplusTE, Ctx.plusU, FMap.find?_modify, h]

/-- What a checked type declaration is made of. -/
theorem fix_parts {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (h : checkTypesFix C TE VE db tbs = true) :
    ∃ VEs TEs VE' TE', elabTypBinds (C.oplusTE TE) tbs = some (VEs, TEs) ∧
      (db = none → VE' = [] ∧ TE' = []) ∧
      (∀ d, db = some d → elabDatBind (C.oplusTE TE) (namesOf TE) d = some (VE', TE') ∧ namesNewB C.T TE' = true) ∧
      TE = FMap.modify TE' (FMap.plusAll TEs) ∧ VE = FMap.modify VE' (FMap.plusAll VEs) := by
  unfold checkTypesFix at h
  cases db with
  | none =>
    simp only at h
    split at h
    · rename_i VEs TEs h1
      simp only [decide_eq_true_eq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      refine ⟨VEs, TEs, [], [], h1, fun _ => ⟨rfl, rfl⟩, fun d e => by simp at e, ?_, ?_⟩ <;>
        simp [FMap.modify]
    · cases h
  | some d =>
    simp only at h
    split at h
    · rename_i VE' TE' VEs TEs h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hn, _, rfl, rfl⟩ := h
      refine ⟨VEs, TEs, VE', TE', h2, fun e => by simp at e, ?_, rfl, rfl⟩
      intro d' e
      simp only [Option.some.injEq] at e
      subst e
      exact ⟨h1, hn⟩
    · cases h

theorem find_other {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (h : checkTypesFix C TE VE db tbs = true) {c : String} (h1 : c ∉ (db.getD []).map (·.1)) (h2 : c ∉ tbs.map (·.c)) :
    FMap.find? TE c = none := by
  obtain ⟨VEs, TEs, VE', TE', hT, hn, hd, rfl, -⟩ := fix_parts h
  rw [FMap.find?_modify]
  have e1 : FMap.find? (FMap.plusAll TEs) c = none := by
    unfold FMap.plusAll
    rw [find_foldl_none]; · rfl
    intro g hg
    obtain ⟨tb, htb, s, rfl⟩ := elabTypBinds_shape hT g hg
    have : tb.c ≠ c := fun e => h2 (e ▸ List.mem_map_of_mem htb)
    simp [FMap.find?, this]
  have e2 : FMap.find? TE' c = none := by
    cases db with
    | none => rw [(hn rfl).2]; rfl
    | some d =>
      cases hf : FMap.find? TE' c with
      | none => rfl
      | some v => exact absurd (elabDatBind_keys (hd d rfl).1 _ (find?_mem hf)) h1
  rw [e1, e2]; rfl

theorem find_alias' {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (h : checkTypesFix C TE VE db tbs = true) (hnd : (tbs.map (·.c)).Nodup) {tb : BTypBind} (htb : tb ∈ tbs) :
    ∃ VEt s, elabTypBind (C.oplusTE TE) tb = some (VEt, [(tb.c, s)]) ∧ FMap.find? TE tb.c = some s := by
  obtain ⟨VEs, TEs, VE', TE', hT, -, -, rfl, -⟩ := fix_parts h
  obtain ⟨VEt, s, he, hf⟩ := find_alias hT hnd tb htb
  refine ⟨VEt, s, he, ?_⟩
  rw [FMap.find?_modify]
  have := hf []
  unfold FMap.plusAll; rw [this]; rfl

/-- Two type environments satisfying r:sm-topdec-types for one ordered phrase in one closed
    context, with the same names for the custom types, are equal. -/
theorem checkTypes_unique {C : Ctx} (hC : C.tyvars = []) {TEa TEb : TyEnv} {VEa VEb : ValEnv}
    {db : Option BDatBind} {tbs : List BTypBind}
    (ha : checkTypes C TEa VEa db tbs = true) (hb : checkTypes C TEb VEb db tbs = true)
    (ho : typesOrdered db tbs = true) (hn : ∀ e ∈ db.getD [], namesOf TEa e.1 = namesOf TEb e.1) :
    TEa = TEb ∧ VEa = VEb := by
  obtain ⟨hnd, hord⟩ := typesOrdered_dec ho
  have hndd : ((db.getD []).map (·.1)).Nodup := (List.nodup_append.mp hnd).1
  have hndt : (tbs.map (·.c)).Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj : ∀ c ∈ (db.getD []).map (·.1), c ∉ tbs.map (·.c) := fun c h1 h2 =>
    (List.nodup_append.mp hnd).2.2 c h1 c h2 rfl
  have fa := checkTypes_fix ha
  have fb := checkTypes_fix hb
  have hCa := Closed.oplusTE_closed hC (checkTypes_closed ha)
  have hCb := Closed.oplusTE_closed hC (checkTypes_closed hb)
  obtain ⟨VEsa, TEsa, VEa', TEa', hTa, hna, hda, eTa, eVa⟩ := fix_parts fa
  obtain ⟨VEsb, TEsb, VEb', TEb', hTb, hnb, hdb, eTb, eVb⟩ := fix_parts fb
  -- custom types
  have hcust : ∀ c ∈ (db.getD []).map (·.1), (FMap.find? TEa c).map (·.1) = (FMap.find? TEb c).map (·.1) := by
    intro c hc
    cases db with
    | none => simp at hc
    | some d =>
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
      obtain ⟨t, ht, -⟩ := elabDatBind_names (hda d rfl).1 hndd e he
      have ht' : namesOf TEb e.1 = some t := (hn e he) ▸ ht
      obtain ⟨sa, h1, h2⟩ := namesOf_some ht
      obtain ⟨sb, h3, h4⟩ := namesOf_some ht'
      rw [h1, h3]; simp [h2, h4]
  have hoth : ∀ c, c ∉ (db.getD []).map (·.1) → c ∉ tbs.map (·.c) →
      (FMap.find? TEa c).map (·.1) = (FMap.find? TEb c).map (·.1) := fun c h1 h2 => by
    rw [find_other fa h1 h2, find_other fb h1 h2]
  -- lookups agree where a type expression's names agree
  have look : ∀ (l : List String), (∀ c ∈ l, (FMap.find? TEa c).map (·.1) = (FMap.find? TEb c).map (·.1)) →
      ∀ U, SameLook ((C.oplusTE TEa).plusU U) ((C.oplusTE TEb).plusU U) (mentions l) := by
    intro l hl U
    refine ⟨by simp [Ctx.plusU, Ctx.oplusTE], fun c hc => ?_⟩
    rw [lookupTy_oplusTE, lookupTy_oplusTE]
    cases hq : c.qual with
    | some _ => rfl
    | none =>
      simp only
      have := hl c.id (hc hq)
      cases e1 : FMap.find? TEa c.id <;> cases e2 : FMap.find? TEb c.id <;> rw [e1, e2] at this <;>
        simp_all
  -- aliases, in order
  have halias : ∀ i (hi : i < tbs.length),
      (FMap.find? TEa tbs[i].c).map (·.1) = (FMap.find? TEb tbs[i].c).map (·.1) := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro hi
      obtain ⟨VEt, sa, hea, hfa⟩ := find_alias' fa hndt (List.getElem_mem hi)
      obtain ⟨VEt', sb, heb, hfb⟩ := find_alias' fb hndt (List.getElem_mem hi)
      have hl : ∀ c ∈ bTyCons tbs[i].t, (FMap.find? TEa c).map (·.1) = (FMap.find? TEb c).map (·.1) := by
        intro c hc
        by_cases h1 : c ∈ (db.getD []).map (·.1)
        · exact hcust c h1
        · by_cases h2 : c ∈ tbs.map (·.c)
          · obtain ⟨j, hj, e⟩ := List.getElem_of_mem h2
            simp only [List.getElem_map] at e
            have hji : j < i := Nat.lt_of_not_le fun hle =>
              hord i j hi (by simpa using hj) hle (by rw [e]; exact hc)
            rw [← e]; exact ih j hji _
          · exact hoth c h1 h2
      have e : elabTypBind (C.oplusTE TEa) tbs[i] = elabTypBind (C.oplusTE TEb) tbs[i] := by
        unfold elabTypBind
        rw [show (C.oplusTE TEa).tyvars = (C.oplusTE TEb).tyvars by rw [hCa, hCb]]
        rw [elabTy_congr _ (look _ hl _)]
      rw [hea, heb] at e
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at e
      rw [hfa, hfb, e.2.2]
  have hall : ∀ c, (FMap.find? TEa c).map (·.1) = (FMap.find? TEb c).map (·.1) := by
    intro c
    by_cases h1 : c ∈ (db.getD []).map (·.1)
    · exact hcust c h1
    · by_cases h2 : c ∈ tbs.map (·.c)
      · obtain ⟨j, hj, e⟩ := List.getElem_of_mem h2
        simp only [List.getElem_map] at e
        rw [← e]; exact halias j _
      · exact hoth c h1 h2
  have hsame : SameAll (C.oplusTE TEa) (C.oplusTE TEb) := by
    refine ⟨?_, by rw [hCa, hCb]⟩
    have := look [] (by simp) []
    refine ⟨by simp [Ctx.oplusTE], fun c _ => ?_⟩
    have h := (look [c.id] (by simp [hall]) []).2 c (fun _ => by simp)
    simpa [Ctx.plusU, Ctx.lookupTy] using h
  have eT := elabTypBinds_congr hsame tbs
  rw [hTa, hTb] at eT
  simp only [Option.some.injEq, Prod.mk.injEq] at eT
  obtain ⟨rfl, rfl⟩ := eT
  have eD : VEa' = VEb' ∧ TEa' = TEb' := by
    cases db with
    | none => rw [(hna rfl).1, (hna rfl).2, (hnb rfl).1, (hnb rfl).2]; exact ⟨rfl, rfl⟩
    | some d =>
      have := elabDatBind_congr hsame d (fun e he => hn e he)
      rw [(hda d rfl).1, (hdb d rfl).1] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact this
  obtain ⟨rfl, rfl⟩ := eD
  exact ⟨eTa.trans eTb.symm, eVa.trans eVb.symm⟩

/-! ## The names of custom types correspond -/

theorem name?_toFcn (t : TyName) : t.toFcn.name? = some t := by
  simp [TyFcn.name?, TyName.toFcn]

theorem natsUpTo_length : ∀ n, (natsUpTo n).length = n
  | 0 => rfl
  | n + 1 => by simp [natsUpTo, natsUpTo_length n]

theorem applyList_length {S : Subst} : ∀ {l l' : List Ty}, S.applyList l = some l' → l'.length = l.length
  | [], l', h => by simp [Subst.applyList] at h; subst h; rfl
  | τ :: rest, l', h => by
    simp only [Subst.applyList] at h
    cases h1 : S.apply τ <;> cases h2 : S.applyList rest <;> rw [h1, h2] at h <;> simp at h
    subst h; simp [applyList_length h2]

theorem renameList_length {ν : List (TyName × TyName)} : ∀ l : List Ty, (Ty.renameList ν l).length = l.length
  | [] => rfl
  | _ :: rest => by simp [Ty.renameList, renameList_length rest]

theorem find_corr {F F2 : TyStr → Ty} {G : Ty → Option Ty} {c : String} :
    ∀ {TE TE2 : TyEnv}, TE.map (·.1) = TE2.map (·.1) → (TE.map fun p => F p.2).mapM G = some (TE2.map fun p => F2 p.2) →
      ∀ {x : TyStr}, FMap.find? TE c = some x → ∃ y, FMap.find? TE2 c = some y ∧ G (F x) = some (F2 y)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], hk, _, _, _ => by simp at hk
  | (k, v) :: rest, (k2, v2) :: rest2, hk, hm, x, hf => by
    simp only [List.map_cons, List.cons.injEq] at hk
    obtain ⟨rfl, hk⟩ := hk
    simp only [List.map_cons, List.mapM_cons] at hm
    cases h1 : G (F v) <;> cases h2 : (rest.map fun p => F p.2).mapM G <;> simp [h1, h2] at hm
    obtain ⟨e1, e2⟩ := hm
    simp only [FMap.find?] at hf ⊢
    split at hf
    · cases hf; exact ⟨v2, by simp [*], by rw [h1, e1]⟩
    · rw [if_neg ‹_›]
      exact find_corr hk (by rw [h2, e2]) hf

/-- The instance at a type declaration's node relates the names the two derivations give each
    custom type: the instance's bijection takes one to the other, keeping the arity; and the
    name is new. -/
theorem custom_corr {C C' : Ctx} {TE TE2 : TyEnv} {VE VE2 : ValEnv} {d : BDatBind} {tbs : List BTypBind}
    (h : checkTypes C TE VE (some d) tbs = true) (h2 : checkTypes C' TE2 VE2 (some d) tbs = true)
    (hnd : (d.map (·.1)).Nodup) {S : Subst} {ν : List (TyName × TyName)}
    (hS : ((TE.map (·.2.1.body)).map (Ty.renameNames ν)).mapM S.apply = some (TE2.map (·.2.1.body))) :
    ∀ e ∈ d, ∃ t, namesOf TE e.1 = some t ∧ namesOf TE2 e.1 = some (renameName ν t) ∧
      (renameName ν t).arity = t.arity ∧ t ∉ C.T := by
  intro e he
  have hk : TE.map (·.1) = TE2.map (·.1) := by
    have a1 := congrArg (List.map (·.1)) (RScope.checkTypes_sk h)
    have a2 := congrArg (List.map (·.1)) (RScope.checkTypes_sk h2)
    simp only [FMap.mapV, List.map_map, Function.comp_def] at a1 a2
    rw [a1, a2]
  obtain ⟨VEs, TEs, VE', TE', -, -, hd, -, -⟩ := fix_parts (checkTypes_fix h)
  obtain ⟨VEs2, TEs2, VE2', TE2', -, -, hd2, -, -⟩ := fix_parts (checkTypes_fix h2)
  obtain ⟨t, ht, s0, hs0, es0⟩ := elabDatBind_names (hd d rfl).1 hnd e he
  obtain ⟨t2, ht2, -⟩ := elabDatBind_names (hd2 d rfl).1 hnd e he
  have hnew : t ∉ C.T := namesNewB_spec _ _ (hd d rfl).2 s0 hs0 t (by rw [es0, name?_toFcn])
  obtain ⟨s, hs, es⟩ := namesOf_some ht
  obtain ⟨s2, hs2, es2⟩ := namesOf_some ht2
  rw [List.map_map] at hS
  obtain ⟨y, hy, hG⟩ := find_corr (F := fun x => Ty.renameNames ν x.1.body) (F2 := fun x => x.1.body) hk hS hs
  rw [hs2] at hy; cases hy
  simp only [es, es2, TyName.toFcn, Ty.renameNames, Subst.apply] at hG
  cases hL : S.applyList (Ty.renameList ν ((natsUpTo t.arity).map fun i => Ty.var (.bnd i .any))) with
  | none => rw [hL] at hG; cases hG
  | some L =>
    rw [hL] at hG
    simp only [Option.some.injEq, Ty.con.injEq] at hG
    obtain ⟨eL, et⟩ := hG
    refine ⟨t, ht, by rw [ht2, et], ?_, hnew⟩
    have := applyList_length hL
    rw [eL, renameList_length] at this
    simp only [List.length_map, natsUpTo_length] at this
    rw [et]; exact this

/-! ## The environment of a type declaration is closed -/

theorem elabDatBind_closed {C : Ctx} (hC : C.tyvars = []) {names : String → Option TyName} :
    ∀ {d : BDatBind} {VE' : ValEnv} {TE' : TyEnv}, elabDatBind C names d = some (VE', TE') →
      (∀ q ∈ VE', q.2.1.tyvars = []) ∧ ∀ p ∈ TE', ∀ q ∈ p.2.2, q.2.1.tyvars = []
  | [], _, _, h => by simp [elabDatBind] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | (c, ps, cb) :: rest, VE', TE', h => by
    simp only [elabDatBind] at h
    split at h; · cases h
    split at h
    · rename_i τs VE1 TE1 h1 h2
      have ih := elabDatBind_closed hC h2
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [hC]
          refine ⟨fun q hq => ?_, fun p hp q hq => ?_⟩
          · rcases Closed.mem_modify hq with hq | hq
            · exact ih.1 q hq
            · exact Closed.closVE_closed _ q hq
          · rcases Closed.mem_modify hp with hp | hp
            · exact ih.2 p hp q hq
            · simp at hp; subst hp; exact Closed.closVE_closed _ q hq
        · cases h
      · cases h
    · cases h

theorem elabTypBind_closed {C : Ctx} (hC : C.tyvars = []) {tb : BTypBind} {VE : ValEnv} {TE : TyEnv}
    (h : elabTypBind C tb = some (VE, TE)) :
    (∀ q ∈ VE, q.2.1.tyvars = []) ∧ ∀ p ∈ TE, ∀ q ∈ p.2.2, q.2.1.tyvars = [] := by
  unfold elabTypBind at h
  rw [hC] at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
    · split at h <;> try cases h
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨Closed.closVE_closed _, fun p hp q hq => ?_⟩
          simp at hp; subst hp; exact Closed.closVE_closed _ q hq
        · cases h
      · cases h

theorem elabTypBinds_closed {C : Ctx} (hC : C.tyvars = []) : ∀ {tbs : List BTypBind} {VEs : List ValEnv} {TEs : List TyEnv},
    elabTypBinds C tbs = some (VEs, TEs) →
      (∀ g ∈ VEs, ∀ q ∈ g, q.2.1.tyvars = []) ∧ ∀ g ∈ TEs, ∀ p ∈ g, ∀ q ∈ p.2.2, q.2.1.tyvars = []
  | [], _, _, h => by simp [elabTypBinds] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | tb :: tbs, VEs, TEs, h => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE TE VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have a := elabTypBind_closed hC h1
      have b := elabTypBinds_closed hC h2
      refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact a.1
        · exact b.1 g hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact a.2
        · exact b.2 g hg
    · cases h

/-- What a type declaration gives in a closed context is closed, constructors included. -/
theorem types_closed {C : Ctx} (hC : C.tyvars = []) {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind}
    {tbs : List BTypBind} (h : checkTypes C TE VE db tbs = true) :
    (⟨[], TE, VE⟩ : Env).tyvars = [] ∧ ∀ p ∈ TE, ∀ q ∈ p.2.2, q.2.1.tyvars = [] := by
  have hTE := checkTypes_closed h
  have hCte := Closed.oplusTE_closed hC hTE
  obtain ⟨VEs, TEs, VE', TE', hT, hn, hd, eT, eV⟩ := fix_parts (checkTypes_fix h)
  have hb := elabTypBinds_closed hCte hT
  have hdd : (∀ q ∈ VE', q.2.1.tyvars = []) ∧ ∀ p ∈ TE', ∀ q ∈ p.2.2, q.2.1.tyvars = [] := by
    cases db with
    | none => rw [(hn rfl).1, (hn rfl).2]; simp
    | some d => exact elabDatBind_closed hCte (hd d rfl).1
  refine ⟨Closed.env_tyvars_nil.mpr ⟨rfl, hTE, Closed.valEnv_closed fun q hq => ?_⟩, fun p hp q hq => ?_⟩
  · rw [eV] at hq
    rcases Closed.mem_modify hq with hq | hq
    · obtain ⟨g, hg, hq⟩ := Closed.mem_plusAll hq; exact hb.1 g hg q hq
    · exact hdd.1 q hq
  · rw [eT] at hp
    rcases Closed.mem_modify hp with hp | hp
    · obtain ⟨g, hg, hp⟩ := Closed.mem_plusAll hp; exact hb.2 g hg p hp q hq
    · exact hdd.2 p hp q hq

end Types

end StandardElm.Stat
