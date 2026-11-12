/-
  A Standard Definition of Elm? Mechanisation: the module step (plan step 10), fifth part: the walk
  over the declarations of two module derivations that are instances of each other.

  Given a bijection σ of type names that agrees with the instance's bijection ν on the generated
  names and fixes the other names of the first derivation's environments that the second does not
  generate, each declaration of the second derivation gives σ of what the first's gives: a value
  group by the renaming of MutualModule.lean (its closure is closed, so only its type names move,
  and the renaming back undoes ν on them), a type declaration by uniqueness, a port by the
  independence of the sorts of its variables.
-/
import StandardElmMech.Stat.ModuleStepPorts

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

namespace Walk

/-! ## Renamings of type names -/

theorem nr_tn_eq (ρ : List (TyName × TyName)) (t : TyName) : (nr ρ).tnApply t = renameName ρ t :=
  (renameName_eq ρ t).symm

theorem renameName_not_mem {ρ : List (TyName × TyName)} {t : TyName} (h : t ∉ ρ.map (·.1)) : renameName ρ t = t := by
  rw [renameName_eq, Swap.lookup_none h]; rfl

theorem renameName_mem : ∀ {ρ : List (TyName × TyName)} {t : TyName}, t ∈ ρ.map (·.1) → renameName ρ t ∈ ρ.map (·.2)
  | [], _, h => by simp at h
  | (a, b) :: rest, t, h => by
    rw [renameName_eq]
    simp only [List.lookup]
    by_cases e : t = a
    · subst e; simp
    · have hb : (t == a) = false := beq_eq_false_iff_ne.mpr e
      rw [hb]
      simp only [List.map_cons, List.mem_cons, e, false_or] at h
      have := renameName_mem h
      rw [renameName_eq] at this
      exact List.mem_cons_of_mem _ this

theorem renameName_of_mem {ρ : List (TyName × TyName)} (hn : (ρ.map (·.1)).Nodup) {p : TyName × TyName} (hp : p ∈ ρ) :
    renameName ρ p.1 = p.2 := by
  rw [renameName_eq, Swap.lookup_of_mem hn hp]; rfl

mutual
theorem ren_bnd {r : Renaming} (hr : r.WF) : (τ : Ty) → (∀ v ∈ τ.vars, v.isBnd = true) → r.ty τ = (nr r.tn).ty τ
  | .var a, h => by
    have := h (.ty a) (by simp [Ty.vars])
    cases a with
    | bnd i c => simp [Renaming.ty, hr.tv_bnd]
    | named _ | fresh _ _ => simp [BVar.isBnd] at this
  | .record ρ none, h => by
    simp only [Renaming.ty, ren_bndRow hr ρ (by simpa [Ty.vars] using h)] <;> try rfl
  | .record ρ (some e), h => by
    have he := h (.row e) (by simp [Ty.vars])
    simp only [Renaming.ty, ren_bndRow hr ρ (fun v hv => h v (by simp [Ty.vars, hv]))]
    cases e with
    | bnd i => simp [hr.rv_bnd]
    | named _ | fresh _ => simp [BVar.isBnd] at he
  | .fn a b, h => by
    simp only [Renaming.ty, ren_bnd hr a (fun v hv => h v (by simp [Ty.vars, hv])),
      ren_bnd hr b (fun v hv => h v (by simp [Ty.vars, hv]))] <;> try rfl
  | .con as t, h => by
    simp only [Renaming.ty, ren_bndList hr as (by simpa [Ty.vars] using h)] <;> try rfl
theorem ren_bndRow {r : Renaming} (hr : r.WF) : (ρ : Row) → (∀ v ∈ Ty.rowVars ρ, v.isBnd = true) → r.row ρ = (nr r.tn).row ρ
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [Renaming.row, ren_bnd hr τ (fun v hv => h v (by simp [Ty.rowVars, hv])),
      ren_bndRow hr rest (fun v hv => h v (by simp [Ty.rowVars, hv]))]
theorem ren_bndList {r : Renaming} (hr : r.WF) : (l : List Ty) → (∀ v ∈ Ty.listVars l, v.isBnd = true) → r.tys l = (nr r.tn).tys l
  | [], _ => rfl
  | τ :: rest, h => by
    simp only [Renaming.tys, ren_bnd hr τ (fun v hv => h v (by simp [Ty.listVars, hv])),
      ren_bndList hr rest (fun v hv => h v (by simp [Ty.listVars, hv]))]
end

mutual
theorem nr_congr {a b : List (TyName × TyName)} : (τ : Ty) → (∀ t ∈ τ.tynames, (nr a).tnApply t = (nr b).tnApply t) →
    (nr a).ty τ = (nr b).ty τ
  | .var _, _ => rfl
  | .record ρ tl, h => by simp only [Renaming.ty, nr_congrRow ρ (by simpa [Ty.tynames] using h)]; rfl
  | .fn x y, h => by
    simp only [Renaming.ty, nr_congr x (fun t ht => h t (by simp [Ty.tynames, ht])),
      nr_congr y (fun t ht => h t (by simp [Ty.tynames, ht]))]
  | .con as t, h => by
    simp only [Renaming.ty, nr_congrList as (fun u hu => h u (by simp [Ty.tynames, hu])),
      h t (by simp [Ty.tynames])]
theorem nr_congrRow {a b : List (TyName × TyName)} : (ρ : Row) → (∀ t ∈ Ty.rowTynames ρ, (nr a).tnApply t = (nr b).tnApply t) →
    (nr a).row ρ = (nr b).row ρ
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [Renaming.row, nr_congr τ (fun t ht => h t (by simp [Ty.rowTynames, ht])),
      nr_congrRow rest (fun t ht => h t (by simp [Ty.rowTynames, ht]))]
theorem nr_congrList {a b : List (TyName × TyName)} : (l : List Ty) → (∀ t ∈ Ty.listTynames l, (nr a).tnApply t = (nr b).tnApply t) →
    (nr a).tys l = (nr b).tys l
  | [], _ => rfl
  | τ :: rest, h => by
    simp only [Renaming.tys, nr_congr τ (fun t ht => h t (by simp [Ty.listTynames, ht])),
      nr_congrList rest (fun t ht => h t (by simp [Ty.listTynames, ht]))]
end

theorem nr_fix_ty {a : List (TyName × TyName)} (τ : Ty) (h : ∀ t ∈ τ.tynames, (nr a).tnApply t = t) : (nr a).ty τ = τ := by
  rw [nr_congr (b := []) τ (fun t ht => h t ht), nr_nil_ty]

theorem nr_fix_valEnv {a : List (TyName × TyName)} (VE : ValEnv) (h : ∀ t ∈ ValEnv.tynames VE, (nr a).tnApply t = t) :
    (nr a).valEnv VE = VE := by
  rw [nr_valEnv_eq]
  conv => rhs; rw [← List.map_id VE]
  apply List.map_congr_left
  intro p hp
  simp only [Renaming.scheme, nr_bvar_fun, List.map_id', id]
  rw [nr_fix_ty _ fun t ht => h t (List.mem_flatMap.mpr ⟨p, hp, ht⟩)]

theorem nr_fix_tyEnv {a : List (TyName × TyName)} (TE : TyEnv) (h : ∀ t ∈ TyEnv.tynames TE, (nr a).tnApply t = t) :
    (nr a).tyEnv TE = TE := by
  rw [nr_tyEnv_eq]
  conv => rhs; rw [← List.map_id TE]
  apply List.map_congr_left
  intro p hp
  have hp' : ∀ t ∈ p.2.1.body.tynames ++ ValEnv.tynames p.2.2, (nr a).tnApply t = t :=
    fun t ht => h t (List.mem_flatMap.mpr ⟨p, hp, ht⟩)
  simp only [Renaming.tyFcn, nr_bvar_fun, List.map_id', id]
  rw [nr_fix_ty _ fun t ht => hp' t (List.mem_append_left _ ht),
    nr_fix_valEnv _ fun t ht => hp' t (List.mem_append_right _ ht)]

theorem nr_fix_iEnv {a : List (TyName × TyName)} (I : IEnv) (h : ∀ t ∈ I.tynames, (nr a).tnApply t = t) :
    (nr a).iEnv I = I := by
  simp only [IEnv.tynames, List.mem_append] at h
  simp only [Renaming.iEnv, nr_fix_tyEnv _ fun t ht => h t (.inl ht), nr_fix_valEnv _ fun t ht => h t (.inr ht)]

/-- A bijection of type names that fixes the names of a basis fixes the basis. -/
theorem nr_fix_basis {a : List (TyName × TyName)} {B : SBasis} (hB : BasisInv B) (h : ∀ t ∈ B.T, (nr a).tnApply t = t) :
    (nr a).basis B = B := by
  obtain ⟨T, ME, PE⟩ := B
  simp only [Renaming.basis, Renaming.portEnv, SBasis.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · conv => rhs; rw [← List.map_id T]
    exact List.map_congr_left fun t ht => h t ht
  · conv => rhs; rw [← List.map_id ME]
    exact List.map_congr_left fun p hp => by
      simp only [id, nr_fix_iEnv p.2 fun t ht => h t (hB.names p hp t ht)]
  · conv => rhs; rw [← List.map_id PE]
    exact List.map_congr_left fun p hp => by
      simp only [id, nr_fix_ty p.2.2 fun t ht => h t (hB.pe p hp t ht)]

theorem map_eq_self {α : Type} {f : α → α} : ∀ {l : List α}, l.map f = l → ∀ x ∈ l, f x = x
  | [], _, _, hx => by simp at hx
  | y :: ys, h, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact map_eq_self h.2 x hx

/-! ## Closures of value groups -/

theorem closGroup_bnd (VE : ValEnv) :
    ∀ p ∈ closGroup [] VE, (∀ v ∈ p.2.1.bound, v.isBnd = true) ∧ ∀ v ∈ p.2.1.body.vars, v.isBnd = true := by
  intro p hp
  have hc := Closed.closGroup_closed VE p hp
  have hb : ∀ v ∈ p.2.1.bound, v.isBnd = true := by
    simp only [closGroup, FMap.mapV, List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    intro v hv
    simp only [Scheme.canon] at hv
    exact renumber_isBnd _ _ _ v hv
  refine ⟨hb, fun v hv => ?_⟩
  cases e : v.isBnd with
  | true => rfl
  | false =>
    have : v ∈ p.2.1.tyvars := mem_diffL.mpr ⟨Closed.mem_tyvars_of hv e, fun hm => by rw [hb v hm] at e; cases e⟩
    rw [hc] at this; cases this

/-- The closure of a renamed group is the closure renamed, and only its type names move. -/
theorem closGroup_ren {r : Renaming} (hr : r.WF) (VE : ValEnv) :
    closGroup [] (r.valEnv VE) = (nr r.tn).valEnv (closGroup [] VE) := by
  rw [closGroup_rename hr (D := fun _ => True) (A := []) (A' := []) (fun _ _ => by simp) VE (fun _ _ _ _ => trivial)]
  simp only [Renaming.valEnv]
  apply List.map_congr_left
  intro p hp
  obtain ⟨hb, hv⟩ := closGroup_bnd VE p hp
  simp only [Renaming.scheme, Prod.mk.injEq, and_true, true_and, Scheme.mk.injEq, nr_bvar_fun, List.map_id']
  refine ⟨?_, ren_bnd hr _ hv⟩
  conv => rhs; rw [← List.map_id p.2.1.bound]
  exact List.map_congr_left fun v hm => hr.bvar_of_isBnd v (hb v hm)

theorem closGroup_nr_bnd (ρ : List (TyName × TyName)) (VE : ValEnv) :
    ∀ p ∈ (nr ρ).valEnv (closGroup [] VE), ∀ v ∈ p.2.1.body.vars, v.isBnd = true := by
  intro p hp v hv
  simp only [nr_valEnv_eq, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [Renaming.scheme, nr_vars] at hv
  exact (closGroup_bnd VE q hq).2 v hv

/-! ## Declarations and their names -/

/-- The type names of the environments of a top-level declaration's parts. -/
def declNames (C : Ctx) : ATopDec → List TyName
  | .seq a b =>
    match checkTopDec C a with
    | some (E1, _) => declNames C a ++ declNames (C.oplusE E1) b
    | none => []
  | .value VE vb => match checkTopDec C (.value VE vb) with | some (E, _) => E.tynames | none => []
  | .types TE VE db tbs => match checkTopDec C (.types TE VE db tbs) with | some (E, _) => E.tynames | none => []
  | .port x ty U => match checkTopDec C (.port x ty U) with | some (E, _) => E.tynames | none => []

/-- What the walk keeps of a declaration's result. -/
def Good (E : Env) (PE : PortEnv) : Prop :=
  E.tyvars = [] ∧ (∀ p ∈ E.TE, ∀ q ∈ p.2.2, q.2.1.tyvars = []) ∧ ∀ p ∈ PE, portB p.2.2 = true

/-- The facts the walk reads. -/
structure Hyps (G G2 : List TyName) (S S' : Subst) (ν ν' : List (TyName × TyName)) (r r' : Renaming)
    (D D' : BVar → Prop) (σ : List (TyName × TyName)) : Prop where
  hw : WalkHyp S S' ν r D
  hw' : WalkHyp S' S ν' r' D'
  rtn : r.tn = ν
  rtn' : r'.tn = ν'
  hσ : NR σ
  pν : ∀ t ∈ G, (nr σ).tnApply t = renameName ν t
  bij : Bijective ν G G2
  bij' : Bijective ν' G2 G

section
variable {G G2 : List TyName} {S S' : Subst} {ν ν' : List (TyName × TyName)} {r r' : Renaming}
  {D D' : BVar → Prop} {σ : List (TyName × TyName)}

/-- A value group: the closure of the second is σ of the first's. -/
theorem value_step (H : Hyps G G2 S S' ν ν' r r' D D' σ) {VE VE2 : ValEnv}
    (e1 : VE2 = r.valEnv VE) (e2 : VE = r'.valEnv VE2)
    (hX : ∀ t ∈ ValEnv.tynames (closGroup [] VE), t ∉ G → t ∉ G2 → (nr σ).tnApply t = t) :
    closGroup [] VE2 = (nr σ).valEnv (closGroup [] VE) := by
  have hw := H.hw.wf
  have hw' := H.hw'.wf
  have k1 : closGroup [] VE2 = (nr ν).valEnv (closGroup [] VE) := by rw [e1, closGroup_ren hw, H.rtn]
  have k2 : closGroup [] VE = (nr ν').valEnv ((nr ν).valEnv (closGroup [] VE)) := by
    conv => lhs; rw [e2]
    rw [closGroup_ren hw', H.rtn', k1]
  rw [k1]
  apply List.map_congr_left
  intro p hp
  have hp2 : p.2.1.body = (nr ν').ty ((nr ν).ty p.2.1.body) := by
    have k3 := k2.symm
    rw [nr_valEnv_eq, nr_valEnv_eq, List.map_map] at k3
    have := map_eq_self k3 p hp
    simp only [Function.comp_apply] at this
    exact congrArg (fun q => q.2.1.body) this.symm
  have hnames : ∀ t ∈ p.2.1.body.tynames, renameName ν' (renameName ν t) = t := by
    have := congrArg Ty.tynames hp2
    rw [nr_tynames, nr_tynames, List.map_map] at this
    intro t ht
    have := map_eq_self this.symm t ht
    simpa [nr_tn_eq] using this
  simp only [Renaming.scheme, Prod.mk.injEq, and_true, nr_bvar_fun, true_and, Scheme.mk.injEq]
  apply nr_congr
  intro t ht
  have htX : t ∈ ValEnv.tynames (closGroup [] VE) := List.mem_flatMap.mpr ⟨p, hp, ht⟩
  by_cases hG : t ∈ G
  · rw [nr_tn_eq, H.pν t hG]
  · have h1 : renameName ν t = t := renameName_not_mem fun hm => hG ((H.bij.1 t).mp hm)
    have h2 := hnames t ht
    rw [h1] at h2
    have hG2 : t ∉ G2 := fun hm => by
      have hm' : t ∈ ν'.map (·.1) := (H.bij'.1 t).mpr hm
      have := renameName_mem hm'
      rw [h2] at this
      exact hG ((H.bij'.2.1 t).mp this)
    rw [nr_tn_eq ν, h1, hX t htX hG hG2]

end

theorem mem_unionL_left {α : Type} [DecidableEq α] {x : α} {A B : List α} (h : x ∈ A) : x ∈ unionL A B :=
  List.mem_append_left _ h

/-- The instance's bijection keeps the arity of every custom type's name. -/
theorem arity_walk {S : Subst} {ν : List (TyName × TyName)} : ∀ (d d2 : ATopDec) (C C2 : Ctx) (path : List Nat),
    d2.erase = d.erase → (checkTopDec C d).isSome → (checkTopDec C2 d2).isSome → topTypesOrdered d.erase = true →
    (∀ n ∈ nodesTopDec C path d, ∀ n2 ∈ nodesTopDec C2 path d2, n.path = n2.path → NodeInstance S (n.renameNames ν) n2) →
    ∀ t ∈ d.custNames, (renameName ν t).arity = t.arity
  | .value _ _, _, _, _, _, _, _, _, _, _, t, ht => by simp [ATopDec.custNames] at ht
  | .port _ _ _, _, _, _, _, _, _, _, _, _, t, ht => by simp [ATopDec.custNames] at ht
  | .types TE VE db tbs, d2, C, C2, path, he, hc, hc2, ho, h, t, ht => by
    cases d2 with
    | types TE2 VE2 db2 tbs2 =>
      simp only [ATopDec.erase, Src.BTopDec.types.injEq] at he
      obtain ⟨h1, h2⟩ := he
      subst db2; subst tbs2
      simp only [checkTopDec] at hc hc2
      have hct : checkTypes C TE VE db tbs = true := by
        cases e : checkTypes C TE VE db tbs <;> simp_all
      have hct2 : checkTypes C2 TE2 VE2 db tbs = true := by
        cases e : checkTypes C2 TE2 VE2 db tbs <;> simp_all
      simp only [ATopDec.erase, topTypesOrdered] at ho
      have hni := h ⟨path, C.U, TE.map (·.2.1.body), veSchemes VE⟩ (by simp [nodesTopDec])
        ⟨path, C2.U, TE2.map (·.2.1.body), veSchemes VE2⟩ (by simp [nodesTopDec]) rfl
      cases db with
      | none => simp [ATopDec.custNames] at ht
      | some dd =>
        simp only [ATopDec.custNames, Option.getD_some, List.mem_filterMap] at ht
        obtain ⟨e, he, ht⟩ := ht
        have hnd : (dd.map (·.1)).Nodup := by
          have := (Types.typesOrdered_dec ho).1
          exact (List.nodup_append.mp this).1
        obtain ⟨t', ht', -, har, -⟩ := Types.custom_corr hct hct2 hnd hni.2.1 e he
        rw [ht] at ht'; cases ht'
        exact har
    | value _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at he
  | .seq a b, d2, C, C2, path, he, hc, hc2, ho, h, t, ht => by
    cases d2 with
    | seq a2 b2 =>
      simp only [ATopDec.erase, Src.BTopDec.seq.injEq] at he
      simp only [ATopDec.erase, topTypesOrdered, Bool.and_eq_true] at ho
      simp only [checkTopDec] at hc hc2
      cases hca : checkTopDec C a with
      | none => rw [hca] at hc; cases hc
      | some p1 =>
        cases hca2 : checkTopDec C2 a2 with
        | none => rw [hca2] at hc2; cases hc2
        | some p2 =>
          rw [hca] at hc; rw [hca2] at hc2
          simp only at hc hc2
          have hcb : (checkTopDec (C.oplusE p1.1) b).isSome := by
            cases e : checkTopDec (C.oplusE p1.1) b <;> rw [e] at hc <;> simp_all
          have hcb2 : (checkTopDec (C2.oplusE p2.1) b2).isSome := by
            cases e : checkTopDec (C2.oplusE p2.1) b2 <;> rw [e] at hc2 <;> simp_all
          simp only [nodesTopDec, hca, hca2] at h
          simp only [ATopDec.custNames, List.mem_append] at ht
          rcases ht with ht | ht
          · exact arity_walk a a2 C C2 (path ++ [0]) he.1 (by rw [hca]; rfl) (by rw [hca2]; rfl) ho.1
              (fun n hn n2 hn2 e => h n (by simp [hn]) n2 (by simp [hn2]) e) t ht
          · exact arity_walk b b2 _ _ (path ++ [1]) he.2 hcb hcb2 ho.2
              (fun n hn n2 hn2 e => h n (by simp [hn]) n2 (by simp [hn2]) e) t ht
    | value _ _ | types _ _ _ _ | port _ _ _ => simp [ATopDec.erase] at he

section
variable {G G2 : List TyName} {S S' : Subst} {ν ν' : List (TyName × TyName)} {r r' : Renaming}
  {D D' : BVar → Prop} {σ : List (TyName × TyName)}

theorem env_tynames_ofVE (VE : ValEnv) : (Env.ofVE VE).tynames = ValEnv.tynames VE := by
  simp [Env.tynames, Env.ofVE, TyEnv.tynames]

/-- The walk: each declaration of the second derivation gives σ of what the first's gives. -/
theorem walk (H : Hyps G G2 S S' ν ν' r r' D D' σ) {BT : List TyName} :
    ∀ (d d2 : ATopDec) (C1 C2 : Ctx) (path : List Nat) (E : Env) (PE : PortEnv),
    d2.erase = d.erase → checkTopDec C1 d = some (E, PE) → (checkTopDec C2 d2).isSome →
    C2 = (nr σ).ctx C1 → C1.tyvars = [] → C1.U = [] → (∀ t ∈ BT, t ∈ C1.T) →
    (∀ t ∈ d.custNames, t ∉ BT → t ∈ G) →
    (∀ t ∈ declNames C1 d, t ∉ G → t ∉ G2 → (nr σ).tnApply t = t) →
    topTypesOrdered d.erase = true → d.NoFreeBnd → d2.NoFreeBnd →
    TopHyp S S' ν ν' D (nodesTopDec C1 path d) (nodesTopDec C2 path d2) →
    TopHyp S' S ν' ν D' (nodesTopDec C2 path d2) (nodesTopDec C1 path d) →
    checkTopDec C2 d2 = some ((nr σ).env E, (nr σ).portEnv PE) ∧ Good E PE
  | .value VE vb, d2, C1, C2, path, E, PE, he, hc, hc2, hC, hcl, hU, hT, hcu, hX, ho, hn, hn2, h, h' => by
    cases d2 with
    | value VE2 vb2 =>
      simp only [ATopDec.erase, Src.BTopDec.value.injEq] at he
      have hX' : ∀ t ∈ declNames C1 (.value VE vb), t ∉ G → t ∉ G2 → (nr σ).tnApply t = t := hX
      simp only [checkTopDec] at hc hc2
      split at hc
      · rename_i hcv0
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        split at hc2
        · rename_i hcv20
          have hcv := hcv0
          have hcv2 := hcv20
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcv hcv2
          simp only [nodesTopDec, List.cons_append, List.singleton_append] at h h'
          have h3 := (h.mono (ms := nodesValBind (C1.plusVE VE) (path ++ [0]) vb)
            (ms'' := nodesValBind (C2.plusVE VE2) (path ++ [0]) vb2)
            (fun n hm => by simp [hm]) (fun n hm => by simp [hm])).rel3
            (fun n hm τ hτ v hv => hn _ _ n hm τ hτ v hv) (fun n hm τ hτ v hv => hn2 _ _ n hm τ hτ v hv)
          have h3' := (h'.mono (ms := nodesValBind (C2.plusVE VE2) (path ++ [0]) vb2)
            (ms'' := nodesValBind (C1.plusVE VE) (path ++ [0]) vb)
            (fun n hm => by simp [hm]) (fun n hm => by simp [hm])).rel3
            (fun n hm τ hτ v hv => hn2 _ _ n hm τ hτ v hv) (fun n hm τ hτ v hv => hn _ _ n hm τ hτ v hv)
          have hvb := walkValBind H.hw vb vb2 _ _ _ he hcv.1 hcv2.1 h3
          have hvb' := walkValBind H.hw' vb2 vb _ _ _ he.symm hcv2.1 hcv.1 h3'
          have e1 : VE2 = r.valEnv VE := by rw [← hcv2.2, (RValBind.ve_rename H.hw.wf vb hvb).1, hcv.2]
          have e2 : VE = r'.valEnv VE2 := by rw [← hcv.2, (RValBind.ve_rename H.hw'.wf vb2 hvb').1, hcv2.2]
          have hcl2 : C2.tyvars = [] := by rw [hC, nr_ctx_tyvars H.hσ, hcl]
          have hXv : ∀ t ∈ ValEnv.tynames (closGroup [] VE), t ∉ G → t ∉ G2 → (nr σ).tnApply t = t := by
            intro t ht
            apply hX' t
            simp only [declNames, checkTopDec, hcv0, ↓reduceIte, env_tynames_ofVE, hcl]
            exact ht
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [checkTopDec, hcv20, ↓reduceIte, hcl2]
            rw [value_step H e1 e2 hXv, hcl]; rfl
          · rw [hcl]
            exact Closed.env_tyvars_nil.mpr ⟨rfl, rfl, Closed.valEnv_closed (Closed.closGroup_closed VE)⟩
          · intro p hp; simp [Env.ofVE] at hp
          · intro p hp; simp at hp
        · cases hc2
      · cases hc
    | types _ _ _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at he
  | .types TE VE db tbs, d2, C1, C2, path, E, PE, he, hc, hc2, hC, hcl, hU, hT, hcu, hX, ho, hn, hn2, h, h' => by
    cases d2 with
    | types TE2 VE2 db2 tbs2 =>
      simp only [ATopDec.erase, Src.BTopDec.types.injEq] at he
      obtain ⟨h1, h2⟩ := he
      subst db2; subst tbs2
      simp only [checkTopDec] at hc hc2
      split at hc
      · rename_i hct
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        split at hc2
        · rename_i hct2
          simp only [ATopDec.erase, topTypesOrdered] at ho
          have hcl2 : C2.tyvars = [] := by rw [hC, nr_ctx_tyvars H.hσ, hcl]
          have hσct : checkTypes C2 ((nr σ).tyEnv TE) ((nr σ).valEnv VE) db tbs = true := by
            rw [hC, nr_checkTypes H.hσ]; exact hct
          have hni := h.ni ⟨path, C1.U, TE.map (·.2.1.body), veSchemes VE⟩ (by simp [nodesTopDec])
            ⟨path, C2.U, TE2.map (·.2.1.body), veSchemes VE2⟩ (by simp [nodesTopDec]) rfl
          have hnames : ∀ e ∈ db.getD [], namesOf ((nr σ).tyEnv TE) e.1 = namesOf TE2 e.1 := by
            cases db with
            | none => simp
            | some dd =>
              intro e he
              have hnd : (dd.map (·.1)).Nodup := (List.nodup_append.mp (Types.typesOrdered_dec ho).1).1
              obtain ⟨t, ht, ht2, -, hnew⟩ := Types.custom_corr hct hct2 hnd hni.2.1 e he
              have htG : t ∈ G := hcu t (by
                simp only [ATopDec.custNames, Option.getD_some, List.mem_filterMap]; exact ⟨e, he, ht⟩)
                (fun hm => hnew (hT t hm))
              rw [nr_namesOf H.hσ, ht, ht2, Option.map_some, H.pν t htG]
          obtain ⟨eT, eV⟩ := Types.checkTypes_unique hcl2 hσct hct2 ho hnames
          refine ⟨?_, (Types.types_closed hcl hct).1, (Types.types_closed hcl hct).2, fun p hp => by simp at hp⟩
          rw [← eT, ← eV]
          simp only [checkTopDec, hσct, ↓reduceIte]; rfl
        · cases hc2
      · cases hc
    | value _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at he
  | .port x ty U, d2, C1, C2, path, E, PE, he, hc, hc2, hC, hcl, hU, hT, hcu, hX, ho, hn, hn2, h, h' => by
    cases d2 with
    | port x2 ty2 U2 =>
      simp only [ATopDec.erase, Src.BTopDec.port.injEq] at he
      obtain ⟨h1, h2⟩ := he
      subst x2; subst ty2
      simp only [checkTopDec] at hc hc2 ⊢
      obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.mp hc2
      have k := nr_elabPort H.hσ C1 x ty U
      rw [hc, ← hC] at k
      simp only [Option.map_some] at k
      refine ⟨by rw [hr2, Ports.elabPort_unique k hr2], ?_⟩
      obtain ⟨τ', α, t, -, c⟩ := Ports.elabPort_cases hc
      rcases c with ⟨-, hp, hr⟩ | ⟨-, τ'', -, -, hp, hr⟩
      · simp only [Ports.outRes, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        refine ⟨?_, fun p hp => by simp [Env.ofVE] at hp, fun p hq => by simp at hq; subst hq; exact hp⟩
        rw [hcl]
        exact Closed.env_tyvars_nil.mpr ⟨rfl, rfl, Closed.valEnv_closed fun q hq => by
          simp [Env.ofVE] at hq; subst hq; exact Closed.closScheme_closed _⟩
      · simp only [Ports.inRes, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        refine ⟨?_, fun p hp => by simp [Env.ofVE] at hp, fun p hq => by simp at hq; subst hq; exact hp⟩
        rw [hcl]
        exact Closed.env_tyvars_nil.mpr ⟨rfl, rfl, Closed.valEnv_closed fun q hq => by
          simp [Env.ofVE] at hq; subst hq; exact Closed.closScheme_closed _⟩
    | value _ _ | types _ _ _ _ | seq _ _ => simp [ATopDec.erase] at he
  | .seq a b, d2, C1, C2, path, E, PE, he, hc, hc2, hC, hcl, hU, hT, hcu, hX, ho, hn, hn2, h, h' => by
    cases d2 with
    | seq a2 b2 =>
      simp only [ATopDec.erase, Src.BTopDec.seq.injEq] at he
      obtain ⟨hea, heb⟩ := he
      simp only [ATopDec.erase, topTypesOrdered, Bool.and_eq_true] at ho
      simp only [ATopDec.custNames, List.mem_append] at hcu
      have hX' : ∀ t ∈ declNames C1 (.seq a b), t ∉ G → t ∉ G2 → (nr σ).tnApply t = t := hX
      simp only [checkTopDec] at hc hc2
      cases hca : checkTopDec C1 a with
      | none => rw [hca] at hc; cases hc
      | some p1 =>
        obtain ⟨E1, PE1⟩ := p1
        rw [hca] at hc; simp only at hc
        cases hcb : checkTopDec (C1.oplusE E1) b with
        | none => rw [hcb] at hc; cases hc
        | some p2 =>
          obtain ⟨E2, PE2⟩ := p2
          rw [hcb] at hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          simp only [declNames, hca, List.mem_append] at hX'
          obtain ⟨q1, hq1⟩ : ∃ q1, checkTopDec C2 a2 = some q1 := by
            cases e : checkTopDec C2 a2 with
            | none => rw [e] at hc2; cases hc2
            | some q => exact ⟨q, rfl⟩
          have hm1 : ∀ n ∈ nodesTopDec C1 (path ++ [0]) a, n ∈ nodesTopDec C1 path (.seq a b) := by
            intro n hn; simp [nodesTopDec, hca, hn]
          have hm2 : ∀ n ∈ nodesTopDec C2 (path ++ [0]) a2, n ∈ nodesTopDec C2 path (.seq a2 b2) := by
            intro n hn; simp [nodesTopDec, hq1, hn]
          obtain ⟨ka, ga⟩ := walk H a a2 C1 C2 (path ++ [0]) E1 PE1 hea hca (by rw [hq1]; rfl) hC hcl hU hT
            (fun t ht => hcu t (.inl ht)) (fun t ht => hX' t (.inl ht)) ho.1 hn.1 hn2.1
            (h.mono hm1 hm2) (h'.mono hm2 hm1)
          rw [hq1] at ka
          cases ka
          rw [hq1] at hc2
          simp only at hc2
          have hcb2 : (checkTopDec (C2.oplusE ((nr σ).env E1)) b2).isSome := by
            cases e : checkTopDec (C2.oplusE ((nr σ).env E1)) b2 <;> rw [e] at hc2 <;> simp_all
          have hC' : C2.oplusE ((nr σ).env E1) = (nr σ).ctx (C1.oplusE E1) := by rw [hC, nr_oplusE H.hσ]
          have hm1' : ∀ n ∈ nodesTopDec (C1.oplusE E1) (path ++ [1]) b, n ∈ nodesTopDec C1 path (.seq a b) := by
            intro n hn; simp [nodesTopDec, hca, hn]
          have hm2' : ∀ n ∈ nodesTopDec (C2.oplusE ((nr σ).env E1)) (path ++ [1]) b2, n ∈ nodesTopDec C2 path (.seq a2 b2) := by
            intro n hn; simp [nodesTopDec, hq1, hn]
          obtain ⟨kb, gb⟩ := walk H b b2 (C1.oplusE E1) _ (path ++ [1]) E2 PE2 heb hcb hcb2 hC'
            (Closed.oplusE_closed hcl ga.1) (by simp [Ctx.oplusE, hU]) (fun t ht => mem_unionL_left (hT t ht))
            (fun t ht => hcu t (.inr ht)) (fun t ht => hX' t (.inr ht)) ho.2 hn.2 hn2.2
            (h.mono hm1' hm2') (h'.mono hm2' hm1')
          refine ⟨?_, Closed.plus_closed ga.1 gb.1, ?_, ?_⟩
          · simp only [checkTopDec, hq1, kb, nr_env_plus, nr_plusPE]
          · intro p hp q hq
            rcases Closed.mem_modify hp with hp | hp
            · exact gb.2.1 p hp q hq
            · exact ga.2.1 p hp q hq
          · intro p hp
            rcases Closed.mem_modify hp with hp | hp
            · exact gb.2.2 p hp
            · exact ga.2.2 p hp
    | value _ _ | types _ _ _ _ | port _ _ _ => simp [ATopDec.erase] at he

end

end Walk

end StandardElm.Stat
