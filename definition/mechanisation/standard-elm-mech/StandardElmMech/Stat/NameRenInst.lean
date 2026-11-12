/-
  A Standard Definition of Elm? Mechanisation: instances of module derivations are carried across a
  bijective renaming of type names (plan step 10, transport across bases, fifth layer).

  `NRInv ρ ρ'`: `nr ρ` and `nr ρ'` are renamings of type names inverse to each other. Then a
  renamed basis renamed back is the basis, a renamed derivation renamed back is the derivation,
  `Gen` is invariant, `NoFreeBnd` is kept, and an instance of a derivation in B is, renamed, an
  instance of the renamed derivation in the renamed basis (`instanceOfMod_nr`).
-/
import StandardElmMech.Stat.NameRenResult

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-- Two renamings of type names, inverse to each other. -/
structure NRInv (ρ ρ' : List (TyName × TyName)) : Prop where
  h : NR ρ
  h' : NR ρ'
  left : ∀ t, (nr ρ').tnApply ((nr ρ).tnApply t) = t
  right : ∀ t, (nr ρ).tnApply ((nr ρ').tnApply t) = t

theorem NRInv.symm {ρ ρ' : List (TyName × TyName)} (h : NRInv ρ ρ') : NRInv ρ' ρ := ⟨h.h', h.h, h.right, h.left⟩

section
variable {a b c d : List (TyName × TyName)}

/-! ## Composition of renamings of type names -/

mutual
theorem nr_comp (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply ((nr d).tnApply t)) :
    (τ : Ty) → (nr a).ty ((nr b).ty τ) = (nr c).ty ((nr d).ty τ)
  | .var _ => rfl
  | .record r tl => by simp only [nr_ty_record, nr_comp_row hc r]
  | .fn x y => by simp only [nr_ty_fn, nr_comp hc x, nr_comp hc y]
  | .con as t => by
    have e := nr_comp_list hc as
    simp only [nr_tys, List.map_map] at e
    simp only [nr_ty_con, List.map_map, hc t, e]
theorem nr_comp_row (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply ((nr d).tnApply t)) :
    (r : Row) → (nr a).row ((nr b).row r) = (nr c).row ((nr d).row r)
  | [] => rfl
  | (l, τ) :: rest => by simp only [nr_row_cons, nr_comp hc τ, nr_comp_row hc rest]
theorem nr_comp_list (hc : ∀ t, (nr a).tnApply ((nr b).tnApply t) = (nr c).tnApply ((nr d).tnApply t)) :
    (l : List Ty) → (nr a).tys ((nr b).tys l) = (nr c).tys ((nr d).tys l)
  | [] => rfl
  | τ :: rest => by simp only [Renaming.tys, nr_comp hc τ, nr_comp_list hc rest]
end

theorem nr_nil_ty (τ : Ty) : (nr []).ty τ = τ := Renaming.ty_id τ
@[simp] theorem nr_nil_tn (t : TyName) : (nr []).tnApply t = t := rfl

theorem nr_inv_ty (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (τ : Ty) : (nr b).ty ((nr a).ty τ) = τ := by
  rw [nr_comp (c := []) (d := []) (by simpa using hl), nr_nil_ty, nr_nil_ty]

theorem nr_inv_row (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (r : Row) : (nr b).row ((nr a).row r) = r := by
  simp [nr_row_map, List.map_map, Function.comp_def, nr_inv_ty hl]

theorem nr_inv_scheme (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (σ : Scheme) :
    (nr b).scheme ((nr a).scheme σ) = σ := by
  simp [Renaming.scheme, nr_inv_ty hl]

theorem nr_inv_valEnv (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (VE : ValEnv) :
    (nr b).valEnv ((nr a).valEnv VE) = VE := by
  simp [Renaming.valEnv, List.map_map, Function.comp_def, nr_inv_scheme hl]

theorem nr_inv_tyEnv (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (TE : TyEnv) :
    (nr b).tyEnv ((nr a).tyEnv TE) = TE := by
  simp [Renaming.tyEnv, List.map_map, Function.comp_def, Renaming.tyFcn, nr_inv_ty hl, nr_inv_valEnv hl]

theorem nr_inv_iEnv (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (I : IEnv) :
    (nr b).iEnv ((nr a).iEnv I) = I := by
  simp [Renaming.iEnv, nr_inv_tyEnv hl, nr_inv_valEnv hl]

theorem nr_inv_env (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (E : Env) :
    (nr b).env ((nr a).env E) = E := by
  simp [Renaming.env, List.map_map, Function.comp_def, nr_inv_iEnv hl, nr_inv_tyEnv hl, nr_inv_valEnv hl]

theorem nr_inv_ctx (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (C : Ctx) :
    (nr b).ctx ((nr a).ctx C) = C := by
  simp [Renaming.ctx, List.map_map, Function.comp_def, hl, nr_inv_env hl]

theorem nr_inv_portEnv (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (PE : PortEnv) :
    (nr b).portEnv ((nr a).portEnv PE) = PE := by
  simp [Renaming.portEnv, List.map_map, Function.comp_def, nr_inv_ty hl]

theorem nr_inv_basis (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (B : SBasis) :
    (nr b).basis ((nr a).basis B) = B := by
  simp [Renaming.basis, List.map_map, Function.comp_def, hl, nr_inv_iEnv hl, nr_inv_portEnv hl]

mutual
theorem nr_inv_atPat (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (p : AAtPat) → (nr b).atPat ((nr a).atPat p) = p
  | .wild _ | .scon _ _ | .var _ _ | .nil _ => by simp [Renaming.atPat, nr_inv_ty hl]
  | .con _ _ _ => by simp [Renaming.atPat, nr_inv_ty hl, nr_tys, List.map_map, Function.comp_def]
  | .unit => rfl
  | .tuple p1 p2 p3 => by simp [Renaming.atPat, nr_inv_pat hl p1, nr_inv_pat hl p2, nr_inv_patOpt hl p3]
  | .record row _ => by simp [Renaming.atPat, nr_inv_ty hl, nr_inv_patRowOpt hl row]
  | .paren p => by simp [Renaming.atPat, nr_inv_pat hl p]
theorem nr_inv_patRow (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (r : APatRow) → (nr b).patRow ((nr a).patRow r) = r
  | .field _ _ rest => by simp [Renaming.patRow, nr_inv_ty hl, nr_inv_patRowOpt hl rest]
theorem nr_inv_patRowOpt (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (r : Option APatRow) →
    (nr b).patRowOpt ((nr a).patRowOpt r) = r
  | none => rfl
  | some r => by simp [Renaming.patRowOpt, nr_inv_patRow hl r]
theorem nr_inv_pat (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (p : APat) → (nr b).pat ((nr a).pat p) = p
  | .atpat x => by simp [Renaming.pat, nr_inv_atPat hl x]
  | .con _ _ args _ => by
    simp [Renaming.pat, nr_inv_ty hl, nr_tys, List.map_map, Function.comp_def, nr_inv_atPats hl args]
  | .cons p1 p2 => by simp [Renaming.pat, nr_inv_pat hl p1, nr_inv_pat hl p2]
  | .as p _ => by simp [Renaming.pat, nr_inv_pat hl p]
theorem nr_inv_patOpt (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (p : Option APat) → (nr b).patOpt ((nr a).patOpt p) = p
  | none => rfl
  | some p => by simp [Renaming.patOpt, nr_inv_pat hl p]
theorem nr_inv_atPats (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (ps : List AAtPat) →
    (nr b).atPats ((nr a).atPats ps) = ps
  | [] => rfl
  | p :: ps => by simp [Renaming.atPats, nr_inv_atPat hl p, nr_inv_atPats hl ps]
end

mutual
theorem nr_inv_atExp (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (x : AAtExp) → (nr b).atExp ((nr a).atExp x) = x
  | .scon _ _ | .nil _ => by simp [Renaming.atExp, nr_inv_ty hl]
  | .var _ _ _ | .con _ _ _ | .op _ _ _ => by simp [Renaming.atExp, nr_inv_ty hl, nr_tys, List.map_map, Function.comp_def]
  | .unit => rfl
  | .tuple e1 e2 e3 => by simp [Renaming.atExp, nr_inv_exp hl e1, nr_inv_exp hl e2, nr_inv_expOpt hl e3]
  | .record row => by simp [Renaming.atExp, nr_inv_expRowOpt hl row]
  | .update _ _ _ row => by
    simp [Renaming.atExp, nr_inv_ty hl, nr_tys, List.map_map, Function.comp_def, nr_inv_expRow hl row]
  | .letE d e => by simp [Renaming.atExp, nr_inv_dec hl d, nr_inv_exp hl e]
  | .paren e => by simp [Renaming.atExp, nr_inv_exp hl e]
theorem nr_inv_expRow (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (r : AExpRow) → (nr b).expRow ((nr a).expRow r) = r
  | .field _ e rest => by simp [Renaming.expRow, nr_inv_exp hl e, nr_inv_expRowOpt hl rest]
theorem nr_inv_expRowOpt (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (r : Option AExpRow) →
    (nr b).expRowOpt ((nr a).expRowOpt r) = r
  | none => rfl
  | some r => by simp [Renaming.expRowOpt, nr_inv_expRow hl r]
theorem nr_inv_exp (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (e : AExp) → (nr b).exp ((nr a).exp e) = e
  | .atexp x => by simp [Renaming.exp, nr_inv_atExp hl x]
  | .app e x => by simp [Renaming.exp, nr_inv_exp hl e, nr_inv_atExp hl x]
  | .lam p e => by simp [Renaming.exp, nr_inv_atPat hl p, nr_inv_exp hl e]
  | .caseE e m => by simp [Renaming.exp, nr_inv_exp hl e, nr_inv_match hl m]
theorem nr_inv_expOpt (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (e : Option AExp) → (nr b).expOpt ((nr a).expOpt e) = e
  | none => rfl
  | some e => by simp [Renaming.expOpt, nr_inv_exp hl e]
theorem nr_inv_match (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (m : AMatch) → (nr b).match_ ((nr a).match_ m) = m
  | .mk mr rest => by simp [Renaming.match_, nr_inv_mrule hl mr, nr_inv_matchOpt hl rest]
theorem nr_inv_matchOpt (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (m : Option AMatch) →
    (nr b).matchOpt ((nr a).matchOpt m) = m
  | none => rfl
  | some m => by simp [Renaming.matchOpt, nr_inv_match hl m]
theorem nr_inv_mrule (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (mr : AMRule) → (nr b).mrule ((nr a).mrule mr) = mr
  | .mk p e => by simp [Renaming.mrule, nr_inv_pat hl p, nr_inv_exp hl e]
theorem nr_inv_dec (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (d : ADec) → (nr b).dec ((nr a).dec d) = d
  | .val VE vb => by simp [Renaming.dec, nr_inv_valEnv hl, nr_inv_valBind hl vb]
theorem nr_inv_valBind (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (vb : AValBind) → (nr b).valBind ((nr a).valBind vb) = vb
  | .var _ ann _ e rest => by
    simp [Renaming.valBind, nr_inv_ty hl, nr_ann_eq, nr_inv_exp hl e, nr_inv_valBindOpt hl rest]
  | .pat p e => by simp [Renaming.valBind, nr_inv_atPat hl p, nr_inv_exp hl e]
theorem nr_inv_valBindOpt (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (vb : Option AValBind) →
    (nr b).valBindOpt ((nr a).valBindOpt vb) = vb
  | none => rfl
  | some vb => by simp [Renaming.valBindOpt, nr_inv_valBind hl vb]
end

theorem nr_inv_topDec (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) : (d : ATopDec) → (nr b).topDec ((nr a).topDec d) = d
  | .value VE vb => by simp [Renaming.topDec, nr_inv_valEnv hl, nr_inv_valBind hl vb]
  | .types TE VE _ _ => by simp [Renaming.topDec, nr_inv_valEnv hl, nr_inv_tyEnv hl]
  | .port _ _ U => by simp [Renaming.topDec]
  | .seq a1 a2 => by simp [Renaming.topDec, nr_inv_topDec hl a1, nr_inv_topDec hl a2]

theorem nr_inv_module (hl : ∀ t, (nr b).tnApply ((nr a).tnApply t) = t) (m : AModule) :
    (m.rename (nr a)).rename (nr b) = m := by
  rcases m with ⟨hd, imps, body⟩
  cases body <;> simp [AModule.rename, nr_inv_topDec hl]

/-! ## Instances -/

variable {ρ ρ' : List (TyName × TyName)}

theorem nr_gen (hi : NRInv ρ ρ') (σ : Scheme) (τ : Ty) : Gen ((nr ρ).scheme σ) ((nr ρ).ty τ) ↔ Gen σ τ := by
  have h := hi.h
  constructor
  · rintro ⟨ts, S, hb, hR, ha⟩
    have ets : ts = (ts.map (nr ρ').ty).map (nr ρ).ty := by
      simp [List.map_map, Function.comp_def, nr_inv_ty hi.right]
    rw [nr_scheme_bound, ets, nr_bindSubst] at hb
    cases hb0 : bindSubst σ.bound (ts.map (nr ρ').ty) with
    | none => rw [hb0] at hb; cases hb
    | some S0 =>
      rw [hb0] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      refine ⟨_, S0, hb0, ?_, ?_⟩
      · rw [← Subst.respectsB_iff, ← nr_respectsB h]; exact (Subst.respectsB_iff _).mpr hR
      · rw [nr_scheme_body, nr_apply h] at ha
        cases ha0 : S0.apply σ.body with
        | none => rw [ha0] at ha; cases ha
        | some τ0 =>
          rw [ha0] at ha
          simp only [Option.map_some, Option.some.injEq] at ha
          rw [nr_ty_inj h _ _ ha]
  · rintro ⟨ts, S, hb, hR, ha⟩
    refine ⟨ts.map (nr ρ).ty, (nr ρ).subst S, ?_, ?_, ?_⟩
    · rw [nr_scheme_bound, nr_bindSubst, hb]; rfl
    · rw [← Subst.respectsB_iff, nr_respectsB h]; exact (Subst.respectsB_iff _).mpr hR
    · rw [nr_scheme_body, nr_apply h, ha]; rfl

theorem nr_applyVar (h : NR ρ) (S : Subst) (v : BVar) : ((nr ρ).subst S).applyVar v = S.applyVar v := by
  cases v with
  | ty x =>
    simp only [Subst.applyVar]
    have e := nr_apply h S (.var x)
    simp only [nr_ty_var] at e
    rw [e]
    cases S.apply (.var x) with
    | none => rfl
    | some τ => cases τ <;> simp
  | row e =>
    simp only [Subst.applyVar]
    have e' := nr_apply h S (.record [] (some e))
    simp only [nr_ty_record, nr_row_nil] at e'
    rw [e']
    cases S.apply (.record [] (some e)) with
    | none => rfl
    | some τ => rcases τ with _ | ⟨_ | ⟨⟨l, τ⟩, r⟩, _ | tl⟩ | _ | _ <;> simp

theorem mapM_map_some {α β γ : Type} (f : α → Option β) (k : β → γ) :
    ∀ l : List α, l.mapM (fun x => (f x).map k) = (l.mapM f).map (List.map k)
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, mapM_map_some f k xs]
    cases f x <;> cases xs.mapM f <;> rfl

theorem nr_mapM_apply (h : NR ρ) (S : Subst) (l : List Ty) :
    (l.map (nr ρ).ty).mapM ((nr ρ).subst S).apply = (l.mapM S.apply).map (List.map (nr ρ).ty) := by
  rw [List.mapM_map]
  rw [show (((nr ρ).subst S).apply ∘ (nr ρ).ty) = fun τ => (S.apply τ).map (nr ρ).ty from funext (nr_apply h S)]
  exact mapM_map_some _ _ l

theorem nr_applyScheme (h : NR ρ) (S : Subst) (σ : Scheme) :
    ((nr ρ).subst S).applyScheme ((nr ρ).scheme σ) = (S.applyScheme σ).map (nr ρ).scheme := by
  simp only [Subst.applyScheme, nr_scheme_body, nr_apply h, nr_scheme_bound]
  cases S.apply σ.body <;> simp [Renaming.scheme]

theorem nr_nodeInstance (hi : NRInv ρ ρ') {S : Subst} {n n' : Node} (hn : NodeInstance S n n') :
    NodeInstance ((nr ρ).subst S) (n.renameNames ρ) (n'.renameNames ρ) := by
  have h := hi.h
  obtain ⟨⟨vs, hU, hset⟩, ht, hl, hs⟩ := hn
  rw [node_renameNames, node_renameNames]
  refine ⟨⟨vs, ?_, hset⟩, ?_, by simpa using hl, ?_⟩
  · simp only
    rw [show ((nr ρ).subst S).applyVar = S.applyVar from funext (nr_applyVar h S)]; exact hU
  · simp only; rw [nr_mapM_apply h, ht]; rfl
  · intro i hi1 hi2 τ hg
    simp only [List.getElem_map] at hg ⊢
    rw [← nr_inv_ty hi.right τ, nr_gen hi] at hg
    simp only [List.length_map] at hi1 hi2
    obtain ⟨σS, e1, e2⟩ := hs i hi1 hi2 _ hg
    refine ⟨(nr ρ).scheme σS, by rw [nr_applyScheme h, e1]; rfl, ?_⟩
    rw [← nr_inv_ty hi.right τ, nr_gen hi]; exact e2

theorem lookup_map_both {f : TyName → TyName} (hf : ∀ x y, f x = f y → x = y) :
    ∀ (l : List (TyName × TyName)) (t : TyName),
      (l.map fun p => (f p.1, f p.2)).lookup (f t) = (l.lookup t).map f
  | [], _ => rfl
  | (x, y) :: rest, t => by
    simp only [List.map_cons, List.lookup]
    by_cases e : t = x
    · subst e; simp
    · have e1 : (f t == f x) = false := beq_eq_false_iff_ne.mpr (fun e' => e (hf _ _ e'))
      have e2 : (t == x) = false := beq_eq_false_iff_ne.mpr e
      simp only [e1, e2]
      exact lookup_map_both hf rest t

theorem nr_renameNames_comm (h : NR ρ) (ν : List (TyName × TyName)) (τ : Ty) :
    Ty.renameNames (ν.map fun p => ((nr ρ).tnApply p.1, (nr ρ).tnApply p.2)) ((nr ρ).ty τ) =
      (nr ρ).ty (Ty.renameNames ν τ) := by
  rw [renameNames_nr, renameNames_nr]
  apply nr_comp
  intro t
  show ((ν.map fun p => ((nr ρ).tnApply p.1, (nr ρ).tnApply p.2)).lookup ((nr ρ).tnApply t)).getD
    ((nr ρ).tnApply t) = (nr ρ).tnApply ((ν.lookup t).getD t)
  rw [lookup_map_both h.inj ν t]
  cases ν.lookup t <;> rfl

theorem nr_comm' (h : NR ρ) (ν : List (TyName × TyName)) (τ : Ty) :
    (nr (ν.map fun p => ((nr ρ).tnApply p.1, (nr ρ).tnApply p.2))).ty ((nr ρ).ty τ) = (nr ρ).ty ((nr ν).ty τ) := by
  have := nr_renameNames_comm h ν τ
  rwa [renameNames_nr, renameNames_nr] at this

theorem nr_node_renameNames_comm (h : NR ρ) (ν : List (TyName × TyName)) (n : Node) :
    (n.renameNames ρ).renameNames (ν.map fun p => ((nr ρ).tnApply p.1, (nr ρ).tnApply p.2)) =
      (n.renameNames ν).renameNames ρ := by
  rw [node_renameNames, node_renameNames, node_renameNames, node_renameNames]
  simp only [List.map_map, Node.mk.injEq, true_and]
  constructor
  · apply List.map_congr_left; intro τ _; exact nr_comm' h ν τ
  · apply List.map_congr_left; intro σ _
    simp [Renaming.scheme, nr_comm' h ν]

theorem nr_setEq_map (h : NR ρ) {l l' : List TyName} (e : SetEq l l') :
    SetEq (l.map (nr ρ).tnApply) (l'.map (nr ρ).tnApply) := by
  intro x
  simp only [List.mem_map]
  exact ⟨fun ⟨y, hy, e'⟩ => ⟨y, (e y).mp hy, e'⟩, fun ⟨y, hy, e'⟩ => ⟨y, (e y).mpr hy, e'⟩⟩

theorem nr_bijective (h : NR ρ) {ν : List (TyName × TyName)} {G G' : List TyName} (hb : Bijective ν G G') :
    Bijective (ν.map fun p => ((nr ρ).tnApply p.1, (nr ρ).tnApply p.2)) (G.map (nr ρ).tnApply) (G'.map (nr ρ).tnApply) := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := nr_setEq_map h h1; simpa [List.map_map, Function.comp_def] using this
  · have := nr_setEq_map h h2; simpa [List.map_map, Function.comp_def, List.Nodup] using this
  · have := List.Pairwise.map (R := fun x y : TyName => x ≠ y) (S := fun x y : TyName => x ≠ y) (nr ρ).tnApply (fun x y hxy e => hxy (h.inj x y e)) h3; simpa [List.map_map, Function.comp_def, List.Nodup] using this
  · have := List.Pairwise.map (R := fun x y : TyName => x ≠ y) (S := fun x y : TyName => x ≠ y) (nr ρ).tnApply (fun x y hxy e => hxy (h.inj x y e)) h4; simpa [List.map_map, Function.comp_def, List.Nodup] using this

/-- An instance of a module derivation, renamed, is an instance of the renamed derivation in the
    renamed basis. -/
theorem instanceOfMod_nr (hi : NRInv ρ ρ') {B : SBasis} {a' a : AModule} (hI : InstanceOfMod B a' a) :
    InstanceOfMod ((nr ρ).basis B) (a'.rename (nr ρ)) (a.rename (nr ρ)) := by
  have h := hi.h
  obtain ⟨he, ν, hb, S, hR, hdom, hdef, hni⟩ := hI
  refine ⟨by rw [AModule.erase_rename, AModule.erase_rename, he], ν.map fun p => ((nr ρ).tnApply p.1, (nr ρ).tnApply p.2),
    ?_, (nr ρ).subst S, ?_, ?_, ?_, ?_⟩
  · rw [nr_genNames h, nr_genNames h]; exact nr_bijective h hb
  · rw [← Subst.respectsB_iff, nr_respectsB h]; exact (Subst.respectsB_iff _).mpr hR
  · intro v _; exact List.not_mem_nil
  · intro τ hτ
    rw [nr_nodesModule h] at hτ
    simp only [nrNodes, List.map_map, Function.comp_def, nr_node_renameNames_comm h, List.flatMap_map,
      List.mem_flatMap] at hτ
    obtain ⟨n, hn, hτn⟩ := hτ
    rw [node_renameNames] at hτn
    simp only [List.mem_map] at hτn
    obtain ⟨τ0, hτ0, rfl⟩ := hτn
    rw [nr_apply h]
    have := hdef τ0 (List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hn, hτ0⟩)
    cases e : S.apply τ0 <;> simp_all
  · intro n hn n' hn' ep
    rw [nr_nodesModule h] at hn hn'
    simp only [nrNodes, List.map_map, Function.comp_def, nr_node_renameNames_comm h, List.mem_map] at hn hn'
    obtain ⟨n0, hn0, rfl⟩ := hn
    obtain ⟨n0', hn0', rfl⟩ := hn'
    have ep' : (n0.renameNames ν).path = n0'.path := by
      rw [node_renameNames, node_renameNames] at ep; rw [node_renameNames]; exact ep
    exact nr_nodeInstance hi (hni _ (List.mem_map_of_mem hn0) n0' hn0' ep')

/-! ## Derivations without free `bnd` variables -/

theorem nr_noFreeBnd (hi : NRInv ρ ρ') {a : AModule} (hn : a.NoFreeBnd) : (a.rename (nr ρ)).NoFreeBnd := by
  have h := hi.h
  intro d hd
  rw [nr_rename_body] at hd
  cases hb : a.body with
  | none => rw [hb] at hd; cases hd
  | some d0 =>
    rw [hb] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    have hn0 := hn d0 hb
    clear hb
    induction d0 with
    | value VE vb =>
      intro C path n hnode τ hτ v hv
      rw [show C = (nr ρ).ctx ((nr ρ').ctx C) from (nr_inv_ctx hi.right C).symm, nr_nodesValBind h] at hnode
      simp only [nrNodes, List.mem_map] at hnode
      obtain ⟨n0, hm0, rfl⟩ := hnode
      rw [node_renameNames] at hτ
      simp only [List.mem_map] at hτ
      obtain ⟨τ0, hτ0, rfl⟩ := hτ
      rw [nr_vars] at hv
      exact hn0 _ _ n0 hm0 τ0 hτ0 v hv
    | types => trivial
    | port => trivial
    | seq a1 a2 ih1 ih2 => exact ⟨ih1 hn0.1, ih2 hn0.2⟩

end

end StandardElm.Stat
