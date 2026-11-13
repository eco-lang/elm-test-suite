/-
  A Standard Definition of Elm? Mechanisation: node correspondence for W with records (plan
  step 11, milestone (d), section 9), WNodes.lean and WNodeRel.lean for substitutions of type and
  row variables.

  `NRelD T U0 n n'`: corresponding nodes of W's result and of its image under `T`, both with the
  instance lists left out: the same path and `U`, the types of the image the images of the types,
  and the scheme clause `SchInstD` (WDNodeClos.lean) at each scheme. The schemes of a pattern's
  node are monotypes with canonical images (the types of the derivation's pattern are canonical,
  `cn_atpat_ve`), so their clause is `schInst_mono`. Here: the patterns (`nodesAtPat_relD`).
-/
import StandardElmMech.Stat.Complete.WDNodeClos
import StandardElmMech.Stat.Complete.WDTheorems
import StandardElmMech.Stat.Complete.WPrincipality

namespace StandardElm.Stat.Complete.WDP
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Stat.Complete

/-! ## The relation between corresponding nodes -/

def NRelD (T : RSub) (U0 : List BVar) (n n' : Node) : Prop :=
  n.U = U0 ∧ n'.path = n.path ∧ n'.U = n.U ∧ n'.tys = n.tys.map (rsb T) ∧ n'.schemes.length = n.schemes.length ∧
    ∀ i (h : i < n.schemes.length) (h' : i < n'.schemes.length), SchInstD T n.schemes[i] n'.schemes[i]

/-- Monotypes with canonical images. -/
def MonoCn (T : RSub) (ss : List Scheme) : Prop := ∀ σ ∈ ss, σ.bound = [] ∧ cnB (rsb T σ.body) = true

theorem schInst_monoCn {T : RSub} {σ : Scheme} (hb : σ.bound = []) (hc : cnB (rsb T σ.body) = true) :
    SchInstD T σ (rsbScheme T σ) := by
  obtain ⟨bs, body⟩ := σ
  simp only at hb hc; subst hb
  exact schInst_mono hc

theorem nrelD_mk {T : RSub} {U0 U U' : List BVar} {path : List Nat} {tys tys' : List Ty} {ss ss' : List Scheme}
    (hU : U = U0) (hU' : U' = U0) (h1 : tys' = tys.map (rsb T)) (h2 : ss' = ss.map (rsbScheme T))
    (hss : MonoCn T ss) : NRelD T U0 ⟨path, U, tys, ss⟩ ⟨path, U', tys', ss'⟩ := by
  subst hU hU' h1 h2
  refine ⟨rfl, rfl, rfl, rfl, by simp, fun i h h' => ?_⟩
  simp only [List.getElem_map]
  obtain ⟨hb, hc⟩ := hss _ (List.getElem_mem h)
  exact schInst_monoCn hb hc

theorem monoCn_nil (T : RSub) : MonoCn T [] := fun _ h => nomatch h

theorem veSchemes_rsb (T : RSub) (VE : ValEnv) : veSchemes (rsbVE T VE) = (veSchemes VE).map (rsbScheme T) := by
  simp [veSchemes, rsbVE]

/-! ## The value environments of patterns are canonical -/

mutual
theorem cn_atpat_ve : ∀ (p : AAtPat), (∀ τ ∈ tysAtPat p, cnB τ = true) → ∀ q ∈ p.ve, cnB q.2.1.body = true
  | .wild _, _, q, h | .scon _ _, _, q, h | .con _ _ _, _, q, h | .nil _, _, q, h | .unit, _, q, h => by
    simp [AAtPat.ve] at h
  | .var x τ, hc, q, h => by
    simp only [AAtPat.ve, List.mem_singleton] at h; subst h
    exact hc τ (by simp [tysAtPat])
  | .tuple p1 p2 p3, hc, q, h => by
    simp only [AAtPat.ve] at h
    rcases mem_modify h with h | h
    · rcases mem_modify h with h | h
      · exact cn_pat_ve p1 (fun τ hτ => hc τ (by simp [tysAtPat, hτ])) q h
      · exact cn_pat_ve p2 (fun τ hτ => hc τ (by simp [tysAtPat, hτ])) q h
    · cases p3 with
      | none => simp [APat.veOpt] at h
      | some p3 =>
        simp only [APat.veOpt] at h
        exact cn_pat_ve p3 (fun τ hτ => hc τ (by simp [tysAtPat, tysPatOpt, hτ])) q h
  | .record r _, hc, q, h => by
    simp only [AAtPat.ve] at h
    exact cn_patRowOpt_ve r (fun τ hτ => hc τ (by simp [tysAtPat, hτ])) q h
  | .paren p, hc, q, h => by
    simp only [AAtPat.ve] at h
    exact cn_pat_ve p (fun τ hτ => hc τ (by simpa [tysAtPat] using hτ)) q h
theorem cn_patRowOpt_ve : ∀ (r : Option APatRow), (∀ τ ∈ tysPatRowOpt r, cnB τ = true) →
    ∀ q ∈ APatRow.veOpt r, cnB q.2.1.body = true
  | none, _, q, h => by simp [APatRow.veOpt] at h
  | some (.field l τ rest), hc, q, h => by
    simp only [APatRow.veOpt, APatRow.ve] at h
    rcases mem_modify h with h | h
    · simp only [List.mem_singleton] at h; subst h
      exact hc τ (by simp [tysPatRowOpt, tysPatRow])
    · exact cn_patRowOpt_ve rest (fun x hx => hc x (by simp [tysPatRowOpt, tysPatRow, hx])) q h
theorem cn_pat_ve : ∀ (p : APat), (∀ τ ∈ tysPat p, cnB τ = true) → ∀ q ∈ p.ve, cnB q.2.1.body = true
  | .atpat a, hc, q, h => by
    simp only [APat.ve] at h
    exact cn_atpat_ve a (fun τ hτ => hc τ (by simpa [tysPat] using hτ)) q h
  | .con _ _ args _, hc, q, h => by
    simp only [APat.ve, FMap.plusAll] at h
    rcases mem_plusAll h with h | ⟨VE, hl, h⟩
    · cases h
    · exact cn_atpats_ve args (fun τ hτ => hc τ (by simp [tysPat, hτ])) VE hl q h
  | .cons p1 p2, hc, q, h => by
    simp only [APat.ve] at h
    rcases mem_modify h with h | h
    · exact cn_pat_ve p1 (fun τ hτ => hc τ (by simp [tysPat, hτ])) q h
    · exact cn_pat_ve p2 (fun τ hτ => hc τ (by simp [tysPat, hτ])) q h
  | .as p x, hc, q, h => by
    simp only [APat.ve] at h
    rcases mem_modify h with h | h
    · exact cn_pat_ve p (fun τ hτ => hc τ (by simpa [tysPat] using hτ)) q h
    · simp only [List.mem_singleton] at h; subst h
      exact cn_pat_ty p (fun τ hτ => hc τ (by simpa [tysPat] using hτ))
theorem cn_atpats_ve : ∀ (l : List AAtPat), (∀ τ ∈ tysAtPats l, cnB τ = true) →
    ∀ VE ∈ AAtPat.veList l, ∀ q ∈ VE, cnB q.2.1.body = true
  | [], _, VE, h, _, _ => by simp [AAtPat.veList] at h
  | a :: as, hc, VE, h, q, hq => by
    simp only [AAtPat.veList, List.mem_cons] at h
    rcases h with rfl | h
    · exact cn_atpat_ve a (fun τ hτ => hc τ (by simp [tysAtPats, hτ])) q hq
    · exact cn_atpats_ve as (fun τ hτ => hc τ (by simp [tysAtPats, hτ])) VE h q hq
end

def CnT (T : RSub) (l : List Ty) : Prop := ∀ τ ∈ l, cnB (rsb T τ) = true

theorem CnT.app {T : RSub} {l1 l2 : List Ty} (h : CnT T (l1 ++ l2)) : CnT T l1 ∧ CnT T l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩

theorem CnT.cons {T : RSub} {τ : Ty} {l : List Ty} (h : CnT T (τ :: l)) : cnB (rsb T τ) = true ∧ CnT T l :=
  ⟨h τ (.head _), fun x hx => h x (.tail _ hx)⟩

theorem monoCn_of_ve {T : RSub} {VE : ValEnv} (hb : ∀ q ∈ VE, q.2.1.bound = [])
    (hc : ∀ q ∈ rsbVE T VE, cnB q.2.1.body = true) : MonoCn T (veSchemes VE) := by
  intro σ hσ
  simp only [veSchemes, List.mem_map] at hσ
  obtain ⟨q, hq, rfl⟩ := hσ
  exact ⟨hb q hq, hc (q.1, (rsbScheme T q.2.1, q.2.2)) (by simp only [rsbVE, List.mem_map]; exact ⟨q, hq, rfl⟩)⟩

theorem monoCn_atpat (T : RSub) (p : AAtPat) (hcn : CnT T (tysAtPat p)) : MonoCn T (veSchemes (stripAtPat p).ve) := by
  rw [stripAtPat_ve]
  refine monoCn_of_ve (fun q hq => (atpat_ve p q hq).1) fun q hq => ?_
  rw [← rsbAtPat_veD] at hq
  refine cn_atpat_ve _ (fun τ hτ => ?_) q hq
  rw [tysAtPat_sbD] at hτ
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hτ
  exact hcn x hx

theorem monoCn_pat (T : RSub) (p : APat) (hcn : CnT T (tysPat p)) : MonoCn T (veSchemes (stripPat p).ve) := by
  rw [stripPat_ve]
  refine monoCn_of_ve (fun q hq => (pat_ve p q hq).1) fun q hq => ?_
  rw [← rsbPat_veD] at hq
  refine cn_pat_ve _ (fun τ hτ => ?_) q hq
  rw [tysPat_sbD] at hτ
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hτ
  exact hcn x hx

/-! ## Stripped and substituted patterns -/

theorem rsbPat_ty_strip (T : RSub) (p : APat) : (stripPat (rsbPat T p)).ty = rsb T (stripPat p).ty := by
  rw [stripPat_ty, stripPat_ty, rsbPat_tyD]
theorem rsbAtPat_ty_strip (T : RSub) (p : AAtPat) : (stripAtPat (rsbAtPat T p)).ty = rsb T (stripAtPat p).ty := by
  rw [stripAtPat_ty, stripAtPat_ty, rsbAtPat_tyD]
theorem rsbPat_ve_strip (T : RSub) (p : APat) : (stripPat (rsbPat T p)).ve = rsbVE T (stripPat p).ve := by
  rw [stripPat_ve, stripPat_ve, rsbPat_veD]
theorem rsbAtPat_ve_strip (T : RSub) (p : AAtPat) : (stripAtPat (rsbAtPat T p)).ve = rsbVE T (stripAtPat p).ve := by
  rw [stripAtPat_ve, stripAtPat_ve, rsbAtPat_veD]

theorem rsbPatRowOpt_rowOpt (T : RSub) : ∀ r : Option APatRow,
    APatRow.rowOpt (rsbPatRowOpt T r) = rsbRow T (APatRow.rowOpt r)
  | none => rfl
  | some (.field l τ rest) => by
    simp only [rsbPatRowOpt, rsbPatRow, APatRow.rowOpt, APatRow.row, rsbPatRowOpt_rowOpt T rest, rsbRow_modifyD]; rfl

theorem tupleTy_rsbOpt (s : RSub) (τ1 τ2 : Ty) (τ3 : Option Ty) :
    tupleTy (rsb s τ1) (rsb s τ2) (rsbOpt s τ3) = rsb s (tupleTy τ1 τ2 τ3) := (tupleTy_sbD s τ1 τ2 τ3).symm

theorem rsbPatOpt_tyOpt_strip (T : RSub) : ∀ p : Option APat,
    APat.tyOpt (stripPatOpt (rsbPatOpt T p)) = rsbOpt T (APat.tyOpt (stripPatOpt p))
  | none => rfl
  | some p => by simp only [rsbPatOpt, stripPatOpt, APat.tyOpt, rsbPat_ty_strip, rsbOpt]

/-! ## Patterns -/

mutual
theorem nodesAtPat_relD (T : RSub) (U0 : List BVar) : ∀ (p : AAtPat) (path : List Nat), CnT T (tysAtPat p) →
    F2 (NRelD T U0) (nodesAtPat U0 path (stripAtPat p)) (nodesAtPat U0 path (stripAtPat (rsbAtPat T p)))
  | .wild τ, path, _ => .cons (nrelD_mk rfl rfl (by simp [stripAtPat, rsbAtPat, AAtPat.ty, AAtPat.ve]) rfl (monoCn_nil T)) .nil
  | .scon sc τ, path, _ => .cons (nrelD_mk rfl rfl (by simp [stripAtPat, rsbAtPat, AAtPat.ty, AAtPat.ve]) rfl (monoCn_nil T)) .nil
  | .var x τ, path, _ => .cons (nrelD_mk rfl rfl (by simp [stripAtPat, rsbAtPat, AAtPat.ty, AAtPat.ve, mono]) rfl (monoCn_nil T)) .nil
  | .con lc inst τ, path, _ => .cons (nrelD_mk rfl rfl (by simp [stripAtPat, rsbAtPat, AAtPat.ty, AAtPat.ve]) rfl (monoCn_nil T)) .nil
  | .nil τ, path, _ => .cons (nrelD_mk rfl rfl (by simp [stripAtPat, rsbAtPat, AAtPat.ty, AAtPat.ve]) rfl (monoCn_nil T)) .nil
  | .unit, path, _ => .cons (nrelD_mk rfl rfl (by simp [stripAtPat, rsbAtPat, AAtPat.ty, AAtPat.ve, tUnitTy, rsb, rsbList]) rfl (monoCn_nil T)) .nil
  | .tuple p1 p2 p3, path, hcn => by
    have hcn' := hcn
    simp only [tysAtPat] at hcn'
    obtain ⟨hc12, hc3⟩ := CnT.app hcn'; obtain ⟨hc1, hc2⟩ := CnT.app hc12
    exact forall2_append (forall2_append (forall2_append
      (.cons (nrelD_mk rfl rfl (by
          simp only [stripAtPat, rsbAtPat, AAtPat.ty, List.map_cons, List.map_nil, rsbPat_ty_strip,
            rsbPatOpt_tyOpt_strip, tupleTy_rsbOpt])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbAtPat_ve_strip T (.tuple p1 p2 p3))
        (monoCn_atpat T (.tuple p1 p2 p3) hcn)) .nil)
      (nodesPat_relD T U0 p1 _ hc1)) (nodesPat_relD T U0 p2 _ hc2)) (nodesPatOpt_relD T U0 p3 _ hc3)
  | .record r τ, path, hcn => by
    have hcn' := hcn
    simp only [tysAtPat] at hcn'
    exact forall2_append (.cons (nrelD_mk rfl rfl rfl
        (by rw [← veSchemes_rsb]; congr 1; exact rsbAtPat_ve_strip T (.record r τ))
        (monoCn_atpat T (.record r τ) hcn)) .nil)
      (nodesPatRowOpt_relD T U0 r _ (CnT.cons hcn').2)
  | .paren p, path, hcn => by
    have hcn' := hcn
    simp only [tysAtPat] at hcn'
    exact forall2_append (.cons (nrelD_mk rfl rfl (by simp [stripAtPat, rsbAtPat, AAtPat.ty, rsbPat_ty_strip])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbPat_ve_strip T p)
        (monoCn_atpat T (.paren p) hcn)) .nil)
      (nodesPat_relD T U0 p _ hcn')
theorem nodesPatRowOpt_relD (T : RSub) (U0 : List BVar) : ∀ (r : Option APatRow) (path : List Nat), CnT T (tysPatRowOpt r) →
    F2 (NRelD T U0) (nodesPatRowOpt U0 path r) (nodesPatRowOpt U0 path (rsbPatRowOpt T r))
  | none, _, _ => .nil
  | some (.field l τ rest), path, hcn => by
    have hcn' := hcn
    simp only [tysPatRowOpt, tysPatRow] at hcn'
    exact forall2_append (.cons (nrelD_mk rfl rfl (by
        show [rsb T τ] ++ (Row.modify [(l, rsb T τ)] (APatRow.rowOpt (rsbPatRowOpt T rest))).map (·.2) = _
        rw [rsbPatRowOpt_rowOpt, show ([(l, rsb T τ)] : Row) = rsbRow T [(l, τ)] from rfl, ← rsbRow_modifyD, rsbRow_eq]
        simp [APatRow.row, mapV]) rfl (monoCn_nil T)) .nil)
      (nodesPatRowOpt_relD T U0 rest _ (CnT.cons hcn').2)
theorem nodesPat_relD (T : RSub) (U0 : List BVar) : ∀ (p : APat) (path : List Nat), CnT T (tysPat p) →
    F2 (NRelD T U0) (nodesPat U0 path (stripPat p)) (nodesPat U0 path (stripPat (rsbPat T p)))
  | .atpat a, path, hcn => by
    have hcn' := hcn
    simp only [tysPat] at hcn'
    exact forall2_append (.cons (nrelD_mk rfl rfl (by simp [stripPat, rsbPat, APat.ty, rsbAtPat_ty_strip])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbAtPat_ve_strip T a)
        (monoCn_pat T (.atpat a) hcn)) .nil)
      (nodesAtPat_relD T U0 a _ hcn')
  | .con lc inst args τ, path, hcn => by
    have hcn' := hcn
    simp only [tysPat] at hcn'
    exact forall2_append (.cons (nrelD_mk rfl rfl (by simp [stripPat, rsbPat])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbPat_ve_strip T (.con lc inst args τ))
        (monoCn_pat T (.con lc inst args τ) hcn)) .nil)
      (nodesAtPats_relD T U0 args path 0 (CnT.cons hcn').2)
  | .cons p1 p2, path, hcn => by
    have hcn' := hcn
    simp only [tysPat] at hcn'
    obtain ⟨hc1, hc2⟩ := CnT.app hcn'
    exact forall2_append (forall2_append (.cons (nrelD_mk rfl rfl
        (by simp [stripPat, rsbPat, APat.ty, rsbPat_ty_strip, listTy_sbD])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbPat_ve_strip T (.cons p1 p2))
        (monoCn_pat T (.cons p1 p2) hcn)) .nil)
      (nodesPat_relD T U0 p1 _ hc1)) (nodesPat_relD T U0 p2 _ hc2)
  | .as p x, path, hcn => by
    have hcn' := hcn
    simp only [tysPat] at hcn'
    exact forall2_append (.cons (nrelD_mk rfl rfl (by simp [stripPat, rsbPat, APat.ty, rsbPat_ty_strip])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbPat_ve_strip T (.as p x))
        (monoCn_pat T (.as p x) hcn)) .nil)
      (nodesPat_relD T U0 p _ hcn')
theorem nodesPatOpt_relD (T : RSub) (U0 : List BVar) : ∀ (p : Option APat) (path : List Nat), CnT T (tysPatOpt p) →
    F2 (NRelD T U0) (nodesPatOpt U0 path (stripPatOpt p)) (nodesPatOpt U0 path (stripPatOpt (rsbPatOpt T p)))
  | none, _, _ => .nil
  | some p, path, hcn => nodesPat_relD T U0 p path hcn
theorem nodesAtPats_relD (T : RSub) (U0 : List BVar) : ∀ (l : List AAtPat) (path : List Nat) (i : Nat), CnT T (tysAtPats l) →
    F2 (NRelD T U0) (nodesAtPats U0 path i (stripAtPats l)) (nodesAtPats U0 path i (stripAtPats (rsbAtPats T l)))
  | [], _, _, _ => .nil
  | a :: as, path, i, hcn => by
    have hcn' := hcn
    simp only [tysAtPats] at hcn'
    obtain ⟨hc1, hc2⟩ := CnT.app hcn'
    exact forall2_append (nodesAtPat_relD T U0 a _ hc1) (nodesAtPats_relD T U0 as path (i + 1) hc2)
end

end StandardElm.Stat.Complete.WDP
