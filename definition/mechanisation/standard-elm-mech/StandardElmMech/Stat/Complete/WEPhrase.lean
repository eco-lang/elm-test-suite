/-
  A Standard Definition of Elm? Mechanisation: the types an annotated phrase records, for W on
  F_e (milestone (e) of plan step 11), as WPhrase.lean and WDPhrase.lean with two changes.

  * An annotation is marked (`annSentinel`, never `OkTD`, never in `NBD`) only when its `U'` is not
    the one W takes (`canonAnnB`), in both modes: W's annotations are unmarked whatever their
    explicit variables, and a derivation's are when they carry W's variables.
  * The environment of a declaration (mode `true`): a monomorphic entry contributes its type; a
    polymorphic one (an annotated member, `∀U'.τ`, with `bnd` variables) contributes its free
    variables other than the `bnd` and named ones (`schTys`, none for W's annotated members).
    Agreement (`AgreeOnD`) is on the types of the list and on every `bnd` and named variable
    (`BN`), which every substitution of the induction fixes; with it, the environment's schemes
    agree (`rsbScheme_congrE`).
-/
import StandardElmMech.Stat.Complete.WE
import StandardElmMech.Stat.Complete.WDCompletePat

namespace StandardElm.Stat.Complete
namespace WE
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## The types of a phrase -/

/-- An annotation is marked when its explicit variables are not W's, and (mode `true`, W's
    result) when the annotated member's type has a variable that is not named. -/
def annMark (w : Bool) (ann : Option (StandardElm.Src.BTy × List BVar)) (τ : Ty) : List Ty :=
  if canonAnnB ann = true ∧ (w = true → ann.isSome = true → ∀ v ∈ τ.vars, v.isNamed = true) then [] else [annSentinel]

theorem annMark_false (ann : Option (StandardElm.Src.BTy × List BVar)) (τ : Ty) :
    annMark false ann τ = if canonAnnB ann = true then [] else [annSentinel] := by
  simp [annMark]

/-- `bnd` and named variables: fixed by every substitution of the induction. -/
def BN (v : BVar) : Bool := v.isBnd || v.isNamed

/-- What a scheme of a declaration's environment contributes in mode `true`. -/
def schTys (σ : Scheme) : List Ty :=
  if σ.bound = [] then [σ.body] else (σ.body.vars.filter fun v => !BN v).map vty

def veTys (VE : ValEnv) : List Ty := VE.flatMap fun q => schTys q.2.1

theorem veTys_mono {VE : ValEnv} (h : ∀ q ∈ VE, q.2.1.bound = []) : veTys VE = veBodies VE := by
  induction VE with
  | nil => rfl
  | cons q r ih =>
    simp only [veTys, veBodies, List.flatMap_cons, List.map_cons] at ih ⊢
    rw [ih fun q' hq' => h q' (.tail _ hq')]
    simp [schTys, h q (.head _)]

mutual
def tysAtExp (w : Bool) : AAtExp → List Ty
  | .scon _ τ | .var _ _ τ | .con _ _ τ | .op _ _ τ | .nil τ => [τ]
  | .unit => []
  | .tuple e1 e2 e3 => tysExp w e1 ++ tysExp w e2 ++ tysExpOpt w e3
  | .record row => tysExpRowOpt w row
  | .update _ _ τ row => τ :: tysExpRow w row
  | .letE d e => tysDec w d ++ tysExp w e
  | .paren e => tysExp w e
def tysExpRow (w : Bool) : AExpRow → List Ty
  | .field _ e rest => tysExp w e ++ tysExpRowOpt w rest
def tysExpRowOpt (w : Bool) : Option AExpRow → List Ty
  | none => []
  | some r => tysExpRow w r
def tysExp (w : Bool) : AExp → List Ty
  | .atexp a => tysAtExp w a
  | .app e a => tysExp w e ++ tysAtExp w a
  | .lam p e => tysAtPat p ++ tysExp w e
  | .caseE e m => tysExp w e ++ tysMatch w m
def tysExpOpt (w : Bool) : Option AExp → List Ty
  | none => []
  | some e => tysExp w e
def tysMatch (w : Bool) : AMatch → List Ty
  | .mk mr rest => tysMRule w mr ++ tysMatchOpt w rest
def tysMatchOpt (w : Bool) : Option AMatch → List Ty
  | none => []
  | some m => tysMatch w m
def tysMRule (w : Bool) : AMRule → List Ty
  | .mk p e => tysPat p ++ tysExp w e
def tysDec (w : Bool) : ADec → List Ty
  | .val VE vb => (if w then veTys VE else []) ++ tysValBind w vb
def tysValBind (w : Bool) : AValBind → List Ty
  | .var _ ann τ e rest => τ :: annMark w ann τ ++ tysExp w e ++ tysValBindOpt w rest
  | .pat p e => tysAtPat p ++ tysExp w e
def tysValBindOpt (w : Bool) : Option AValBind → List Ty
  | none => []
  | some vb => tysValBind w vb
end


/-! ## Strip -/

mutual
theorem tysAtExp_strip (w : Bool) : ∀ a : AAtExp, tysAtExp w (stripAtExp a) = tysAtExp w a
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [stripAtExp, tysAtExp, tysExp_strip w e1, tysExp_strip w e2, tysExpOpt_strip w e3]
  | .record r => by simp only [stripAtExp, tysAtExp, tysExpRowOpt_strip w r]
  | .update _ _ _ r => by simp only [stripAtExp, tysAtExp, tysExpRow_strip w r]
  | .letE d e => by simp only [stripAtExp, tysAtExp, tysDec_strip w d, tysExp_strip w e]
  | .paren e => by simp only [stripAtExp, tysAtExp, tysExp_strip w e]
theorem tysExpRow_strip (w : Bool) : ∀ r : AExpRow, tysExpRow w (stripExpRow r) = tysExpRow w r
  | .field _ e rest => by simp only [stripExpRow, tysExpRow, tysExp_strip w e, tysExpRowOpt_strip w rest]
theorem tysExpRowOpt_strip (w : Bool) : ∀ r : Option AExpRow, tysExpRowOpt w (stripExpRowOpt r) = tysExpRowOpt w r
  | none => rfl
  | some r => by simp only [stripExpRowOpt, tysExpRowOpt, tysExpRow_strip w r]
theorem tysExp_strip (w : Bool) : ∀ e : AExp, tysExp w (stripExp e) = tysExp w e
  | .atexp a => by simp only [stripExp, tysExp, tysAtExp_strip w a]
  | .app e a => by simp only [stripExp, tysExp, tysExp_strip w e, tysAtExp_strip w a]
  | .lam p e => by simp only [stripExp, tysExp, tysAtPat_strip p, tysExp_strip w e]
  | .caseE e m => by simp only [stripExp, tysExp, tysExp_strip w e, tysMatch_strip w m]
theorem tysExpOpt_strip (w : Bool) : ∀ e : Option AExp, tysExpOpt w (stripExpOpt e) = tysExpOpt w e
  | none => rfl
  | some e => by simp only [stripExpOpt, tysExpOpt, tysExp_strip w e]
theorem tysMatch_strip (w : Bool) : ∀ m : AMatch, tysMatch w (stripMatch m) = tysMatch w m
  | .mk mr rest => by simp only [stripMatch, tysMatch, tysMRule_strip w mr, tysMatchOpt_strip w rest]
theorem tysMatchOpt_strip (w : Bool) : ∀ m : Option AMatch, tysMatchOpt w (stripMatchOpt m) = tysMatchOpt w m
  | none => rfl
  | some m => by simp only [stripMatchOpt, tysMatchOpt, tysMatch_strip w m]
theorem tysMRule_strip (w : Bool) : ∀ mr : AMRule, tysMRule w (stripMRule mr) = tysMRule w mr
  | .mk p e => by simp only [stripMRule, tysMRule, tysPat_strip p, tysExp_strip w e]
theorem tysDec_strip (w : Bool) : ∀ d : ADec, tysDec w (stripDec d) = tysDec w d
  | .val VE vb => by simp only [stripDec, tysDec, tysValBind_strip w vb]
theorem tysValBind_strip (w : Bool) : ∀ vb : AValBind, tysValBind w (stripValBind vb) = tysValBind w vb
  | .var _ _ _ e rest => by simp only [stripValBind, tysValBind, tysExp_strip w e, tysValBindOpt_strip w rest]
  | .pat p e => by simp only [stripValBind, tysValBind, tysAtPat_strip p, tysExp_strip w e]
theorem tysValBindOpt_strip (w : Bool) : ∀ vb : Option AValBind, tysValBindOpt w (stripValBindOpt vb) = tysValBindOpt w vb
  | none => rfl
  | some vb => by simp only [stripValBindOpt, tysValBindOpt, tysValBind_strip w vb]
end

/-! ## Substitution (mode `false`) -/

theorem annMark_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0)))
    (ann : Option (StandardElm.Src.BTy × List BVar)) (τ τ' : Ty) : (annMark false ann τ).map (rsb s) = annMark false ann τ' := by
  simp only [annMark_false]
  split
  · rfl
  · simp [annSentinel, rsb, RSub.tl, hs, rsbRow, mrg_nil_right]

theorem annSentinel_not_okTD {n : Nat} : ¬ OkTD n annSentinel := fun h => by
  have := (h (.row (.bnd 0)) (by simp [annSentinel, Ty.vars, Ty.rowVars])).1; simp [BVar.isBnd] at this

theorem canon_of_okAD {n : Nat} {w : Bool} {ann : Option (StandardElm.Src.BTy × List BVar)}
    {τ0 : Ty} (h : ∀ τ ∈ annMark w ann τ0, OkTD n τ) : canonAnnB ann = true := by
  simp only [annMark] at h
  split at h
  · rename_i hc; exact hc.1
  · exact absurd (h _ (.head _)) annSentinel_not_okTD

theorem named_of_okAD {n : Nat} {ann : Option (StandardElm.Src.BTy × List BVar)}
    {τ0 : Ty} (h : ∀ τ ∈ annMark true ann τ0, OkTD n τ) (hs : ann.isSome = true) : ∀ v ∈ τ0.vars, v.isNamed = true := by
  unfold annMark at h
  split at h
  · rename_i hc; exact hc.2 rfl hs
  · exact absurd (h _ (.head _)) annSentinel_not_okTD

mutual
theorem tysAtExp_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ a : AAtExp, tysAtExp false (rsbAtExp s a) = (tysAtExp false a).map (rsb s)
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [rsbAtExp, tysAtExp, tysExp_sbD s hs e1, tysExp_sbD s hs e2, tysExpOpt_sbD s hs e3, List.map_append]
  | .record r => by simp only [rsbAtExp, tysAtExp, tysExpRowOpt_sbD s hs r]
  | .update _ _ _ r => by simp only [rsbAtExp, tysAtExp, tysExpRow_sbD s hs r, List.map_cons]
  | .letE d e => by simp only [rsbAtExp, tysAtExp, tysDec_sbD s hs d, tysExp_sbD s hs e, List.map_append]
  | .paren e => by simp only [rsbAtExp, tysAtExp, tysExp_sbD s hs e]
theorem tysExpRow_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ r : AExpRow, tysExpRow false (rsbExpRow s r) = (tysExpRow false r).map (rsb s)
  | .field _ e rest => by simp only [rsbExpRow, tysExpRow, tysExp_sbD s hs e, tysExpRowOpt_sbD s hs rest, List.map_append]
theorem tysExpRowOpt_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ r : Option AExpRow,
    tysExpRowOpt false (rsbExpRowOpt s r) = (tysExpRowOpt false r).map (rsb s)
  | none => rfl
  | some r => by simp only [rsbExpRowOpt, tysExpRowOpt, tysExpRow_sbD s hs r]
theorem tysExp_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ e : AExp, tysExp false (rsbExp s e) = (tysExp false e).map (rsb s)
  | .atexp a => by simp only [rsbExp, tysExp, tysAtExp_sbD s hs a]
  | .app e a => by simp only [rsbExp, tysExp, tysExp_sbD s hs e, tysAtExp_sbD s hs a, List.map_append]
  | .lam p e => by simp only [rsbExp, tysExp, tysAtPat_sbD s p, tysExp_sbD s hs e, List.map_append]
  | .caseE e m => by simp only [rsbExp, tysExp, tysExp_sbD s hs e, tysMatch_sbD s hs m, List.map_append]
theorem tysExpOpt_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ e : Option AExp, tysExpOpt false (rsbExpOpt s e) = (tysExpOpt false e).map (rsb s)
  | none => rfl
  | some e => by simp only [rsbExpOpt, tysExpOpt, tysExp_sbD s hs e]
theorem tysMatch_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ m : AMatch, tysMatch false (rsbMatch s m) = (tysMatch false m).map (rsb s)
  | .mk mr rest => by simp only [rsbMatch, tysMatch, tysMRule_sbD s hs mr, tysMatchOpt_sbD s hs rest, List.map_append]
theorem tysMatchOpt_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ m : Option AMatch, tysMatchOpt false (rsbMatchOpt s m) = (tysMatchOpt false m).map (rsb s)
  | none => rfl
  | some m => by simp only [rsbMatchOpt, tysMatchOpt, tysMatch_sbD s hs m]
theorem tysMRule_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ mr : AMRule, tysMRule false (rsbMRule s mr) = (tysMRule false mr).map (rsb s)
  | .mk p e => by simp only [rsbMRule, tysMRule, tysPat_sbD s p, tysExp_sbD s hs e, List.map_append]
theorem tysDec_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ d : ADec, tysDec false (rsbDec s d) = (tysDec false d).map (rsb s)
  | .val VE vb => by
    simp only [rsbDec, tysDec, tysValBind_sbD s hs vb, List.map_append, Bool.false_eq_true, ↓reduceIte, List.map_nil,
      List.nil_append]
theorem tysValBind_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ vb : AValBind, tysValBind false (rsbValBind s vb) = (tysValBind false vb).map (rsb s)
  | .var _ ann τ e rest => by
    simp only [rsbValBind, tysValBind, tysExp_sbD s hs e, tysValBindOpt_sbD s hs rest, List.map_append, List.map_cons,
      List.cons_append, annMark_sbD s hs ann τ (rsb s τ)]
  | .pat p e => by simp only [rsbValBind, tysValBind, tysAtPat_sbD s p, tysExp_sbD s hs e, List.map_append]
theorem tysValBindOpt_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ vb : Option AValBind,
    tysValBindOpt false (rsbValBindOpt s vb) = (tysValBindOpt false vb).map (rsb s)
  | none => rfl
  | some vb => by simp only [rsbValBindOpt, tysValBindOpt, tysValBind_sbD s hs vb]
end
/-! ## Congruence: substitutions agreeing on the types give the same phrase -/

/-- Agreement of two substitutions on a list of types. -/
def AgreeOnD (s t : RSub) (l : List Ty) : Prop :=
  (∀ τ ∈ l, rsb s τ = rsb t τ) ∧ ∀ v, BN v = true → s.img v = t.img v

theorem AgreeOnD.app {s t : RSub} {l1 l2 : List Ty} (h : AgreeOnD s t (l1 ++ l2)) : AgreeOnD s t l1 ∧ AgreeOnD s t l2 :=
  ⟨⟨fun τ hτ => h.1 τ (List.mem_append_left _ hτ), h.2⟩, ⟨fun τ hτ => h.1 τ (List.mem_append_right _ hτ), h.2⟩⟩

theorem AgreeOnD.cons {s t : RSub} {τ : Ty} {l : List Ty} (h : AgreeOnD s t (τ :: l)) : rsb s τ = rsb t τ ∧ AgreeOnD s t l :=
  ⟨h.1 τ (.head _), fun x hx => h.1 x (.tail _ hx), h.2⟩

theorem rsbScheme_congrE {s t : RSub} {σ : Scheme} (h : AgreeOnD s t (schTys σ)) : rsbScheme s σ = rsbScheme t σ := by
  unfold schTys at h
  simp only [rsbScheme, Scheme.mk.injEq, true_and]
  split at h
  · exact (AgreeOnD.cons h).1
  · refine rsb_congr _ fun w hw => ?_
    cases hb : BN w
    · have hm : vty w ∈ (σ.body.vars.filter fun v => !BN v).map vty :=
        List.mem_map_of_mem (List.mem_filter.mpr ⟨hw, by simp [hb]⟩)
      have := h.1 _ hm
      rwa [rsb_vty, rsb_vty] at this
    · exact h.2 w hb

theorem rsbVE_congrD {s t : RSub} {VE : ValEnv} (h : AgreeOnD s t (veTys VE)) : rsbVE s VE = rsbVE t VE := by
  induction VE with
  | nil => rfl
  | cons p r ih =>
    simp only [veTys, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbVE, List.map_cons] at ih ⊢
    rw [ih h2, rsbScheme_congrE h1]

mutual
theorem rsbAtPat_congrD {s t : RSub} : ∀ p : AAtPat, AgreeOnD s t (tysAtPat p) →
    stripAtPat (rsbAtPat s p) = stripAtPat (rsbAtPat t p)
  | .wild _, h | .scon _ _, h | .var _ _, h | .con _ _ _, h | .nil _, h => by
    simp only [tysAtPat] at h; simp [rsbAtPat, stripAtPat, (AgreeOnD.cons h).1]
  | .unit, _ => rfl
  | .tuple p1 p2 p3, h => by
    simp only [tysAtPat] at h
    obtain ⟨h12, h3⟩ := AgreeOnD.app h; obtain ⟨h1, h2⟩ := AgreeOnD.app h12
    simp only [rsbAtPat, stripAtPat, rsbPat_congrD p1 h1, rsbPat_congrD p2 h2, rsbPatOpt_congrD p3 h3]
  | .record r _, h => by
    simp only [tysAtPat] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.cons h
    simp only [rsbAtPat, stripAtPat, h1, rsbPatRowOpt_congrD r h2]
  | .paren p, h => by simp only [tysAtPat] at h; simp only [rsbAtPat, stripAtPat, rsbPat_congrD p h]
theorem rsbPatRowOpt_congrD {s t : RSub} : ∀ r : Option APatRow, AgreeOnD s t (tysPatRowOpt r) →
    rsbPatRowOpt s r = rsbPatRowOpt t r
  | none, _ => rfl
  | some (.field l τ rest), h => by
    simp only [tysPatRowOpt, tysPatRow] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.cons h
    simp only [rsbPatRowOpt, rsbPatRow, h1, rsbPatRowOpt_congrD rest h2]
theorem rsbPat_congrD {s t : RSub} : ∀ p : APat, AgreeOnD s t (tysPat p) → stripPat (rsbPat s p) = stripPat (rsbPat t p)
  | .atpat a, h => by simp only [tysPat] at h; simp only [rsbPat, stripPat, rsbAtPat_congrD a h]
  | .con _ _ args _, h => by
    simp only [tysPat] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.cons h
    simp only [rsbPat, stripPat, h1, rsbAtPats_congrD args h2]
  | .cons p1 p2, h => by
    simp only [tysPat] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbPat, stripPat, rsbPat_congrD p1 h1, rsbPat_congrD p2 h2]
  | .as p _, h => by simp only [tysPat] at h; simp only [rsbPat, stripPat, rsbPat_congrD p h]
theorem rsbPatOpt_congrD {s t : RSub} : ∀ p : Option APat, AgreeOnD s t (tysPatOpt p) →
    stripPatOpt (rsbPatOpt s p) = stripPatOpt (rsbPatOpt t p)
  | none, _ => rfl
  | some p, h => by simp only [tysPatOpt] at h; simp only [rsbPatOpt, stripPatOpt, rsbPat_congrD p h]
theorem rsbAtPats_congrD {s t : RSub} : ∀ l : List AAtPat, AgreeOnD s t (tysAtPats l) →
    stripAtPats (rsbAtPats s l) = stripAtPats (rsbAtPats t l)
  | [], _ => rfl
  | a :: as, h => by
    simp only [tysAtPats] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbAtPats, stripAtPats, rsbAtPat_congrD a h1, rsbAtPats_congrD as h2]
end

mutual
theorem rsbAtExp_congrD {s t : RSub} : ∀ a : AAtExp, AgreeOnD s t (tysAtExp true a) →
    stripAtExp (rsbAtExp s a) = stripAtExp (rsbAtExp t a)
  | .scon _ _, h | .var _ _ _, h | .con _ _ _, h | .op _ _ _, h | .nil _, h => by
    simp only [tysAtExp] at h; simp [rsbAtExp, stripAtExp, (AgreeOnD.cons h).1]
  | .unit, _ => rfl
  | .tuple e1 e2 e3, h => by
    simp only [tysAtExp] at h
    obtain ⟨h12, h3⟩ := AgreeOnD.app h; obtain ⟨h1, h2⟩ := AgreeOnD.app h12
    simp only [rsbAtExp, stripAtExp, rsbExp_congrD e1 h1, rsbExp_congrD e2 h2, rsbExpOpt_congrD e3 h3]
  | .record r, h => by simp only [tysAtExp] at h; simp only [rsbAtExp, stripAtExp, rsbExpRowOpt_congrD r h]
  | .update _ _ _ r, h => by
    simp only [tysAtExp] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.cons h
    simp only [rsbAtExp, stripAtExp, h1, rsbExpRow_congrD r h2]
  | .letE d e, h => by
    simp only [tysAtExp] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbAtExp, stripAtExp, rsbDec_congrD d h1, rsbExp_congrD e h2]
  | .paren e, h => by simp only [tysAtExp] at h; simp only [rsbAtExp, stripAtExp, rsbExp_congrD e h]
theorem rsbExpRow_congrD {s t : RSub} : ∀ r : AExpRow, AgreeOnD s t (tysExpRow true r) →
    stripExpRow (rsbExpRow s r) = stripExpRow (rsbExpRow t r)
  | .field _ e rest, h => by
    simp only [tysExpRow] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbExpRow, stripExpRow, rsbExp_congrD e h1, rsbExpRowOpt_congrD rest h2]
theorem rsbExpRowOpt_congrD {s t : RSub} : ∀ r : Option AExpRow, AgreeOnD s t (tysExpRowOpt true r) →
    stripExpRowOpt (rsbExpRowOpt s r) = stripExpRowOpt (rsbExpRowOpt t r)
  | none, _ => rfl
  | some r, h => by simp only [tysExpRowOpt] at h; simp only [rsbExpRowOpt, stripExpRowOpt, rsbExpRow_congrD r h]
theorem rsbExp_congrD {s t : RSub} : ∀ e : AExp, AgreeOnD s t (tysExp true e) →
    stripExp (rsbExp s e) = stripExp (rsbExp t e)
  | .atexp a, h => by simp only [tysExp] at h; simp only [rsbExp, stripExp, rsbAtExp_congrD a h]
  | .app e a, h => by
    simp only [tysExp] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbExp, stripExp, rsbExp_congrD e h1, rsbAtExp_congrD a h2]
  | .lam p e, h => by
    simp only [tysExp] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbExp, stripExp, rsbAtPat_congrD p h1, rsbExp_congrD e h2]
  | .caseE e m, h => by
    simp only [tysExp] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbExp, stripExp, rsbExp_congrD e h1, rsbMatch_congrD m h2]
theorem rsbExpOpt_congrD {s t : RSub} : ∀ e : Option AExp, AgreeOnD s t (tysExpOpt true e) →
    stripExpOpt (rsbExpOpt s e) = stripExpOpt (rsbExpOpt t e)
  | none, _ => rfl
  | some e, h => by simp only [tysExpOpt] at h; simp only [rsbExpOpt, stripExpOpt, rsbExp_congrD e h]
theorem rsbMatch_congrD {s t : RSub} : ∀ m : AMatch, AgreeOnD s t (tysMatch true m) →
    stripMatch (rsbMatch s m) = stripMatch (rsbMatch t m)
  | .mk mr rest, h => by
    simp only [tysMatch] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbMatch, stripMatch, rsbMRule_congrD mr h1, rsbMatchOpt_congrD rest h2]
theorem rsbMatchOpt_congrD {s t : RSub} : ∀ m : Option AMatch, AgreeOnD s t (tysMatchOpt true m) →
    stripMatchOpt (rsbMatchOpt s m) = stripMatchOpt (rsbMatchOpt t m)
  | none, _ => rfl
  | some m, h => by simp only [tysMatchOpt] at h; simp only [rsbMatchOpt, stripMatchOpt, rsbMatch_congrD m h]
theorem rsbMRule_congrD {s t : RSub} : ∀ mr : AMRule, AgreeOnD s t (tysMRule true mr) →
    stripMRule (rsbMRule s mr) = stripMRule (rsbMRule t mr)
  | .mk p e, h => by
    simp only [tysMRule] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbMRule, stripMRule, rsbPat_congrD p h1, rsbExp_congrD e h2]
theorem rsbDec_congrD {s t : RSub} : ∀ d : ADec, AgreeOnD s t (tysDec true d) →
    stripDec (rsbDec s d) = stripDec (rsbDec t d)
  | .val VE vb, h => by
    simp only [tysDec, ↓reduceIte] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbDec, stripDec, rsbVE_congrD h1, rsbValBind_congrD vb h2]
theorem rsbValBind_congrD {s t : RSub} : ∀ vb : AValBind, AgreeOnD s t (tysValBind true vb) →
    stripValBind (rsbValBind s vb) = stripValBind (rsbValBind t vb)
  | .var _ _ _ e rest, h => by
    simp only [tysValBind, List.cons_append] at h
    obtain ⟨h0, h⟩ := AgreeOnD.cons h
    obtain ⟨h12, h2⟩ := AgreeOnD.app h
    obtain ⟨-, h1⟩ := AgreeOnD.app h12
    simp only [rsbValBind, stripValBind, h0, rsbExp_congrD e h1, rsbValBindOpt_congrD rest h2]
  | .pat p e, h => by
    simp only [tysValBind] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.app h
    simp only [rsbValBind, stripValBind, rsbAtPat_congrD p h1, rsbExp_congrD e h2]
theorem rsbValBindOpt_congrD {s t : RSub} : ∀ vb : Option AValBind, AgreeOnD s t (tysValBindOpt true vb) →
    stripValBindOpt (rsbValBindOpt s vb) = stripValBindOpt (rsbValBindOpt t vb)
  | none, _ => rfl
  | some vb, h => by simp only [tysValBindOpt] at h; simp only [rsbValBindOpt, stripValBindOpt, rsbValBind_congrD vb h]
end


/-! ## A derivation's types are canonical when the types it records are -/

mutual
theorem cn_atexp_ty : ∀ a : AAtExp, (∀ τ ∈ tysAtExp false a, cnB τ = true) → cnB a.ty = true
  | .scon _ _, h | .var _ _ _, h | .con _ _ _, h | .op _ _ _, h | .nil _, h | .update _ _ _ _, h =>
    h _ (by simp [tysAtExp, AAtExp.ty])
  | .unit, _ => rfl
  | .tuple e1 e2 e3, h => by
    simp only [tysAtExp, List.mem_append] at h
    exact cnB_tuple (cn_exp_ty e1 fun τ hτ => h τ (.inl (.inl hτ))) (cn_exp_ty e2 fun τ hτ => h τ (.inl (.inr hτ)))
      (cn_expopt_ty e3 fun τ hτ => h τ (.inr hτ))
  | .record r, h => by
    simp only [tysAtExp] at h
    exact cnB_record_of (cn_exprowopt_row r h)
  | .letE d e, h => by
    simp only [tysAtExp, List.mem_append] at h
    exact cn_exp_ty e fun τ hτ => h τ (.inr hτ)
  | .paren e, h => by simp only [tysAtExp] at h; exact cn_exp_ty e h
theorem cn_exprow_row : ∀ r : AExpRow, (∀ τ ∈ tysExpRow false r, cnB τ = true) → CnRow r.row
  | .field l e rest, h => by
    simp only [tysExpRow, List.mem_append] at h
    exact cnRow_modify1 (cn_exp_ty e fun τ hτ => h τ (.inl hτ)) (cn_exprowopt_row rest fun τ hτ => h τ (.inr hτ))
theorem cn_exprowopt_row : ∀ r : Option AExpRow, (∀ τ ∈ tysExpRowOpt false r, cnB τ = true) → CnRow (AExpRow.rowOpt r)
  | none, _ => cnRow_nil
  | some r, h => by simp only [tysExpRowOpt] at h; exact cn_exprow_row r h
theorem cn_exp_ty : ∀ e : AExp, (∀ τ ∈ tysExp false e, cnB τ = true) → cnB e.ty = true
  | .atexp a, h => by simp only [tysExp] at h; exact cn_atexp_ty a h
  | .app e a, h => by
    simp only [tysExp, List.mem_append] at h
    exact cnB_cod (cn_exp_ty e fun τ hτ => h τ (.inl hτ))
  | .lam p e, h => by
    simp only [tysExp, List.mem_append] at h
    exact cnB_fn.mpr ⟨cn_atpat_ty p fun τ hτ => h τ (.inl hτ), cn_exp_ty e fun τ hτ => h τ (.inr hτ)⟩
  | .caseE e m, h => by
    simp only [tysExp, List.mem_append] at h
    exact cnB_cod (cn_match_ty m fun τ hτ => h τ (.inr hτ))
theorem cn_expopt_ty : ∀ e : Option AExp, (∀ τ ∈ tysExpOpt false e, cnB τ = true) → ∀ τ, AExp.tyOpt e = some τ → cnB τ = true
  | none, _, _, h => by cases h
  | some e, h, τ, h' => by
    simp only [AExp.tyOpt, Option.some.injEq] at h'; subst h'
    exact cn_exp_ty e h
theorem cn_match_ty : ∀ m : AMatch, (∀ τ ∈ tysMatch false m, cnB τ = true) → cnB m.ty = true
  | .mk (.mk p e) rest, h => by
    simp only [tysMatch, tysMRule, List.mem_append] at h
    exact cnB_fn.mpr ⟨cn_pat_ty p fun τ hτ => h τ (.inl (.inl hτ)), cn_exp_ty e fun τ hτ => h τ (.inl (.inr hτ))⟩
end

theorem cn_mrule_ty : ∀ mr : AMRule, (∀ τ ∈ tysMRule false mr, cnB τ = true) → cnB mr.ty = true
  | .mk p e, h => by
    simp only [tysMRule, List.mem_append] at h
    exact cnB_fn.mpr ⟨cn_pat_ty p fun τ hτ => h τ (.inl hτ), cn_exp_ty e fun τ hτ => h τ (.inr hτ)⟩

theorem newB_BN {n : Nat} {v : BVar} (h : BN v = true) : newB n v = false := by
  rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BN, BVar.isBnd, BVar.isNamed, newB, TyVar.isNew]

end WE

open WE in
theorem FoundD.agreeOnE {n0 n : Nat} {S' T : RSub} {st : WDSt} (h : FoundD n0 S' n st T) {l : List Ty}
    (hl : OkAD n l) : WE.AgreeOnD T S' l :=
  ⟨fun τ hτ => h.sb_eq (hl τ hτ), fun v hv => h.agree v (newB_BN hv)⟩

end StandardElm.Stat.Complete
