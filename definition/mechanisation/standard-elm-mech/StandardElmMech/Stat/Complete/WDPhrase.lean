/-
  A Standard Definition of Elm? Mechanisation: the types an annotated phrase records, under
  substitutions of type and row variables, for the main induction L11 of plan step 11,
  milestone (d) (WPhrase.lean for `RSub`; the lists `tysExp` etc. are WPhrase.lean's).

  Lemmas: they commute with substitution; two substitutions agreeing on them give the same phrase
  (with the instance lists left out).
-/
import StandardElmMech.Stat.Complete.WDClosure
import StandardElmMech.Stat.Complete.WPhrase

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-- A substitution fixing the row variable `bnd 0` (every one fixing the rigid variables does)
    fixes the annotation marks. -/
theorem annMark_sbD (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) (w : Bool)
    (ann : Option (StandardElm.Src.BTy × List BVar)) : (annMark w ann).map (rsb s) = annMark w ann := by
  cases w <;> simp only [annMark]
  · rfl
  · split
    · rfl
    · simp [annSentinel, rsb, RSub.tl, hs, rsbRow, mrg_nil_right]

theorem annSentinel_not_okTD {n : Nat} : ¬ OkTD n annSentinel := fun h => by
  have := (h (.row (.bnd 0)) (by simp [annSentinel, Ty.vars, Ty.rowVars])).1; simp [BVar.isBnd] at this

theorem annU_of_okAD {n : Nat} {ann : Option (StandardElm.Src.BTy × List BVar)} (h : ∀ τ ∈ annMark true ann, OkTD n τ) :
    annU ann = [] := by
  simp only [annMark] at h
  split at h
  · assumption
  · exact absurd (h _ (.head _)) annSentinel_not_okTD
/-! ## Substitution and strip -/

mutual
theorem tysAtPat_sbD (s : RSub) : ∀ p : AAtPat, tysAtPat (rsbAtPat s p) = (tysAtPat p).map (rsb s)
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit => rfl
  | .tuple p1 p2 p3 => by
    simp only [rsbAtPat, tysAtPat, tysPat_sbD s p1, tysPat_sbD s p2, tysPatOpt_sbD s p3, List.map_append]
  | .record r _ => by simp only [rsbAtPat, tysAtPat, tysPatRowOpt_sbD s r, List.map_cons]
  | .paren p => by simp only [rsbAtPat, tysAtPat, tysPat_sbD s p]
theorem tysPatRow_sbD (s : RSub) : ∀ r : APatRow, tysPatRow (rsbPatRow s r) = (tysPatRow r).map (rsb s)
  | .field _ _ rest => by simp only [rsbPatRow, tysPatRow, tysPatRowOpt_sbD s rest, List.map_cons]
theorem tysPatRowOpt_sbD (s : RSub) : ∀ r : Option APatRow, tysPatRowOpt (rsbPatRowOpt s r) = (tysPatRowOpt r).map (rsb s)
  | none => rfl
  | some r => by simp only [rsbPatRowOpt, tysPatRowOpt, tysPatRow_sbD s r]
theorem tysPat_sbD (s : RSub) : ∀ p : APat, tysPat (rsbPat s p) = (tysPat p).map (rsb s)
  | .atpat a => by simp only [rsbPat, tysPat, tysAtPat_sbD s a]
  | .con _ _ args _ => by simp only [rsbPat, tysPat, tysAtPats_sbD s args, List.map_cons]
  | .cons p1 p2 => by simp only [rsbPat, tysPat, tysPat_sbD s p1, tysPat_sbD s p2, List.map_append]
  | .as p _ => by simp only [rsbPat, tysPat, tysPat_sbD s p]
theorem tysPatOpt_sbD (s : RSub) : ∀ p : Option APat, tysPatOpt (rsbPatOpt s p) = (tysPatOpt p).map (rsb s)
  | none => rfl
  | some p => by simp only [rsbPatOpt, tysPatOpt, tysPat_sbD s p]
theorem tysAtPats_sbD (s : RSub) : ∀ l : List AAtPat, tysAtPats (rsbAtPats s l) = (tysAtPats l).map (rsb s)
  | [] => rfl
  | a :: as => by simp only [rsbAtPats, tysAtPats, tysAtPat_sbD s a, tysAtPats_sbD s as, List.map_append]
end

theorem veBodies_sbD (s : RSub) (VE : ValEnv) : veBodies (rsbVE s VE) = (veBodies VE).map (rsb s) := by
  simp [veBodies, rsbVE, rsbScheme]

mutual
theorem tysAtExp_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ a : AAtExp, tysAtExp w (rsbAtExp s a) = (tysAtExp w a).map (rsb s)
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [rsbAtExp, tysAtExp, tysExp_sbD w s hs e1, tysExp_sbD w s hs e2, tysExpOpt_sbD w s hs e3, List.map_append]
  | .record r => by simp only [rsbAtExp, tysAtExp, tysExpRowOpt_sbD w s hs r]
  | .update _ _ _ r => by simp only [rsbAtExp, tysAtExp, tysExpRow_sbD w s hs r, List.map_cons]
  | .letE d e => by simp only [rsbAtExp, tysAtExp, tysDec_sbD w s hs d, tysExp_sbD w s hs e, List.map_append]
  | .paren e => by simp only [rsbAtExp, tysAtExp, tysExp_sbD w s hs e]
theorem tysExpRow_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ r : AExpRow, tysExpRow w (rsbExpRow s r) = (tysExpRow w r).map (rsb s)
  | .field _ e rest => by simp only [rsbExpRow, tysExpRow, tysExp_sbD w s hs e, tysExpRowOpt_sbD w s hs rest, List.map_append]
theorem tysExpRowOpt_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ r : Option AExpRow,
    tysExpRowOpt w (rsbExpRowOpt s r) = (tysExpRowOpt w r).map (rsb s)
  | none => rfl
  | some r => by simp only [rsbExpRowOpt, tysExpRowOpt, tysExpRow_sbD w s hs r]
theorem tysExp_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ e : AExp, tysExp w (rsbExp s e) = (tysExp w e).map (rsb s)
  | .atexp a => by simp only [rsbExp, tysExp, tysAtExp_sbD w s hs a]
  | .app e a => by simp only [rsbExp, tysExp, tysExp_sbD w s hs e, tysAtExp_sbD w s hs a, List.map_append]
  | .lam p e => by simp only [rsbExp, tysExp, tysAtPat_sbD s p, tysExp_sbD w s hs e, List.map_append]
  | .caseE e m => by simp only [rsbExp, tysExp, tysExp_sbD w s hs e, tysMatch_sbD w s hs m, List.map_append]
theorem tysExpOpt_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ e : Option AExp, tysExpOpt w (rsbExpOpt s e) = (tysExpOpt w e).map (rsb s)
  | none => rfl
  | some e => by simp only [rsbExpOpt, tysExpOpt, tysExp_sbD w s hs e]
theorem tysMatch_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ m : AMatch, tysMatch w (rsbMatch s m) = (tysMatch w m).map (rsb s)
  | .mk mr rest => by simp only [rsbMatch, tysMatch, tysMRule_sbD w s hs mr, tysMatchOpt_sbD w s hs rest, List.map_append]
theorem tysMatchOpt_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ m : Option AMatch, tysMatchOpt w (rsbMatchOpt s m) = (tysMatchOpt w m).map (rsb s)
  | none => rfl
  | some m => by simp only [rsbMatchOpt, tysMatchOpt, tysMatch_sbD w s hs m]
theorem tysMRule_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ mr : AMRule, tysMRule w (rsbMRule s mr) = (tysMRule w mr).map (rsb s)
  | .mk p e => by simp only [rsbMRule, tysMRule, tysPat_sbD s p, tysExp_sbD w s hs e, List.map_append]
theorem tysDec_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ d : ADec, tysDec w (rsbDec s d) = (tysDec w d).map (rsb s)
  | .val VE vb => by
    cases w <;> simp only [rsbDec, tysDec, tysValBind_sbD _ s hs vb, List.map_append, veBodies_sbD, Bool.false_eq_true,
      ↓reduceIte, List.map_nil]
theorem tysValBind_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ vb : AValBind, tysValBind w (rsbValBind s vb) = (tysValBind w vb).map (rsb s)
  | .var _ ann _ e rest => by
    simp only [rsbValBind, tysValBind, tysExp_sbD w s hs e, tysValBindOpt_sbD w s hs rest, List.map_append, List.map_cons,
      List.cons_append, annMark_sbD s hs]
  | .pat p e => by simp only [rsbValBind, tysValBind, tysAtPat_sbD s p, tysExp_sbD w s hs e, List.map_append]
theorem tysValBindOpt_sbD (w : Bool) (s : RSub) (hs : s.r (.bnd 0) = ([], some (.bnd 0))) : ∀ vb : Option AValBind,
    tysValBindOpt w (rsbValBindOpt s vb) = (tysValBindOpt w vb).map (rsb s)
  | none => rfl
  | some vb => by simp only [rsbValBindOpt, tysValBindOpt, tysValBind_sbD w s hs vb]
end
/-! ## Congruence: substitutions agreeing on the types give the same phrase -/

/-- Agreement of two substitutions on a list of types. -/
def AgreeOnD (s t : RSub) (l : List Ty) : Prop := ∀ τ ∈ l, rsb s τ = rsb t τ

theorem AgreeOnD.app {s t : RSub} {l1 l2 : List Ty} (h : AgreeOnD s t (l1 ++ l2)) : AgreeOnD s t l1 ∧ AgreeOnD s t l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩

theorem AgreeOnD.cons {s t : RSub} {τ : Ty} {l : List Ty} (h : AgreeOnD s t (τ :: l)) : rsb s τ = rsb t τ ∧ AgreeOnD s t l :=
  ⟨h τ (.head _), fun x hx => h x (.tail _ hx)⟩

theorem rsbVE_congrD {s t : RSub} {VE : ValEnv} (h : AgreeOnD s t (veBodies VE)) : rsbVE s VE = rsbVE t VE := by
  induction VE with
  | nil => rfl
  | cons p r ih =>
    simp only [veBodies, List.map_cons] at h
    obtain ⟨h1, h2⟩ := AgreeOnD.cons h
    simp only [rsbVE, List.map_cons] at ih ⊢
    rw [ih h2]; simp [rsbScheme, h1]

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

end StandardElm.Stat.Complete
