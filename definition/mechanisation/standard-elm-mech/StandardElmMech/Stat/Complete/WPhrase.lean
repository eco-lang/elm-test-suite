/-
  A Standard Definition of Elm? Mechanisation: the types an annotated phrase records, for the main
  induction L11 of plan step 11 (milestone (b), section 8).

  `tysExp w a`: the types at the leaves and binders of `a`, without the instance lists, and with
  the value environments of its declarations when `w` is true. W's output has all of them
  `OkT`; a derivation compared with it has no `bnd` variable in them (without the declarations'
  environments, which may hold canonical schemes of annotations). Lemmas: they commute with
  substitution and with `strip`; two substitutions agreeing on them give the same phrase (with
  the instance lists left out); the value environment of a pattern is made of monotypes over
  the pattern's types.
-/
import StandardElmMech.Stat.Complete.Closure

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

/-! ## The types of a phrase -/

mutual
def tysAtPat : AAtPat → List Ty
  | .wild τ | .scon _ τ | .var _ τ | .con _ _ τ | .nil τ => [τ]
  | .unit => []
  | .tuple p1 p2 p3 => tysPat p1 ++ tysPat p2 ++ tysPatOpt p3
  | .record row τ => τ :: tysPatRowOpt row
  | .paren p => tysPat p
def tysPatRow : APatRow → List Ty
  | .field _ τ rest => τ :: tysPatRowOpt rest
def tysPatRowOpt : Option APatRow → List Ty
  | none => []
  | some r => tysPatRow r
def tysPat : APat → List Ty
  | .atpat a => tysAtPat a
  | .con _ _ args τ => τ :: tysAtPats args
  | .cons p1 p2 => tysPat p1 ++ tysPat p2
  | .as p _ => tysPat p
def tysPatOpt : Option APat → List Ty
  | none => []
  | some p => tysPat p
def tysAtPats : List AAtPat → List Ty
  | [] => []
  | a :: as => tysAtPat a ++ tysAtPats as
end

def veBodies (VE : ValEnv) : List Ty := VE.map (·.2.1.body)

/-- A type that is never `OkT` (it has a row variable): marks, in `tysExp true`, an annotation
    with explicit variables (W gives none). -/
def annSentinel : Ty := .record [] (some (.bnd 0))

def annMark : Bool → Option (StandardElm.Src.BTy × List BVar) → List Ty
  | false, _ => []
  | true, ann => if annU ann = [] then [] else [annSentinel]

theorem annMark_sb (s : FSub) (w : Bool) (ann : Option (StandardElm.Src.BTy × List BVar)) :
    (annMark w ann).map (sb s) = annMark w ann := by
  cases w <;> simp only [annMark]
  · rfl
  · split <;> rfl

theorem annSentinel_not_okT {n : Nat} : ¬ OkT n annSentinel := fun h => by
  obtain ⟨_, e, _⟩ := h (.row (.bnd 0)) (by simp [annSentinel, Ty.vars, Ty.rowVars]); cases e

theorem annU_of_okA {n : Nat} {ann : Option (StandardElm.Src.BTy × List BVar)} (h : ∀ τ ∈ annMark true ann, OkT n τ) :
    annU ann = [] := by
  simp only [annMark] at h
  split at h
  · assumption
  · exact absurd (h _ (.head _)) annSentinel_not_okT

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
  | .val VE vb => (if w then veBodies VE else []) ++ tysValBind w vb
def tysValBind (w : Bool) : AValBind → List Ty
  | .var _ ann τ e rest => τ :: annMark w ann ++ tysExp w e ++ tysValBindOpt w rest
  | .pat p e => tysAtPat p ++ tysExp w e
def tysValBindOpt (w : Bool) : Option AValBind → List Ty
  | none => []
  | some vb => tysValBind w vb
end

/-! ## Substitution and strip -/

mutual
theorem tysAtPat_sb (s : FSub) : ∀ p : AAtPat, tysAtPat (sbAtPat s p) = (tysAtPat p).map (sb s)
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit => rfl
  | .tuple p1 p2 p3 => by
    simp only [sbAtPat, tysAtPat, tysPat_sb s p1, tysPat_sb s p2, tysPatOpt_sb s p3, List.map_append]
  | .record r _ => by simp only [sbAtPat, tysAtPat, tysPatRowOpt_sb s r, List.map_cons]
  | .paren p => by simp only [sbAtPat, tysAtPat, tysPat_sb s p]
theorem tysPatRow_sb (s : FSub) : ∀ r : APatRow, tysPatRow (sbPatRow s r) = (tysPatRow r).map (sb s)
  | .field _ _ rest => by simp only [sbPatRow, tysPatRow, tysPatRowOpt_sb s rest, List.map_cons]
theorem tysPatRowOpt_sb (s : FSub) : ∀ r : Option APatRow, tysPatRowOpt (sbPatRowOpt s r) = (tysPatRowOpt r).map (sb s)
  | none => rfl
  | some r => by simp only [sbPatRowOpt, tysPatRowOpt, tysPatRow_sb s r]
theorem tysPat_sb (s : FSub) : ∀ p : APat, tysPat (sbPat s p) = (tysPat p).map (sb s)
  | .atpat a => by simp only [sbPat, tysPat, tysAtPat_sb s a]
  | .con _ _ args _ => by simp only [sbPat, tysPat, tysAtPats_sb s args, List.map_cons]
  | .cons p1 p2 => by simp only [sbPat, tysPat, tysPat_sb s p1, tysPat_sb s p2, List.map_append]
  | .as p _ => by simp only [sbPat, tysPat, tysPat_sb s p]
theorem tysPatOpt_sb (s : FSub) : ∀ p : Option APat, tysPatOpt (sbPatOpt s p) = (tysPatOpt p).map (sb s)
  | none => rfl
  | some p => by simp only [sbPatOpt, tysPatOpt, tysPat_sb s p]
theorem tysAtPats_sb (s : FSub) : ∀ l : List AAtPat, tysAtPats (sbAtPats s l) = (tysAtPats l).map (sb s)
  | [] => rfl
  | a :: as => by simp only [sbAtPats, tysAtPats, tysAtPat_sb s a, tysAtPats_sb s as, List.map_append]
end

theorem veBodies_sb (s : FSub) (VE : ValEnv) : veBodies (sbVE s VE) = (veBodies VE).map (sb s) := by
  simp [veBodies, sbVE, sbScheme]

mutual
theorem tysAtExp_sb (w : Bool) (s : FSub) : ∀ a : AAtExp, tysAtExp w (sbAtExp s a) = (tysAtExp w a).map (sb s)
  | .scon _ _ | .var _ _ _ | .con _ _ _ | .op _ _ _ | .nil _ | .unit => rfl
  | .tuple e1 e2 e3 => by
    simp only [sbAtExp, tysAtExp, tysExp_sb w s e1, tysExp_sb w s e2, tysExpOpt_sb w s e3, List.map_append]
  | .record r => by simp only [sbAtExp, tysAtExp, tysExpRowOpt_sb w s r]
  | .update _ _ _ r => by simp only [sbAtExp, tysAtExp, tysExpRow_sb w s r, List.map_cons]
  | .letE d e => by simp only [sbAtExp, tysAtExp, tysDec_sb w s d, tysExp_sb w s e, List.map_append]
  | .paren e => by simp only [sbAtExp, tysAtExp, tysExp_sb w s e]
theorem tysExpRow_sb (w : Bool) (s : FSub) : ∀ r : AExpRow, tysExpRow w (sbExpRow s r) = (tysExpRow w r).map (sb s)
  | .field _ e rest => by simp only [sbExpRow, tysExpRow, tysExp_sb w s e, tysExpRowOpt_sb w s rest, List.map_append]
theorem tysExpRowOpt_sb (w : Bool) (s : FSub) : ∀ r : Option AExpRow,
    tysExpRowOpt w (sbExpRowOpt s r) = (tysExpRowOpt w r).map (sb s)
  | none => rfl
  | some r => by simp only [sbExpRowOpt, tysExpRowOpt, tysExpRow_sb w s r]
theorem tysExp_sb (w : Bool) (s : FSub) : ∀ e : AExp, tysExp w (sbExp s e) = (tysExp w e).map (sb s)
  | .atexp a => by simp only [sbExp, tysExp, tysAtExp_sb w s a]
  | .app e a => by simp only [sbExp, tysExp, tysExp_sb w s e, tysAtExp_sb w s a, List.map_append]
  | .lam p e => by simp only [sbExp, tysExp, tysAtPat_sb s p, tysExp_sb w s e, List.map_append]
  | .caseE e m => by simp only [sbExp, tysExp, tysExp_sb w s e, tysMatch_sb w s m, List.map_append]
theorem tysExpOpt_sb (w : Bool) (s : FSub) : ∀ e : Option AExp, tysExpOpt w (sbExpOpt s e) = (tysExpOpt w e).map (sb s)
  | none => rfl
  | some e => by simp only [sbExpOpt, tysExpOpt, tysExp_sb w s e]
theorem tysMatch_sb (w : Bool) (s : FSub) : ∀ m : AMatch, tysMatch w (sbMatch s m) = (tysMatch w m).map (sb s)
  | .mk mr rest => by simp only [sbMatch, tysMatch, tysMRule_sb w s mr, tysMatchOpt_sb w s rest, List.map_append]
theorem tysMatchOpt_sb (w : Bool) (s : FSub) : ∀ m : Option AMatch, tysMatchOpt w (sbMatchOpt s m) = (tysMatchOpt w m).map (sb s)
  | none => rfl
  | some m => by simp only [sbMatchOpt, tysMatchOpt, tysMatch_sb w s m]
theorem tysMRule_sb (w : Bool) (s : FSub) : ∀ mr : AMRule, tysMRule w (sbMRule s mr) = (tysMRule w mr).map (sb s)
  | .mk p e => by simp only [sbMRule, tysMRule, tysPat_sb s p, tysExp_sb w s e, List.map_append]
theorem tysDec_sb (w : Bool) (s : FSub) : ∀ d : ADec, tysDec w (sbDec s d) = (tysDec w d).map (sb s)
  | .val VE vb => by
    cases w <;> simp only [sbDec, tysDec, tysValBind_sb _ s vb, List.map_append, veBodies_sb, Bool.false_eq_true,
      ↓reduceIte, List.map_nil]
theorem tysValBind_sb (w : Bool) (s : FSub) : ∀ vb : AValBind, tysValBind w (sbValBind s vb) = (tysValBind w vb).map (sb s)
  | .var _ ann _ e rest => by
    simp only [sbValBind, tysValBind, tysExp_sb w s e, tysValBindOpt_sb w s rest, List.map_append, List.map_cons,
      List.cons_append, annMark_sb]
  | .pat p e => by simp only [sbValBind, tysValBind, tysAtPat_sb s p, tysExp_sb w s e, List.map_append]
theorem tysValBindOpt_sb (w : Bool) (s : FSub) : ∀ vb : Option AValBind,
    tysValBindOpt w (sbValBindOpt s vb) = (tysValBindOpt w vb).map (sb s)
  | none => rfl
  | some vb => by simp only [sbValBindOpt, tysValBindOpt, tysValBind_sb w s vb]
end

mutual
theorem tysAtPat_strip : ∀ p : AAtPat, tysAtPat (stripAtPat p) = tysAtPat p
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit | .record _ _ => rfl
  | .tuple p1 p2 p3 => by simp only [stripAtPat, tysAtPat, tysPat_strip p1, tysPat_strip p2, tysPatOpt_strip p3]
  | .paren p => by simp only [stripAtPat, tysAtPat, tysPat_strip p]
theorem tysPat_strip : ∀ p : APat, tysPat (stripPat p) = tysPat p
  | .atpat a => by simp only [stripPat, tysPat, tysAtPat_strip a]
  | .con _ _ args _ => by simp only [stripPat, tysPat, tysAtPats_strip args]
  | .cons p1 p2 => by simp only [stripPat, tysPat, tysPat_strip p1, tysPat_strip p2]
  | .as p _ => by simp only [stripPat, tysPat, tysPat_strip p]
theorem tysPatOpt_strip : ∀ p : Option APat, tysPatOpt (stripPatOpt p) = tysPatOpt p
  | none => rfl
  | some p => by simp only [stripPatOpt, tysPatOpt, tysPat_strip p]
theorem tysAtPats_strip : ∀ l : List AAtPat, tysAtPats (stripAtPats l) = tysAtPats l
  | [] => rfl
  | a :: as => by simp only [stripAtPats, tysAtPats, tysAtPat_strip a, tysAtPats_strip as]
end

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

/-! ## Congruence: substitutions agreeing on the types give the same phrase -/

/-- Agreement of two substitutions on a list of types. -/
def AgreeOn (s t : FSub) (l : List Ty) : Prop := ∀ τ ∈ l, sb s τ = sb t τ

theorem AgreeOn.app {s t : FSub} {l1 l2 : List Ty} (h : AgreeOn s t (l1 ++ l2)) : AgreeOn s t l1 ∧ AgreeOn s t l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩

theorem AgreeOn.cons {s t : FSub} {τ : Ty} {l : List Ty} (h : AgreeOn s t (τ :: l)) : sb s τ = sb t τ ∧ AgreeOn s t l :=
  ⟨h τ (.head _), fun x hx => h x (.tail _ hx)⟩

theorem sbVE_congr {s t : FSub} {VE : ValEnv} (h : AgreeOn s t (veBodies VE)) : sbVE s VE = sbVE t VE := by
  induction VE with
  | nil => rfl
  | cons p r ih =>
    simp only [veBodies, List.map_cons] at h
    obtain ⟨h1, h2⟩ := AgreeOn.cons h
    simp only [sbVE, List.map_cons] at ih ⊢
    rw [ih h2]; simp [sbScheme, h1]

mutual
theorem sbAtPat_congr {s t : FSub} : ∀ p : AAtPat, AgreeOn s t (tysAtPat p) →
    stripAtPat (sbAtPat s p) = stripAtPat (sbAtPat t p)
  | .wild _, h | .scon _ _, h | .var _ _, h | .con _ _ _, h | .nil _, h => by
    simp only [tysAtPat] at h; simp [sbAtPat, stripAtPat, (AgreeOn.cons h).1]
  | .unit, _ => rfl
  | .tuple p1 p2 p3, h => by
    simp only [tysAtPat] at h
    obtain ⟨h12, h3⟩ := AgreeOn.app h; obtain ⟨h1, h2⟩ := AgreeOn.app h12
    simp only [sbAtPat, stripAtPat, sbPat_congr p1 h1, sbPat_congr p2 h2, sbPatOpt_congr p3 h3]
  | .record r _, h => by
    simp only [tysAtPat] at h
    obtain ⟨h1, h2⟩ := AgreeOn.cons h
    simp only [sbAtPat, stripAtPat, h1, sbPatRowOpt_congr r h2]
  | .paren p, h => by simp only [tysAtPat] at h; simp only [sbAtPat, stripAtPat, sbPat_congr p h]
theorem sbPatRowOpt_congr {s t : FSub} : ∀ r : Option APatRow, AgreeOn s t (tysPatRowOpt r) →
    sbPatRowOpt s r = sbPatRowOpt t r
  | none, _ => rfl
  | some (.field l τ rest), h => by
    simp only [tysPatRowOpt, tysPatRow] at h
    obtain ⟨h1, h2⟩ := AgreeOn.cons h
    simp only [sbPatRowOpt, sbPatRow, h1, sbPatRowOpt_congr rest h2]
theorem sbPat_congr {s t : FSub} : ∀ p : APat, AgreeOn s t (tysPat p) → stripPat (sbPat s p) = stripPat (sbPat t p)
  | .atpat a, h => by simp only [tysPat] at h; simp only [sbPat, stripPat, sbAtPat_congr a h]
  | .con _ _ args _, h => by
    simp only [tysPat] at h
    obtain ⟨h1, h2⟩ := AgreeOn.cons h
    simp only [sbPat, stripPat, h1, sbAtPats_congr args h2]
  | .cons p1 p2, h => by
    simp only [tysPat] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbPat, stripPat, sbPat_congr p1 h1, sbPat_congr p2 h2]
  | .as p _, h => by simp only [tysPat] at h; simp only [sbPat, stripPat, sbPat_congr p h]
theorem sbPatOpt_congr {s t : FSub} : ∀ p : Option APat, AgreeOn s t (tysPatOpt p) →
    stripPatOpt (sbPatOpt s p) = stripPatOpt (sbPatOpt t p)
  | none, _ => rfl
  | some p, h => by simp only [tysPatOpt] at h; simp only [sbPatOpt, stripPatOpt, sbPat_congr p h]
theorem sbAtPats_congr {s t : FSub} : ∀ l : List AAtPat, AgreeOn s t (tysAtPats l) →
    stripAtPats (sbAtPats s l) = stripAtPats (sbAtPats t l)
  | [], _ => rfl
  | a :: as, h => by
    simp only [tysAtPats] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbAtPats, stripAtPats, sbAtPat_congr a h1, sbAtPats_congr as h2]
end

mutual
theorem sbAtExp_congr {s t : FSub} : ∀ a : AAtExp, AgreeOn s t (tysAtExp true a) →
    stripAtExp (sbAtExp s a) = stripAtExp (sbAtExp t a)
  | .scon _ _, h | .var _ _ _, h | .con _ _ _, h | .op _ _ _, h | .nil _, h => by
    simp only [tysAtExp] at h; simp [sbAtExp, stripAtExp, (AgreeOn.cons h).1]
  | .unit, _ => rfl
  | .tuple e1 e2 e3, h => by
    simp only [tysAtExp] at h
    obtain ⟨h12, h3⟩ := AgreeOn.app h; obtain ⟨h1, h2⟩ := AgreeOn.app h12
    simp only [sbAtExp, stripAtExp, sbExp_congr e1 h1, sbExp_congr e2 h2, sbExpOpt_congr e3 h3]
  | .record r, h => by simp only [tysAtExp] at h; simp only [sbAtExp, stripAtExp, sbExpRowOpt_congr r h]
  | .update _ _ _ r, h => by
    simp only [tysAtExp] at h
    obtain ⟨h1, h2⟩ := AgreeOn.cons h
    simp only [sbAtExp, stripAtExp, h1, sbExpRow_congr r h2]
  | .letE d e, h => by
    simp only [tysAtExp] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbAtExp, stripAtExp, sbDec_congr d h1, sbExp_congr e h2]
  | .paren e, h => by simp only [tysAtExp] at h; simp only [sbAtExp, stripAtExp, sbExp_congr e h]
theorem sbExpRow_congr {s t : FSub} : ∀ r : AExpRow, AgreeOn s t (tysExpRow true r) →
    stripExpRow (sbExpRow s r) = stripExpRow (sbExpRow t r)
  | .field _ e rest, h => by
    simp only [tysExpRow] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbExpRow, stripExpRow, sbExp_congr e h1, sbExpRowOpt_congr rest h2]
theorem sbExpRowOpt_congr {s t : FSub} : ∀ r : Option AExpRow, AgreeOn s t (tysExpRowOpt true r) →
    stripExpRowOpt (sbExpRowOpt s r) = stripExpRowOpt (sbExpRowOpt t r)
  | none, _ => rfl
  | some r, h => by simp only [tysExpRowOpt] at h; simp only [sbExpRowOpt, stripExpRowOpt, sbExpRow_congr r h]
theorem sbExp_congr {s t : FSub} : ∀ e : AExp, AgreeOn s t (tysExp true e) →
    stripExp (sbExp s e) = stripExp (sbExp t e)
  | .atexp a, h => by simp only [tysExp] at h; simp only [sbExp, stripExp, sbAtExp_congr a h]
  | .app e a, h => by
    simp only [tysExp] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbExp, stripExp, sbExp_congr e h1, sbAtExp_congr a h2]
  | .lam p e, h => by
    simp only [tysExp] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbExp, stripExp, sbAtPat_congr p h1, sbExp_congr e h2]
  | .caseE e m, h => by
    simp only [tysExp] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbExp, stripExp, sbExp_congr e h1, sbMatch_congr m h2]
theorem sbExpOpt_congr {s t : FSub} : ∀ e : Option AExp, AgreeOn s t (tysExpOpt true e) →
    stripExpOpt (sbExpOpt s e) = stripExpOpt (sbExpOpt t e)
  | none, _ => rfl
  | some e, h => by simp only [tysExpOpt] at h; simp only [sbExpOpt, stripExpOpt, sbExp_congr e h]
theorem sbMatch_congr {s t : FSub} : ∀ m : AMatch, AgreeOn s t (tysMatch true m) →
    stripMatch (sbMatch s m) = stripMatch (sbMatch t m)
  | .mk mr rest, h => by
    simp only [tysMatch] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbMatch, stripMatch, sbMRule_congr mr h1, sbMatchOpt_congr rest h2]
theorem sbMatchOpt_congr {s t : FSub} : ∀ m : Option AMatch, AgreeOn s t (tysMatchOpt true m) →
    stripMatchOpt (sbMatchOpt s m) = stripMatchOpt (sbMatchOpt t m)
  | none, _ => rfl
  | some m, h => by simp only [tysMatchOpt] at h; simp only [sbMatchOpt, stripMatchOpt, sbMatch_congr m h]
theorem sbMRule_congr {s t : FSub} : ∀ mr : AMRule, AgreeOn s t (tysMRule true mr) →
    stripMRule (sbMRule s mr) = stripMRule (sbMRule t mr)
  | .mk p e, h => by
    simp only [tysMRule] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbMRule, stripMRule, sbPat_congr p h1, sbExp_congr e h2]
theorem sbDec_congr {s t : FSub} : ∀ d : ADec, AgreeOn s t (tysDec true d) →
    stripDec (sbDec s d) = stripDec (sbDec t d)
  | .val VE vb, h => by
    simp only [tysDec, ↓reduceIte] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbDec, stripDec, sbVE_congr h1, sbValBind_congr vb h2]
theorem sbValBind_congr {s t : FSub} : ∀ vb : AValBind, AgreeOn s t (tysValBind true vb) →
    stripValBind (sbValBind s vb) = stripValBind (sbValBind t vb)
  | .var _ _ _ e rest, h => by
    simp only [tysValBind, List.cons_append] at h
    obtain ⟨h0, h⟩ := AgreeOn.cons h
    obtain ⟨h12, h2⟩ := AgreeOn.app h
    obtain ⟨-, h1⟩ := AgreeOn.app h12
    simp only [sbValBind, stripValBind, h0, sbExp_congr e h1, sbValBindOpt_congr rest h2]
  | .pat p e, h => by
    simp only [tysValBind] at h
    obtain ⟨h1, h2⟩ := AgreeOn.app h
    simp only [sbValBind, stripValBind, sbAtPat_congr p h1, sbExp_congr e h2]
theorem sbValBindOpt_congr {s t : FSub} : ∀ vb : Option AValBind, AgreeOn s t (tysValBindOpt true vb) →
    stripValBindOpt (sbValBindOpt s vb) = stripValBindOpt (sbValBindOpt t vb)
  | none, _ => rfl
  | some vb, h => by simp only [tysValBindOpt] at h; simp only [sbValBindOpt, stripValBindOpt, sbValBind_congr vb h]
end

/-! ## Value environments of patterns -/

theorem mem_modify {p : String × (Scheme × IdStatus)} {f g : ValEnv} (h : p ∈ FMap.modify f g) : p ∈ f ∨ p ∈ g := by
  simp only [FMap.modify, List.mem_append, List.mem_filter] at h
  rcases h with h | ⟨h, _⟩
  · exact .inr h
  · exact .inl h

theorem mem_plusAll {p : String × (Scheme × IdStatus)} : ∀ {l : List ValEnv} {acc : ValEnv},
    p ∈ l.foldl FMap.modify acc → p ∈ acc ∨ ∃ VE ∈ l, p ∈ VE
  | [], _, h => .inl h
  | VE :: l, acc, h => by
    simp only [List.foldl_cons] at h
    rcases mem_plusAll h with h | ⟨VE', hl, h⟩
    · rcases mem_modify h with h | h
      · exact .inl h
      · exact .inr ⟨VE, .head _, h⟩
    · exact .inr ⟨VE', .tail _ hl, h⟩

/-- An entry of a pattern's environment: a monotype, of status v, whose variables are variables of
    the pattern's types. -/
def PEnt (l : List Ty) (p : String × (Scheme × IdStatus)) : Prop :=
  p.2.1.bound = [] ∧ p.2.2 = .v ∧ ∀ v ∈ p.2.1.body.vars, ∃ τ ∈ l, v ∈ τ.vars

theorem PEnt.mono {l l' : List Ty} (h : ∀ τ ∈ l, τ ∈ l') {p : String × (Scheme × IdStatus)} (hp : PEnt l p) :
    PEnt l' p := ⟨hp.1, hp.2.1, fun v hv => by obtain ⟨τ, h1, h2⟩ := hp.2.2 v hv; exact ⟨τ, h _ h1, h2⟩⟩

theorem vars_tupleTy {v : BVar} {τ1 τ2 : Ty} {τ3 : Option Ty} (h : v ∈ (tupleTy τ1 τ2 τ3).vars) :
    v ∈ τ1.vars ∨ v ∈ τ2.vars ∨ ∃ τ, τ3 = some τ ∧ v ∈ τ.vars := by
  cases τ3 <;> simp_all [tupleTy, Ty.vars, Ty.listVars]

mutual
theorem atpat_ty_vars : ∀ (p : AAtPat), ∀ v ∈ p.ty.vars, ∃ τ ∈ tysAtPat p, v ∈ τ.vars
  | .wild _, v, h | .scon _ _, v, h | .var _ _, v, h | .con _ _ _, v, h | .nil _, v, h =>
    ⟨_, .head _, h⟩
  | .record _ _, v, h => ⟨_, .head _, h⟩
  | .unit, v, h => by simp [AAtPat.ty, tUnitTy, Ty.vars, Ty.listVars] at h
  | .tuple p1 p2 p3, v, h => by
    simp only [AAtPat.ty] at h
    rcases vars_tupleTy h with h | h | ⟨τ, e, h⟩
    · obtain ⟨τ, h1, h2⟩ := pat_ty_vars p1 v h; exact ⟨τ, by simp [tysAtPat, h1], h2⟩
    · obtain ⟨τ, h1, h2⟩ := pat_ty_vars p2 v h; exact ⟨τ, by simp [tysAtPat, h1], h2⟩
    · cases p3 with
      | none => cases e
      | some p3 =>
        simp only [APat.tyOpt, Option.some.injEq] at e; subst e
        obtain ⟨τ, h1, h2⟩ := pat_ty_vars p3 v h; exact ⟨τ, by simp [tysAtPat, tysPatOpt, h1], h2⟩
  | .paren p, v, h => by simp only [AAtPat.ty] at h; simpa [tysAtPat] using pat_ty_vars p v h
theorem pat_ty_vars : ∀ (p : APat), ∀ v ∈ p.ty.vars, ∃ τ ∈ tysPat p, v ∈ τ.vars
  | .atpat a, v, h => by simp only [APat.ty] at h; simpa [tysPat] using atpat_ty_vars a v h
  | .con _ _ _ _, v, h => ⟨_, .head _, h⟩
  | .cons p1 _, v, h => by
    simp only [APat.ty, listTy, Ty.vars, Ty.listVars, List.append_nil] at h
    obtain ⟨τ, h1, h2⟩ := pat_ty_vars p1 v h; exact ⟨τ, by simp [tysPat, h1], h2⟩
  | .as p _, v, h => by simp only [APat.ty] at h; simpa [tysPat] using pat_ty_vars p v h
end

mutual
theorem atpat_ve : ∀ (p : AAtPat), ∀ q ∈ p.ve, PEnt (tysAtPat p) q
  | .wild _, q, h | .scon _ _, q, h | .con _ _ _, q, h | .nil _, q, h | .unit, q, h => by
    simp [AAtPat.ve] at h
  | .var x τ, q, h => by
    simp only [AAtPat.ve, List.mem_singleton] at h; subst h
    exact ⟨rfl, rfl, fun v hv => ⟨τ, .head _, hv⟩⟩
  | .tuple p1 p2 p3, q, h => by
    simp only [AAtPat.ve] at h
    rcases mem_modify h with h | h
    · rcases mem_modify h with h | h
      · exact (pat_ve p1 q h).mono (fun τ hτ => by simp [tysAtPat, hτ])
      · exact (pat_ve p2 q h).mono (fun τ hτ => by simp [tysAtPat, hτ])
    · cases p3 with
      | none => simp [APat.veOpt] at h
      | some p3 =>
        simp only [APat.veOpt] at h
        exact (pat_ve p3 q h).mono (fun τ hτ => by simp [tysAtPat, tysPatOpt, hτ])
  | .record r _, q, h => by
    simp only [AAtPat.ve] at h
    exact (patRowOpt_ve r q h).mono (fun τ hτ => by simp [tysAtPat, hτ])
  | .paren p, q, h => by simp only [AAtPat.ve] at h; simpa [tysAtPat] using pat_ve p q h
theorem patRowOpt_ve : ∀ (r : Option APatRow), ∀ q ∈ APatRow.veOpt r, PEnt (tysPatRowOpt r) q
  | none, q, h => by simp [APatRow.veOpt] at h
  | some (.field l τ rest), q, h => by
    simp only [APatRow.veOpt, APatRow.ve] at h
    rcases mem_modify h with h | h
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨rfl, rfl, fun v hv => ⟨τ, by simp [tysPatRowOpt, tysPatRow], hv⟩⟩
    · exact (patRowOpt_ve rest q h).mono (fun x hx => by simp [tysPatRowOpt, tysPatRow, hx])
theorem pat_ve : ∀ (p : APat), ∀ q ∈ p.ve, PEnt (tysPat p) q
  | .atpat a, q, h => by simp only [APat.ve] at h; simpa [tysPat] using atpat_ve a q h
  | .con _ _ args _, q, h => by
    simp only [APat.ve, FMap.plusAll] at h
    rcases mem_plusAll h with h | ⟨VE, hl, h⟩
    · cases h
    · exact (atpats_ve args VE hl q h).mono (fun τ hτ => by simp [tysPat, hτ])
  | .cons p1 p2, q, h => by
    simp only [APat.ve] at h
    rcases mem_modify h with h | h
    · exact (pat_ve p1 q h).mono (fun τ hτ => by simp [tysPat, hτ])
    · exact (pat_ve p2 q h).mono (fun τ hτ => by simp [tysPat, hτ])
  | .as p x, q, h => by
    simp only [APat.ve] at h
    rcases mem_modify h with h | h
    · simpa [tysPat] using pat_ve p q h
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨rfl, rfl, fun v hv => by simpa [tysPat] using pat_ty_vars p v hv⟩
theorem atpats_ve : ∀ (l : List AAtPat), ∀ VE ∈ AAtPat.veList l, ∀ q ∈ VE, PEnt (tysAtPats l) q
  | [], VE, h, _, _ => by simp [AAtPat.veList] at h
  | a :: as, VE, h, q, hq => by
    simp only [AAtPat.veList, List.mem_cons] at h
    rcases h with rfl | h
    · exact (atpat_ve a q hq).mono (fun τ hτ => by simp [tysAtPats, hτ])
    · exact (atpats_ve as VE h q hq).mono (fun τ hτ => by simp [tysAtPats, hτ])
end

/-- A pattern's value environment as a lookup: monotypes of status v over the pattern's types. -/
theorem find?_pat_ve {p : AAtPat} {x : String} {q : Scheme × IdStatus} (h : FMap.find? p.ve x = some q) :
    PEnt (tysAtPat p) (x, q) := atpat_ve p _ (find?_mem h)

mutual
theorem stripAtPat_ve : ∀ p : AAtPat, (stripAtPat p).ve = p.ve
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit | .record _ _ => rfl
  | .tuple p1 p2 p3 => by simp only [stripAtPat, AAtPat.ve, stripPat_ve p1, stripPat_ve p2, stripPatOpt_ve p3]
  | .paren p => by simp only [stripAtPat, AAtPat.ve, stripPat_ve p]
theorem stripPat_ve : ∀ p : APat, (stripPat p).ve = p.ve
  | .atpat a => by simp only [stripPat, APat.ve, stripAtPat_ve a]
  | .con _ _ args _ => by simp only [stripPat, APat.ve, stripAtPats_veList args]
  | .cons p1 p2 => by simp only [stripPat, APat.ve, stripPat_ve p1, stripPat_ve p2]
  | .as p _ => by simp only [stripPat, APat.ve, stripPat_ve p, stripPat_ty p]
theorem stripPatOpt_ve : ∀ p : Option APat, APat.veOpt (stripPatOpt p) = APat.veOpt p
  | none => rfl
  | some p => by simp only [stripPatOpt, APat.veOpt, stripPat_ve p]
theorem stripAtPats_veList : ∀ l : List AAtPat, AAtPat.veList (stripAtPats l) = AAtPat.veList l
  | [] => rfl
  | a :: as => by simp only [stripAtPats, AAtPat.veList, stripAtPat_ve a, stripAtPats_veList as]
theorem stripAtPat_ty : ∀ p : AAtPat, (stripAtPat p).ty = p.ty
  | .wild _ | .scon _ _ | .var _ _ | .con _ _ _ | .nil _ | .unit | .record _ _ => rfl
  | .tuple p1 p2 p3 => by simp only [stripAtPat, AAtPat.ty, stripPat_ty p1, stripPat_ty p2, stripPatOpt_ty p3]
  | .paren p => by simp only [stripAtPat, AAtPat.ty, stripPat_ty p]
theorem stripPat_ty : ∀ p : APat, (stripPat p).ty = p.ty
  | .atpat a => by simp only [stripPat, APat.ty, stripAtPat_ty a]
  | .con _ _ _ _ => rfl
  | .cons p1 _ => by simp only [stripPat, APat.ty, stripPat_ty p1]
  | .as p _ => by simp only [stripPat, APat.ty, stripPat_ty p]
theorem stripPatOpt_ty : ∀ p : Option APat, APat.tyOpt (stripPatOpt p) = APat.tyOpt p
  | none => rfl
  | some p => by simp only [stripPatOpt, APat.tyOpt, stripPat_ty p]
end

end StandardElm.Stat.Complete
