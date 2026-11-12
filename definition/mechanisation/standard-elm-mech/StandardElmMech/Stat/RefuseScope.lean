/-
  A Standard Definition of Elm? Mechanisation: refusals by scope, constructor arity and imports,
  plan step 9 (section 10, group 8).

  A derivation-independent *shape* of a context says, of each long value identifier, whether it is
  bound and, for a constructor, how many arguments it takes. A bare checker (`scExp` and the rest)
  fails when an occurrence of a variable or constructor is unbound in the shape, or a constructor
  pattern has the wrong number of arguments. It is sound for every derivation: whenever the
  checker of annotated phrases accepts a derivation in a context the shape abstracts (`Abs`), the
  bare checker accepts its erasure. So a module the bare checker refuses has no derivation at all.

  The shape of a module's import context is read from the context itself when the basis is
  concrete (`ctxShape`); for the second module of a program it is read from the provider map of its
  imports (`piShape`), which depends on the first module's interface only through a skeleton (its
  type names with their constructors' statuses, and its value names) that is the same in every
  derivation of the first module (`teSkTop`, `exposeItemsSk`).
-/
import StandardElmMech.Stat.Refusals

namespace StandardElm.Stat.RScope
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BTyRow BAtPat BPatRow BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind
  BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule SProgram)

/-! ## Shapes -/

/-- A shape: for each long value identifier, `none` when it is unbound, `some (some n)` for a
    constructor of n arguments, `some none` for any other binding (or an unknown arity). -/
abbrev Shape := LongId → Option (Option Nat)

/-- σ's body is τ1 → ... → τn → τ(k) t. -/
def ArityIs (σ : Scheme) (n : Nat) : Prop :=
  ∃ ks args t, σ.body = arrows ks (.con args t) ∧ ks.length = n

def Valid (a : Option Nat) (b : Scheme × IdStatus) : Prop :=
  ∀ n, a = some n → b.2 = .c → ArityIs b.1 n

/-- The shape Γ abstracts the context C. -/
def Abs (C : Ctx) (Γ : Shape) : Prop :=
  ∀ lid b, C.lookupVal lid = some b → ∃ a, Γ lid = some a ∧ Valid a b

/-- Γ extended by unqualified bindings (the first binding of a name wins). -/
def extT (Γ : Shape) (bs : List (String × Option Nat)) : Shape := fun lid =>
  match lid.qual with
  | none => (FMap.find? bs lid.id).or (Γ lid)
  | some _ => Γ lid

def vs (xs : List String) : List (String × Option Nat) := xs.map fun x => (x, none)

def arityOf : Ty → Option Nat
  | .fn _ t => (arityOf t).map (· + 1)
  | .con _ _ => some 0
  | _ => none

def infoOf (b : Scheme × IdStatus) : Option Nat :=
  match b.2 with
  | .c => arityOf b.1.body
  | .v => none

/-- The shape of a concrete context. -/
def ctxShape (C : Ctx) : Shape := fun lid => (C.lookupVal lid).map infoOf

/-- The shape of the context a provider map gives: every value identifier it provides is bound. -/
def piShape (π : ProvMap) : Shape := fun lid =>
  if (⟨lid.qual, .val lid.id⟩ : SmLongId) ∈ π.keys then some none else none

/-! ## The bare checker -/

mutual
def atPatVars : BAtPat → List String
  | .var x => [x]
  | .tuple p1 p2 p3 => patVars p1 ++ patVars p2 ++ patVarsOpt p3
  | .record row => patRowVarsOpt row
  | .paren p => patVars p
  | .wild | .scon _ | .con _ | .unit | .nil => []
def patRowVars : BPatRow → List String
  | .field l rest => l :: patRowVarsOpt rest
def patRowVarsOpt : Option BPatRow → List String
  | none => []
  | some r => patRowVars r
def patVars : BPat → List String
  | .atpat a => atPatVars a
  | .con _ args => atPatListVars args
  | .cons p1 p2 => patVars p1 ++ patVars p2
  | .as p x => x :: patVars p
def patVarsOpt : Option BPat → List String
  | none => []
  | some p => patVars p
def atPatListVars : List BAtPat → List String
  | [] => []
  | a :: as => atPatVars a ++ atPatListVars as
end

def conOK (Γ : Shape) (lc : LongId) (k : Nat) : Bool :=
  match Γ lc with
  | some (some n) => n == k
  | some none => true
  | none => false

mutual
def scAtPat (Γ : Shape) : BAtPat → Bool
  | .con lc => conOK Γ lc 0
  | .tuple p1 p2 p3 => scPat Γ p1 && scPat Γ p2 && scPatOpt Γ p3
  | .paren p => scPat Γ p
  | .wild | .scon _ | .var _ | .unit | .nil | .record _ => true
def scPat (Γ : Shape) : BPat → Bool
  | .atpat a => scAtPat Γ a
  | .con lc args => conOK Γ lc args.length && scAtPatList Γ args
  | .cons p1 p2 => scPat Γ p1 && scPat Γ p2
  | .as p _ => scPat Γ p
def scPatOpt (Γ : Shape) : Option BPat → Bool
  | none => true
  | some p => scPat Γ p
def scAtPatList (Γ : Shape) : List BAtPat → Bool
  | [] => true
  | a :: as => scAtPat Γ a && scAtPatList Γ as
end

mutual
def scAtExp (Γ : Shape) : BAtExp → Bool
  | .var lv => (Γ lv).isSome
  | .con lc => (Γ lc).isSome
  | .tuple e1 e2 e3 => scExp Γ e1 && scExp Γ e2 && scExpOpt Γ e3
  | .record row => scExpRowOpt Γ row
  | .update x row => (Γ ⟨none, x⟩).isSome && scExpRow Γ row
  | .letE d e => scDec Γ d && scExp (extT Γ (vs (decVars d))) e
  | .paren e => scExp Γ e
  | .scon _ | .op _ | .unit | .nil => true
def scExpRow (Γ : Shape) : BExpRow → Bool
  | .field _ e rest => scExp Γ e && scExpRowOpt Γ rest
def scExpRowOpt (Γ : Shape) : Option BExpRow → Bool
  | none => true
  | some r => scExpRow Γ r
def scExp (Γ : Shape) : BExp → Bool
  | .atexp a => scAtExp Γ a
  | .app e a => scExp Γ e && scAtExp Γ a
  | .lam p e => scAtPat Γ p && scExp (extT Γ (vs (atPatVars p))) e
  | .caseE e m => scExp Γ e && scMatch Γ m
def scExpOpt (Γ : Shape) : Option BExp → Bool
  | none => true
  | some e => scExp Γ e
def scMatch (Γ : Shape) : BMatch → Bool
  | .mk mr rest => scMRule Γ mr && scMatchOpt Γ rest
def scMatchOpt (Γ : Shape) : Option BMatch → Bool
  | none => true
  | some m => scMatch Γ m
def scMRule (Γ : Shape) : BMRule → Bool
  | .mk p e => scPat Γ p && scExp (extT Γ (vs (patVars p))) e
def scDec (Γ : Shape) : BDec → Bool
  | .val vb => scVB (extT Γ (vs (vbVars vb))) vb
def decVars : BDec → List String
  | .val vb => vbVars vb
def scVB (Γ : Shape) : BValBind → Bool
  | .var _ _ e rest => scExp Γ e && scVBOpt Γ rest
  | .pat p e => scAtPat Γ p && scExp Γ e
def scVBOpt (Γ : Shape) : Option BValBind → Bool
  | none => true
  | some vb => scVB Γ vb
def vbVars : BValBind → List String
  | .var x _ _ rest => x :: vbVarsOpt rest
  | .pat p _ => atPatVars p
def vbVarsOpt : Option BValBind → List String
  | none => []
  | some vb => vbVars vb
end

/-! ## Arities -/

theorem apply_arrows (S : Subst) : (ks : List Ty) → (args : List Ty) → (t : TyName) → (τ : Ty) →
    S.apply (arrows ks (.con args t)) = some τ →
    ∃ ks' args', τ = arrows ks' (.con args' t) ∧ ks'.length = ks.length
  | [], args, t, τ, h => by
    simp only [arrows, Subst.apply] at h
    split at h
    · cases h; exact ⟨[], _, rfl, rfl⟩
    · cases h
  | k :: ks, args, t, τ, h => by
    simp only [arrows, Subst.apply] at h
    split at h
    · rename_i a' b' _ hb
      cases h
      obtain ⟨ks', args', rfl, hl⟩ := apply_arrows S ks args t b' hb
      exact ⟨a' :: ks', args', rfl, by simp [hl]⟩
    · cases h

theorem arrows_len : (ks ts : List Ty) → (args : List Ty) → (t : TyName) → (τ : Ty) → isConTy τ = true →
    arrows ks (.con args t) = arrows ts τ → ks.length = ts.length
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h => by simp [arrows] at h
  | _ :: _, [], _, _, τ, hc, h => by
    simp only [arrows] at h; subst h; simp [isConTy] at hc
  | _ :: ks, _ :: ts, args, t, τ, hc, h => by
    simp only [arrows, Ty.fn.injEq] at h
    simp [arrows_len ks ts args t τ hc h.2]

theorem genAt_arity {σ : Scheme} {inst ts : List Ty} {τ : Ty} {n : Nat}
    (hg : genAt σ inst (arrows ts τ) = true) (hc : isConTy τ = true) (ha : ArityIs σ n) :
    ts.length = n := by
  obtain ⟨ks, args, t, hb, hl⟩ := ha
  unfold genAt at hg
  split at hg
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    rw [hb] at hg
    obtain ⟨ks', args', he, hl'⟩ := apply_arrows _ ks args t _ hg.2
    rw [← hl, ← hl']
    exact (arrows_len ks' ts args' t τ hc he.symm).symm
  · cases hg

theorem arityOf_spec : (τ : Ty) → (n : Nat) → arityOf τ = some n →
    ∃ ks args t, τ = arrows ks (.con args t) ∧ ks.length = n
  | .fn a b, n, h => by
    simp only [arityOf] at h
    cases hb : arityOf b with
    | none => rw [hb] at h; cases h
    | some m =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨ks, args, t, rfl, hl⟩ := arityOf_spec b m hb
      exact ⟨a :: ks, args, t, rfl, by simp [hl, h]⟩
  | .con args t, n, h => by
    simp only [arityOf, Option.some.injEq] at h
    exact ⟨[], args, t, rfl, by simp [h]⟩
  | .var _, _, h => by simp [arityOf] at h
  | .record _ _, _, h => by simp [arityOf] at h

theorem arity_canon {σ : Scheme} {n : Nat} (h : ArityIs σ n) : ArityIs (Scheme.canon σ) n := by
  obtain ⟨ks, args, t, hb, hl⟩ := h
  unfold Scheme.canon
  generalize renumber true 0 (canonVars σ.bound σ.body) = r
  obtain ⟨S, bs⟩ := r
  simp only
  cases ha : S.apply σ.body with
  | none => exact ⟨ks, args, t, by simp [hb], hl⟩
  | some τ =>
    rw [hb] at ha
    obtain ⟨ks', args', rfl, hl'⟩ := apply_arrows S ks args t τ ha
    exact ⟨ks', args', t, rfl, by rw [hl', hl]⟩

theorem arity_clos {A : List BVar} {σ : Scheme} {n : Nat} (h : ArityIs σ n) :
    ArityIs (closScheme A σ) n := by
  unfold closScheme
  apply arity_canon
  obtain ⟨ks, args, t, hb, hl⟩ := h
  exact ⟨ks, args, t, hb, hl⟩

/-! ## Finite maps -/

section
variable {K V W : Type} [DecidableEq K]

theorem find?_mapV (f : FMap K V) (g : V → W) (k : K) :
    FMap.find? (FMap.mapV f g) k = (FMap.find? f k).map g := by
  induction f with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k', v⟩ := p
    simp only [FMap.mapV, List.map_cons, FMap.find?] at ih ⊢
    split <;> simp_all

omit [DecidableEq K] in
theorem keys_mapV (f : FMap K V) (g : V → W) : FMap.keys (FMap.mapV f g) = FMap.keys f := by
  simp [FMap.keys, FMap.mapV, List.map_map, Function.comp_def]

theorem mapV_modify (f g : FMap K V) (h : V → W) :
    FMap.mapV (FMap.modify f g) h = FMap.modify (FMap.mapV f h) (FMap.mapV g h) := by
  unfold FMap.modify
  rw [keys_mapV]
  simp [FMap.mapV, List.map_append, List.filter_map, Function.comp_def]

theorem mapV_foldl_modify (fs : List (FMap K V)) (acc : FMap K V) (h : V → W) :
    FMap.mapV (fs.foldl FMap.modify acc) h = (fs.map (FMap.mapV · h)).foldl FMap.modify (FMap.mapV acc h) := by
  induction fs generalizing acc with
  | nil => rfl
  | cons f fs ih => simp only [List.foldl_cons, List.map_cons, ih, mapV_modify]

theorem mapV_plusAll (fs : List (FMap K V)) (h : V → W) :
    FMap.mapV (FMap.plusAll fs) h = FMap.plusAll (fs.map (FMap.mapV · h)) := by
  unfold FMap.plusAll
  rw [mapV_foldl_modify]
  rfl

theorem keys_modify (f g : FMap K V) :
    FMap.keys (FMap.modify f g) = FMap.keys g ++ (FMap.keys f).filter (fun k => !decide (k ∈ FMap.keys g)) := by
  simp [FMap.modify, FMap.keys, List.map_append, List.filter_map, Function.comp_def]

/-- Every key a finite map binds is in xs. -/
def KeysIn (f : FMap K V) (xs : List K) : Prop := ∀ x v, FMap.find? f x = some v → x ∈ xs

theorem keysIn_nil (xs : List K) : KeysIn ([] : FMap K V) xs := by
  intro x v h; cases h

theorem keysIn_single {x : K} {v : V} {xs : List K} (h : x ∈ xs) : KeysIn [(x, v)] xs := by
  intro y w hy
  simp only [FMap.find?] at hy
  split at hy
  · rename_i e; subst e; exact h
  · cases hy

theorem keysIn_modify {f g : FMap K V} {xs : List K} (hf : KeysIn f xs) (hg : KeysIn g xs) :
    KeysIn (FMap.modify f g) xs := by
  intro x v h
  rw [FMap.find?_modify] at h
  cases hx : FMap.find? g x with
  | some w => exact hg x w hx
  | none => rw [hx] at h; exact hf x v h

theorem keysIn_mono {f : FMap K V} {xs ys : List K} (h : KeysIn f xs) (hs : ∀ x ∈ xs, x ∈ ys) :
    KeysIn f ys := fun x v hx => hs x (h x v hx)

theorem keysIn_foldl {fs : List (FMap K V)} {acc : FMap K V} {xs : List K}
    (hacc : KeysIn acc xs) (h : ∀ f ∈ fs, KeysIn f xs) : KeysIn (fs.foldl FMap.modify acc) xs := by
  induction fs generalizing acc with
  | nil => exact hacc
  | cons f fs ih =>
    simp only [List.foldl_cons]
    exact ih (keysIn_modify hacc (h f (by simp))) (fun g hg => h g (by simp [hg]))

theorem keysIn_plusAll {fs : List (FMap K V)} {xs : List K} (h : ∀ f ∈ fs, KeysIn f xs) :
    KeysIn (FMap.plusAll fs) xs := keysIn_foldl (keysIn_nil xs) h

theorem keysIn_mapV {f : FMap K V} {g : V → W} {xs : List K} (h : KeysIn f xs) :
    KeysIn (FMap.mapV f g) xs := by
  intro x w hx
  rw [find?_mapV] at hx
  cases hf : FMap.find? f x with
  | none => rw [hf] at hx; cases hx
  | some v => exact h x v hf

end

theorem find?_vs (xs : List String) (x : String) :
    FMap.find? (vs xs) x = if x ∈ xs then some none else none := by
  induction xs with
  | nil => simp [vs]
  | cons y ys ih =>
    simp only [vs, List.map_cons, FMap.find?] at ih ⊢
    rw [ih]
    by_cases h : y = x
    · subst h; simp
    · have h' : ¬ x = y := fun e => h e.symm
      simp [h, h']

/-! ## Sound value environments and the extension of shapes -/

/-- The shape bs describes VE: what VE binds bs binds, validly; a constructor arity bs records is
    for a name VE binds. -/
def VESound (VE : ValEnv) (bs : List (String × Option Nat)) : Prop :=
  (∀ x b, FMap.find? VE x = some b → ∃ a, FMap.find? bs x = some a ∧ Valid a b) ∧
  (∀ x n, FMap.find? bs x = some (some n) → (FMap.find? VE x).isSome)

theorem vesound_of_keysIn {VE : ValEnv} {xs : List String} (h : KeysIn VE xs) : VESound VE (vs xs) := by
  refine ⟨fun x b hx => ⟨none, ?_, fun n hn => by cases hn⟩, fun x n hx => ?_⟩
  · simp [find?_vs, h x b hx]
  · rw [find?_vs] at hx; split at hx <;> cases hx

theorem vesound_modify {f g : ValEnv} {bf bg : List (String × Option Nat)} (hf : VESound f bf)
    (hg : VESound g bg) : VESound (FMap.modify f g) (bg ++ bf) := by
  refine ⟨fun x b hx => ?_, fun x n hx => ?_⟩
  · rw [FMap.find?_modify] at hx
    rw [FMap.find?_append]
    cases hgx : FMap.find? g x with
    | some w =>
      rw [hgx] at hx; simp only [Option.some_or, Option.some.injEq] at hx; subst hx
      obtain ⟨a, ha, hv⟩ := hg.1 x w hgx
      exact ⟨a, by rw [ha]; rfl, hv⟩
    | none =>
      rw [hgx] at hx
      simp only [Option.none_or] at hx
      obtain ⟨a, ha, hv⟩ := hf.1 x b hx
      cases hbg : FMap.find? bg x with
      | none => exact ⟨a, by rw [ha]; rfl, hv⟩
      | some a' =>
        refine ⟨a', rfl, fun n hn _ => ?_⟩
        subst hn
        have := hg.2 x n hbg
        rw [hgx] at this; cases this
  · rw [FMap.find?_append] at hx
    rw [FMap.find?_modify]
    cases hbg : FMap.find? bg x with
    | some a' =>
      rw [hbg] at hx; cases hx
      have := hg.2 x n hbg
      cases hgx : FMap.find? g x with
      | none => rw [hgx] at this; cases this
      | some _ => rfl
    | none =>
      rw [hbg] at hx
      simp only [Option.none_or] at hx
      have := hf.2 x n hx
      cases hgx : FMap.find? g x with
      | none => simpa using this
      | some _ => rfl

theorem vesound_clos {VE : ValEnv} {bs : List (String × Option Nat)} (A : List BVar) (h : VESound VE bs) :
    VESound (closVE A VE) bs := by
  refine ⟨fun x b hx => ?_, fun x n hx => ?_⟩
  · unfold closVE at hx
    rw [find?_mapV] at hx
    cases hv : FMap.find? VE x with
    | none => rw [hv] at hx; cases hx
    | some b0 =>
      rw [hv] at hx; cases hx
      obtain ⟨a, ha, hval⟩ := h.1 x b0 hv
      exact ⟨a, ha, fun n hn hc => arity_clos (hval n hn hc)⟩
  · unfold closVE
    rw [find?_mapV]
    have := h.2 x n hx
    cases hv : FMap.find? VE x with
    | none => rw [hv] at this; cases this
    | some _ => rfl

/-- The context's lookup after adding VE in front of its unqualified values. -/
def LookupExt (C C' : Ctx) (VE : ValEnv) : Prop :=
  ∀ lid, C'.lookupVal lid =
    match lid.qual with
    | none => (FMap.find? VE lid.id).or (C.lookupVal lid)
    | some _ => C.lookupVal lid

theorem abs_ext {C C' : Ctx} {Γ : Shape} {VE : ValEnv} {bs : List (String × Option Nat)}
    (hA : Abs C Γ) (hS : VESound VE bs) (hL : LookupExt C C' VE) : Abs C' (extT Γ bs) := by
  intro lid b h
  rw [hL lid] at h
  obtain ⟨q, x⟩ := lid
  cases q with
  | some m =>
    simp only at h
    obtain ⟨a, ha, hv⟩ := hA _ b h
    exact ⟨a, by simp only [extT]; exact ha, hv⟩
  | none =>
    simp only at h
    simp only [extT]
    cases hx : FMap.find? VE x with
    | some w =>
      rw [hx] at h; simp only [Option.some_or, Option.some.injEq] at h; subst h
      obtain ⟨a, ha, hv⟩ := hS.1 x w hx
      exact ⟨a, by rw [ha]; rfl, hv⟩
    | none =>
      rw [hx] at h
      simp only [Option.none_or] at h
      obtain ⟨a, ha, hv⟩ := hA _ b h
      cases hb : FMap.find? bs x with
      | none => exact ⟨a, by rw [ha]; rfl, hv⟩
      | some a' =>
        refine ⟨a', rfl, fun n hn _ => ?_⟩
        subst hn
        have := hS.2 x n hb
        rw [hx] at this; cases this

theorem lookupExt_plusVE (C : Ctx) (VE : ValEnv) : LookupExt C (C.plusVE VE) VE := by
  intro lid
  obtain ⟨q, x⟩ := lid
  cases q with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, Ctx.plusVE]
    exact FMap.find?_append VE C.E.VE x
  | some m => rfl

theorem abs_plusVE {C : Ctx} {Γ : Shape} {VE : ValEnv} {xs : List String} (hA : Abs C Γ)
    (h : KeysIn VE xs) : Abs (C.plusVE VE) (extT Γ (vs xs)) :=
  abs_ext hA (vesound_of_keysIn h) (lookupExt_plusVE C VE)

theorem abs_plusU {C : Ctx} {Γ : Shape} (U : List BVar) (hA : Abs C Γ) : Abs (C.plusU U) Γ := hA

theorem abs_ctxShape (C : Ctx) : Abs C (ctxShape C) := by
  intro lid b h
  refine ⟨infoOf b, by simp [ctxShape, h], fun n hn hc => ?_⟩
  obtain ⟨σ, st⟩ := b
  simp only at hc
  subst hc
  simp only [infoOf] at hn
  exact arityOf_spec σ.body n hn

/-! ## The keys of the value environments of patterns and bindings -/

mutual
theorem keys_atPat : (p : AAtPat) → KeysIn p.ve (atPatVars p.erase)
  | .wild _ => keysIn_nil _
  | .scon _ _ => keysIn_nil _
  | .var x _ => keysIn_single (by simp [AAtPat.erase, atPatVars])
  | .con _ _ _ => keysIn_nil _
  | .unit => keysIn_nil _
  | .tuple p1 p2 p3 => by
    simp only [AAtPat.ve, AAtPat.erase, atPatVars]
    refine keysIn_modify (keysIn_modify ?_ ?_) ?_
    · exact keysIn_mono (keys_pat p1) (by intro x hx; simp [hx])
    · exact keysIn_mono (keys_pat p2) (by intro x hx; simp [hx])
    · exact keysIn_mono (keys_patOpt p3) (by intro x hx; simp [hx])
  | .nil _ => keysIn_nil _
  | .record row _ => by
    simp only [AAtPat.ve, AAtPat.erase, atPatVars]
    exact keys_patRowOpt row
  | .paren p => by
    simp only [AAtPat.ve, AAtPat.erase, atPatVars]
    exact keys_pat p
theorem keys_patRow : (r : APatRow) → KeysIn r.ve (patRowVars r.erase)
  | .field l _ rest => by
    simp only [APatRow.ve, APatRow.erase, patRowVars]
    refine keysIn_modify (keysIn_single (by simp)) ?_
    exact keysIn_mono (keys_patRowOpt rest) (by intro x hx; simp [hx])
theorem keys_patRowOpt : (r : Option APatRow) → KeysIn (APatRow.veOpt r) (patRowVarsOpt (APatRow.eraseOpt r))
  | none => keysIn_nil _
  | some r => by
    simp only [APatRow.veOpt, APatRow.eraseOpt, patRowVarsOpt]
    exact keys_patRow r
theorem keys_pat : (p : APat) → KeysIn p.ve (patVars p.erase)
  | .atpat a => by
    simp only [APat.ve, APat.erase, patVars]
    exact keys_atPat a
  | .con _ _ args _ => by
    simp only [APat.ve, APat.erase, patVars]
    exact keysIn_plusAll (keys_atPatList args)
  | .cons p1 p2 => by
    simp only [APat.ve, APat.erase, patVars]
    refine keysIn_modify ?_ ?_
    · exact keysIn_mono (keys_pat p1) (by intro x hx; simp [hx])
    · exact keysIn_mono (keys_pat p2) (by intro x hx; simp [hx])
  | .as p x => by
    simp only [APat.ve, APat.erase, patVars]
    refine keysIn_modify ?_ (keysIn_single (by simp))
    exact keysIn_mono (keys_pat p) (by intro x hx; simp [hx])
theorem keys_patOpt : (p : Option APat) → KeysIn (APat.veOpt p) (patVarsOpt (APat.eraseOpt p))
  | none => keysIn_nil _
  | some p => by
    simp only [APat.veOpt, APat.eraseOpt, patVarsOpt]
    exact keys_pat p
theorem keys_atPatList : (as : List AAtPat) →
    ∀ f ∈ AAtPat.veList as, KeysIn f (atPatListVars (AAtPat.eraseList as))
  | [] => by simp [AAtPat.veList]
  | a :: as => by
    intro f hf
    simp only [AAtPat.veList, List.mem_cons] at hf
    simp only [AAtPat.eraseList, atPatListVars]
    rcases hf with rfl | hf
    · exact keysIn_mono (keys_atPat a) (by intro x hx; simp [hx])
    · exact keysIn_mono (keys_atPatList as f hf) (by intro x hx; simp [hx])
end

theorem keys_valBind : (vb : AValBind) → KeysIn vb.ve (vbVars vb.erase)
  | .var x ann τ e none => by
    simp only [AValBind.ve, AValBind.erase, AValBind.eraseOpt, vbVars, vbVarsOpt]
    exact keysIn_modify (keysIn_single (by simp)) (keysIn_nil _)
  | .var x ann τ e (some vb) => by
    simp only [AValBind.ve, AValBind.erase, AValBind.eraseOpt, vbVars, vbVarsOpt]
    refine keysIn_modify (keysIn_single (by simp)) ?_
    exact keysIn_mono (keys_valBind vb) (by intro y hy; simp [hy])
  | .pat p e => by
    simp only [AValBind.ve, AValBind.erase, vbVars]
    exact keys_atPat p

theorem keysIn_closGroup {VE : ValEnv} {xs : List String} (A : List BVar) (h : KeysIn VE xs) :
    KeysIn (closGroup A VE) xs := by
  unfold closGroup
  exact keysIn_mapV h

/-! ## The bare checker is sound -/

theorem conOK_of {C : Ctx} {Γ : Shape} (hA : Abs C Γ) {lc : LongId} {σ : Scheme} {k : Nat}
    (hl : C.lookupVal lc = some (σ, .c)) (hk : ∀ n, ArityIs σ n → k = n) : conOK Γ lc k = true := by
  obtain ⟨a, ha, hv⟩ := hA lc _ hl
  unfold conOK
  rw [ha]
  cases a with
  | none => rfl
  | some n => simp [hk n (hv n rfl rfl)]

theorem length_tyList : (as : List AAtPat) → (AAtPat.tyList as).length = as.length
  | [] => rfl
  | a :: as => by simp [AAtPat.tyList, length_tyList as]

theorem length_eraseList : (as : List AAtPat) → (AAtPat.eraseList as).length = as.length
  | [] => rfl
  | a :: as => by simp [AAtPat.eraseList, length_eraseList as]

mutual
theorem sc_atPat (C : Ctx) (Γ : Shape) (hA : Abs C Γ) : (p : AAtPat) → checkAtPat C p = true →
    scAtPat Γ p.erase = true
  | .wild _, _ => rfl
  | .scon _ _, _ => rfl
  | .var _ _, _ => rfl
  | .con lc inst τ, h => by
    simp only [checkAtPat] at h
    split at h
    · rename_i σ hl
      simp only [Bool.and_eq_true] at h
      simp only [AAtPat.erase, scAtPat]
      exact conOK_of hA hl (fun n hn => (genAt_arity (ts := []) h.1 h.2 hn))
    · cases h
  | .unit, _ => rfl
  | .tuple p1 p2 p3, h => by
    simp only [checkAtPat, Bool.and_eq_true] at h
    simp only [AAtPat.erase, scAtPat, Bool.and_eq_true]
    exact ⟨⟨sc_pat C Γ hA p1 h.1.1, sc_pat C Γ hA p2 h.1.2⟩, sc_patOpt C Γ hA p3 h.2⟩
  | .nil _, _ => rfl
  | .record _ _, _ => rfl
  | .paren p, h => by
    simp only [checkAtPat] at h
    simp only [AAtPat.erase, scAtPat]
    exact sc_pat C Γ hA p h
theorem sc_pat (C : Ctx) (Γ : Shape) (hA : Abs C Γ) : (p : APat) → checkPat C p = true →
    scPat Γ p.erase = true
  | .atpat a, h => by
    simp only [checkPat] at h
    simp only [APat.erase, scPat]
    exact sc_atPat C Γ hA a h
  | .con lc inst args τ, h => by
    simp only [checkPat, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h1
    · rename_i σ hl
      simp only [Bool.and_eq_true] at h1
      simp only [APat.erase, scPat, Bool.and_eq_true]
      refine ⟨conOK_of hA hl (fun n hn => ?_), sc_atPatList C Γ hA args h2⟩
      have := genAt_arity h1.1 h1.2 hn
      rw [length_tyList] at this
      rw [length_eraseList, this]
    · cases h1
  | .cons p1 p2, h => by
    simp only [checkPat, Bool.and_eq_true] at h
    simp only [APat.erase, scPat, Bool.and_eq_true]
    exact ⟨sc_pat C Γ hA p1 h.1.1, sc_pat C Γ hA p2 h.1.2⟩
  | .as p _, h => by
    simp only [checkPat] at h
    simp only [APat.erase, scPat]
    exact sc_pat C Γ hA p h
theorem sc_patOpt (C : Ctx) (Γ : Shape) (hA : Abs C Γ) : (p : Option APat) → checkPatOpt C p = true →
    scPatOpt Γ (APat.eraseOpt p) = true
  | none, _ => rfl
  | some p, h => by
    simp only [checkPatOpt] at h
    simp only [APat.eraseOpt, scPatOpt]
    exact sc_pat C Γ hA p h
theorem sc_atPatList (C : Ctx) (Γ : Shape) (hA : Abs C Γ) : (as : List AAtPat) →
    checkAtPatList C as = true → scAtPatList Γ (AAtPat.eraseList as) = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [checkAtPatList, Bool.and_eq_true] at h
    simp only [AAtPat.eraseList, scAtPatList, Bool.and_eq_true]
    exact ⟨sc_atPat C Γ hA a h.1, sc_atPatList C Γ hA as h.2⟩
end

theorem isSome_of_lookup {C : Ctx} {Γ : Shape} (hA : Abs C Γ) {lv : LongId} {inst : List Ty} {τ : Ty}
    (h : (match C.lookupVal lv with
      | some (σ, _) => genAt σ inst τ
      | none => false) = true) : (Γ lv).isSome = true := by
  split at h
  · rename_i σ st hl
    obtain ⟨a, ha, _⟩ := hA lv _ hl
    rw [ha]; rfl
  · cases h

/-- The environment a declaration adds binds only the variables of its bindings. -/
theorem keys_dec {C : Ctx} {d : ADec} (h : checkDec C d = true) : KeysIn (d.result C) (decVars d.erase) := by
  cases d with
  | val VE vb =>
    simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [ADec.result, ADec.erase, decVars]
    rw [← h.2]
    exact keysIn_closGroup _ (keys_valBind vb)

mutual
theorem sc_atExp : (a : AAtExp) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkAtExp C a = true →
    scAtExp Γ a.erase = true
  | .scon _ _, _, _, _, _ => rfl
  | .var lv inst τ, C, Γ, hA, h => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, scAtExp]
    exact isSome_of_lookup hA h
  | .con lc inst τ, C, Γ, hA, h => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, scAtExp]
    exact isSome_of_lookup hA h
  | .op _ _ _, _, _, _, _ => rfl
  | .unit, _, _, _, _ => rfl
  | .tuple e1 e2 e3, C, Γ, hA, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [AAtExp.erase, scAtExp, Bool.and_eq_true]
    exact ⟨⟨sc_exp e1 C Γ hA h.1.1, sc_exp e2 C Γ hA h.1.2⟩, sc_expOpt e3 C Γ hA h.2⟩
  | .nil _, _, _, _, _ => rfl
  | .record row, C, Γ, hA, h => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, scAtExp]
    exact sc_expRowOpt row C Γ hA h
  | .update x inst τ row, C, Γ, hA, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, _⟩, h3⟩, _⟩ := h
    simp only [AAtExp.erase, scAtExp, Bool.and_eq_true]
    exact ⟨isSome_of_lookup hA h1, sc_expRow row C Γ hA h3⟩
  | .letE d e, C, Γ, hA, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [AAtExp.erase, scAtExp, Bool.and_eq_true]
    exact ⟨sc_dec d C Γ hA h.1, sc_exp e _ _ (abs_plusVE hA (keys_dec h.1)) h.2⟩
  | .paren e, C, Γ, hA, h => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, scAtExp]
    exact sc_exp e C Γ hA h
theorem sc_expRow : (r : AExpRow) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkExpRow C r = true →
    scExpRow Γ r.erase = true
  | .field _ e rest, C, Γ, hA, h => by
    simp only [checkExpRow, Bool.and_eq_true] at h
    simp only [AExpRow.erase, scExpRow, Bool.and_eq_true]
    exact ⟨sc_exp e C Γ hA h.1, sc_expRowOpt rest C Γ hA h.2⟩
theorem sc_expRowOpt : (r : Option AExpRow) → (C : Ctx) → (Γ : Shape) → Abs C Γ →
    checkExpRowOpt C r = true → scExpRowOpt Γ (AExpRow.eraseOpt r) = true
  | none, _, _, _, _ => rfl
  | some r, C, Γ, hA, h => by
    simp only [checkExpRowOpt] at h
    simp only [AExpRow.eraseOpt, scExpRowOpt]
    exact sc_expRow r C Γ hA h
theorem sc_exp : (a : AExp) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkExp C a = true →
    scExp Γ a.erase = true
  | .atexp a, C, Γ, hA, h => by
    simp only [checkExp] at h
    simp only [AExp.erase, scExp]
    exact sc_atExp a C Γ hA h
  | .app e a, C, Γ, hA, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    simp only [AExp.erase, scExp, Bool.and_eq_true]
    exact ⟨sc_exp e C Γ hA h.1.1, sc_atExp a C Γ hA h.1.2⟩
  | .lam p e, C, Γ, hA, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    simp only [AExp.erase, scExp, Bool.and_eq_true]
    exact ⟨sc_atPat C Γ hA p h.1, sc_exp e _ _ (abs_plusVE hA (keys_atPat p)) h.2⟩
  | .caseE e m, C, Γ, hA, h => by
    simp only [checkExp, Bool.and_eq_true] at h
    simp only [AExp.erase, scExp, Bool.and_eq_true]
    exact ⟨sc_exp e C Γ hA h.1.1, sc_match m C Γ hA h.1.2⟩
theorem sc_expOpt : (e : Option AExp) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkExpOpt C e = true →
    scExpOpt Γ (AExp.eraseOpt e) = true
  | none, _, _, _, _ => rfl
  | some e, C, Γ, hA, h => by
    simp only [checkExpOpt] at h
    simp only [AExp.eraseOpt, scExpOpt]
    exact sc_exp e C Γ hA h
theorem sc_match : (m : AMatch) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkMatch C m = true →
    scMatch Γ m.erase = true
  | .mk mr rest, C, Γ, hA, h => by
    simp only [checkMatch, Bool.and_eq_true] at h
    simp only [AMatch.erase, scMatch, Bool.and_eq_true]
    exact ⟨sc_mrule mr C Γ hA h.1, sc_matchOpt rest _ C Γ hA h.2⟩
theorem sc_matchOpt : (m : Option AMatch) → (τ : Ty) → (C : Ctx) → (Γ : Shape) → Abs C Γ →
    checkMatchOptAt C τ m = true → scMatchOpt Γ (AMatch.eraseOpt m) = true
  | none, _, _, _, _, _ => rfl
  | some m, τ, C, Γ, hA, h => by
    simp only [checkMatchOptAt, Bool.and_eq_true] at h
    simp only [AMatch.eraseOpt, scMatchOpt]
    exact sc_match m C Γ hA h.1
theorem sc_mrule : (mr : AMRule) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkMRule C mr = true →
    scMRule Γ mr.erase = true
  | .mk p e, C, Γ, hA, h => by
    simp only [checkMRule, Bool.and_eq_true] at h
    simp only [AMRule.erase, scMRule, Bool.and_eq_true]
    exact ⟨sc_pat C Γ hA p h.1, sc_exp e _ _ (abs_plusVE hA (keys_pat p)) h.2⟩
theorem sc_dec : (d : ADec) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkDec C d = true →
    scDec Γ d.erase = true
  | .val VE vb, C, Γ, hA, h => by
    simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [ADec.erase, scDec]
    have hk : KeysIn VE (vbVars vb.erase) := h.2 ▸ keys_valBind vb
    exact sc_valBind vb _ _ (abs_plusVE hA hk) h.1
theorem sc_valBind : (vb : AValBind) → (C : Ctx) → (Γ : Shape) → Abs C Γ → checkValBind C vb = true →
    scVB Γ vb.erase = true
  | .var _ ann _ e rest, C, Γ, hA, h => by
    simp only [checkValBind, Bool.and_eq_true] at h
    simp only [AValBind.erase, scVB, Bool.and_eq_true]
    exact ⟨sc_exp e _ Γ (abs_plusU _ hA) h.1.1.2, sc_valBindOpt rest C Γ hA h.2⟩
  | .pat p e, C, Γ, hA, h => by
    simp only [checkValBind, Bool.and_eq_true] at h
    simp only [AValBind.erase, scVB, Bool.and_eq_true]
    exact ⟨sc_atPat C Γ hA p h.1.1, sc_exp e C Γ hA h.1.2⟩
theorem sc_valBindOpt : (vb : Option AValBind) → (C : Ctx) → (Γ : Shape) → Abs C Γ →
    checkValBindOpt C vb = true → scVBOpt Γ (AValBind.eraseOpt vb) = true
  | none, _, _, _, _ => rfl
  | some vb, C, Γ, hA, h => by
    simp only [checkValBindOpt] at h
    simp only [AValBind.eraseOpt, scVBOpt]
    exact sc_valBind vb C Γ hA h
end

/-! ## Top-level declarations -/

def conBs : BConBind → List (String × Option Nat)
  | [] => []
  | (k, tys) :: rest => conBs rest ++ [(k, some tys.length)]

def datBsL : BDatBind → List (String × Option Nat)
  | [] => []
  | (_, _, cb) :: rest => datBsL rest ++ conBs cb

def datBs : Option BDatBind → List (String × Option Nat)
  | none => []
  | some d => datBsL d

def typesBs (db : Option BDatBind) (tbs : List BTypBind) : List (String × Option Nat) :=
  vs ((tbs.map (·.c)).reverse) ++ datBs db

/-- The shape of the values a top-level declaration binds, in the order of FMap.modify. -/
def topBs : BTopDec → List (String × Option Nat)
  | .value vb => vs (vbVars vb)
  | .types db tbs => typesBs db tbs
  | .port x _ => [(x, none)]
  | .seq d1 d2 => topBs d2 ++ topBs d1

def scTop (Γ : Shape) : BTopDec → Bool
  | .value vb => scVB (extT Γ (vs (vbVars vb))) vb
  | .types _ _ => true
  | .port _ _ => true
  | .seq d1 d2 => scTop Γ d1 && scTop (extT Γ (topBs d1)) d2

def scTopOpt (Γ : Shape) : Option BTopDec → Bool
  | none => true
  | some d => scTop Γ d

theorem vesound_nil : VESound [] [] := ⟨fun _ _ hx => (by cases hx), fun _ _ hx => (by cases hx)⟩

theorem vesound_single {k : String} {b : Scheme × IdStatus} {a : Option Nat} (h : Valid a b) :
    VESound [(k, b)] [(k, a)] := by
  refine ⟨fun x b' hx => ?_, fun x n hx => ?_⟩
  · simp only [FMap.find?] at hx
    split at hx
    · rename_i e; subst e; cases hx; exact ⟨a, by simp [FMap.find?], h⟩
    · cases hx
  · simp only [FMap.find?] at hx ⊢
    split at hx
    · rename_i e; simp [e]
    · cases hx

theorem elabTyList_length (C : Ctx) : (tys : List BTy) → (τs : List Ty) → elabTyList C tys = some τs →
    τs.length = tys.length
  | [], τs, h => by simp only [elabTyList, Option.some.injEq] at h; subst h; rfl
  | t :: ts, τs, h => by
    simp only [elabTyList] at h
    split at h
    · rename_i τ τs' _ h2
      cases h
      simp [elabTyList_length C ts τs' h2]
    · cases h

theorem vesound_conBind (C : Ctx) (args : List Ty) (t : TyName) : (cb : BConBind) → (VE : ValEnv) →
    elabConBind C (.con args t) cb = some VE → VESound VE (conBs cb)
  | [], VE, h => by
    simp only [elabConBind, Option.some.injEq] at h; subst h
    exact vesound_nil
  | (k, tys) :: rest, VE, h => by
    simp only [elabConBind] at h
    split at h
    · rename_i τs VE' h1 h2
      cases h
      simp only [conBs]
      refine vesound_modify (vesound_single ?_) (vesound_conBind C args t rest VE' h2)
      intro n hn _
      cases hn
      exact ⟨τs, args, t, rfl, elabTyList_length C tys τs h1⟩
    · cases h

theorem vesound_datBind (C : Ctx) (names : String → Option TyName) : (d : BDatBind) → (VE : ValEnv) →
    (TE : TyEnv) → elabDatBind C names d = some (VE, TE) → VESound VE (datBsL d)
  | [], VE, TE, h => by
    simp only [elabDatBind, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact vesound_nil
  | (c, ps, cb) :: rest, VE, TE, h => by
    simp only [elabDatBind] at h
    split at h
    · cases h
    · rename_i t _
      split at h
      · rename_i τs VE' TE' _ h2
        split at h
        · rename_i VEc h3
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [datBsL]
            exact vesound_modify (vesound_clos _ (vesound_conBind _ _ _ cb VEc h3))
              (vesound_datBind C names rest VE' TE' h2)
          · cases h
        · cases h
      · cases h

theorem keysIn_closVE {VE : ValEnv} {xs : List String} (A : List BVar) (h : KeysIn VE xs) :
    KeysIn (closVE A VE) xs := by
  unfold closVE
  exact keysIn_mapV h

theorem keysIn_typBind (C : Ctx) (tb : BTypBind) (VE : ValEnv) (TE : TyEnv)
    (h : elabTypBind C tb = some (VE, TE)) : KeysIn VE [tb.c] := by
  unfold elabTypBind at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact keysIn_nil _
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact keysIn_closVE _ (keysIn_single (by simp))
          · cases h
        · cases h
      · cases h

theorem keysIn_typBinds (C : Ctx) : (tbs : List BTypBind) → (VEs : List ValEnv) → (TEs : List TyEnv) →
    elabTypBinds C tbs = some (VEs, TEs) → ∀ f ∈ VEs, KeysIn f (tbs.map (·.c))
  | [], VEs, TEs, h => by
    simp only [elabTypBinds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | tb :: tbs, VEs, TEs, h => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE TE VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact keysIn_mono (keysIn_typBind C tb f TE h1) (by simp)
      · exact keysIn_mono (keysIn_typBinds C tbs VEs' TEs' h2 f hf) (by intro x hx; simp [hx])
    · cases h

theorem vesound_typBinds {C : Ctx} {tbs : List BTypBind} {VEs : List ValEnv} {TEs : List TyEnv}
    (h : elabTypBinds C tbs = some (VEs, TEs)) :
    VESound (FMap.plusAll VEs) (vs ((tbs.map (·.c)).reverse)) := by
  apply vesound_of_keysIn
  exact keysIn_mono (keysIn_plusAll (keysIn_typBinds C tbs VEs TEs h)) (by intro x hx; simpa using hx)

theorem vesound_checkTypes {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind}
    {tbs : List BTypBind} (h : checkTypes C TE VE db tbs = true) : VESound VE (typesBs db tbs) := by
  replace h := checkTypes_fix h
  unfold checkTypesFix at h
  cases db with
  | none =>
    simp only at h
    split at h
    · rename_i VEs TEs h1
      simp only [decide_eq_true_eq] at h
      obtain ⟨_, _, rfl⟩ := h
      simp only [typesBs, datBs, List.append_nil]
      exact vesound_typBinds h1
    · cases h
  | some d =>
    simp only at h
    split at h
    · rename_i VE' TE' VEs TEs h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      simp only [typesBs, datBs]
      exact vesound_modify (vesound_datBind _ _ d VE' TE' h1) (vesound_typBinds h2)
    · cases h

def TopSound (E : Env) (bs : List (String × Option Nat)) : Prop := E.QE = [] ∧ VESound E.VE bs

theorem topSound_plus {E1 E2 : Env} {b1 b2 : List (String × Option Nat)} (h1 : TopSound E1 b1)
    (h2 : TopSound E2 b2) : TopSound (E1.plus E2) (b2 ++ b1) := by
  refine ⟨?_, vesound_modify h1.2 h2.2⟩
  simp only [Env.plus, h1.1, h2.1]
  rfl

theorem elabPort_shape {C : Ctx} {x : Var} {ty : BTy} {U : List BVar} {E : Env} {PE : PortEnv}
    (h : elabPort C x ty U = some (E, PE)) : TopSound E [(x, none)] := by
  have key : ∀ σ : Scheme, TopSound (Env.ofVE [(x, (σ, .v))]) [(x, none)] := fun σ =>
    ⟨rfl, vesound_single (fun n hn => by cases hn)⟩
  unfold elabPort at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact key _
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact key _
          · cases h
        · cases h
    · cases h
  · cases h

theorem topSound : (a : ATopDec) → (C : Ctx) → (E : Env) → (PE : PortEnv) →
    checkTopDec C a = some (E, PE) → TopSound E (topBs a.erase)
  | .value VE vb, C, E, PE, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, vesound_of_keysIn ?_⟩
      simp only [Env.ofVE]
      rw [← hc.2]
      exact keysIn_closGroup _ (keys_valBind vb)
    · cases h
  | .types TE VE db tbs, C, E, PE, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, vesound_checkTypes hc⟩
    · cases h
  | .port x ty U, C, E, PE, h => by
    simp only [checkTopDec] at h
    exact elabPort_shape h
  | .seq a1 a2, C, E, PE, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i E1 PE1 h1
      split at h
      · rename_i E2 PE2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact topSound_plus (topSound a1 C E1 PE1 h1) (topSound a2 _ E2 PE2 h2)
      · cases h
    · cases h

theorem lookupExt_oplusE (C : Ctx) {E : Env} (hq : E.QE = []) : LookupExt C (C.oplusE E) E.VE := by
  intro lid
  obtain ⟨q, x⟩ := lid
  cases q with
  | none =>
    simp only [Ctx.lookupVal, Env.lookupVal, Ctx.oplusE, Env.plus]
    rw [FMap.find?_modify]
  | some m =>
    simp only [Ctx.lookupVal, Env.lookupVal, Ctx.oplusE, Env.plus]
    rw [FMap.find?_modify, hq]
    rfl

theorem sc_top : (a : ATopDec) → (C : Ctx) → (Γ : Shape) → (E : Env) → (PE : PortEnv) → Abs C Γ →
    checkTopDec C a = some (E, PE) → scTop Γ a.erase = true
  | .value VE vb, C, Γ, E, PE, hA, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [ATopDec.erase, scTop]
      have hk : KeysIn VE (vbVars vb.erase) := hc.2 ▸ keys_valBind vb
      exact sc_valBind vb _ _ (abs_plusVE hA hk) hc.1
    · cases h
  | .types _ _ _ _, _, _, _, _, _, _ => rfl
  | .port _ _ _, _, _, _, _, _, _ => rfl
  | .seq a1 a2, C, Γ, E, PE, hA, h => by
    simp only [checkTopDec] at h
    split at h
    · rename_i E1 PE1 h1
      split at h
      · rename_i E2 PE2 h2
        have s1 := topSound a1 C E1 PE1 h1
        simp only [ATopDec.erase, scTop, Bool.and_eq_true]
        exact ⟨sc_top a1 C Γ E1 PE1 hA h1,
          sc_top a2 _ _ E2 PE2 (abs_ext hA s1.2 (lookupExt_oplusE C s1.1)) h2⟩
      · cases h
    · cases h

theorem sc_topOpt {a : Option ATopDec} {C : Ctx} {Γ : Shape} {E : Env} {PE : PortEnv} (hA : Abs C Γ)
    (h : checkTopDecOpt C a = some (E, PE)) : scTopOpt Γ (a.map ATopDec.erase) = true := by
  cases a with
  | none => rfl
  | some d => exact sc_top d C Γ E PE hA h

/-! ## One module: the shape of a concrete import context -/

/-- The first module's body is out of scope in its import context (or its imports fail). -/
def scope1 (B : SBasis) (m : BModule) : Bool :=
  match importCtx B m.imports with
  | none => true
  | some C => !(scTopOpt (ctxShape C) m.body)

theorem noDeriv_of_ctx {B : SBasis} {m : BModule} {C : Ctx} {Γ : Shape} (hC : importCtx B m.imports = some C)
    (hA : Abs C Γ) (h : scTopOpt Γ m.body = false) : NoDeriv B m := by
  intro a he
  have him : a.imports = m.imports := by rw [← he]; rfl
  have hb : a.body.map ATopDec.erase = m.body := by rw [← he]; rfl
  unfold checkModule
  rw [AModule.result_of_ctx (him ▸ hC)]
  unfold AModule.resultIn
  cases hd : checkTopDecOpt C a.body with
  | none => rfl
  | some EP =>
    obtain ⟨E, PE⟩ := EP
    have := sc_topOpt hA hd
    rw [hb, h] at this
    cases this

theorem noDeriv_scope1 {B : SBasis} {m : BModule} (h : scope1 B m = true) : NoDeriv B m := by
  unfold scope1 at h
  cases hC : importCtx B m.imports with
  | none => exact noDeriv_of_imports hC
  | some C =>
    rw [hC] at h
    simp only [Bool.not_eq_true'] at h
    exact noDeriv_of_ctx hC (abs_ctxShape C) h

/-! ## The context of a provider map binds only what the map provides -/

def EnvKeys (E : Env) (K : List SmLongId) : Prop :=
  (∀ x b, FMap.find? E.VE x = some b → (⟨none, .val x⟩ : SmLongId) ∈ K) ∧
  (∀ q I, FMap.find? E.QE q = some I → ∀ x b, FMap.find? I.VE x = some b → (⟨some q, .val x⟩ : SmLongId) ∈ K)

theorem find?_addQ (q : ModId) (f : IEnv → IEnv) : (QE : FMap ModId IEnv) → (q' : ModId) →
    FMap.find? (addQ q f QE) q' = if q = q' then some (f ((FMap.find? QE q).getD IEnv.empty)) else FMap.find? QE q'
  | [], q' => by
    simp only [addQ, FMap.find?]
    split <;> simp
  | (q0, I) :: rest, q' => by
    simp only [addQ]
    by_cases h0 : q0 = q
    · subst h0
      simp only [ite_true, FMap.find?]
      by_cases h1 : q0 = q' <;> simp [h1]
    · simp only [h0, ite_false, FMap.find?]
      rw [find?_addQ q f rest q']
      by_cases h1 : q0 = q'
      · subst h1
        simp [Ne.symm h0]
      · simp [h1]

theorem envKeys_mono {E : Env} {K K' : List SmLongId} (h : EnvKeys E K) (hs : ∀ k ∈ K, k ∈ K') :
    EnvKeys E K' :=
  ⟨fun x b hx => hs _ (h.1 x b hx), fun q I hq x b hx => hs _ (h.2 q I hq x b hx)⟩

theorem envKeys_addQ {E : Env} {K : List SmLongId} (q : ModId) (f : IEnv → IEnv) (h : EnvKeys E K)
    (hf : ∀ I x b, FMap.find? (f I).VE x = some b → FMap.find? I.VE x = some b ∨ (⟨some q, .val x⟩ : SmLongId) ∈ K) :
    EnvKeys { E with QE := addQ q f E.QE } K := by
  refine ⟨h.1, fun q' I hq x b hx => ?_⟩
  simp only at hq
  rw [find?_addQ] at hq
  split at hq
  · rename_i e
    subst e
    cases hq
    rcases hf _ x b hx with h1 | h1
    · cases hI : FMap.find? E.QE q with
      | none => rw [hI] at h1; cases h1
      | some I0 =>
        rw [hI] at h1
        exact h.2 q I0 hI x b h1
    · exact h1
  · exact h.2 q' I hq x b hx

theorem envKeys_step (ME : ModEnv) (p : SmLongId × List ModId) (E : Env) (K : List SmLongId)
    (h : EnvKeys E K) : EnvKeys (envStep ME p E) (p.1 :: K) := by
  have h' := envKeys_mono h (fun k hk => List.mem_cons_of_mem p.1 hk)
  have hid : ∀ q, EnvKeys { E with QE := addQ q id E.QE } (p.1 :: K) :=
    fun q => envKeys_addQ q id h' (fun I x b hx => .inl hx)
  obtain ⟨⟨q, i⟩, mids⟩ := p
  cases q with
  | none =>
    cases i with
    | ty c =>
      rcases mids with _ | ⟨mid, _ | ⟨mid2, rest⟩⟩ <;> simp only [envStep] <;> try exact h'
      split
      · exact h'
      · exact h'
    | val x =>
      rcases mids with _ | ⟨mid, _ | ⟨mid2, rest⟩⟩ <;> simp only [envStep] <;> try exact h'
      split
      · rename_i b0 _
        refine ⟨fun y b hy => ?_, h'.2⟩
        simp only [FMap.find?] at hy
        split at hy
        · rename_i e; subst e; simp
        · exact h'.1 y b hy
      · exact h'
  | some q =>
    cases i with
    | ty c =>
      rcases mids with _ | ⟨mid, _ | ⟨mid2, rest⟩⟩ <;> simp only [envStep] <;> try exact hid q
      split
      · exact envKeys_addQ q _ h' (fun I x b hx => .inl hx)
      · exact hid q
    | val x =>
      rcases mids with _ | ⟨mid, _ | ⟨mid2, rest⟩⟩ <;> simp only [envStep] <;> try exact hid q
      split
      · refine envKeys_addQ q _ h' (fun I y b hy => ?_)
        simp only [FMap.find?] at hy
        split at hy
        · rename_i e; subst e; exact .inr (by simp)
        · exact .inl hy
      · exact hid q

theorem envKeys_envOf (ME : ModEnv) : (π : ProvMap) → EnvKeys (envOf ME π) (FMap.keys π)
  | [] => ⟨fun _ _ hx => (by cases hx), fun _ _ hq => (by cases hq)⟩
  | p :: π => by
    have := envKeys_step ME p _ _ (envKeys_envOf ME π)
    simpa [envOf, FMap.keys] using this

theorem abs_piShape (B : SBasis) (π : ProvMap) : Abs (modCtx B π) (piShape π) := by
  intro lid b h
  have hk := envKeys_envOf B.ME π
  refine ⟨none, ?_, fun n hn => by cases hn⟩
  obtain ⟨q, x⟩ := lid
  simp only [piShape]
  cases q with
  | none =>
    simp only [modCtx, Ctx.lookupVal, Env.lookupVal] at h
    simp [hk.1 x b h]
  | some m =>
    simp only [modCtx, Ctx.lookupVal, Env.lookupVal] at h
    cases hq : FMap.find? (envOf B.ME π).QE m with
    | none => rw [hq] at h; cases h
    | some I =>
      rw [hq] at h
      simp [hk.2 m I hq x b h]

/-! ## Skeletons of interfaces: what the elaboration of imports reads of them -/

abbrev SkVE := List (String × IdStatus)
/-- A skeleton: the type names with the statuses of their values, and the value names. -/
abbrev SkI := FMap String SkVE × List String

def skS (s : TyStr) : SkVE := FMap.mapV s.2 Prod.snd
def skI (I : IEnv) : SkI := (FMap.mapV I.TE skS, FMap.keys I.VE)

def elabItemSk (mid : ModId) (s : SkI) : BItem → Option (List SmLongId × List SmLongId)
  | .var x => if x ∈ s.2 then some ([], [⟨none, .val x⟩]) else none
  | .op o => if o ∈ smops mid then some ([], []) else none
  | .ty c =>
    match FMap.find? s.1 c with
    | some ve => some ([⟨none, .ty c⟩], (FMap.keys (ve.filter fun p => p.2 == .v)).map fun k => ⟨none, .val k⟩)
    | none => none
  | .tyAll c =>
    match FMap.find? s.1 c with
    | some ve =>
      if (FMap.keys ve).any (fun k => (FMap.find? ve k).any (· == .c)) then
        some ([⟨none, .ty c⟩], ((FMap.keys ve).filter (· ∈ s.2)).map fun k => ⟨none, .val k⟩)
      else none
    | none => none

def elabItemsSk (mid : ModId) (s : SkI) : List BItem → Option (List SmLongId × List SmLongId)
  | [] => some ([], [])
  | it :: rest =>
    match elabItemSk mid s it, elabItemsSk mid s rest with
    | some (N, N'), some (M, M') => some (unionL N M, unionL N' M')
    | _, _ => none

def domSk (s : SkI) : List SmId := (FMap.keys s.1).map .ty ++ s.2.map .val

def elabExpListSk (mid : ModId) (s : SkI) : BExpList → Option (List SmLongId × List SmLongId)
  | .all => some ([], unqualified (domSk s))
  | .items is => elabItemsSk mid s is

def elabImportsSk (ME : ModId → Option SkI) (π : ProvMap) : List BImport → Option ProvMap
  | [] => some π
  | i :: is =>
    match ME i.mod with
    | none => none
    | some s =>
      let π1 := π.merge i.mod [] ((domSk s).map fun x => ⟨some (i.alias.getD i.mod), x⟩)
      match i.exposing with
      | none => elabImportsSk ME π1 is
      | some el =>
        match elabExpListSk i.mod s el with
        | some (N, N') => elabImportsSk ME (π1.merge i.mod N N') is
        | none => none

theorem keys_ofStatusV (VE : ValEnv) :
    FMap.keys (ValEnv.ofStatusV VE) = FMap.keys ((FMap.mapV VE Prod.snd).filter fun p => p.2 == .v) := by
  simp [ValEnv.ofStatusV, FMap.keys, FMap.mapV, List.filter_map, Function.comp_def]

theorem any_find?_mapV (VE : ValEnv) (k : String) :
    (FMap.find? (FMap.mapV VE Prod.snd) k).any (· == .c) = (FMap.find? VE k).any (·.2 == .c) := by
  rw [find?_mapV]
  cases FMap.find? VE k <;> rfl

theorem elabItem_sk (mid : ModId) (I : IEnv) (it : BItem) : elabItem (mid, I) it = elabItemSk mid (skI I) it := by
  cases it with
  | var x => simp only [elabItem, elabItemSk, skI] <;> rfl
  | op o => simp only [elabItem, elabItemSk]
  | ty c =>
    simp only [elabItem, elabItemSk, skI, find?_mapV]
    cases FMap.find? I.TE c with
    | none => rfl
    | some st =>
      obtain ⟨θ, VE⟩ := st
      simp only [Option.map_some, skS, keys_ofStatusV]
  | tyAll c =>
    simp only [elabItem, elabItemSk, skI, find?_mapV]
    cases FMap.find? I.TE c with
    | none => rfl
    | some st =>
      obtain ⟨θ, VE⟩ := st
      simp only [Option.map_some, skS, keys_mapV, any_find?_mapV] <;> rfl

theorem elabItems_sk (mid : ModId) (I : IEnv) : (is : List BItem) →
    elabItems (mid, I) is = elabItemsSk mid (skI I) is
  | [] => rfl
  | it :: rest => by
    simp only [elabItems, elabItemsSk, elabItem_sk, elabItems_sk mid I rest] <;> rfl

theorem dom_sk (I : IEnv) : domSk (skI I) = I.dom := by
  simp [domSk, skI, IEnv.dom, keys_mapV]

theorem elabExpList_sk (mid : ModId) (I : IEnv) (el : BExpList) :
    elabExpList (mid, I) el = elabExpListSk mid (skI I) el := by
  cases el with
  | all => simp only [elabExpList, elabExpListSk, dom_sk]
  | items is => exact elabItems_sk mid I is

theorem elabImports_sk (B : SBasis) : (is : List BImport) → (π : ProvMap) →
    elabImports B π is = elabImportsSk (fun mid => (FMap.find? B.ME mid).map skI) π is
  | [], π => rfl
  | i :: is, π => by
    simp only [elabImports, elabImportsSk]
    cases hI : FMap.find? B.ME i.mod with
    | none => rfl
    | some I =>
      simp only [Option.map_some]
      have hq : qualified (i.alias.getD i.mod) I = (domSk (skI I)).map fun x => ⟨some (i.alias.getD i.mod), x⟩ := by
        rw [dom_sk]; rfl
      rw [hq]
      cases i.exposing with
      | none => exact elabImports_sk B is _
      | some el =>
        simp only [elabExpList_sk]
        cases elabExpListSk i.mod (skI I) el with
        | none => rfl
        | some NN =>
          obtain ⟨N, N'⟩ := NN
          exact elabImports_sk B is _

/-! ## The skeleton of a module's interface is the same in every derivation -/

def conSkL : BConBind → SkVE
  | [] => []
  | (k, _) :: rest => FMap.modify [(k, .c)] (conSkL rest)

def datTeSkL : BDatBind → FMap String SkVE
  | [] => []
  | (c, _, cb) :: rest => FMap.modify [(c, conSkL cb)] (datTeSkL rest)

def datTeSk : Option BDatBind → FMap String SkVE
  | none => []
  | some d => datTeSkL d

def tbTeSk (tb : BTypBind) : FMap String SkVE :=
  [(tb.c, if (smlabs tb.t).isSome then [(tb.c, .v)] else [])]

def teSkTypes (db : Option BDatBind) (tbs : List BTypBind) : FMap String SkVE :=
  FMap.modify (datTeSk db) (FMap.plusAll (tbs.map tbTeSk))

/-- The skeleton of the type environment a top-level declaration gives. -/
def teSkTop : BTopDec → FMap String SkVE
  | .value _ => []
  | .types db tbs => teSkTypes db tbs
  | .port _ _ => []
  | .seq d1 d2 => FMap.modify (teSkTop d1) (teSkTop d2)

def teSkTopOpt : Option BTopDec → FMap String SkVE
  | none => []
  | some d => teSkTop d

theorem conBind_sk (C : Ctx) (τ : Ty) : (cb : BConBind) → (VE : ValEnv) →
    elabConBind C τ cb = some VE → FMap.mapV VE Prod.snd = conSkL cb
  | [], VE, h => by simp only [elabConBind, Option.some.injEq] at h; subst h; rfl
  | (k, tys) :: rest, VE, h => by
    simp only [elabConBind] at h
    split at h
    · rename_i τs VE' _ h2
      cases h
      rw [mapV_modify, conBind_sk C τ rest VE' h2]
      rfl
    · cases h

theorem closVE_sk (A : List BVar) (VE : ValEnv) : FMap.mapV (closVE A VE) Prod.snd = FMap.mapV VE Prod.snd := by
  simp [closVE, FMap.mapV, List.map_map, Function.comp_def]

theorem datBind_sk (C : Ctx) (names : String → Option TyName) : (d : BDatBind) → (VE : ValEnv) →
    (TE : TyEnv) → elabDatBind C names d = some (VE, TE) → FMap.mapV TE skS = datTeSkL d
  | [], VE, TE, h => by
    simp only [elabDatBind, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | (c, ps, cb) :: rest, VE, TE, h => by
    simp only [elabDatBind] at h
    split at h
    · cases h
    · rename_i t _
      split at h
      · rename_i τs VE' TE' _ h2
        split at h
        · rename_i VEc h3
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [mapV_modify, datBind_sk C names rest VE' TE' h2]
            simp only [datTeSkL, FMap.mapV, List.map_cons, List.map_nil, skS]
            rw [← FMap.mapV, closVE_sk, conBind_sk _ _ cb VEc h3]
          · cases h
        · cases h
      · cases h

theorem typBind_sk (C : Ctx) (tb : BTypBind) (VE : ValEnv) (TE : TyEnv)
    (h : elabTypBind C tb = some (VE, TE)) : FMap.mapV TE skS = tbTeSk tb := by
  unfold elabTypBind at h
  cases hτ : elabTy (C.plusU (seqVars tb.params (bTyExtNames tb.t))) tb.t with
  | none => rw [hτ] at h; cases h
  | some τ =>
    rw [hτ] at h
    simp only at h
    cases hl : smlabs tb.t with
    | none =>
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [tbTeSk, hl, FMap.mapV, skS]
    | some ls =>
      rw [hl] at h
      simp only at h
      match τ, h with
      | .record ρ none, h =>
        simp only at h
        cases hτs : Row.lookupAll ρ ls with
        | none => rw [hτs] at h; cases h
        | some τs =>
          rw [hτs] at h
          simp only at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [tbTeSk, hl, FMap.mapV, skS, closVE]
          · cases h
      | .record _ (some _), h => cases h
      | .var _, h => cases h
      | .fn _ _, h => cases h
      | .con _ _, h => cases h

theorem typBinds_sk (C : Ctx) : (tbs : List BTypBind) → (VEs : List ValEnv) → (TEs : List TyEnv) →
    elabTypBinds C tbs = some (VEs, TEs) → TEs.map (FMap.mapV · skS) = tbs.map tbTeSk
  | [], VEs, TEs, h => by
    simp only [elabTypBinds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | tb :: tbs, VEs, TEs, h => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE TE VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.map_cons, typBind_sk C tb VE TE h1, typBinds_sk C tbs VEs' TEs' h2]
    · cases h

theorem checkTypes_sk {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (h : checkTypes C TE VE db tbs = true) : FMap.mapV TE skS = teSkTypes db tbs := by
  replace h := checkTypes_fix h
  unfold checkTypesFix at h
  cases db with
  | none =>
    simp only at h
    split at h
    · rename_i VEs TEs h1
      simp only [decide_eq_true_eq] at h
      obtain ⟨_, rfl, _⟩ := h
      rw [mapV_plusAll, typBinds_sk _ tbs VEs TEs h1]
      simp [teSkTypes, datTeSk, FMap.modify]
    · cases h
  | some d =>
    simp only at h
    split at h
    · rename_i VE' TE' VEs TEs h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨_, _, rfl, _⟩ := h
      rw [mapV_modify, mapV_plusAll, typBinds_sk _ tbs VEs TEs h2, datBind_sk _ _ d VE' TE' h1]
      rfl
    · cases h

theorem elabPort_TE {C : Ctx} {x : Var} {ty : BTy} {U : List BVar} {E : Env} {PE : PortEnv}
    (h : elabPort C x ty U = some (E, PE)) : E.TE = [] := by
  unfold elabPort at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
          · cases h
        · cases h
    · cases h
  · cases h

theorem teSk_top : (a : ATopDec) → (C : Ctx) → (E : Env) → (PE : PortEnv) →
    checkTopDec C a = some (E, PE) → ∀ c, FMap.find? (FMap.mapV E.TE skS) c = FMap.find? (teSkTop a.erase) c
  | .value VE vb, C, E, PE, h, c => by
    simp only [checkTopDec] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · cases h
  | .types TE VE db tbs, C, E, PE, h, c => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [ATopDec.erase, teSkTop]
      rw [checkTypes_sk hc]
    · cases h
  | .port x ty U, C, E, PE, h, c => by
    simp only [checkTopDec] at h
    rw [elabPort_TE h]
    rfl
  | .seq a1 a2, C, E, PE, h, c => by
    simp only [checkTopDec] at h
    split at h
    · rename_i E1 PE1 h1
      split at h
      · rename_i E2 PE2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Env.plus, ATopDec.erase, teSkTop]
        rw [mapV_modify, FMap.find?_modify, FMap.find?_modify, teSk_top a1 C E1 PE1 h1 c,
          teSk_top a2 _ E2 PE2 h2 c]
      · cases h
    · cases h

theorem teSk_topOpt {a : Option ATopDec} {C : Ctx} {E : Env} {PE : PortEnv}
    (h : checkTopDecOpt C a = some (E, PE)) (c : String) :
    FMap.find? (FMap.mapV E.TE skS) c = FMap.find? (teSkTopOpt (a.map ATopDec.erase)) c := by
  cases a with
  | none =>
    simp only [checkTopDecOpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | some d => exact teSk_top d C E PE h c

def exposeItemSk (T : FMap String SkVE) : BItem → Option SkI
  | .var x => some ([], [x])
  | .op _ => none
  | .ty c => (FMap.find? T c).map fun ve => ([(c, ve)], FMap.keys (ve.filter fun p => p.2 == .v))
  | .tyAll c => (FMap.find? T c).map fun ve => ([(c, ve)], FMap.keys ve)

def plusSk (s s' : SkI) : SkI :=
  (FMap.modify s.1 s'.1, s'.2 ++ s.2.filter fun k => !decide (k ∈ s'.2))

def exposeItemsSk (T : FMap String SkVE) : List BItem → Option SkI
  | [] => some ([], [])
  | it :: rest =>
    match exposeItemSk T it, exposeItemsSk T rest with
    | some s, some s' => some (plusSk s s')
    | _, _ => none

theorem skI_plus (I I' : IEnv) : skI (I.plus I') = plusSk (skI I) (skI I') := by
  simp only [skI, IEnv.plus, plusSk, mapV_modify, keys_modify] <;> rfl

theorem exposeItem_sk {E : Env} {T : FMap String SkVE}
    (hT : ∀ c, FMap.find? (FMap.mapV E.TE skS) c = FMap.find? T c) (it : BItem) (I : IEnv)
    (h : exposeItem E it = some I) : exposeItemSk T it = some (skI I) := by
  cases it with
  | var x =>
    simp only [exposeItem] at h
    cases hx : FMap.find? E.VE x with
    | none => rw [hx] at h; cases h
    | some b =>
      rw [hx] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rfl
  | op o => simp [exposeItem] at h
  | ty c =>
    simp only [exposeItem] at h
    have hc := hT c
    rw [find?_mapV] at hc
    cases hx : FMap.find? E.TE c with
    | none => rw [hx] at h; cases h
    | some st =>
      rw [hx] at h hc
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp only [exposeItemSk, ← hc, Option.map_some, skI, keys_ofStatusV]
      rfl
  | tyAll c =>
    simp only [exposeItem] at h
    have hc := hT c
    rw [find?_mapV] at hc
    cases hx : FMap.find? E.TE c with
    | none => rw [hx] at h; cases h
    | some st =>
      rw [hx] at h hc
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp only [exposeItemSk, ← hc, Option.map_some, skI, skS, keys_mapV]
      rfl

theorem exposeItems_sk {E : Env} {T : FMap String SkVE}
    (hT : ∀ c, FMap.find? (FMap.mapV E.TE skS) c = FMap.find? T c) : (is : List BItem) → (I : IEnv) →
    exposeItems E is = some I → exposeItemsSk T is = some (skI I)
  | [], I, h => by
    simp only [exposeItems, Option.some.injEq] at h
    subst h
    rfl
  | it :: rest, I, h => by
    simp only [exposeItems] at h
    split at h
    · rename_i I1 I2 h1 h2
      cases h
      simp only [exposeItemsSk, exposeItem_sk hT it I1 h1, exposeItems_sk hT rest I2 h2, skI_plus]
    · cases h

/-! ## Two modules: the second module's imports, or its body, fail for every derivation of the first -/

/-- The skeleton of the interface of a module whose header lists what it exposes. -/
def helperSk (m : BModule) : Option SkI :=
  match m.header.exposing with
  | .all => none
  | .items is => exposeItemsSk (teSkTopOpt m.body) is

/-- The modules' skeletons after the first module's interface is added under its name. -/
def meSk (B : SBasis) (name : ModId) (s : SkI) : ModId → Option SkI := fun mid =>
  if name = mid then some s else (FMap.find? B.ME mid).map skI

def scope2 (B : SBasis) (m1 m2 : BModule) : Bool :=
  match helperSk m1 with
  | none => false
  | some s =>
    match elabImportsSk (meSk B m1.header.name s) π0 (defaultImports ++ m2.imports) with
    | none => true
    | some π => !(scTopOpt (piShape π) m2.body)

theorem result_inv {B : SBasis} {a : AModule} {B' : SBasis} {E : Env} (h : a.result B = some (B', E)) :
    ∃ C E' PE I, checkTopDecOpt C a.body = some (E', PE) ∧ expose E' a.header.exposing = some I ∧
      B'.ME = [(a.header.name, I)] := by
  unfold AModule.result at h
  cases hC : importCtx B a.imports with
  | none => rw [hC] at h; cases h
  | some C =>
    rw [hC] at h
    simp only at h
    unfold AModule.resultIn at h
    split at h
    · cases h
    · rename_i E' PE hd
      split at h
      · cases h
      · rename_i I hI
        split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨C, E', PE, I, hd, hI, rfl⟩

theorem noDeriv_scope2 {B : SBasis} {m1 m2 : BModule} (h : scope2 B m1 m2 = true) :
    ∀ a1 B' E, a1.erase = m1 → checkModule B a1 = true → a1.result B = some (B', E) →
      NoDeriv (B.plus B') m2 := by
  intro a1 B' E he1 _ hr
  obtain ⟨C, E', PE, I, hd, hI, hME⟩ := result_inv hr
  have hh : a1.header = m1.header := by rw [← he1]; rfl
  have hb : a1.body.map ATopDec.erase = m1.body := by rw [← he1]; rfl
  unfold scope2 at h
  cases hs : helperSk m1 with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only at h
    -- the skeleton of the first module's interface
    have hsk : s = skI I := by
      rw [hh] at hI
      cases hx : m1.header.exposing with
      | all => simp only [helperSk, hx] at hs; cases hs
      | items is =>
        simp only [helperSk, hx] at hs
        rw [hx] at hI
        have hT := teSk_topOpt hd
        rw [hb] at hT
        have := exposeItems_sk hT is I hI
        rw [hs] at this
        exact (Option.some.inj this)
    have hme : (fun mid => (FMap.find? (B.plus B').ME mid).map skI) = meSk B m1.header.name s := by
      funext mid
      simp only [SBasis.plus, meSk, hME, FMap.find?_modify, FMap.find?, hh, hsk]
      by_cases e : m1.header.name = mid <;> simp [e]
    intro a2 he2
    have him : a2.imports = m2.imports := by rw [← he2]; rfl
    unfold checkModule AModule.result importCtx
    rw [elabImports_sk, hme, him]
    cases hπ : elabImportsSk (meSk B m1.header.name s) π0 (defaultImports ++ m2.imports) with
    | none => rfl
    | some π =>
      rw [hπ] at h
      simp only [Bool.not_eq_true'] at h
      simp only [Option.map_some]
      have hb2 : a2.body.map ATopDec.erase = m2.body := by rw [← he2]; rfl
      unfold AModule.resultIn
      cases hd2 : checkTopDecOpt (modCtx (B.plus B') π) a2.body with
      | none => rfl
      | some EP =>
        obtain ⟨E2, PE2⟩ := EP
        have := sc_topOpt (abs_piShape (B.plus B') π) hd2
        rw [hb2, h] at this
        cases this

end StandardElm.Stat.RScope

namespace StandardElm.Stat

/-- The decider: the first module is out of scope (or has a constructor pattern of the wrong
    arity) in its import context, or the second module's imports or body fail whatever the
    derivation of the first. -/
def scopeFailB (B : SBasis) (sp : Src.SProgram) : Bool :=
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | m :: rest =>
    RScope.scope1 B m ||
      (match rest with
       | m2 :: _ => RScope.scope2 B m m2
       | [] => false)
  | [] => false

theorem not_legal_of_scopeFailB {B : SBasis} {sp : Src.SProgram} (h : scopeFailB B sp = true) :
    ¬ LegalProgram B sp := by
  unfold scopeFailB at h
  split at h
  · rename_i m rest hms
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact not_legal_of_noDeriv hms (RScope.noDeriv_scope1 h)
    · split at h
      · rename_i m2 rest2
        exact not_legal_of_noDeriv2 hms (RScope.noDeriv_scope2 h)
      · cases h
  · cases h

end StandardElm.Stat
