/-
  A Standard Definition of Elm? Mechanisation: the meaning of a program and the general theorems of
  the pipeline, plan step 10 ("The pipeline, SpecOf and r:p-program"; Theorems, "Copy names",
  "Payload types, main", "The pipeline").

  `SpecOf B p r`: r is what specialisation and erasure give on a principal program derivation of p
  (finding B1). `ProgramSem` is r:p-program (programs.tex) with both premises: the static one
  (step 9's `ElProgram`) and the dynamic one on the specialisation of the program. From a run of the
  pipeline (`endToEnd B s = .ok r`) and D11 for the program (`InferPrincipalFor`, `D11For`), r is a
  specialisation of the program; with the program's legality (step 9's `legal_X`) and a value of
  its reduced modules (Part I's `t_X`), the program has a meaning by r:p-program.
-/
import StandardElmMech.Stat.EndToEndIn
import StandardElmMech.Stat.CopyLoop

namespace StandardElm.Stat
open StandardElm (Var Lab ModId)
open StandardElm.Src (BImport BModule BProgram SProgram)

/-! ## Definitions -/

/-- D11's hypothesis for one program, in the form the theorems of this step need: what the
    inference returns for it is principal. -/
def D11For (B : SBasis) (p : BProgram) : Prop := InferPrincipalFor B p

/-- The specialisation of the program: what reduce gives on a principal program derivation. -/
def SpecOf (B : SBasis) (p : BProgram) (r : Mod.Reduced) : Prop :=
  ∃ a, PrincipalProgDeriv B p a ∧ reduceProgram B a = .ok r

/-- ⊢_DYN (r:p-dyn-module, r:p-dyn-main) on the reduced part of a program, in Part I's test basis. -/
def DynOf (r : Mod.Reduced) (v : Val) : Prop := Mod.EvalProgram (Mod.Btest []) r.modules v

/-- B_stat ⊢_STAT program ⇒ (τ, PE): step 9's `ElProgram` on the program's modules. -/
abbrev StatProgram (B : SBasis) (p : BProgram) (τ : Ty) (PE : PortEnv) : Prop :=
  ElProgram B p.modules τ PE

/-- r:p-program (programs.tex), in the reading of finding B1: the dynamic premise is about the
    specialisation of the program. -/
inductive ProgramSem (Bs : SBasis) : BProgram → Ty × PortEnv × Val → Prop
  /-- r:p-program -/
  | r_p_program {p : BProgram} {τ : Ty} {PE : PortEnv} {r : Mod.Reduced} {v : Val} :
      StatProgram Bs p τ PE → SpecOf Bs p r → DynOf r v → ProgramSem Bs p (τ, PE, v)

/-! ## Copy names -/

theorem Assignment.isDefault_default (k : Nat) : (Assignment.default k).isDefault = true := by
  simp [Assignment.isDefault, Assignment.default, List.all_replicate]

theorem copyName_default (x : Var) (k : Nat) : copyName x (Assignment.default k) = x := by
  simp [copyName, Assignment.isDefault_default]

/-- The characters of a key: the keys of the numbers joined by `$`. -/
def keyChars : Assignment → List Char
  | [] => []
  | [n] => (Num.key n).toList
  | n :: m :: rest => (Num.key n).toList ++ '$' :: keyChars (m :: rest)

theorem key_toList : ∀ a : Assignment, (Assignment.key a).toList = keyChars a
  | [] => by simp [Assignment.key, keyChars]
  | [n] => by simp [Assignment.key, keyChars]
  | n :: m :: rest => by
    have ih := key_toList (m :: rest)
    simp only [Assignment.key, List.map_cons] at ih ⊢
    rw [String.intercalate_cons_cons, String.toList_append, String.toList_append, ih]
    simp [keyChars]

theorem num_key_toList (n : Num) : (Num.key n).toList = if n = .int then ['I', 'n', 't'] else ['F', 'l', 'o', 'a', 't'] := by
  cases n <;> rfl

theorem keyChars_inj : ∀ (a b : Assignment), a.length = b.length → keyChars a = keyChars b → a = b
  | [], [], _, _ => rfl
  | [n], [m], _, h => by
    simp only [keyChars, num_key_toList] at h
    cases n <;> cases m <;> simp at h <;> rfl
  | n :: n' :: as, m :: m' :: bs, hl, h => by
    simp only [keyChars, num_key_toList] at h
    have ih := keyChars_inj (n' :: as) (m' :: bs) (by simpa using hl)
    cases n <;> cases m <;> simp at h <;> simp [ih h]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | [_], _ :: _ :: _, hl, _ => by simp at hl
  | _ :: _ :: _, [_], hl, _ => by simp at hl

/-- The part before the first `$`. -/
theorem append_dollar_inj : ∀ (l1 l2 r1 r2 : List Char), '$' ∉ l1 → '$' ∉ l2 →
    l1 ++ '$' :: r1 = l2 ++ '$' :: r2 → l1 = l2 ∧ r1 = r2
  | [], [], _, _, _, _, h => by simpa using h
  | [], c :: l2, _, _, _, h2, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h2
  | c :: l1, [], _, _, h1, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h1
  | c :: l1, d :: l2, r1, r2, h1, h2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := append_dollar_inj l1 l2 r1 r2 (fun hm => h1 (List.mem_cons_of_mem _ hm))
      (fun hm => h2 (List.mem_cons_of_mem _ hm)) h
    exact ⟨by rw [this.1], this.2⟩

theorem isDefault_iff (a : Assignment) : a.isDefault = true ↔ a = Assignment.default a.length := by
  simp only [Assignment.isDefault, Assignment.default, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h; exact List.eq_replicate_iff.mpr ⟨rfl, h⟩
  · intro h n hn; rw [h] at hn; exact List.eq_of_mem_replicate hn

/-- Copy names are new and distinct (`$` spells no identifier, syntax-core). -/
theorem copyName_inj {x y : Var} {a b : Assignment} (ha : a.length = b.length)
    (hx : '$' ∉ x.toList) (hy : '$' ∉ y.toList) (h : copyName x a = copyName y b) : x = y ∧ a = b := by
  unfold copyName at h
  by_cases da : a.isDefault = true <;> by_cases db : b.isDefault = true <;>
    simp only [da, db, ↓reduceIte, Bool.false_eq_true] at h
  · refine ⟨h, ?_⟩
    rw [(isDefault_iff a).mp da, (isDefault_iff b).mp db, ha]
  · exfalso; apply hx; rw [h]; simp [String.toList_append]
  · exfalso; apply hy; rw [← h]; simp [String.toList_append]
  · have h' := congrArg String.toList h
    simp only [String.toList_append, List.append_assoc] at h'
    have : ("$" : String).toList = ['$'] := rfl
    rw [this] at h'
    simp only [List.singleton_append] at h'
    obtain ⟨h1, h2⟩ := append_dollar_inj _ _ _ _ hx hy h'
    rw [key_toList, key_toList] at h2
    exact ⟨String.toList_inj.mp h1, keyChars_inj a b ha h2⟩

/-! ## Payload types and `main` -/

mutual
theorem toPTy_isSome : (τ : Ty) → (toPTy τ).isSome = portB τ
  | .con [] t => by
    simp only [toPTy, portB]
    by_cases h1 : t = tInt; · subst h1; rfl
    by_cases h2 : t = tFloat; · subst h2; rfl
    by_cases h3 : t = tBool; · subst h3; rfl
    by_cases h4 : t = tString; · subst h4; rfl
    by_cases h5 : t = tBytes; · subst h5; rfl
    by_cases h6 : t = tUnit; · subst h6; rfl
    by_cases h7 : t = tValue; · subst h7; rfl
    simp [h1, h2, h3, h4, h5, h6, h7]
  | .con [τ] t => by
    have ih := toPTy_isSome τ
    simp only [toPTy, portB]
    by_cases h1 : t = tList; · subst h1; simp [ih]
    by_cases h2 : t = tMaybe; · subst h2; simp [ih, show tMaybe ≠ tList from by decide]
    by_cases h3 : t = tArray
    · subst h3; simp [ih, show tArray ≠ tList from by decide, show tArray ≠ tMaybe from by decide]
    simp [h1, h2, h3]
  | .con [τ1, τ2] t => by
    have ih1 := toPTy_isSome τ1
    have ih2 := toPTy_isSome τ2
    simp only [toPTy, portB]
    by_cases h : t = tTuple2
    · subst h
      simp only [ite_true, beq_self_eq_true, Bool.true_and]
      rw [← ih1, ← ih2]
      cases toPTy τ1 <;> cases toPTy τ2 <;> rfl
    · simp [h]
  | .con [τ1, τ2, τ3] t => by
    have ih1 := toPTy_isSome τ1
    have ih2 := toPTy_isSome τ2
    have ih3 := toPTy_isSome τ3
    simp only [toPTy, portB]
    by_cases h : t = tTuple3
    · subst h
      simp only [ite_true, beq_self_eq_true, Bool.true_and]
      rw [← ih1, ← ih2, ← ih3]
      cases toPTy τ1 <;> cases toPTy τ2 <;> cases toPTy τ3 <;> rfl
    · simp [h]
  | .con (_ :: _ :: _ :: _ :: _) _ => by simp [toPTy, portB]
  | .record ρ none => by
    simp only [toPTy, portB, Option.isSome_map]
    exact toPFields_isSome ρ
  | .record _ (some _) => by simp [toPTy, portB]
  | .var _ => by simp [toPTy, portB]
  | .fn _ _ => by simp [toPTy, portB]
theorem toPFields_isSome : (ρ : Row) → (toPFields ρ).isSome = portRowB ρ
  | [] => rfl
  | (l, τ) :: rest => by
    have ih1 := toPTy_isSome τ
    have ih2 := toPFields_isSome rest
    simp only [toPFields, portRowB]
    rw [← ih1, ← ih2]
    cases toPTy τ <;> cases toPFields rest <;> rfl
end

theorem portRowB_of_all : ∀ (ρ : Row), (∀ l τ, (l, τ) ∈ ρ → portB τ = true) → portRowB ρ = true
  | [], _ => rfl
  | (l, τ) :: rest, h => by
    simp only [portRowB, Bool.and_eq_true]
    exact ⟨h l τ List.mem_cons_self, portRowB_of_all rest fun l' τ' hm => h l' τ' (List.mem_cons_of_mem _ hm)⟩

theorem portB_complete {τ : Ty} (h : Port τ) : portB τ = true := by
  induction h with
  | int | float | bool | string | bytes | unit | value => rfl
  | list _ ih => simp [listTy, portB, ih]
  | maybe _ ih => simp [portB, ih]
  | array _ ih => simp [portB, ih]
  | tuple2 _ _ ih1 ih2 => simp [portB, ih1, ih2]
  | tuple3 _ _ _ ih1 ih2 ih3 => simp [portB, ih1, ih2, ih3]
  | @record ρ _ ih =>
    simp only [portB]
    exact portRowB_of_all ρ ih

/-- fig:static-modules-port: `toPTy` is defined exactly on the types of `Port`. -/
theorem toPTy_isSome_iff (τ : Ty) : (toPTy τ).isSome ↔ Port τ := by
  rw [toPTy_isSome]
  exact ⟨portB_sound τ, portB_complete⟩

theorem port_of_toPTy {τ : Ty} {π : Eff.PTy} (h : toPTy τ = some π) : Port τ :=
  (toPTy_isSome_iff τ).mp (by simp [h])

theorem mainKind_worker_iff (σ : Scheme) (π : Eff.PTy) :
    mainKind σ = some (.worker, π) ↔
      ∃ τ1 τ2 τ3, σ.body = .con [τ1, τ2, τ3] tProgram ∧ Port τ1 ∧ toPTy τ1 = some π := by
  unfold mainKind
  constructor
  · intro h
    split at h
    · rename_i τ1 τ2 τ3 t hb
      split at h
      · rename_i ht
        subst ht
        cases hp : toPTy τ1 with
        | none => rw [hp] at h; cases h
        | some π' =>
          rw [hp] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨τ1, τ2, τ3, hb, port_of_toPTy hp, hp⟩
      · split at h
        · split at h <;> simp at h
        · cases h
    · split at h
      · split at h <;> simp at h
      · cases h
  · rintro ⟨τ1, τ2, τ3, hb, -, hp⟩
    rw [hb]
    simp [hp]

theorem mainKind_view_iff (σ : Scheme) (π : Eff.PTy) :
    mainKind σ = some (.view, π) ↔ π = .unit ∧
      (¬ ∃ τ1 τ2 τ3, σ.body = .con [τ1, τ2, τ3] tProgram) ∧ ∃ τ, dflt σ = .con [τ] tNode := by
  unfold mainKind
  constructor
  · intro h
    split at h
    · rename_i τ1 τ2 τ3 t hb
      split at h
      · rename_i ht
        cases toPTy τ1 <;> simp at h
      · rename_i ht
        split at h
        · rename_i τ t' hd
          split at h
          · rename_i ht'
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            refine ⟨rfl, ?_, τ, ht' ▸ hd⟩
            rintro ⟨τ1', τ2', τ3', hb'⟩
            rw [hb] at hb'
            cases hb'
            exact ht rfl
          · cases h
        · cases h
    · rename_i hb
      split at h
      · rename_i τ t' hd
        split at h
        · rename_i ht'
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          refine ⟨rfl, ?_, τ, ht' ▸ hd⟩
          rintro ⟨τ1', τ2', τ3', hb'⟩
          exact hb τ1' τ2' τ3' tProgram hb'
        · cases h
      · cases h
  · rintro ⟨rfl, hnp, τ, hd⟩
    split
    · rename_i τ1 τ2 τ3 t hb
      split
      · rename_i ht
        exact absurd ⟨τ1, τ2, τ3, ht ▸ hb⟩ hnp
      · rw [hd]; simp
    · rw [hd]; simp

/-! ## The pipeline -/

theorem checkProgram_of_progResults {B : SBasis} {a : AProgram} {rs : List (SBasis × SBasis × Env)}
    (h : progResults B a = some rs) : checkProgram B a = true := by
  rw [← progResults_isSome, h]; rfl

/-- What a successful run of the pipeline gives: the derivation the inference returned, the
    results of its modules, and the reduced program. -/
theorem endToEnd_ok {B : SBasis} {s : SProgram} {r : Mod.Reduced} (h : endToEnd B s = .ok r) :
    ∃ a rs, inferProgram B (bareOf s) = .ok a ∧ progResults B a = some rs ∧
      a.map AModule.erase = (bareOf s).modules ∧ checksAll rs = true ∧ reduceWith B a rs = .ok r := by
  unfold endToEnd at h
  dsimp only at h
  cases hi : inferProgram B (bareOf s) with
  | error e => simp only [hi, Except.mapError, bind, Except.bind] at h; cases h
  | ok a =>
    simp only [hi, Except.mapError, bind, Except.bind] at h
    cases hr : progResults B a with
    | none => rw [hr] at h; cases h
    | some rs =>
      rw [hr] at h
      simp only at h
      by_cases hc : (a.map AModule.erase == (bareOf s).modules && checksAll rs) = true
      · simp only [hc, ↓reduceIte] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        refine ⟨a, rs, rfl, hr, hc.1, hc.2, ?_⟩
        cases hw : reduceWith B a rs with
        | error e => rw [hw] at h; cases h
        | ok r' => rw [hw] at h; cases h; rfl
      · simp only [hc] at h; cases h

theorem principalProgDeriv_of_endToEnd {B : SBasis} {s : SProgram} {r : Mod.Reduced}
    (hI : InferPrincipalFor B (bareOf s)) (h : endToEnd B s = .ok r) :
    ∃ a, PrincipalProgDeriv B (bareOf s) a ∧ reduceProgram B a = .ok r := by
  obtain ⟨a, rs, hi, hr, -, -, hw⟩ := endToEnd_ok h
  refine ⟨a, hI a hi (checkProgram_of_progResults hr), ?_⟩
  simp only [reduceProgram, hr, hw]

/-- A run of the pipeline gives a specialisation of the program, under D11 for it. -/
theorem specOf_of_endToEnd {B : SBasis} {s : SProgram} {r : Mod.Reduced}
    (hI : InferPrincipalFor B (bareOf s)) (h : endToEnd B s = .ok r) : SpecOf B (bareOf s) r :=
  principalProgDeriv_of_endToEnd hI h

/-- The further restrictions (sec:static-modules-further, A96) on the modules of what the inference
    returns for a program. `endToEnd` does not check them (they refuse programs, they do not change
    the reduced program); step 9's legality does. -/
def FurtherFor (B : SBasis) (p : BProgram) : Prop :=
  ∀ a, inferProgram B p = .ok a → ∀ Bs, AProgram.bases B a = some Bs →
    ∀ i (h : i < a.length) (h' : i < Bs.length), FurtherMod Bs[i] a[i]

theorem bases_of_progResults : ∀ {B : SBasis} {a : AProgram} {rs : List (SBasis × SBasis × Env)},
    progResults B a = some rs → AProgram.bases B a = some (rs.map (·.1))
  | _, [], rs, h => by simp only [progResults, Option.some.injEq] at h; subst h; rfl
  | B, m :: rest, rs, h => by
    simp only [progResults] at h
    cases hm : m.result B with
    | none => rw [hm] at h; cases h
    | some p =>
      obtain ⟨B', E⟩ := p
      simp only [hm] at h
      cases hr : progResults (B.plus B') rest with
      | none => simp [hr] at h
      | some rs' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        simp [AProgram.bases, hm, bases_of_progResults hr]

theorem progResults_length : ∀ {B : SBasis} {a : AProgram} {rs : List (SBasis × SBasis × Env)},
    progResults B a = some rs → rs.length = a.length
  | _, [], rs, h => by simp only [progResults, Option.some.injEq] at h; subst h; rfl
  | B, m :: rest, rs, h => by
    simp only [progResults] at h
    cases hm : m.result B with
    | none => simp [hm] at h
    | some p =>
      obtain ⟨B', E⟩ := p
      simp only [hm] at h
      cases hr : progResults (B.plus B') rest with
      | none => simp [hr] at h
      | some rs' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        simp [progResults_length hr]

theorem mainScheme_some : ∀ {rs : List (SBasis × SBasis × Env)} {σ : Scheme}, mainScheme rs = some σ →
    ∃ rs0 B B' E, rs = rs0 ++ [(B, B', E)] ∧ E.VE.find? "main" = some (σ, .v)
  | [], _, h => by cases h
  | [(B, B', E)], σ, h => by
    simp only [mainScheme] at h
    split at h
    · rename_i σ' h'; cases h; exact ⟨[], B, B', E, rfl, h'⟩
    · cases h
  | x :: y :: rest, σ, h => by
    have h' : mainScheme (y :: rest) = some σ := h
    obtain ⟨rs0, B, B', E, e, hf⟩ := mainScheme_some h'
    exact ⟨x :: rs0, B, B', E, by rw [e]; rfl, hf⟩

/-- r:p-stat-main-program or r:p-stat-main-view from `mainKind`. -/
theorem elProgram_main_of_kind {B : SBasis} {m : BModule} {B' : SBasis} {E : Env} {σ : Scheme}
    {k : Mod.ProgKind × Eff.PTy} (hd : PrincipalModDer B m B' E) (hp : PortsDisjoint B B')
    (hσ : E.VE.find? "main" = some (σ, .v)) (hk : mainKind σ = some k) :
    ∃ τ, ElProgram B [m] τ (B.plus B').PE := by
  obtain ⟨kind, π⟩ := k
  cases kind with
  | worker =>
    obtain ⟨τ1, τ2, τ3, hb, hP, -⟩ := (mainKind_worker_iff σ π).mp hk
    exact ⟨_, .r_p_stat_main_program hd hp hσ hb hP⟩
  | view =>
    obtain ⟨-, -, τ, hd'⟩ := (mainKind_view_iff σ π).mp hk
    exact ⟨_, .r_p_stat_main_view hd hp hσ hd'⟩

theorem elProgram_of_results : ∀ (B : SBasis) (a : AProgram) (Bs : List SBasis)
    (rs : List (SBasis × SBasis × Env)),
    progResults B a = some rs → AProgram.bases B a = some Bs →
    (∀ i (h : i < a.length) (h' : i < Bs.length), IsPrincipalMod Bs[i] a[i]) →
    (∀ i (h : i < a.length) (h' : i < Bs.length), FurtherMod Bs[i] a[i]) →
    checksAll rs = true → a ≠ [] → ∃ τ PE, ElProgram B (a.map AModule.erase) τ PE
  | _, [], _, _, _, _, _, _, _, hne => absurd rfl hne
  | B, m :: rest, Bs, rs, hr, hb, hp, hf, hc, _ => by
    simp only [progResults] at hr
    cases hm : m.result B with
    | none => rw [hm] at hr; cases hr
    | some pr =>
      obtain ⟨B', E⟩ := pr
      simp only [hm] at hr
      cases hrr : progResults (B.plus B') rest with
      | none => simp [hrr] at hr
      | some rs' =>
        simp only [hrr, Option.map_some, Option.some.injEq] at hr
        subst hr
        simp only [AProgram.bases, hm] at hb
        cases hbr : AProgram.bases (B.plus B') rest with
        | none => simp [hbr] at hb
        | some Bs' =>
          simp only [hbr, Option.map_some, Option.some.injEq] at hb
          subst hb
          simp only [checksAll, List.all_cons, Bool.and_eq_true] at hc
          obtain ⟨⟨hpd, hall⟩, hmain⟩ := hc
          have hprin : IsPrincipalMod B m := hp 0 (by simp) (by simp)
          have hfm : FurtherMod B m := hf 0 (by simp) (by simp)
          have hder : PrincipalModDer B m.erase B' E := ⟨m, rfl, hprin, hm, hfm⟩
          cases rest with
          | nil =>
            simp only [progResults, Option.some.injEq] at hrr
            subst hrr
            simp only [mainScheme] at hmain
            split at hmain
            · rename_i σ hσ
              obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (by simpa using hmain)
              obtain ⟨τ, hel⟩ := elProgram_main_of_kind hder (portsDisjointB_sound hpd) hσ hk
              exact ⟨τ, _, hel⟩
            · simp at hmain
          | cons m2 rest2 =>
            have hc' : checksAll rs' = true := by
              simp only [checksAll, Bool.and_eq_true]
              refine ⟨hall, ?_⟩
              have : mainScheme ((B, B', E) :: rs') = mainScheme rs' := by
                cases rs' with
                | nil => have := progResults_length hrr; simp at this
                | cons _ _ => rfl
              rw [← this]; exact hmain
            obtain ⟨τ, PE, hel⟩ := elProgram_of_results (B.plus B') (m2 :: rest2) Bs' rs' hrr hbr
              (fun i h1 h2 => hp (i + 1) (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega))
              (fun i h1 h2 => hf (i + 1) (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega))
              hc' (by simp)
            exact ⟨τ, PE, .r_p_stat_module hder (portsDisjointB_sound hpd) (by simp) hel⟩

/-- A run of the pipeline gives the static premise of r:p-program, under D11 for the program and
    its further restrictions. -/
theorem statProgram_of_endToEnd {B : SBasis} {s : SProgram} {r : Mod.Reduced}
    (hI : InferPrincipalFor B (bareOf s)) (hF : FurtherFor B (bareOf s)) (h : endToEnd B s = .ok r) :
    ∃ τ PE, StatProgram B (bareOf s) τ PE := by
  obtain ⟨a, rs, hi, hr, he, hc, -⟩ := endToEnd_ok h
  obtain ⟨-, Bs, hBs, hpr⟩ := hI a hi (checkProgram_of_progResults hr)
  have hne : a ≠ [] := by
    rintro rfl
    simp [progResults] at hr; subst hr
    simp [checksAll, mainScheme] at hc
  obtain ⟨τ, PE, hel⟩ := elProgram_of_results B a Bs rs hr hBs hpr (hF a hi Bs hBs) hc hne
  refine ⟨τ, PE, ?_⟩
  show ElProgram B (bareOf s).modules τ PE
  rw [← he]; exact hel

/-- r:p-program with both premises, from a run of the pipeline, the static premise, and a value of
    the reduced modules. -/
theorem programSem_of_spec {B : SBasis} {s : SProgram} {r : Mod.Reduced}
    (hI : InferPrincipalFor B (bareOf s)) (h : endToEnd B s = .ok r)
    (hS : ∃ τ PE, StatProgram B (bareOf s) τ PE) (hv : ∃ v, DynOf r v) :
    ∃ τ PE v, ProgramSem B (bareOf s) (τ, PE, v) := by
  obtain ⟨τ, PE, hst⟩ := hS
  obtain ⟨v, hd⟩ := hv
  exact ⟨τ, PE, v, .r_p_program hst (specOf_of_endToEnd hI h) hd⟩

/-- The same, with the static premise from step 9's legality of the program (`legal_X h`). -/
theorem programSem_of_legal {B : SBasis} {s : SProgram} {r : Mod.Reduced}
    (hI : D11For B (bareOf s)) (h : endToEnd B s = .ok r) (hL : LegalProgram B s)
    (hv : ∃ v, DynOf r v) : ∃ τ PE v, ProgramSem B (bareOf s) (τ, PE, v) :=
  programSem_of_spec hI h hL.2 hv

/-! ## Values of Part I's programs -/

/-- A check statement includes a value of the program (the logged relation's forget, D4). -/
theorem value_of_viewChecks {B : Mod.Basis} {ms : List Mod.Module} {cs : List LogCheck}
    (h : Mod.ViewChecks B ms cs) : ∃ v, Mod.EvalProgram B ms v := by
  obtain ⟨v, l, hl, -⟩ := h
  exact ⟨v, hl.forget⟩

/-- A worker's execution starts from the value of `main`. -/
theorem value_of_holds {w : Prog.WorkerTest} (h : w.Holds) :
    ∃ v, Mod.EvalProgram (Mod.Btest []) w.prog.modules v := by
  obtain ⟨lg, ⟨r, lm, K0, ls, π, hs, he, -⟩, -⟩ := h
  exact ⟨_, he.forget⟩

theorem dynOf_view {g : Program} {v : Val} : DynOf g.reduced v ↔ Mod.EvalProgram (Mod.Btest []) g.modules v :=
  Iff.rfl

theorem dynOf_worker {w : Prog.WorkerTest} {v : Val} :
    DynOf w.reduced v ↔ Mod.EvalProgram (Mod.Btest []) w.prog.modules v :=
  Iff.rfl

end StandardElm.Stat
