/-
  A Standard Definition of Elm? Mechanisation: the property of interfaces (dynamic-modules.tex,
  sec:dynamic-modules-objects, the paragraph after the definition of interfaces), plan step 2.

  An interface I has the property when every record alias it lists is bound in its VE, and every
  constructor that one of its CE entries binds is bound in its VE to the same value. The interfaces
  of ME0 and the harness have it (`ME0_good`); a top-level declaration whose bound names are
  distinct infers an interface that has it (`EvalTopDec.good`); and the exposing list of a header
  keeps it (`EvalHeader.good`), so every interface a module's derivation puts in the basis has it
  (`EvalModule.good`).
-/
import StandardElmMech.Mod.Properties
import StandardElmMech.Mod.ME0

namespace StandardElm.Mod
open StandardElm StandardElm.Eff

/-- The property of interfaces. -/
def Interface.Good (I : Interface) : Prop :=
  (∀ t ∈ I.RA, (fmLookup I.VE t).isSome) ∧
  (∀ t VEt c v, fmLookup I.CE t = some VEt → fmLookup VEt c = some v → fmLookup I.VE c = some v)

/-! ## Bound names -/

/-- The constructors a constructor binding binds. -/
def ConBind.names : ConBind → List String
  | .mk c none => [c.name]
  | .mk c (some cb) => c.name :: cb.names

/-- The constructors a custom-type binding binds. -/
def DatBind.names : DatBind → List String
  | .mk _ cb none => cb.names
  | .mk _ cb (some db) => cb.names ++ db.names

/-- The names a top-level declaration binds in VE: group variables, ports, constructors, the
    constructors of record aliases. The restrictions of Section sec:syntax-modules-restrictions
    make them distinct. -/
def TopDec.boundNames : TopDec → List String
  | .val vb => vb.map Prod.fst
  | .type db => db.names
  | .alias tb => match tb.labels with
    | some _ => [tb.tycon]
    | none => []
  | .port x _ _ => [x]
  | .seq a b => a.boundNames ++ b.boundNames

/-! ## Finite maps -/

theorem fmLookup_isSome_mem {β : Type} : ∀ (f : List (String × β)) (a : String),
    (fmLookup f a).isSome → a ∈ fmDom f
  | [], a, h => by simp [fmLookup] at h
  | (k, x) :: f, a, h => by
    simp only [fmLookup] at h
    by_cases hk : k = a
    · subst hk; simp [fmDom]
    · have hk' : (k == a) = false := by simpa using hk
      rw [hk'] at h
      have := fmLookup_isSome_mem f a (by simpa using h)
      simp only [fmDom, List.map_cons, List.mem_cons]
      exact Or.inr this

theorem fmLookup_none_of_not_mem {β : Type} (f : List (String × β)) (a : String)
    (h : a ∉ fmDom f) : fmLookup f a = none := by
  cases hl : fmLookup f a with
  | none => rfl
  | some x => exact absurd (fmLookup_isSome_mem f a (by simp [hl])) h

theorem fmLookup_fmPlus_some_right {β : Type} {f g : List (String × β)} {a : String} {x : β}
    (h : fmLookup g a = some x) : fmLookup (fmPlus f g) a = some x := by
  rw [fmLookup_fmPlus, h]

theorem fmLookup_fmPlus_left {β : Type} {f g : List (String × β)} {a : String}
    (h : fmLookup g a = none) : fmLookup (fmPlus f g) a = fmLookup f a := by
  rw [fmLookup_fmPlus, h]

theorem fmLookup_fmPlus_isSome {β : Type} {f g : List (String × β)} {a : String}
    (h : (fmLookup f a).isSome ∨ (fmLookup g a).isSome) : (fmLookup (fmPlus f g) a).isSome := by
  rw [fmLookup_fmPlus]
  cases hg : fmLookup g a with
  | some x => rfl
  | none => rcases h with h | h
            · simpa using h
            · simp [hg] at h

/-- A binding of f + g is a binding of g, or of f where g binds nothing. -/
theorem fmLookup_fmPlus_cases {β : Type} {f g : List (String × β)} {a : String} {x : β}
    (h : fmLookup (fmPlus f g) a = some x) :
    fmLookup g a = some x ∨ (fmLookup g a = none ∧ fmLookup f a = some x) := by
  rw [fmLookup_fmPlus] at h
  cases hg : fmLookup g a with
  | some y => rw [hg] at h; exact Or.inl h
  | none => rw [hg] at h; exact Or.inr ⟨rfl, h⟩

theorem fmLookup_fmPlus_isSome_cases {β : Type} {f g : List (String × β)} {a : String}
    (h : (fmLookup (fmPlus f g) a).isSome) : (fmLookup f a).isSome ∨ (fmLookup g a).isSome := by
  rw [fmLookup_fmPlus] at h
  cases hg : fmLookup g a with
  | some y => exact Or.inr rfl
  | none => rw [hg] at h; exact Or.inl h

theorem fmLookup_singleton_isSome {β : Type} {k a : String} {x : β}
    (h : (fmLookup [(k, x)] a).isSome) : a = k := by
  simp only [fmLookup] at h
  by_cases hk : k = a
  · exact hk.symm
  · have hk' : (k == a) = false := by simpa using hk
    simp [hk'] at h

/-! ## The domains of the bindings -/

theorem EvalConBind.dom : ∀ {cb : ConBind} {VE : ValEnv}, EvalConBind cb VE →
    ∀ c, (fmLookup VE c).isSome → c ∈ cb.names
  | .mk c0 none, _, .r_dm_conbind _ _ _ .opt_none, c, h => by
    rcases fmLookup_fmPlus_isSome_cases h with h | h
    · simp [ConBind.names, fmLookup_singleton_isSome h]
    · simp [fmLookup] at h
  | .mk c0 (some cb), _, .r_dm_conbind _ _ VE' (.opt_some _ _ h'), c, h => by
    rcases fmLookup_fmPlus_isSome_cases h with h | h
    · simp [ConBind.names, fmLookup_singleton_isSome h]
    · simp only [ConBind.names, List.mem_cons]; exact Or.inr (EvalConBind.dom h' c h)

theorem EvalDatBind.dom : ∀ {db : DatBind} {CE : ConEnv} {VE : ValEnv}, EvalDatBind db CE VE →
    ∀ c, (fmLookup VE c).isSome → c ∈ db.names
  | .mk _ cb none, _, _, .r_dm_datbind _ _ _ _ _ _ hcb .opt_none, c, h => by
    rcases fmLookup_fmPlus_isSome_cases h with h | h
    · exact EvalConBind.dom hcb c h
    · simp [fmLookup] at h
  | .mk _ cb (some db), _, _, .r_dm_datbind _ _ _ _ _ _ hcb (.opt_some _ _ _ hdb), c, h => by
    simp only [DatBind.names, List.mem_append]
    rcases fmLookup_fmPlus_isSome_cases h with h | h
    · exact Or.inl (EvalConBind.dom hcb c h)
    · exact Or.inr (EvalDatBind.dom hdb c h)

theorem zip_keys_isSome {β : Type} : ∀ (xs : List String) (vs : List β) (a : String),
    (fmLookup (xs.zip vs) a).isSome → a ∈ xs := by
  intro xs vs a h
  have := fmLookup_isSome_mem _ a h
  simp only [fmDom, List.mem_map] at this
  obtain ⟨⟨k, v⟩, hm, rfl⟩ := this
  exact (List.of_mem_zip hm).1

/-- A top-level declaration's interface binds in its VE only the names the declaration binds. -/
theorem EvalTopDec.dom : ∀ {E : Env} {td : TopDec} {I : Interface}, EvalTopDec E td I →
    ∀ x, (fmLookup I.VE x).isSome → x ∈ td.boundNames
  | _, _, _, .r_dm_topdec_val _ vb _ vs _ _ _, x, h => by
    simp only [Interface.ofVE] at h
    simpa [TopDec.boundNames] using zip_keys_isSome _ _ x h
  | _, _, _, .r_dm_topdec_type _ _ _ _ hdb, x, h => EvalDatBind.dom hdb x h
  | _, _, _, .r_dm_topdec_alias _ ⟨t, ls⟩ _ _ (.r_dm_typbind _ _), x, h => by
    cases ls with
    | none => simp [fmLookup] at h
    | some ls => simp [TopDec.boundNames, fmLookup_singleton_isSome h]
  | _, _, _, .r_dm_topdec_port_out _ _ _, x, h => by
    simp [Interface.ofVE] at h; simp [TopDec.boundNames, fmLookup_singleton_isSome h]
  | _, _, _, .r_dm_topdec_port_in _ _ _, x, h => by
    simp [Interface.ofVE] at h; simp [TopDec.boundNames, fmLookup_singleton_isSome h]
  | _, _, _, .r_dm_topdec_seq _ _ _ _ _ _ _ h1 h2, x, h => by
    simp only [Interface.plus] at h
    simp only [TopDec.boundNames, List.mem_append]
    rcases fmLookup_fmPlus_isSome_cases h with h | h
    · exact Or.inl (EvalTopDec.dom h1 x h)
    · exact Or.inr (EvalTopDec.dom h2 x h)

/-! ## Top-level declarations -/

theorem fmLookup_singleton_some {β : Type} {k a : String} {x y : β}
    (h : fmLookup [(k, x)] a = some y) : y = x := by
  simp only [fmLookup] at h
  split at h
  · exact (Option.some.inj h).symm
  · simp at h

theorem nodup_append_disjoint {l1 l2 : List String} (h : (l1 ++ l2).Nodup) {a : String}
    (h1 : a ∈ l1) : a ∉ l2 :=
  fun h2 => (List.nodup_append.mp h).2.2 a h1 a h2 rfl

theorem nodup_append_left {l1 l2 : List String} (h : (l1 ++ l2).Nodup) : l1.Nodup :=
  (List.nodup_append.mp h).1

theorem nodup_append_right {l1 l2 : List String} (h : (l1 ++ l2).Nodup) : l2.Nodup :=
  (List.nodup_append.mp h).2.1

/-- A binding of VE outside the names a derivation binds is none. -/
theorem none_of_not_bound {VE : ValEnv} {names : List String} {c : String}
    (hdom : ∀ c, (fmLookup VE c).isSome → c ∈ names) (h : c ∉ names) : fmLookup VE c = none := by
  cases hl : fmLookup VE c with
  | none => rfl
  | some w => exact absurd (hdom c (by simp [hl])) h

/-- The constructors of a custom-type binding: each CE entry's bindings are VE's, when the
    constructors are distinct. -/
theorem EvalDatBind.good : ∀ {db : DatBind} {CE : ConEnv} {VE : ValEnv}, EvalDatBind db CE VE →
    db.names.Nodup → ∀ t VEt c v, fmLookup CE t = some VEt → fmLookup VEt c = some v →
      fmLookup VE c = some v
  | .mk _ cb none, _, _, .r_dm_datbind _ _ _ _ _ _ hcb .opt_none, _, t, VEt, c, v, h1, h2 => by
    rcases fmLookup_fmPlus_cases h1 with h | ⟨_, h⟩
    · simp [fmLookup] at h
    · rw [fmLookup_singleton_some h] at h2
      rw [fmLookup_fmPlus_left (by simp [fmLookup])]; exact h2
  | .mk _ cb (some db), _, _, .r_dm_datbind _ _ _ VEcb CE' VE' hcb (.opt_some _ _ _ hdb), hnd,
      t, VEt, c, v, h1, h2 => by
    rcases fmLookup_fmPlus_cases h1 with h | ⟨_, h⟩
    · exact fmLookup_fmPlus_some_right
        (EvalDatBind.good hdb (nodup_append_right hnd) t VEt c v h h2)
    · rw [fmLookup_singleton_some h] at h2
      have hc : c ∈ cb.names := EvalConBind.dom hcb c (by simp [h2])
      have hnone : fmLookup VE' c = none :=
        none_of_not_bound (EvalDatBind.dom hdb) (nodup_append_disjoint hnd hc)
      rw [fmLookup_fmPlus_left hnone]; exact h2

theorem ofVE_good (VE : ValEnv) : (Interface.ofVE VE).Good :=
  ⟨fun t h => by simp [Interface.ofVE] at h, fun t VEt c v h => by simp [Interface.ofVE, fmLookup] at h⟩

theorem empty_good : Interface.empty.Good :=
  ⟨fun t h => by simp [Interface.empty] at h, fun t VEt c v h => by simp [Interface.empty, fmLookup] at h⟩

/-- A top-level declaration whose bound names are distinct infers an interface with the property
    (the restrictions of sec:syntax-modules-restrictions make them distinct). -/
theorem EvalTopDec.good : ∀ {E : Env} {td : TopDec} {I : Interface}, EvalTopDec E td I →
    td.boundNames.Nodup → I.Good
  | _, _, _, .r_dm_topdec_val _ vb _ vs _ _ _, _ => ofVE_good _
  | _, _, _, .r_dm_topdec_type _ _ _ _ hdb, hnd =>
    ⟨fun t h => by simp at h, fun t VEt c v h1 h2 => EvalDatBind.good hdb hnd t VEt c v h1 h2⟩
  | _, _, _, .r_dm_topdec_alias _ ⟨t, ls⟩ _ _ (.r_dm_typbind _ _), _ => by
    cases ls with
    | none => exact ⟨fun t h => by simp at h, fun t VEt c v h => by simp [fmLookup] at h⟩
    | some ls =>
      refine ⟨fun t' h => ?_, fun t VEt c v h => by simp [fmLookup] at h⟩
      simp only [List.mem_singleton] at h; subst h; simp [fmLookup]
  | _, _, _, .r_dm_topdec_port_out _ _ _, _ => ofVE_good _
  | _, _, _, .r_dm_topdec_port_in _ _ _, _ => ofVE_good _
  | _, _, _, .r_dm_topdec_seq _ t1 t2 RA1 CE1 VE1 I2 h1 h2, hnd => by
    have g1 := EvalTopDec.good h1 (nodup_append_left hnd)
    have g2 := EvalTopDec.good h2 (nodup_append_right hnd)
    refine ⟨fun t ht => ?_, fun t VEt c v hce hc => ?_⟩
    · simp only [Interface.plus, List.mem_append] at ht ⊢
      rcases ht with ht | ht
      · exact fmLookup_fmPlus_isSome (Or.inl (g1.1 t ht))
      · exact fmLookup_fmPlus_isSome (Or.inr (g2.1 t ht))
    · simp only [Interface.plus] at hce ⊢
      rcases fmLookup_fmPlus_cases hce with h | ⟨_, h⟩
      · exact fmLookup_fmPlus_some_right (g2.2 t VEt c v h hc)
      · have hv1 : fmLookup VE1 c = some v := g1.2 t VEt c v h hc
        have hc1 : c ∈ t1.boundNames := EvalTopDec.dom h1 c (by simp [hv1])
        have hnone : fmLookup I2.VE c = none :=
          none_of_not_bound (EvalTopDec.dom h2) (nodup_append_disjoint hnd hc1)
        rw [fmLookup_fmPlus_left hnone]; exact hv1

/-! ## Headers -/

/-- J is part of the interface I exposes from: its bindings are I's, and it has the property. -/
def Interface.PartOf (I J : Interface) : Prop :=
  (∀ c w, fmLookup J.VE c = some w → fmLookup I.VE c = some w) ∧ J.Good

theorem partOf_empty (I : Interface) : I.PartOf .empty :=
  ⟨fun c w h => by simp [Interface.empty, fmLookup] at h, empty_good⟩

theorem partOf_plus {I J1 J2 : Interface} (h1 : I.PartOf J1) (h2 : I.PartOf J2) :
    I.PartOf (J1.plus J2) := by
  refine ⟨fun c w h => ?_, fun t ht => ?_, fun t VEt c v hce hc => ?_⟩
  · simp only [Interface.plus] at h
    rcases fmLookup_fmPlus_cases h with h | ⟨_, h⟩
    · exact h2.1 c w h
    · exact h1.1 c w h
  · simp only [Interface.plus, List.mem_append] at ht ⊢
    rcases ht with ht | ht
    · exact fmLookup_fmPlus_isSome (Or.inl (h1.2.1 t ht))
    · exact fmLookup_fmPlus_isSome (Or.inr (h2.2.1 t ht))
  · simp only [Interface.plus] at hce ⊢
    rcases fmLookup_fmPlus_cases hce with h | ⟨_, h⟩
    · exact fmLookup_fmPlus_some_right (h2.2.2 t VEt c v h hc)
    · have hv1 : fmLookup J1.VE c = some v := h1.2.2 t VEt c v h hc
      cases hj2 : fmLookup J2.VE c with
      | some w =>
        have e1 := h2.1 c w hj2
        have e2 := h1.1 c v hv1
        rw [e1] at e2
        rw [fmLookup_fmPlus_some_right hj2, e2]
      | none => rw [fmLookup_fmPlus_left hj2]; exact hv1

theorem partOf_foldl {I : Interface} : ∀ (Js : List Interface) (acc : Interface),
    I.PartOf acc → (∀ J ∈ Js, I.PartOf J) → I.PartOf (Js.foldl Interface.plus acc)
  | [], _, ha, _ => ha
  | J :: Js, acc, ha, hJ =>
    partOf_foldl Js _ (partOf_plus ha (hJ J (by simp))) (fun J' hm => hJ J' (by simp [hm]))

theorem EvalExpItem.partOf {I : Interface} (hI : I.Good) : ∀ {it : ExpItem} {J : Interface},
    EvalExpItem I it J → I.PartOf J
  | _, _, .r_dm_expitem_var _ x v hv =>
    ⟨fun c w h => by
      simp only [Interface.ofVE] at h
      have := fmLookup_singleton_isSome (by simp [h] : (fmLookup [(x, v)] c).isSome)
      subst this; rw [fmLookup_singleton_some h]; exact hv, ofVE_good _⟩
  | _, _, .r_dm_expitem_op _ _ => partOf_empty I
  | _, _, .r_dm_expitem_alias _ t v _ hv =>
    ⟨fun c w h => by
      simp only at h
      have := fmLookup_singleton_isSome (by simp [h] : (fmLookup [(t, v)] c).isSome)
      subst this; rw [fmLookup_singleton_some h]; exact hv,
     fun t' ht => by simp only [List.mem_singleton] at ht; subst ht; simp [fmLookup],
     fun t' VEt c v' h => by simp [fmLookup] at h⟩
  | _, _, .r_dm_expitem_type _ t CE _ hCE =>
    ⟨fun c w h => by simp [fmLookup] at h,
     fun t' ht => by simp at ht,
     fun t' VEt c v h1 h2 => by
      simp only at h1
      subst hCE
      split at h1
      · rw [fmLookup_singleton_some h1] at h2; simp [fmLookup] at h2
      · simp [fmLookup] at h1⟩
  | _, _, .r_dm_expitem_open _ t VE hVE =>
    ⟨fun c w h => hI.2 t VE c w hVE h,
     fun t' ht => by simp at ht,
     fun t' VEt c v h1 h2 => by
      simp only at h1 ⊢
      rw [fmLookup_singleton_some h1] at h2; exact h2⟩

theorem EvalExpItems.partOf {I : Interface} (hI : I.Good) : ∀ {is : List ExpItem}
    {Is : List Interface}, EvalExpItems I is Is → ∀ J ∈ Is, I.PartOf J
  | _, _, .seq_nil _, J, hm => by simp at hm
  | _, _, .seq_cons _ _ _ _ _ h hs, J, hm => by
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact EvalExpItem.partOf hI h
    · exact EvalExpItems.partOf hI hs J hm

/-- The exposing list of a header keeps the property. -/
theorem EvalHeader.good {I : Interface} {h : Header} {m : ModId} {I' : Interface}
    (d : EvalHeader I h m I') (hI : I.Good) : I'.Good := by
  cases d
  rename_i dl
  cases dl with
  | r_dm_explist_all => exact hI
  | r_dm_explist_items _ Is _ hs =>
    exact (partOf_foldl Is .empty (partOf_empty I) (EvalExpItems.partOf hI hs)).2

/-- Every interface a module's derivation puts in the basis has the property, when the module's
    bound names are distinct. -/
theorem EvalModule.good {B : Basis} {m : Module} {B' : Basis} {VE : ValEnv}
    (d : EvalModule B m B' VE) (hnd : m.body.boundNames.Nodup) :
    ∀ md I, fmLookup B' md = some I → I.Good := by
  cases d
  rename_i htd hh
  intro md I hl
  rw [fmLookup_singleton_some hl]
  exact EvalHeader.good hh (EvalTopDec.good htd hnd)

/-! ## ME0 and the harness -/

theorem fmLookup_some_mem {β : Type} : ∀ (f : List (String × β)) (a : String) (x : β),
    fmLookup f a = some x → (a, x) ∈ f
  | [], _, _, h => by simp [fmLookup] at h
  | (k, y) :: f, a, x, h => by
    simp only [fmLookup] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk; cases h; simp
    · exact List.mem_cons_of_mem _ (fmLookup_some_mem f a x h)

theorem mem_fmPlus {β : Type} {f g : List (String × β)} {p : String × β} (h : p ∈ fmPlus f g) :
    p ∈ f ∨ p ∈ g := by
  unfold fmPlus at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inr h
  · exact Or.inl (List.mem_filter.mp h).1

/-- An interface without record aliases has the property when every constructor its CE entries
    bind is bound in its VE to the same value. -/
theorem good_of_entries {CE : ConEnv} {VE : ValEnv}
    (h : ∀ p ∈ CE, ∀ q ∈ p.2, fmLookup VE q.1 = some q.2) : (⟨[], CE, VE⟩ : Interface).Good :=
  ⟨fun t ht => by simp at ht, fun t VEt c v h1 h2 =>
    h (t, VEt) (fmLookup_some_mem CE t VEt h1) (c, v) (fmLookup_some_mem VEt c v h2)⟩

theorem I_Basics_good : I_Basics.Good := by
  unfold I_Basics
  apply good_of_entries
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, fun q h => by simp at h⟩

theorem I_Maybe_good : I_Maybe.Good := by
  unfold I_Maybe VE_MaybeI
  apply good_of_entries
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨rfl, rfl⟩

theorem I_Result_good : I_Result.Good := by
  unfold I_Result VE_ResultI
  apply good_of_entries
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨rfl, rfl⟩

/-- The interfaces of ME0 and of the harness have the property. -/
theorem ME0_good : ∀ md I, fmLookup (Btest []) md = some I → I.Good := by
  intro md I h
  have hm := fmLookup_some_mem _ md I h
  simp only [Btest, List.foldl_nil] at hm
  rcases mem_fmPlus hm with hm | hm
  · simp only [ME0, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    all_goals first
      | exact I_Basics_good | exact I_Maybe_good | exact I_Result_good | exact empty_good
      | exact ofVE_good _
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨_, rfl⟩ := hm
    exact ofVE_good _

end StandardElm.Mod
