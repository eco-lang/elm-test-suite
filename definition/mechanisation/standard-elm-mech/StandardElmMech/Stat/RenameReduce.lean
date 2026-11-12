/-
  A Standard Definition of Elm? Mechanisation: the invariance lemma at the level of `reduceWith`
  (plan step 10, `reduceProgram_rename` and `reduceProgram_equiv`, stated as the coordinator's
  revision of 2026-11-12 asks: per-module renamings, invariance of `reduceWith` given the facts it
  reads of the modules' results).

  `reduceWith B a rs` reads the results `rs` of the modules only through each module's provider
  map, the payload types of its ports, and the kind of the last module's `main`; and the annotated
  modules only through their headers, imports and top-level items. `ProgRel` says that two
  programs agree on all of these, each module's items related by its own renaming
  (`RenameSpec.lean`); `reduceWith_rename` concludes that they give the same reduced program.
-/
import StandardElmMech.Stat.RenameSpecExp
import StandardElmMech.Stat.EndToEnd

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BImport BHeader)

/-! ## The identity renaming -/

def Renaming.id : Renaming := ⟨fun a => a, fun e => e, []⟩

theorem Renaming.id_wf : Renaming.id.WF :=
  ⟨fun _ _ h => h, fun _ => rfl, fun _ _ => rfl, fun _ _ h => h, fun _ => rfl, fun _ _ _ => Iff.rfl⟩

mutual
theorem Renaming.ty_id : (τ : Ty) → Renaming.id.ty τ = τ
  | .var _ => rfl
  | .record ρ tl => by
    simp only [Renaming.ty, Renaming.row_id ρ]
    cases tl <;> rfl
  | .fn a b => by simp only [Renaming.ty, Renaming.ty_id a, Renaming.ty_id b]
  | .con as t => by simp only [Renaming.ty, Renaming.tys_id as]; rfl
theorem Renaming.row_id : (ρ : Row) → Renaming.id.row ρ = ρ
  | [] => rfl
  | (l, τ) :: rest => by simp only [Renaming.row, Renaming.ty_id τ, Renaming.row_id rest]
theorem Renaming.tys_id : (l : List Ty) → Renaming.id.tys l = l
  | [] => rfl
  | τ :: rest => by simp only [Renaming.tys, Renaming.ty_id τ, Renaming.tys_id rest]
end

theorem Renaming.bvar_id (v : BVar) : Renaming.id.bvar v = v := by cases v <;> rfl

theorem Renaming.ref_id (ref : Ref) : Renaming.id.ref ref = ref := by
  have h1 : ∀ V : List TyVar, V.map Renaming.id.tvApply = V := fun V => by
    induction V with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, ih]; rfl
  have h2 : ∀ bv : List BVar, bv.map Renaming.id.bvar = bv := fun bv => by
    induction bv with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, ih, Renaming.bvar_id]
  cases ref <;> simp only [Renaming.ref, Renaming.ty_id, h1, h2]

theorem GlobRel.refl : ∀ (g : List ((ModId × Var) × Ref)), (∀ e ∈ g, e.2.Closed) → GlobRel g g
  | [], _ => trivial
  | e :: es, h =>
    ⟨rfl, ⟨Renaming.id, Renaming.id_wf, (Renaming.ref_id e.2).symm, h e (List.mem_cons_self ..)⟩,
      GlobRel.refl es fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

theorem GlobRel.append : ∀ {g g' h h' : List ((ModId × Var) × Ref)}, GlobRel g g' → GlobRel h h' →
    GlobRel (g ++ h) (g' ++ h')
  | [], [], _, _, _, hh => hh
  | _ :: _, _ :: _, _, _, hg, hh => ⟨hg.1, hg.2.1, GlobRel.append hg.2.2 hh⟩
  | [], _ :: _, _, _, hg, _ | _ :: _, [], _, _, hg, _ => hg.elim

theorem basisRefs_closed (B : SBasis) : ∀ e ∈ basisRefs B, e.2.Closed := by
  intro e he
  unfold basisRefs at he
  obtain ⟨⟨m, x⟩, _, he⟩ := List.mem_filterMap.mp he
  simp only at he
  split at he
  · cases he
    intro v hv
    simp only [List.mem_filterMap] at hv
    obtain ⟨w, hw, e⟩ := hv
    cases w with
    | ty a =>
      by_cases hc : a.cls = .num
      · simp only [hc, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at e
        subst e; exact hw
      · simp [hc] at e
    | row _ => simp at e
  · cases he

/-! ## Top-level items and groups -/

def ItemRel (r : Renaming) (D : BVar → Prop) : TopItem → TopItem → Prop
  | .value VE vb, .value VE' vb' => VE' = r.valEnv VE ∧ (∀ p ∈ VE, ∀ v ∈ p.2.1.tyvars, D v) ∧ RValBind r D vb vb'
  | .types db tbs, .types db' tbs' => db' = db ∧ tbs' = tbs
  | .port x, .port x' => x' = x
  | _, _ => False

def ItemsRel (r : Renaming) (D : BVar → Prop) : List TopItem → List TopItem → Prop
  | [], [] => True
  | i :: is, i' :: is' => ItemRel r D i i' ∧ ItemsRel r D is is'
  | _, _ => False

structure GroupRel (r : Renaming) (D : BVar → Prop) (G G' : TopGroup) : Prop where
  gid : G'.gid = G.gid
  VE : G'.VE = r.valEnv G.VE
  VED : ∀ p ∈ G.VE, ∀ v ∈ p.2.1.tyvars, D v
  vb : RValBind r D G.vb G'.vb
  members : MembersRel r D G.view.members G'.view.members
  V : G'.V = G.V.map r.tvApply

def GroupsRel (r : Renaming) (D : BVar → Prop) : List TopGroup → List TopGroup → Prop
  | [], [] => True
  | G :: gs, G' :: gs' => GroupRel r D G G' ∧ GroupsRel r D gs gs'
  | _, _ => False

theorem topGroups_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    ∀ (n : Nat) {is is' : List TopItem}, ItemsRel r D is is' → GroupsRel r D (topGroupsFrom n is) (topGroupsFrom n is')
  | _, [], [], _ => trivial
  | n, .value VE vb :: is, .value VE' vb' :: is', h => by
    obtain ⟨⟨hVE, hD, hvb⟩, h2⟩ := h
    subst hVE
    have hA : ∀ v, D v → (v ∈ ([] : List BVar) ↔ r.bvar v ∈ ([] : List BVar)) := by simp
    obtain ⟨hm, hV⟩ := groupView_rename hr hA hD hvb
    exact ⟨⟨rfl, rfl, hD, hvb, hm, hV⟩, topGroups_rename hr (n + 1) h2⟩
  | n, .types _ _ :: is, .types _ _ :: is', h => by simp only [topGroupsFrom]; exact topGroups_rename hr n h.2
  | n, .port _ :: is, .port _ :: is', h => by simp only [topGroupsFrom]; exact topGroups_rename hr n h.2
  | _, .value _ _ :: _, .types _ _ :: _, h | _, .value _ _ :: _, .port _ :: _, h
  | _, .types _ _ :: _, .value _ _ :: _, h | _, .types _ _ :: _, .port _ :: _, h
  | _, .port _ :: _, .value _ _ :: _, h | _, .port _ :: _, .types _ _ :: _, h
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp [ItemsRel, ItemRel] at h

theorem GroupsRel.length {r : Renaming} {D : BVar → Prop} :
    ∀ {gs gs' : List TopGroup}, GroupsRel r D gs gs' → gs'.length = gs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, GroupsRel.length h.2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem GroupsRel.refsOut {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    ∀ {gs gs' : List TopGroup}, GroupsRel r D gs gs' →
      gs'.flatMap TopGroup.refsOut = r.binds (gs.flatMap TopGroup.refsOut)
  | [], [], _ => rfl
  | G :: gs, G' :: gs', h => by
    simp only [List.flatMap_cons, Renaming.binds_append, GroupsRel.refsOut hr h.2]
    congr 1
    unfold TopGroup.refsOut
    rw [h.1.V, h.1.gid]
    exact refsOut_rename hr G.gid G.V h.1.members
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem GroupRel.refsIn {r : Renaming} {D : BVar → Prop} {G G' : TopGroup} (h : GroupRel r D G G') :
    G'.refsIn = r.binds G.refsIn := by
  unfold TopGroup.refsIn
  rw [h.V, h.gid]
  exact refsIn_rename r G.gid G.V h.members

theorem zip_map_numEnv (r : Renaming) (V : List TyVar) (a : Assignment) :
    (V.map r.tvApply).zip a = r.numEnv (V.zip a) := by
  have := numEnv_zip r V a []
  simpa [Renaming.numEnv] using this

theorem CtxRel.empty (r : Renaming) (D : BVar → Prop) : CtxRel r D Ctx.empty Ctx.empty :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp [Ctx.empty]⟩

theorem specTop_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {Γ Γ' : Scope} (hΓ : ScopeRel r Γ Γ')
    (T : Nat) : ∀ {gs gs' : List TopGroup}, GroupsRel r D gs gs' → ∀ inc, specTop Γ' T gs' inc = specTop Γ T gs inc
  | [], [], _, _ => rfl
  | G :: gs, G' :: gs', h, inc => by
    have hG := h.1
    have hvbs : (fun a => specValBind (G'.V.zip a) (Γ'.push G'.refsIn) (Ctx.empty.plusVE G'.VE) T a G'.vb) =
        (fun a => specValBind (G.V.zip a) (Γ.push G.refsIn) (Ctx.empty.plusVE G.VE) T a G.vb) := by
      funext a
      rw [hG.V, zip_map_numEnv, hG.refsIn, hG.VE]
      exact specValBind_rename hr G.vb hG.vb (G.V.zip a) T a (hΓ.push _) ((CtxRel.empty r D).plusVE G.VE)
    simp only [specTop]
    rw [specTop_rename hr hΓ T h.2 inc, hvbs, hG.V, hG.gid]
    simp only [List.length_map]
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

/-! ## Modules -/

structure ModInfoRel (r : Renaming) (D : BVar → Prop) (mi mi' : ModInfo) : Prop where
  header : mi'.header = mi.header
  imports : mi'.imports = mi.imports
  groups : GroupsRel r D mi.groups mi'.groups
  prov : mi'.prov = mi.prov
  types : eraseTypeDecs mi'.items = eraseTypeDecs mi.items
  ports : portsOf mi'.PE mi'.items = portsOf mi.PE mi.items

def ModInfosRel : List ModInfo → List ModInfo → Prop
  | [], [] => True
  | mi :: ms, mi' :: ms' => (∃ (r : Renaming) (D : BVar → Prop), r.WF ∧ ModInfoRel r D mi mi') ∧ ModInfosRel ms ms'
  | _, _ => False

theorem globals_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {mi mi' : ModInfo} (h : ModInfoRel r D mi mi') :
    GlobRel mi.globals mi'.globals := by
  unfold ModInfo.globals
  rw [h.header]
  have key : ∀ {gs gs' : List TopGroup}, GroupsRel r D gs gs' →
      GlobRel (gs.flatMap fun G => if G.V.isEmpty then [] else G.view.members.map fun m =>
          ((mi.header.name, m.x), Ref.group G.gid G.V m.body (m.bOutAll G.V)))
        (gs'.flatMap fun G => if G.V.isEmpty then [] else G.view.members.map fun m =>
          ((mi.header.name, m.x), Ref.group G.gid G.V m.body (m.bOutAll G.V))) := by
    intro gs gs' hg
    induction gs generalizing gs' with
    | nil => cases gs' with
      | nil => trivial
      | cons _ _ => exact hg.elim
    | cons G gs ih =>
      cases gs' with
      | nil => exact hg.elim
      | cons G' gs' =>
        obtain ⟨hG, h2⟩ := hg
        simp only [List.flatMap_cons]
        apply GlobRel.append _ (ih h2)
        rw [hG.V, hG.gid]
        simp only [List.isEmpty_map]
        split
        · trivial
        · have : ∀ {ms ms' : List Member}, MembersRel r D ms ms' →
              GlobRel (ms.map fun m => ((mi.header.name, m.x), Ref.group G.gid G.V m.body (m.bOutAll G.V)))
                (ms'.map fun m => ((mi.header.name, m.x),
                  Ref.group G.gid (G.V.map r.tvApply) m.body (m.bOutAll (G.V.map r.tvApply)))) := by
            intro ms ms' hm
            induction ms generalizing ms' with
            | nil => cases ms' with
              | nil => trivial
              | cons _ _ => exact hm.elim
            | cons m ms ihm =>
              cases ms' with
              | nil => exact hm.elim
              | cons m' ms' =>
                refine ⟨by simp [hm.1.x], ⟨r, hr, ?_, ?_⟩, ihm hm.2⟩
                · simp only [Renaming.ref, hm.1.body, bOutAll_rename hr G.V hm.1.bOut]
                · intro v hv
                  simp only [Member.bOutAll, List.mem_append, List.mem_map, List.mem_filter]
                  by_cases hc : m.bOut.contains (.ty v) = true
                  · exact .inl (List.contains_iff_mem.mp hc)
                  · exact .inr ⟨v, ⟨hv, by simpa using hc⟩, rfl⟩
          exact this hG.members
  exact key h.groups

theorem specMods_rename (B : SBasis) (T : Nat) :
    ∀ {mis mis' : List ModInfo} {glob glob' : List ((ModId × Var) × Ref)}, ModInfosRel mis mis' →
      GlobRel glob glob' → specMods B T glob' mis' = specMods B T glob mis
  | [], [], _, _, _, _ => rfl
  | mi :: rest, mi' :: rest', glob, glob', h, hg => by
    obtain ⟨⟨r, D, hr, hmi⟩, h2⟩ := h
    have ih := specMods_rename B T h2 (hg.append (globals_rename hr hmi))
    have hΓ : ScopeRel r ⟨[], mi.groups.flatMap TopGroup.refsOut, glob ++ basisRefs B, mi.prov⟩
        ⟨[], mi'.groups.flatMap TopGroup.refsOut, glob' ++ basisRefs B, mi'.prov⟩ :=
      ⟨rfl, hmi.groups.refsOut hr, hg.append (GlobRel.refl _ (basisRefs_closed B)), hmi.prov⟩
    simp only [specMods, ih]
    congr 1; funext x
    rw [specTop_rename hr hΓ T hmi.groups]
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

theorem copies_rename {r : Renaming} {D : BVar → Prop} {mi mi' : ModInfo} (h : ModInfoRel r D mi mi')
    (mades : List (List (Assignment × List StandardElm.D.Def))) : mi'.copies mades = mi.copies mades := by
  unfold ModInfo.copies
  have key : ∀ {gs gs' : List TopGroup}, GroupsRel r D gs gs' → ∀ mades : List (List (Assignment × List StandardElm.D.Def)),
      (gs'.zip mades).flatMap (fun (G, made) => copyTable G made) =
        (gs.zip mades).flatMap (fun (G, made) => copyTable G made) := by
    intro gs gs' hg
    induction gs generalizing gs' with
    | nil => cases gs' with
      | nil => intro _; rfl
      | cons _ _ => exact hg.elim
    | cons G gs ih =>
      cases gs' with
      | nil => exact hg.elim
      | cons G' gs' =>
        intro mades
        cases mades with
        | nil => rfl
        | cons made rest =>
          simp only [List.zip_cons_cons, List.flatMap_cons, ih hg.2 rest]
          congr 1
          unfold copyTable
          split
          · rfl
          · have := MembersRel.map (fun m => (m.x, (orderAssignments (made.map (·.1))).map (copyName m.x)))
                (fun m => (m.x, (orderAssignments (made.map (·.1))).map (copyName m.x))) (fun p => p)
                (fun m m' hm => by simp only [hm.x]) hg.1.members
            rw [List.map_id'] at this
            exact this
  exact key h.groups mades

theorem buildModules_rename (B : SBasis) :
    ∀ {mis mis' : List ModInfo}, ModInfosRel mis mis' → ∀ tables mades,
      buildModules B tables mis' mades = buildModules B tables mis mades
  | [], [], _, _, _ => rfl
  | mi :: rest, mi' :: rest', h, tables, mades => by
    obtain ⟨⟨r, D, _, hmi⟩, h2⟩ := h
    cases mades with
    | nil => rfl
    | cons md mds =>
      have hb : buildModule B tables mi' md = buildModule B tables mi md := by
        unfold buildModule
        rw [copies_rename hmi, hmi.types, hmi.ports, hmi.header, hmi.imports]
      simp only [buildModules]
      rw [hb, copies_rename hmi, hmi.header, buildModules_rename B h2]
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-! ## Programs -/

/-- What `modInfos` reads of one module and its result, related. -/
def TopItem.isValue : TopItem → Bool
  | .value _ _ => true
  | _ => false

/-- The value declarations among the top-level items (what `topGroupsFrom` reads). -/
def valuesOnly (is : List TopItem) : List TopItem := is.filter TopItem.isValue

theorem topGroupsFrom_values : ∀ (n : Nat) (is : List TopItem), topGroupsFrom n (valuesOnly is) = topGroupsFrom n is
  | _, [] => rfl
  | n, .value VE vb :: is => by
    simp only [valuesOnly, List.filter_cons, TopItem.isValue, ↓reduceIte, topGroupsFrom]
    exact congrArg _ (topGroupsFrom_values (n + 1) is)
  | n, .types _ _ :: is => by
    simp only [valuesOnly, List.filter_cons, TopItem.isValue, Bool.false_eq_true, ↓reduceIte, topGroupsFrom]
    exact topGroupsFrom_values n is
  | n, .port _ :: is => by
    simp only [valuesOnly, List.filter_cons, TopItem.isValue, Bool.false_eq_true, ↓reduceIte, topGroupsFrom]
    exact topGroupsFrom_values n is

def ModResRel (m : AModule) (res : SBasis × SBasis × Env) (m' : AModule) (res' : SBasis × SBasis × Env) : Prop :=
  m'.header = m.header ∧ m'.imports = m.imports ∧
  (elabImports res'.1 π0 (defaultImports ++ m'.imports)).getD [] = (elabImports res.1 π0 (defaultImports ++ m.imports)).getD [] ∧
  portsOf res'.2.1.PE ((m'.body.map ATopDec.items).getD []) = portsOf res.2.1.PE ((m.body.map ATopDec.items).getD []) ∧
  eraseTypeDecs ((m'.body.map ATopDec.items).getD []) = eraseTypeDecs ((m.body.map ATopDec.items).getD []) ∧
  ∃ (r : Renaming) (D : BVar → Prop), r.WF ∧
    ItemsRel r D (valuesOnly ((m.body.map ATopDec.items).getD [])) (valuesOnly ((m'.body.map ATopDec.items).getD []))

def ProgRel : AProgram → List (SBasis × SBasis × Env) → AProgram → List (SBasis × SBasis × Env) → Prop
  | m :: ms, res :: rs, m' :: ms', res' :: rs' => ModResRel m res m' res' ∧ ProgRel ms rs ms' rs'
  | [], [], [], [] => True
  | _, _, _, _ => False

theorem ItemsRel.types {r : Renaming} {D : BVar → Prop} :
    ∀ {is is' : List TopItem}, ItemsRel r D is is' → eraseTypeDecs is' = eraseTypeDecs is
  | [], [], _ => rfl
  | .types db tbs :: is, .types db' tbs' :: is', h => by
    obtain ⟨⟨rfl, rfl⟩, h2⟩ := h
    simp only [eraseTypeDecs, ItemsRel.types h2]
  | .value _ _ :: is, .value _ _ :: is', h => by simp only [eraseTypeDecs, ItemsRel.types h.2]
  | .port _ :: is, .port _ :: is', h => by simp only [eraseTypeDecs, ItemsRel.types h.2]
  | .value _ _ :: _, .types _ _ :: _, h | .value _ _ :: _, .port _ :: _, h
  | .types _ _ :: _, .value _ _ :: _, h | .types _ _ :: _, .port _ :: _, h
  | .port _ :: _, .value _ _ :: _, h | .port _ :: _, .types _ _ :: _, h
  | [], _ :: _, h | _ :: _, [], h => by simp [ItemsRel, ItemRel] at h

theorem modInfos_rename : ∀ (n : Nat) {a a' : AProgram} {rs rs' : List (SBasis × SBasis × Env)},
    ProgRel a rs a' rs' → ModInfosRel (modInfos n a rs) (modInfos n a' rs')
  | n, m :: ms, m' :: ms', res :: rs, res' :: rs', h => by
    obtain ⟨⟨hh, hi, hπ, hp, ht, r, D, hr, hit⟩, h2⟩ := h
    obtain ⟨Bi, B'i, Ei⟩ := res
    obtain ⟨Bi', B'i', Ei'⟩ := res'
    have hg := topGroups_rename hr n hit
    rw [topGroupsFrom_values, topGroupsFrom_values] at hg
    simp only [modInfos]
    rw [hg.length]
    exact ⟨⟨r, D, hr, ⟨hh, hi, hg, hπ, ht, hp⟩⟩, modInfos_rename _ h2⟩
  | _, [], [], [], [], _ => trivial
  | _, [], [], [], _ :: _, h | _, [], [], _ :: _, [], h | _, [], [], _ :: _, _ :: _, h
  | _, [], _ :: _, _, _, h | _, _ :: _, [], _, _, h
  | _, _ :: _, _ :: _, [], _, h | _, _ :: _, _ :: _, _ :: _, [], h => by simp [ProgRel] at h

theorem ModInfosRel.groupsLengths : ∀ {mis mis' : List ModInfo}, ModInfosRel mis mis' →
    (mis'.map (·.groups.length)).sum = (mis.map (·.groups.length)).sum
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    obtain ⟨⟨r, D, _, hmi⟩, h2⟩ := h
    simp only [List.map_cons, List.sum_cons, hmi.groups.length, ModInfosRel.groupsLengths h2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- The invariance lemma at the level of `reduceWith`. -/
theorem reduceWith_rename (B : SBasis) {a a' : AProgram} {rs rs' : List (SBasis × SBasis × Env)}
    (h : ProgRel a rs a' rs') (hmain : (mainScheme rs').bind mainKind = (mainScheme rs).bind mainKind) :
    reduceWith B a' rs' = reduceWith B a rs := by
  have hm := modInfos_rename 0 h
  unfold reduceWith specProgram
  simp only [hm.groupsLengths, specMods_rename B _ hm (show GlobRel [] [] from trivial), hmain, buildModules_rename B hm]

end StandardElm.Stat
