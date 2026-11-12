/-
  A Standard Definition of Elm? Mechanisation: the specialisation of a program is unique (plan
  step 10, "The pipeline": `reduce_principal_unique`, `specOf_functional`, `ident_of_spec`), given
  the module step (`ModuleStep`, ProgInduction.lean) for the modules of the program.
-/
import StandardElmMech.Stat.ProgInduction
import StandardElmMech.Stat.TestBasis

namespace StandardElm.Stat
open StandardElm.Src (BProgram SProgram BTy BTyRow BTopDec BModule BDatBind BTypBind)

/-! ## The restriction on type declarations the module step needs -/

mutual
/-- The type constructors a type expression names without a qualifier. -/
def bTyCons : BTy → List String
  | .tyvar _ | .unit => []
  | .record row => bTyRowOptCons row
  | .openRecord _ row => bTyRowCons row
  | .tuple t1 t2 t3 => bTyCons t1 ++ bTyCons t2 ++ bTyOptCons t3
  | .con c args => (match c.qual with | none => [c.id] | some _ => []) ++ bTyListCons args
  | .fn t1 t2 => bTyCons t1 ++ bTyCons t2
  | .paren t => bTyCons t
def bTyRowCons : BTyRow → List String
  | .field _ t rest => bTyCons t ++ bTyRowOptCons rest
def bTyRowOptCons : Option BTyRow → List String
  | none => []
  | some r => bTyRowCons r
def bTyOptCons : Option BTy → List String
  | none => []
  | some t => bTyCons t
def bTyListCons : List BTy → List String
  | [] => []
  | t :: ts => bTyCons t ++ bTyListCons ts
end

/-- A type-declaration phrase whose type names are distinct and whose aliases each mention only
    earlier aliases (res:modules-types-distinct, res:modules-alias-not-recursive, in Appendix A's
    order of aliases). -/
def typesOrdered (db : Option BDatBind) (tbs : List BTypBind) : Bool :=
  decide (((db.getD []).map (·.1) ++ tbs.map (·.c)).Nodup) &&
    (tbs.zipIdx.all fun (tb, i) => (tbs.drop i).all fun tb' => !decide (tb'.c ∈ bTyCons tb.t))

def topTypesOrdered : BTopDec → Bool
  | .types db tbs => typesOrdered db tbs
  | .seq a b => topTypesOrdered a && topTypesOrdered b
  | _ => true

/-- The restriction on a module's type declarations. -/
def TypesOrdered (m : BModule) : Prop := ((m.body.map topTypesOrdered).getD true) = true

instance (m : BModule) : Decidable (TypesOrdered m) := inferInstanceAs (Decidable (_ = true))

/-! ## The test basis -/

set_option maxRecDepth 100000 in
theorem Btest_inv : BasisInv Btest := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem NRInv.nil : NRInv [] [] :=
  ⟨⟨fun _ _ e => e, fun _ => rfl, fun _ _ => rfl⟩, ⟨fun _ _ e => e, fun _ => rfl, fun _ _ => rfl⟩,
   fun _ => rfl, fun _ => rfl⟩

theorem nr_nil_basis (B : SBasis) : (nr []).basis B = B := by
  have := nr_inv_basis (a := []) (b := []) (fun _ => rfl) B
  have e : ∀ X : SBasis, (nr []).basis X = (nr []).basis ((nr []).basis X) := fun X => by
    rw [nr_comp2_basis (c := []) (fun _ => rfl)]
  rwa [← e] at this

theorem progResults_some {B : SBasis} {a : AProgram} (h : checkProgram B a = true) : ∃ rs, progResults B a = some rs := by
  rw [← progResults_isSome] at h
  cases e : progResults B a with
  | none => rw [e] at h; cases h
  | some rs => exact ⟨rs, rfl⟩

section
variable {hyp : Src.BModule → Prop}

/-- Two principal program derivations give the same reduced program. -/
theorem reduce_principal_unique (hstep : ModuleStep hyp) {B : SBasis} {p : BProgram} {a a' : AProgram}
    (hB : BasisInv B) (hyps : ∀ m ∈ p.modules, hyp m)
    (ha : PrincipalProgDeriv B p a) (ha' : PrincipalProgDeriv B p a') :
    reduceProgram B a = reduceProgram B a' := by
  obtain ⟨⟨hc, he⟩, Bs, hb, hp⟩ := ha
  obtain ⟨⟨hc', he'⟩, Bs', hb', hp'⟩ := ha'
  obtain ⟨rs, hrs⟩ := progResults_some hc
  obtain ⟨rs', hrs'⟩ := progResults_some hc'
  have hpa := allPrincipal_of hb hp
  have hpa' : AllPrincipal ((nr []).basis B) a' := by rw [nr_nil_basis]; exact allPrincipal_of hb' hp'
  have hrs'' : progResults ((nr []).basis B) a' = some rs' := by rw [nr_nil_basis]; exact hrs'
  obtain ⟨hrel, hmain⟩ := prog_rel hstep a a' B [] [] rs rs' NRInv.nil hB
    (fun m hm => hyps _ (he ▸ List.mem_map_of_mem hm)) (he'.trans he.symm) hpa hpa' hrs hrs''
  simp only [reduceProgram, hrs, hrs']
  exact (reduceWith_rename B hrel hmain).symm

/-- The specialisation of a program is unique. -/
theorem specOf_functional (hstep : ModuleStep hyp) {B : SBasis} {p : BProgram} {r r' : Mod.Reduced}
    (hB : BasisInv B) (hyps : ∀ m ∈ p.modules, hyp m) (h : SpecOf B p r) (h' : SpecOf B p r') : r = r' := by
  obtain ⟨a, ha, hr⟩ := h
  obtain ⟨a', ha', hr'⟩ := h'
  rw [reduce_principal_unique hstep hB hyps ha ha', hr'] at hr
  cases hr; rfl

/-- What the pipeline gives is the specialisation of the program. -/
theorem ident_of_spec_of (hstep : ModuleStep hyp) {B : SBasis} {s : SProgram} {q : Mod.Reduced}
    (hB : BasisInv B) (hyps : ∀ m ∈ (bareOf s).modules, hyp m)
    (hI : InferPrincipalFor B (bareOf s)) (h : endToEnd B s = .ok q) :
    ∀ r, SpecOf B (bareOf s) r → r = q :=
  fun r hr => specOf_functional hstep hB hyps hr (specOf_of_endToEnd hI h)

end

/-- What the pipeline gives is the specialisation of the program (plan step 10), given the module
    step for modules whose type declarations are ordered. -/
theorem ident_of_spec (hstep : ModuleStep TypesOrdered) {s : SProgram} {q : Mod.Reduced}
    (hT : ∀ m ∈ (bareOf s).modules, TypesOrdered m)
    (hI : InferPrincipalFor Btest (bareOf s)) (h : endToEnd Btest s = .ok q) :
    ∀ r, SpecOf Btest (bareOf s) r → r = q :=
  ident_of_spec_of hstep Btest_inv hT hI h

end StandardElm.Stat
