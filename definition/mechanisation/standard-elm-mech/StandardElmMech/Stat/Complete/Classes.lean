/-
  A Standard Definition of Elm? Mechanisation: classes for unification, plan step 11, milestone (a)
  ("The mathematics", section 3). The meet of classes is step 9's `Cls.meet`; the class
  propagation table D(κ, t) is `Cls.prop`. For refutation only the forward halves of K4 and K5 are
  needed: an admissible type has the shape the tables say.
-/
import StandardElmMech.Stat.Complete.Term

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-- D(κ, t): the classes the arguments of a constructed type `(τi) t` must have for it to be in
    Adm κ (κ ≠ any); `none` when no such type is. -/
def Cls.prop (k : Cls) (t : TyName) : Option (List Cls) :=
  match k with
  | .any => none
  | .num => if t = tInt ∨ t = tFloat then some [] else none
  | .comp =>
    if t = tInt ∨ t = tFloat ∨ t = tChar ∨ t = tString then some []
    else if t = tList then some [.comp]
    else if t = tTuple2 then some [.comp, .comp]
    else if t = tTuple3 then some [.comp, .comp, .comp]
    else none
  | .app => if t = tString then some [] else if t = tList then some [.any] else none
  | .capp => if t = tString then some [] else if t = tList then some [.comp] else none

/-- The class constraints on the arguments, pairwise. -/
def zipAdm : List Ty → List Cls → Prop
  | [], [] => True
  | x :: xs, k :: ks => Adm k x ∧ zipAdm xs ks
  | _, _ => False

/-- K5, forward: a constructed type in Adm κ (κ ≠ any) has D(κ, t) defined, the arity, and
    admissible arguments. -/
theorem adm_con {k : Cls} {as : List Ty} {t : TyName} (hk : k ≠ .any) (h : Adm k (.con as t)) :
    ∃ ks, Cls.prop k t = some ks ∧ zipAdm as ks := by
  cases h with
  | any => exact absurd rfl hk
  | num_int => exact ⟨[], by decide, trivial⟩
  | num_float => exact ⟨[], by decide, trivial⟩
  | comp_int => exact ⟨[], by decide, trivial⟩
  | comp_float => exact ⟨[], by decide, trivial⟩
  | comp_char => exact ⟨[], by decide, trivial⟩
  | comp_string => exact ⟨[], by decide, trivial⟩
  | comp_list τ h => exact ⟨[.comp], by decide, h, trivial⟩
  | comp_tuple2 τ1 τ2 h1 h2 => exact ⟨[.comp, .comp], by decide, h1, h2, trivial⟩
  | comp_tuple3 τ1 τ2 τ3 h1 h2 h3 => exact ⟨[.comp, .comp, .comp], by decide, h1, h2, h3, trivial⟩
  | app_string => exact ⟨[], by decide, trivial⟩
  | app_list τ => exact ⟨[.any], by decide, .any τ, trivial⟩
  | capp_string => exact ⟨[], by decide, trivial⟩
  | capp_list τ h => exact ⟨[.comp], by decide, h, trivial⟩

theorem adm_fn {k : Cls} {a b : Ty} (h : Adm k (.fn a b)) : k = .any := by
  cases h; rfl

theorem adm_record {k : Cls} {ρ : Row} {tl : Option RowVar} (h : Adm k (.record ρ tl)) : k = .any := by
  cases h; rfl

theorem adm_var {k : Cls} {a : TyVar} (h : Adm k (.var a)) : a.cls.le k = true := by
  cases h with
  | any => cases a.cls <;> rfl
  | num_var _ h => rw [h]; rfl
  | comp_var _ h => exact h
  | app_var _ h => exact h
  | capp_var _ h => rw [h]; rfl

/-- K4, forward: a type in two classes has them meet. -/
theorem adm_meet {k k' : Cls} {τ : Ty} (h : Adm k τ) (h' : Adm k' τ) : (Cls.meet k k').isSome = true := by
  cases k <;> cases k' <;> simp only [Cls.meet, Option.isSome_some] <;>
    (exfalso; cases h <;> cases h' <;> (try simp_all [Cls.le]) <;> (try contradiction))

end StandardElm.Stat.Complete
