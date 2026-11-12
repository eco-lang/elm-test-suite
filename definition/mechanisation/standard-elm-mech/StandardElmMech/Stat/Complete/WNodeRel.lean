/-
  A Standard Definition of Elm? Mechanisation: the nodes of W's result and of its image under the
  instance substitution correspond one to one (plan step 11, milestone (b), section 9).
-/
import StandardElmMech.Stat.Complete.WNodes

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

theorem sbPat_ty_strip (T : FSub) (p : APat) : (stripPat (sbPat T p)).ty = sb T (stripPat p).ty := by
  rw [stripPat_ty, stripPat_ty, sbPat_ty]
theorem sbAtPat_ty_strip (T : FSub) (p : AAtPat) : (stripAtPat (sbAtPat T p)).ty = sb T (stripAtPat p).ty := by
  rw [stripAtPat_ty, stripAtPat_ty, sbAtPat_ty]
theorem sbPat_ve_strip (T : FSub) (p : APat) : (stripPat (sbPat T p)).ve = sbVE T (stripPat p).ve := by
  rw [stripPat_ve, stripPat_ve, sbPat_ve]
theorem sbAtPat_ve_strip (T : FSub) (p : AAtPat) : (stripAtPat (sbAtPat T p)).ve = sbVE T (stripAtPat p).ve := by
  rw [stripAtPat_ve, stripAtPat_ve, sbAtPat_ve]

theorem veBodies_map (T : FSub) (VE : ValEnv) : (sbVE T VE).map (·.2.1.body) = (VE.map (·.2.1.body)).map (sb T) := by
  simp [sbVE, sbScheme]

theorem sbPatRowOpt_rowOpt (T : FSub) : ∀ r : Option APatRow, APatRow.rowOpt (sbPatRowOpt T r) = sbRow T (APatRow.rowOpt r)
  | none => rfl
  | some (.field l τ rest) => by
    simp only [sbPatRowOpt, sbPatRow, APatRow.rowOpt, APatRow.row, sbPatRowOpt_rowOpt T rest, sbRow_modify]; rfl

mutual
theorem nodesAtPat_rel (T : FSub) (U0 : List BVar) : ∀ (p : AAtPat) (path : List Nat),
    F2 (NRel T U0) (nodesAtPat U0 path (stripAtPat p)) (nodesAtPat U0 path (stripAtPat (sbAtPat T p)))
  | .wild τ, path => .cons (nrel_mk rfl rfl (by simp [stripAtPat, sbAtPat, AAtPat.ty, AAtPat.ve, mono, sbScheme, tUnitTy, sb, sbList]) rfl) .nil
  | .scon sc τ, path => .cons (nrel_mk rfl rfl (by simp [stripAtPat, sbAtPat, AAtPat.ty, AAtPat.ve, mono, sbScheme, tUnitTy, sb, sbList]) rfl) .nil
  | .var x τ, path => .cons (nrel_mk rfl rfl (by simp [stripAtPat, sbAtPat, AAtPat.ty, AAtPat.ve, mono, sbScheme, tUnitTy, sb, sbList]) rfl) .nil
  | .con lc inst τ, path => .cons (nrel_mk rfl rfl (by simp [stripAtPat, sbAtPat, AAtPat.ty, AAtPat.ve, mono, sbScheme, tUnitTy, sb, sbList]) rfl) .nil
  | .nil τ, path => .cons (nrel_mk rfl rfl (by simp [stripAtPat, sbAtPat, AAtPat.ty, AAtPat.ve, mono, sbScheme, tUnitTy, sb, sbList]) rfl) .nil
  | .unit, path => .cons (nrel_mk rfl rfl (by simp [stripAtPat, sbAtPat, AAtPat.ty, AAtPat.ve, mono, sbScheme, tUnitTy, sb, sbList]) rfl) .nil
  | .tuple p1 p2 p3, path =>
    forall2_append (forall2_append (forall2_append
      (.cons (nrel_mk rfl rfl (by
          simp only [AAtPat.ty, List.map_cons, List.map_nil, tupleTy_sb, sbPat_ty_strip]
          cases p3 <;> simp [stripPatOpt, sbPatOpt, APat.tyOpt, sbOpt, sbPat_ty_strip])
        (by rw [← veSchemes_sb]; congr 1; exact sbAtPat_ve_strip T (.tuple p1 p2 p3))) .nil)
      (nodesPat_rel T U0 p1 _)) (nodesPat_rel T U0 p2 _)) (nodesPatOpt_rel T U0 p3 _)
  | .record r τ, path =>
    forall2_append (.cons (nrel_mk rfl rfl rfl (by rw [← veSchemes_sb]; congr 1; exact sbAtPat_ve_strip T (.record r τ))) .nil)
      (nodesPatRowOpt_rel T U0 r _)
  | .paren p, path =>
    forall2_append (.cons (nrel_mk rfl rfl (by simp [sbPat_ty_strip])
        (by rw [← veSchemes_sb]; congr 1; exact sbPat_ve_strip T p)) .nil)
      (nodesPat_rel T U0 p _)
theorem nodesPatRowOpt_rel (T : FSub) (U0 : List BVar) : ∀ (r : Option APatRow) (path : List Nat),
    F2 (NRel T U0) (nodesPatRowOpt U0 path r) (nodesPatRowOpt U0 path (sbPatRowOpt T r))
  | none, _ => .nil
  | some (.field l τ rest), path =>
    forall2_append (.cons (nrel_mk rfl rfl (by
        show [sb T τ] ++ (Row.modify [(l, sb T τ)] (APatRow.rowOpt (sbPatRowOpt T rest))).map (·.2) = _
        rw [sbPatRowOpt_rowOpt, show ([(l, sb T τ)] : Row) = sbRow T [(l, τ)] from rfl, ← sbRow_modify, sbRow_eq]
        simp [APatRow.row]) rfl) .nil)
      (nodesPatRowOpt_rel T U0 rest _)
theorem nodesPat_rel (T : FSub) (U0 : List BVar) : ∀ (p : APat) (path : List Nat),
    F2 (NRel T U0) (nodesPat U0 path (stripPat p)) (nodesPat U0 path (stripPat (sbPat T p)))
  | .atpat a, path =>
    forall2_append (.cons (nrel_mk rfl rfl (by simp [sbAtPat_ty_strip])
        (by rw [← veSchemes_sb]; congr 1; exact sbAtPat_ve_strip T a)) .nil)
      (nodesAtPat_rel T U0 a _)
  | .con lc inst args τ, path =>
    forall2_append (.cons (nrel_mk rfl rfl (by simp [sbList])
        (by rw [← veSchemes_sb]; congr 1; exact sbPat_ve_strip T (.con lc inst args τ))) .nil)
      (nodesAtPats_rel T U0 args path 0)
  | .cons p1 p2, path =>
    forall2_append (forall2_append (.cons (nrel_mk rfl rfl (by simp [sbPat_ty_strip, listTy_sb])
        (by rw [← veSchemes_sb]; congr 1; exact sbPat_ve_strip T (.cons p1 p2))) .nil)
      (nodesPat_rel T U0 p1 _)) (nodesPat_rel T U0 p2 _)
  | .as p x, path =>
    forall2_append (.cons (nrel_mk rfl rfl (by simp [sbPat_ty_strip])
        (by rw [← veSchemes_sb]; congr 1; exact sbPat_ve_strip T (.as p x))) .nil)
      (nodesPat_rel T U0 p _)
theorem nodesPatOpt_rel (T : FSub) (U0 : List BVar) : ∀ (p : Option APat) (path : List Nat),
    F2 (NRel T U0) (nodesPatOpt U0 path (stripPatOpt p)) (nodesPatOpt U0 path (stripPatOpt (sbPatOpt T p)))
  | none, _ => .nil
  | some p, path => nodesPat_rel T U0 p path
theorem nodesAtPats_rel (T : FSub) (U0 : List BVar) : ∀ (l : List AAtPat) (path : List Nat) (i : Nat),
    F2 (NRel T U0) (nodesAtPats U0 path i (stripAtPats l)) (nodesAtPats U0 path i (stripAtPats (sbAtPats T l)))
  | [], _, _ => .nil
  | a :: as, path, i => forall2_append (nodesAtPat_rel T U0 a _) (nodesAtPats_rel T U0 as path (i + 1))
end

end StandardElm.Stat.Complete
