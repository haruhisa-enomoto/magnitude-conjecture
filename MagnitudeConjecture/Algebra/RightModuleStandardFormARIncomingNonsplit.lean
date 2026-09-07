import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncoming

/-!
# Nonsplitting of the recovered incoming map
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARIncomingNonsplitQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARIncomingNonsplitArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- The complete recovered incoming map is not a split epimorphism. -/
theorem standardFormRecoveredIncomingMap_not_splitEpi
    (z : Fin S.n) :
    ¬ IsSplitEpi (S.standardFormRecoveredIncomingMap (k := k) z) := by
  let T := S.standardFormRightMeshData
  let e := S.standardFormAdditiveRestrictedYonedaSingletonIso
    (k := k) z
  let F := S.standardFormAdditiveRestrictedYonedaFunctor (k := k)
  let g := T.additiveIncomingMap (k := k) z
  intro hsplit
  letI : IsSplitEpi (S.standardFormRecoveredIncomingMap (k := k) z) :=
    hsplit
  haveI : IsSplitEpi
      (S.standardFormRecoveredIncomingMap (k := k) z ≫ e.inv) := by
    infer_instance
  have heq : S.standardFormRecoveredIncomingMap (k := k) z ≫ e.inv =
      F.map g := by
    rw [S.standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso
      (k := k) z]
    change (F.map g ≫ e.hom) ≫ e.inv = F.map g
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  have hmapSplit : IsSplitEpi (F.map g) := heq ▸ inferInstance
  exact T.additiveIncomingMap_not_splitEpi (k := k) z
    ((F.isSplitEpi_iff g).mp hmapSplit)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
