import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncomingAdditiveLift
import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncomingPreimage
import MagnitudeConjecture.Algebra.RightModuleStandardFormARSingletonMap

/-!
# Factorization through the recovered incoming map
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARIncomingFactorsQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARIncomingFactorsArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- Every nonsplit morphism between recovered skeleton objects factors through
the complete recovered incoming map. -/
theorem standardFormRecoveredIncomingMap_factors_obj
    (x z : Fin S.n)
    (q : (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
          (k := k)).obj x ⟶
        (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
          (k := k)).obj z)
    (hq : ¬ IsSplitEpi q) :
    ∃ factor :
        (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
          (k := k)).obj x ⟶
          (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
            (S.standardFormRightMeshData.additiveIncomingObj (k := k) z),
      factor ≫ S.standardFormRecoveredIncomingMap (k := k) z = q := by
  let T := S.standardFormRightMeshData
  let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  let Y := S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite
  let F := S.standardFormAdditiveRestrictedYonedaFunctor (k := k)
  obtain ⟨coeff, hrFactor⟩ :=
    S.exists_standardFormIncomingCoefficient_preimage_eq_incomingSum
      (k := k) x z q hq
  let factor : sigma.obj x ⟶
      F.obj
        (T.additiveIncomingObj (k := k) z) :=
    (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) x).inv ≫
      F.map
        (S.standardFormIncomingCoefficientAdditiveLift (k := k) x z coeff)
  refine ⟨factor, ?_⟩
  rw [S.standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso
    (k := k) z]
  dsimp only [factor, F]
  simp only [Category.assoc]
  rw [← (S.standardFormAdditiveRestrictedYonedaFunctor
    (k := k)).map_comp_assoc]
  rw [S.standardFormIncomingCoefficientAdditiveLift_comp_incomingMap
    (k := k) x z coeff]
  rw [S.standardFormAdditiveRestrictedYoneda_singleton_map (k := k) x z]
  rw [← hrFactor]
  exact Y.map_preimage q

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
