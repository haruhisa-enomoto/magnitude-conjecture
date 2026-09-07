import MagnitudeConjecture.Algebra.RightModuleStandardFormCoveringAverageBase
import MagnitudeConjecture.CategoryTheory.StandardCoveringCategoryAlgebraEquivInequality

/-!
# The inequality in the standard-form covering average
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormCoveringAverageInequalityQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormCoveringAverageInequalityArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormCoveringAverageInequalityFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormCoveringAverageInequalityNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

set_option maxHeartbeats 4000000 in
/-- Frozen manuscript, Corollary `cor:standard-deletion`, for a covering
idempotent of a connected standard-form component. -/
theorem standardFormCoveringPrimitiveQuotient_ambientARSurplus_le
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let P := standardFormCoveringPrimitive S x₀ hconnected x
    letI : IsNoetherianRing
        (RightModule.primitiveQuotientAlgebra
          (standardFormCoveringIdempotent S x₀ hconnected x))ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    ((S.standardFormAlgebraIndecomposableSkeleton
        (k := k)).primitiveQuotientFiniteIndecomposableSkeleton P
          ).ambientARSurplus ≤
      (S.standardFormAlgebraIndecomposableSkeleton
        (k := k)).ambientARSurplus := by
  letI : IsMulTorsionFree (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  letI : Group.ResiduallyFinite (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_residuallyFinite x₀ hconnected
  let H := standardFormOppositeProjectiveSourceCategoryIsAdmissible
    S x₀ hconnected
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient
      (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  let f := Classical.choice
    (standardFormOppositeProjectiveLiftedOrbitCategoryAlgebraEquivNonempty
      S x₀ hconnected S.standardFormMeshHomFinite)
  exact
    StandardCovering.primitiveQuotient_ambientARSurplus_le_of_admissible_of_algEquiv
      (k := k) D H (S.standardFormAlgebraIndecomposableSkeleton (k := k)) f x

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
