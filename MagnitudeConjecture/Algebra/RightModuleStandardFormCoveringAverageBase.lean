import MagnitudeConjecture.Algebra.RightModuleAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModuleStandardFormLiftedOrbitAlgebra
import MagnitudeConjecture.Algebra.RightModuleStandardFormPeriodicComponent
import MagnitudeConjecture.Algebra.RightModuleStandardFormSurplus
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalDirected
import MagnitudeConjecture.CategoryTheory.StandardCoveringCategoryAlgebra

/-!
# The covering-average base for the literal standard-form algebra

The universe-lifted strict orbit algebra is already identified with the
manuscript's standard-form algebra.  This file transports the covering-average
primitive deletion and its equality clause across that algebra equivalence,
including the literal primitive quotient.
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

local instance standardFormCoveringAverageQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormCoveringAverageArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormCoveringAverageFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormCoveringAverageNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

/-- The primitive idempotent in the literal standard-form algebra obtained
from an object in its universal projective cover. -/
noncomputable def standardFormCoveringIdempotent
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    S.standardFormAlgebra S.standardFormMeshHomFinite := by
  let H := standardFormOppositeProjectiveSourceCategoryIsAdmissible
    S x₀ hconnected
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
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
  exact f (StandardCovering.orbitCategoryProjector (k := k) D hP x)

/-- The covering idempotent is primitive. -/
theorem standardFormCoveringPrimitive
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    RightModule.PrimitiveIdempotentData
      (standardFormCoveringIdempotent S x₀ hconnected x) := by
  letI : IsMulTorsionFree (ProjectiveGroup S x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  let H := standardFormOppositeProjectiveSourceCategoryIsAdmissible
    S x₀ hconnected
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient
      (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let P := StandardCovering.orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  let f := Classical.choice
    (standardFormOppositeProjectiveLiftedOrbitCategoryAlgebraEquivNonempty
      S x₀ hconnected S.standardFormMeshHomFinite)
  change RightModule.PrimitiveIdempotentData
    (f (StandardCovering.orbitCategoryProjector (k := k) D hP x))
  exact P.mapAlgEquiv f

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
