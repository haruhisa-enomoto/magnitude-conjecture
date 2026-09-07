import MagnitudeConjecture.Algebra.RightModuleStandardFormCoveringAverageCore

/-!
# Equality in the standard-form covering average

The equality clause is separated from the primitive-deletion inequality so
that the two large proofs elaborate in distinct Lean processes.
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

local instance standardFormCoveringAverageEqualityQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormCoveringAverageEqualityArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormCoveringAverageEqualityFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance standardFormCoveringAverageEqualityNoetherian :
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
/-- Equality in the literal standard-form primitive deletion forces the
manuscript's one-dimensional fibre conclusion on the universal cover. -/
theorem standardFormCovering_finrank_obj_eq_one_of_ambientARSurplus_eq
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (x : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (hEquality :
      let P := standardFormCoveringPrimitive S x₀ hconnected x
      letI : IsNoetherianRing
          (RightModule.primitiveQuotientAlgebra
            (standardFormCoveringIdempotent S x₀ hconnected x))ᵐᵒᵖ :=
        IsNoetherianRing.of_finite k _
      (S.standardFormAlgebraIndecomposableSkeleton
          (k := k)).ambientARSurplus =
        ((S.standardFormAlgebraIndecomposableSkeleton
          (k := k)).primitiveQuotientFiniteIndecomposableSkeleton P
            ).ambientARSurplus)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
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
    StandardCovering.finrank_obj_eq_one_of_ambientARSurplus_eq_of_admissible_of_algEquiv
      (k := k) D H (S.standardFormAlgebraIndecomposableSkeleton (k := k))
        f x hEquality M hM hMx

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
