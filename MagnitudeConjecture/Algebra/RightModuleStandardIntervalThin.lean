import MagnitudeConjecture.Algebra.RightModuleStandardIntervalPacking
import MagnitudeConjecture.CategoryTheory.FiniteCategoryDirectedSurplus
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPointwiseThinBiserial

/-! # Thin indecomposables and biserial projectives in zero-surplus intervals -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance intervalThinBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
local instance intervalThinFintype (m : ℕ) :
    Fintype (S.standardFormIntervalPrincipalCategory m) :=
  inferInstanceAs (Fintype (S.StandardFormProjectiveMeshCategory × Fin (m + 1)))
local instance intervalThinOpFintype (m : ℕ) :
    Fintype (S.standardFormIntervalPrincipalCategory m)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite
local instance intervalThinAlgebraFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) := S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalThinAlgebraNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- Every indecomposable interval category module is pointwise thin at zero ambient surplus. -/
theorem standardFormIntervalCategory_pointwiseThin_of_ambient_eq_zero
    (hz : S.ambientARSurplus = 0) (m : ℕ)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (S.standardFormIntervalPrincipalCategory m)ᵒᵖ) k) (hM : Indecomposable M) :
    CoveringHom.IsPointwiseThin M.obj.obj := by
  intro X
  apply CoveringHom.finrank_obj_le_one_of_finiteCategorySurplus_eq_zero
    (S.standardFormIntervalCategory_finiteRepresentables m)
    (S.standardFormIntervalCategory_repFinite m) (S.standardFormIntervalCategory_directed m)
    (Graded.FiniteGradedModule.principalIntervalOp_end_isLocalRing
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
      S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
      S.standardFormHomogeneousCorner_diagonal m)
    (Graded.FiniteGradedModule.principalIntervalOp_skeletal
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
      S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
      S.standardFormHomogeneousCorner_diagonal S.standardFormOppositeAlgebra_negative
      S.standardFormHomogeneousCorner_off_diagonal m) _ M hM X
  rw [S.standardFormIntervalCategory_surplus_eq]
  exact S.standardFormInterval_surplus_eq_zero_of_ambient_eq_zero hz m

/-- Every representable interval module is biserial at zero ambient surplus. -/
theorem standardFormIntervalCategory_representable_biserial_of_ambient_eq_zero
    (hz : S.ambientARSurplus = 0) (m : ℕ) (X : (S.standardFormIntervalPrincipalCategory m)ᵒᵖ) :
    MagnitudeConjecture.IsBiserialObject
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k)
        (S.standardFormIntervalCategory_finiteRepresentables m)).obj (Opposite.op X)) := by
  exact CoveringHom.finiteCovariantRepresentable_isBiserialObject_of_pointwiseThin
    (S.standardFormIntervalCategory_finiteRepresentables m)
    (Graded.FiniteGradedModule.principalIntervalOp_end_isLocalRing
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
      S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
      S.standardFormHomogeneousCorner_diagonal m)
    (S.standardFormIntervalCategory_pointwiseThin_of_ambient_eq_zero hz m) X

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
