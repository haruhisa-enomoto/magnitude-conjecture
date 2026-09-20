import MagnitudeConjecture.Algebra.RightModuleStandardHomogeneousIdempotents
import MagnitudeConjecture.Algebra.RightModuleStandardSupportedCategory
import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalAlgebra

/-! # The finite interval algebra of the graded standard form -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardIntervalAlgebraBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

/-- The finite interval algebra for the actual graded standard form. -/
abbrev standardFormIntervalAlgebra (m : ℕ) :=
  Graded.FiniteGradedModule.principalIntervalAlgebra
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent m

/-- The standard-form interval algebra is finite dimensional. -/
theorem standardFormIntervalAlgebra_finiteDimensional (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  Graded.FiniteGradedModule.principalIntervalAlgebra_finiteDimensional
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent m

/-- Modules over the standard-form interval algebra realize exactly the actual supported graded modules. -/
def standardFormIntervalAlgebraEquivalence (m : ℕ) :
    FGModuleCat.{u} (S.standardFormIntervalAlgebra m)ᵐᵒᵖ ≌ S.standardFormSupportedCategory m :=
  Graded.FiniteGradedModule.principalIntervalAlgebraGradedModuleEquivalence
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
    S.standardFormOppositeAlgebra_negative S.standardFormOppositeAlgebra_one_mem
    S.sum_standardFormHomogeneousIdempotent S.standardFormHomogeneousIdempotent_orthogonal m

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
