import MagnitudeConjecture.Algebra.RightModuleStandardGradedRecovery

/-! # Identifying the graded generator algebra with the standard form -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The representable-model standard algebra and the actual mesh projective-sum
endomorphism algebra are algebra-equivalent. -/
def standardFormGeneratorEndAlgEquiv (hfinite : S.StandardFormMeshHomFinite) :
    S.standardFormAlgebra hfinite ≃ₐ[k] End (⨁ S.standardGradedProjectiveFamily) :=
  S.standardGradedRecoveryEndEquiv.symm

/-- The comparison in the variance used for right modules. -/
def standardFormOppositeGeneratorAlgEquiv (hfinite : S.StandardFormMeshHomFinite) :
    (S.standardFormAlgebra hfinite)ᵐᵒᵖ ≃ₐ[k] S.StandardGradedGeneratorAlgebra :=
  AlgEquiv.op (S.standardFormGeneratorEndAlgEquiv hfinite)

/-- The graded algebra structure transported to the existing standard-form algebra. -/
def standardFormOppositeAlgebraGrading (hfinite : S.StandardFormMeshHomFinite) :
    Graded.VectorGrading k (S.standardFormAlgebra hfinite)ᵐᵒᵖ :=
  (S.standardGradedGeneratorAlgebraGrading hfinite).comap
    (S.standardFormOppositeGeneratorAlgEquiv hfinite).toLinearEquiv

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
