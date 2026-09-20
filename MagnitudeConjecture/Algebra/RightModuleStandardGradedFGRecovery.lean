import MagnitudeConjecture.Algebra.RightModuleStandardGradedFunctor
import MagnitudeConjecture.CategoryTheory.GradedUnderlyingFG
import MagnitudeConjecture.CategoryTheory.LinearMatrixFunctor
import Mathlib.CategoryTheory.Whiskering

/-! # Finitely generated recovery of the actual graded standard form -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)

/-- The graded realization recovers the established standard-form functor
already in the finitely generated module category. -/
def standardFormGradedUnderlyingFGNatIso :
    S.standardFormGradedFunctor ⋙ Graded.FiniteGradedModule.underlyingFG ≅
      S.standardGradedRecovery ⋙ S.standardFormProjectiveVertexModuleAlgebraEquivalence.functor :=
  ((Functor.whiskeringRight _ _ _).obj
    (forget₂ (RightModule.FinitelyGeneratedCategory
      (S.standardFormAlgebra S.standardFormMeshHomFinite))
      (RightModule.Category (S.standardFormAlgebra S.standardFormMeshHomFinite)))).preimageIso
        S.standardFormGradedUnderlyingNatIso

/-- Entrywise passage from the induced vertex model to the raw mesh gives
the same recovered finite module, including its chosen biproduct coordinates. -/
def standardGradedRawRecoveryIso :
    (S.standardFormMeshRawFunctor (k := k)).mapMat_ ⋙ S.standardGradedRecovery ≅
      S.standardFormAdditiveRestrictedYonedaFunctor (k := k) := Iso.refl _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
