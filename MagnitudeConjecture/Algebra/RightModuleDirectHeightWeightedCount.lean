import MagnitudeConjecture.Algebra.RightModuleDirectHeightSink
import MagnitudeConjecture.Combinatorics.HeightArrowCount
import MagnitudeConjecture.Combinatorics.HeightTranslationSum

/-! # The actual factor's weighted-height arrow sum -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- The direct height gives the weighted incoming-minus-outgoing identity
for the actual official arrow multiplicities. -/
theorem PrimitiveDirectedBoundaryData.directHeight_weighted_arrow_count
    (B : S.PrimitiveDirectedBoundaryData D) :
    let a := fun X Y : S.SurvivingLabel K ↦
      (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ)
    let h := fun X ↦ (B.directFactorHeight X : ℤ)
    (∑ X, ∑ Y, a X Y) =
      (∑ Y, h Y * ∑ X, a X Y) - (∑ X, h X * ∑ Y, a X Y) := by
  intro a h
  apply HeightArrowCount.weighted_difference a h
  intro X Y hxy
  have hne : directFactorArrow X Y := by
    intro hz
    apply hxy
    simp [a, hz]
  dsimp only [h]
  exact_mod_cast B.directFactorHeight_arrow X Y hne

/-- The actual translation identifies the boundary height difference with
twice the number of nonprojective vertices. -/
noncomputable def PrimitiveDirectedBoundaryData.directHeight_boundary_difference
    (B : S.PrimitiveDirectedBoundaryData D) :=
  @HeightArrowCount.boundary_height_difference (S.SurvivingLabel K) inferInstance
    (S.factorFiniteTauCategoryData K).IsProjective
    (S.factorFiniteTauCategoryData K).IsInjective
    (Classical.decPred _) (Classical.decPred _)
    (S.factorFiniteTauCategoryData K).tauPlusEquiv
    (fun X ↦ (B.directFactorHeight X : ℤ))
    (fun X ↦ by exact_mod_cast B.directFactorHeight_tauPlus X)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
