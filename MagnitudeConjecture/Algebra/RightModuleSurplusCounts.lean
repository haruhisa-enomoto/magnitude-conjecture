import MagnitudeConjecture.Algebra.RightModulePrimitiveDirectedDeletion
import MagnitudeConjecture.Algebra.RightModuleSimpleCount
import MagnitudeConjecture.Combinatorics.SurplusCounts

/-! # Official module-category surplus and numerical count estimates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A B : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring B] [Algebra k B] [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

/-- The official ambient surplus uses the literal indecomposable and simple
counts and the official arrow multiplicities. -/
theorem ambientARSurplus_eq_counts (S : RightModule.FiniteIndecomposableSkeleton k A) :
    S.ambientARSurplus = 2 * (S.n : ℤ) -
      ARCount.arrowCount (FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData) - 2 * S.simpleCount := by
  classical
  rw [ambientARSurplus, ARCount.surplus_eq_counts, ← S.simpleCount_eq_projectiveCount]
  simp only [ARCount.vertexCount, Fintype.card_fin]

/-- Exact indecomposable and simple counts and an arrow bound control the
official surplus of a second finite module skeleton. -/
theorem ambientARSurplus_error_of_counts
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (T : RightModule.FiniteIndecomposableSkeleton k B) (m : ℕ) (W C : ℤ)
    (hN : (T.n : ℤ) = (S.n : ℤ) * ((m : ℤ) + 1) - W)
    (ha : |ARCount.arrowCount (FiniteTauMatrix.arrowMultiplicity
        T.finiteTauCategoryData.toFiniteRightTauCategoryData) -
      ((m : ℤ) + 1) * ARCount.arrowCount (FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData)| ≤ C)
    (hp : T.simpleCount = S.simpleCount * (m + 1)) :
    |T.ambientARSurplus - ((m : ℤ) + 1) * S.ambientARSurplus| ≤ 2 * |W| + C := by
  rw [T.ambientARSurplus_eq_counts, S.ambientARSurplus_eq_counts]
  exact GradedInterval.surplus_error_of_exact_counts S.n T.n S.simpleCount T.simpleCount
    m _ _ W C hN ha hp

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
