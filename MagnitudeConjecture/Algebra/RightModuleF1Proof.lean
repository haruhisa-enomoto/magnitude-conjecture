import MagnitudeConjecture.Algebra.RightModuleF1Inequality
import MagnitudeConjecture.Algebra.RightModuleF1EqualityCharacterization
import MagnitudeConjecture.Algebra.RightModuleBasicMorita
import MagnitudeConjecture.DeferredStructuralInputs
import MagnitudeConjecture.Algebra.RightModuleSimpleCount
import MagnitudeConjecture.CategoryTheory.F1FiniteDeletionSupport
import MagnitudeConjecture.CategoryTheory.IncomingHomLocalDensity
import MagnitudeConjecture.Combinatorics.DeletionOrderWeight
import MagnitudeConjecture.Combinatorics.F1FiniteDeletionAverage
import MagnitudeConjecture.Algebra.RightModuleStandardMeshConstruction
import MagnitudeConjecture.Algebra.RightModulePrimitiveGrading

/-!
# Frozen proof route for the magnitude conjecture

This is the public production layer for the September 10 frozen manuscript.
The declarations retain the historical API, while the route is organized by
the finite deletion-locality, deletion-order averaging, direct mesh, and
primitive grading interfaces used by F1.  The superseded characterization
source was removed after the dependency audit; its declarations now live in
the F1-named modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

/-- The finite positive averaging interface used by the frozen route. -/
theorem finitePositiveDeletionOrderAverage_certificate
    {α : Type u} [DecidableEq α] (Ω : Finset α)
    (localChange : Finset α → ℤ)
    (hnonnegative : ∀ S ∈ Ω.powerset, 0 ≤ localChange S) :
    0 ≤ ∑ S ∈ Ω.powerset,
      MagnitudeConjecture.DeletionOrderAverage.weight Ω S *
        (localChange S : ℚ) :=
  MagnitudeConjecture.DeletionOrderAverage.weightedIntegerAverage_nonnegative
    Ω localChange hnonnegative

/-- The F1 equality boundary for a displayed primitive projective
presentation. -/
theorem ambientARSurplus_eq_zero_iff_isSpecialBiserial
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (P : S.PrimitiveProjectivePresentation) :
    S.ambientARSurplus = 0 ↔ BoundQuiver.IsSpecialBiserial k A := by
  have hBeta :
      MagnitudeConjecture.RepresentationFiniteSpecialBiserialBetaCharacterization
        k := by
    intro B _ _ _ _ T
    exact MagnitudeConjecture.representationFinite_isSpecialBiserial_iff_beta_le_two
      T
  exact P.ambientARSurplus_eq_zero_iff_isSpecialBiserial hBeta
    (fun hSpecial ↦
      MagnitudeConjecture.specialBiserial_socleFamilyQuotient_admitsStringPresentation
        S P hSpecial)

/-- The F1 equality boundary after Morita reconstruction of the primitive
projective presentation. -/
theorem ambientARSurplus_eq_zero_iff_isSpecialBiserial_withoutPresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    S.ambientARSurplus = 0 ↔ BoundQuiver.IsSpecialBiserial k A := by
  have hBeta :
      MagnitudeConjecture.RepresentationFiniteSpecialBiserialBetaCharacterization
        k := by
    intro B _ _ _ _ T
    exact MagnitudeConjecture.representationFinite_isSpecialBiserial_iff_beta_le_two
      T
  constructor
  · intro hzero
    exact (hBeta A S).2
      (S.beta_le_two_of_ambientARSurplus_eq_zero hBeta hzero)
  · intro hSpecial
    let U := S.moritaBasicSkeleton
    let P := S.moritaBasicPrimitiveProjectivePresentation
    have hBetaS : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 :=
      (hBeta A S).1 hSpecial
    have hBetaU : FiniteTauMatrix.beta
        U.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 :=
      S.moritaBasicSkeleton_beta_le hBetaS
    have hSpecialU :
        BoundQuiver.IsSpecialBiserial k S.moritaBasicAlgebra :=
      (hBeta S.moritaBasicAlgebra U).2 hBetaU
    have hzeroU : U.ambientARSurplus = 0 :=
      (U.ambientARSurplus_eq_zero_iff_isSpecialBiserial P).2 hSpecialU
    rw [S.ambientARSurplus_moritaBasicSkeleton] at hzeroU
    exact hzeroU

theorem categoryMagnitude_eq_projectiveCount_iff_isSpecialBiserial
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (P : S.PrimitiveProjectivePresentation) :
    MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
        (k := k) S.finiteTauCategoryData =
      (@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
        (fun x : Fin S.n ↦ Projective (S.fgObj x))
        (Classical.decPred _) : ℚ) ↔
    BoundQuiver.IsSpecialBiserial k A :=
  S.categoryMagnitude_eq_projectiveCount_iff_ambientARSurplus_eq_zero.trans
    (S.ambientARSurplus_eq_zero_iff_isSpecialBiserial P)

theorem categoryMagnitude_eq_projectiveCount_iff_isSpecialBiserial_withoutPresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
        (k := k) S.finiteTauCategoryData =
      (@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
        (fun x : Fin S.n ↦ Projective (S.fgObj x))
        (Classical.decPred _) : ℚ) ↔
    BoundQuiver.IsSpecialBiserial k A :=
  S.categoryMagnitude_eq_projectiveCount_iff_ambientARSurplus_eq_zero.trans
    S.ambientARSurplus_eq_zero_iff_isSpecialBiserial_withoutPresentation

theorem magnitudeConjecture_of_primitiveProjectivePresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (P : S.PrimitiveProjectivePresentation) :
    ((@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
        (fun x : Fin S.n ↦ Projective (S.fgObj x))
        (Classical.decPred _) : ℚ) ≤
      MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
        (k := k) S.finiteTauCategoryData) ∧
    (MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
          (k := k) S.finiteTauCategoryData =
        (@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
          (fun x : Fin S.n ↦ Projective (S.fgObj x))
          (Classical.decPred _) : ℚ) ↔
      BoundQuiver.IsSpecialBiserial k A) :=
  ⟨S.categoryMagnitude_ge_projectiveCount,
    S.categoryMagnitude_eq_projectiveCount_iff_isSpecialBiserial P⟩

theorem magnitudeConjecture_of_finiteIndecomposableSkeleton
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    ((@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
        (fun x : Fin S.n ↦ Projective (S.fgObj x))
        (Classical.decPred _) : ℚ) ≤
      MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
        (k := k) S.finiteTauCategoryData) ∧
    (MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
          (k := k) S.finiteTauCategoryData =
        (@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
          (fun x : Fin S.n ↦ Projective (S.fgObj x))
          (Classical.decPred _) : ℚ) ↔
      BoundQuiver.IsSpecialBiserial k A) :=
  ⟨S.categoryMagnitude_ge_projectiveCount,
    S.categoryMagnitude_eq_projectiveCount_iff_isSpecialBiserial_withoutPresentation⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]

def representationFiniteSkeleton (hA : IsRepresentationFinite k A) :
    FiniteIndecomposableSkeleton k A :=
  Classical.choice
    (FiniteIndecomposableSkeleton.exists_of_isRepresentationFinite hA)

def moduleCategoryMagnitude (hA : IsRepresentationFinite k A) : ℚ :=
  by
    letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
    exact FiniteTauMatrix.categoryMagnitude (k := k)
      (representationFiniteSkeleton hA).finiteTauCategoryData

def numberOfSimpleModules (hA : IsRepresentationFinite k A) : ℤ :=
  by
    letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
    exact @ARCount.projectiveCount
      (Fin (representationFiniteSkeleton hA).n) inferInstance
      (fun x ↦ Projective ((representationFiniteSkeleton hA).fgObj x))
      (Classical.decPred _)

theorem magnitudeConjecture (hA : IsRepresentationFinite k A) :
    ((numberOfSimpleModules hA : ℚ) ≤ moduleCategoryMagnitude hA) ∧
      (moduleCategoryMagnitude hA = (numberOfSimpleModules hA : ℚ) ↔
        BoundQuiver.IsSpecialBiserial k A) := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
  simpa only [moduleCategoryMagnitude, numberOfSimpleModules] using
    (representationFiniteSkeleton hA).magnitudeConjecture_of_finiteIndecomposableSkeleton

end MagnitudeConjecture.RightModule
