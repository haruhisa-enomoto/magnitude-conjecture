import MagnitudeConjecture.Algebra.RightModuleMagnitudeSurplus
import MagnitudeConjecture.Algebra.RightModuleIntervalEquality
import MagnitudeConjecture.Algebra.RightModuleBasicMorita
import MagnitudeConjecture.Algebra.RightModuleSocleReductionString
import MagnitudeConjecture.Algebra.RightModuleSimpleCount

/-!
# The magnitude theorem through graded intervals

The inequality follows from nonnegative directed interval surplus and its
uniform comparison with ambient surplus. At equality, separated interval
packing and thinness make the control interval special biserial. The actual
graded incoming maps transfer its beta bound to the original algebra. The
converse uses the proved socle reduction to a string algebra.
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

/-- Zero surplus is equivalent to special biseriality for a displayed
primitive-projective presentation. -/
theorem ambientARSurplus_eq_zero_iff_isSpecialBiserial
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (P : S.PrimitiveProjectivePresentation) :
    S.ambientARSurplus = 0 ↔ BoundQuiver.IsSpecialBiserial k A := by
  constructor
  · exact S.isSpecialBiserial_of_ambientARSurplus_eq_zero_by_intervals
  · intro hSpecial
    exact P.ambientARSurplus_eq_zero_of_socleFamilyQuotient_admitsStringPresentation
      (MagnitudeConjecture.specialBiserial_socleFamilyQuotient_admitsStringPresentation S P hSpecial)

/-- The equality characterization for an arbitrary finite-dimensional algebra,
using its basic Morita representative for the converse. -/
theorem ambientARSurplus_eq_zero_iff_isSpecialBiserial_withoutPresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    S.ambientARSurplus = 0 ↔ BoundQuiver.IsSpecialBiserial k A := by
  constructor
  · exact S.isSpecialBiserial_of_ambientARSurplus_eq_zero_by_intervals
  · intro hSpecial
    let U := S.moritaBasicSkeleton
    let P := S.moritaBasicPrimitiveProjectivePresentation
    have hBetaS : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 :=
      MagnitudeConjecture.specialBiserial_beta_le_two S hSpecial
    have hBetaU : FiniteTauMatrix.beta
        U.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 :=
      S.moritaBasicSkeleton_beta_le hBetaS
    have hSpecialU : BoundQuiver.IsSpecialBiserial k S.moritaBasicAlgebra :=
      U.isSpecialBiserial_of_beta_le_two hBetaU
    have hzeroU : U.ambientARSurplus = 0 :=
      (U.ambientARSurplus_eq_zero_iff_isSpecialBiserial P).mpr hSpecialU
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
