import MagnitudeConjecture.Algebra.RightModuleMagnitudeCharacterizationConditional
import MagnitudeConjecture.Algebra.RightModuleBasicMorita
import MagnitudeConjecture.DeferredStructuralInputs

/-!
# Equality characterization from the proved structural inputs

This is the thin wrapper layer for basic algebras.  The proofs combine the
proved socle-reduction and Auslander--Reiten characterization theorems and
then discharge the axiom-free conditional endpoints.
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

/-- The proved socle reduction and AR characterization, specialized
through the axiom-free conditional equality characterization. -/
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

/-- The equality characterization for an arbitrary representation-finite
algebra.  The canonical basic Morita representative supplies the primitive
projective presentation internally. -/
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

/-- For a basic algebra with its primitive-projective presentation, magnitude
equals the number of simple modules exactly in the special-biserial case. -/
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

/-- Magnitude equality for an arbitrary representation-finite algebra, with
no basicness presentation supplied by the caller. -/
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

/-- The full magnitude inequality and equality characterization for a basic
representation-finite algebra presented by its primitive projectives. -/
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

/-- The full magnitude inequality and equality characterization for an
arbitrary finite-dimensional representation-finite algebra, relative only to
a complete finite indecomposable skeleton. -/
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

/-- A fixed duplicate-free finite indecomposable skeleton supplied by
representation-finiteness. -/
def representationFiniteSkeleton (hA : IsRepresentationFinite k A) :
    FiniteIndecomposableSkeleton k A :=
  Classical.choice
    (FiniteIndecomposableSkeleton.exists_of_isRepresentationFinite hA)

/-- The Leinster magnitude of the category of finitely generated right
modules, computed on the finite skeleton supplied by representation-
finiteness. -/
def moduleCategoryMagnitude (hA : IsRepresentationFinite k A) : ℚ :=
  by
    letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
    exact FiniteTauMatrix.categoryMagnitude (k := k)
      (representationFiniteSkeleton hA).finiteTauCategoryData

/-- The number of simple right modules.  For a finite-dimensional algebra it
is equivalently the number of indecomposable projectives, which is the count
used here on the chosen complete indecomposable skeleton. -/
def numberOfSimpleModules (hA : IsRepresentationFinite k A) : ℤ :=
  by
    letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
    exact @ARCount.projectiveCount
      (Fin (representationFiniteSkeleton hA).n) inferInstance
      (fun x ↦ Projective ((representationFiniteSkeleton hA).fgObj x))
      (Classical.decPred _)

/-- The magnitude conjecture for finitely generated right modules over an
arbitrary finite-dimensional representation-finite algebra.  Equality is
characterized by the Morita-invariant special-biserial predicate, so the
statement does not assume that the displayed algebra itself is basic. -/
theorem magnitudeConjecture (hA : IsRepresentationFinite k A) :
    ((numberOfSimpleModules hA : ℚ) ≤ moduleCategoryMagnitude hA) ∧
      (moduleCategoryMagnitude hA = (numberOfSimpleModules hA : ℚ) ↔
        BoundQuiver.IsSpecialBiserial k A) := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
  simpa only [moduleCategoryMagnitude, numberOfSimpleModules] using
    (representationFiniteSkeleton hA).magnitudeConjecture_of_finiteIndecomposableSkeleton

end MagnitudeConjecture.RightModule
