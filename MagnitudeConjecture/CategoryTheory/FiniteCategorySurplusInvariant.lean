import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplusReindex
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteObjects

/-! # Intrinsic surplus of finite linear module categories -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
universe u u' v
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Fintype C]
variable {D : Type u'} [Category.{v} D] [Preadditive D] [Linear k D] [Fintype D]

/-- The finite module-category surplus, with a complete skeleton constructed
from local representation finiteness. -/
def finiteCategorySurplus
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) : ℤ := by
  letI := enoughProjectives_of_finiteRepresentables hP
  let T := finiteCategoryModuleIndecomposableSkeleton hrep
  exact @ARCount.surplus (Fin T.n) inferInstance
    (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
    T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _)

/-- Any complete indecomposable skeleton computes the intrinsic surplus. -/
theorem finiteCategorySurplus_eq_skeleton
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C)) :
    letI := enoughProjectives_of_finiteRepresentables hP
    finiteCategorySurplus hP hrep = @ARCount.surplus (Fin T.n) inferInstance
      (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
      T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  letI := enoughProjectives_of_finiteRepresentables hP
  unfold finiteCategorySurplus
  rw [← (finiteCategoryModuleIndecomposableSkeleton hrep).sum_rightTauLocalDensity_eq_surplus,
    ← T.sum_rightTauLocalDensity_eq_surplus]
  exact (finiteCategoryModuleIndecomposableSkeleton hrep).sum_rightTauLocalDensity_eq T

/-- A finite linear category equivalence preserves module-category surplus. -/
theorem finiteCategorySurplus_eq_of_equivalence
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hQ : ∀ X : D, IsFiniteDimensionalModule (C := D) k
      (linearCoyonedaLinearModule (k := k) X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (hrepD : IsLocallyRepresentationFinite (k := k) (C := D))
    (E : C ≌ D) [E.functor.Additive] [E.functor.Linear k] :
    finiteCategorySurplus hP hrep = finiteCategorySurplus hQ hrepD := by
  letI := enoughProjectives_of_finiteRepresentables hP
  letI := enoughProjectives_of_finiteRepresentables hQ
  exact (finiteCategoryModuleIndecomposableSkeleton hrepD).surplus_eq_of_equivalence
    (finiteDimensionalModuleCongrEquivalenceOfFinite (k := k) E)
    (finiteCategoryModuleIndecomposableSkeleton hrep)

end MagnitudeConjecture.CoveringHom
