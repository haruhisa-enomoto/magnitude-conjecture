import MagnitudeConjecture.Algebra.RightModuleStandardInteriorSupport
import MagnitudeConjecture.Algebra.RightModuleStandardSupportedCategory
import MagnitudeConjecture.CategoryTheory.RadicalSquareFullSubcategory

/-! # Intrinsic radical squares at interior interval targets -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- At an interior target, restriction preserves and reflects membership
in the square of the intrinsic categorical radical. -/
theorem standardFormSupported_interior_radicalSquare_iff
    {m : ℕ} (a b : S.standardFormSupportedLabel m)
    (ht0 : 0 ≤ b.2.val)
    (htm : b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight)
    (f : S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b) :
    f.hom ∈ ((homIdeal : HomIdeal (Graded.FiniteGradedModule.ShiftedModule
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite))) ⋆ᵢ homIdeal).hom
        (S.standardFormSupportedFamily m a).obj (S.standardFormSupportedFamily m b).obj ↔
      f ∈ ((homIdeal : HomIdeal (S.standardFormSupportedCategory m)) ⋆ᵢ homIdeal).hom
        (S.standardFormSupportedFamily m a) (S.standardFormSupportedFamily m b) :=
  MagnitudeConjecture.radicalSquare_fullSubcategory_iff
    (Graded.FiniteGradedModule.intervalSupport m)
    Graded.FiniteGradedModule.finiteDecomposition _ _
    (fun Z hZ g hg ↦ S.standardFormGraded_interior_indecomposable_supported
      m b.1 b.2.val ht0 htm Z hZ g hg) f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
