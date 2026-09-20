import MagnitudeConjecture.Algebra.RightModuleStandardInteriorRadicalSquare
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceFullSubcategory

/-! # Exact irreducible-space comparison at interior interval targets -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- At an interior target, the full supported inclusion preserves the
linear irreducible quotient exactly. -/
def standardFormSupported_interior_irreducibleEquiv
    {m : ℕ} (a b : S.standardFormSupportedLabel m)
    (ht0 : 0 ≤ b.2.val)
    (htm : b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight) :
    CategoricalIrreducible.Space k (S.standardFormSupportedFamily m a).obj
      (S.standardFormSupportedFamily m b).obj ≃ₗ[k]
    CategoricalIrreducible.Space k (S.standardFormSupportedFamily m a)
      (S.standardFormSupportedFamily m b) :=
  CategoricalIrreducible.spaceFullSubcategoryEquiv k
    (Graded.FiniteGradedModule.intervalSupport m)
    Graded.FiniteGradedModule.finiteDecomposition _ _
    (fun Z hZ g hg ↦ S.standardFormGraded_interior_indecomposable_supported
      m b.1 b.2.val ht0 htm Z hZ g hg)

/-- The interior comparison retains irreducible multiplicities. -/
theorem standardFormSupported_interior_irreducible_finrank
    {m : ℕ} (a b : S.standardFormSupportedLabel m)
    (ht0 : 0 ≤ b.2.val)
    (htm : b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight) :
    Module.finrank k (CategoricalIrreducible.Space k (S.standardFormSupportedFamily m a)
      (S.standardFormSupportedFamily m b)) =
    Module.finrank k (CategoricalIrreducible.Space k (S.standardFormSupportedFamily m a).obj
      (S.standardFormSupportedFamily m b).obj) :=
  (S.standardFormSupported_interior_irreducibleEquiv a b ht0 htm).finrank_eq.symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
