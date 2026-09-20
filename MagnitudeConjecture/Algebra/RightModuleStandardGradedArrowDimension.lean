import MagnitudeConjecture.Algebra.RightModuleStandardGradedIrreducibleDimension
import MagnitudeConjecture.Algebra.RightModuleStandardDegreeOneDimension

/-! # Graded irreducible dimensions in terms of ordinary arrow multiplicities -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Shift difference one contributes the ordinary arrow multiplicity; every
other shift difference contributes zero. -/
def standardFormGraded_irreducible_arrowMultiplicity
    (X Y : S.StandardFormMeshCategory) (s t : ℤ) :=
  (S.standardFormGraded_irreducible_finrank X Y s t).trans
    (congrArg (fun d : ℕ ↦ if s = t + 1 then d else 0)
      (S.standardFormIntegerHomGrading_one_finrank X Y))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
