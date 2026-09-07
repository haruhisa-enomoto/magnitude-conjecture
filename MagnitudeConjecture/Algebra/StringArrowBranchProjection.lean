import MagnitudeConjecture.Algebra.StringArrowBranchMaps

/-! # Retraction of an arrow-branch inclusion -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance arrowBranchProjectionAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance arrowBranchProjectionAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

@[simp]
theorem arrowBranchRadicalInclusion_projection
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    (P.arrowBranchRadicalProjectionLinearMap a).comp
        (P.arrowBranchRadicalInclusionLinearMap a) =
      LinearMap.id := by
  classical
  apply LinearMap.ext
  intro z
  change (LinearMap.proj (R := P.quotientCategoryAlgebraᵐᵒᵖ) a)
    ((P.incomingArrowRangeFamilyRadicalLinearEquiv y).symm
      ((P.incomingArrowRangeFamilyRadicalLinearEquiv y)
        ((LinearMap.single P.quotientCategoryAlgebraᵐᵒᵖ
          (fun b : DisplayedIncomingArrow y ↦
            LinearMap.range (P.representedArrowLinearMap b.2)) a) z))) = z
  simp


end StringPresentation
end MagnitudeConjecture.BoundQuiver
