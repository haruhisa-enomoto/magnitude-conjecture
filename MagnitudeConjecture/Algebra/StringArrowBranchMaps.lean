import MagnitudeConjecture.Algebra.StringArrowBranchCoordinate

/-! # Branch maps for the represented projective radical -/

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

noncomputable local instance arrowBranchMapsAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance arrowBranchMapsAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The literal linear inclusion of one incoming-arrow range into the
represented projective radical. -/
def arrowBranchRadicalInclusionLinearMap
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    LinearMap.range (P.representedArrowLinearMap a.2) →ₗ[
      P.quotientCategoryAlgebraᵐᵒᵖ]
      Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) := by
  classical
  exact (P.incomingArrowRangeFamilyRadicalLinearEquiv y).toLinearMap.comp
    (LinearMap.single P.quotientCategoryAlgebraᵐᵒᵖ
      (fun b : DisplayedIncomingArrow y ↦
        LinearMap.range (P.representedArrowLinearMap b.2)) a)

/-- The literal coordinate projection from the represented projective
radical onto one incoming-arrow range. -/
def arrowBranchRadicalProjectionLinearMap
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) →ₗ[
      P.quotientCategoryAlgebraᵐᵒᵖ]
      LinearMap.range (P.representedArrowLinearMap a.2) :=
  (LinearMap.proj (R := P.quotientCategoryAlgebraᵐᵒᵖ) a).comp
    (P.incomingArrowRangeFamilyRadicalLinearEquiv y).symm.toLinearMap

/-- The literal arrow branch included in the represented projective radical. -/
def arrowBranchRadicalInclusion
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    P.incomingArrowRangeFGObj a ⟶ P.representedVertexRadicalFGObj y := by
  exact ConcreteCategory.ofHom (P.arrowBranchRadicalInclusionLinearMap a)

/-- Coordinate projection from the radical onto one arrow branch. -/
def arrowBranchRadicalProjection
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    P.representedVertexRadicalFGObj y ⟶ P.incomingArrowRangeFGObj a := by
  exact ConcreteCategory.ofHom (P.arrowBranchRadicalProjectionLinearMap a)


end StringPresentation
end MagnitudeConjecture.BoundQuiver
