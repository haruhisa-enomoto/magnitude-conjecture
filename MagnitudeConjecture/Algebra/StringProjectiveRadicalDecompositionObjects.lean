import MagnitudeConjecture.Algebra.StringProjectiveRadical

/-!
# Module objects underlying string projective radical decompositions
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- A represented string-arrow range is nonzero: the trivial path before
the arrow is one of its continuation-basis indices. -/
theorem representedArrowLinearRange_nontrivial
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Nontrivial (LinearMap.range (P.representedArrowLinearMap a)) := by
  let p : P.toSpecialBiserialPresentation.LeftContinuationPath a :=
    ⟨⟨x, Quiver.Path.nil⟩, by
      rw [arrowMap, pathMap_comp]
      change pathMap P.toPresentation.relations
        ((Quiver.Path.nil : Quiver.Path x x).comp a.toPath) ≠ 0
      rw [Quiver.Path.comp_toPath_eq_cons]
      change pathMap P.toPresentation.relations a.toPath ≠ 0
      simpa [arrowMap] using
        arrowMap_ne_zero P.toPresentation.admissible a⟩
  exact ⟨P.representedArrowModuleBasis a p, 0,
    (P.representedArrowModuleBasis a).ne_zero p⟩

/-- The finitely generated module carried by one represented incoming-arrow
range. -/
def incomingArrowRangeFGObj
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := inferInstance
  exact FGModuleCat.of P.quotientCategoryAlgebraᵐᵒᵖ
    (LinearMap.range (P.representedArrowLinearMap a.2))

/-- The module Jacobson radical of a represented canonical projective,
retained as a finitely generated module. -/
def representedVertexRadicalFGObj
    (P : StringPresentation k A Q) (y : Q) :
    FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := inferInstance
  exact FGModuleCat.of P.quotientCategoryAlgebraᵐᵒᵖ
    (Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y))

/-- The incoming-arrow range family is linearly equivalent to the radical
of the represented projective. -/
def incomingArrowRangeFamilyRadicalLinearEquiv
    (P : StringPresentation k A Q) (y : Q) :
    (∀ a : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap a.2)) ≃ₗ[
        P.quotientCategoryAlgebraᵐᵒᵖ]
      Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) :=
  (LinearEquiv.ofInjective (P.incomingArrowRangeSumLinearMap y)
      (P.incomingArrowRangeSumLinearMap_injective y)).trans
    (LinearEquiv.ofEq _ _ (P.incomingArrowRangeSum_eq_jacobson y))

end StringPresentation

end MagnitudeConjecture.BoundQuiver
