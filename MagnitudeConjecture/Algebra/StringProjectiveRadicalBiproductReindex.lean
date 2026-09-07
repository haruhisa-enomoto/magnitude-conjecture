import MagnitudeConjecture.Algebra.StringProjectiveRadicalArrowPi
import MagnitudeConjecture.Algebra.StringProjectiveRadicalDecompositionBasic

/-!
# Reindexing the incoming-arrow biproduct by a finite ordinal
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

noncomputable local instance quotientFGHasFiniteBiproductsForReindex
    (P : StringPresentation k A Q) :
    HasFiniteBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Reindex the incoming-arrow categorical biproduct by its cardinality. -/
noncomputable def incomingArrowBiproductReindexIso
    (P : StringPresentation k A Q) (y : Q) :
    (⨁ (fun a : DisplayedIncomingArrow y ↦
      P.incomingArrowRangeFGObj a)) ≅
      ⨁ (P.representedVertexRadicalSummand y) := by
  classical
  exact biproduct.whiskerEquiv
    (displayedIncomingArrowEquivFin y).symm
    (fun a ↦ eqToIso (by
      simp [representedVertexRadicalSummand]))

end MagnitudeConjecture.BoundQuiver.StringPresentation
