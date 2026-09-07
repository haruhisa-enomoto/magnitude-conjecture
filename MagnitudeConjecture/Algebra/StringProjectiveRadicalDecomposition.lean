import MagnitudeConjecture.Algebra.StringProjectiveRadicalBiproductReindex
import MagnitudeConjecture.Algebra.StringProjectiveRadicalSummandIndec
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition

/-!
# Indecomposable decomposition of string projective radicals

The radical of a represented canonical projective is the internal direct
sum of the represented ranges of the displayed arrows ending at its vertex.
Each such range is uniserial and nonzero, hence indecomposable.  This file
packages that literal path decomposition in the finite categorical format
used by almost-split multiplicity arguments.
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

noncomputable local instance quotientFGHasFiniteBiproductsForDecomposition
    (P : StringPresentation k A Q) :
    HasFiniteBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact HasFiniteBiproducts.of_hasFiniteProducts

noncomputable local instance quotientFGHasBinaryBiproductsForDecomposition
    (P : StringPresentation k A Q) :
    HasBinaryBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact HasBinaryBiproducts.of_hasBinaryProducts

private noncomputable def representedVertexRadicalIsoBiproduct
    (P : StringPresentation k A Q) (y : Q) :
    P.representedVertexRadicalFGObj y ≅
      ⨁ (representedVertexRadicalSummand P y) :=
  (P.representedVertexRadicalToArrowPiIso y).trans <|
    (P.representedVertexRadicalArrowPiToBiproductIso y).trans <|
      P.incomingArrowBiproductReindexIso y

/-- The radical of the represented projective at `y`, decomposed into one
indecomposable uniserial summand for every displayed arrow ending at `y`. -/
def representedVertexRadicalDecomposition
    (P : StringPresentation k A Q) (y : Q) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (P.representedVertexRadicalFGObj y) := by
  classical
  exact {
    n := Nat.card (DisplayedIncomingArrow y)
    summand := representedVertexRadicalSummand P y
    indecomposable := representedVertexRadicalSummand_indec P y
    isoBiproduct := representedVertexRadicalIsoBiproduct P y }

/-- The displayed radical decomposition has exactly as many summands as
there are displayed arrows ending at the vertex. -/
@[simp]
theorem representedVertexRadicalDecomposition_n
    (P : StringPresentation k A Q) (y : Q) :
    (P.representedVertexRadicalDecomposition y).n =
      Nat.card (DisplayedIncomingArrow y) := by
  dsimp [representedVertexRadicalDecomposition]

end StringPresentation

end MagnitudeConjecture.BoundQuiver
