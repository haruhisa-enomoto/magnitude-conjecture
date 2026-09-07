import MagnitudeConjecture.Algebra.StringProjectiveRadicalDecompositionBasic
import MagnitudeConjecture.Algebra.StringArrowRangeIndecomposableModule
import MagnitudeConjecture.CategoryTheory.FGModuleIndecomposable

/-!
# Indecomposability of string projective radical summands
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

noncomputable local instance quotientFGHasBinaryBiproducts
    (P : StringPresentation k A Q) :
    HasBinaryBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact HasBinaryBiproducts.of_hasBinaryProducts

theorem representedVertexRadicalSummand_indec
    (P : StringPresentation k A Q) (y : Q)
    (i : Fin (Nat.card (DisplayedIncomingArrow y))) :
    Indecomposable (representedVertexRadicalSummand P y i) := by
  classical
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := inferInstance
  let a := displayedIncomingArrowEquivFin y i
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (LinearMap.range (P.representedArrowLinearMap a.2)) := inferInstance
  change Indecomposable (FGModuleCat.of P.quotientCategoryAlgebraᵐᵒᵖ
    (LinearMap.range (P.representedArrowLinearMap a.2)))
  exact MagnitudeConjecture.fgModuleCatOf_indecomposable
    (P.representedArrowLinearRange_isIndecomposableModule a.2)

end MagnitudeConjecture.BoundQuiver.StringPresentation
