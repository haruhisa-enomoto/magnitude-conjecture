import MagnitudeConjecture.Algebra.StringArrowRightIdealRangeK
import MagnitudeConjecture.CategoryTheory.LinearBiproduct

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- The Hom-space family indexed by objects of the quotient path category. -/
abbrev representedVertexCoordinateFamily
    (P : StringPresentation k A Q) (x : Q)
    (X : Category P.toPresentation.relations) :=
  P.quotientRepresentable X ⟶
    P.quotientRepresentable (obj P.toPresentation.relations x)

/-- The same Hom-space family indexed by displayed quiver vertices. -/
abbrev representedVertexDisplayedCoordinateFamily
    (P : StringPresentation k A Q) (x z : Q) :=
  P.representedVertexCoordinateFamily x
    (obj P.toPresentation.relations z)

/-- Restriction to biproduct summands gives the first stage of the displayed
coordinates of a represented vertex module. -/
def representedVertexBiproductLinearEquiv
    (P : StringPresentation k A Q) (x : Q) :
    P.representedVertexHom x ≃ₗ[k]
      (∀ X : Category P.toPresentation.relations,
        P.representedVertexCoordinateFamily x X) :=
  MagnitudeConjecture.CategoryTheory.biproductHomLinearEquiv k
    (P.quotientRepresentable (obj P.toPresentation.relations x))
    P.quotientRepresentable

end MagnitudeConjecture.BoundQuiver.StringPresentation
