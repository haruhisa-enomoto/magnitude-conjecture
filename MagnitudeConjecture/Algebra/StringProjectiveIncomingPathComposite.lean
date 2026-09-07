import MagnitudeConjecture.Algebra.StringProjectivePathBasis
import MagnitudeConjecture.CategoryTheory.CompCongr

/-!
# A represented-path composition used by incoming-arrow sums
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- Precomposing the path-representable composition law by the relevant
biproduct projection gives the literal continuation/path equality. -/
theorem biproductProjection_pathRepresentableMap_comp_arrow
    (P : StringPresentation k A Q) {z x y : Q}
    (p : Quiver.Path z x) (a : x ⟶ y) :
    (biproduct.π P.quotientRepresentable
        (obj P.toPresentation.relations z) ≫
      P.pathRepresentableMap p) ≫ P.arrowRepresentableMap a =
      biproduct.π P.quotientRepresentable
        (obj P.toPresentation.relations z) ≫
          P.pathRepresentableMap (p.cons a) := by
  have hpa :
      P.pathRepresentableMap p ≫ P.arrowRepresentableMap a =
        P.pathRepresentableMap (p.cons a) := by
    change P.pathRepresentableMap p ≫
        P.pathRepresentableMap a.toPath = _
    exact P.pathRepresentableMap_comp p a.toPath
  exact MagnitudeConjecture.assoc_comp_congr _ hpa

end MagnitudeConjecture.BoundQuiver.StringPresentation
