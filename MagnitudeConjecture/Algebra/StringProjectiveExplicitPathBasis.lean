import MagnitudeConjecture.Algebra.StringProjectivePathBasis
import MagnitudeConjecture.LinearAlgebra.PiExplicitBasis

/-!
# An explicit path-element basis of a represented string projective
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The represented projective path basis rebuilt with the explicit
matrix-supported path elements as its definitional coefficient family. -/
def representedVertexExplicitPathBasis
    (P : StringPresentation k A Q) (y : Q) :
    Module.Basis (P.VertexPath y) k (P.representedVertexModule y) :=
  MagnitudeConjecture.explicitBasisOfFamily
    (P.representedVertexPathBasis y)
    (fun p ↦ P.representedPathElement y p)
    (fun p ↦ P.representedVertexPathBasis_apply y p)

@[simp]
theorem representedVertexExplicitPathBasis_apply
    (P : StringPresentation k A Q) (y : Q) (p : P.VertexPath y) :
    P.representedVertexExplicitPathBasis y p =
      P.representedPathElement y p := by
  unfold representedVertexExplicitPathBasis
  exact MagnitudeConjecture.explicitBasisOfFamily_apply _ _ _ p

end StringPresentation

end MagnitudeConjecture.BoundQuiver
