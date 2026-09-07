import MagnitudeConjecture.Algebra.StringArrowRightIdealBiproductCoordinate

/-!
# Object-indexed coordinates for represented string-arrow maps

Keeping the biproduct coordinates indexed by the objects of the quotient path
category avoids transporting a large dependent product along the equivalence
with the displayed quiver vertices.  Yoneda evaluation is performed directly
in each object coordinate.
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

/-- Forgetting the finite-dimensional-module subtype identifies a morphism
between represented modules with the corresponding natural transformation. -/
def representedVertexObjectFiniteHomLinearEquiv
    (P : StringPresentation k A Q) (x : Q)
    (X : Category P.toPresentation.relations) :
    P.representedVertexCoordinateFamily x X ≃ₗ[k]
      (CoveringHom.linearCoyonedaLinearModule (k := k) X ⟶
        (P.quotientRepresentable
          (obj P.toPresentation.relations x)).obj) :=
  InducedCategory.homLinearEquiv

/-- Linear Yoneda evaluation in coordinates indexed by quotient-category
objects. -/
def representedVertexObjectYonedaLinearEquiv
    (P : StringPresentation k A Q) (x : Q) :
    (∀ X : Category P.toPresentation.relations,
        P.representedVertexCoordinateFamily x X) ≃ₗ[k]
      (∀ X : Category P.toPresentation.relations,
        obj P.toPresentation.relations x ⟶ X) :=
  LinearEquiv.piCongrRight fun X ↦
    (P.representedVertexObjectFiniteHomLinearEquiv x X).trans
      (CoveringHom.linearCoyonedaHomEquiv
        (P.quotientRepresentable
          (obj P.toPresentation.relations x)).obj X)

/-- Biproduct restriction followed by linear Yoneda evaluation gives
coordinates indexed directly by quotient-category objects. -/
def representedVertexCoordinateLinearEquiv
    (P : StringPresentation k A Q) (x : Q) :
    P.representedVertexHom x ≃ₗ[k]
      (∀ X : Category P.toPresentation.relations,
        obj P.toPresentation.relations x ⟶ X) :=
  (P.representedVertexBiproductLinearEquiv x).trans
    (P.representedVertexObjectYonedaLinearEquiv x)

@[simp]
theorem representedVertexCoordinateLinearEquiv_apply
    (P : StringPresentation k A Q) (x : Q)
    (X : Category P.toPresentation.relations)
    (f : P.representedVertexHom x) :
    P.representedVertexCoordinateLinearEquiv x f X =
      (biproduct.ι P.quotientRepresentable X ≫ f).hom.hom.app X (𝟙 _) :=
  rfl

/-- Left composition by a displayed arrow at an arbitrary quotient-category
object. -/
def leftArrowCompositionLinearMapObj
    (P : StringPresentation k A Q)
    {x y : Q} (a : x ⟶ y)
    (X : Category P.toPresentation.relations) :
    (obj P.toPresentation.relations x ⟶ X) →ₗ[k]
      (obj P.toPresentation.relations y ⟶ X) where
  toFun f := arrowMap P.toPresentation.relations a ≫ f
  map_add' f g := by simp only [Preadditive.comp_add]
  map_smul' r f := by
    simpa only [RingHom.id_apply] using
      (CategoryTheory.Linear.comp_smul _ _ _
        (arrowMap P.toPresentation.relations a) r f)

@[simp]
theorem leftArrowCompositionLinearMapObj_obj
    (P : StringPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    P.leftArrowCompositionLinearMapObj a
        (obj P.toPresentation.relations z) =
      P.leftArrowCompositionLinearMap a z :=
  rfl

/-- In object-indexed coordinates, the represented arrow map is pointwise
left composition. -/
theorem representedVertexCoordinateLinearEquiv_arrow
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (f : P.representedVertexHom x)
    (X : Category P.toPresentation.relations) :
    P.representedVertexCoordinateLinearEquiv y
        (P.representedArrowKLinearMap a f) X =
      P.leftArrowCompositionLinearMapObj a X
        (P.representedVertexCoordinateLinearEquiv x f X) := by
  rw [P.representedVertexCoordinateLinearEquiv_apply y X,
    P.representedVertexCoordinateLinearEquiv_apply x X]
  rfl

/-- The pointwise continuation basis, stated at an arbitrary quotient-category
object. -/
def leftArrowCoordinateBasisObj
    (P : StringPresentation k A Q)
    {x y : Q} (a : x ⟶ y)
    (X : Category P.toPresentation.relations) :
    Module.Basis (P.LeftContinuationAt a (P.quotientObjectEquiv X)) k
      (LinearMap.range (P.leftArrowCompositionLinearMapObj a X)) := by
  rcases X with ⟨z⟩
  exact P.leftArrowCoordinateBasis a z

end StringPresentation

end MagnitudeConjecture.BoundQuiver
