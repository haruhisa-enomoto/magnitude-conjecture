import MagnitudeConjecture.Algebra.StringArrowRightIdealRange
import Mathlib.LinearAlgebra.StdBasis

/-!
# The global continuation basis of a string-arrow right ideal

The product decomposition of the represented arrow range supplies a basis
indexed by all surviving paths before the arrow, with their starting vertices
retained.
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

/-- Collecting the fixed-startpoint continuation types over all displayed
vertices gives the manuscript's complete left-continuation type. -/
def leftContinuationSigmaEquiv
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    (Σ z : Q, P.LeftContinuationAt a z) ≃
      P.toSpecialBiserialPresentation.LeftContinuationPath a where
  toFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  invFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  left_inv p := by cases p with | mk z p => cases p; rfl
  right_inv p := by cases p with | mk p hp => cases p; rfl

@[simp]
theorem leftContinuationSigmaEquiv_symm_apply
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
    (P.leftContinuationSigmaEquiv a).symm p =
      ⟨p.1.1, ⟨p.1.2, p.2⟩⟩ :=
  rfl

/-- Reindexing the small family of pointwise continuation indices from
quotient-category objects to displayed vertices, and then collecting them
into complete left continuations. -/
def leftContinuationObjectSigmaEquiv
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    (Σ X : Category P.toPresentation.relations,
      P.LeftContinuationAt a (P.quotientObjectEquiv X)) ≃
      P.toSpecialBiserialPresentation.LeftContinuationPath a :=
  (Equiv.sigmaCongrLeft P.quotientObjectEquiv).trans
    (P.leftContinuationSigmaEquiv a)

@[simp]
theorem leftContinuationObjectSigmaEquiv_symm_apply
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
    (P.leftContinuationObjectSigmaEquiv a).symm p =
      ⟨obj P.toPresentation.relations p.1.1, ⟨p.1.2, p.2⟩⟩ :=
  rfl

/-- The global range of the represented arrow has a basis indexed by all
surviving paths before that arrow, with the starting vertex retained. -/
def representedArrowRangeBasis
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Module.Basis
      (P.toSpecialBiserialPresentation.LeftContinuationPath a) k
  (LinearMap.range (P.representedArrowKLinearMap a)) :=
  ((Pi.basis fun X : Category P.toPresentation.relations ↦
      P.leftArrowCoordinateBasisObj a X).map
      (P.representedArrowRangeCoordinateLinearEquiv a).symm).reindex
    (P.leftContinuationObjectSigmaEquiv a)

/-- At its starting vertex, a global basis vector is the corresponding
pointwise continuation-path vector. -/
theorem representedArrowRangeBasis_coordinate_self
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
    P.representedArrowRangeCoordinateLinearEquiv a
        (P.representedArrowRangeBasis a p)
          (obj P.toPresentation.relations p.1.1) =
      P.leftArrowCoordinateBasis a p.1.1 ⟨p.1.2, p.2⟩ := by
  classical
  rw [representedArrowRangeBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply]
  rw [P.leftContinuationObjectSigmaEquiv_symm_apply]
  exact Pi.single_eq_same _ _

/-- Away from its starting vertex, a global continuation basis vector has
zero coordinate. -/
theorem representedArrowRangeBasis_coordinate_ne
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (z : Q) (hz : z ≠ p.1.1) :
    P.representedArrowRangeCoordinateLinearEquiv a
        (P.representedArrowRangeBasis a p)
          (obj P.toPresentation.relations z) = 0 := by
  classical
  rw [representedArrowRangeBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply]
  rw [P.leftContinuationObjectSigmaEquiv_symm_apply]
  apply Pi.single_eq_of_ne
  intro h
  apply hz
  simpa using congrArg P.quotientObjectEquiv h

/-- The coefficient-field dimension of the assembled represented arrow
image is the number of its surviving left continuations. -/
theorem finrank_representedArrowKLinearMap_range_eq_natCard
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Module.finrank k (LinearMap.range (P.representedArrowKLinearMap a)) =
      Nat.card
        (P.toSpecialBiserialPresentation.LeftContinuationPath a) := by
  letI : Finite
      (P.toSpecialBiserialPresentation.LeftContinuationPath a) :=
    P.toSpecialBiserialPresentation.leftContinuationPath_finite a
  letI : Fintype
      (P.toSpecialBiserialPresentation.LeftContinuationPath a) :=
    Fintype.ofFinite _
  simpa only [Fintype.card_eq_nat_card] using
    Module.finrank_eq_card_basis (P.representedArrowRangeBasis a)

end StringPresentation

end MagnitudeConjecture.BoundQuiver
