import MagnitudeConjecture.Algebra.StringArrowRepresentedMap

/-!
# Coefficient-field range of a represented string-arrow map

The algebra-linear and coefficient-field-linear arrow maps have the same
underlying range, which identifies the principal arrow right ideal with its
coefficient-field continuation model.
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

/-- The algebra-linear and coefficient-field-linear realizations of the
represented arrow map have the same underlying coefficient-field-linear
range. -/
def representedArrowRangeKLinearEquiv
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    LinearMap.range (P.representedArrowLinearMap a) ≃ₗ[k]
      LinearMap.range (P.representedArrowKLinearMap a) where
  toFun g := ⟨g.1, by
    rcases g.2 with ⟨f, hf⟩
    exact ⟨f, hf⟩⟩
  invFun g := ⟨g.1, by
    rcases g.2 with ⟨f, hf⟩
    exact ⟨f, hf⟩⟩
  left_inv g := by rfl
  right_inv g := by rfl
  map_add' g h := by rfl
  map_smul' r g := by
    apply Subtype.ext
    let gk : P.representedVertexHom y := g.1
    have hscalar :
        r • gk =
          (algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ r) • g.1 := by
      change
        r • gk = (r • 𝟙 _) ≫ gk
      simp
    exact hscalar.symm

/-- The literal principal arrow right ideal and its continuation model are
linearly equivalent over the coefficient field. -/
def arrowRightIdealContinuationLinearEquiv
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    RightModule.rightIdeal (P.arrowAlgebraCoordinate a) ≃ₗ[k]
      LinearMap.range (P.representedArrowKLinearMap a) :=
  ((P.arrowRightIdealRepresentedRangeLinearEquiv a).restrictScalars k).trans
    (P.representedArrowRangeKLinearEquiv a)

end StringPresentation

end MagnitudeConjecture.BoundQuiver
