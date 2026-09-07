import MagnitudeConjecture.Algebra.StringProjectiveIncomingSumSingle

/-!
# An explicit positive-path basis for the incoming-arrow product
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

/-- The single-coordinate continuation vector belonging to a positive path. -/
def positiveIncomingVector
    (P : StringPresentation k A Q) (y : Q)
    (q : P.PositiveVertexPath y) :
    ∀ a : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap a.2) :=
  MagnitudeConjecture.piBasisVector
    (P.incomingArrowModuleBasisFamily y)
    ((P.incomingContinuationEquivPositiveVertexPath y).symm q)

/-- After a positive path is presented by its final arrow and continuation,
its named vector is the corresponding product-basis vector. -/
theorem positiveIncomingVector_equiv_apply
    (P : StringPresentation k A Q) (y : Q)
    (t : Σ a : DisplayedIncomingArrow y,
      P.toSpecialBiserialPresentation.LeftContinuationPath a.2) :
    P.positiveIncomingVector y
        (P.incomingContinuationEquivPositiveVertexPath y t) =
      MagnitudeConjecture.piBasisVector
        (P.incomingArrowModuleBasisFamily y) t := by
  unfold positiveIncomingVector
  rw [Equiv.symm_apply_apply]

/-- The incoming-arrow product basis reindexed by positive paths. -/
def incomingArrowRangePositiveRawBasis
    (P : StringPresentation k A Q) (y : Q) :
    Module.Basis (P.PositiveVertexPath y) k
      (∀ a : DisplayedIncomingArrow y,
        LinearMap.range (P.representedArrowLinearMap a.2)) :=
  (P.incomingArrowRangeBasis y).reindex
    (P.incomingContinuationEquivPositiveVertexPath y)

/-- The raw reindexed product basis has the named positive-path vector as
its value. -/
theorem incomingArrowRangePositiveRawBasis_apply
    (P : StringPresentation k A Q) (y : Q)
    (q : P.PositiveVertexPath y) :
    P.incomingArrowRangePositiveRawBasis y q =
      P.positiveIncomingVector y q := by
  rw [incomingArrowRangePositiveRawBasis, Module.Basis.reindex_apply]
  unfold incomingArrowRangeBasis positiveIncomingVector
  exact MagnitudeConjecture.piExplicitBasis_apply _ _

/-- A positive-path-indexed basis whose coefficient function is definitionally
the named positive incoming vector. -/
def incomingArrowRangePositiveBasis
    (P : StringPresentation k A Q) (y : Q) :
    Module.Basis (P.PositiveVertexPath y) k
      (∀ a : DisplayedIncomingArrow y,
        LinearMap.range (P.representedArrowLinearMap a.2)) :=
  MagnitudeConjecture.explicitBasisOfFamily
    (P.incomingArrowRangePositiveRawBasis y)
    (P.positiveIncomingVector y)
    (P.incomingArrowRangePositiveRawBasis_apply y)

@[simp]
theorem incomingArrowRangePositiveBasis_apply
    (P : StringPresentation k A Q) (y : Q)
    (q : P.PositiveVertexPath y) :
    P.incomingArrowRangePositiveBasis y q =
      P.positiveIncomingVector y q := by
  unfold incomingArrowRangePositiveBasis
  exact MagnitudeConjecture.explicitBasisOfFamily_apply _ _ _ q

end StringPresentation

end MagnitudeConjecture.BoundQuiver
