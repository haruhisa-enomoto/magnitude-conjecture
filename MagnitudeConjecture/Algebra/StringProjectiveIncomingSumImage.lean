import MagnitudeConjecture.Algebra.StringProjectiveIncomingPositiveBasis
import MagnitudeConjecture.Algebra.StringProjectiveIncomingContinuationImage
import MagnitudeConjecture.Algebra.StringProjectiveExplicitPathBasis

/-!
# Images of incoming-arrow product-basis vectors

Reindexing the incoming-arrow product basis by positive surviving paths keeps
the image calculation out of the nested arrow/continuation sigma type.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

set_option maxHeartbeats 1000000 in
/-- The incoming-range sum sends the vector belonging to a positive path to
the corresponding represented path element. -/
theorem incomingArrowRangeSumKLinearMap_positiveVector
    (P : StringPresentation k A Q) (y : Q)
    (q : P.PositiveVertexPath y) :
    P.incomingArrowRangeSumKLinearMap y
        (P.positiveIncomingVector y q) =
      P.representedPathElement y q.1 := by
  classical
  let t := (P.incomingContinuationEquivPositiveVertexPath y).symm q
  have ht : P.incomingContinuationEquivPositiveVertexPath y t = q :=
    (P.incomingContinuationEquivPositiveVertexPath y).apply_symm_apply q
  rw [← ht, P.positiveIncomingVector_equiv_apply]
  rcases t with ⟨⟨x, a⟩, p⟩
  rw [MagnitudeConjecture.piBasisVector_mk]
  change P.incomingArrowRangeSumKLinearMap y
      (P.incomingArrowRangeSingle y ⟨x, a⟩
        (P.incomingArrowModuleBasisFamily y ⟨x, a⟩ p)) = _
  exact P.incomingArrowRangeSumKLinearMap_singleBasis y ⟨x, a⟩ p

/-- The positive-path basis is carried to the corresponding subfamily of the
explicit represented-projective path basis. -/
theorem incomingArrowRangeSumKLinearMap_positiveBasis
    (P : StringPresentation k A Q) (y : Q)
    (q : P.PositiveVertexPath y) :
    P.incomingArrowRangeSumKLinearMap y
        (P.incomingArrowRangePositiveBasis y q) =
      P.representedVertexExplicitPathBasis y q.1 := by
  rw [P.incomingArrowRangePositiveBasis_apply,
    P.representedVertexExplicitPathBasis_apply]
  exact P.incomingArrowRangeSumKLinearMap_positiveVector y q

end StringPresentation

end MagnitudeConjecture.BoundQuiver
