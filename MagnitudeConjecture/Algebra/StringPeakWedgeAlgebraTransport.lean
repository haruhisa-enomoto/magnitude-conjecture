import MagnitudeConjecture.Algebra.StringAlgebraSkeletonClassification
import MagnitudeConjecture.Algebra.StringPeakWedgeRepresentable

/-!
# Peak-wedge projectivity under algebra-skeleton transport

The quotient-category algebra skeleton is classified by reverse coefficient
duals of literal right-string modules.  This file records the resulting
projective/injective reversal explicitly: a projective literal string gives
an injective object of the right-module algebra skeleton.  In particular,
the strict overlapping-cohook boundary is injective after transport.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance peakWedgeTransportAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance peakWedgeTransportAlgebraOppositeNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- An algebra-skeleton object is injective exactly when its selected
literal right-string representative is projective. -/
theorem algebraSkeletonObj_injective_iff_literalString_projective
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (i : Fin T.n) :
    let L := (P.algebraSkeletonDetectorIndex S T i).endpointWord.word
      |>.finiteRightModule P.monomial
    Injective (T.fgObj i) ↔ Projective L := by
  let C := Category P.toPresentation.relations
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  let L := (P.algebraSkeletonDetectorIndex S T i).endpointWord.word
    |>.finiteRightModule P.monomial
  let R := reverseFiniteCoefficientDual (k := k) L
  let e : E.functor.obj R ≅ T.fgObj i :=
    P.representedAlgebraSkeletonStringDualIso S T i
  constructor
  · intro hT
    have hmap : Injective (E.functor.obj R) :=
      Injective.of_iso e.symm hT
    have hR : Injective R := (E.map_injective_iff R).1 hmap
    exact (reverseFiniteCoefficientDual_injective_iff_projective L).1 hR
  · intro hL
    have hR : Injective R :=
      (reverseFiniteCoefficientDual_injective_iff_projective L).2 hL
    have hmap : Injective (E.functor.obj R) :=
      (E.map_injective_iff R).2 hR
    exact Injective.of_iso e hmap

/-- A strict overlap of the two maximal cohook deletions makes the
corresponding quotient-algebra skeleton object injective. -/
theorem algebraSkeletonObj_injective_of_overlappingCohookDeletions
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (i : Fin T.n)
    {L D : StringWord.Word P.toPresentation.relations}
    (leftDeletion : StringWord.Word.LeftCohookDeletion
      (P.algebraSkeletonDetectorIndex S T i).endpointWord.word D)
    (rightDeletion : StringWord.Word.CohookDeletion
      (P.algebraSkeletonDetectorIndex S T i).endpointWord.word L)
    (hoverlap :
      (P.algebraSkeletonDetectorIndex S T i).endpointWord.word.length <
        leftDeletion.steps + rightDeletion.steps) :
    Injective (T.fgObj i) := by
  apply
    (P.algebraSkeletonObj_injective_iff_literalString_projective S T i).2
  exact
    StringWord.Word.finiteRightModule_projective_of_overlappingCohookDeletions
      P leftDeletion rightDeletion hoverlap

end StringPresentation
end MagnitudeConjecture.BoundQuiver
