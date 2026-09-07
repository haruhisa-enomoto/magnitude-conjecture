import MagnitudeConjecture.Algebra.RightModuleSupportCoordinate

/-!
# Literal middle-support Cartan data

This file assembles all algebraic and coordinate fields of the manuscript's
middle-support Cartan package from the literal complementary-vertex quotient.
The only remaining input is the root/Coxeter assertion for the two endpoints
of each supported Auslander--Reiten sequence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- The support skeleton attached to the middle term at `z`. -/
abbrev rightSequenceMiddleSupportSkeleton
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :=
  P.supportAlgebraSkeleton hA
    (S.minimalRightAlmostSplitAt z.1).middle

/-- Directedness of the support skeleton attached to the middle term at
`z`. -/
theorem rightSequenceMiddleSupportAcyclic
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    (P.rightSequenceMiddleSupportSkeleton hA z).HasAcyclicNonzeroNonisomorphisms :=
  P.supportAlgebraSkeleton_hasAcyclicNonzeroNonisomorphisms H hA
    (S.minimalRightAlmostSplitAt z.1).middle

/-- The literal support quotients provide every field of
`MiddleSupportCartanData` once the sequence-local root pairs are available.
This is the internal assembly boundary used by the unconditional constructor. -/
def middleSupportCartanDataOfRootPairs
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : RightModule.PrimitiveIdempotentData e)
    (R : ∀ (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}),
      (P.rightSequenceMiddleSupportSkeleton hA z).SupportCartanRootPairData
        (P.rightSequenceMiddleSupportAcyclic hA H z)
        (P.rightSequenceSupportTargetLabel hA z)
        (P.rightSequenceSupportSourceLabel hA z)) :
    S.MiddleSupportCartanData D where
  supportAlgebra z :=
    P.SupportAlgebra (S.minimalRightAlmostSplitAt z.1).middle
  supportRing _ := inferInstance
  supportAlgebraMap _ := inferInstance
  supportFiniteDimensional _ := inferInstance
  supportNoetherian _ := inferInstance
  skeleton z :=
    P.rightSequenceMiddleSupportSkeleton hA z
  acyclic z :=
    P.rightSequenceMiddleSupportAcyclic hA H z
  sourceLabel z := P.rightSequenceSupportTargetLabel hA z
  translatedLabel z := P.rightSequenceSupportSourceLabel hA z
  coordinate z hsupport :=
    P.supportProjectiveCoordinate hA
      (S.minimalRightAlmostSplitAt z.1).middle
      (S.primitiveSourceProjectiveLabel D) hsupport
  rootPair z _ := R z
  source_coordinate z hsupport :=
    P.supportProjectiveHomVector_eq_primitiveMultiplicity hA D
      (S.minimalRightAlmostSplitAt z.1).middle z.1
      (S.rightSequence_endpointSupport_subset_middle z).2 hsupport
  translated_coordinate z hsupport :=
    P.supportProjectiveHomVector_eq_primitiveMultiplicity hA D
      (S.minimalRightAlmostSplitAt z.1).middle
      (S.rightTranslationLabel z)
      (S.rightSequence_endpointSupport_subset_middle z).1 hsupport

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
