import MagnitudeConjecture.Algebra.StringFiniteBoundaryIrreducible
import MagnitudeConjecture.Algebra.StringFiniteDoubleCohookIrreducible
import MagnitudeConjecture.Algebra.StringFiniteMixedBoundaryIrreducible
import MagnitudeConjecture.Algebra.StringFinitePureOneSidedHook
import MagnitudeConjecture.Algebra.StringFiniteSkeletonClassification
import MagnitudeConjecture.Algebra.StringCohookDeletionNesting
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIrreducibleAlmostSplit

/-!
# Almost-split string boundary complexes

The positive, mixed, and negative Butler--Ringel boundary complexes are short
exact with irreducible differentials.  A complete finite indecomposable
skeleton therefore identifies each one with the almost-split sequence at its
literal string endpoint.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The label of the fixed finite indecomposable skeleton belonging to a
literal string word. -/
def finiteStringSkeletonLabel
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    (C : StringWord.Word P.toPresentation.relations) : Fin V.n :=
  StringWord.DetectorIndex.finiteSkeletonLabel V
    (StringWord.DetectorIndex.ofWord S C)

/-- A literal string module is isomorphic to the selected skeleton object
with the same inversion-class detector index. -/
def finiteStringSkeletonIso
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    (C : StringWord.Word P.toPresentation.relations) :
    C.finiteRightModule P.monomial ≅
      V.obj (P.finiteStringSkeletonLabel S V C) := by
  let i := StringWord.DetectorIndex.ofWord S C
  have hi : StringWord.DetectorIndex.ofWord S i.endpointWord.word =
      StringWord.DetectorIndex.ofWord S C :=
    StringWord.DetectorIndex.ofWord_endpointWord i
  have hIso : Nonempty
      (C.finiteRightModule P.monomial ≅
        V.obj (P.finiteStringSkeletonLabel S V C)) := by
    rcases (StringWord.DetectorIndex.ofWord_eq_iff
        S i.endpointWord.word C).mp hi with hsame | hreverse
    · exact ⟨
        eqToIso (congrArg
          (fun W : StringWord.Word P.toPresentation.relations ↦
            W.finiteRightModule P.monomial) hsame).symm ≪≫
          StringWord.DetectorIndex.finiteSkeletonIso V i⟩
    · exact ⟨
        C.finiteReverseRightModuleIso ≪≫
          eqToIso (congrArg
            (fun W : StringWord.Word P.toPresentation.relations ↦
              W.finiteRightModule P.monomial) hreverse).symm ≪≫
            StringWord.DetectorIndex.finiteSkeletonIso V i⟩
  exact Classical.choice hIso

/-- Admissibility makes the contravariant finite string-module category have
enough projectives. -/
noncomputable local instance finiteStringBoundaryEnoughProjectives
    (P : StringPresentation k A Q) :
    EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, u, u, u}
        (C := (Category P.toPresentation.relations)ᵒᵖ) k) := by
  apply enoughProjectives_of_finiteRepresentables
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k (Y.unop ⟶ X.unop) :=
      quotientHom_finiteDimensional P.toPresentation.admissible _ _
    exact FiniteDimensional.of_injective
      (CoveringHom.oppositeHomLinearEquiv X Y).toLinearMap
      (CoveringHom.oppositeHomLinearEquiv X Y).injective
  · letI : Finite ((Category P.toPresentation.relations)ᵒᵖ) :=
      Finite.of_injective Opposite.unop Opposite.unop_injective
    exact Set.toFinite _

/-- The positive two-hook complex is the right almost-split sequence ending
at its base string. -/
theorem twoHookMaximalFiniteShortComplex_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C rightResult : StringWord.Word P.toPresentation.relations}
    (right : StringWord.Word.HookExtension C rightResult)
    (left : StringWord.Word.LeftHookExtension C)
    (hpath : StringWord.IsString P.toPresentation.relations
      (StringWord.Word.twoHookPath right left)) :
    IsRightAlmostSplit
      (StringWord.Word.twoHookMaximalFiniteShortComplex
        right left hpath P.monomial).g := by
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  exact V.isRightAlmostSplit_of_shortExact_of_irreducible
    (StringWord.Word.twoHookMaximalFiniteShortComplex_shortExact
      S right left hpath)
    (StringWord.Word.twoHookMaximalFiniteShortComplex_f_isIrreducible
      S right left hpath)
    (StringWord.Word.twoHookMaximalFiniteShortComplex_g_isIrreducible
      S right left hpath)
    (P.finiteStringSkeletonLabel S V C)
    (P.finiteStringSkeletonIso S V C)

omit [IsAlgClosed k] in
/-- A pure-positive left-hook projection is right almost split whenever its
hooked result is maximal at the opposite endpoint. -/
theorem purePositiveLeftHookResultPeakFiniteShortComplex_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C : StringWord.Word P.toPresentation.relations}
    (hpure : C.IsPurePositive P.toPresentation.admissible)
    (left : StringWord.Word.LeftHookExtension C)
    (hresultPeak : left.result.StartsOnPeak) :
    IsRightAlmostSplit
      (left.purePositiveResultPeakFiniteShortComplex
        P.toPresentation.admissible hpure hresultPeak P.monomial).g := by
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let hcover : StringWord.Word.EveryFiniteModuleIsFiniteStringSum P.monomial :=
    StringWord.DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  exact V.isRightAlmostSplit_of_shortExact_of_irreducible
    (left.purePositiveResultPeakFiniteShortComplex_shortExact
      P.toPresentation.admissible hpure hresultPeak P.monomial)
    (left.purePositiveResultPeakFiniteShortComplex_f_isIrreducible
      P.toPresentation.admissible hpure hresultPeak P.monomial hcover)
    (left.purePositiveResultPeakFiniteShortComplex_g_isIrreducible
      P.toPresentation.admissible hpure hresultPeak P.monomial hcover)
    (P.finiteStringSkeletonLabel S V C)
    (P.finiteStringSkeletonIso S V C)

omit [IsAlgClosed k] in
/-- A pure-positive string which is maximal at the right endpoint and has a
left hook has a one-middle right almost-split sequence. -/
theorem purePositiveLeftHookFiniteShortComplex_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C : StringWord.Word P.toPresentation.relations}
    (hpure : C.IsPurePositive P.toPresentation.admissible)
    (hstart : C.StartsOnPeak)
    (left : StringWord.Word.LeftHookExtension C) :
    IsRightAlmostSplit
      (left.purePositiveFiniteShortComplex P.toPresentation.admissible
        hpure hstart P.monomial).g := by
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let hcover : StringWord.Word.EveryFiniteModuleIsFiniteStringSum P.monomial :=
    StringWord.DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  exact V.isRightAlmostSplit_of_shortExact_of_irreducible
    (left.purePositiveFiniteShortComplex_shortExact
      P.toPresentation.admissible hpure hstart P.monomial)
    (left.purePositiveFiniteShortComplex_f_isIrreducible
      P.toPresentation.admissible hpure hstart P.monomial hcover)
    (left.purePositiveFiniteShortComplex_g_isIrreducible
      P.toPresentation.admissible hpure hstart P.monomial hcover)
    (P.finiteStringSkeletonLabel S V C)
    (P.finiteStringSkeletonIso S V C)

omit [IsAlgClosed k] in
/-- The reversed pure-negative form: a pure-negative string maximal at its
left endpoint with a right hook has a one-middle right almost-split map. -/
theorem pureNegativeRightHookReverseFiniteMap_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C D : StringWord.Word P.toPresentation.relations}
    (hpure : C.IsPureNegative P.toPresentation.admissible)
    (hend : C.EndsOnPeak)
    (right : StringWord.Word.HookExtension C D) :
    IsRightAlmostSplit
      (((right.toReverseLeftHook).purePositiveFiniteShortComplex
          P.toPresentation.admissible hpure hend P.monomial).g ≫
        C.finiteReverseRightModuleIso.symm.hom) := by
  have hreverse :=
    P.purePositiveLeftHookFiniteShortComplex_isRightAlmostSplit
      S V hpure hend right.toReverseLeftHook
  exact hreverse.postcomp_iso C.finiteReverseRightModuleIso.symm

/-- A left cohook deletion and a right hook give the right almost-split
sequence ending at the original string. -/
theorem leftCohookDeletionRightHookMaximalFiniteShortComplex_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C D corner : StringWord.Word P.toPresentation.relations}
    (deletion : StringWord.Word.LeftCohookDeletion C D)
    (right : StringWord.Word.HookExtension C corner) :
    IsRightAlmostSplit
      (StringWord.Word.leftCohookDeletionRightHookMaximalFiniteShortComplex
        deletion right P.monomial).g := by
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let leftCohook := deletion.toLeftCohookExtension
  have hleft : leftCohook.result = C :=
    deletion.toLeftCohookExtension_result
  let transportedRight : StringWord.Word.HookExtension
      leftCohook.result corner :=
    Eq.mp
      (congrArg
        (fun W : StringWord.Word P.toPresentation.relations ↦
          StringWord.Word.HookExtension W corner)
        hleft.symm)
      right
  change IsRightAlmostSplit
    (StringWord.Word.mixedMaximalFiniteShortComplex
      leftCohook transportedRight P.monomial).g
  exact V.isRightAlmostSplit_of_shortExact_of_irreducible
    (StringWord.Word.mixedMaximalFiniteShortComplex_shortExact
      S leftCohook transportedRight)
    (StringWord.Word.mixedMaximalFiniteShortComplex_f_isIrreducible
      S leftCohook transportedRight)
    (StringWord.Word.mixedMaximalFiniteShortComplex_g_isIrreducible
      S leftCohook transportedRight)
    (P.finiteStringSkeletonLabel S V C)
    (eqToIso (congrArg
        (fun W : StringWord.Word P.toPresentation.relations ↦
          W.finiteRightModule P.monomial) hleft) ≪≫
      P.finiteStringSkeletonIso S V C)

/-- The target of the reversed asymmetric finite complex, returned to the
original literal string module. -/
def rightCohookDeletionLeftHookReverseTargetIso
    (P : StringPresentation k A Q)
    {C D : StringWord.Word P.toPresentation.relations}
    (deletion : StringWord.Word.CohookDeletion C D)
    (left : StringWord.Word.LeftHookExtension C) :
    (StringWord.Word.leftCohookDeletionRightHookMaximalFiniteShortComplex
        deletion.toReverseLeftCohookDeletion left.hook P.monomial).X₃ ≅
      C.finiteRightModule P.monomial := by
  let reverseDeletion := deletion.toReverseLeftCohookDeletion
  let leftCohook := reverseDeletion.toLeftCohookExtension
  have htarget : leftCohook.result = C.reverse :=
    reverseDeletion.toLeftCohookExtension_result
  change leftCohook.result.finiteRightModule P.monomial ≅
    C.finiteRightModule P.monomial
  exact eqToIso (congrArg
      (fun W : StringWord.Word P.toPresentation.relations ↦
        W.finiteRightModule P.monomial) htarget) ≪≫
    C.finiteReverseRightModuleIso.symm

/-- A right cohook deletion and a left hook give the opposite asymmetric
right almost-split sequence.  The existing mixed complex is constructed on
the reversed word; the canonical reversal isomorphism returns its endpoint
to the original literal string module. -/
theorem rightCohookDeletionLeftHookReverseMaximalFiniteShortComplex_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C D : StringWord.Word P.toPresentation.relations}
    (deletion : StringWord.Word.CohookDeletion C D)
    (left : StringWord.Word.LeftHookExtension C) :
    IsRightAlmostSplit
      ((StringWord.Word.leftCohookDeletionRightHookMaximalFiniteShortComplex
          deletion.toReverseLeftCohookDeletion left.hook P.monomial).g ≫
        (P.rightCohookDeletionLeftHookReverseTargetIso deletion left).hom) := by
  have hreverse :=
    P.leftCohookDeletionRightHookMaximalFiniteShortComplex_isRightAlmostSplit
      S V deletion.toReverseLeftCohookDeletion left.hook
  exact hreverse.postcomp_iso
    (P.rightCohookDeletionLeftHookReverseTargetIso deletion left)

/-- Two cohook deletions give the right almost-split sequence ending at the
original string. -/
theorem doubleCohookDeletionMaximalFiniteShortComplex_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C L D : StringWord.Word P.toPresentation.relations}
    (leftDeletion : StringWord.Word.LeftCohookDeletion L D)
    (rightDeletion : StringWord.Word.CohookDeletion C L) :
    IsRightAlmostSplit
      (StringWord.Word.doubleCohookDeletionMaximalFiniteShortComplex
        leftDeletion rightDeletion P.monomial).g := by
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let leftCohook := leftDeletion.toLeftCohookExtension
  let cornerRight :=
    StringWord.Word.doubleCohookDeletionCornerRightCohook
      leftDeletion rightDeletion
  change IsRightAlmostSplit
    (StringWord.Word.doubleCohookMaximalFiniteShortComplex
      leftCohook cornerRight P.monomial).g
  have hcorner :
      (StringWord.Word.doubleCohookMaximalSquare
        leftCohook cornerRight).corner = C :=
    StringWord.Word.doubleCohookMaximalSquare_corner
      leftCohook cornerRight
  exact V.isRightAlmostSplit_of_shortExact_of_irreducible
    (StringWord.Word.doubleCohookMaximalFiniteShortComplex_shortExact
      S leftCohook cornerRight)
    (StringWord.Word.doubleCohookMaximalFiniteShortComplex_f_isIrreducible
      S leftCohook cornerRight)
    (StringWord.Word.doubleCohookMaximalFiniteShortComplex_g_isIrreducible
      S leftCohook cornerRight)
    (P.finiteStringSkeletonLabel S V C)
    (eqToIso (congrArg
        (fun W : StringWord.Word P.toPresentation.relations ↦
          W.finiteRightModule P.monomial) hcorner) ≪≫
      P.finiteStringSkeletonIso S V C)

/-- Nonoverlapping cohook deletions at the two endpoints can be ordered into
the double-cohook right almost-split sequence ending at the original word. -/
theorem exists_doubleCohookDeletion_rightAlmostSplit_of_steps_add_le
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C L D : StringWord.Word P.toPresentation.relations}
    (leftDeletion : StringWord.Word.LeftCohookDeletion C D)
    (rightDeletion : StringWord.Word.CohookDeletion C L)
    (hnonoverlap :
      leftDeletion.steps + rightDeletion.steps ≤ C.length) :
    ∃ (E : StringWord.Word P.toPresentation.relations)
      (leftAfter : StringWord.Word.LeftCohookDeletion L E),
      IsRightAlmostSplit
        (StringWord.Word.doubleCohookDeletionMaximalFiniteShortComplex
          leftAfter rightDeletion P.monomial).g := by
  rcases
      StringWord.Word.exists_leftCohookDeletion_after_right_of_steps_add_le
        leftDeletion rightDeletion hnonoverlap with
    ⟨E, ⟨leftAfter⟩⟩
  exact ⟨E, leftAfter,
    P.doubleCohookDeletionMaximalFiniteShortComplex_isRightAlmostSplit
      S V leftAfter rightDeletion⟩

/-- Two cohook deletions either give the double-cohook right almost-split
sequence, or lie in the rigid two-letter overlap boundary. -/
theorem doubleCohookDeletion_rightAlmostSplit_or_overlap
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C L D : StringWord.Word P.toPresentation.relations}
    (leftDeletion : StringWord.Word.LeftCohookDeletion C D)
    (rightDeletion : StringWord.Word.CohookDeletion C L) :
    (∃ (E : StringWord.Word P.toPresentation.relations)
      (leftAfter : StringWord.Word.LeftCohookDeletion L E),
      IsRightAlmostSplit
        (StringWord.Word.doubleCohookDeletionMaximalFiniteShortComplex
          leftAfter rightDeletion P.monomial).g) ∨
      (leftDeletion.steps + rightDeletion.steps = C.length + 2 ∧
        StringWord.signedPathSigns C.path =
          List.replicate rightDeletion.cohook.tail.steps false ++
            List.replicate leftDeletion.cohook.tail.steps true) := by
  rcases StringWord.Word.cohookDeletion_nesting_or_overlap
      leftDeletion rightDeletion with hnested | hoverlap
  · rcases hnested with ⟨E, ⟨leftAfter⟩⟩
    exact Or.inl ⟨E, leftAfter,
      P.doubleCohookDeletionMaximalFiniteShortComplex_isRightAlmostSplit
        S V leftAfter rightDeletion⟩
  · exact Or.inr hoverlap

end StringPresentation
end MagnitudeConjecture.BoundQuiver
