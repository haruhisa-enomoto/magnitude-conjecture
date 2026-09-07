import MagnitudeConjecture.Algebra.StringFiniteBoundaryAlmostSplit
import MagnitudeConjecture.Algebra.StringPeakWedgeRepresentable
import MagnitudeConjecture.CategoryTheory.AlmostSplitMultiplicity

/-!
# Arity bounds for literal string almost-split sequences

The Butler--Ringel boundary complexes have either one literal string in the
middle or a binary biproduct of literal strings.  This file records their
displayed indecomposable decompositions and packages the resulting minimal
right almost-split maps with the uniform bound two.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringWord.Word

/-- A literal finite string module, displayed as its one indecomposable
summand. -/
def finiteRightModuleSingletonDecomposition
    (P : StringPresentation k A Q)
    (C : Word P.toPresentation.relations) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (C.finiteRightModule P.monomial) :=
  MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
    _ (C.finiteRightModule_indecomposable P.monomial)

/-- A binary biproduct of literal finite string modules, displayed as its
two indecomposable summands. -/
def finiteRightModuleBiprodDecomposition
    (P : StringPresentation k A Q)
    (C D : Word P.toPresentation.relations) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (C.finiteRightModule P.monomial ⊞ D.finiteRightModule P.monomial) :=
  (finiteRightModuleSingletonDecomposition P C).biprod
    (finiteRightModuleSingletonDecomposition P D)

omit [IsAlgClosed k] in
@[simp]
theorem finiteRightModuleSingletonDecomposition_n
    (P : StringPresentation k A Q)
    (C : Word P.toPresentation.relations) :
    (finiteRightModuleSingletonDecomposition P C).n = 1 := rfl

omit [IsAlgClosed k] in
@[simp]
theorem finiteRightModuleBiprodDecomposition_n
    (P : StringPresentation k A Q)
    (C D : Word P.toPresentation.relations) :
    (finiteRightModuleBiprodDecomposition P C D).n = 2 := by
  simp [finiteRightModuleBiprodDecomposition,
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.biprod]

/-- A positive two-hook boundary square gives a minimal right almost-split
map whose source has two displayed string summands. -/
def twoHookMaximalFiniteRightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C rightResult : Word P.toPresentation.relations}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString P.toPresentation.relations
      (twoHookPath right left)) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 2 := by
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let sequence := twoHookMaximalFiniteShortComplex
    right left hpath P.monomial
  let d := finiteRightModuleBiprodDecomposition P left.result rightResult
  let corner := (twoHookMaximalSquare right left hpath).corner
  letI : IsLocalRing (End sequence.X₁) := by
    change IsLocalRing (End (corner.finiteRightModule P.monomial))
    exact finiteDimensionalModule_end_isLocalRing k _
      (corner.finiteRightModule_indecomposable P.monomial)
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.rightAlmostSplitDecompositionBound
      (twoHookMaximalFiniteShortComplex_shortExact S right left hpath) d
        (P.twoHookMaximalFiniteShortComplex_isRightAlmostSplit
          S V right left hpath) (by simp [d])

omit [IsAlgClosed k] in
/-- The unary pure-positive boundary complex gives a minimal right
almost-split map with one displayed string summand. -/
def purePositiveLeftHookResultPeakFiniteRightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C : Word P.toPresentation.relations}
    (hpure : C.IsPurePositive P.toPresentation.admissible)
    (left : LeftHookExtension C)
    (hresultPeak : left.result.StartsOnPeak) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 1 := by
  let data := left.purePositiveKernelDataOfResultPeak
    P.toPresentation.admissible hpure hresultPeak
  let sequence := left.purePositiveResultPeakFiniteShortComplex
    P.toPresentation.admissible hpure hresultPeak P.monomial
  let d := finiteRightModuleSingletonDecomposition P left.result
  letI : IsLocalRing (End sequence.X₁) := by
    change IsLocalRing (End (data.kernel.finiteRightModule P.monomial))
    exact finiteDimensionalModule_end_isLocalRing k _
      (data.kernel.finiteRightModule_indecomposable P.monomial)
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.rightAlmostSplitDecompositionBound
      (left.purePositiveResultPeakFiniteShortComplex_shortExact
        P.toPresentation.admissible hpure hresultPeak P.monomial) d
          (P.purePositiveLeftHookResultPeakFiniteShortComplex_isRightAlmostSplit
            S V hpure left hresultPeak) (by simp [d])

omit [IsAlgClosed k] in
/-- The usual pure-positive endpoint hypothesis specializes the unary
result-peak witness. -/
def purePositiveLeftHookFiniteRightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C : Word P.toPresentation.relations}
    (hpure : C.IsPurePositive P.toPresentation.admissible)
    (hstart : C.StartsOnPeak) (left : LeftHookExtension C) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 1 :=
  purePositiveLeftHookResultPeakFiniteRightAlmostSplitDecompositionBound
    P S V hpure left (left.result_startsOnPeak_of_startsOnPeak hstart)

omit [IsAlgClosed k] in
/-- The reversed pure-negative unary sequence has the same one-summand
middle bound after returning its endpoint to the original word. -/
def pureNegativeRightHookReverseFiniteRightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C D : Word P.toPresentation.relations}
    (hpure : C.IsPureNegative P.toPresentation.admissible)
    (hend : C.EndsOnPeak) (right : HookExtension C D) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 1 :=
  MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound.postcompIso
    (purePositiveLeftHookFiniteRightAlmostSplitDecompositionBound
      P S V hpure hend right.toReverseLeftHook)
    C.finiteReverseRightModuleIso.symm

/-- A left cohook deletion and a right hook give a two-summand minimal
right almost-split source at the original string. -/
def leftCohookDeletionRightHookFiniteRightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C D corner : Word P.toPresentation.relations}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 2 := by
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let square := leftCohookDeletionRightHookMaximalSquare deletion right
  let sequence := leftCohookDeletionRightHookMaximalFiniteShortComplex
    deletion right P.monomial
  let d := finiteRightModuleBiprodDecomposition P D square.corner
  letI : IsLocalRing (End sequence.X₁) := by
    change IsLocalRing (End (square.rightResult.finiteRightModule P.monomial))
    exact finiteDimensionalModule_end_isLocalRing k _
      (square.rightResult.finiteRightModule_indecomposable P.monomial)
  let w :
      MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
        sequence.X₃ 2 :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.rightAlmostSplitDecompositionBound
      (leftCohookDeletionRightHookMaximalFiniteShortComplex_shortExact
        S deletion right) d
      (P.leftCohookDeletionRightHookMaximalFiniteShortComplex_isRightAlmostSplit
        S V deletion right) (by simp [d])
  let leftCohook := deletion.toLeftCohookExtension
  have hleft : leftCohook.result = C :=
    deletion.toLeftCohookExtension_result
  let e : sequence.X₃ ≅ C.finiteRightModule P.monomial := by
    change leftCohook.result.finiteRightModule P.monomial ≅
      C.finiteRightModule P.monomial
    exact eqToIso (congrArg
      (fun W : Word P.toPresentation.relations ↦
        W.finiteRightModule P.monomial) hleft)
  exact
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound.postcompIso
      w e

/-- A right cohook deletion and a left hook give the reversed two-summand
minimal right almost-split source at the original string. -/
def rightCohookDeletionLeftHookReverseFiniteRightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C D : Word P.toPresentation.relations}
    (deletion : CohookDeletion C D) (left : LeftHookExtension C) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 2 := by
  let reverseDeletion := deletion.toReverseLeftCohookDeletion
  let square := leftCohookDeletionRightHookMaximalSquare
    reverseDeletion left.hook
  let sequence := leftCohookDeletionRightHookMaximalFiniteShortComplex
    reverseDeletion left.hook P.monomial
  let d := finiteRightModuleBiprodDecomposition P D.reverse square.corner
  letI : IsLocalRing (End sequence.X₁) := by
    change IsLocalRing (End (square.rightResult.finiteRightModule P.monomial))
    exact finiteDimensionalModule_end_isLocalRing k _
      (square.rightResult.finiteRightModule_indecomposable P.monomial)
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let w :
      MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
        sequence.X₃ 2 :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.rightAlmostSplitDecompositionBound
      (leftCohookDeletionRightHookMaximalFiniteShortComplex_shortExact
        S reverseDeletion left.hook) d
      (P.leftCohookDeletionRightHookMaximalFiniteShortComplex_isRightAlmostSplit
        S V reverseDeletion left.hook) (by simp [d])
  exact
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound.postcompIso
      w (P.rightCohookDeletionLeftHookReverseTargetIso deletion left)

/-- Two compatible cohook deletions give a two-summand minimal right
almost-split source at the original string. -/
def doubleCohookDeletionFiniteRightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C L D : Word P.toPresentation.relations}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 2 := by
  let cornerRight := doubleCohookDeletionCornerRightCohook
    leftDeletion rightDeletion
  let square := doubleCohookMaximalSquare
    leftDeletion.toLeftCohookExtension cornerRight
  let sequence := doubleCohookDeletionMaximalFiniteShortComplex
    leftDeletion rightDeletion P.monomial
  let d := finiteRightModuleBiprodDecomposition P
    square.left.result square.rightResult
  letI : IsLocalRing (End sequence.X₁) := by
    change IsLocalRing (End (D.finiteRightModule P.monomial))
    exact finiteDimensionalModule_end_isLocalRing k _
      (D.finiteRightModule_indecomposable P.monomial)
  letI : Finite (StringWord.DetectorIndex S) :=
    StringWord.DetectorIndex.finite_of_finiteIndecomposableSkeleton V
  letI : Fintype (StringWord.DetectorIndex S) := Fintype.ofFinite _
  let w :
      MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
        sequence.X₃ 2 :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.rightAlmostSplitDecompositionBound
      (doubleCohookDeletionMaximalFiniteShortComplex_shortExact
        S leftDeletion rightDeletion) d
      (P.doubleCohookDeletionMaximalFiniteShortComplex_isRightAlmostSplit
        S V leftDeletion rightDeletion) (by simp [d])
  have hcorner : square.corner = C :=
    doubleCohookMaximalSquare_corner
      leftDeletion.toLeftCohookExtension cornerRight
  let e : sequence.X₃ ≅ C.finiteRightModule P.monomial := by
    change square.corner.finiteRightModule P.monomial ≅
      C.finiteRightModule P.monomial
    exact eqToIso (congrArg
      (fun W : Word P.toPresentation.relations ↦
        W.finiteRightModule P.monomial) hcorner)
  exact
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound.postcompIso
      w e

/-- Every nonprojective literal finite string module admits a minimal right
almost-split map whose source is displayed as at most two indecomposable
literal string modules. -/
theorem exists_finiteRightAlmostSplitDecompositionBound_two_of_not_projective
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    (C : Word P.toPresentation.relations)
    (hnonprojective : ¬ Projective (C.finiteRightModule P.monomial)) :
    Nonempty
      (MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
        (C.finiteRightModule P.monomial) 2) := by
  rcases exists_hook_or_cohookDeletion_or_isPurePositive_startsOnPeak
      P.toPresentation.admissible C with
    ⟨rightResult, ⟨right⟩⟩ | ⟨rightBase, ⟨rightDeletion⟩⟩ |
      ⟨hpurePositive, hstart⟩
  · rcases exists_leftHook_or_leftCohookDeletion_or_isPureNegative_endsOnPeak
        P.toPresentation.admissible C with
      hleft | ⟨leftBase, ⟨leftDeletion⟩⟩ | ⟨hpureNegative, hend⟩
    · obtain ⟨left⟩ := hleft
      by_cases hlength : 0 < C.length
      · exact ⟨twoHookMaximalFiniteRightAlmostSplitDecompositionBound
          P S V right left (twoHookPath_isString right left hlength)⟩
      · have hzero : C.length = 0 := Nat.eq_zero_of_not_pos hlength
        have hpure : C.IsPurePositive P.toPresentation.admissible :=
          isPurePositive_of_length_eq_zero
            P.toPresentation.admissible C hzero
        by_cases hresultPeak : left.result.StartsOnPeak
        · exact
            ⟨(purePositiveLeftHookResultPeakFiniteRightAlmostSplitDecompositionBound
              P S V hpure left hresultPeak).mono (by omega)⟩
        · obtain ⟨newRightResult, newRight, hpath⟩ :=
            exists_hook_twoHookPath_isString_of_leftHookResult_not_startsOnPeak
              P.toPresentation.admissible left hresultPeak
          exact ⟨twoHookMaximalFiniteRightAlmostSplitDecompositionBound
            P S V newRight left hpath⟩
    · exact
        ⟨leftCohookDeletionRightHookFiniteRightAlmostSplitDecompositionBound
          P S V leftDeletion right⟩
    · exact
        ⟨(pureNegativeRightHookReverseFiniteRightAlmostSplitDecompositionBound
          P S V hpureNegative hend right).mono (by omega)⟩
  · rcases exists_leftHook_or_leftCohookDeletion_or_isPureNegative_endsOnPeak
        P.toPresentation.admissible C with
      hleft | ⟨leftBase, ⟨leftDeletion⟩⟩ | ⟨hpureNegative, hend⟩
    · obtain ⟨left⟩ := hleft
      exact
        ⟨rightCohookDeletionLeftHookReverseFiniteRightAlmostSplitDecompositionBound
          P S V rightDeletion left⟩
    · rcases cohookDeletion_nesting_or_overlap
          leftDeletion rightDeletion with
        ⟨cornerBase, ⟨leftAfter⟩⟩ | ⟨hoverlap, _⟩
      · exact ⟨doubleCohookDeletionFiniteRightAlmostSplitDecompositionBound
          P S V leftAfter rightDeletion⟩
      · exfalso
        apply hnonprojective
        apply finiteRightModule_projective_of_overlappingCohookDeletions
          P leftDeletion rightDeletion
        omega
    · obtain ⟨newRightResult, ⟨newRight⟩⟩ :=
          exists_hook_of_isPureNegative_of_endsOnPeak_of_not_projective
            P hpureNegative hend hnonprojective
      exact
        ⟨(pureNegativeRightHookReverseFiniteRightAlmostSplitDecompositionBound
          P S V hpureNegative hend newRight).mono (by omega)⟩
  · obtain ⟨left⟩ :=
      exists_leftHook_of_isPurePositive_of_startsOnPeak_of_not_projective
        P hpurePositive hstart hnonprojective
    exact ⟨(purePositiveLeftHookFiniteRightAlmostSplitDecompositionBound
      P S V hpurePositive hstart left).mono (by omega)⟩

end StringWord.Word
end MagnitudeConjecture.BoundQuiver
