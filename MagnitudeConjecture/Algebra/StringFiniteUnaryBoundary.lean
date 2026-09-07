import MagnitudeConjecture.Algebra.StringFiniteBoundaryArity
import MagnitudeConjecture.Algebra.StringHookKernelDeterminism

/-!
# Literal one-middle Butler--Ringel boundaries

The exhaustive endpoint analysis for a nonprojective string has five binary
boundary shapes and two unary shapes, exchanged by word reversal.  Comparing
their displayed decompositions with an arbitrary one-summand minimal right
almost-split source eliminates every binary shape.  Thus a literal
one-middle mesh is represented by a pure one-sided hook boundary.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringWord.Word

/-- The two literal unary Butler--Ringel boundary shapes at a word.  The
negative case is stored before reversal, so its central arrow remains an
ordinary displayed arrow of the original quiver. -/
inductive FiniteUnaryBoundary
    (P : StringPresentation k A Q)
    (C : Word P.toPresentation.relations) : Type u
  | positive
      (hpure : C.IsPurePositive P.toPresentation.admissible)
      (left : LeftHookExtension C)
      (hresultPeak : left.result.StartsOnPeak)
  | negative
      (hpure : C.IsPureNegative P.toPresentation.admissible)
      (hend : C.EndsOnPeak)
      {D : Word P.toPresentation.relations}
      (right : HookExtension C D)

/-- The central displayed arrow indexing a unary boundary. -/
def FiniteUnaryBoundary.displayedArrow
    {P : StringPresentation k A Q}
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) : Σ y : Q, Σ x : Q, x ⟶ y :=
  match B with
  | .positive _ left _ =>
      ⟨left.hook.vertex, C.source, left.hook.arrow⟩
  | .negative _ _ right =>
      ⟨right.vertex, C.target, right.arrow⟩

/-- A literal unary boundary supplies a minimal right almost-split map with
exactly one displayed middle summand. -/
def FiniteUnaryBoundary.rightAlmostSplitDecompositionBound
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) :
    MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
      (C.finiteRightModule P.monomial) 1 :=
  match B with
  | .positive hpure left hresultPeak =>
      purePositiveLeftHookResultPeakFiniteRightAlmostSplitDecompositionBound
        P S V hpure left hresultPeak
  | .negative hpure hend right =>
      pureNegativeRightHookReverseFiniteRightAlmostSplitDecompositionBound
        P S V hpure hend right

/-- The literal kernel word at the left end of a unary boundary sequence. -/
def FiniteUnaryBoundary.kernelWord
    {P : StringPresentation k A Q}
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) : Word P.toPresentation.relations :=
  match B with
  | .positive hpure left hresultPeak =>
      (left.purePositiveKernelDataOfResultPeak
        P.toPresentation.admissible hpure hresultPeak).kernel
  | .negative hpure hend right =>
      ((right.toReverseLeftHook).purePositiveKernelData
        P.toPresentation.admissible hpure hend).kernel

/-- The underlying short complex before the negative case is transported
back across the canonical reversal isomorphism of its endpoint. -/
def FiniteUnaryBoundary.rawShortComplex
    {P : StringPresentation k A Q}
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) :
    ShortComplex (CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :=
  match B with
  | .positive hpure left hresultPeak =>
      left.purePositiveResultPeakFiniteShortComplex
        P.toPresentation.admissible hpure hresultPeak P.monomial
  | .negative hpure hend right =>
      (right.toReverseLeftHook).purePositiveFiniteShortComplex
        P.toPresentation.admissible hpure hend P.monomial

omit [IsAlgClosed k] in
@[simp]
theorem FiniteUnaryBoundary.rawShortComplex_X₁
    {P : StringPresentation k A Q}
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) :
    B.rawShortComplex.X₁ = B.kernelWord.finiteRightModule P.monomial := by
  cases B <;> rfl

/-- The endpoint of the raw unary complex is the original word in the
positive case and its reversal in the negative case. -/
def FiniteUnaryBoundary.endpointIso
    {P : StringPresentation k A Q}
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) :
    B.rawShortComplex.X₃ ≅ C.finiteRightModule P.monomial :=
  match B with
  | .positive _ _ _ => Iso.refl _
  | .negative _ _ _ => C.finiteReverseRightModuleIso.symm

omit [IsAlgClosed k] in
/-- The raw literal unary boundary complex is short exact. -/
theorem FiniteUnaryBoundary.rawShortComplex_shortExact
    {P : StringPresentation k A Q}
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) : B.rawShortComplex.ShortExact := by
  cases B with
  | positive hpure left hresultPeak =>
      exact left.purePositiveResultPeakFiniteShortComplex_shortExact
        P.toPresentation.admissible hpure hresultPeak P.monomial
  | negative hpure hend right =>
      exact (right.toReverseLeftHook).purePositiveFiniteShortComplex_shortExact
        P.toPresentation.admissible hpure hend P.monomial

omit [IsAlgClosed k] in
/-- The raw terminal map of a unary boundary is right almost split. -/
theorem FiniteUnaryBoundary.rawShortComplex_isRightAlmostSplit
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) :
    IsRightAlmostSplit B.rawShortComplex.g := by
  cases B with
  | positive hpure left hresultPeak =>
      exact P.purePositiveLeftHookResultPeakFiniteShortComplex_isRightAlmostSplit
        S V hpure left hresultPeak
  | negative hpure hend right =>
      exact P.purePositiveLeftHookFiniteShortComplex_isRightAlmostSplit
        S V hpure hend right.toReverseLeftHook

omit [IsAlgClosed k] in
/-- The raw terminal map of a unary boundary is right minimal. -/
theorem FiniteUnaryBoundary.rawShortComplex_isRightMinimal
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) :
    IsRightMinimal B.rawShortComplex.g := by
  letI : IsLocalRing (End B.rawShortComplex.X₁) := by
    rw [B.rawShortComplex_X₁]
    exact finiteDimensionalModule_end_isLocalRing k _
      (B.kernelWord.finiteRightModule_indecomposable P.monomial)
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_local_end
      B.rawShortComplex_shortExact
      (B.rawShortComplex_isRightAlmostSplit P S V).not_isSplitEpi

/-- If a displayed minimal right almost-split source at a nonprojective
literal string has one indecomposable summand, the exhaustive endpoint
classification leaves only a unary Butler--Ringel boundary. -/
theorem nonempty_finiteUnaryBoundary_of_decomposition_n_eq_one
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (V : StringWord.DetectorIndex.FiniteIndecomposableSkeleton (P := P))
    (C : Word P.toPresentation.relations)
    (hnonprojective : ¬ Projective (C.finiteRightModule P.monomial))
    {E : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k}
    (f : E ⟶ C.finiteRightModule P.monomial)
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition E)
    (hlocal : ∀ i, IsLocalRing (End (d.summand i)))
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f)
    (hd : d.n = 1) : Nonempty (FiniteUnaryBoundary P C) := by
  let binaryContradiction
      (w : MagnitudeConjecture.CategoryTheory.RightAlmostSplitDecompositionBound
        (C.finiteRightModule P.monomial) 2)
      (hw : w.decomposition.n = 2) : False := by
    have hn := d.n_eq_of_minimalRightAlmostSplit w.decomposition hlocal
      hf hfmin w.rightAlmostSplit w.rightMinimal
    omega
  rcases exists_hook_or_cohookDeletion_or_isPurePositive_startsOnPeak
      P.toPresentation.admissible C with
    ⟨rightResult, ⟨right⟩⟩ | ⟨rightBase, ⟨rightDeletion⟩⟩ |
      ⟨hpurePositive, hstart⟩
  · rcases exists_leftHook_or_leftCohookDeletion_or_isPureNegative_endsOnPeak
        P.toPresentation.admissible C with
      hleft | ⟨leftBase, ⟨leftDeletion⟩⟩ | ⟨hpureNegative, hend⟩
    · obtain ⟨left⟩ := hleft
      by_cases hlength : 0 < C.length
      · let w := twoHookMaximalFiniteRightAlmostSplitDecompositionBound
          P S V right left (twoHookPath_isString right left hlength)
        exact (binaryContradiction w rfl).elim
      · have hzero : C.length = 0 := Nat.eq_zero_of_not_pos hlength
        have hpure : C.IsPurePositive P.toPresentation.admissible :=
          isPurePositive_of_length_eq_zero
            P.toPresentation.admissible C hzero
        by_cases hresultPeak : left.result.StartsOnPeak
        · exact ⟨.positive hpure left hresultPeak⟩
        · obtain ⟨newRightResult, newRight, hpath⟩ :=
            exists_hook_twoHookPath_isString_of_leftHookResult_not_startsOnPeak
              P.toPresentation.admissible left hresultPeak
          let w := twoHookMaximalFiniteRightAlmostSplitDecompositionBound
            P S V newRight left hpath
          exact (binaryContradiction w rfl).elim
    · let w := leftCohookDeletionRightHookFiniteRightAlmostSplitDecompositionBound
        P S V leftDeletion right
      exact (binaryContradiction w rfl).elim
    · exact ⟨.negative hpureNegative hend right⟩
  · rcases exists_leftHook_or_leftCohookDeletion_or_isPureNegative_endsOnPeak
        P.toPresentation.admissible C with
      hleft | ⟨leftBase, ⟨leftDeletion⟩⟩ | ⟨hpureNegative, hend⟩
    · obtain ⟨left⟩ := hleft
      let w :=
        rightCohookDeletionLeftHookReverseFiniteRightAlmostSplitDecompositionBound
          P S V rightDeletion left
      exact (binaryContradiction w rfl).elim
    · rcases cohookDeletion_nesting_or_overlap
          leftDeletion rightDeletion with
        ⟨cornerBase, ⟨leftAfter⟩⟩ | ⟨hoverlap, _⟩
      · let w := doubleCohookDeletionFiniteRightAlmostSplitDecompositionBound
          P S V leftAfter rightDeletion
        exact (binaryContradiction w rfl).elim
      · exfalso
        apply hnonprojective
        apply finiteRightModule_projective_of_overlappingCohookDeletions
          P leftDeletion rightDeletion
        omega
    · obtain ⟨newRightResult, ⟨newRight⟩⟩ :=
          exists_hook_of_isPureNegative_of_endsOnPeak_of_not_projective
            P hpureNegative hend hnonprojective
      exact ⟨.negative hpureNegative hend newRight⟩
  · obtain ⟨left⟩ :=
      exists_leftHook_of_isPurePositive_of_startsOnPeak_of_not_projective
        P hpurePositive hstart hnonprojective
    exact ⟨.positive hpurePositive left
      (left.result_startsOnPeak_of_startsOnPeak hstart)⟩

omit [IsAlgClosed k] in
/-- The literal kernel of a unary boundary depends only on its displayed
central arrow. -/
theorem FiniteUnaryBoundary.kernelWord_eq_canonicalKernelWord
    (P : StringPresentation k A Q)
    {C : Word P.toPresentation.relations}
    (B : FiniteUnaryBoundary P C) :
    B.kernelWord =
      HookExtension.canonicalKernelWord P.toSpecialBiserialPresentation
        B.displayedArrow := by
  cases B with
  | positive hpure left hresultPeak =>
      have hkernel :
          (left.purePositiveKernelDataOfResultPeak
            P.toPresentation.admissible hpure hresultPeak).kernel =
            left.hook.tail.positiveWord P.toPresentation.admissible := by
        apply Word.ext
        · rfl
        · rfl
        · exact heq_of_eq
            left.hook.tail.suffixPath_reverse_eq_positivePath_ordinaryPath
      exact hkernel.trans
        (left.hook.tail_positiveWord_eq_canonicalKernelWord
          P.toSpecialBiserialPresentation)
  | negative hpure hend right =>
      let left := right.toReverseLeftHook
      have hkernel :
          (left.purePositiveKernelData
            P.toPresentation.admissible hpure hend).kernel =
            left.hook.tail.positiveWord P.toPresentation.admissible := by
        apply Word.ext
        · rfl
        · rfl
        · exact heq_of_eq
            left.hook.tail.suffixPath_reverse_eq_positivePath_ordinaryPath
      have hcanonical :=
        left.hook.tail_positiveWord_eq_canonicalKernelWord
          P.toSpecialBiserialPresentation
      have hboundary :
          (⟨left.hook.vertex, C.reverse.reverse.target, left.hook.arrow⟩ :
              Σ y : Q, Σ x : Q, x ⟶ y) =
            ⟨right.vertex, C.target, right.arrow⟩ := by
        simpa only [left, HookExtension.toReverseLeftHook] using
          (HookExtension.displayedArrow_transport_source
            (reverse_reverse P.toPresentation.relations C).symm right)
      rw [hboundary] at hcanonical
      exact hkernel.trans hcanonical

end StringWord.Word
end MagnitudeConjecture.BoundQuiver
