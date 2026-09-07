import MagnitudeConjecture.Algebra.StringFiniteModuleClassification
import MagnitudeConjecture.Algebra.StringDoubleCohookSquare
import MagnitudeConjecture.Algebra.StringReducedReverse

/-!
# Repeated middle words for the negative cohook square

The finite detector classification reduces an isomorphism between the two
middle string modules to literal equality or reversal.  In the reversal
branch, cancellation of equally long cohook prefixes shows that the original
word has length zero.  The reverse double-cohook path then contains an
adjacent inverse pair, contradicting its reducedness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

theorem not_isReduced_positiveArrow_comp_zero_comp_negativeArrow_of_letter_eq
    {a b c d : Q} (leftArrow : a ⟶ b) (middle : SignedPath b c)
    (rightArrow : d ⟶ c) (hmiddle : middle.length = 0)
    (hletter : signedArrowLetter (positiveArrow leftArrow) =
      signedArrowLetter (positiveArrow rightArrow)) :
    ¬ IsReduced ((positiveArrow leftArrow).toPath.comp
      (middle.comp (negativeArrow rightArrow).toPath)) := by
  intro hred
  have hgenerator := congrArg Prod.fst hletter
  cases hgenerator
  have hmiddleNil := middle.eq_nil_of_length_zero hmiddle
  subst middle
  exact hred (positiveArrow leftArrow) (isContiguousSubpath_refl _)

/-- The explicit path of a left cohook, ending at the old right endpoint. -/
private def leftCohookBasePath {D : Word R} (left : LeftCohookExtension D) :
    SignedPath left.reverseResult.target D.target :=
  left.cohook.tail.toRightExtension.suffixPath.reverse.comp
    ((positiveArrow left.cohook.arrow).toPath.comp D.path)

private theorem leftCohookBasePath_isString {D : Word R}
    (left : LeftCohookExtension D) :
    IsString R (leftCohookBasePath left) := by
  have hforward :=
    left.cohook.toNegativeBoundaryExtension.toRightExtension.comp_suffixPath_isString
  have hreverse :=
    (isString_reverse_iff R
      (D.reverse.path.comp
        left.cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath)).2
      hforward
  have hreverseReverse : D.path.reverse.reverse = D.path :=
    @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ D.path
  simp only [NegativeBoundaryExtension.toRightExtension_suffixPath,
    CohookExtension.toNegativeBoundaryExtension, reverse_path,
    Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    reverse_negativeArrow, Quiver.Path.comp_assoc] at hreverse
  have hpathEq :
      left.cohook.tail.toRightExtension.suffixPath.reverse.comp
          ((positiveArrow left.cohook.arrow).toPath.comp
            D.path.reverse.reverse) =
        left.cohook.tail.toRightExtension.suffixPath.reverse.comp
          ((positiveArrow left.cohook.arrow).toPath.comp D.path) :=
    congrArg
      (fun p : SignedPath D.source D.target ↦
        left.cohook.tail.toRightExtension.suffixPath.reverse.comp
          ((positiveArrow left.cohook.arrow).toPath.comp p))
      hreverseReverse
  change IsString R
    (left.cohook.tail.toRightExtension.suffixPath.reverse.comp
      ((positiveArrow left.cohook.arrow).toPath.comp D.path))
  exact hpathEq ▸ hreverse

private def leftCohookBaseWord {D : Word R}
    (left : LeftCohookExtension D) : Word R :=
  ofStringPath (leftCohookBasePath left) (leftCohookBasePath_isString left)

private theorem leftCohookBaseWord_eq_result {D : Word R}
    (left : LeftCohookExtension D) :
    leftCohookBaseWord left = left.result := by
  let extension :=
    left.cohook.toNegativeBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hreverseFactor := congrArg Quiver.Path.reverse hfactor
  rw [path_reverse_cast] at hreverseFactor
  have hsuffix :=
    left.cohook.toNegativeBoundaryExtension.toRightExtension_suffixPath
  change extension.suffixPath =
    (negativeArrow left.cohook.arrow).toPath.comp
      left.cohook.tail.toRightExtension.suffixPath at hsuffix
  rw [hsuffix] at hreverseFactor
  simp only [reverse_path, Quiver.Path.reverse_comp,
    Quiver.Path.reverse_toPath, reverse_negativeArrow,
    Quiver.Path.comp_assoc] at hreverseFactor
  have hreverseReverse : D.path.reverse.reverse = D.path :=
    @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ D.path
  have hpathCast :
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        left.reverseResult.target left.reverseResult.source
        left.reverseResult.target D.target rfl extension.source_eq
        left.reverseResult.path.reverse) = leftCohookBasePath left := by
    calc
      _ = left.cohook.tail.toRightExtension.suffixPath.reverse.comp
          ((positiveArrow left.cohook.arrow).toPath.comp
            D.path.reverse.reverse) := hreverseFactor
      _ = leftCohookBasePath left := by
        exact congrArg
          (fun p : SignedPath D.source D.target ↦
            left.cohook.tail.toRightExtension.suffixPath.reverse.comp
              ((positiveArrow left.cohook.arrow).toPath.comp p))
          hreverseReverse
  apply Word.ext
  · rfl
  · exact extension.source_eq.symm
  · exact HEq.trans (heq_of_eq hpathCast.symm)
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _ rfl extension.source_eq
        left.reverseResult.path.reverse)

private def rightCohookReverseBasePath {D rightResult : Word R}
    (right : CohookExtension D rightResult) :
    SignedPath rightResult.target D.source :=
  (D.path.comp ((negativeArrow right.arrow).toPath.comp
    right.tail.toRightExtension.suffixPath)).reverse

private theorem rightCohookReverseBasePath_isString
    {D rightResult : Word R} (right : CohookExtension D rightResult) :
    IsString R (rightCohookReverseBasePath right) := by
  exact (isString_reverse_iff R
    (D.path.comp ((negativeArrow right.arrow).toPath.comp
      right.tail.toRightExtension.suffixPath))).2 (by
        simpa only [NegativeBoundaryExtension.toRightExtension_suffixPath,
          CohookExtension.toNegativeBoundaryExtension] using
          right.toNegativeBoundaryExtension.toRightExtension.comp_suffixPath_isString)

private theorem rightCohookReverseBasePath_eq
    {D rightResult : Word R} (right : CohookExtension D rightResult) :
    rightCohookReverseBasePath right =
      right.tail.toRightExtension.suffixPath.reverse.comp
        ((positiveArrow right.arrow).toPath.comp D.path.reverse) := by
  simp only [rightCohookReverseBasePath, Quiver.Path.reverse_comp,
    Quiver.Path.reverse_toPath, reverse_negativeArrow,
    Quiver.Path.comp_assoc]
  rfl

private def rightCohookReverseBaseWord {D rightResult : Word R}
    (right : CohookExtension D rightResult) : Word R :=
  ofStringPath (rightCohookReverseBasePath right)
    (rightCohookReverseBasePath_isString right)

private theorem rightCohookReverseBaseWord_eq_reverseResult
    {D rightResult : Word R} (right : CohookExtension D rightResult) :
    rightCohookReverseBaseWord right = rightResult.reverse := by
  let extension := right.toNegativeBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hreverseFactor := congrArg Quiver.Path.reverse hfactor
  rw [path_reverse_cast] at hreverseFactor
  have hsuffix := right.toNegativeBoundaryExtension.toRightExtension_suffixPath
  change extension.suffixPath =
    (negativeArrow right.arrow).toPath.comp
      right.tail.toRightExtension.suffixPath at hsuffix
  rw [hsuffix] at hreverseFactor
  simp only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    reverse_negativeArrow, Quiver.Path.comp_assoc] at hreverseFactor
  have hpathCast :
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        rightResult.target rightResult.source rightResult.target D.source
        rfl extension.source_eq rightResult.path.reverse) =
        rightCohookReverseBasePath right := by
    exact hreverseFactor.trans (rightCohookReverseBasePath_eq right).symm
  apply Word.ext
  · rfl
  · exact extension.source_eq.symm
  · exact HEq.trans (heq_of_eq hpathCast.symm)
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _ rfl extension.source_eq
        rightResult.path.reverse)

/-- If a left-cohook result is the reverse of a right-cohook result, then the
base has length zero and the two boundary letters coincide. -/
theorem length_eq_zero_and_boundaryLetter_eq_of_leftCohook_result_eq_reverse_rightCohook_result
    {D rightResult : Word R}
    (right : CohookExtension D rightResult)
    (left : LeftCohookExtension D)
    (hmiddle : left.result = rightResult.reverse) :
    D.length = 0 ∧
      signedArrowLetter (positiveArrow left.cohook.arrow) =
        signedArrowLetter (positiveArrow right.arrow) := by
  have hbaseWords : leftCohookBaseWord left =
      rightCohookReverseBaseWord right := by
    rw [leftCohookBaseWord_eq_result,
      rightCohookReverseBaseWord_eq_reverseResult]
    exact hmiddle
  have hpathWords := congrArg
    (fun W : Word R ↦ signedPathWord W.path) hbaseWords
  change signedPathWord (leftCohookBasePath left) =
    signedPathWord (rightCohookReverseBasePath right) at hpathWords
  rw [rightCohookReverseBasePath_eq right] at hpathWords
  simp only [leftCohookBasePath, signedPathWord_comp,
    signedPathWord_reverse] at hpathWords
  have hleftMiddle :
      signedPathWord
          ((positiveArrow left.cohook.arrow).toPath.comp D.path) =
        signedPathWord D.path ++
          signedPathWord (positiveArrow left.cohook.arrow).toPath :=
    signedPathWord_comp _ _
  have hrightMiddle :
      signedPathWord
          ((positiveArrow right.arrow).toPath.comp D.path.reverse) =
        signedPathWord D.path.reverse ++
          signedPathWord (positiveArrow right.arrow).toPath :=
    signedPathWord_comp _ _
  have hpathWords' :
      (signedPathWord D.path ++
          signedPathWord (positiveArrow left.cohook.arrow).toPath) ++
          FreeGroup.invRev
            (signedPathWord left.cohook.tail.toRightExtension.suffixPath) =
        (signedPathWord D.path.reverse ++
          signedPathWord (positiveArrow right.arrow).toPath) ++
          FreeGroup.invRev
            (signedPathWord right.tail.toRightExtension.suffixPath) := by
    calc
      _ = signedPathWord
            ((positiveArrow left.cohook.arrow).toPath.comp D.path) ++
          FreeGroup.invRev
            (signedPathWord left.cohook.tail.toRightExtension.suffixPath) :=
        congrArg
          (fun w ↦ w ++ FreeGroup.invRev
            (signedPathWord left.cohook.tail.toRightExtension.suffixPath))
          hleftMiddle.symm
      _ = _ := hpathWords
      _ = _ := congrArg
        (fun w ↦ w ++ FreeGroup.invRev
          (signedPathWord right.tail.toRightExtension.suffixPath))
        hrightMiddle
  simp only [signedPathWord_toPath, signedPathWord_reverse] at hpathWords'
  have htakes := congrArg (List.take D.length) hpathWords'
  have hwordLength : D.length = (signedPathWord D.path).length := by
    change D.path.length = (signedPathWord D.path).length
    exact (signedPathWord_length D.path).symm
  rw [hwordLength] at htakes
  have hreverseWord : signedPathWord D.path =
      FreeGroup.invRev (signedPathWord D.path) := by
    have htakes' :
        List.take (signedPathWord D.path).length
            (signedPathWord D.path ++
              ([signedArrowLetter (positiveArrow left.cohook.arrow)] ++
                FreeGroup.invRev
                  (signedPathWord
                    left.cohook.tail.toRightExtension.suffixPath))) =
          List.take (signedPathWord D.path).length
            (FreeGroup.invRev (signedPathWord D.path) ++
              ([signedArrowLetter (positiveArrow right.arrow)] ++
                FreeGroup.invRev
                  (signedPathWord
                    right.tail.toRightExtension.suffixPath))) := by
      simpa only [List.append_assoc] using htakes
    calc
      signedPathWord D.path =
          List.take (signedPathWord D.path).length
            (signedPathWord D.path ++
              ([signedArrowLetter (positiveArrow left.cohook.arrow)] ++
                FreeGroup.invRev
                  (signedPathWord
                    left.cohook.tail.toRightExtension.suffixPath))) :=
        (List.take_left).symm
      _ = _ := htakes'
      _ = FreeGroup.invRev (signedPathWord D.path) := by
        rw [show (signedPathWord D.path).length =
            (FreeGroup.invRev (signedPathWord D.path)).length from
          FreeGroup.invRev_length.symm]
        exact List.take_left
  have hzero := IsReduced.length_eq_zero_of_signedPathWord_eq_invRev
    D.path D.isString.1 hreverseWord
  have hDwordNil : signedPathWord D.path = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [signedPathWord_length]
    exact hzero
  have hboundaryLetter :
      signedArrowLetter (positiveArrow left.cohook.arrow) =
        signedArrowLetter (positiveArrow right.arrow) := by
    have hheads := congrArg List.head? hpathWords'
    simpa [hDwordNil, FreeGroup.invRev] using hheads
  exact ⟨hzero, hboundaryLetter⟩

/-- The reverse-oriented path obtained by adjoining maximal cohooks at both
ends of a word. -/
def twoCohookReversePath {D rightResult : Word R}
    (right : CohookExtension D rightResult)
    (left : LeftCohookExtension D) :
    SignedPath rightResult.target left.reverseResult.target :=
  right.tail.toRightExtension.suffixPath.reverse.comp
    ((positiveArrow right.arrow).toPath.comp
      (D.path.reverse.comp ((negativeArrow left.cohook.arrow).toPath.comp
        left.cohook.tail.toRightExtension.suffixPath)))

/-- A valid two-cohook corner rules out reversal of its two middle words. -/
theorem leftCohook_result_ne_reverse_rightCohook_result_of_twoCohookReversePath_isString
    {D rightResult : Word R}
    (right : CohookExtension D rightResult)
    (left : LeftCohookExtension D)
    (hpath : IsString R (twoCohookReversePath right left)) :
    left.result ≠ rightResult.reverse := by
  intro hmiddle
  obtain ⟨hzero, hboundaryLetter⟩ :=
    length_eq_zero_and_boundaryLetter_eq_of_leftCohook_result_eq_reverse_rightCohook_result
      right left hmiddle
  let central := (positiveArrow right.arrow).toPath.comp
    (D.path.reverse.comp (negativeArrow left.cohook.arrow).toPath)
  have hmiddleZero : D.path.reverse.length = 0 := by
    change D.path.length = 0 at hzero
    simpa only [length_reverse] using hzero
  have hcentralSub : IsContiguousSubpath central
      (twoCohookReversePath right left) := by
    refine ⟨right.tail.toRightExtension.suffixPath.reverse,
      left.cohook.tail.toRightExtension.suffixPath, ?_⟩
    simp only [central, twoCohookReversePath]
    calc
      _ = right.tail.toRightExtension.suffixPath.reverse.comp
          ((positiveArrow right.arrow).toPath.comp
            ((D.path.reverse.comp
              (negativeArrow left.cohook.arrow).toPath).comp
                left.cohook.tail.toRightExtension.suffixPath)) := by
        rw [Quiver.Path.comp_assoc D.path.reverse
          (negativeArrow left.cohook.arrow).toPath
          left.cohook.tail.toRightExtension.suffixPath]
        rfl
      _ = _ := congrArg
        (fun p ↦ right.tail.toRightExtension.suffixPath.reverse.comp p)
        (Quiver.Path.comp_assoc
          (positiveArrow right.arrow).toPath
          (D.path.reverse.comp (negativeArrow left.cohook.arrow).toPath)
          left.cohook.tail.toRightExtension.suffixPath).symm
  have hcentralReduced : IsReduced central :=
    IsReduced.of_contiguousSubpath hpath.1 hcentralSub
  exact
    (not_isReduced_positiveArrow_comp_zero_comp_negativeArrow_of_letter_eq
      right.arrow D.path.reverse left.cohook.arrow hmiddleZero
        hboundaryLetter.symm) hcentralReduced

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : StringPresentation k A Q}

/-- For a valid two-cohook square, isomorphism of the two middle modules
forces literal equality of their words. -/
theorem leftCohook_result_eq_of_finiteRightModule_iso_of_twoCohookReversePath_isString
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    {D rightResult : Word P.toPresentation.relations}
    (right : CohookExtension D rightResult)
    (left : LeftCohookExtension D)
    (hpath : IsString P.toPresentation.relations
      (twoCohookReversePath right left))
    (e : left.result.finiteRightModule P.monomial ≅
      rightResult.finiteRightModule P.monomial) :
    left.result = rightResult := by
  rcases DetectorIndex.eq_or_eq_reverse_of_finiteRightModule_iso
      S left.result rightResult e with hmiddle | hreverse
  · exact hmiddle
  · exact False.elim
      (leftCohook_result_ne_reverse_rightCohook_result_of_twoCohookReversePath_isString
        right left hpath hreverse)

end MagnitudeConjecture.BoundQuiver.StringWord.Word
