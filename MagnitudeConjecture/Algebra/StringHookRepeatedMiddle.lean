import MagnitudeConjecture.Algebra.StringFiniteModuleClassification
import MagnitudeConjecture.Algebra.StringHookSquare
import MagnitudeConjecture.Algebra.StringReducedReverse

/-!
# Repeated middle words for the positive hook square

The finite detector classification reduces an isomorphism between the two
middle string modules to literal equality or reversal.  In the reversal
branch, cancellation of equally long hook prefixes shows that the original
word has length zero.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

private theorem not_isReduced_negativeArrow_comp_zero_comp_positiveArrow_of_letter_eq
    {a b c d : Q} (leftArrow : b ⟶ a) (middle : SignedPath b c)
    (rightArrow : c ⟶ d) (hmiddle : middle.length = 0)
    (hletter : signedArrowLetter (negativeArrow leftArrow) =
      signedArrowLetter (negativeArrow rightArrow)) :
    ¬ IsReduced ((negativeArrow leftArrow).toPath.comp
      (middle.comp (positiveArrow rightArrow).toPath)) := by
  intro hred
  have hgenerator := congrArg Prod.fst hletter
  cases hgenerator
  have hmiddleNil := middle.eq_nil_of_length_zero hmiddle
  subst middle
  exact hred (negativeArrow leftArrow) (isContiguousSubpath_refl _)

private theorem length_eq_zero_and_boundaryLetter_eq_of_leftHook_result_eq_reverse_rightHook_result
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hmiddle : left.result = rightResult.reverse) :
    C.length = 0 ∧
      signedArrowLetter (negativeArrow left.hook.arrow) =
        signedArrowLetter (negativeArrow right.arrow) := by
  have hbaseWords : leftHookBaseWord left =
      rightHookReverseBaseWord right := by
    rw [leftHookBaseWord_eq_result,
      rightHookReverseBaseWord_eq_reverseResult]
    exact hmiddle
  have hpathWords := congrArg
    (fun W : Word R ↦ signedPathWord W.path) hbaseWords
  have hrightPath := rightHookReverseBasePath_eq right
  change signedPathWord (leftHookBasePath left) =
    signedPathWord (rightHookReverseBasePath right) at hpathWords
  rw [hrightPath] at hpathWords
  simp only [leftHookBasePath, signedPathWord_comp] at hpathWords
  have hleftMiddle :
      signedPathWord
          ((negativeArrow left.hook.arrow).toPath.comp C.path) =
        signedPathWord C.path ++
          signedPathWord (negativeArrow left.hook.arrow).toPath :=
    signedPathWord_comp _ _
  have hrightMiddle :
      signedPathWord
          ((negativeArrow right.arrow).toPath.comp C.path.reverse) =
        signedPathWord C.path.reverse ++
          signedPathWord (negativeArrow right.arrow).toPath :=
    signedPathWord_comp _ _
  have hpathWords' :
      (signedPathWord C.path ++
          signedPathWord (negativeArrow left.hook.arrow).toPath) ++
          signedPathWord
            left.hook.tail.toRightExtension.suffixPath.reverse =
        (signedPathWord C.path.reverse ++
          signedPathWord (negativeArrow right.arrow).toPath) ++
          signedPathWord
            right.tail.toRightExtension.suffixPath.reverse := by
    calc
      _ = signedPathWord
            ((negativeArrow left.hook.arrow).toPath.comp C.path) ++
          signedPathWord
            left.hook.tail.toRightExtension.suffixPath.reverse :=
        congrArg
          (fun w ↦ w ++ signedPathWord
            left.hook.tail.toRightExtension.suffixPath.reverse)
          hleftMiddle.symm
      _ = _ := hpathWords
      _ = _ := congrArg
        (fun w ↦ w ++ signedPathWord
          right.tail.toRightExtension.suffixPath.reverse)
        hrightMiddle
  simp only [signedPathWord_toPath, signedPathWord_reverse] at hpathWords'
  have htakes := congrArg (List.take C.length) hpathWords'
  have hwordLength : C.length = (signedPathWord C.path).length := by
    change C.path.length = (signedPathWord C.path).length
    exact (signedPathWord_length C.path).symm
  rw [hwordLength] at htakes
  have hreverseWord : signedPathWord C.path =
      FreeGroup.invRev (signedPathWord C.path) := by
    have htakes' :
        List.take (signedPathWord C.path).length
            (signedPathWord C.path ++
              ([signedArrowLetter (negativeArrow left.hook.arrow)] ++
                FreeGroup.invRev
                  (signedPathWord
                    left.hook.tail.toRightExtension.suffixPath))) =
          List.take (signedPathWord C.path).length
            (FreeGroup.invRev (signedPathWord C.path) ++
              ([signedArrowLetter (negativeArrow right.arrow)] ++
                FreeGroup.invRev
                  (signedPathWord
                    right.tail.toRightExtension.suffixPath))) := by
      simpa only [List.append_assoc] using htakes
    calc
      signedPathWord C.path =
          List.take (signedPathWord C.path).length
            (signedPathWord C.path ++
              ([signedArrowLetter (negativeArrow left.hook.arrow)] ++
                FreeGroup.invRev
                  (signedPathWord
                    left.hook.tail.toRightExtension.suffixPath))) :=
        (List.take_left).symm
      _ = _ := htakes'
      _ = FreeGroup.invRev (signedPathWord C.path) := by
        rw [show (signedPathWord C.path).length =
            (FreeGroup.invRev (signedPathWord C.path)).length from
          FreeGroup.invRev_length.symm]
        exact List.take_left
  have hzero := IsReduced.length_eq_zero_of_signedPathWord_eq_invRev
    C.path C.isString.1 hreverseWord
  have hCwordNil : signedPathWord C.path = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [signedPathWord_length]
    exact hzero
  have hboundaryLetter :
      signedArrowLetter (negativeArrow left.hook.arrow) =
        signedArrowLetter (negativeArrow right.arrow) := by
    have hheads := congrArg List.head? hpathWords'
    simpa [hCwordNil, FreeGroup.invRev] using hheads
  exact ⟨hzero, hboundaryLetter⟩

/-- If the left-hook result is the reverse of the right-hook result, then the
base string has length zero. -/
theorem length_eq_zero_of_leftHook_result_eq_reverse_rightHook_result
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hmiddle : left.result = rightResult.reverse) :
    C.length = 0 :=
  (length_eq_zero_and_boundaryLetter_eq_of_leftHook_result_eq_reverse_rightHook_result
    right left hmiddle).1

/-- A valid two-hook corner rules out the reversal branch altogether: in the
only possible length-zero case, equality of the reversed middle words forces
the two central boundary letters to cancel. -/
theorem leftHook_result_ne_reverse_rightHook_result_of_twoHookPath_isString
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    left.result ≠ rightResult.reverse := by
  intro hmiddle
  obtain ⟨hzero, hboundaryLetter⟩ :=
    length_eq_zero_and_boundaryLetter_eq_of_leftHook_result_eq_reverse_rightHook_result
      right left hmiddle
  let central := (negativeArrow left.hook.arrow).toPath.comp
    (C.path.comp (positiveArrow right.arrow).toPath)
  have hcentralSub : IsContiguousSubpath central
      (twoHookPath right left) := by
    refine ⟨left.hook.tail.toRightExtension.suffixPath.reverse,
      right.tail.toRightExtension.suffixPath, ?_⟩
    simp only [central, twoHookPath]
    calc
      _ = left.hook.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow left.hook.arrow).toPath.comp
            ((C.path.comp (positiveArrow right.arrow).toPath).comp
              right.tail.toRightExtension.suffixPath)) :=
        congrArg
          (fun p ↦ left.hook.tail.toRightExtension.suffixPath.reverse.comp
            ((negativeArrow left.hook.arrow).toPath.comp p))
          (Quiver.Path.comp_assoc C.path
            (positiveArrow right.arrow).toPath
            right.tail.toRightExtension.suffixPath).symm
      _ = _ := congrArg
        (fun p ↦ left.hook.tail.toRightExtension.suffixPath.reverse.comp p)
        (Quiver.Path.comp_assoc
          (negativeArrow left.hook.arrow).toPath
          (C.path.comp (positiveArrow right.arrow).toPath)
          right.tail.toRightExtension.suffixPath).symm
  have hcentralReduced : IsReduced central :=
    IsReduced.of_contiguousSubpath hpath.1 hcentralSub
  exact
    (not_isReduced_negativeArrow_comp_zero_comp_positiveArrow_of_letter_eq
      left.hook.arrow C.path right.arrow hzero hboundaryLetter)
      hcentralReduced

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : StringPresentation k A Q}

/-- Isomorphic positive-hook middle modules have either literally equal
middle words or a length-zero base word.  Thus reversal is confined to the
single convention-sensitive edge case. -/
theorem leftHook_result_eq_or_base_length_eq_zero_of_finiteRightModule_iso
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    {C rightResult : Word P.toPresentation.relations}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (e : left.result.finiteRightModule P.monomial ≅
      rightResult.finiteRightModule P.monomial) :
    left.result = rightResult ∨ C.length = 0 := by
  rcases DetectorIndex.eq_or_eq_reverse_of_finiteRightModule_iso
      S left.result rightResult e with hmiddle | hreverse
  · exact Or.inl hmiddle
  · exact Or.inr
      (length_eq_zero_of_leftHook_result_eq_reverse_rightHook_result
        right left hreverse)

/-- For a valid positive two-hook square, isomorphism of the two middle
modules forces literal equality of their words.  The detector classification
gives equality or reversal, and reducedness excludes reversal. -/
theorem leftHook_result_eq_of_finiteRightModule_iso_of_twoHookPath_isString
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    {C rightResult : Word P.toPresentation.relations}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString P.toPresentation.relations
      (twoHookPath right left))
    (e : left.result.finiteRightModule P.monomial ≅
      rightResult.finiteRightModule P.monomial) :
    left.result = rightResult := by
  rcases DetectorIndex.eq_or_eq_reverse_of_finiteRightModule_iso
      S left.result rightResult e with hmiddle | hreverse
  · exact hmiddle
  · exact False.elim
      (leftHook_result_ne_reverse_rightHook_result_of_twoHookPath_isString
        right left hpath hreverse)

end MagnitudeConjecture.BoundQuiver.StringWord.Word
