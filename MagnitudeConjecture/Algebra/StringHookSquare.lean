import MagnitudeConjecture.Algebra.StringBoundarySquare
import MagnitudeConjecture.Algebra.StringLeftHookCohook

/-!
# Common corners for two-ended string hooks

This file constructs the signed path obtained by applying a maximal hook at
both endpoints of a nontrivial string.  The signs at the two seams block
relations from crossing the whole word, while the nonempty original word
prevents a new inverse pair from spanning both seams.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- The explicit path of a left hook, ending at the old right endpoint. -/
def leftHookBasePath {C : Word R} (left : LeftHookExtension C) :
    SignedPath left.reverseResult.target C.target :=
  left.hook.tail.toRightExtension.suffixPath.reverse.comp
    ((negativeArrow left.hook.arrow).toPath.comp C.path)

/-- The explicit signed path obtained by adjoining the left-hook suffix in
reverse order and the right-hook suffix in forward order. -/
def twoHookPath {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) :
    SignedPath left.reverseResult.target rightResult.target :=
  left.hook.tail.toRightExtension.suffixPath.reverse.comp
    ((negativeArrow left.hook.arrow).toPath.comp
      (C.path.comp ((positiveArrow right.arrow).toPath.comp
        right.tail.toRightExtension.suffixPath)))

/-- The same two-ended path written directly in the reverse orientation. -/
def twoHookReversePath {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) :
    SignedPath rightResult.target left.reverseResult.target :=
  right.tail.toRightExtension.suffixPath.reverse.comp
    ((negativeArrow right.arrow).toPath.comp
      (C.path.reverse.comp ((positiveArrow left.hook.arrow).toPath.comp
        left.hook.tail.toRightExtension.suffixPath)))

/-- The left one-ended hook certifies the left part of the explicit
two-hook path. -/
theorem leftHookPath_isString {C : Word R}
    (left : LeftHookExtension C) :
    IsString R
      (left.hook.tail.toRightExtension.suffixPath.reverse.comp
        ((negativeArrow left.hook.arrow).toPath.comp C.path)) := by
  have hforward :=
    left.hook.toPositiveBoundaryExtension.toRightExtension.comp_suffixPath_isString
  have hreverse :=
    (isString_reverse_iff R
      (C.reverse.path.comp
        left.hook.toPositiveBoundaryExtension.toRightExtension.suffixPath)).2
      hforward
  have hreverseReverse : C.path.reverse.reverse = C.path :=
    @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ C.path
  simp only [PositiveBoundaryExtension.toRightExtension_suffixPath,
    HookExtension.toPositiveBoundaryExtension, reverse_path,
    Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    reverse_positiveArrow,
    Quiver.Path.comp_assoc] at hreverse
  have hpathEq :
      left.hook.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow left.hook.arrow).toPath.comp
            C.path.reverse.reverse) =
        left.hook.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow left.hook.arrow).toPath.comp C.path) :=
    congrArg
      (fun p : SignedPath C.source C.target ↦
        left.hook.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow left.hook.arrow).toPath.comp p))
      hreverseReverse
  exact hpathEq ▸ hreverse

/-- Bundle the explicit left-hook path as a word. -/
def leftHookBaseWord {C : Word R} (left : LeftHookExtension C) : Word R :=
  ofStringPath (leftHookBasePath left) (leftHookPath_isString left)

/-- The explicit left-hook word is the transported reversal-based result. -/
theorem leftHookBaseWord_eq_result {C : Word R}
    (left : LeftHookExtension C) :
    leftHookBaseWord left = left.result := by
  let extension :=
    left.hook.toPositiveBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hreverseFactor := congrArg Quiver.Path.reverse hfactor
  rw [path_reverse_cast] at hreverseFactor
  have hsuffix :=
    left.hook.toPositiveBoundaryExtension.toRightExtension_suffixPath
  change extension.suffixPath =
    (positiveArrow left.hook.arrow).toPath.comp
      left.hook.tail.toRightExtension.suffixPath at hsuffix
  rw [hsuffix] at hreverseFactor
  simp only [reverse_path,
    Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    reverse_positiveArrow, Quiver.Path.comp_assoc] at hreverseFactor
  have hreverseReverse : C.path.reverse.reverse = C.path :=
    @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ C.path
  have hpathCast :
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        left.reverseResult.target left.reverseResult.source
        left.reverseResult.target C.target rfl extension.source_eq
        left.reverseResult.path.reverse) = leftHookBasePath left := by
    calc
      _ = left.hook.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow left.hook.arrow).toPath.comp
            C.path.reverse.reverse) := hreverseFactor
      _ = leftHookBasePath left := by
        exact congrArg
          (fun p : SignedPath C.source C.target ↦
            left.hook.tail.toRightExtension.suffixPath.reverse.comp
              ((negativeArrow left.hook.arrow).toPath.comp p))
          hreverseReverse
  apply Word.ext
  · rfl
  · exact extension.source_eq.symm
  · exact HEq.trans (heq_of_eq hpathCast.symm)
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _ rfl extension.source_eq
        left.reverseResult.path.reverse)

/-- The right one-ended hook certifies the right part of the explicit
two-hook path. -/
theorem rightHookPath_isString {C rightResult : Word R}
    (right : HookExtension C rightResult) :
    IsString R
      (C.path.comp ((positiveArrow right.arrow).toPath.comp
        right.tail.toRightExtension.suffixPath)) := by
  simpa only [PositiveBoundaryExtension.toRightExtension_suffixPath,
    HookExtension.toPositiveBoundaryExtension] using
    right.toPositiveBoundaryExtension.toRightExtension.comp_suffixPath_isString

/-- The reversed explicit right-hook path, ending at the old left endpoint. -/
def rightHookReverseBasePath {C rightResult : Word R}
    (right : HookExtension C rightResult) :
    SignedPath rightResult.target C.source :=
  (C.path.comp ((positiveArrow right.arrow).toPath.comp
    right.tail.toRightExtension.suffixPath)).reverse

/-- The right hook certifies its explicit reversed base path. -/
theorem rightHookReverseBasePath_isString {C rightResult : Word R}
    (right : HookExtension C rightResult) :
    IsString R (rightHookReverseBasePath right) := by
  exact (isString_reverse_iff R
    (C.path.comp ((positiveArrow right.arrow).toPath.comp
      right.tail.toRightExtension.suffixPath))).2
    (rightHookPath_isString right)

/-- Expanded form of the reversed right-hook path. -/
theorem rightHookReverseBasePath_eq {C rightResult : Word R}
    (right : HookExtension C rightResult) :
    rightHookReverseBasePath right =
      right.tail.toRightExtension.suffixPath.reverse.comp
        ((negativeArrow right.arrow).toPath.comp C.path.reverse) := by
  simp only [rightHookReverseBasePath, Quiver.Path.reverse_comp,
    Quiver.Path.reverse_toPath, reverse_positiveArrow,
    Quiver.Path.comp_assoc]
  rfl

/-- Bundle the reversed explicit right-hook path as a word. -/
def rightHookReverseBaseWord {C rightResult : Word R}
    (right : HookExtension C rightResult) : Word R :=
  ofStringPath (rightHookReverseBasePath right)
    (rightHookReverseBasePath_isString right)

/-- The explicit reversed right-hook word is the reversal of the hook
result. -/
theorem rightHookReverseBaseWord_eq_reverseResult
    {C rightResult : Word R} (right : HookExtension C rightResult) :
    rightHookReverseBaseWord right = rightResult.reverse := by
  let extension := right.toPositiveBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hreverseFactor := congrArg Quiver.Path.reverse hfactor
  rw [path_reverse_cast] at hreverseFactor
  have hsuffix := right.toPositiveBoundaryExtension.toRightExtension_suffixPath
  change extension.suffixPath =
    (positiveArrow right.arrow).toPath.comp
      right.tail.toRightExtension.suffixPath at hsuffix
  rw [hsuffix] at hreverseFactor
  simp only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    reverse_positiveArrow, Quiver.Path.comp_assoc] at hreverseFactor
  have hpathCast :
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        rightResult.target rightResult.source rightResult.target C.source
        rfl extension.source_eq rightResult.path.reverse) =
        rightHookReverseBasePath right := by
    exact hreverseFactor.trans (rightHookReverseBasePath_eq right).symm
  apply Word.ext
  · rfl
  · exact extension.source_eq.symm
  · exact HEq.trans (heq_of_eq hpathCast.symm)
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _ rfl extension.source_eq
        rightResult.path.reverse)

/-- The directly written reverse two-hook path is a string whenever the
original word is nonempty. -/
theorem twoHookReversePath_isString {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hC : 0 < C.length) : IsString R (twoHookReversePath right left) := by
  apply isString_comp_of_negative_positive_boundaries R
    right.tail.toRightExtension.suffixPath.reverse
    right.arrow C.path.reverse left.hook.arrow
    left.hook.tail.toRightExtension.suffixPath
  · change 0 < C.path.length at hC
    rw [length_reverse]
    exact hC
  · exact (rightHookReverseBasePath_eq right) ▸
      rightHookReverseBasePath_isString right
  · change IsString R
      (C.reverse.path.comp ((positiveArrow left.hook.arrow).toPath.comp
        left.hook.tail.toRightExtension.suffixPath))
    simpa only [PositiveBoundaryExtension.toRightExtension_suffixPath,
      HookExtension.toPositiveBoundaryExtension] using
      left.hook.toPositiveBoundaryExtension.toRightExtension.comp_suffixPath_isString

/-- Hooks at both ends of a nontrivial string produce a valid common-corner
path. -/
theorem twoHookPath_isString {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hC : 0 < C.length) : IsString R (twoHookPath right left) := by
  exact isString_comp_of_negative_positive_boundaries R
    left.hook.tail.toRightExtension.suffixPath.reverse
    left.hook.arrow C.path right.arrow
    right.tail.toRightExtension.suffixPath hC
    (leftHookPath_isString left) (rightHookPath_isString right)

/-- If the right-hook boundary already extends the full left-hook result,
the two hook arms glue through the nonempty overlap consisting of the base
word and that boundary letter. -/
theorem twoHookPath_isString_of_leftHookResult_extension
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hext : IsString R
      ((leftHookBasePath left).comp
        (positiveArrow right.arrow).toPath)) :
    IsString R (twoHookPath right left) := by
  let leftTail := left.hook.tail.toRightExtension.suffixPath.reverse
  let leftBoundary := leftTail.comp
    (negativeArrow left.hook.arrow).toPath
  let middle := C.path.comp (positiveArrow right.arrow).toPath
  let rightTail := right.tail.toRightExtension.suffixPath
  have hmiddle : 0 < middle.length := by
    simp only [middle, Quiver.Path.length_comp,
      Quiver.Path.length_toPath]
    omega
  have hleftReduced : IsReduced (leftBoundary.comp middle) := by
    intro x y e hsub
    have hpath :
        (leftHookBasePath left).comp
            (positiveArrow right.arrow).toPath =
          leftBoundary.comp middle := by
      dsimp only [leftHookBasePath, leftTail, leftBoundary, middle]
      let boundary := (negativeArrow left.hook.arrow).toPath
      let newArrow := (positiveArrow right.arrow).toPath
      calc
        (leftTail.comp (boundary.comp C.path)).comp newArrow =
            leftTail.comp ((boundary.comp C.path).comp newArrow) :=
          Quiver.Path.comp_assoc _ _ _
        _ = leftTail.comp (boundary.comp (C.path.comp newArrow)) :=
          congrArg (fun p ↦ leftTail.comp p)
            (Quiver.Path.comp_assoc boundary C.path newArrow)
        _ = (leftTail.comp boundary).comp (C.path.comp newArrow) :=
          (Quiver.Path.comp_assoc _ _ _).symm
    apply hext.1 e
    rw [hpath]
    exact hsub
  have hrightReduced : IsReduced (middle.comp rightTail) := by
    intro x y e hsub
    apply (rightHookPath_isString right).1 e
    simpa only [middle, rightTail, Quiver.Path.comp_assoc] using hsub
  have hfullReduced : IsReduced
      (leftBoundary.comp (middle.comp rightTail)) :=
    isReduced_comp_of_overlap leftBoundary middle rightTail hmiddle
      hleftReduced hrightReduced
  have hfullPath : leftBoundary.comp (middle.comp rightTail) =
      leftTail.comp ((negativeArrow left.hook.arrow).toPath.comp
        (C.path.comp ((positiveArrow right.arrow).toPath.comp
          rightTail))) := by
    dsimp only [leftBoundary, middle]
    let boundary := (negativeArrow left.hook.arrow).toPath
    let newArrow := (positiveArrow right.arrow).toPath
    calc
      (leftTail.comp boundary).comp
          ((C.path.comp newArrow).comp rightTail) =
        leftTail.comp
          (boundary.comp ((C.path.comp newArrow).comp rightTail)) :=
        Quiver.Path.comp_assoc _ _ _
      _ = leftTail.comp
          (boundary.comp (C.path.comp (newArrow.comp rightTail))) :=
        congrArg (fun p ↦ leftTail.comp (boundary.comp p))
          (Quiver.Path.comp_assoc C.path newArrow rightTail)
  rw [hfullPath] at hfullReduced
  apply isString_comp_of_negative_positive_boundaries_of_reduced R
    leftTail left.hook.arrow C.path right.arrow rightTail
  · exact hfullReduced
  · exact leftHookPath_isString left
  · exact rightHookPath_isString right

/-- If a left-hook result is not a right peak, one of its positive boundary
extensions induces a right hook on the original word and hence a valid
two-hook corner. -/
theorem exists_hook_twoHookPath_isString_of_leftHookResult_not_startsOnPeak
    (hR : IsAdmissible R) {C : Word R}
    (left : LeftHookExtension C)
    (hnotPeak : ¬ left.result.StartsOnPeak) :
    ∃ rightResult : Word R, ∃ right : HookExtension C rightResult,
      IsString R (twoHookPath right left) := by
  have hnotBase : ¬ (leftHookBaseWord left).StartsOnPeak := by
    rw [leftHookBaseWord_eq_result]
    exact hnotPeak
  simp only [StartsOnPeak] at hnotBase
  push Not at hnotBase
  obtain ⟨z, a, hext⟩ := hnotBase
  have hrightValid : IsString R
      (C.path.comp (positiveArrow a).toPath) := by
    apply IsString.of_contiguousSubpath R hext
    let leftPrefix :=
      left.hook.tail.toRightExtension.suffixPath.reverse.comp
        (negativeArrow left.hook.arrow).toPath
    refine ⟨leftPrefix, Quiver.Path.nil, ?_⟩
    dsimp only [leftHookBaseWord, ofStringPath, leftHookBasePath,
      leftPrefix]
    simp only [Quiver.Path.comp_nil]
    let tailPath := left.hook.tail.toRightExtension.suffixPath.reverse
    let boundary := (negativeArrow left.hook.arrow).toPath
    let newArrow := (positiveArrow a).toPath
    exact (Quiver.Path.comp_assoc tailPath boundary
      (C.path.comp newArrow)).symm
  obtain ⟨rightResult, right, hboundary⟩ :=
    HookExtension.exists_of_append_positive hR C a hrightValid
  cases hboundary
  refine ⟨rightResult, right, ?_⟩
  apply twoHookPath_isString_of_leftHookResult_extension right left
  simpa only [leftHookBaseWord, ofStringPath] using hext

/-- At a length-zero word, two hooks still glue when their adjacent signed
boundary letters do not cancel. -/
theorem twoHookPath_isString_of_length_zero {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hC : C.length = 0)
    (hboundary : ¬ HEq (positiveArrow right.arrow)
      (Quiver.reverse (negativeArrow left.hook.arrow))) :
    IsString R (twoHookPath right left) := by
  change C.path.length = 0 at hC
  let leftTail := left.hook.tail.toRightExtension.suffixPath.reverse
  let leftMiddle :=
    (negativeArrow left.hook.arrow).toPath.comp C.path
  let central := leftMiddle.comp (positiveArrow right.arrow).toPath
  let rightMiddle :=
    C.path.comp (positiveArrow right.arrow).toPath
  let rightTail := right.tail.toRightExtension.suffixPath
  have hleft : IsReduced (leftTail.comp leftMiddle) := by
    have hleftString := leftHookPath_isString left
    have hpath : leftTail.comp leftMiddle =
        left.hook.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow left.hook.arrow).toPath.comp C.path) := rfl
    intro x y (signedArrow : SignedArrow x y) hsub
    apply hleftString.1 signedArrow
    exact hpath ▸ hsub
  have hright : IsReduced (rightMiddle.comp rightTail) := by
    have hrightString := rightHookPath_isString right
    have hpath : rightMiddle.comp rightTail =
        C.path.comp ((positiveArrow right.arrow).toPath.comp
          right.tail.toRightExtension.suffixPath) := by
      exact Quiver.Path.comp_assoc _ _ _
    intro x y (signedArrow : SignedArrow x y) hsub
    apply hrightString.1 signedArrow
    exact hpath ▸ hsub
  have hcenterRaw : IsReduced
      ((negativeArrow left.hook.arrow).toPath.comp
        (C.path.comp (positiveArrow right.arrow).toPath)) := by
    intro x y (signedArrow : SignedArrow x y) hsub
    exact
      (isReduced_toPath_comp_zero_comp_toPath_of_not_heq_reverse
        (negativeArrow left.hook.arrow) C.path
        (positiveArrow right.arrow) hC hboundary) signedArrow hsub
  have hcenter : IsReduced central := by
    have hpath : central =
        (negativeArrow left.hook.arrow).toPath.comp
          (C.path.comp (positiveArrow right.arrow).toPath) := by
      exact Quiver.Path.comp_assoc _ _ _
    intro x y (signedArrow : SignedArrow x y) hsub
    apply hcenterRaw signedArrow
    exact hpath ▸ hsub
  have hleftMiddleLength : 0 < leftMiddle.length := by
    simp only [leftMiddle, Quiver.Path.length_comp,
      Quiver.Path.length_toPath]
    omega
  have hrightMiddleLength : 0 < rightMiddle.length := by
    simp only [rightMiddle, Quiver.Path.length_comp,
      Quiver.Path.length_toPath, hC]
    omega
  have hleftCenter :
      IsReduced (leftTail.comp central) := by
    apply isReduced_comp_of_overlap leftTail leftMiddle
      (positiveArrow right.arrow).toPath hleftMiddleLength
    · exact hleft
    · exact hcenter
  have hcenterRight :
      IsReduced ((negativeArrow left.hook.arrow).toPath.comp
        (rightMiddle.comp rightTail)) := by
    apply isReduced_comp_of_overlap
      (negativeArrow left.hook.arrow).toPath rightMiddle rightTail
      hrightMiddleLength
    · exact hcenterRaw
    · exact hright
  have hcenterRight' :
      IsReduced (central.comp rightTail) := by
    have hpath : central.comp rightTail =
        (negativeArrow left.hook.arrow).toPath.comp
          (rightMiddle.comp rightTail) := by
      dsimp only [central, leftMiddle, rightMiddle]
      simp only [Quiver.Path.comp_assoc]
      rfl
    intro x y (signedArrow : SignedArrow x y) hsub
    apply hcenterRight signedArrow
    exact hpath ▸ hsub
  have hcentralLength : 0 < central.length := by
    simp only [central, leftMiddle, Quiver.Path.length_comp,
      Quiver.Path.length_toPath]
    omega
  have hreduced :
      IsReduced (leftTail.comp (central.comp rightTail)) := by
    apply isReduced_comp_of_overlap leftTail central rightTail hcentralLength
    · exact hleftCenter
    · exact hcenterRight'
  have hfullPath : leftTail.comp (central.comp rightTail) =
      leftTail.comp ((negativeArrow left.hook.arrow).toPath.comp
        (C.path.comp ((positiveArrow right.arrow).toPath.comp rightTail))) := by
    dsimp only [central, leftMiddle]
    simp only [Quiver.Path.comp_assoc]
    rfl
  have hfullReduced : IsReduced
      (leftTail.comp ((negativeArrow left.hook.arrow).toPath.comp
        (C.path.comp ((positiveArrow right.arrow).toPath.comp rightTail)))) := by
    intro x y (signedArrow : SignedArrow x y) hsub
    apply hreduced signedArrow
    exact hfullPath.symm ▸ hsub
  apply isString_comp_of_negative_positive_boundaries_of_reduced R
    leftTail left.hook.arrow C.path right.arrow rightTail
  · exact hfullReduced
  · exact leftHookPath_isString left
  · exact rightHookPath_isString right

/-- Reversing the directly written reverse path recovers the forward
two-hook path. -/
theorem twoHookReversePath_reverse {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) :
    (twoHookReversePath right left).reverse = twoHookPath right left := by
  unfold twoHookReversePath twoHookPath
  calc
    _ = ((negativeArrow right.arrow).toPath.comp
          (C.path.reverse.comp ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath))).reverse.comp
        right.tail.toRightExtension.suffixPath.reverse.reverse :=
      @Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        right.tail.toRightExtension.suffixPath.reverse
        ((negativeArrow right.arrow).toPath.comp
          (C.path.reverse.comp ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath)))
    _ = ((C.path.reverse.comp
          ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath)).reverse.comp
          (negativeArrow right.arrow).toPath.reverse).comp
        right.tail.toRightExtension.suffixPath.reverse.reverse := by
      exact congrArg
        (fun p ↦ p.comp
          right.tail.toRightExtension.suffixPath.reverse.reverse)
        (@Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          (negativeArrow right.arrow).toPath
          (C.path.reverse.comp
            ((positiveArrow left.hook.arrow).toPath.comp
              left.hook.tail.toRightExtension.suffixPath)))
    _ = ((((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath).reverse.comp
          C.path.reverse.reverse).comp
          (negativeArrow right.arrow).toPath.reverse).comp
        right.tail.toRightExtension.suffixPath.reverse.reverse := by
      exact congrArg
        (fun p ↦ (p.comp (negativeArrow right.arrow).toPath.reverse).comp
          right.tail.toRightExtension.suffixPath.reverse.reverse)
        (@Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _ C.path.reverse
          ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath))
    _ = (((left.hook.tail.toRightExtension.suffixPath.reverse.comp
            (positiveArrow left.hook.arrow).toPath.reverse).comp
          C.path.reverse.reverse).comp
          (negativeArrow right.arrow).toPath.reverse).comp
        right.tail.toRightExtension.suffixPath.reverse.reverse := by
      exact congrArg
        (fun p ↦ ((p.comp C.path.reverse.reverse).comp
          (negativeArrow right.arrow).toPath.reverse).comp
            right.tail.toRightExtension.suffixPath.reverse.reverse)
        (@Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          (positiveArrow left.hook.arrow).toPath
          left.hook.tail.toRightExtension.suffixPath)
    _ = _ := by
      simp only [Quiver.Path.reverse_toPath, reverse_negativeArrow,
        reverse_positiveArrow, Quiver.Path.reverse_reverse,
        Quiver.Path.comp_assoc]
      rfl

/-- The common word together with its right positive-boundary extension from
the left-hook result. -/
structure TwoHookRightCorner {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) where
  corner : Word R
  extension : PositiveBoundaryExtension left.result corner
  steps_eq : extension.toRightExtension.steps = right.steps
  source_eq : corner.source = left.reverseResult.target
  target_eq : corner.target = rightResult.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) corner.source corner.target
      left.reverseResult.target rightResult.target source_eq target_eq
      corner.path) = twoHookPath right left

/-- Replay the right-hook tail after the explicit left-hook word. -/
def twoHookRightCorner {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    TwoHookRightCorner right left := by
  let basePath := leftHookBasePath left
  let hbase : IsString R basePath := leftHookPath_isString left
  let baseWord : Word R := ofStringPath basePath hbase
  have hbaseWord : baseWord = left.result := by
    calc
      baseWord = leftHookBaseWord left := by
        apply Word.ext
        · rfl
        · rfl
        · exact HEq.rfl
      _ = left.result := leftHookBaseWord_eq_result left
  have hfull : IsString R
      (basePath.comp ((positiveArrow right.arrow).toPath.comp
        right.tail.toRightExtension.suffixPath)) := by
    have hcombined := hpath
    change IsString R
      (left.hook.tail.toRightExtension.suffixPath.reverse.comp
        ((negativeArrow left.hook.arrow).toPath.comp
          (C.path.comp ((positiveArrow right.arrow).toPath.comp
            right.tail.toRightExtension.suffixPath)))) at hcombined
    have houter := Quiver.Path.comp_assoc
      left.hook.tail.toRightExtension.suffixPath.reverse
      ((negativeArrow left.hook.arrow).toPath.comp C.path)
      ((positiveArrow right.arrow).toPath.comp
        right.tail.toRightExtension.suffixPath)
    have hinner := Quiver.Path.comp_assoc
      (negativeArrow left.hook.arrow).toPath C.path
      ((positiveArrow right.arrow).toPath.comp
        right.tail.toRightExtension.suffixPath)
    have hassoc := houter.trans (congrArg
      (fun p ↦
        left.hook.tail.toRightExtension.suffixPath.reverse.comp p)
      hinner)
    change IsString R
      ((left.hook.tail.toRightExtension.suffixPath.reverse.comp
        ((negativeArrow left.hook.arrow).toPath.comp C.path)).comp
          ((positiveArrow right.arrow).toPath.comp
            right.tail.toRightExtension.suffixPath))
    exact hassoc.symm ▸ hcombined
  have hvalid : IsString R
      (basePath.comp (positiveArrow right.arrow).toPath) := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil,
      right.tail.toRightExtension.suffixPath, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
  let firstWord : Word R :=
    append R baseWord (positiveArrow right.arrow) hvalid
  have htailFull : IsString R
      (firstWord.path.comp right.tail.toRightExtension.suffixPath) := by
    change IsString R
      ((basePath.comp (positiveArrow right.arrow).toPath).comp
        right.tail.toRightExtension.suffixPath)
    simpa only [Quiver.Path.comp_assoc] using hfull
  let replay := right.tail.toRightExtension.rebase
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayExtension : RightExtension firstWord replay.result := by
    exact Eq.mp
      (congrArg (fun W : Word R ↦ RightExtension W replay.result)
        hreplayBase)
      replay.rebased
  let fromBase : PositiveBoundaryExtension baseWord replay.result := {
    vertex := right.vertex
    arrow := right.arrow
    valid := hvalid
    tail := replayExtension }
  let fromLeft : PositiveBoundaryExtension left.result replay.result := by
    exact Eq.mp
      (congrArg
        (fun W : Word R ↦ PositiveBoundaryExtension W replay.result)
        hbaseWord)
      fromBase
  have hpathFull :
      (basePath.comp (positiveArrow right.arrow).toPath).comp
          right.tail.toRightExtension.suffixPath =
        twoHookPath right left := by
    dsimp only [basePath, leftHookBasePath, twoHookPath]
    calc
      _ = (left.hook.tail.toRightExtension.suffixPath.reverse.comp
            ((negativeArrow left.hook.arrow).toPath.comp C.path)).comp
          ((positiveArrow right.arrow).toPath.comp
            right.tail.toRightExtension.suffixPath) :=
        Quiver.Path.comp_assoc _ _ _
      _ = left.hook.tail.toRightExtension.suffixPath.reverse.comp
          (((negativeArrow left.hook.arrow).toPath.comp C.path).comp
            ((positiveArrow right.arrow).toPath.comp
              right.tail.toRightExtension.suffixPath)) :=
        Quiver.Path.comp_assoc _ _ _
      _ = _ := congrArg
        (fun p ↦
          left.hook.tail.toRightExtension.suffixPath.reverse.comp p)
        (Quiver.Path.comp_assoc _ _ _)
  exact {
    corner := replay.result
    extension := fromLeft
    steps_eq := by
      calc
        fromLeft.toRightExtension.steps =
            fromBase.toRightExtension.steps :=
          PositiveBoundaryExtension.toRightExtension_steps_transport_source
            hbaseWord fromBase
        _ = replayExtension.steps + 1 := by
          simp only [fromBase,
            PositiveBoundaryExtension.toRightExtension_steps]
        _ = replay.rebased.steps + 1 := by
          exact congrArg (fun n ↦ n + 1)
            (RightExtension.steps_transport_source
              hreplayBase replay.rebased)
        _ = right.tail.toRightExtension.steps + 1 := by
          rw [RightExtension.rebase_steps]
        _ = right.steps := by
          simp only [NegativeExtension.toRightExtension_steps,
            HookExtension.steps]
    source_eq := replay.source_eq
    target_eq := replay.target_eq
    path_cast_eq := by
      calc
        _ = firstWord.path.comp
              right.tail.toRightExtension.suffixPath :=
          replay.path_cast_eq
        _ = (basePath.comp (positiveArrow right.arrow).toPath).comp
              right.tail.toRightExtension.suffixPath := rfl
        _ = twoHookPath right left := hpathFull }

/-- The canonical bundled common-corner word. -/
def twoHookCornerWord {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) : Word R :=
  ofStringPath (twoHookPath right left) hpath

/-- The replayed right corner is the canonical bundled two-hook word. -/
theorem TwoHookRightCorner.corner_eq_twoHookCornerWord
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (corner : TwoHookRightCorner right left) :
    corner.corner = twoHookCornerWord right left hpath := by
  apply Word.ext
  · exact corner.source_eq
  · exact corner.target_eq
  · exact HEq.trans
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        corner.source_eq corner.target_eq corner.corner.path).symm
      (heq_of_eq corner.path_cast_eq)

/-- The common reversed word together with the positive-boundary extension
whose reversal is a left extension of the right-hook result. -/
structure TwoHookLeftCorner {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) where
  reverseCorner : Word R
  extension : LeftPositiveBoundaryExtension rightResult
  reverseResult_eq : extension.reverseResult = reverseCorner
  steps_eq : extension.steps = left.steps
  source_eq : reverseCorner.source = rightResult.target
  target_eq : reverseCorner.target = left.reverseResult.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q)
      reverseCorner.source reverseCorner.target
      rightResult.target left.reverseResult.target source_eq target_eq
      reverseCorner.path) = twoHookReversePath right left

/-- Replay the left-hook tail after the reversed explicit right-hook word. -/
def twoHookLeftCorner {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    TwoHookLeftCorner right left := by
  let basePath := rightHookReverseBasePath right
  let hbase : IsString R basePath :=
    rightHookReverseBasePath_isString right
  let baseWord : Word R := ofStringPath basePath hbase
  have hbaseWord : baseWord = rightResult.reverse := by
    calc
      baseWord = rightHookReverseBaseWord right := by
        apply Word.ext
        · rfl
        · rfl
        · exact HEq.rfl
      _ = rightResult.reverse :=
        rightHookReverseBaseWord_eq_reverseResult right
  have hcornerReverse : IsString R (twoHookReversePath right left) :=
    (isString_reverse_iff R (twoHookReversePath right left)).1 (by
      rw [twoHookReversePath_reverse]
      exact hpath)
  have hpathFull :
      (rightHookReverseBasePath right).comp
          ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath) =
        twoHookReversePath right left := by
    rw [rightHookReverseBasePath_eq]
    exact (Quiver.Path.comp_assoc _ _ _).trans
      (congrArg
        (fun p ↦ right.tail.toRightExtension.suffixPath.reverse.comp p)
        (Quiver.Path.comp_assoc _ _ _))
  have hfull : IsString R
      (basePath.comp ((positiveArrow left.hook.arrow).toPath.comp
        left.hook.tail.toRightExtension.suffixPath)) := by
    change IsString R
      ((rightHookReverseBasePath right).comp
        ((positiveArrow left.hook.arrow).toPath.comp
          left.hook.tail.toRightExtension.suffixPath))
    exact hpathFull.symm ▸ hcornerReverse
  have hvalid : IsString R
      (basePath.comp (positiveArrow left.hook.arrow).toPath) := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil,
      left.hook.tail.toRightExtension.suffixPath, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
    rfl
  let firstWord : Word R :=
    append R baseWord (positiveArrow left.hook.arrow) hvalid
  have htailFull : IsString R
      (firstWord.path.comp left.hook.tail.toRightExtension.suffixPath) := by
    change IsString R
      ((basePath.comp (positiveArrow left.hook.arrow).toPath).comp
        left.hook.tail.toRightExtension.suffixPath)
    have hassoc :
        (basePath.comp (positiveArrow left.hook.arrow).toPath).comp
            left.hook.tail.toRightExtension.suffixPath =
          basePath.comp ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath) :=
      @Quiver.Path.comp_assoc (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _ basePath
        (positiveArrow left.hook.arrow).toPath
        left.hook.tail.toRightExtension.suffixPath
    exact hassoc.symm ▸ hfull
  let replay := left.hook.tail.toRightExtension.rebase
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayExtension : RightExtension firstWord replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ RightExtension W replay.result)
        hreplayBase)
      replay.rebased
  let fromBase : PositiveBoundaryExtension baseWord replay.result := {
    vertex := left.hook.vertex
    arrow := left.hook.arrow
    valid := hvalid
    tail := replayExtension }
  let fromReverseRight :
      PositiveBoundaryExtension rightResult.reverse replay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ PositiveBoundaryExtension W replay.result)
        hbaseWord)
      fromBase
  let leftExtension : LeftPositiveBoundaryExtension rightResult := {
    reverseResult := replay.result
    extension := fromReverseRight }
  exact {
    reverseCorner := replay.result
    extension := leftExtension
    reverseResult_eq := rfl
    steps_eq := by
      change fromReverseRight.toRightExtension.steps = left.hook.steps
      calc
        fromReverseRight.toRightExtension.steps =
            fromBase.toRightExtension.steps :=
          PositiveBoundaryExtension.toRightExtension_steps_transport_source
            hbaseWord fromBase
        _ = replayExtension.steps + 1 := by
          simp only [fromBase,
            PositiveBoundaryExtension.toRightExtension_steps]
        _ = replay.rebased.steps + 1 := by
          exact congrArg (fun n ↦ n + 1)
            (RightExtension.steps_transport_source
              hreplayBase replay.rebased)
        _ = left.hook.tail.toRightExtension.steps + 1 := by
          rw [RightExtension.rebase_steps]
        _ = left.hook.steps := by
          simp only [NegativeExtension.toRightExtension_steps,
            HookExtension.steps]
    source_eq := replay.source_eq
    target_eq := replay.target_eq
    path_cast_eq := by
      calc
        _ = firstWord.path.comp
              left.hook.tail.toRightExtension.suffixPath :=
          replay.path_cast_eq
        _ = (basePath.comp (positiveArrow left.hook.arrow).toPath).comp
              left.hook.tail.toRightExtension.suffixPath := rfl
        _ = (rightHookReverseBasePath right).comp
              ((positiveArrow left.hook.arrow).toPath.comp
                left.hook.tail.toRightExtension.suffixPath) :=
          Quiver.Path.comp_assoc _ _ _
        _ = twoHookReversePath right left := hpathFull }

/-- The canonical bundled common corner in reverse orientation. -/
def twoHookReverseCornerWord {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) : Word R :=
  ofStringPath (twoHookReversePath right left)
    ((isString_reverse_iff R (twoHookReversePath right left)).1 (by
      rw [twoHookReversePath_reverse]
      exact hpath))

/-- The replayed left corner is the canonical reverse-oriented two-hook
word. -/
theorem TwoHookLeftCorner.reverseCorner_eq_twoHookReverseCornerWord
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (corner : TwoHookLeftCorner right left) :
    corner.reverseCorner = twoHookReverseCornerWord right left hpath := by
  apply Word.ext
  · exact corner.source_eq
  · exact corner.target_eq
  · exact HEq.trans
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        corner.source_eq corner.target_eq corner.reverseCorner.path).symm
      (heq_of_eq corner.path_cast_eq)

/-- The two canonical orientations of the common corner are reversals of
one another. -/
theorem twoHookReverseCornerWord_reverse {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    (twoHookReverseCornerWord right left hpath).reverse =
      twoHookCornerWord right left hpath := by
  apply Word.ext
  · rfl
  · rfl
  · exact heq_of_eq (twoHookReversePath_reverse right left)

/-- The left replay has the same forward-oriented result as the canonical
two-hook corner. -/
theorem TwoHookLeftCorner.result_eq_twoHookCornerWord
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (corner : TwoHookLeftCorner right left) :
    corner.extension.result = twoHookCornerWord right left hpath := by
  rw [LeftPositiveBoundaryExtension.result, corner.reverseResult_eq,
    corner.reverseCorner_eq_twoHookReverseCornerWord right left hpath,
    twoHookReverseCornerWord_reverse]

/-- Hooks at both ends of a nonempty word form a coherent positive-boundary
square with the canonical two-hook word as common corner. -/
def twoHookSquare {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    PositiveBoundarySquare C := by
  let rightCorner := twoHookRightCorner right left hpath
  let leftCorner := twoHookLeftCorner right left hpath
  have hrightCorner :
      rightCorner.corner = twoHookCornerWord right left hpath :=
    rightCorner.corner_eq_twoHookCornerWord right left hpath
  have hleftCorner :
      leftCorner.extension.result = twoHookCornerWord right left hpath :=
    leftCorner.result_eq_twoHookCornerWord right left hpath
  have hcorner : rightCorner.corner = leftCorner.extension.result :=
    hrightCorner.trans hleftCorner.symm
  let cornerRight :
      PositiveBoundaryExtension left.result leftCorner.extension.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ PositiveBoundaryExtension left.result W)
        hcorner)
      rightCorner.extension
  exact PositiveBoundarySquare.ofExtensions
    right.toPositiveBoundaryExtension
    left.toLeftPositiveBoundaryExtension
    leftCorner.extension cornerRight (by
      simpa only [LeftPositiveBoundaryExtension.steps,
        LeftHookExtension.toLeftPositiveBoundaryExtension,
        HookExtension.toPositiveBoundaryExtension,
        PositiveBoundaryExtension.toRightExtension_steps,
        NegativeExtension.toRightExtension_steps,
        LeftHookExtension.steps, HookExtension.steps] using
        leftCorner.steps_eq)

/-- The canonical two-hook square gives an exact short complex of string
modules. -/
theorem twoHookSquare_shortComplex_exact {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R) :
    ((twoHookSquare right left hpath).shortComplex hmono).Exact :=
  PositiveBoundarySquare.shortComplex_exact
    (twoHookSquare right left hpath) hmono

/-- The canonical two-hook square for a positive-length base word. -/
def twoHookSquareOfPositiveLength {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) (hC : 0 < C.length) :
    PositiveBoundarySquare C :=
  twoHookSquare right left (twoHookPath_isString right left hC)

/-- The canonical two-hook square at a length-zero word whose two signed
boundary letters do not cancel. -/
def twoHookSquareOfLengthZero {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) (hC : C.length = 0)
    (hboundary : ¬ HEq (positiveArrow right.arrow)
      (Quiver.reverse (negativeArrow left.hook.arrow))) :
    PositiveBoundarySquare C :=
  twoHookSquare right left
    (twoHookPath_isString_of_length_zero right left hC hboundary)

/-- The positive-length two-hook square gives an exact canonical short
complex. -/
theorem twoHookSquareOfPositiveLength_shortComplex_exact
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) (hC : 0 < C.length)
    (hmono : IsMonomial R) :
    ((twoHookSquareOfPositiveLength right left hC).shortComplex hmono).Exact :=
  twoHookSquare_shortComplex_exact right left
    (twoHookPath_isString right left hC) hmono

/-- The noncancelling length-zero two-hook square gives an exact canonical
short complex. -/
theorem twoHookSquareOfLengthZero_shortComplex_exact
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C) (hC : C.length = 0)
    (hboundary : ¬ HEq (positiveArrow right.arrow)
      (Quiver.reverse (negativeArrow left.hook.arrow)))
    (hmono : IsMonomial R) :
    ((twoHookSquareOfLengthZero right left hC hboundary).shortComplex
      hmono).Exact :=
  twoHookSquare_shortComplex_exact right left
    (twoHookPath_isString_of_length_zero right left hC hboundary) hmono

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
