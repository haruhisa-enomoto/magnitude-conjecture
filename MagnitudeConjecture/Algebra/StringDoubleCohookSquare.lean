import MagnitudeConjecture.Algebra.StringMixedHookSquare
import MagnitudeConjecture.Algebra.StringNegativeBoundarySquare

/-!
# Constructing the double-cohook common corner

Starting with a negative left-boundary extension and then a negative
right-boundary extension, this file restricts and replays the two suffixes to
construct the other one-ended word.  Both routes recover the same common
corner, giving the literal double-cohook Butler--Ringel square.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- Delete the negative left extension while retaining the negative right
suffix of the common corner. -/
def doubleCohookRestrictedPath {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    SignedPath D.source corner.target :=
  (mixedBasePath left).comp cornerRight.toRightExtension.suffixPath

/-- The restricted path is a contiguous subpath of the common corner. -/
theorem doubleCohookRestrictedPath_isString {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    IsString R (doubleCohookRestrictedPath left cornerRight) := by
  have hambient := cornerRight.toRightExtension.comp_suffixPath_isString
  apply IsString.of_contiguousSubpath R hambient
  refine ⟨left.prefixPath, Quiver.Path.nil, ?_⟩
  rw [left.path_eq_prefixPath_comp_cast]
  simp only [doubleCohookRestrictedPath, mixedBasePath,
    Quiver.Path.comp_nil, Quiver.Path.comp_assoc]

/-- Rebase the complete negative right boundary after deleting the left
prefix. -/
def doubleCohookRightReplay {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    NegativeBoundaryExtension.RebaseResult cornerRight
      (mixedBasePath left) (mixedBasePath_isString left) :=
  cornerRight.rebase (mixedBasePath left) (mixedBasePath_isString left)
    (doubleCohookRestrictedPath_isString left cornerRight)

/-- The negative right-boundary extension of the shortened core obtained by
retaining the original right cohook. -/
def doubleCohookRightExtension {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    NegativeBoundaryExtension D
      (doubleCohookRightReplay left cornerRight).result :=
  Eq.mp
    (congrArg
      (fun W : Word R ↦ NegativeBoundaryExtension W
        (doubleCohookRightReplay left cornerRight).result)
      (mixedBaseWord_eq left))
    (doubleCohookRightReplay left cornerRight).rebased

/-- Restricting across the left prefix preserves the number of right-added
letters. -/
@[simp]
theorem doubleCohookRightExtension_steps {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    (doubleCohookRightExtension left cornerRight).toRightExtension.steps =
      cornerRight.toRightExtension.steps := by
  calc
    _ = (doubleCohookRightReplay left cornerRight).rebased.toRightExtension.steps :=
      NegativeBoundaryExtension.toRightExtension_steps_transport_source
        (mixedBaseWord_eq left) (doubleCohookRightReplay left cornerRight).rebased
    _ = cornerRight.toRightExtension.steps := by
      exact NegativeBoundaryExtension.rebase_steps cornerRight
        (mixedBasePath left) (mixedBasePath_isString left)
        (doubleCohookRestrictedPath_isString left cornerRight)

/-- Reverse the restricted right-cohook word before replaying the original
negative left boundary. -/
def doubleCohookReverseBasePath {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    SignedPath corner.target D.source :=
  (doubleCohookRestrictedPath left cornerRight).reverse

/-- The reversed restricted word is again a string. -/
theorem doubleCohookReverseBasePath_isString {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    IsString R (doubleCohookReverseBasePath left cornerRight) := by
  exact (isString_reverse_iff R
    (doubleCohookRestrictedPath left cornerRight)).2
      (doubleCohookRestrictedPath_isString left cornerRight)

/-- The reversed restricted word followed by the original negative left
boundary suffix. -/
def doubleCohookReverseFullPath {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    SignedPath corner.target left.reverseResult.target :=
  (doubleCohookReverseBasePath left cornerRight).comp
    left.extension.toRightExtension.suffixPath

/-- The explicit reverse full path is the reverse of the original common
corner path. -/
theorem doubleCohookReverseFullPath_eq {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    doubleCohookReverseFullPath left cornerRight =
      (left.result.path.comp
        cornerRight.toRightExtension.suffixPath).reverse := by
  have hprefixReverse : left.prefixPath.reverse =
      left.extension.toRightExtension.suffixPath := by
    change left.extension.toRightExtension.suffixPath.reverse.reverse =
      left.extension.toRightExtension.suffixPath
    exact @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _
      left.extension.toRightExtension.suffixPath
  have hleftReverse := congrArg Quiver.Path.reverse
    left.path_eq_prefixPath_comp_cast
  simp only [Quiver.Path.reverse_comp] at hleftReverse
  calc
    doubleCohookReverseFullPath left cornerRight =
        (cornerRight.toRightExtension.suffixPath.reverse.comp
          (mixedBasePath left).reverse).comp
            left.extension.toRightExtension.suffixPath := by
      simp only [doubleCohookReverseFullPath,
        doubleCohookReverseBasePath, doubleCohookRestrictedPath,
        Quiver.Path.reverse_comp]
    _ = cornerRight.toRightExtension.suffixPath.reverse.comp
        ((mixedBasePath left).reverse.comp
          left.extension.toRightExtension.suffixPath) :=
      Quiver.Path.comp_assoc _ _ _
    _ = cornerRight.toRightExtension.suffixPath.reverse.comp
        ((mixedBasePath left).reverse.comp left.prefixPath.reverse) := by
      rw [hprefixReverse]
      rfl
    _ = cornerRight.toRightExtension.suffixPath.reverse.comp
        left.result.path.reverse := by
      exact congrArg
        (fun p ↦ cornerRight.toRightExtension.suffixPath.reverse.comp p)
        hleftReverse.symm
    _ = (left.result.path.comp
        cornerRight.toRightExtension.suffixPath).reverse := by
      exact (Quiver.Path.reverse_comp _ _).symm

/-- The reverse full path used for the second replay is a string. -/
theorem doubleCohookReverseFullPath_isString {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    IsString R (doubleCohookReverseFullPath left cornerRight) := by
  rw [doubleCohookReverseFullPath_eq]
  exact (isString_reverse_iff R
    (left.result.path.comp cornerRight.toRightExtension.suffixPath)).2
      cornerRight.toRightExtension.comp_suffixPath_isString

/-- The reversed restricted word is the reversal of the replayed right-result
word. -/
theorem doubleCohookReverseBaseWord_eq_rightReverse
    {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    ofStringPath (doubleCohookReverseBasePath left cornerRight)
        (doubleCohookReverseBasePath_isString left cornerRight) =
      (doubleCohookRightReplay left cornerRight).result.reverse := by
  let replay := doubleCohookRightReplay left cornerRight
  have hreverse := congrArg Quiver.Path.reverse replay.path_cast_eq
  rw [path_reverse_cast] at hreverse
  apply Word.ext
  · exact replay.target_eq.symm
  · exact replay.source_eq.symm
  · exact HEq.trans (heq_of_eq hreverse.symm)
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        replay.target_eq replay.source_eq replay.result.path.reverse)

/-- Replay the original negative left boundary after the restricted right
cohook word in reverse orientation. -/
def doubleCohookLeftReplay {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    NegativeBoundaryExtension.RebaseResult left.extension
      (doubleCohookReverseBasePath left cornerRight)
      (doubleCohookReverseBasePath_isString left cornerRight) :=
  left.extension.rebase (doubleCohookReverseBasePath left cornerRight)
    (doubleCohookReverseBasePath_isString left cornerRight)
    (doubleCohookReverseFullPath_isString left cornerRight)

/-- The negative left-boundary extension of the replayed right-cohook word. -/
def doubleCohookCornerLeftExtension {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    LeftNegativeBoundaryExtension
      (doubleCohookRightReplay left cornerRight).result where
  reverseResult := (doubleCohookLeftReplay left cornerRight).result
  extension := Eq.mp
    (congrArg
      (fun W : Word R ↦ NegativeBoundaryExtension W
        (doubleCohookLeftReplay left cornerRight).result)
      (doubleCohookReverseBaseWord_eq_rightReverse left cornerRight))
    (doubleCohookLeftReplay left cornerRight).rebased

/-- The replayed negative left boundary has its original length. -/
@[simp]
theorem doubleCohookCornerLeftExtension_steps {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    (doubleCohookCornerLeftExtension left cornerRight).steps = left.steps := by
  calc
    (doubleCohookCornerLeftExtension left cornerRight).steps =
        (doubleCohookLeftReplay left cornerRight).rebased.toRightExtension.steps :=
      NegativeBoundaryExtension.toRightExtension_steps_transport_source
        (doubleCohookReverseBaseWord_eq_rightReverse left cornerRight)
        (doubleCohookLeftReplay left cornerRight).rebased
    _ = left.extension.toRightExtension.steps := by
      exact NegativeBoundaryExtension.rebase_steps left.extension
        (doubleCohookReverseBasePath left cornerRight)
        (doubleCohookReverseBasePath_isString left cornerRight)
        (doubleCohookReverseFullPath_isString left cornerRight)

/-- The second replay recovers the original two-cohook corner. -/
theorem doubleCohookCornerLeftExtension_result {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    (doubleCohookCornerLeftExtension left cornerRight).result = corner := by
  let replay := doubleCohookLeftReplay left cornerRight
  have hreverse := congrArg Quiver.Path.reverse replay.path_cast_eq
  rw [path_reverse_cast] at hreverse
  have hfullReverse := congrArg Quiver.Path.reverse
    (doubleCohookReverseFullPath_eq left cornerRight)
  have hambientReverseReverse :
      (left.result.path.comp
        cornerRight.toRightExtension.suffixPath).reverse.reverse =
      left.result.path.comp cornerRight.toRightExtension.suffixPath :=
    @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _
      (left.result.path.comp cornerRight.toRightExtension.suffixPath)
  have hmiddle :
      (doubleCohookReverseFullPath left cornerRight).reverse =
        left.result.path.comp cornerRight.toRightExtension.suffixPath :=
    hfullReverse.trans hambientReverseReverse
  have hcorner := cornerRight.toRightExtension.path_cast_comp_suffixPath
  have hcastEq :
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        replay.result.target replay.result.source
        left.reverseResult.target corner.target
        replay.target_eq replay.source_eq replay.result.path.reverse) =
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        corner.source corner.target left.result.source corner.target
        cornerRight.toRightExtension.source_eq rfl corner.path) :=
    hreverse.trans (hmiddle.trans hcorner.symm)
  apply Word.ext
  · exact replay.target_eq.trans
      cornerRight.toRightExtension.source_eq.symm
  · exact replay.source_eq
  · exact HEq.trans
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        replay.target_eq replay.source_eq replay.result.path.reverse).symm
      (HEq.trans (heq_of_eq hcastEq)
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          cornerRight.toRightExtension.source_eq rfl corner.path))

/-- A negative extension at each endpoint forms the coherent double-cohook
boundary square obtained by restricting and replaying both suffixes. -/
def doubleCohookBoundarySquare {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner) :
    NegativeBoundarySquare D := by
  let cornerLeft := doubleCohookCornerLeftExtension left cornerRight
  have hcorner : cornerLeft.result = corner :=
    doubleCohookCornerLeftExtension_result left cornerRight
  let transportedCornerRight :
      NegativeBoundaryExtension left.result cornerLeft.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ NegativeBoundaryExtension left.result W)
        hcorner.symm)
      cornerRight
  exact NegativeBoundarySquare.ofExtensions
    (doubleCohookRightExtension left cornerRight) left cornerLeft
    transportedCornerRight (doubleCohookCornerLeftExtension_steps left cornerRight)

/-- The replayed double-cohook boundary square has an exact canonical short
complex. -/
theorem doubleCohookBoundarySquare_shortComplex_exact
    {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : NegativeBoundaryExtension left.result corner)
    (hmono : IsMonomial R) :
    ((doubleCohookBoundarySquare left cornerRight).shortComplex hmono).Exact :=
  NegativeBoundarySquare.shortComplex_exact
    (doubleCohookBoundarySquare left cornerRight) hmono

/-- The double-cohook square attached to a left cohook of the core followed
by a right cohook of the resulting one-sided word. -/
def doubleCohookDeletionSquare {C L D : Word R}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L) : NegativeBoundarySquare D := by
  let left := leftDeletion.toLeftNegativeBoundaryExtension
  have hleft : left.result = L :=
    leftDeletion.toLeftNegativeBoundaryExtension_result
  let cornerRight : NegativeBoundaryExtension left.result C :=
    Eq.mp
      (congrArg (fun W : Word R ↦ NegativeBoundaryExtension W C) hleft.symm)
      rightDeletion.cohook.toNegativeBoundaryExtension
  exact doubleCohookBoundarySquare left cornerRight

/-- Two successive endpoint cohook deletions give the literal p. 172
canonical exact complex in right-module orientation. -/
theorem doubleCohookDeletionSquare_shortComplex_exact
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L)
    (hmono : IsMonomial R) :
    ((doubleCohookDeletionSquare leftDeletion rightDeletion).shortComplex
      hmono).Exact :=
  NegativeBoundarySquare.shortComplex_exact
    (doubleCohookDeletionSquare leftDeletion rightDeletion) hmono

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
