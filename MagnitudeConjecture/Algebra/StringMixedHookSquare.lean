import MagnitudeConjecture.Algebra.StringCohookDeletion
import MagnitudeConjecture.Algebra.StringMixedBoundarySquare

/-!
# Restricting a hook across a left cohook deletion

This file supplies the word-combinatorics part of the asymmetric
Butler--Ringel square.  A negative left-boundary extension and a positive
right-boundary extension have a common subword obtained by deleting the left
extension while retaining the complete right suffix.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- The shorter base path, with its right endpoint cast to the endpoint of a
negative left extension. -/
def mixedBasePath {D : Word R} (left : LeftNegativeBoundaryExtension D) :
    SignedPath D.source left.result.target :=
  @Quiver.Path.cast (Quiver.Symmetrify Q)
    (Quiver.symmetrifyQuiver Q)
    D.source D.target D.source left.result.target rfl
    left.extension.toRightExtension.source_eq.symm D.path

/-- Endpoint casting preserves the string condition on the shorter base. -/
theorem mixedBasePath_isString {D : Word R}
    (left : LeftNegativeBoundaryExtension D) :
    IsString R (mixedBasePath left) := by
  exact (isString_cast R rfl
    left.extension.toRightExtension.source_eq.symm D.path).2 D.isString

/-- Delete the negative left extension while retaining an arbitrary positive
right-boundary suffix. -/
def mixedRestrictedPath {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    SignedPath D.source corner.target :=
  (mixedBasePath left).comp
    cornerRight.toRightExtension.suffixPath

/-- The mixed restricted path is a contiguous subpath of the common corner,
so it is automatically a string. -/
theorem mixedRestrictedPath_isString {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    IsString R (mixedRestrictedPath left cornerRight) := by
  have hambient :=
    cornerRight.toRightExtension.comp_suffixPath_isString
  apply IsString.of_contiguousSubpath R hambient
  refine ⟨left.prefixPath, Quiver.Path.nil, ?_⟩
  rw [left.path_eq_prefixPath_comp_cast]
  simp only [mixedRestrictedPath, mixedBasePath, Quiver.Path.comp_nil,
    Quiver.Path.comp_assoc]

/-- Rebase the complete positive boundary after deleting the left prefix. -/
def mixedRightReplay {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    PositiveBoundaryExtension.RebaseResult cornerRight
      (mixedBasePath left) (mixedBasePath_isString left) :=
  cornerRight.rebase (mixedBasePath left) (mixedBasePath_isString left)
    (mixedRestrictedPath_isString left cornerRight)

/-- Bundling the cast shorter path gives the original shorter word. -/
theorem mixedBaseWord_eq {D : Word R}
    (left : LeftNegativeBoundaryExtension D) :
    ofStringPath (mixedBasePath left) (mixedBasePath_isString left) = D := by
  apply Word.ext
  · rfl
  · exact left.extension.toRightExtension.source_eq
  · exact @Quiver.Path.cast_heq (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ _ rfl
      left.extension.toRightExtension.source_eq.symm D.path

/-- The positive-boundary extension of the shortened word obtained by
retaining the original complete right suffix. -/
def mixedRightExtension {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    PositiveBoundaryExtension D (mixedRightReplay left cornerRight).result :=
  Eq.mp
    (congrArg
      (fun W : Word R ↦ PositiveBoundaryExtension W
        (mixedRightReplay left cornerRight).result)
      (mixedBaseWord_eq left))
    (mixedRightReplay left cornerRight).rebased

/-- Restricting across the left prefix preserves the number of right-added
letters. -/
@[simp]
theorem mixedRightExtension_steps {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    (mixedRightExtension left cornerRight).toRightExtension.steps =
      cornerRight.toRightExtension.steps := by
  calc
    _ = (mixedRightReplay left cornerRight).rebased.toRightExtension.steps :=
      PositiveBoundaryExtension.toRightExtension_steps_transport_source
        (mixedBaseWord_eq left) (mixedRightReplay left cornerRight).rebased
    _ = cornerRight.toRightExtension.steps := by
      exact PositiveBoundaryExtension.rebase_steps cornerRight
        (mixedBasePath left) (mixedBasePath_isString left)
        (mixedRestrictedPath_isString left cornerRight)

/-- Reverse the restricted right-hook word before replaying the original
negative left boundary in reverse orientation. -/
def mixedReverseBasePath {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    SignedPath corner.target D.source :=
  (mixedRestrictedPath left cornerRight).reverse

/-- The reversed restricted word is again a string. -/
theorem mixedReverseBasePath_isString {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    IsString R (mixedReverseBasePath left cornerRight) := by
  exact (isString_reverse_iff R (mixedRestrictedPath left cornerRight)).2
    (mixedRestrictedPath_isString left cornerRight)

/-- The reversed restricted word followed by the original negative-boundary
suffix. -/
def mixedReverseFullPath {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    SignedPath corner.target left.reverseResult.target :=
  (mixedReverseBasePath left cornerRight).comp
    left.extension.toRightExtension.suffixPath

/-- The explicit reverse full path is the reverse of the original common
corner path written as base plus right suffix. -/
theorem mixedReverseFullPath_eq {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    mixedReverseFullPath left cornerRight =
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
    mixedReverseFullPath left cornerRight =
        (cornerRight.toRightExtension.suffixPath.reverse.comp
          (mixedBasePath left).reverse).comp
            left.extension.toRightExtension.suffixPath := by
      simp only [mixedReverseFullPath, mixedReverseBasePath,
        mixedRestrictedPath, Quiver.Path.reverse_comp]
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
theorem mixedReverseFullPath_isString {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    IsString R (mixedReverseFullPath left cornerRight) := by
  rw [mixedReverseFullPath_eq]
  exact (isString_reverse_iff R
    (left.result.path.comp cornerRight.toRightExtension.suffixPath)).2
    cornerRight.toRightExtension.comp_suffixPath_isString

/-- The explicit reversed restricted word is the reversal of the replayed
right-result word. -/
theorem mixedReverseBaseWord_eq_rightReverse {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    ofStringPath (mixedReverseBasePath left cornerRight)
        (mixedReverseBasePath_isString left cornerRight) =
      (mixedRightReplay left cornerRight).result.reverse := by
  let replay := mixedRightReplay left cornerRight
  have hreverse := congrArg Quiver.Path.reverse replay.path_cast_eq
  rw [path_reverse_cast] at hreverse
  apply Word.ext
  · exact replay.target_eq.symm
  · exact replay.source_eq.symm
  · exact HEq.trans (heq_of_eq hreverse.symm)
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        replay.target_eq replay.source_eq replay.result.path.reverse)

/-- Replay the original negative left boundary after the reversed restricted
right-result word. -/
def mixedLeftReplay {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    NegativeBoundaryExtension.RebaseResult left.extension
      (mixedReverseBasePath left cornerRight)
      (mixedReverseBasePath_isString left cornerRight) :=
  left.extension.rebase (mixedReverseBasePath left cornerRight)
    (mixedReverseBasePath_isString left cornerRight)
    (mixedReverseFullPath_isString left cornerRight)

/-- The negative left-boundary extension of the replayed right-result word. -/
def mixedCornerLeftExtension {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    LeftNegativeBoundaryExtension (mixedRightReplay left cornerRight).result where
  reverseResult := (mixedLeftReplay left cornerRight).result
  extension := Eq.mp
    (congrArg
      (fun W : Word R ↦ NegativeBoundaryExtension W
        (mixedLeftReplay left cornerRight).result)
      (mixedReverseBaseWord_eq_rightReverse left cornerRight))
    (mixedLeftReplay left cornerRight).rebased

/-- The replayed negative boundary adds the same number of letters as the
original negative left boundary. -/
@[simp]
theorem mixedCornerLeftExtension_steps {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    (mixedCornerLeftExtension left cornerRight).steps = left.steps := by
  calc
    (mixedCornerLeftExtension left cornerRight).steps =
        (mixedLeftReplay left cornerRight).rebased.toRightExtension.steps :=
      NegativeBoundaryExtension.toRightExtension_steps_transport_source
        (mixedReverseBaseWord_eq_rightReverse left cornerRight)
        (mixedLeftReplay left cornerRight).rebased
    _ = left.extension.toRightExtension.steps := by
      exact NegativeBoundaryExtension.rebase_steps left.extension
        (mixedReverseBasePath left cornerRight)
        (mixedReverseBasePath_isString left cornerRight)
        (mixedReverseFullPath_isString left cornerRight)

/-- The second replay recovers the original common corner in forward
orientation. -/
theorem mixedCornerLeftExtension_result {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    (mixedCornerLeftExtension left cornerRight).result = corner := by
  let replay := mixedLeftReplay left cornerRight
  have hreverse := congrArg Quiver.Path.reverse replay.path_cast_eq
  rw [path_reverse_cast] at hreverse
  have hfullReverse := congrArg Quiver.Path.reverse
    (mixedReverseFullPath_eq left cornerRight)
  have hambientReverseReverse :
      (left.result.path.comp
        cornerRight.toRightExtension.suffixPath).reverse.reverse =
      left.result.path.comp cornerRight.toRightExtension.suffixPath :=
    @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _
      (left.result.path.comp cornerRight.toRightExtension.suffixPath)
  have hmiddle :
      (mixedReverseFullPath left cornerRight).reverse =
        left.result.path.comp cornerRight.toRightExtension.suffixPath :=
    hfullReverse.trans hambientReverseReverse
  have hcorner :=
    cornerRight.toRightExtension.path_cast_comp_suffixPath
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

/-- A negative left extension followed by a positive right extension forms
the coherent mixed boundary square obtained by restricting and replaying both
suffixes. -/
def mixedBoundarySquare {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner) :
    MixedBoundarySquare D := by
  let cornerLeft := mixedCornerLeftExtension left cornerRight
  have hcorner : cornerLeft.result = corner :=
    mixedCornerLeftExtension_result left cornerRight
  let transportedCornerRight :
      PositiveBoundaryExtension left.result cornerLeft.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ PositiveBoundaryExtension left.result W)
        hcorner.symm)
      cornerRight
  exact MixedBoundarySquare.ofExtensions
    (mixedRightExtension left cornerRight) left cornerLeft
    transportedCornerRight (mixedCornerLeftExtension_steps left cornerRight)

/-- The replayed mixed boundary square has an exact canonical short
complex. -/
theorem mixedBoundarySquare_shortComplex_exact {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : PositiveBoundaryExtension left.result corner)
    (hmono : IsMonomial R) :
    ((mixedBoundarySquare left cornerRight).shortComplex hmono).Exact :=
  MixedBoundarySquare.shortComplex_exact
    (mixedBoundarySquare left cornerRight) hmono

/-- The mixed square attached to an actual left cohook deletion and a right
hook of the original word. -/
def leftCohookDeletionRightHookSquare {C D corner : Word R}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner) : MixedBoundarySquare D := by
  let left := deletion.toLeftNegativeBoundaryExtension
  have hleft : left.result = C :=
    deletion.toLeftNegativeBoundaryExtension_result
  let cornerRight : PositiveBoundaryExtension left.result corner :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ PositiveBoundaryExtension W corner)
        hleft.symm)
      right.toPositiveBoundaryExtension
  exact mixedBoundarySquare left cornerRight

/-- A left cohook deletion and a right hook give the asymmetric canonical
exact complex. -/
theorem leftCohookDeletionRightHookSquare_shortComplex_exact
    {C D corner : Word R}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner)
    (hmono : IsMonomial R) :
    ((leftCohookDeletionRightHookSquare deletion right).shortComplex
      hmono).Exact :=
  MixedBoundarySquare.shortComplex_exact
    (leftCohookDeletionRightHookSquare deletion right) hmono

/-- The opposite asymmetric case, expressed on reversed words: a right
cohook deletion becomes a left cohook deletion and a left hook becomes its
stored right hook. -/
def rightCohookDeletionLeftHookReverseSquare {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) : MixedBoundarySquare D.reverse :=
  leftCohookDeletionRightHookSquare
    deletion.toReverseLeftCohookDeletion left.hook

/-- The reversed square for a right cohook deletion and a left hook has an
exact canonical short complex.  This is the intermediate exactness result
transported back to the original orientation below. -/
theorem rightCohookDeletionLeftHookReverseSquare_shortComplex_exact
    {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C)
    (hmono : IsMonomial R) :
    ((rightCohookDeletionLeftHookReverseSquare deletion left).shortComplex
      hmono).Exact :=
  MixedBoundarySquare.shortComplex_exact
    (rightCohookDeletionLeftHookReverseSquare deletion left) hmono

/-- The common corner of the reversed asymmetric square is the stored result
of the original left hook. -/
@[simp]
theorem rightCohookDeletionLeftHookReverseSquare_corner
    {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) :
    (rightCohookDeletionLeftHookReverseSquare deletion left).corner =
      left.reverseResult := by
  simp only [rightCohookDeletionLeftHookReverseSquare,
    leftCohookDeletionRightHookSquare, mixedBoundarySquare,
    MixedBoundarySquare.corner]
  exact mixedCornerLeftExtension_result _ _

/-- The target of the reversed asymmetric square is the reverse of the
original word. -/
@[simp]
theorem rightCohookDeletionLeftHookReverseSquare_left_result
    {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) :
    (rightCohookDeletionLeftHookReverseSquare deletion left).left.result =
      C.reverse := by
  simp only [rightCohookDeletionLeftHookReverseSquare,
    leftCohookDeletionRightHookSquare, mixedBoundarySquare]
  exact deletion.toReverseLeftCohookDeletion
    |>.toLeftNegativeBoundaryExtension_result

/-- The source word of the right-cohook/left-hook sequence, returned to the
original orientation. -/
def rightCohookDeletionLeftHookSourceWord {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) : Word R :=
  (rightCohookDeletionLeftHookReverseSquare deletion left).rightResult.reverse

/-- Reversing the square corner recovers the original left-hook result. -/
theorem rightCohookDeletionLeftHookReverseCorner_eq_result
    {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) :
    (rightCohookDeletionLeftHookReverseSquare deletion left).corner.reverse =
      left.result := by
  exact congrArg (fun W : Word R ↦ W.reverse)
    (rightCohookDeletionLeftHookReverseSquare_corner deletion left)

/-- Reversing the square target recovers the original word. -/
theorem rightCohookDeletionLeftHookReverseTarget_eq
    {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) :
    (rightCohookDeletionLeftHookReverseSquare deletion left).left.result.reverse =
      C := by
  exact (congrArg (fun W : Word R ↦ W.reverse)
    (rightCohookDeletionLeftHookReverseSquare_left_result deletion left)).trans
      (reverse_reverse R C)

/-- Reversal identifies the source of the reversed square with the source
word in the original orientation. -/
def rightCohookDeletionLeftHookSourceIso {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :
    (rightCohookDeletionLeftHookReverseSquare deletion left).rightResult.rightModule
        hmono ≅
      (rightCohookDeletionLeftHookSourceWord deletion left).rightModule hmono :=
  reverseRightModuleIso
    (rightCohookDeletionLeftHookReverseSquare deletion left).rightResult hmono

/-- Reversal identifies the two middle terms with the shortened word and the
original left-hook result. -/
def rightCohookDeletionLeftHookMiddleIso {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :
    D.reverse.rightModule hmono ⊞
        (rightCohookDeletionLeftHookReverseSquare deletion left).corner.rightModule
          hmono ≅
      D.rightModule hmono ⊞ left.result.rightModule hmono :=
  biprod.mapIso
    (reverseRightModuleIso D hmono).symm
    ((reverseRightModuleIso
      (rightCohookDeletionLeftHookReverseSquare deletion left).corner hmono).trans
      (eqToIso (congrArg (fun W : Word R ↦ W.rightModule hmono)
        (rightCohookDeletionLeftHookReverseCorner_eq_result deletion left))))

/-- Reversal identifies the target of the reversed square with the original
word. -/
def rightCohookDeletionLeftHookTargetIso {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :
    (rightCohookDeletionLeftHookReverseSquare deletion left).left.result.rightModule
        hmono ≅ C.rightModule hmono :=
  (reverseRightModuleIso
    (rightCohookDeletionLeftHookReverseSquare deletion left).left.result hmono).trans
    (eqToIso (congrArg (fun W : Word R ↦ W.rightModule hmono)
      (rightCohookDeletionLeftHookReverseTarget_eq deletion left)))

/-- The complete right-cohook/left-hook canonical complex in the original
right-module orientation.  Both differentials are transported, together with
all three objects, through the canonical word-reversal isomorphisms. -/
def rightCohookDeletionLeftHookShortComplex {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :
    ShortComplex ((Category R)ᵒᵖ ⥤ ModuleCat.{u} k) :=
  let square := rightCohookDeletionLeftHookReverseSquare deletion left
  let e₁ := rightCohookDeletionLeftHookSourceIso deletion left hmono
  let e₂ := rightCohookDeletionLeftHookMiddleIso deletion left hmono
  let e₃ := rightCohookDeletionLeftHookTargetIso deletion left hmono
  ShortComplex.mk
    (e₁.inv ≫ square.toMiddleMap hmono ≫ e₂.hom)
    (e₂.inv ≫ square.fromMiddleMap hmono ≫ e₃.hom) (by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [square.toMiddleMap_fromMiddleMap_assoc]
      simp)

/-- The original-orientation canonical complex is isomorphic to the exact
reversed mixed square. -/
def rightCohookDeletionLeftHookShortComplexIso {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :
    (rightCohookDeletionLeftHookReverseSquare deletion left).shortComplex hmono ≅
      rightCohookDeletionLeftHookShortComplex deletion left hmono := by
  refine ShortComplex.isoMk
    (rightCohookDeletionLeftHookSourceIso deletion left hmono)
    (rightCohookDeletionLeftHookMiddleIso deletion left hmono)
    (rightCohookDeletionLeftHookTargetIso deletion left hmono) ?_ ?_
  · dsimp [rightCohookDeletionLeftHookShortComplex,
      MixedBoundarySquare.shortComplex]
    rw [Iso.hom_inv_id_assoc]
  · dsimp [rightCohookDeletionLeftHookShortComplex,
      MixedBoundarySquare.shortComplex]
    rw [Iso.hom_inv_id_assoc]

/-- A right cohook deletion and a left hook give the asymmetric canonical
exact complex in the original right-module orientation. -/
theorem rightCohookDeletionLeftHookShortComplex_exact {C D : Word R}
    (deletion : CohookDeletion C D)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :
    (rightCohookDeletionLeftHookShortComplex deletion left hmono).Exact :=
  ShortComplex.exact_of_iso
    (rightCohookDeletionLeftHookShortComplexIso deletion left hmono)
    (rightCohookDeletionLeftHookReverseSquare_shortComplex_exact
      deletion left hmono)

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
