import MagnitudeConjecture.Algebra.StringFiniteBoundaryIrreducible
import MagnitudeConjecture.Algebra.StringHookCohookReplay
import MagnitudeConjecture.Algebra.StringMixedHookSquare

/-!
# Irreducible mixed hook--cohook boundary sequences

The generic mixed boundary square retains only the signs of its four
boundary maps.  Here an actual left cohook deletion and right hook are
replayed with their maximal arms intact, so all four maps are literal hook
or cohook maps.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q} [Fintype Q]

omit [Fintype Q] in
/-- A left cohook deletion is literally the left cohook extension which
reattaches the deleted prefix. -/
def LeftCohookDeletion.toLeftCohookExtension {C D : Word R}
    (deletion : LeftCohookDeletion C D) : LeftCohookExtension D where
  reverseResult := C.reverse
  cohook := deletion.cohook

omit [Fintype Q] in
@[simp]
theorem LeftCohookDeletion.toLeftCohookExtension_result
    {C D : Word R} (deletion : LeftCohookDeletion C D) :
    deletion.toLeftCohookExtension.result = C :=
  reverse_reverse R C

omit [Fintype Q] in
/-- Sign-preserving replay of the right hook after deleting the left
cohook prefix. -/
def mixedRightHookReplay {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : HookExtension left.result corner) :
    HookExtension.RebaseResult cornerRight
      (mixedBasePath left) (mixedBasePath_isString left) :=
  cornerRight.rebase (mixedBasePath left) (mixedBasePath_isString left)
    (mixedRestrictedPath_isString left
      cornerRight.toPositiveBoundaryExtension)

omit [Fintype Q] in
/-- The sign-preserving hook replay and the generic positive-boundary replay
produce the same word. -/
theorem mixedRightHookReplay_result_eq {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : HookExtension left.result corner) :
    (mixedRightHookReplay left cornerRight).result =
      (mixedRightReplay left
        cornerRight.toPositiveBoundaryExtension).result := by
  let hookReplay := mixedRightHookReplay left cornerRight
  let boundaryReplay := mixedRightReplay left
    cornerRight.toPositiveBoundaryExtension
  apply Word.ext
  · exact hookReplay.source_eq.trans boundaryReplay.source_eq.symm
  · exact hookReplay.target_eq.trans boundaryReplay.target_eq.symm
  · exact HEq.trans
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        hookReplay.source_eq hookReplay.target_eq
        hookReplay.result.path).symm
      (HEq.trans
        (heq_of_eq
          (hookReplay.path_cast_eq.trans boundaryReplay.path_cast_eq.symm))
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          boundaryReplay.source_eq boundaryReplay.target_eq
          boundaryReplay.result.path))

omit [Fintype Q] in
/-- The shortened word carries a literal maximal right hook to the mixed
square's right result. -/
def mixedRightHook {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : HookExtension left.result corner) :
    HookExtension D
      (mixedRightReplay left
        cornerRight.toPositiveBoundaryExtension).result := by
  let replay := mixedRightHookReplay left cornerRight
  let sourceHook : HookExtension D replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension W replay.result)
        (mixedBaseWord_eq left))
      replay.rebased
  exact Eq.mp
    (congrArg (fun W : Word R ↦ HookExtension D W)
    (mixedRightHookReplay_result_eq left cornerRight))
    sourceHook

omit [Fintype Q] in
@[simp]
theorem mixedRightHook_steps {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : HookExtension left.result corner) :
    (mixedRightHook left cornerRight).steps = cornerRight.steps := by
  let replay := mixedRightHookReplay left cornerRight
  let sourceHook : HookExtension D replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension W replay.result)
        (mixedBaseWord_eq left))
      replay.rebased
  let finalHook : HookExtension D
      (mixedRightReplay left
        cornerRight.toPositiveBoundaryExtension).result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension D W)
        (mixedRightHookReplay_result_eq left cornerRight))
      sourceHook
  change finalHook.steps = cornerRight.steps
  calc
    finalHook.steps = sourceHook.steps :=
      HookExtension.steps_transport_result
        (mixedRightHookReplay_result_eq left cornerRight) sourceHook
    _ = replay.rebased.steps :=
      HookExtension.steps_transport_source (mixedBaseWord_eq left)
        replay.rebased
    _ = cornerRight.steps := HookExtension.rebase_steps
      cornerRight (mixedBasePath left) (mixedBasePath_isString left)
      (mixedRestrictedPath_isString left
        cornerRight.toPositiveBoundaryExtension)

omit [Fintype Q] in
/-- Sign-preserving replay of the deleted left cohook after the restricted
right-hook word is reversed. -/
def mixedLeftCohookReplay {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    CohookExtension.RebaseResult leftCohook.cohook
      (mixedReverseBasePath leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toPositiveBoundaryExtension)
      (mixedReverseBasePath_isString
        leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toPositiveBoundaryExtension) :=
  leftCohook.cohook.rebase
    (mixedReverseBasePath leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toPositiveBoundaryExtension)
    (mixedReverseBasePath_isString
      leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toPositiveBoundaryExtension)
    (mixedReverseFullPath_isString
      leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toPositiveBoundaryExtension)

omit [Fintype Q] in
/-- The sign-preserving cohook replay and the generic negative-boundary
replay produce the same reversed corner word. -/
theorem mixedLeftCohookReplay_result_eq {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    (mixedLeftCohookReplay leftCohook cornerRight).result =
      (mixedLeftReplay leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toPositiveBoundaryExtension).result := by
  let cohookReplay := mixedLeftCohookReplay leftCohook cornerRight
  let boundaryReplay := mixedLeftReplay
    leftCohook.toLeftNegativeBoundaryExtension
    cornerRight.toPositiveBoundaryExtension
  apply Word.ext
  · exact cohookReplay.source_eq.trans boundaryReplay.source_eq.symm
  · exact cohookReplay.target_eq.trans boundaryReplay.target_eq.symm
  · exact HEq.trans
      (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) _ _ _ _
        cohookReplay.source_eq cohookReplay.target_eq
        cohookReplay.result.path).symm
      (HEq.trans
        (heq_of_eq
          (cohookReplay.path_cast_eq.trans boundaryReplay.path_cast_eq.symm))
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          boundaryReplay.source_eq boundaryReplay.target_eq
          boundaryReplay.result.path))

omit [Fintype Q] in
/-- The restricted right-hook word carries a literal maximal left cohook to
the common corner. -/
def mixedCornerLeftCohook {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    LeftCohookExtension
      (mixedRightReplay leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toPositiveBoundaryExtension).result := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let replay := mixedLeftCohookReplay leftCohook cornerRight
  let boundaryReplay := mixedLeftReplay left
    cornerRight.toPositiveBoundaryExtension
  let rightReplay := mixedRightReplay left
    cornerRight.toPositiveBoundaryExtension
  let sourceCohook : CohookExtension rightReplay.result.reverse replay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension W replay.result)
        (mixedReverseBaseWord_eq_rightReverse left
          cornerRight.toPositiveBoundaryExtension))
      replay.rebased
  let cornerCohook : CohookExtension rightReplay.result.reverse
      boundaryReplay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension rightReplay.result.reverse W)
        (mixedLeftCohookReplay_result_eq leftCohook cornerRight))
      sourceCohook
  exact {
    reverseResult := boundaryReplay.result
    cohook := cornerCohook }

omit [Fintype Q] in
@[simp]
theorem mixedCornerLeftCohook_result {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    (mixedCornerLeftCohook leftCohook cornerRight).result = corner := by
  change
    (mixedLeftReplay leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toPositiveBoundaryExtension).result.reverse = corner
  exact mixedCornerLeftExtension_result
    leftCohook.toLeftNegativeBoundaryExtension
    cornerRight.toPositiveBoundaryExtension

omit [Fintype Q] in
@[simp]
theorem mixedCornerLeftCohook_steps {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    (mixedCornerLeftCohook leftCohook cornerRight).steps =
      leftCohook.steps := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let replay := mixedLeftCohookReplay leftCohook cornerRight
  let boundaryReplay := mixedLeftReplay left
    cornerRight.toPositiveBoundaryExtension
  let rightReplay := mixedRightReplay left
    cornerRight.toPositiveBoundaryExtension
  let sourceCohook : CohookExtension rightReplay.result.reverse replay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension W replay.result)
        (mixedReverseBaseWord_eq_rightReverse left
          cornerRight.toPositiveBoundaryExtension))
      replay.rebased
  let cornerCohook : CohookExtension rightReplay.result.reverse
      boundaryReplay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension rightReplay.result.reverse W)
        (mixedLeftCohookReplay_result_eq leftCohook cornerRight))
      sourceCohook
  change cornerCohook.steps = leftCohook.cohook.steps
  calc
    cornerCohook.steps = sourceCohook.steps :=
      CohookExtension.steps_transport_result
        (mixedLeftCohookReplay_result_eq leftCohook cornerRight)
        sourceCohook
    _ = replay.rebased.steps :=
      CohookExtension.steps_transport_source
        (mixedReverseBaseWord_eq_rightReverse left
          cornerRight.toPositiveBoundaryExtension) replay.rebased
    _ = leftCohook.cohook.steps := CohookExtension.rebase_steps
      leftCohook.cohook
      (mixedReverseBasePath left
        cornerRight.toPositiveBoundaryExtension)
      (mixedReverseBasePath_isString left
        cornerRight.toPositiveBoundaryExtension)
      (mixedReverseFullPath_isString left
        cornerRight.toPositiveBoundaryExtension)

/-- The mixed boundary square rebuilt from four literal maximal maps: the
replayed right hook, the original left cohook, the replayed left cohook, and
the original right hook. -/
def mixedMaximalSquare {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    MixedBoundarySquare D := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let rightHook := mixedRightHook left cornerRight
  let cornerLeft := mixedCornerLeftCohook leftCohook cornerRight
  have hcorner : cornerLeft.result = corner :=
    mixedCornerLeftCohook_result leftCohook cornerRight
  let transportedCornerRight : HookExtension left.result cornerLeft.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ HookExtension left.result W) hcorner.symm)
      cornerRight
  exact MixedBoundarySquare.ofExtensions
    rightHook.toPositiveBoundaryExtension
    left cornerLeft.toLeftNegativeBoundaryExtension
    transportedCornerRight.toPositiveBoundaryExtension (by
      have hsteps :=
        mixedCornerLeftCohook_steps leftCohook cornerRight
      change cornerLeft.cohook.steps = leftCohook.cohook.steps at hsteps
      change
        cornerLeft.cohook.toNegativeBoundaryExtension.toRightExtension.steps =
          leftCohook.cohook.toNegativeBoundaryExtension.toRightExtension.steps
      simpa only [CohookExtension.toNegativeBoundaryExtension,
        NegativeBoundaryExtension.toRightExtension_steps,
        PositiveExtension.toRightExtension_steps,
        CohookExtension.steps] using hsteps)

omit [Fintype Q] in
/-- The manuscript input of a left cohook deletion and a right hook, rebuilt
as the literal four-maximal-map mixed square. -/
def leftCohookDeletionRightHookMaximalSquare {C D corner : Word R}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner) : MixedBoundarySquare D := by
  let leftCohook := deletion.toLeftCohookExtension
  have hleft : leftCohook.result = C :=
    deletion.toLeftCohookExtension_result
  let transportedRight : HookExtension leftCohook.result corner :=
    Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension W corner) hleft.symm)
      right
  exact mixedMaximalSquare leftCohook transportedRight

/-- The four-maximal-map mixed boundary complex in the finite-dimensional
module category. -/
def mixedMaximalFiniteShortComplex {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner)
    (hmono : IsMonomial R) :=
  (mixedMaximalSquare leftCohook cornerRight).finiteShortComplex hmono

/-- The finite four-maximal-map mixed boundary complex is exact. -/
theorem mixedMaximalFiniteShortComplex_exact {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner)
    (hmono : IsMonomial R) :
    (mixedMaximalFiniteShortComplex leftCohook cornerRight hmono).Exact :=
  MixedBoundarySquare.finiteShortComplex_exact
    (mixedMaximalSquare leftCohook cornerRight) hmono

/-- In the distinct-middle case, the replayed right hook and left cohook
assemble to the irreducible first differential of the mixed sequence. -/
theorem mixedMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (D.finiteRightModule hmono ≅ corner.finiteRightModule hmono)) :
    IsIrreducibleMorphism
      (mixedMaximalFiniteShortComplex leftCohook cornerRight hmono).f := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let rightHook := mixedRightHook left cornerRight
  let cornerLeft := mixedCornerLeftCohook leftCohook cornerRight
  have hmiddle' : ¬ Nonempty
      (D.finiteRightModule hmono ≅
        cornerLeft.result.finiteRightModule hmono) := by
    intro hiso
    apply hmiddle
    rw [mixedCornerLeftCohook_result leftCohook cornerRight] at hiso
    exact hiso
  change IsIrreducibleMorphism
    (biprod.lift (rightHook.finiteModuleMap hmono)
      (-cornerLeft.finiteModuleMap hmono))
  exact isIrreducibleMorphism_finiteRightModule_biprod_lift_of_not_iso
    hmono _ _
      (rightHook.finiteModuleMap_isIrreducible_of_finiteStringSum
        hmono hcover)
      (MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_neg
        (cornerLeft.finiteModuleMap_isIrreducible_of_finiteStringSum
          hmono hcover))
      hmiddle'

/-- In the distinct-middle case, the original left cohook and transported
right hook assemble to the irreducible second differential. -/
theorem mixedMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (D.finiteRightModule hmono ≅ corner.finiteRightModule hmono)) :
    IsIrreducibleMorphism
      (mixedMaximalFiniteShortComplex leftCohook cornerRight hmono).g := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let cornerLeft := mixedCornerLeftCohook leftCohook cornerRight
  have hcorner : cornerLeft.result = corner :=
    mixedCornerLeftCohook_result leftCohook cornerRight
  let transportedCornerRight : HookExtension left.result cornerLeft.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ HookExtension left.result W) hcorner.symm)
      cornerRight
  have hmiddle' : ¬ Nonempty
      (D.finiteRightModule hmono ≅
        cornerLeft.result.finiteRightModule hmono) := by
    intro hiso
    apply hmiddle
    rw [hcorner] at hiso
    exact hiso
  change IsIrreducibleMorphism
    (biprod.desc (leftCohook.finiteModuleMap hmono)
      (transportedCornerRight.finiteModuleMap hmono))
  exact isIrreducibleMorphism_finiteRightModule_biprod_desc_of_not_iso
    hmono _ _
      (leftCohook.finiteModuleMap_isIrreducible_of_finiteStringSum
        hmono hcover)
      (transportedCornerRight.finiteModuleMap_isIrreducible_of_finiteStringSum
        hmono hcover)
      hmiddle'

/-- In the distinct-middle case, the literal finite mixed boundary complex
is short exact. -/
theorem mixedMaximalFiniteShortComplex_shortExact_of_not_iso
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (D.finiteRightModule hmono ≅ corner.finiteRightModule hmono)) :
    (mixedMaximalFiniteShortComplex leftCohook cornerRight hmono).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (mixedMaximalFiniteShortComplex_exact leftCohook cornerRight hmono)
  · exact mixedMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
      leftCohook cornerRight hmono hcover hmiddle
  · exact mixedMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
      leftCohook cornerRight hmono hcover hmiddle

variable {A : Type u} [Ring A] [Algebra k A]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : StringPresentation k A Q}

/-- The two middle modules of a mixed cohook--hook square cannot be
isomorphic: the common corner is strictly longer than the base word. -/
theorem not_nonempty_finiteRightModule_iso_of_leftCohook_rightHook
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    {D corner : Word P.toPresentation.relations}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    ¬ Nonempty
      (D.finiteRightModule P.monomial ≅
        corner.finiteRightModule P.monomial) := by
  have hlength : D.length < corner.length := by
    rw [cornerRight.result_length, leftCohook.result_length]
    simp only [LeftCohookExtension.steps, CohookExtension.steps,
      HookExtension.steps]
    omega
  intro hmiddle
  rcases DetectorIndex.eq_or_eq_reverse_of_finiteRightModule_iso
      S D corner hmiddle.some with hwords | hreverse
  · have hwordLength := congrArg
      (fun W : Word P.toPresentation.relations ↦ W.length) hwords
    omega
  · have hwordLength := congrArg
      (fun W : Word P.toPresentation.relations ↦ W.length) hreverse
    rw [reverse_length] at hwordLength
    omega

/-- The first differential of the mixed cohook--hook complex is
unconditionally irreducible. -/
theorem mixedMaximalFiniteShortComplex_f_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {D corner : Word P.toPresentation.relations}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    IsIrreducibleMorphism
      (mixedMaximalFiniteShortComplex
        leftCohook cornerRight P.monomial).f := by
  let hcover : EveryFiniteModuleIsFiniteStringSum P.monomial :=
    DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  exact mixedMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
    leftCohook cornerRight P.monomial hcover
      (not_nonempty_finiteRightModule_iso_of_leftCohook_rightHook
        S leftCohook cornerRight)

/-- The second differential of the mixed cohook--hook complex is
unconditionally irreducible. -/
theorem mixedMaximalFiniteShortComplex_g_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {D corner : Word P.toPresentation.relations}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    IsIrreducibleMorphism
      (mixedMaximalFiniteShortComplex
        leftCohook cornerRight P.monomial).g := by
  let hcover : EveryFiniteModuleIsFiniteStringSum P.monomial :=
    DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  exact mixedMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
    leftCohook cornerRight P.monomial hcover
      (not_nonempty_finiteRightModule_iso_of_leftCohook_rightHook
        S leftCohook cornerRight)

/-- The literal mixed cohook--hook complex is unconditionally short exact. -/
theorem mixedMaximalFiniteShortComplex_shortExact
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {D corner : Word P.toPresentation.relations}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : HookExtension leftCohook.result corner) :
    (mixedMaximalFiniteShortComplex
      leftCohook cornerRight P.monomial).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (mixedMaximalFiniteShortComplex_exact
      leftCohook cornerRight P.monomial)
  · exact mixedMaximalFiniteShortComplex_f_isIrreducible
      S leftCohook cornerRight
  · exact mixedMaximalFiniteShortComplex_g_isIrreducible
      S leftCohook cornerRight

/-- The finite literal mixed complex in the manuscript's deletion--hook
input form. -/
def leftCohookDeletionRightHookMaximalFiniteShortComplex
    {C D corner : Word R}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner)
    (hmono : IsMonomial R) := by
  let leftCohook := deletion.toLeftCohookExtension
  have hleft : leftCohook.result = C :=
    deletion.toLeftCohookExtension_result
  let transportedRight : HookExtension leftCohook.result corner :=
    Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension W corner) hleft.symm)
      right
  exact mixedMaximalFiniteShortComplex leftCohook transportedRight hmono

/-- The first differential in the deletion--hook input form is irreducible. -/
theorem leftCohookDeletionRightHookMaximalFiniteShortComplex_f_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C D corner : Word P.toPresentation.relations}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner) :
    IsIrreducibleMorphism
      (leftCohookDeletionRightHookMaximalFiniteShortComplex
        deletion right P.monomial).f := by
  let leftCohook := deletion.toLeftCohookExtension
  have hleft : leftCohook.result = C :=
    deletion.toLeftCohookExtension_result
  let transportedRight : HookExtension leftCohook.result corner :=
    Eq.mp
      (congrArg
        (fun W : Word P.toPresentation.relations ↦ HookExtension W corner)
        hleft.symm)
      right
  change IsIrreducibleMorphism
    (mixedMaximalFiniteShortComplex
      leftCohook transportedRight P.monomial).f
  exact mixedMaximalFiniteShortComplex_f_isIrreducible
    S leftCohook transportedRight

/-- The second differential in the deletion--hook input form is
irreducible. -/
theorem leftCohookDeletionRightHookMaximalFiniteShortComplex_g_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C D corner : Word P.toPresentation.relations}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner) :
    IsIrreducibleMorphism
      (leftCohookDeletionRightHookMaximalFiniteShortComplex
        deletion right P.monomial).g := by
  let leftCohook := deletion.toLeftCohookExtension
  have hleft : leftCohook.result = C :=
    deletion.toLeftCohookExtension_result
  let transportedRight : HookExtension leftCohook.result corner :=
    Eq.mp
      (congrArg
        (fun W : Word P.toPresentation.relations ↦ HookExtension W corner)
        hleft.symm)
      right
  change IsIrreducibleMorphism
    (mixedMaximalFiniteShortComplex
      leftCohook transportedRight P.monomial).g
  exact mixedMaximalFiniteShortComplex_g_isIrreducible
    S leftCohook transportedRight

/-- A left cohook deletion and a right hook give the literal short exact
mixed boundary sequence. -/
theorem leftCohookDeletionRightHookMaximalFiniteShortComplex_shortExact
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C D corner : Word P.toPresentation.relations}
    (deletion : LeftCohookDeletion C D)
    (right : HookExtension C corner) :
    (leftCohookDeletionRightHookMaximalFiniteShortComplex
      deletion right P.monomial).ShortExact := by
  let leftCohook := deletion.toLeftCohookExtension
  have hleft : leftCohook.result = C :=
    deletion.toLeftCohookExtension_result
  let transportedRight : HookExtension leftCohook.result corner :=
    Eq.mp
      (congrArg
        (fun W : Word P.toPresentation.relations ↦ HookExtension W corner)
        hleft.symm)
      right
  change
    (mixedMaximalFiniteShortComplex
      leftCohook transportedRight P.monomial).ShortExact
  exact mixedMaximalFiniteShortComplex_shortExact
    S leftCohook transportedRight

end MagnitudeConjecture.BoundQuiver.StringWord.Word
