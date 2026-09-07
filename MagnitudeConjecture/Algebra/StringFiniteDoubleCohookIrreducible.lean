import MagnitudeConjecture.Algebra.StringFiniteMixedBoundaryIrreducible
import MagnitudeConjecture.Algebra.StringDoubleCohookSquare
import MagnitudeConjecture.Algebra.StringCohookRepeatedMiddle

/-!
# Irreducible double-cohook boundary sequences

Both generic negative boundaries in the double-cohook square are upgraded to
literal maximal cohooks by the sign-preserving replay construction.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q} [Fintype Q]

omit [Fintype Q] in
@[simp]
theorem CohookExtension.boundaryLetter_transportResult
    {C D D' : Word R} (cohook : CohookExtension C D) (h : D = D') :
    signedArrowLetter (positiveArrow (cohook.transportResult h).arrow) =
      signedArrowLetter (positiveArrow cohook.arrow) := by
  subst D'
  rfl

omit [Fintype Q] in
@[simp]
theorem CohookExtension.boundaryLetter_transportSource
    {C C' D : Word R} (cohook : CohookExtension C D) (h : C = C') :
    signedArrowLetter (positiveArrow (cohook.transportSource h).arrow) =
      signedArrowLetter (positiveArrow cohook.arrow) := by
  subst C'
  rfl

omit [Fintype Q] in
@[simp]
theorem CohookExtension.boundaryLetter_rebase {C D : Word R}
    (cohook : CohookExtension C D) {source : Q}
    (basePath : SignedPath source C.target) (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp
        cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath)) :
    signedArrowLetter
        (positiveArrow (cohook.rebase basePath hbase hfull).rebased.arrow) =
      signedArrowLetter (positiveArrow cohook.arrow) := by
  rfl

omit [Fintype Q] in
/-- Replay the right cohook after deleting the left cohook prefix. -/
def doubleCohookRightCohookReplay {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : CohookExtension left.result corner) :
    CohookExtension.RebaseResult cornerRight
      (mixedBasePath left) (mixedBasePath_isString left) :=
  cornerRight.rebase (mixedBasePath left) (mixedBasePath_isString left)
    (doubleCohookRestrictedPath_isString left
      cornerRight.toNegativeBoundaryExtension)

omit [Fintype Q] in
theorem doubleCohookRightCohookReplay_result_eq {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : CohookExtension left.result corner) :
    (doubleCohookRightCohookReplay left cornerRight).result =
      (doubleCohookRightReplay left
        cornerRight.toNegativeBoundaryExtension).result := by
  let cohookReplay := doubleCohookRightCohookReplay left cornerRight
  let boundaryReplay := doubleCohookRightReplay left
    cornerRight.toNegativeBoundaryExtension
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
/-- The shortened core carries a literal maximal right cohook to the other
middle word. -/
def doubleCohookRightCohook {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : CohookExtension left.result corner) :
    CohookExtension D
      (doubleCohookRightReplay left
        cornerRight.toNegativeBoundaryExtension).result := by
  let replay := doubleCohookRightCohookReplay left cornerRight
  let sourceCohook : CohookExtension D replay.result :=
    replay.rebased.transportSource (mixedBaseWord_eq left)
  exact sourceCohook.transportResult
    (doubleCohookRightCohookReplay_result_eq left cornerRight)

omit [Fintype Q] in
theorem doubleCohookRightCohook_boundaryLetter {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : CohookExtension left.result corner) :
    signedArrowLetter
        (positiveArrow (doubleCohookRightCohook left cornerRight).arrow) =
      signedArrowLetter (positiveArrow cornerRight.arrow) := by
  simp only [doubleCohookRightCohook,
    CohookExtension.boundaryLetter_transportResult,
    CohookExtension.boundaryLetter_transportSource]
  exact CohookExtension.boundaryLetter_rebase cornerRight
    (mixedBasePath left) (mixedBasePath_isString left)
    (doubleCohookRestrictedPath_isString left
      cornerRight.toNegativeBoundaryExtension)

omit [Fintype Q] in
/-- The certified double-cohook corner rules out reversal of its two middle
words. -/
theorem leftCohook_result_ne_reverse_doubleCohookRight_result
    {D corner : Word R}
    (left : LeftCohookExtension D)
    (cornerRight : CohookExtension left.result corner) :
    left.result ≠
      (doubleCohookRightReplay left.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension).result.reverse := by
  intro hmiddle
  let rightCohook := doubleCohookRightCohook
    left.toLeftNegativeBoundaryExtension cornerRight
  obtain ⟨hzero, hboundaryLetter⟩ :=
    length_eq_zero_and_boundaryLetter_eq_of_leftCohook_result_eq_reverse_rightCohook_result
      rightCohook left hmiddle
  have hboundaryCorner :
      signedArrowLetter (positiveArrow left.cohook.arrow) =
        signedArrowLetter (positiveArrow cornerRight.arrow) :=
    hboundaryLetter.trans
      (doubleCohookRightCohook_boundaryLetter
        left.toLeftNegativeBoundaryExtension cornerRight)
  let middle :=
    (mixedBasePath left.toLeftNegativeBoundaryExtension).reverse
  let central := (positiveArrow cornerRight.arrow).toPath.comp
    (middle.comp (negativeArrow left.cohook.arrow).toPath)
  have hmiddleZero : middle.length = 0 := by
    change D.path.length = 0 at hzero
    simpa only [middle, length_reverse, mixedBasePath, path_cast_length]
      using hzero
  have hcentralSub : IsContiguousSubpath central
      (doubleCohookReverseFullPath left.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension) := by
    refine ⟨cornerRight.tail.toRightExtension.suffixPath.reverse,
      left.cohook.tail.toRightExtension.suffixPath, ?_⟩
    simp only [central, middle, doubleCohookReverseFullPath,
      doubleCohookReverseBasePath, doubleCohookRestrictedPath,
      LeftCohookExtension.toLeftNegativeBoundaryExtension,
      NegativeBoundaryExtension.toRightExtension_suffixPath,
      CohookExtension.toNegativeBoundaryExtension,
      Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_negativeArrow, ← Quiver.Path.comp_assoc]
    exact (Quiver.Path.comp_assoc
      ((cornerRight.tail.toRightExtension.suffixPath.reverse.comp
        (positiveArrow cornerRight.arrow).toPath).comp
          (mixedBasePath left.toLeftNegativeBoundaryExtension).reverse)
      (negativeArrow left.cohook.arrow).toPath
      left.cohook.tail.toRightExtension.suffixPath).symm
  have hcentralReduced : IsReduced central :=
    IsReduced.of_contiguousSubpath
      (doubleCohookReverseFullPath_isString
        left.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension).1 hcentralSub
  exact
    (not_isReduced_positiveArrow_comp_zero_comp_negativeArrow_of_letter_eq
      cornerRight.arrow middle left.cohook.arrow hmiddleZero
        hboundaryCorner.symm) hcentralReduced

omit [Fintype Q] in
@[simp]
theorem doubleCohookRightCohook_steps {D corner : Word R}
    (left : LeftNegativeBoundaryExtension D)
    (cornerRight : CohookExtension left.result corner) :
    (doubleCohookRightCohook left cornerRight).steps =
      cornerRight.steps := by
  let replay := doubleCohookRightCohookReplay left cornerRight
  let sourceCohook : CohookExtension D replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ CohookExtension W replay.result)
        (mixedBaseWord_eq left))
      replay.rebased
  let finalCohook : CohookExtension D
      (doubleCohookRightReplay left
        cornerRight.toNegativeBoundaryExtension).result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ CohookExtension D W)
        (doubleCohookRightCohookReplay_result_eq left cornerRight))
      sourceCohook
  change finalCohook.steps = cornerRight.steps
  calc
    finalCohook.steps = sourceCohook.steps :=
      CohookExtension.steps_transport_result
        (doubleCohookRightCohookReplay_result_eq left cornerRight)
        sourceCohook
    _ = replay.rebased.steps :=
      CohookExtension.steps_transport_source (mixedBaseWord_eq left)
        replay.rebased
    _ = cornerRight.steps := CohookExtension.rebase_steps
      cornerRight (mixedBasePath left) (mixedBasePath_isString left)
      (doubleCohookRestrictedPath_isString left
        cornerRight.toNegativeBoundaryExtension)

omit [Fintype Q] in
/-- Replay the original left cohook after reversing the restricted right
cohook word. -/
def doubleCohookLeftCohookReplay {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    CohookExtension.RebaseResult leftCohook.cohook
      (doubleCohookReverseBasePath
        leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension)
      (doubleCohookReverseBasePath_isString
        leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension) :=
  leftCohook.cohook.rebase
    (doubleCohookReverseBasePath
      leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toNegativeBoundaryExtension)
    (doubleCohookReverseBasePath_isString
      leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toNegativeBoundaryExtension)
    (doubleCohookReverseFullPath_isString
      leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toNegativeBoundaryExtension)

omit [Fintype Q] in
theorem doubleCohookLeftCohookReplay_result_eq {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    (doubleCohookLeftCohookReplay leftCohook cornerRight).result =
      (doubleCohookLeftReplay leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension).result := by
  let cohookReplay := doubleCohookLeftCohookReplay leftCohook cornerRight
  let boundaryReplay := doubleCohookLeftReplay
    leftCohook.toLeftNegativeBoundaryExtension
    cornerRight.toNegativeBoundaryExtension
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
/-- The other middle word carries a literal maximal left cohook to the
common corner. -/
def doubleCohookCornerLeftCohook {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    LeftCohookExtension
      (doubleCohookRightReplay
        leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension).result := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let replay := doubleCohookLeftCohookReplay leftCohook cornerRight
  let boundaryReplay := doubleCohookLeftReplay left
    cornerRight.toNegativeBoundaryExtension
  let rightReplay := doubleCohookRightReplay left
    cornerRight.toNegativeBoundaryExtension
  let sourceCohook : CohookExtension rightReplay.result.reverse replay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension W replay.result)
        (doubleCohookReverseBaseWord_eq_rightReverse left
          cornerRight.toNegativeBoundaryExtension))
      replay.rebased
  let finalCohook : CohookExtension rightReplay.result.reverse
      boundaryReplay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension rightReplay.result.reverse W)
        (doubleCohookLeftCohookReplay_result_eq leftCohook cornerRight))
      sourceCohook
  exact {
    reverseResult := boundaryReplay.result
    cohook := finalCohook }

omit [Fintype Q] in
@[simp]
theorem doubleCohookCornerLeftCohook_result {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    (doubleCohookCornerLeftCohook leftCohook cornerRight).result = corner := by
  change
    (doubleCohookLeftReplay leftCohook.toLeftNegativeBoundaryExtension
      cornerRight.toNegativeBoundaryExtension).result.reverse = corner
  exact doubleCohookCornerLeftExtension_result
    leftCohook.toLeftNegativeBoundaryExtension
    cornerRight.toNegativeBoundaryExtension

omit [Fintype Q] in
@[simp]
theorem doubleCohookCornerLeftCohook_steps {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    (doubleCohookCornerLeftCohook leftCohook cornerRight).steps =
      leftCohook.steps := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let replay := doubleCohookLeftCohookReplay leftCohook cornerRight
  let boundaryReplay := doubleCohookLeftReplay left
    cornerRight.toNegativeBoundaryExtension
  let rightReplay := doubleCohookRightReplay left
    cornerRight.toNegativeBoundaryExtension
  let sourceCohook : CohookExtension rightReplay.result.reverse replay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension W replay.result)
        (doubleCohookReverseBaseWord_eq_rightReverse left
          cornerRight.toNegativeBoundaryExtension))
      replay.rebased
  let finalCohook : CohookExtension rightReplay.result.reverse
      boundaryReplay.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension rightReplay.result.reverse W)
        (doubleCohookLeftCohookReplay_result_eq leftCohook cornerRight))
      sourceCohook
  change finalCohook.steps = leftCohook.cohook.steps
  calc
    finalCohook.steps = sourceCohook.steps :=
      CohookExtension.steps_transport_result
        (doubleCohookLeftCohookReplay_result_eq leftCohook cornerRight)
        sourceCohook
    _ = replay.rebased.steps :=
      CohookExtension.steps_transport_source
        (doubleCohookReverseBaseWord_eq_rightReverse left
          cornerRight.toNegativeBoundaryExtension) replay.rebased
    _ = leftCohook.cohook.steps := CohookExtension.rebase_steps
      leftCohook.cohook
      (doubleCohookReverseBasePath left
        cornerRight.toNegativeBoundaryExtension)
      (doubleCohookReverseBasePath_isString left
        cornerRight.toNegativeBoundaryExtension)
      (doubleCohookReverseFullPath_isString left
        cornerRight.toNegativeBoundaryExtension)

/-- The double-cohook square rebuilt from four literal maximal cohooks. -/
def doubleCohookMaximalSquare {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    NegativeBoundarySquare D := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let rightCohook := doubleCohookRightCohook left cornerRight
  let cornerLeft := doubleCohookCornerLeftCohook leftCohook cornerRight
  have hcorner : cornerLeft.result = corner :=
    doubleCohookCornerLeftCohook_result leftCohook cornerRight
  let transportedCornerRight :
      CohookExtension left.result cornerLeft.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension left.result W) hcorner.symm)
      cornerRight
  exact NegativeBoundarySquare.ofExtensions
    rightCohook.toNegativeBoundaryExtension
    left cornerLeft.toLeftNegativeBoundaryExtension
    transportedCornerRight.toNegativeBoundaryExtension (by
      have hsteps :=
        doubleCohookCornerLeftCohook_steps leftCohook cornerRight
      change cornerLeft.cohook.steps = leftCohook.cohook.steps at hsteps
      change
        cornerLeft.cohook.toNegativeBoundaryExtension.toRightExtension.steps =
          leftCohook.cohook.toNegativeBoundaryExtension.toRightExtension.steps
      simpa only [CohookExtension.toNegativeBoundaryExtension,
        NegativeBoundaryExtension.toRightExtension_steps,
        PositiveExtension.toRightExtension_steps,
        CohookExtension.steps] using hsteps)

omit [Fintype Q] in
/-- The common corner of the rebuilt double-cohook square is the prescribed
corner word. -/
theorem doubleCohookMaximalSquare_corner {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    (doubleCohookMaximalSquare leftCohook cornerRight).corner = corner := by
  change (doubleCohookCornerLeftCohook leftCohook cornerRight).result = corner
  exact doubleCohookCornerLeftCohook_result leftCohook cornerRight

/-- The four-maximal-cohook complex in the finite-dimensional module
category. -/
def doubleCohookMaximalFiniteShortComplex {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R) :=
  (doubleCohookMaximalSquare leftCohook cornerRight).finiteShortComplex hmono

theorem doubleCohookMaximalFiniteShortComplex_exact {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R) :
    (doubleCohookMaximalFiniteShortComplex
      leftCohook cornerRight hmono).Exact :=
  NegativeBoundarySquare.finiteShortComplex_exact
    (doubleCohookMaximalSquare leftCohook cornerRight) hmono

/-- In the literal repeated-middle case, the two base cohook components make
the first differential irreducible. -/
theorem doubleCohookMaximalFiniteShortComplex_f_isIrreducible_of_eq
    [IsAlgClosed k]
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : leftCohook.result =
      (doubleCohookRightReplay
        leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension).result) :
    IsIrreducibleMorphism
      (doubleCohookMaximalFiniteShortComplex
        leftCohook cornerRight hmono).f := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let rightCohook := doubleCohookRightCohook left cornerRight
  change IsIrreducibleMorphism
    (biprod.lift (leftCohook.finiteModuleMap hmono)
      (rightCohook.finiteModuleMap hmono))
  let e :
      (doubleCohookRightReplay left
          cornerRight.toNegativeBoundaryExtension).result.finiteRightModule
            hmono ≅
        leftCohook.result.finiteRightModule hmono :=
    eqToIso (congrArg
      (fun W : Word R ↦ W.finiteRightModule hmono) hmiddle.symm)
  let rightCohookEq : CohookExtension D leftCohook.result :=
    rightCohook.transportResult hmiddle.symm
  have htransport : rightCohook.finiteModuleMap hmono ≫ e.hom =
      rightCohookEq.finiteModuleMap hmono := by
    exact (rightCohook.finiteModuleMap_transportResult
      hmiddle.symm hmono).symm
  have hleftIrreducible :=
    leftCohook.finiteModuleMap_isIrreducible_of_finiteStringSum
      hmono hcover
  letI : IsLocalRing (End (D.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (D.finiteRightModule hmono)
      (D.finiteRightModule_indecomposable hmono)
  have hleftRadical : IsRadicalMorphism
      (leftCohook.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (D.finiteRightModule_indecomposable hmono).1
      (leftCohook.finiteModuleMap hmono)).2
        hleftIrreducible.not_isSplitMono
  have hleftCoefficient : D.morphismCoefficientAt leftCohook.result
      hmono hmono (leftCohook.finiteModuleMap hmono).hom.hom
      (rightCohookEq.moduleMapComponent hmono).1.representative = 0 := by
    exact
      leftCohook.morphismCoefficientAt_moduleMap_rightCohookComponent_eq_zero
        rightCohookEq hmono
  apply isIrreducibleMorphism_finiteRightModule_biprod_lift_isomorphic
    hmono e (leftCohook.finiteModuleMap hmono)
      (rightCohook.finiteModuleMap hmono) hleftIrreducible
  intro c
  have hc :=
    rightCohookEq.finiteModuleMap_sub_smul_isIrreducible_of_coefficient_eq_zero
      hmono hcover (leftCohook.finiteModuleMap hmono) hleftRadical
        hleftCoefficient c
  rw [← htransport] at hc
  exact hc

/-- In the literal repeated-middle case, the two corner cohook components
make the second differential irreducible. -/
theorem doubleCohookMaximalFiniteShortComplex_g_isIrreducible_of_eq
    [IsAlgClosed k]
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : leftCohook.result =
      (doubleCohookRightReplay
        leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension).result) :
    IsIrreducibleMorphism
      (doubleCohookMaximalFiniteShortComplex
        leftCohook cornerRight hmono).g := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let otherMiddle :=
    (doubleCohookRightReplay left
      cornerRight.toNegativeBoundaryExtension).result
  let cornerLeft := doubleCohookCornerLeftCohook leftCohook cornerRight
  have hcorner : cornerLeft.result = corner :=
    doubleCohookCornerLeftCohook_result leftCohook cornerRight
  let transportedCornerRight :
      CohookExtension left.result cornerLeft.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension left.result W) hcorner.symm)
      cornerRight
  change IsIrreducibleMorphism
    (biprod.desc (transportedCornerRight.finiteModuleMap hmono)
      (-cornerLeft.finiteModuleMap hmono))
  let e : leftCohook.result.finiteRightModule hmono ≅
      otherMiddle.finiteRightModule hmono :=
    eqToIso (congrArg
      (fun W : Word R ↦ W.finiteRightModule hmono) hmiddle)
  let rightCohookEq : CohookExtension otherMiddle cornerLeft.result :=
    transportedCornerRight.transportSource hmiddle
  have htransport : e.inv ≫ transportedCornerRight.finiteModuleMap hmono =
      rightCohookEq.finiteModuleMap hmono := by
    exact (transportedCornerRight.finiteModuleMap_transportSource
      hmiddle hmono).symm
  have hleftIrreducible :=
    cornerLeft.finiteModuleMap_isIrreducible_of_finiteStringSum
      hmono hcover
  have hnegativeIrreducible : IsIrreducibleMorphism
      (-cornerLeft.finiteModuleMap hmono) :=
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_neg
      hleftIrreducible
  letI : IsLocalRing (End (otherMiddle.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (otherMiddle.finiteRightModule hmono)
      (otherMiddle.finiteRightModule_indecomposable hmono)
  have hleftRadical : IsRadicalMorphism
      (cornerLeft.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (otherMiddle.finiteRightModule_indecomposable hmono).1
      (cornerLeft.finiteModuleMap hmono)).2
        hleftIrreducible.not_isSplitMono
  have hnegativeRadical : IsRadicalMorphism
      (-cornerLeft.finiteModuleMap hmono) :=
    isRadicalMorphism_neg hleftRadical
  have hnegativeCoefficient :
      otherMiddle.morphismCoefficientAt cornerLeft.result hmono hmono
        (-cornerLeft.finiteModuleMap hmono).hom.hom
        (rightCohookEq.moduleMapComponent hmono).1.representative = 0 := by
    change otherMiddle.morphismCoefficientAt cornerLeft.result hmono hmono
      (-cornerLeft.moduleMap hmono)
      (rightCohookEq.moduleMapComponent hmono).1.representative = 0
    rw [otherMiddle.morphismCoefficientAt_neg,
      cornerLeft.morphismCoefficientAt_moduleMap_rightCohookComponent_eq_zero
        rightCohookEq hmono, neg_zero]
  apply
    isIrreducibleMorphism_finiteRightModule_biprod_desc_isomorphic_symm
      hmono e (transportedCornerRight.finiteModuleMap hmono)
        (-cornerLeft.finiteModuleMap hmono) hnegativeIrreducible
  intro c
  have hc :=
    rightCohookEq.finiteModuleMap_sub_smul_isIrreducible_of_coefficient_eq_zero
      hmono hcover (-cornerLeft.finiteModuleMap hmono) hnegativeRadical
        hnegativeCoefficient c
  rw [← htransport] at hc
  exact hc

/-- The two base cohook maps assemble to an irreducible first differential
when the two middle string modules are nonisomorphic. -/
theorem doubleCohookMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (leftCohook.result.finiteRightModule hmono ≅
        (doubleCohookRightReplay
          leftCohook.toLeftNegativeBoundaryExtension
          cornerRight.toNegativeBoundaryExtension).result.finiteRightModule
            hmono)) :
    IsIrreducibleMorphism
      (doubleCohookMaximalFiniteShortComplex
        leftCohook cornerRight hmono).f := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let rightCohook := doubleCohookRightCohook left cornerRight
  change IsIrreducibleMorphism
    (biprod.lift (leftCohook.finiteModuleMap hmono)
      (rightCohook.finiteModuleMap hmono))
  exact isIrreducibleMorphism_finiteRightModule_biprod_lift_of_not_iso
    hmono _ _
      (leftCohook.finiteModuleMap_isIrreducible_of_finiteStringSum
        hmono hcover)
      (rightCohook.finiteModuleMap_isIrreducible_of_finiteStringSum
        hmono hcover)
      hmiddle

/-- The two corner cohook maps assemble to an irreducible second
differential in the distinct-middle case. -/
theorem doubleCohookMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (leftCohook.result.finiteRightModule hmono ≅
        (doubleCohookRightReplay
          leftCohook.toLeftNegativeBoundaryExtension
          cornerRight.toNegativeBoundaryExtension).result.finiteRightModule
            hmono)) :
    IsIrreducibleMorphism
      (doubleCohookMaximalFiniteShortComplex
        leftCohook cornerRight hmono).g := by
  let left := leftCohook.toLeftNegativeBoundaryExtension
  let cornerLeft := doubleCohookCornerLeftCohook leftCohook cornerRight
  have hcorner : cornerLeft.result = corner :=
    doubleCohookCornerLeftCohook_result leftCohook cornerRight
  let transportedCornerRight :
      CohookExtension left.result cornerLeft.result :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ CohookExtension left.result W) hcorner.symm)
      cornerRight
  change IsIrreducibleMorphism
    (biprod.desc (transportedCornerRight.finiteModuleMap hmono)
      (-cornerLeft.finiteModuleMap hmono))
  exact isIrreducibleMorphism_finiteRightModule_biprod_desc_of_not_iso
    hmono _ _
      (transportedCornerRight.finiteModuleMap_isIrreducible_of_finiteStringSum
        hmono hcover)
      (MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_neg
        (cornerLeft.finiteModuleMap_isIrreducible_of_finiteStringSum
          hmono hcover))
      hmiddle

/-- In the distinct-middle case, the literal finite double-cohook complex is
short exact. -/
theorem doubleCohookMaximalFiniteShortComplex_shortExact_of_not_iso
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (leftCohook.result.finiteRightModule hmono ≅
        (doubleCohookRightReplay
          leftCohook.toLeftNegativeBoundaryExtension
          cornerRight.toNegativeBoundaryExtension).result.finiteRightModule
            hmono)) :
    (doubleCohookMaximalFiniteShortComplex
      leftCohook cornerRight hmono).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (doubleCohookMaximalFiniteShortComplex_exact
      leftCohook cornerRight hmono)
  · exact doubleCohookMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
      leftCohook cornerRight hmono hcover hmiddle
  · exact doubleCohookMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
      leftCohook cornerRight hmono hcover hmiddle

/-- In the literal repeated-middle case, the finite double-cohook complex is
short exact. -/
theorem doubleCohookMaximalFiniteShortComplex_shortExact_of_eq
    [IsAlgClosed k]
    {D corner : Word R}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : leftCohook.result =
      (doubleCohookRightReplay
        leftCohook.toLeftNegativeBoundaryExtension
        cornerRight.toNegativeBoundaryExtension).result) :
    (doubleCohookMaximalFiniteShortComplex
      leftCohook cornerRight hmono).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (doubleCohookMaximalFiniteShortComplex_exact
      leftCohook cornerRight hmono)
  · exact doubleCohookMaximalFiniteShortComplex_f_isIrreducible_of_eq
      leftCohook cornerRight hmono hcover hmiddle
  · exact doubleCohookMaximalFiniteShortComplex_g_isIrreducible_of_eq
      leftCohook cornerRight hmono hcover hmiddle

variable {A : Type u} [Ring A] [Algebra k A]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : StringPresentation k A Q}

/-- The first differential of the double-cohook complex is irreducible
without a middle-summand case hypothesis. -/
theorem doubleCohookMaximalFiniteShortComplex_f_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {D corner : Word P.toPresentation.relations}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    IsIrreducibleMorphism
      (doubleCohookMaximalFiniteShortComplex
        leftCohook cornerRight P.monomial).f := by
  let hcover : EveryFiniteModuleIsFiniteStringSum P.monomial :=
    DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  by_cases hmiddle : Nonempty
      (leftCohook.result.finiteRightModule P.monomial ≅
        (doubleCohookRightReplay
          leftCohook.toLeftNegativeBoundaryExtension
          cornerRight.toNegativeBoundaryExtension).result.finiteRightModule
            P.monomial)
  · rcases DetectorIndex.eq_or_eq_reverse_of_finiteRightModule_iso
        S leftCohook.result
          (doubleCohookRightReplay
            leftCohook.toLeftNegativeBoundaryExtension
            cornerRight.toNegativeBoundaryExtension).result
          hmiddle.some with hwords | hreverse
    · exact doubleCohookMaximalFiniteShortComplex_f_isIrreducible_of_eq
        leftCohook cornerRight P.monomial hcover hwords
    · exact False.elim
        (leftCohook_result_ne_reverse_doubleCohookRight_result
          leftCohook cornerRight hreverse)
  · exact doubleCohookMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
      leftCohook cornerRight P.monomial hcover hmiddle

/-- The second differential of the double-cohook complex is irreducible
without a middle-summand case hypothesis. -/
theorem doubleCohookMaximalFiniteShortComplex_g_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {D corner : Word P.toPresentation.relations}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    IsIrreducibleMorphism
      (doubleCohookMaximalFiniteShortComplex
        leftCohook cornerRight P.monomial).g := by
  let hcover : EveryFiniteModuleIsFiniteStringSum P.monomial :=
    DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  by_cases hmiddle : Nonempty
      (leftCohook.result.finiteRightModule P.monomial ≅
        (doubleCohookRightReplay
          leftCohook.toLeftNegativeBoundaryExtension
          cornerRight.toNegativeBoundaryExtension).result.finiteRightModule
            P.monomial)
  · rcases DetectorIndex.eq_or_eq_reverse_of_finiteRightModule_iso
        S leftCohook.result
          (doubleCohookRightReplay
            leftCohook.toLeftNegativeBoundaryExtension
            cornerRight.toNegativeBoundaryExtension).result
          hmiddle.some with hwords | hreverse
    · exact doubleCohookMaximalFiniteShortComplex_g_isIrreducible_of_eq
        leftCohook cornerRight P.monomial hcover hwords
    · exact False.elim
        (leftCohook_result_ne_reverse_doubleCohookRight_result
          leftCohook cornerRight hreverse)
  · exact doubleCohookMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
      leftCohook cornerRight P.monomial hcover hmiddle

/-- The finite double-cohook complex is short exact without a middle-summand
case hypothesis.  Detector classification gives literal equality or reversal
of the middle words, and reducedness of the common corner excludes reversal. -/
theorem doubleCohookMaximalFiniteShortComplex_shortExact
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {D corner : Word P.toPresentation.relations}
    (leftCohook : LeftCohookExtension D)
    (cornerRight : CohookExtension leftCohook.result corner) :
    (doubleCohookMaximalFiniteShortComplex
      leftCohook cornerRight P.monomial).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (doubleCohookMaximalFiniteShortComplex_exact
      leftCohook cornerRight P.monomial)
  · exact doubleCohookMaximalFiniteShortComplex_f_isIrreducible
      S leftCohook cornerRight
  · exact doubleCohookMaximalFiniteShortComplex_g_isIrreducible
      S leftCohook cornerRight

omit [Fintype Q] in
/-- The right cohook reattachment in the manuscript's pair of deletion
inputs, transported to the literal result of the left reattachment. -/
def doubleCohookDeletionCornerRightCohook {C L D : Word R}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L) :
    CohookExtension leftDeletion.toLeftCohookExtension.result C := by
  exact Eq.mp
    (congrArg (fun W : Word R ↦ CohookExtension W C)
      leftDeletion.toLeftCohookExtension_result.symm)
    rightDeletion.cohook

/-- The finite four-maximal-cohook complex in the manuscript's two-deletion
input form. -/
def doubleCohookDeletionMaximalFiniteShortComplex {C L D : Word R}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L)
    (hmono : IsMonomial R) :=
  doubleCohookMaximalFiniteShortComplex
    leftDeletion.toLeftCohookExtension
    (doubleCohookDeletionCornerRightCohook leftDeletion rightDeletion)
    hmono

/-- The first differential in the two-deletion input form is irreducible. -/
theorem doubleCohookDeletionMaximalFiniteShortComplex_f_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C L D : Word P.toPresentation.relations}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L) :
    IsIrreducibleMorphism
      (doubleCohookDeletionMaximalFiniteShortComplex
        leftDeletion rightDeletion P.monomial).f := by
  exact doubleCohookMaximalFiniteShortComplex_f_isIrreducible
    S leftDeletion.toLeftCohookExtension
      (doubleCohookDeletionCornerRightCohook leftDeletion rightDeletion)

/-- The second differential in the two-deletion input form is irreducible. -/
theorem doubleCohookDeletionMaximalFiniteShortComplex_g_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C L D : Word P.toPresentation.relations}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L) :
    IsIrreducibleMorphism
      (doubleCohookDeletionMaximalFiniteShortComplex
        leftDeletion rightDeletion P.monomial).g := by
  exact doubleCohookMaximalFiniteShortComplex_g_isIrreducible
    S leftDeletion.toLeftCohookExtension
      (doubleCohookDeletionCornerRightCohook leftDeletion rightDeletion)

/-- Two cohook deletions give the literal finite short exact double-cohook
sequence, including the repeated-middle case. -/
theorem doubleCohookDeletionMaximalFiniteShortComplex_shortExact
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C L D : Word P.toPresentation.relations}
    (leftDeletion : LeftCohookDeletion L D)
    (rightDeletion : CohookDeletion C L) :
    (doubleCohookDeletionMaximalFiniteShortComplex
      leftDeletion rightDeletion P.monomial).ShortExact := by
  let leftCohook := leftDeletion.toLeftCohookExtension
  let cornerRight :=
    doubleCohookDeletionCornerRightCohook leftDeletion rightDeletion
  exact doubleCohookMaximalFiniteShortComplex_shortExact
    S leftCohook cornerRight

end MagnitudeConjecture.BoundQuiver.StringWord.Word
