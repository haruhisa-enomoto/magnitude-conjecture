import MagnitudeConjecture.Algebra.StringFiniteBiproductIrreducible
import MagnitudeConjecture.Algebra.StringFiniteBoundarySquare
import MagnitudeConjecture.Algebra.StringHookCohookFiniteIrreducible
import MagnitudeConjecture.Algebra.StringHookCohookReplay
import MagnitudeConjecture.Algebra.StringHookRepeatedMiddle
import MagnitudeConjecture.Algebra.StringHookSquare
import MagnitudeConjecture.Algebra.StringReconstructionCoverage
import MagnitudeConjecture.CategoryTheory.IrreducibleShortExactAlmostSplit

/-!
# Irreducible differentials of finite string boundary squares

This file connects the explicit boundary-square maps to the maximal hook and
cohook maps whose irreducibility has already been proved.
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
/-- Adding a left hook does not destroy maximality of the already maximal
right hook at the opposite endpoint. -/
theorem twoHookCornerWord_startsInDeep {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    (twoHookCornerWord right left hpath).StartsInDeep := by
  intro z a hcorner
  apply right.maximal a
  let signedArrow : @Quiver.Hom (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) rightResult.target z := negativeArrow a
  have hrightExplicit : IsString R
      ((C.path.comp ((positiveArrow right.arrow).toPath.comp
          right.tail.toRightExtension.suffixPath)).comp
        signedArrow.toPath) := by
    change IsString R
      ((twoHookPath right left).comp signedArrow.toPath) at hcorner
    apply IsString.of_contiguousSubpath R hcorner
    refine ⟨left.hook.tail.toRightExtension.suffixPath.reverse.comp
        (negativeArrow left.hook.arrow).toPath,
      Quiver.Path.nil, ?_⟩
    simp only [twoHookPath, signedArrow, Quiver.Path.comp_nil]
    calc
      _ = left.hook.tail.toRightExtension.suffixPath.reverse.comp
          (((negativeArrow left.hook.arrow).toPath.comp
            (C.path.comp ((positiveArrow right.arrow).toPath.comp
              right.tail.toRightExtension.suffixPath))).comp
                (negativeArrow a).toPath) :=
        @Quiver.Path.comp_assoc (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          left.hook.tail.toRightExtension.suffixPath.reverse
          ((negativeArrow left.hook.arrow).toPath.comp
            (C.path.comp ((positiveArrow right.arrow).toPath.comp
              right.tail.toRightExtension.suffixPath)))
          (negativeArrow a).toPath
      _ = left.hook.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow left.hook.arrow).toPath.comp
            ((C.path.comp ((positiveArrow right.arrow).toPath.comp
              right.tail.toRightExtension.suffixPath)).comp
                (negativeArrow a).toPath)) := by
        exact congrArg
          (fun p ↦ left.hook.tail.toRightExtension.suffixPath.reverse.comp p)
          (@Quiver.Path.comp_assoc (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q) _ _ _ _
            (negativeArrow left.hook.arrow).toPath
            (C.path.comp ((positiveArrow right.arrow).toPath.comp
              right.tail.toRightExtension.suffixPath))
            (negativeArrow a).toPath)
      _ = _ :=
        (@Quiver.Path.comp_assoc (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          left.hook.tail.toRightExtension.suffixPath.reverse
          (negativeArrow left.hook.arrow).toPath
          ((C.path.comp ((positiveArrow right.arrow).toPath.comp
            right.tail.toRightExtension.suffixPath)).comp
              (negativeArrow a).toPath)).symm
  let extension := right.toPositiveBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hsuffix :=
    right.toPositiveBoundaryExtension.toRightExtension_suffixPath
  change extension.suffixPath =
    (positiveArrow right.arrow).toPath.comp
      right.tail.toRightExtension.suffixPath at hsuffix
  rw [hsuffix] at hfactor
  have hcast : IsString R
      ((@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        rightResult.source rightResult.target C.source rightResult.target
        extension.source_eq rfl rightResult.path).comp
        signedArrow.toPath) := by
    rw [hfactor]
    exact hrightExplicit
  have hresult := isString_comp_cast_toPath (Q := Q) R rightResult.path
    signedArrow extension.source_eq rfl hcast
  simpa only [signedArrow, Quiver.Hom.cast_rfl_rfl] using hresult

/-- Replaying the right negative tail after a left hook gives a literal
maximal right hook from the left-hook result to the common corner. -/
def twoHookRightCornerHook {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    HookExtension left.result (twoHookCornerWord right left hpath) := by
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
  have hfull : IsString R
      (basePath.comp ((positiveArrow right.arrow).toPath.comp
        right.tail.toRightExtension.suffixPath)) := by
    rw [← Quiver.Path.comp_assoc, hpathFull]
    exact hpath
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
  let replay := right.tail.rebaseNegative
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayTail : NegativeExtension firstWord replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ NegativeExtension W replay.result)
        hreplayBase)
      replay.rebased
  have hresult : replay.result = twoHookCornerWord right left hpath := by
    apply Word.ext
    · exact replay.source_eq
    · exact replay.target_eq
    · exact HEq.trans
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          replay.source_eq replay.target_eq replay.result.path).symm
        (heq_of_eq (replay.path_cast_eq.trans hpathFull))
  let rawHook : HookExtension baseWord replay.result := {
    vertex := right.vertex
    arrow := right.arrow
    valid := hvalid
    tail := replayTail
    maximal := by
      rw [hresult]
      exact twoHookCornerWord_startsInDeep right left hpath }
  let sourceHook : HookExtension left.result replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension W replay.result)
        hbaseWord)
      rawHook
  exact Eq.mp
    (congrArg (fun W : Word R ↦ HookExtension left.result W) hresult)
    sourceHook

omit [Fintype Q] in
/-- Adding a right hook does not destroy maximality of the already maximal
left hook when the common corner is viewed in reverse orientation. -/
theorem twoHookReverseCornerWord_startsInDeep {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    (twoHookReverseCornerWord right left hpath).StartsInDeep := by
  intro z a hcorner
  apply left.hook.maximal a
  let signedArrow : @Quiver.Hom (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) left.reverseResult.target z :=
    negativeArrow a
  have hleftExplicit : IsString R
      ((C.path.reverse.comp
          ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath)).comp
        signedArrow.toPath) := by
    change IsString R
      ((twoHookReversePath right left).comp signedArrow.toPath) at hcorner
    apply IsString.of_contiguousSubpath R hcorner
    refine ⟨right.tail.toRightExtension.suffixPath.reverse.comp
        (negativeArrow right.arrow).toPath,
      Quiver.Path.nil, ?_⟩
    simp only [twoHookReversePath, signedArrow, Quiver.Path.comp_nil]
    calc
      _ = right.tail.toRightExtension.suffixPath.reverse.comp
          (((negativeArrow right.arrow).toPath.comp
            (C.path.reverse.comp
              ((positiveArrow left.hook.arrow).toPath.comp
                left.hook.tail.toRightExtension.suffixPath))).comp
                  (negativeArrow a).toPath) :=
        @Quiver.Path.comp_assoc (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          right.tail.toRightExtension.suffixPath.reverse
          ((negativeArrow right.arrow).toPath.comp
            (C.path.reverse.comp
              ((positiveArrow left.hook.arrow).toPath.comp
                left.hook.tail.toRightExtension.suffixPath)))
          (negativeArrow a).toPath
      _ = right.tail.toRightExtension.suffixPath.reverse.comp
          ((negativeArrow right.arrow).toPath.comp
            ((C.path.reverse.comp
              ((positiveArrow left.hook.arrow).toPath.comp
                left.hook.tail.toRightExtension.suffixPath)).comp
                  (negativeArrow a).toPath)) := by
        exact congrArg
          (fun p ↦ right.tail.toRightExtension.suffixPath.reverse.comp p)
          (@Quiver.Path.comp_assoc (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q) _ _ _ _
            (negativeArrow right.arrow).toPath
            (C.path.reverse.comp
              ((positiveArrow left.hook.arrow).toPath.comp
                left.hook.tail.toRightExtension.suffixPath))
            (negativeArrow a).toPath)
      _ = _ :=
        (@Quiver.Path.comp_assoc (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          right.tail.toRightExtension.suffixPath.reverse
          (negativeArrow right.arrow).toPath
          ((C.path.reverse.comp
            ((positiveArrow left.hook.arrow).toPath.comp
              left.hook.tail.toRightExtension.suffixPath)).comp
                (negativeArrow a).toPath)).symm
  let extension := left.hook.toPositiveBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hsuffix :=
    left.hook.toPositiveBoundaryExtension.toRightExtension_suffixPath
  change extension.suffixPath =
    (positiveArrow left.hook.arrow).toPath.comp
      left.hook.tail.toRightExtension.suffixPath at hsuffix
  rw [hsuffix] at hfactor
  have hcast : IsString R
      ((@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        left.reverseResult.source left.reverseResult.target
        C.reverse.source left.reverseResult.target
        extension.source_eq rfl left.reverseResult.path).comp
        signedArrow.toPath) := by
    rw [hfactor]
    change IsString R
      ((C.path.reverse.comp
        ((positiveArrow left.hook.arrow).toPath.comp
          left.hook.tail.toRightExtension.suffixPath)).comp
            signedArrow.toPath)
    exact hleftExplicit
  have hresult := isString_comp_cast_toPath (Q := Q) R
    left.reverseResult.path signedArrow extension.source_eq rfl hcast
  simpa only [signedArrow, Quiver.Hom.cast_rfl_rfl] using hresult

/-- Replaying the left negative tail after the reversed right hook gives a
literal maximal left hook from the right-hook result to the common corner. -/
def twoHookLeftCornerHook {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    LeftHookExtension rightResult := by
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
      basePath.comp
          ((positiveArrow left.hook.arrow).toPath.comp
            left.hook.tail.toRightExtension.suffixPath) =
        twoHookReversePath right left := by
    dsimp only [basePath]
    rw [rightHookReverseBasePath_eq]
    exact (Quiver.Path.comp_assoc _ _ _).trans
      (congrArg
        (fun p ↦ right.tail.toRightExtension.suffixPath.reverse.comp p)
        (Quiver.Path.comp_assoc _ _ _))
  have hfull : IsString R
      (basePath.comp ((positiveArrow left.hook.arrow).toPath.comp
        left.hook.tail.toRightExtension.suffixPath)) := by
    rw [hpathFull]
    exact hcornerReverse
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
    rw [Quiver.Path.comp_assoc]
    exact hfull
  let replay := left.hook.tail.rebaseNegative
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayTail : NegativeExtension firstWord replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ NegativeExtension W replay.result)
        hreplayBase)
      replay.rebased
  have hpathReplay :
      firstWord.path.comp left.hook.tail.toRightExtension.suffixPath =
        twoHookReversePath right left := by
    change
      (basePath.comp (positiveArrow left.hook.arrow).toPath).comp
          left.hook.tail.toRightExtension.suffixPath =
        twoHookReversePath right left
    exact (Quiver.Path.comp_assoc _ _ _).trans hpathFull
  have hresult : replay.result =
      twoHookReverseCornerWord right left hpath := by
    apply Word.ext
    · exact replay.source_eq
    · exact replay.target_eq
    · exact HEq.trans
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          replay.source_eq replay.target_eq replay.result.path).symm
        (heq_of_eq (replay.path_cast_eq.trans hpathReplay))
  let rawHook : HookExtension baseWord replay.result := {
    vertex := left.hook.vertex
    arrow := left.hook.arrow
    valid := hvalid
    tail := replayTail
    maximal := by
      rw [hresult]
      exact twoHookReverseCornerWord_startsInDeep right left hpath }
  let sourceHook : HookExtension rightResult.reverse replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension W replay.result)
        hbaseWord)
      rawHook
  let cornerHook : HookExtension rightResult.reverse
      (twoHookReverseCornerWord right left hpath) :=
    Eq.mp
      (congrArg
        (fun W : Word R ↦ HookExtension rightResult.reverse W) hresult)
      sourceHook
  exact {
    reverseResult := twoHookReverseCornerWord right left hpath
    hook := cornerHook }

omit [Fintype Q] in
@[simp]
theorem twoHookLeftCornerHook_result {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    (twoHookLeftCornerHook right left hpath).result =
      twoHookCornerWord right left hpath := by
  change (twoHookReverseCornerWord right left hpath).reverse =
    twoHookCornerWord right left hpath
  exact twoHookReverseCornerWord_reverse right left hpath

omit [Fintype Q] in
/-- The replayed maximal left corner adds exactly as many letters as the
original left hook. -/
theorem twoHookLeftCornerHook_steps {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    (twoHookLeftCornerHook right left hpath).steps = left.steps := by
  let oldCorner := twoHookLeftCorner right left hpath
  have hnew :=
    (twoHookLeftCornerHook right left hpath).result_length
  have hold := oldCorner.extension.result_length
  rw [twoHookLeftCornerHook_result] at hnew
  rw [oldCorner.result_eq_twoHookCornerWord right left hpath] at hold
  have holdSteps := oldCorner.steps_eq
  change oldCorner.extension.steps = left.steps at holdSteps
  omega

/-- Transport the maximal right-corner hook to the literal result word of
the maximal left-corner hook. -/
def twoHookRightCornerHookForLeftResult {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    HookExtension left.result
      (twoHookLeftCornerHook right left hpath).result := by
  exact Eq.mp
    (congrArg (fun W : Word R ↦ HookExtension left.result W)
      (twoHookLeftCornerHook_result right left hpath).symm)
    (twoHookRightCornerHook right left hpath)

/-- The positive two-hook square rebuilt from four maximal hooks.  All four
coordinate maps are now literally hook maps, while the common corner remains
the canonical two-hook word. -/
def twoHookMaximalSquare {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left)) :
    PositiveBoundarySquare C := by
  let cornerRightHook := twoHookRightCornerHook right left hpath
  let cornerLeftHook := twoHookLeftCornerHook right left hpath
  let cornerRight :=
    twoHookRightCornerHookForLeftResult right left hpath
  exact PositiveBoundarySquare.ofExtensions
    right.toPositiveBoundaryExtension
    left.toLeftPositiveBoundaryExtension
    cornerLeftHook.toLeftPositiveBoundaryExtension
    cornerRight.toPositiveBoundaryExtension (by
      simpa only [LeftPositiveBoundaryExtension.steps,
        LeftHookExtension.toLeftPositiveBoundaryExtension,
        HookExtension.toPositiveBoundaryExtension,
        PositiveBoundaryExtension.toRightExtension_steps,
        NegativeExtension.toRightExtension_steps,
        LeftHookExtension.steps, HookExtension.steps] using
        twoHookLeftCornerHook_steps right left hpath)

/-- In the distinct-middle case, the two maximal corner hooks assemble to
an irreducible first differential of the positive boundary sequence. -/
theorem twoHookCorner_finiteCombinedMap_isIrreducible_of_not_iso
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (left.result.finiteRightModule hmono ≅
        rightResult.finiteRightModule hmono)) :
    IsIrreducibleMorphism
      (biprod.lift
        ((twoHookRightCornerHookForLeftResult right left hpath).finiteModuleMap
          hmono)
        (-((twoHookLeftCornerHook right left hpath).finiteModuleMap
          hmono))) := by
  let cornerRight :=
    twoHookRightCornerHookForLeftResult right left hpath
  let cornerLeft := twoHookLeftCornerHook right left hpath
  have hright : IsIrreducibleMorphism
      (cornerRight.finiteModuleMap hmono) :=
    cornerRight.finiteModuleMap_isIrreducible_of_finiteStringSum
      hmono hcover
  have hleft : IsIrreducibleMorphism
      (cornerLeft.finiteModuleMap hmono) :=
    cornerLeft.finiteModuleMap_isIrreducible_of_finiteStringSum
      hmono hcover
  exact isIrreducibleMorphism_finiteRightModule_biprod_lift_of_not_iso
    hmono _ _ hright
      (MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_neg hleft)
    hmiddle

/-- In the literal repeated-middle case, the two corner projections occupy
different hook components.  The symmetric Gaussian-elimination criterion
therefore makes the first differential irreducible. -/
theorem twoHookCorner_finiteCombinedMap_isIrreducible_of_eq
    [IsAlgClosed k]
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : left.result = rightResult) :
    IsIrreducibleMorphism
      (biprod.lift
        ((twoHookRightCornerHookForLeftResult right left hpath).finiteModuleMap
          hmono)
        (-((twoHookLeftCornerHook right left hpath).finiteModuleMap
          hmono))) := by
  subst rightResult
  let cornerRight :=
    twoHookRightCornerHookForLeftResult right left hpath
  let cornerLeft := twoHookLeftCornerHook right left hpath
  have hleftIrreducible :=
    cornerLeft.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  have hnegativeIrreducible : IsIrreducibleMorphism
      (-cornerLeft.finiteModuleMap hmono) :=
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_neg
      hleftIrreducible
  letI : IsLocalRing (End (cornerLeft.result.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (cornerLeft.result.finiteRightModule hmono)
      (cornerLeft.result.finiteRightModule_indecomposable hmono)
  have hleftRadical : IsRadicalMorphism
      (cornerLeft.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (cornerLeft.result.finiteRightModule_indecomposable hmono).1
      (cornerLeft.finiteModuleMap hmono)).2
        hleftIrreducible.not_isSplitMono
  have hnegativeRadical : IsRadicalMorphism
      (-cornerLeft.finiteModuleMap hmono) :=
    isRadicalMorphism_neg hleftRadical
  have hnegativeCoefficient :
      cornerLeft.result.morphismCoefficientAt left.result hmono hmono
        (-cornerLeft.finiteModuleMap hmono).hom.hom
        (cornerRight.moduleMapComponent hmono).1.representative = 0 := by
    change cornerLeft.result.morphismCoefficientAt left.result hmono hmono
      (-cornerLeft.moduleMap hmono)
      (cornerRight.moduleMapComponent hmono).1.representative = 0
    rw [cornerLeft.result.morphismCoefficientAt_neg,
      cornerLeft.morphismCoefficientAt_moduleMap_rightHookComponent_eq_zero
        cornerRight hmono, neg_zero]
  apply isIrreducibleMorphism_finiteRightModule_biprod_lift_repeated_symm
    hmono (cornerRight.finiteModuleMap hmono)
      (-cornerLeft.finiteModuleMap hmono) hnegativeIrreducible
  intro c
  exact
    cornerRight.finiteModuleMap_sub_smul_isIrreducible_of_coefficient_eq_zero
      hmono hcover (-cornerLeft.finiteModuleMap hmono) hnegativeRadical
        hnegativeCoefficient c

/-- In the distinct-middle case, the original two hooks assemble to an
irreducible second differential of the positive boundary sequence. -/
theorem twoHookBase_finiteCombinedMap_isIrreducible_of_not_iso
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (left.result.finiteRightModule hmono ≅
        rightResult.finiteRightModule hmono)) :
    IsIrreducibleMorphism
      (biprod.desc (left.finiteModuleMap hmono)
        (right.finiteModuleMap hmono)) := by
  exact isIrreducibleMorphism_finiteRightModule_biprod_desc_of_not_iso
    hmono _ _
      (left.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover)
      (right.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover)
      hmiddle

/-- When the two middle words are literally equal, the two hook components
are different graph-basis vectors.  Gaussian elimination on this repeated
summand therefore makes the second differential irreducible. -/
theorem twoHookBase_finiteCombinedMap_isIrreducible_of_eq
    [IsAlgClosed k]
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : left.result = rightResult) :
    IsIrreducibleMorphism
      (biprod.desc (left.finiteModuleMap hmono)
        (right.finiteModuleMap hmono)) := by
  subst rightResult
  have hleftIrreducible :=
    left.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  letI : IsLocalRing (End (left.result.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (left.result.finiteRightModule hmono)
      (left.result.finiteRightModule_indecomposable hmono)
  have hleftRadical : IsRadicalMorphism (left.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (left.result.finiteRightModule_indecomposable hmono).1
      (left.finiteModuleMap hmono)).2 hleftIrreducible.not_isSplitMono
  have hleftCoefficient : left.result.morphismCoefficientAt C hmono hmono
      (left.finiteModuleMap hmono).hom.hom
      (right.moduleMapComponent hmono).1.representative = 0 := by
    exact left.morphismCoefficientAt_moduleMap_rightHookComponent_eq_zero
      right hmono
  apply isIrreducibleMorphism_finiteRightModule_biprod_desc_repeated
    hmono (left.finiteModuleMap hmono) (right.finiteModuleMap hmono)
    hleftIrreducible
  intro c
  exact right.finiteModuleMap_sub_smul_isIrreducible_of_coefficient_eq_zero
    hmono hcover (left.finiteModuleMap hmono) hleftRadical
      hleftCoefficient c

/-- The four-maximal-hook positive boundary complex in the finite-dimensional
module category. -/
def twoHookMaximalFiniteShortComplex {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R) :=
  (twoHookMaximalSquare right left hpath).finiteShortComplex hmono

/-- The finite four-maximal-hook positive boundary complex is exact. -/
theorem twoHookMaximalFiniteShortComplex_exact
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R) :
    (twoHookMaximalFiniteShortComplex right left hpath hmono).Exact :=
  PositiveBoundarySquare.finiteShortComplex_exact
    (twoHookMaximalSquare right left hpath) hmono

/-- In the distinct-middle case, the first differential of the literal
finite positive boundary complex is irreducible. -/
theorem twoHookMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (left.result.finiteRightModule hmono ≅
        rightResult.finiteRightModule hmono)) :
    IsIrreducibleMorphism
      (twoHookMaximalFiniteShortComplex right left hpath hmono).f := by
  change IsIrreducibleMorphism
    (biprod.lift
      ((twoHookRightCornerHookForLeftResult right left hpath).finiteModuleMap
        hmono)
      (-((twoHookLeftCornerHook right left hpath).finiteModuleMap hmono)))
  exact twoHookCorner_finiteCombinedMap_isIrreducible_of_not_iso
    right left hpath hmono hcover hmiddle

/-- In the distinct-middle case, the second differential of the literal
finite positive boundary complex is irreducible. -/
theorem twoHookMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (left.result.finiteRightModule hmono ≅
        rightResult.finiteRightModule hmono)) :
    IsIrreducibleMorphism
      (twoHookMaximalFiniteShortComplex right left hpath hmono).g := by
  change IsIrreducibleMorphism
    (biprod.desc (left.finiteModuleMap hmono)
      (right.finiteModuleMap hmono))
  exact twoHookBase_finiteCombinedMap_isIrreducible_of_not_iso
    right left hmono hcover hmiddle

/-- In the literal repeated-middle case, the first differential of the
finite positive boundary complex is irreducible. -/
theorem twoHookMaximalFiniteShortComplex_f_isIrreducible_of_eq
    [IsAlgClosed k]
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : left.result = rightResult) :
    IsIrreducibleMorphism
      (twoHookMaximalFiniteShortComplex right left hpath hmono).f := by
  change IsIrreducibleMorphism
    (biprod.lift
      ((twoHookRightCornerHookForLeftResult right left hpath).finiteModuleMap
        hmono)
      (-((twoHookLeftCornerHook right left hpath).finiteModuleMap hmono)))
  exact twoHookCorner_finiteCombinedMap_isIrreducible_of_eq
    right left hpath hmono hcover hmiddle

/-- In the literal repeated-middle case, the second differential of the
finite positive boundary complex is irreducible. -/
theorem twoHookMaximalFiniteShortComplex_g_isIrreducible_of_eq
    [IsAlgClosed k]
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : left.result = rightResult) :
    IsIrreducibleMorphism
      (twoHookMaximalFiniteShortComplex right left hpath hmono).g := by
  change IsIrreducibleMorphism
    (biprod.desc (left.finiteModuleMap hmono)
      (right.finiteModuleMap hmono))
  exact twoHookBase_finiteCombinedMap_isIrreducible_of_eq
    right left hmono hcover hmiddle

/-- In the distinct-middle case, the literal finite positive boundary
complex is short exact. -/
theorem twoHookMaximalFiniteShortComplex_shortExact_of_not_iso
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : ¬ Nonempty
      (left.result.finiteRightModule hmono ≅
        rightResult.finiteRightModule hmono)) :
    (twoHookMaximalFiniteShortComplex right left hpath hmono).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (twoHookMaximalFiniteShortComplex_exact right left hpath hmono)
  · exact twoHookMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
      right left hpath hmono hcover hmiddle
  · exact twoHookMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
      right left hpath hmono hcover hmiddle

/-- In the literal repeated-middle case, the finite positive boundary
complex is short exact. -/
theorem twoHookMaximalFiniteShortComplex_shortExact_of_eq
    [IsAlgClosed k]
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hmiddle : left.result = rightResult) :
    (twoHookMaximalFiniteShortComplex right left hpath hmono).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (twoHookMaximalFiniteShortComplex_exact right left hpath hmono)
  · exact twoHookMaximalFiniteShortComplex_f_isIrreducible_of_eq
      right left hpath hmono hcover hmiddle
  · exact twoHookMaximalFiniteShortComplex_g_isIrreducible_of_eq
      right left hpath hmono hcover hmiddle

omit [Fintype Q] in
/-- The four-maximal-hook positive square is exact in the raw string-module
category. -/
theorem twoHookMaximalSquare_shortComplex_exact
    {C rightResult : Word R}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString R (twoHookPath right left))
    (hmono : IsMonomial R) :
    ((twoHookMaximalSquare right left hpath).shortComplex hmono).Exact :=
  PositiveBoundarySquare.shortComplex_exact
    (twoHookMaximalSquare right left hpath) hmono

variable {A : Type u} [Ring A] [Algebra k A]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : StringPresentation k A Q}

/-- The first differential of the positive two-hook complex is irreducible
without a middle-summand case hypothesis. -/
theorem twoHookMaximalFiniteShortComplex_f_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C rightResult : Word P.toPresentation.relations}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString P.toPresentation.relations
      (twoHookPath right left)) :
    IsIrreducibleMorphism
      (twoHookMaximalFiniteShortComplex right left hpath P.monomial).f := by
  let hcover : EveryFiniteModuleIsFiniteStringSum P.monomial :=
    DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  by_cases hmiddle : Nonempty
      (left.result.finiteRightModule P.monomial ≅
        rightResult.finiteRightModule P.monomial)
  · have hwords :=
      leftHook_result_eq_of_finiteRightModule_iso_of_twoHookPath_isString
        S right left hpath hmiddle.some
    exact twoHookMaximalFiniteShortComplex_f_isIrreducible_of_eq
      right left hpath P.monomial hcover hwords
  · exact twoHookMaximalFiniteShortComplex_f_isIrreducible_of_not_iso
      right left hpath P.monomial hcover hmiddle

/-- The second differential of the positive two-hook complex is irreducible
without a middle-summand case hypothesis. -/
theorem twoHookMaximalFiniteShortComplex_g_isIrreducible
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C rightResult : Word P.toPresentation.relations}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString P.toPresentation.relations
      (twoHookPath right left)) :
    IsIrreducibleMorphism
      (twoHookMaximalFiniteShortComplex right left hpath P.monomial).g := by
  let hcover : EveryFiniteModuleIsFiniteStringSum P.monomial :=
    DetectorIndex.everyFiniteModuleIsFiniteStringSum S
  by_cases hmiddle : Nonempty
      (left.result.finiteRightModule P.monomial ≅
        rightResult.finiteRightModule P.monomial)
  · have hwords :=
      leftHook_result_eq_of_finiteRightModule_iso_of_twoHookPath_isString
        S right left hpath hmiddle.some
    exact twoHookMaximalFiniteShortComplex_g_isIrreducible_of_eq
      right left hpath P.monomial hcover hwords
  · exact twoHookMaximalFiniteShortComplex_g_isIrreducible_of_not_iso
      right left hpath P.monomial hcover hmiddle

/-- The positive two-hook complex is short exact without a middle-summand
case hypothesis.  Detector classification turns an isomorphism of the middle
modules into literal word equality, while nonisomorphic summands use the
ordinary binary-biproduct criterion. -/
theorem twoHookMaximalFiniteShortComplex_shortExact
    [IsAlgClosed k]
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    {C rightResult : Word P.toPresentation.relations}
    (right : HookExtension C rightResult)
    (left : LeftHookExtension C)
    (hpath : IsString P.toPresentation.relations
      (twoHookPath right left)) :
    (twoHookMaximalFiniteShortComplex right left hpath P.monomial).ShortExact := by
  apply MagnitudeConjecture.CategoryTheory.ShortComplex.shortExact_of_exact_of_irreducible
    (twoHookMaximalFiniteShortComplex_exact right left hpath P.monomial)
  · exact twoHookMaximalFiniteShortComplex_f_isIrreducible
      S right left hpath
  · exact twoHookMaximalFiniteShortComplex_g_isIrreducible
      S right left hpath

end MagnitudeConjecture.BoundQuiver.StringWord.Word
