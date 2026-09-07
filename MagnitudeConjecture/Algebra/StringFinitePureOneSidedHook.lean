import MagnitudeConjecture.Algebra.StringHookCohookReplay
import MagnitudeConjecture.Algebra.StringLeftHookCohook
import MagnitudeConjecture.Algebra.StringHookSquare
import MagnitudeConjecture.Algebra.StringFiniteBoundarySquare
import MagnitudeConjecture.Algebra.StringPurePeakRepresentable
import MagnitudeConjecture.Algebra.StringHookCohookFiniteIrreducible
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Unary boundary complexes for pure string endpoints

A pure-positive string which is maximal at its right endpoint but has a left
hook has a one-middle Butler--Ringel boundary complex.  The kernel of the
left-hook projection is the positive arm before its first negative letter;
its inclusion is a maximal right cohook.  This file constructs that kernel
word, proves the resulting coordinate sequence short exact, and proves both
differentials irreducible in the finite module category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

theorem CohookExtension.spaceProjection_spaceInclusion_eq_zero
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps) (x : Q) :
    left.spaceProjection x ∘ₗ
      cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion x = 0 := by
  apply LinearMap.ext
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      change left.spaceProjection x
        (cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion x
          (Finsupp.single i c)) = 0
      rw [RightExtension.spaceInclusion_single]
      apply LeftPositiveBoundaryExtension.spaceProjection_single_of_not_exists
      rintro ⟨j, hj⟩
      have hindex := congrArg PositionAt.index hj
      simp only [LeftPositiveBoundaryExtension.position_index,
        RightExtension.position_index] at hindex
      have hi := i.index_le
      omega

theorem CohookExtension.moduleMap_comp_leftBoundaryModuleMap_eq_zero
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps)
    (hmono : IsMonomial R) :
    cohook.moduleMap hmono ≫ left.moduleMap hmono = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change left.spaceProjection X.unop.as
      (cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion
        X.unop.as v) = 0
  have hzero := cohook.spaceProjection_spaceInclusion_eq_zero
    left hcutoff X.unop.as
  exact LinearMap.congr_fun hzero v

theorem CohookExtension.prefixSuffixSpaceMap_exact
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps) (x : Q) :
    Function.Exact
      (cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion x)
      (left.spaceProjection x) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · exact cohook.spaceProjection_spaceInclusion_eq_zero left hcutoff x
  · intro v hv
    let extension := cohook.toNegativeBoundaryExtension.toRightExtension
    refine ⟨extension.spaceProjection x v, ?_⟩
    change extension.spaceInclusion x (extension.spaceProjection x v) = v
    classical
    apply Finsupp.ext
    intro j
    by_cases hj : ∃ i : K.PositionAt x, extension.position i = j
    · rcases hj with ⟨i, rfl⟩
      rw [RightExtension.spaceInclusion_apply_position,
        RightExtension.spaceProjection_apply_position]
    · rw [extension.spaceInclusion_apply_of_not_exists _ j hj]
      have hjIndex : K.length < j.index := by
        by_contra hnot
        have hjLe : j.index ≤ K.length := Nat.le_of_not_gt hnot
        exact hj (extension.exists_eq_position_of_index_le j hjLe)
      have hjCutoff : left.steps ≤ j.index := by omega
      rcases left.exists_eq_position_of_steps_le j hjCutoff with ⟨i, hi⟩
      have hcoeff := congrArg (fun w : C.Space x ↦ w i) hv
      rw [LeftPositiveBoundaryExtension.spaceProjection_apply_position,
        Finsupp.zero_apply, hi] at hcoeff
      exact hcoeff.symm

def CohookExtension.prefixSuffixShortComplex
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps)
    (hmono : IsMonomial R) :=
  ShortComplex.mk (cohook.moduleMap hmono) (left.moduleMap hmono)
    (cohook.moduleMap_comp_leftBoundaryModuleMap_eq_zero
      left hcutoff hmono)

theorem CohookExtension.prefixSuffixShortComplex_exact
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps)
    (hmono : IsMonomial R) :
    (cohook.prefixSuffixShortComplex left hcutoff hmono).Exact := by
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  change LinearMap.range
      (cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion
        X.unop.as) =
    LinearMap.ker (left.spaceProjection X.unop.as)
  exact (LinearMap.exact_iff.mp
    (cohook.prefixSuffixSpaceMap_exact left hcutoff X.unop.as)).symm

theorem CohookExtension.prefixSuffixShortComplex_shortExact
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps)
    (hmono : IsMonomial R) :
    (cohook.prefixSuffixShortComplex left hcutoff hmono).ShortExact := by
  exact ShortComplex.ShortExact.mk'
    (cohook.prefixSuffixShortComplex_exact left hcutoff hmono)
    (by dsimp [prefixSuffixShortComplex]; infer_instance)
    (by dsimp [prefixSuffixShortComplex]; infer_instance)

structure LeftHookExtension.PurePositiveKernelData
    (C : Word R) (left : LeftHookExtension C) where
  kernel : Word R
  cohook : CohookExtension kernel
    left.toLeftPositiveBoundaryExtension.result
  cutoff : kernel.length + 1 =
    left.toLeftPositiveBoundaryExtension.steps

/-- Regard a right hook on `C` as a left hook on the reversed word. -/
def HookExtension.toReverseLeftHook {C D : Word R}
    (hook : HookExtension C D) : LeftHookExtension C.reverse where
  reverseResult := D
  hook := Eq.mp
    (congrArg (fun W : Word R ↦ HookExtension W D)
      (reverse_reverse R C).symm)
    hook

/-- Extending a word at its left endpoint preserves a peak at its right
endpoint. -/
theorem LeftHookExtension.result_startsOnPeak_of_startsOnPeak
    {C : Word R} (left : LeftHookExtension C)
    (hstart : C.StartsOnPeak) : left.result.StartsOnPeak := by
  rw [← leftHookBaseWord_eq_result left]
  intro z a hnew
  apply hstart a
  apply IsString.of_contiguousSubpath R hnew
  let basePath :=
    left.hook.tail.toRightExtension.suffixPath.reverse.comp
      (negativeArrow left.hook.arrow).toPath
  refine ⟨basePath, Quiver.Path.nil, ?_⟩
  simp only [leftHookBaseWord, ofStringPath, leftHookBasePath,
    basePath, Quiver.Path.comp_nil]
  let tailPath := left.hook.tail.toRightExtension.suffixPath.reverse
  let boundary := (negativeArrow left.hook.arrow).toPath
  let newArrow := (positiveArrow a).toPath
  calc
    tailPath.comp ((boundary.comp C.path).comp newArrow) =
        tailPath.comp (boundary.comp (C.path.comp newArrow)) :=
      congrArg (fun p ↦ tailPath.comp p)
        (Quiver.Path.comp_assoc boundary C.path newArrow)
    _ = (tailPath.comp boundary).comp (C.path.comp newArrow) :=
      (Quiver.Path.comp_assoc tailPath boundary
        (C.path.comp newArrow)).symm

/-- Construct the cohook kernel of a pure-positive left-hook projection when
the hooked result is maximal at its right endpoint. -/
def LeftHookExtension.purePositiveKernelDataOfResultPeak
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (left : LeftHookExtension C)
    (hresultPeak : left.result.StartsOnPeak) :
    LeftHookExtension.PurePositiveKernelData C left := by
  let tailPath := left.hook.tail.toRightExtension.suffixPath.reverse
  have hkernel : IsString R tailPath := by
    apply IsString.of_contiguousSubpath R (leftHookPath_isString left)
    refine ⟨Quiver.Path.nil,
      (negativeArrow left.hook.arrow).toPath.comp C.path, ?_⟩
    simp only [Quiver.Path.nil_comp, tailPath]
  let K : Word R := ofStringPath tailPath hkernel
  let basePath := tailPath.comp (negativeArrow left.hook.arrow).toPath
  have hbase : IsString R basePath := by
    apply IsString.of_contiguousSubpath R (leftHookPath_isString left)
    refine ⟨Quiver.Path.nil, C.path, ?_⟩
    simp only [Quiver.Path.nil_comp, basePath, tailPath,
      Quiver.Path.comp_assoc]
    rfl
  let arm := Classical.choice hpure
  have hCpath : C.path = positivePath arm.ordinaryPath := by
    have hfactor := arm.toRightExtension.path_cast_comp_suffixPath
    rw [arm.toRightExtension_suffixPath_eq_positivePath] at hfactor
    simpa [vertex] using hfactor
  have hsuffix : arm.toRightExtension.suffixPath = C.path := by
    rw [arm.toRightExtension_suffixPath_eq_positivePath, hCpath]
  have hfull : IsString R
      (basePath.comp arm.toRightExtension.suffixPath) := by
    rw [hsuffix]
    change IsString R
      ((tailPath.comp (negativeArrow left.hook.arrow).toPath).comp C.path)
    rw [Quiver.Path.comp_assoc]
    exact leftHookPath_isString left
  let replay := arm.rebasePositive basePath hbase hfull
  let firstWord : Word R :=
    append R K (negativeArrow left.hook.arrow) hbase
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayTail : PositiveExtension firstWord replay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ PositiveExtension W replay.result)
        hreplayBase)
      replay.rebased
  have hpath : basePath.comp arm.toRightExtension.suffixPath =
      leftHookBasePath left := by
    rw [hsuffix]
    simp only [basePath, tailPath, leftHookBasePath,
      Quiver.Path.comp_assoc]
    rfl
  have hresultBase : replay.result = leftHookBaseWord left := by
    apply Word.ext
    · exact replay.source_eq
    · exact replay.target_eq
    · exact HEq.trans
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          replay.source_eq replay.target_eq replay.result.path).symm
        (heq_of_eq (replay.path_cast_eq.trans hpath))
  have hresult : replay.result = left.result :=
    hresultBase.trans (leftHookBaseWord_eq_result left)
  let cohookBase : CohookExtension K replay.result := {
    vertex := C.source
    arrow := left.hook.arrow
    valid := hbase
    tail := replayTail
    maximal := by rw [hresult]; exact hresultPeak }
  have hresultExtension : replay.result =
      left.toLeftPositiveBoundaryExtension.result := hresult
  let cohook : CohookExtension K
      left.toLeftPositiveBoundaryExtension.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ CohookExtension K W) hresultExtension)
      cohookBase
  exact {
    kernel := K
    cohook := cohook
    cutoff := by
      dsimp only [K, ofStringPath, Word.length, tailPath,
        LeftHookExtension.toLeftPositiveBoundaryExtension,
        LeftPositiveBoundaryExtension.steps, HookExtension.steps]
      rw [length_reverse, RightExtension.suffixPath_length,
        NegativeExtension.toRightExtension_steps]
      simp only [HookExtension.toPositiveBoundaryExtension,
        PositiveBoundaryExtension.toRightExtension_steps,
        NegativeExtension.toRightExtension_steps] }

/-- The kernel data in the common one-sided case where the original pure
word is already maximal at its right endpoint. -/
def LeftHookExtension.purePositiveKernelData
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (hstart : C.StartsOnPeak)
    (left : LeftHookExtension C) :
    LeftHookExtension.PurePositiveKernelData C left :=
  left.purePositiveKernelDataOfResultPeak hR hpure
    (left.result_startsOnPeak_of_startsOnPeak hstart)

section Finite

variable [Fintype Q]

def CohookExtension.prefixSuffixFiniteShortComplex
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps)
    (hmono : IsMonomial R) :=
  ShortComplex.mk
    (finiteRightModuleHom hmono (cohook.moduleMap hmono))
    (finiteRightModuleHom hmono (left.moduleMap hmono)) (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact cohook.moduleMap_comp_leftBoundaryModuleMap_eq_zero
        left hcutoff hmono)

theorem CohookExtension.prefixSuffixFiniteShortComplex_shortExact
    {K C : Word R} (left : LeftPositiveBoundaryExtension C)
    (cohook : CohookExtension K left.result)
    (hcutoff : K.length + 1 = left.steps)
    (hmono : IsMonomial R) :
    (cohook.prefixSuffixFiniteShortComplex
      left hcutoff hmono).ShortExact := by
  let P := CoveringHom.IsFiniteDimensionalModule
      (C := (Category R)ᵒᵖ) k
  let L := CoveringHom.IsLinearModule (C := (Category R)ᵒᵖ) k
  let J : CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category R)ᵒᵖ) k ⥤
      ((Category R)ᵒᵖ ⥤ ModuleCat k) := P.ι ⋙ L.ι
  apply ShortExact.reflects_shortExact_of_faithful J
  convert cohook.prefixSuffixShortComplex_shortExact
    left hcutoff hmono using 1
  all_goals rfl

/-- The unary finite complex whenever the pure-positive hook result is a
peak at its right endpoint. -/
def LeftHookExtension.purePositiveResultPeakFiniteShortComplex
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (left : LeftHookExtension C)
    (hresultPeak : left.result.StartsOnPeak) (hmono : IsMonomial R) :=
  let data :=
    left.purePositiveKernelDataOfResultPeak hR hpure hresultPeak
  data.cohook.prefixSuffixFiniteShortComplex
    left.toLeftPositiveBoundaryExtension data.cutoff hmono

theorem LeftHookExtension.purePositiveResultPeakFiniteShortComplex_shortExact
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (left : LeftHookExtension C)
    (hresultPeak : left.result.StartsOnPeak) (hmono : IsMonomial R) :
    (left.purePositiveResultPeakFiniteShortComplex
      hR hpure hresultPeak hmono).ShortExact := by
  let data :=
    left.purePositiveKernelDataOfResultPeak hR hpure hresultPeak
  exact data.cohook.prefixSuffixFiniteShortComplex_shortExact
    left.toLeftPositiveBoundaryExtension data.cutoff hmono

theorem LeftHookExtension.purePositiveResultPeakFiniteShortComplex_f_isIrreducible
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (left : LeftHookExtension C)
    (hresultPeak : left.result.StartsOnPeak) (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism
      (left.purePositiveResultPeakFiniteShortComplex
        hR hpure hresultPeak hmono).f := by
  let data :=
    left.purePositiveKernelDataOfResultPeak hR hpure hresultPeak
  change IsIrreducibleMorphism (data.cohook.finiteModuleMap hmono)
  exact data.cohook.finiteModuleMap_isIrreducible_of_finiteStringSum
    hmono hcover

theorem LeftHookExtension.purePositiveResultPeakFiniteShortComplex_g_isIrreducible
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (left : LeftHookExtension C)
    (hresultPeak : left.result.StartsOnPeak) (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism
      (left.purePositiveResultPeakFiniteShortComplex
        hR hpure hresultPeak hmono).g := by
  change IsIrreducibleMorphism (left.finiteModuleMap hmono)
  exact left.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover

def LeftHookExtension.purePositiveFiniteShortComplex
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (hstart : C.StartsOnPeak)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :=
  let data := left.purePositiveKernelData hR hpure hstart
  data.cohook.prefixSuffixFiniteShortComplex
    left.toLeftPositiveBoundaryExtension data.cutoff hmono

theorem LeftHookExtension.purePositiveFiniteShortComplex_shortExact
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (hstart : C.StartsOnPeak)
    (left : LeftHookExtension C) (hmono : IsMonomial R) :
    (left.purePositiveFiniteShortComplex
      hR hpure hstart hmono).ShortExact := by
  let data := left.purePositiveKernelData hR hpure hstart
  exact data.cohook.prefixSuffixFiniteShortComplex_shortExact
    left.toLeftPositiveBoundaryExtension data.cutoff hmono

theorem LeftHookExtension.purePositiveFiniteShortComplex_f_isIrreducible
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (hstart : C.StartsOnPeak)
    (left : LeftHookExtension C) (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism
      (left.purePositiveFiniteShortComplex
        hR hpure hstart hmono).f := by
  let data := left.purePositiveKernelData hR hpure hstart
  change IsIrreducibleMorphism (data.cohook.finiteModuleMap hmono)
  exact data.cohook.finiteModuleMap_isIrreducible_of_finiteStringSum
    hmono hcover

theorem LeftHookExtension.purePositiveFiniteShortComplex_g_isIrreducible
    (hR : IsAdmissible R) {C : Word R}
    (hpure : C.IsPurePositive hR) (hstart : C.StartsOnPeak)
    (left : LeftHookExtension C) (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism
      (left.purePositiveFiniteShortComplex
        hR hpure hstart hmono).g := by
  change IsIrreducibleMorphism (left.finiteModuleMap hmono)
  exact left.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover

end Finite

end MagnitudeConjecture.BoundQuiver.StringWord.Word
