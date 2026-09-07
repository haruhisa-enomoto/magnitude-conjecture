import MagnitudeConjecture.Algebra.StringIndecomposable
import MagnitudeConjecture.Algebra.StringLeftHookCohook
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix

/-!
# Strict hook and cohook morphisms

Every hook or cohook adds at least one word position.  The canonical hook
projection kills a new position, while the canonical cohook inclusion misses
one.  Thus the four right-module maps at the two word endpoints are proper
epimorphisms or proper monomorphisms.  String-module indecomposability then
rules out a splitting in the other direction as well.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The final position of a nontrivial right extension is not inherited from
the original word. -/
theorem RightExtension.not_exists_position_targetPosition
    {C D : Word R} (extension : RightExtension C D)
    (hsteps : extension.steps ≠ 0) :
    ¬ ∃ i : C.PositionAt D.target,
      extension.position i = D.targetPosition := by
  rintro ⟨i, hi⟩
  have hindex := congrArg PositionAt.index hi
  rw [extension.position_index, D.targetPosition_index,
    extension.result_length] at hindex
  have hiLe := i.index_le
  omega

/-- The coordinate inclusion of a nontrivial right extension misses its new
final position. -/
theorem RightExtension.spaceInclusion_not_surjective
    {C D : Word R} (extension : RightExtension C D)
    (hsteps : extension.steps ≠ 0) :
    ¬ Function.Surjective (extension.spaceInclusion D.target) := by
  intro hsurjective
  obtain ⟨v, hv⟩ := hsurjective (Finsupp.single D.targetPosition 1)
  have hnew := extension.not_exists_position_targetPosition hsteps
  have hzero := extension.spaceInclusion_apply_of_not_exists
    v D.targetPosition hnew
  have hcoeff := congrArg (fun w : D.Space D.target ↦ w D.targetPosition) hv
  simp only [hzero, Finsupp.single_eq_same] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- The coordinate projection of a nontrivial right extension kills its new
final basis vector. -/
theorem RightExtension.spaceProjection_not_injective
    {C D : Word R} (extension : RightExtension C D)
    (hsteps : extension.steps ≠ 0) :
    ¬ Function.Injective (extension.spaceProjection D.target) := by
  intro hinjective
  have hnew := extension.not_exists_position_targetPosition hsteps
  have hzero := extension.spaceProjection_single_of_not_exists
    D.targetPosition 1 hnew
  have hsingle : (Finsupp.single D.targetPosition (1 : k) : D.Space D.target) = 0 :=
    hinjective (by simpa only [map_zero] using hzero)
  have hcoeff := congrArg
    (fun w : D.Space D.target ↦ w D.targetPosition) hsingle
  simp at hcoeff

/-- The source position of a nontrivial left extension is not inherited from
the original word. -/
theorem LeftPositiveBoundaryExtension.not_exists_position_sourcePosition
    {C : Word R} (extension : LeftPositiveBoundaryExtension C) :
    ¬ ∃ i : C.PositionAt extension.result.source,
      extension.position i = extension.result.sourcePosition := by
  rintro ⟨i, hi⟩
  have hindex := congrArg PositionAt.index hi
  rw [extension.position_index, extension.result.sourcePosition_index] at hindex
  have hsteps : extension.steps ≠ 0 := by
    simp [LeftPositiveBoundaryExtension.steps]
  omega

/-- The source position of a nontrivial negative left extension is not
inherited from the original word. -/
theorem LeftNegativeBoundaryExtension.not_exists_position_sourcePosition
    {C : Word R} (extension : LeftNegativeBoundaryExtension C) :
    ¬ ∃ i : C.PositionAt extension.result.source,
      extension.position i = extension.result.sourcePosition := by
  rintro ⟨i, hi⟩
  have hindex := congrArg PositionAt.index hi
  rw [extension.position_index, extension.result.sourcePosition_index] at hindex
  have hsteps : extension.steps ≠ 0 := by
    simp [LeftNegativeBoundaryExtension.steps]
  omega

/-- A negative right-boundary inclusion is a proper monomorphism. -/
theorem NegativeBoundaryExtension.rightModuleInclusion_not_epi
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    ¬ Epi (extension.rightModuleInclusion hmono) := by
  intro hepi
  letI : Epi (extension.rightModuleInclusion hmono) := hepi
  have happ : Epi ((extension.rightModuleInclusion hmono).app
      (Opposite.op (obj R D.target))) := by infer_instance
  have hsurjective := (ModuleCat.epi_iff_surjective _).mp happ
  exact extension.toRightExtension.spaceInclusion_not_surjective
    (by simp) hsurjective

/-- A positive right-boundary projection is a proper epimorphism. -/
theorem PositiveBoundaryExtension.rightModuleProjection_not_mono
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    ¬ Mono (extension.rightModuleProjection hmono) := by
  intro hmonoMap
  letI : Mono (extension.rightModuleProjection hmono) := hmonoMap
  have happ : Mono ((extension.rightModuleProjection hmono).app
      (Opposite.op (obj R D.target))) := by infer_instance
  have hinjective := (ModuleCat.mono_iff_injective _).mp happ
  exact extension.toRightExtension.spaceProjection_not_injective
    (by simp) hinjective

/-- A positive left-boundary projection is a proper epimorphism. -/
theorem LeftPositiveBoundaryExtension.moduleMap_not_mono
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) :
    ¬ Mono (extension.moduleMap hmono) := by
  intro hmonoMap
  letI : Mono (extension.moduleMap hmono) := hmonoMap
  have happ : Mono ((extension.moduleMap hmono).app
      (Opposite.op (obj R extension.result.source))) := by infer_instance
  have hinjective := (ModuleCat.mono_iff_injective _).mp happ
  have hnew := extension.not_exists_position_sourcePosition
  have hzero := extension.spaceProjection_single_of_not_exists
    extension.result.sourcePosition 1 hnew
  have hsingle :
      (Finsupp.single extension.result.sourcePosition (1 : k) :
        extension.result.Space extension.result.source) = 0 := by
    apply hinjective
    change extension.spaceProjection extension.result.source
        (Finsupp.single extension.result.sourcePosition 1) =
      extension.spaceProjection extension.result.source 0
    simpa using hzero
  have hcoeff := congrArg
    (fun w : extension.result.Space extension.result.source ↦
      w extension.result.sourcePosition)
    hsingle
  simp at hcoeff

/-- A negative left-boundary inclusion is a proper monomorphism. -/
theorem LeftNegativeBoundaryExtension.moduleMap_not_epi
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) :
    ¬ Epi (extension.moduleMap hmono) := by
  intro hepi
  letI : Epi (extension.moduleMap hmono) := hepi
  have happ : Epi ((extension.moduleMap hmono).app
      (Opposite.op (obj R extension.result.source))) := by infer_instance
  have hsurjective := (ModuleCat.epi_iff_surjective _).mp happ
  obtain ⟨v, hv⟩ := hsurjective
    (Finsupp.single extension.result.sourcePosition 1)
  change extension.spaceInclusion extension.result.source v =
    Finsupp.single extension.result.sourcePosition 1 at hv
  have hnew := extension.not_exists_position_sourcePosition
  have hzero := extension.spaceInclusion_apply_of_not_exists
    v extension.result.sourcePosition hnew
  have hzero' :
      extension.spaceInclusion extension.result.source v
          extension.result.sourcePosition = 0 := by
    exact hzero
  have hcoeff := congrArg
    (fun w : extension.result.Space extension.result.source ↦
      w extension.result.sourcePosition) hv
  rw [hzero'] at hcoeff
  simp only [Finsupp.single_eq_same] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- A right hook projection is not monic. -/
theorem HookExtension.moduleMap_not_mono
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) : ¬ Mono (hook.moduleMap hmono) :=
  hook.toPositiveBoundaryExtension.rightModuleProjection_not_mono hmono

/-- A right hook projection is not split monic. -/
theorem HookExtension.moduleMap_not_isSplitMono
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) : ¬ IsSplitMono (hook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitMono (hook.moduleMap hmono) := hsplit
  exact hook.moduleMap_not_mono hmono inferInstance

/-- A right hook projection is not split epic. -/
theorem HookExtension.moduleMap_not_isSplitEpi
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) : ¬ IsSplitEpi (hook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitEpi (hook.moduleMap hmono) := hsplit
  have hD : Indecomposable (D.rightModule hmono) :=
    D.rightModule_indecomposable hmono
  haveI : IsIso (hook.moduleMap hmono) :=
    isIso_of_isSplitEpi_from_indecomposable hD _
      (C.rightModule_not_isZero hmono)
  exact hook.moduleMap_not_mono hmono inferInstance

/-- A right cohook inclusion is not epic. -/
theorem CohookExtension.moduleMap_not_epi
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) : ¬ Epi (cohook.moduleMap hmono) :=
  cohook.toNegativeBoundaryExtension.rightModuleInclusion_not_epi hmono

/-- A right cohook inclusion is not split epic. -/
theorem CohookExtension.moduleMap_not_isSplitEpi
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) : ¬ IsSplitEpi (cohook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitEpi (cohook.moduleMap hmono) := hsplit
  exact cohook.moduleMap_not_epi hmono inferInstance

/-- A right cohook inclusion is not split monic. -/
theorem CohookExtension.moduleMap_not_isSplitMono
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) : ¬ IsSplitMono (cohook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitMono (cohook.moduleMap hmono) := hsplit
  have hD : Indecomposable (D.rightModule hmono) :=
    D.rightModule_indecomposable hmono
  haveI : IsIso (cohook.moduleMap hmono) :=
    isIso_of_isSplitMono_to_indecomposable hD _
      (C.rightModule_not_isZero hmono)
  exact cohook.moduleMap_not_epi hmono inferInstance

/-- A left hook projection is not monic. -/
theorem LeftHookExtension.moduleMap_not_mono
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) : ¬ Mono (hook.moduleMap hmono) :=
  hook.toLeftPositiveBoundaryExtension.moduleMap_not_mono hmono

/-- A left hook projection is not split monic. -/
theorem LeftHookExtension.moduleMap_not_isSplitMono
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) : ¬ IsSplitMono (hook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitMono (hook.moduleMap hmono) := hsplit
  exact hook.moduleMap_not_mono hmono inferInstance

/-- A left hook projection is not split epic. -/
theorem LeftHookExtension.moduleMap_not_isSplitEpi
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) : ¬ IsSplitEpi (hook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitEpi (hook.moduleMap hmono) := hsplit
  have hD : Indecomposable (hook.result.rightModule hmono) :=
    hook.result.rightModule_indecomposable hmono
  haveI : IsIso (hook.moduleMap hmono) :=
    isIso_of_isSplitEpi_from_indecomposable hD _
      (C.rightModule_not_isZero hmono)
  exact hook.moduleMap_not_mono hmono inferInstance

/-- A left cohook inclusion is not epic. -/
theorem LeftCohookExtension.moduleMap_not_epi
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) : ¬ Epi (cohook.moduleMap hmono) :=
  cohook.toLeftNegativeBoundaryExtension.moduleMap_not_epi hmono

/-- A left cohook inclusion is not split epic. -/
theorem LeftCohookExtension.moduleMap_not_isSplitEpi
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) : ¬ IsSplitEpi (cohook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitEpi (cohook.moduleMap hmono) := hsplit
  exact cohook.moduleMap_not_epi hmono inferInstance

/-- A left cohook inclusion is not split monic. -/
theorem LeftCohookExtension.moduleMap_not_isSplitMono
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) : ¬ IsSplitMono (cohook.moduleMap hmono) := by
  intro hsplit
  letI : IsSplitMono (cohook.moduleMap hmono) := hsplit
  have hD : Indecomposable (cohook.result.rightModule hmono) :=
    cohook.result.rightModule_indecomposable hmono
  haveI : IsIso (cohook.moduleMap hmono) :=
    isIso_of_isSplitMono_to_indecomposable hD _
      (C.rightModule_not_isZero hmono)
  exact cohook.moduleMap_not_epi hmono inferInstance

end MagnitudeConjecture.BoundQuiver.StringWord.Word
