import MagnitudeConjecture.Algebra.RightModuleStandardFormAlgebraSkeleton
import MagnitudeConjecture.Algebra.RightModuleStandardFormSimpleResolution
import MagnitudeConjecture.CategoryTheory.AlmostSplitShortExact
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable

/-!
# Short exact recovered standard-form meshes

The additive standard mesh becomes a nonsplit short exact sequence under the
recovered restricted-Yoneda equivalence, and its terminal map is right minimal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The additive standard mesh after restricted-Yoneda recovery. -/
abbrev standardFormRecoveredRightMesh
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    ShortComplex (S.StandardFormProjectiveVertexModuleCategory (k := k)) :=
  (S.standardFormAdditiveRightMesh (k := k) z).map
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k))

/-- Recovered standard meshes are short exact. -/
theorem standardFormRecoveredRightMesh_shortExact
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    (S.standardFormRecoveredRightMesh (k := k) z).ShortExact := by
  let T := S.standardFormRightMeshData
  let E := S.standardFormAdditiveRestrictedYonedaEquivalence (k := k)
  let F := E.functor
  let M := S.standardFormRecoveredRightMesh (k := k) z
  letI : Mono (T.additiveTranslationMap (k := k) z) :=
    S.standardFormAdditiveTranslationMap_mono z
  haveI : Mono M.f := by
    dsimp only [M, standardFormRecoveredRightMesh,
      standardFormAdditiveRightMesh, MeshCategory.RightMeshData.additiveRightMesh]
    exact F.map_mono (T.additiveTranslationMap (k := k) z)
  letI : Epi (T.additiveIncomingMap (k := k) z.1) :=
    (S.standardFormRiedtmannConditionB_iff_incoming_epi
      (k := k)).1 S.standardFormRiedtmannConditionB z
  haveI : Epi M.g := by
    dsimp only [M, standardFormRecoveredRightMesh,
      standardFormAdditiveRightMesh, MeshCategory.RightMeshData.additiveRightMesh]
    exact F.map_epi (T.additiveIncomingMap (k := k) z.1)
  have hWeak : QuotientSubmoduleEquidistribution.Iyama.ShortComplex.IsWeakKernel M :=
    MagnitudeConjecture.CategoryTheory.isWeakKernel_map_equivalence
      (S.standardFormAdditiveRightMesh_isWeakKernel (k := k) z)
      E
  exact
    { exact := M.exact_of_f_is_kernel
        (MagnitudeConjecture.CategoryTheory.isLimit_kernelFork_of_isWeakKernel hWeak)
      mono_f := inferInstance
      epi_g := inferInstance }

/-- The recovered incoming mesh remains nonsplit. -/
theorem standardFormRecoveredRightMesh_g_not_splitEpi
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    ¬ IsSplitEpi (S.standardFormRecoveredRightMesh (k := k) z).g := by
  let T := S.standardFormRightMeshData
  let F := S.standardFormAdditiveRestrictedYonedaFunctor (k := k)
  change ¬ IsSplitEpi (F.map (T.additiveIncomingMap (k := k) z.1))
  intro hsplit
  exact T.additiveIncomingMap_not_splitEpi (k := k) z.1
    ((F.isSplitEpi_iff (T.additiveIncomingMap (k := k) z.1)).mp hsplit)

/-- The recovered incoming mesh is right minimal. -/
theorem standardFormRecoveredRightMesh_g_rightMinimal
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    IsRightMinimal (S.standardFormRecoveredRightMesh (k := k) z).g := by
  let M := S.standardFormRecoveredRightMesh (k := k) z
  let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  let e := S.standardFormAdditiveRestrictedYonedaSingletonIso
    (k := k) (S.standardFormRightMeshData.tau z)
  have hInd : Indecomposable M.X₁ :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).mpr
      (sigma.indecomposable (S.standardFormRightMeshData.tau z))
  letI : IsLocalRing (End M.X₁) :=
    finiteDimensionalModule_end_isLocalRing k M.X₁ hInd
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_local_end
      (S.standardFormRecoveredRightMesh_shortExact (k := k) z)
      (S.standardFormRecoveredRightMesh_g_not_splitEpi (k := k) z)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
