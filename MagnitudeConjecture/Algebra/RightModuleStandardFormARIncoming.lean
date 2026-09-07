import MagnitudeConjecture.Algebra.RightModuleStandardFormARShortExact

/-!
# Recovered incoming maps for the standard-form algebra

This file identifies the recovered incoming map with its biproduct formula and
proves right minimality at every standard-form label.
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

local instance standardFormARIncomingQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARIncomingArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The recovered complete incoming map at any standard-form label, with its
singleton endpoint identified with the literal recovered indecomposable
skeleton object. -/
def standardFormRecoveredIncomingMap
    (z : Fin S.n) :
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
        (S.standardFormRightMeshData.additiveIncomingObj (k := k) z) ⟶
      (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
        (k := k)).obj z :=
  biproduct.desc (fun a : MeshCategory.RightMeshData.IncomingArrow z ↦
    (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).map
        (S.standardFormRightMeshData.incomingArrowHom (k := k) a))

set_option backward.isDefEq.respectTransparency false in
/-- The recovered incoming map is literally the biproduct descendant of the
restricted-Yoneda images of all incoming mesh arrows. -/
theorem standardFormRecoveredIncomingMap_eq_biproduct_desc
    (z : Fin S.n) :
    S.standardFormRecoveredIncomingMap (k := k) z =
      biproduct.desc (fun a : MeshCategory.RightMeshData.IncomingArrow z ↦
        (S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite).map
            (S.standardFormRightMeshData.incomingArrowHom (k := k) a)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The biproduct-defined recovered incoming map is the restricted-Yoneda
image of the additive incoming mesh map, followed by the singleton endpoint
identification. -/
theorem standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso
    (z : Fin S.n) :
    S.standardFormRecoveredIncomingMap (k := k) z =
      (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).map
          (S.standardFormRightMeshData.additiveIncomingMap (k := k) z) ≫
        (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) z).hom := by
  symm
  apply biproduct.hom_ext'
  intro a
  dsimp only [standardFormRecoveredIncomingMap,
    standardFormAdditiveRestrictedYonedaFunctor,
    standardFormVertexRestrictedYonedaFunctor,
    standardFormMeshRawFunctor, finiteMatrixLift,
    MeshCategory.RightMeshData.additiveIncomingMap,
    MeshCategory.RightMeshData.additiveIncomingObj,
    MeshCategory.RightMeshData.additiveVertexObj, Mat_.embedding,
    standardFormAdditiveRestrictedYonedaSingletonIso]
  simp [biproduct.lift_desc]

/-- At an original projective label, the recovered incoming map is monic. -/
theorem standardFormRecoveredIncomingMap_mono_of_projective
    (z : Fin S.n) (hz : Projective (S.fgObj z)) :
    Mono (S.standardFormRecoveredIncomingMap (k := k) z) := by
  letI : Mono
      (S.standardFormRightMeshData.additiveIncomingMap (k := k) z) :=
    S.standardFormAdditiveIncomingMap_mono_of_projective
      (k := k) z (by simpa [standardFormProjectiveSet] using hz)
  let F := S.standardFormAdditiveRestrictedYonedaFunctor (k := k)
  haveI : Mono
      (F.map (S.standardFormRightMeshData.additiveIncomingMap (k := k) z)) :=
    F.map_mono (S.standardFormRightMeshData.additiveIncomingMap (k := k) z)
  rw [S.standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso
    (k := k) z]
  change Mono
    (F.map (S.standardFormRightMeshData.additiveIncomingMap (k := k) z) ≫
      (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) z).hom)
  infer_instance

/-- The recovered incoming map is right minimal at every label.  At a
projective label this follows from monicity; at a nonprojective label it is
the terminal map of the recovered short exact mesh. -/
theorem standardFormRecoveredIncomingMap_rightMinimal
    (z : Fin S.n) :
    IsRightMinimal (S.standardFormRecoveredIncomingMap (k := k) z) := by
  by_cases hz : Projective (S.fgObj z)
  · letI : Mono (S.standardFormRecoveredIncomingMap (k := k) z) :=
      S.standardFormRecoveredIncomingMap_mono_of_projective (k := k) z hz
    intro a ha
    have haid : a = 𝟙 _ := by
      apply (cancel_mono (S.standardFormRecoveredIncomingMap (k := k) z)).1
      simpa using ha
    rw [haid]
    infer_instance
  · let zn : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
      ⟨z, by simpa [standardFormProjectiveSet] using hz⟩
    rw [S.standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso
      (k := k) z]
    change IsRightMinimal
      ((S.standardFormRecoveredRightMesh (k := k) zn).g ≫
        (S.standardFormAdditiveRestrictedYonedaSingletonIso
          (k := k) z).hom)
    exact IsRightMinimal.postcomp_iso
      (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) z)
      (S.standardFormRecoveredRightMesh_g_rightMinimal (k := k) zn)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
