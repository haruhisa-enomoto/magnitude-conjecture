import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalSurjective
import MagnitudeConjecture.LinearAlgebra.DFinsuppComponentSurjective

/-!
# Degree-zero homogeneous surjectivity of universal restricted Yoneda
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalShiftZeroSurjectiveQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalShiftZeroSurjectiveArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- Surjectivity of the shift-orbit map implies surjectivity of its
degree-zero homogeneous component. -/
theorem standardFormUniversalRestrictedYonedaShiftHomZeroLinearMap_surjective
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :
    Function.Surjective
      (standardFormUniversalRestrictedYonedaShiftHomLinearMap S p X Y 0) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := DAmbient.hasShift
  letI := DAmbient.additiveShift
  letI := DAmbient.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := CoveringHom.isLinearModule_stableUnderShift (k := k) D.core
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  letI := CoveringHom.linearModuleCategoryAdditiveShift (R := k) D.core
  letI := CoveringHom.linearModuleCategoryLinearShift (R := k) D.core
  classical
  exact DFinsupp.linearMap_component_surjective _
    (standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap_surjective
      S p hconnected X Y) 0

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
