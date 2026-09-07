import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivDownstairs

/-!
# Universal Hom comparison: Gabriel push-down
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

local instance standardFormUniversalHomEquivPushdownQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalHomEquivPushdownArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

set_option maxHeartbeats 800000 in
/-- Gabriel push-down gives the final linear Hom equivalence in the universal
comparison chain. -/
noncomputable def standardFormUniversalPushdownHomLinearEquiv
    (p : Fin S.n) (X Y : SourceCategory S p) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
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
  let U := standardFormUniversalRestrictedYonedaFunctor S p
  exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
      (k := k) (U.obj X) (U.obj Y)).symm

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
