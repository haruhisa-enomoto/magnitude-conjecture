import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalYonedaUnderlyingObject

/-! # The target zero-degree shift-Hom coordinate -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomMapsShiftZeroTargetChoiceQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalHomMapsShiftZeroTargetChoiceArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

universe uC uG uK

/-- A small generic boundary around the canonical degree-zero coordinate.
Keeping the large standard-form functor objects outside the linear-equivalence
structure substantially reduces elaboration memory. -/
private noncomputable def shiftHomZeroTargetLinearMapAux
    {C : Type uC} [CategoryTheory.Category C] [Preadditive C]
    {G : Type uG} [AddGroup G] [HasShift C G]
    {R : Type uK} [CommSemiring R] [CategoryTheory.Linear R C]
    (X Y : C) : (X ⟶ Y) →ₗ[R] CoveringHom.ShiftHom X Y (0 : G) :=
  (CoveringHom.shiftHomZeroLinearEquiv (A := G) X Y).toLinearMap

private theorem shiftHomZeroTargetLinearMapAux_injective
    {C : Type uC} [CategoryTheory.Category C] [Preadditive C]
    {G : Type uG} [AddGroup G] [HasShift C G]
    {R : Type uK} [CommSemiring R] [CategoryTheory.Linear R C]
    (X Y : C) : Function.Injective
      (shiftHomZeroTargetLinearMapAux (G := G) (R := R) X Y) :=
  (CoveringHom.shiftHomZeroLinearEquiv (A := G) X Y).injective

/-- Linear-map form of the target degree-zero coordinate. -/
noncomputable def standardFormUniversalShiftHomZeroTargetLinearMap
    (p : Fin S.n) (X Y : SourceCategory S p) := by
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  exact shiftHomZeroTargetLinearMapAux
    (G := Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p)) (R := k)
    (standardFormUniversalRestrictedYonedaUnderlyingObject S p X)
    (standardFormUniversalRestrictedYonedaUnderlyingObject S p Y)

/-- The target degree-zero coordinate is injective. -/
theorem standardFormUniversalShiftHomZeroTargetLinearMap_injective
    (p : Fin S.n) (X Y : SourceCategory S p) :
    Function.Injective
      (standardFormUniversalShiftHomZeroTargetLinearMap S p X Y) := by
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  exact shiftHomZeroTargetLinearMapAux_injective
    (G := Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p)) (R := k)
    (standardFormUniversalRestrictedYonedaUnderlyingObject S p X)
    (standardFormUniversalRestrictedYonedaUnderlyingObject S p Y)


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
