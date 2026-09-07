import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMaps

/-!
# Injectivity of universal restricted-Yoneda Hom maps
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

local instance standardFormUniversalInjectiveQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalInjectiveArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

theorem standardFormUniversalRestrictedYonedaShiftHomLinearMap_injective
    (p : Fin S.n) (X Y : SourceCategory S p)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p)) :
    Function.Injective
      (standardFormUniversalRestrictedYonedaShiftHomLinearMap S p X Y a) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := DAmbient.hasShift
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  let U := standardFormUniversalRestrictedYonedaFunctor S p
  letI : U.Faithful :=
    standardFormUniversalRestrictedYonedaFunctor_faithful S p
  let eFinite := standardFormUniversalRestrictedYonedaShiftIso S p a Y
  let e : (U.obj Y).obj⟦a⟧ ≅
      (U.obj ((DAmbient.core.F a).obj Y)).obj :=
    (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) (U.obj Y) a).symm ≪≫
      (CoveringHom.IsFiniteDimensionalModule
        (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k).ι.mapIso eFinite
  intro f g hfg
  change (U.map f).hom ≫ e.inv = (U.map g).hom ≫ e.inv at hfg
  apply U.map_injective
  apply ObjectProperty.hom_ext
  apply (cancel_mono e.inv).1
  exact hfg

theorem standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap_injective
    (p : Fin S.n) (X Y : SourceCategory S p) :
    Function.Injective
      (standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap S p X Y) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := DAmbient.hasShift
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  apply (DFinsupp.mapRange_injective
    (fun a ↦ standardFormUniversalRestrictedYonedaShiftHomLinearMap
      S p X Y a) (fun a ↦ LinearMap.map_zero _)).2
  intro a
  exact standardFormUniversalRestrictedYonedaShiftHomLinearMap_injective
    S p X Y a

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
