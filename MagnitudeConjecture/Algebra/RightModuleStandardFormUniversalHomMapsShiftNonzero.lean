import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMapsShiftZero

/-! # The nonzero-degree formula for universal restricted Yoneda -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomMapsShiftNonzeroQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalHomMapsShiftNonzeroArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The positive-degree formula: map the ambient morphism and then identify
the shifted restricted representable with the translated representable. -/
noncomputable def standardFormUniversalRestrictedYonedaShiftHomNonzeroLinearMap
    (p : Fin S.n) (X Y : SourceCategory S p)
    (a : Additive (StandardFormProjectiveGroup S p)) :
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let D := standardFormOppositeProjectiveDeckShift S p
    letI := DAmbient.hasShift
    letI := D.hasShift
    letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
    CoveringHom.ShiftHom X Y a →ₗ[k]
      CoveringHom.ShiftHom
        ((standardFormUniversalRestrictedYonedaFunctor S p).obj X).obj
        ((standardFormUniversalRestrictedYonedaFunctor S p).obj Y).obj a := by
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
  let eFinite := standardFormUniversalRestrictedYonedaShiftIso S p a Y
  let e : (U.obj Y).obj⟦a⟧ ≅
      (U.obj ((DAmbient.core.F a).obj Y)).obj :=
    (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) (U.obj Y) a).symm ≪≫
      (CoveringHom.IsFiniteDimensionalModule
        (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k).ι.mapIso eFinite
  exact
    { toFun := fun f ↦ (U.map f).hom ≫ e.inv
      map_add' := fun f g ↦ by
        rw [U.map_add]
        change ((U.map f).hom + (U.map g).hom) ≫ e.inv =
          (U.map f).hom ≫ e.inv + (U.map g).hom ≫ e.inv
        rw [Preadditive.add_comp]
      map_smul' := fun r f ↦ by
        rw [U.map_smul]
        exact CategoryTheory.Linear.smul_comp _ _ _ r (U.map f).hom e.inv }

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
