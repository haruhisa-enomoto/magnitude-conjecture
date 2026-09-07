import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalShiftZeroSurjective

/-!
# Degree-zero surjectivity of universal restricted Yoneda

Surjectivity on shift-orbit Hom spaces is restricted to the degree-zero
component before the categorical fullness structure is assembled.
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

local instance standardFormUniversalUnderlyingSurjectiveQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalUnderlyingSurjectiveArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

set_option maxHeartbeats 800000 in
/-- The ordinary Hom map is surjective, obtained by lifting a target morphism
as a degree-zero shift-orbit morphism and reading the degree-zero component of
an orbit preimage. -/
theorem standardFormUniversalRestrictedYonedaUnderlyingHomLinearMap_surjective
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :
    Function.Surjective
      (standardFormUniversalRestrictedYonedaUnderlyingHomLinearMap S p X Y) := by
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
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  let U := standardFormUniversalRestrictedYonedaFunctor S p
  intro XtoY
  let ESource := CoveringHom.shiftHomZeroLinearEquiv
    (k := k) (A := Additive G) X Y
  let map₀ := standardFormUniversalRestrictedYonedaUnderlyingHomLinearMap
    S p X Y
  let sY : Y ≅ (DAmbient.core.F (0 : Additive G)).obj Y :=
    (shiftFunctorZero (SourceCategory S p) (Additive G)).symm.app Y
  let eFinite := standardFormUniversalRestrictedYonedaShiftIso S p 0 Y
  let e : (U.obj Y).obj⟦(0 : Additive G)⟧ ≅
      (U.obj ((DAmbient.core.F 0).obj Y)).obj :=
    (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) (U.obj Y) 0).symm ≪≫
      (CoveringHom.IsFiniteDimensionalModule
        (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k).ι.mapIso eFinite
  let t : (U.obj Y).obj ≅ (U.obj Y).obj⟦(0 : Additive G)⟧ :=
    (CoveringHom.IsFiniteDimensionalModule
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k).ι.mapIso
        (U.mapIso sY) ≪≫ e.symm
  obtain ⟨q₀, hq₀⟩ :=
    standardFormUniversalRestrictedYonedaShiftHomZeroLinearMap_surjective
      S p hconnected X Y (XtoY ≫ t.hom)
  let f₀ := ESource.symm q₀
  have hzero : (CoveringHom.shiftHomZeroLinearEquiv
      (k := k) (A := Additive G) X Y) f₀ = f₀ ≫ sY.hom := by
    simp [CoveringHom.shiftHomZeroLinearEquiv,
      CategoryTheory.ShiftedHom.homEquiv,
      CategoryTheory.ShiftedHom.mk₀, sY, shiftFunctorZero']
    rfl
  have hmap : (U.map f₀).hom ≫ (U.map sY.hom).hom =
      (U.map (f₀ ≫ sY.hom)).hom := by
    change (U.map f₀ ≫ U.map sY.hom).hom =
      (U.map (f₀ ≫ sY.hom)).hom
    exact congrArg (fun q => q.hom) (U.map_comp f₀ sY.hom).symm
  refine ⟨f₀, ?_⟩
  apply (cancel_mono t.hom).1
  calc
    map₀ f₀ ≫ t.hom =
        (standardFormUniversalRestrictedYonedaShiftHomLinearMap
          S p X Y 0) (ESource f₀) := by
      simp [map₀, t, sY, e,
        standardFormUniversalRestrictedYonedaShiftHomLinearMap,
        standardFormUniversalRestrictedYonedaShiftHomNonzeroLinearMap,
        standardFormUniversalRestrictedYonedaUnderlyingHomLinearMap,
        ESource]
      rw [hzero]
      change ((U.map f₀).hom ≫ (U.map sY.hom).hom) ≫
          eFinite.inv.hom ≫
            (D.finiteDimensionalModuleShiftUnderlyingIso
              (k := k) (U.obj Y) 0).hom =
        (U.map (f₀ ≫ sY.hom)).hom ≫ eFinite.inv.hom ≫
          (D.finiteDimensionalModuleShiftUnderlyingIso
            (k := k) (U.obj Y) 0).hom
      exact congrArg
        (fun q => q ≫ eFinite.inv.hom ≫
          (D.finiteDimensionalModuleShiftUnderlyingIso
            (k := k) (U.obj Y) 0).hom)
        hmap
    _ = (standardFormUniversalRestrictedYonedaShiftHomLinearMap
          S p X Y 0) q₀ := by
      rw [ESource.apply_symm_apply]
    _ = XtoY ≫ t.hom := hq₀

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
