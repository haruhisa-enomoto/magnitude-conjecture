import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivRestricted

/-!
# Universal Hom comparison: indexed deck-orbit change of base
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

local instance standardFormUniversalHomEquivChangeOfBaseQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalHomEquivChangeOfBaseArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The indexed deck-orbit equivalence induces a linear equivalence on the
selected Hom space. -/
noncomputable def standardFormIndexedDeckOrbitHomLinearEquiv
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :
    let R := S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite
    let EF := standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
      S p hconnected
    (R.obj ((meshProjection S p).obj X) ⟶
        R.obj ((meshProjection S p).obj Y)) ≃ₗ[k]
      (EF.functor.obj (R.obj ((meshProjection S p).obj X)) ⟶
        EF.functor.obj (R.obj ((meshProjection S p).obj Y))) := by
  let R := S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite
  let EF := standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
    S p hconnected
  letI : EF.functor.Additive := by
    dsimp only [EF,
      standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence]
    infer_instance
  letI : EF.functor.Linear k := by
    dsimp only [EF,
      standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence]
    infer_instance
  letI : EF.functor.Faithful := by infer_instance
  letI : EF.functor.Full := by infer_instance
  exact LinearEquiv.ofBijective
    (EF.functor.mapLinearMap k
      (X := R.obj ((meshProjection S p).obj X))
      (Y := R.obj ((meshProjection S p).obj Y)))
    ⟨EF.functor.map_injective, EF.functor.map_surjective⟩

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
