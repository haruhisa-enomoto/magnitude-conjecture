import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalYoneda

/-!
# Universal Hom comparison: restricted Yoneda
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

local instance standardFormUniversalHomEquivRestrictedQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalHomEquivRestrictedArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- Downstairs restricted Yoneda is a linear equivalence on the selected Hom
space. -/
noncomputable def standardFormRestrictedYonedaDownstairsHomLinearEquiv
    (p : Fin S.n) (X Y : SourceCategory S p) :
    ((meshProjection S p).obj X ⟶ (meshProjection S p).obj Y) ≃ₗ[k]
      ((S.standardFormRestrictedYonedaFunctor
            S.standardFormMeshHomFinite).obj
          ((meshProjection S p).obj X) ⟶
        (S.standardFormRestrictedYonedaFunctor
            S.standardFormMeshHomFinite).obj
          ((meshProjection S p).obj Y)) := by
  let R := S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite
  letI : R.Linear k := by
    dsimp only [R, standardFormRestrictedYonedaFunctor]
    infer_instance
  letI : R.Faithful := S.standardFormRestrictedYonedaFunctor_faithful
  letI : R.Full := by
    dsimp only [R]
    infer_instance
  exact LinearEquiv.ofBijective
    (R.mapLinearMap k
      (X := (meshProjection S p).obj X)
      (Y := (meshProjection S p).obj Y))
    ⟨R.map_injective, R.map_surjective⟩

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
