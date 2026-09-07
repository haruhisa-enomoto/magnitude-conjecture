import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalUnderlyingSurjective

/-!
# Fullness of universal restricted Yoneda

Surjectivity of the shift-orbit Hom map is converted to ordinary fullness by
extracting the degree-zero component.
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

local instance standardFormUniversalFullQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalFullArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The universal restricted Yoneda realization is full. -/
theorem standardFormUniversalRestrictedYonedaFunctor_full
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p) :
    (standardFormUniversalRestrictedYonedaFunctor S p).Full where
  map_surjective := by
    intro X Y h
    obtain ⟨f, hf⟩ :=
      standardFormUniversalRestrictedYonedaUnderlyingHomLinearMap_surjective
        S p hconnected X Y h.hom
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    exact hf

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
