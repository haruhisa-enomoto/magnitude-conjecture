import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivTotal
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomFiniteDimensional
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMaps
import MagnitudeConjecture.LinearAlgebra.FiniteDimensionalSurjective

/-! # The universal orbit-Hom bijectivity criterion -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalBijectiveCriterionQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalBijectiveCriterionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

set_option backward.isDefEq.respectTransparency false in
/-- Since the source and target orbit-Hom spaces are linearly equivalent and
the source is finite-dimensional, injectivity of the universal Hom map implies
surjectivity. -/
noncomputable def standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap_surjective_of_injective
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :
    LinearMap.SurjectiveOfInjective
      (standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap S p X Y) := by
  let f := standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap S p X Y
  let e := standardFormUniversalHomLinearEquivTotal S p hconnected X Y
  letI := standardFormUniversalShiftOrbitHomFiniteDimensional S p X Y
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  letI : HasShift (SourceCategory S p)
      (Additive (StandardFormProjectiveGroup S p)) := DAmbient.hasShift
  letI : FiniteDimensional k
      (Π₀ i : Additive (StandardFormProjectiveGroup S p),
        CoveringHom.ShiftHom X Y i) :=
    standardFormUniversalShiftOrbitHomFiniteDimensional S p X Y
  refine ⟨?_⟩
  intro hf
  let g := e.symm.toLinearMap.comp f
  have hg : Function.Injective g := e.symm.injective.comp hf
  have hg_surjective : Function.Surjective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hg
  intro y
  obtain ⟨x, hx⟩ := hg_surjective (e.symm y)
  exact ⟨x, e.symm.injective hx⟩

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
