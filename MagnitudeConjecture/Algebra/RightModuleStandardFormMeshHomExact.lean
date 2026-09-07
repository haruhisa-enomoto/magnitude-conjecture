import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateAssembly

/-! # Hom exactness for the standard-form mesh-simple resolution -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomExactQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomExactArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- Applying `Hom(-, k(Γ)(-,x))` to the first two maps of the standard
nonprojective simple resolution is exact at the incoming coefficient term. -/
theorem standardFormSimpleResolution_hom_exact
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (hh : S.standardFormRightMeshData.translationMapFinite (k := k) hP z ≫ h = 0) :
    ∃ b : S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x,
      S.standardFormRightMeshData.incomingMapFinite (k := k) hP z.1 ≫ b = h := by
  obtain ⟨b, hcoordinate⟩ :=
    S.standardFormSimpleResolution_hom_coordinate_factor hP z x h hh
  exact ⟨b, S.standardFormSimpleResolution_hom_eq_of_coordinates
    hP z x h b hcoordinate⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
