import MagnitudeConjecture.Algebra.RightModuleStandardFormLiftedOrbitChangeUniverseNonempty

/-! # The universe-lifted standard-form orbit algebra -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormLiftedOrbitAlgebraEquivQuiverInstance : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormLiftedOrbitAlgebraEquivArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

/-- The universe-lifted orbit-category algebra used by the covering-average
interface is isomorphic to the manuscript's literal standard-form algebra. -/
theorem standardFormOppositeProjectiveLiftedOrbitCategoryAlgebraEquivNonempty
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hfinite : S.StandardFormMeshHomFinite) :
    let hP :=
      (standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
        ).finiteCovariantRepresentables
    let D₀ := standardFormOppositeProjectiveDeckShift S x₀
    let D := D₀.ulift.{0, u, 0, u}
    letI := D₀.hasShift
    letI := D₀.additiveShift
    letI := D₀.linearShift (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI : Finite (MulAction.orbitRel.Quotient (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
      standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
    Nonempty
      (StandardCovering.orbitCategoryAlgebra (k := k) D hP ≃ₐ[k]
        S.standardFormAlgebra hfinite) := by
  obtain ⟨f⟩ :=
    standardFormOppositeProjectiveLiftedOrbitChangeUniverseNonempty
      S x₀ hconnected hfinite
  exact ⟨f.trans
    (standardFormOppositeProjectiveOrbitCategoryAlgebraEquiv
      S x₀ hconnected hfinite)⟩

end UniversalCover
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
