import MagnitudeConjecture.Algebra.RightModuleStandardFormOrbitAlgebra
import MagnitudeConjecture.Algebra.RightModuleStandardFormCoverLocallyBounded
import MagnitudeConjecture.CategoryTheory.DeckShiftUniverseLiftSkeleton

/-! # Finiteness of the universe-lifted standard-form orbit -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormLiftedOrbitFiniteQuiverInstance : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormLiftedOrbitFiniteArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

/-- The strict orbit quotient remains finite after universe lifting the deck
group. -/
theorem standardFormOppositeProjectiveLiftedDeckOrbitFinite
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D₀ := standardFormOppositeProjectiveDeckShift S x₀
    let D := D₀.ulift.{0, u, 0, u}
    letI := D₀.hasShift
    letI := D₀.additiveShift
    letI := D₀.linearShift (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Finite (MulAction.orbitRel.Quotient (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) := by
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveDeckOrbitFinite S x₀ hconnected
  letI : Finite (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := by
    change Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    infer_instance
  exact Finite.of_injective
    (D₀.uliftDeckOrbitSkeletonEquivalence (k := k)).functor.obj
    (D₀.uliftDeckOrbitSkeletonFunctor_obj_bijective (k := k)).1

end UniversalCover
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
