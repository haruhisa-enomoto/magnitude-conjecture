import MagnitudeConjecture.Algebra.RightModuleStandardFormLiftedOrbitFinite

/-! # Representables on the universe-lifted standard-form orbit -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormLiftedOrbitRepresentablesQuiverInstance : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormLiftedOrbitRepresentablesArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

/-- Finite-dimensional covariant representables on the lifted strict orbit
category, transported from the small strict orbit category. -/
theorem standardFormOppositeProjectiveLiftedDeckOrbitFiniteRightRepresentables
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hfinite : S.StandardFormMeshHomFinite) :
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
    ∀ X : CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (LiftedProjectiveGroup S x₀),
      CoveringHom.IsFiniteDimensionalModule
        (C := CoveringHom.DeckOrbitSkeleton
          (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
          (LiftedProjectiveGroup S x₀)) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
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
  letI : Finite (MulAction.orbitRel.Quotient (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveLiftedDeckOrbitFinite S x₀ hconnected
  letI : Finite (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := by
    change Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    infer_instance
  letI : Finite (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (LiftedProjectiveGroup S x₀)) := by
    change Finite (MulAction.orbitRel.Quotient (LiftedProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    infer_instance
  letI : Fintype (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (LiftedProjectiveGroup S x₀)) := Fintype.ofFinite _
  let e := D₀.uliftDeckOrbitSkeletonEquivalence (k := k)
  letI : e.functor.Additive := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Additive
    infer_instance
  letI : e.functor.Linear k := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Linear k
    infer_instance
  exact CoveringHom.linearCoyonedaFiniteOfFullyFaithful
    (k := k) e.functor
    (standardFormOppositeProjectiveDeckOrbitFiniteRightRepresentables
      S x₀ hconnected hfinite)

end UniversalCover
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
