import MagnitudeConjecture.Algebra.RightModuleStandardFormLiftedOrbitRepresentables
import MagnitudeConjecture.CategoryTheory.StandardCoveringCategoryAlgebraDefs

/-! # Existence of the standard-form orbit-algebra universe change -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormLiftedOrbitChangeUniverseNonemptyQuiver :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormLiftedOrbitChangeUniverseNonemptyArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev LiftedProjectiveGroup (x₀ : Fin S.n) :=
  ULift.{u} (ProjectiveGroup S x₀)

set_option backward.isDefEq.respectTransparency false in
/-- There is an algebra equivalence between the orbit algebras formed before
and after universe lifting the deck group. -/
theorem standardFormOppositeProjectiveLiftedOrbitChangeUniverseNonempty
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
        standardFormOppositeProjectiveDeckOrbitAlgebra
          S x₀ hconnected hfinite) := by
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
  letI : Fintype (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := Fintype.ofFinite _
  let e := D₀.uliftDeckOrbitSkeletonEquivalence (k := k)
  letI : e.functor.Additive := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Additive
    infer_instance
  letI : e.functor.Linear k := by
    change (D₀.uliftDeckOrbitSkeletonFunctor (k := k)).Linear k
    infer_instance
  let hLift :=
    standardFormOppositeProjectiveLiftedDeckOrbitFiniteRightRepresentables
      S x₀ hconnected hfinite
  let hSmall :=
    standardFormOppositeProjectiveDeckOrbitFiniteRightRepresentables
      S x₀ hconnected hfinite
  let hObj := D₀.uliftDeckOrbitSkeletonFunctor_obj_bijective (k := k)
  exact ⟨CoveringHom.finiteCategoryAlgebraEquiv
    (hC := hLift) (hD := hSmall) (e := e) hObj⟩

end UniversalCover
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
