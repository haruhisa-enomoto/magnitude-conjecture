import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivChangeOfBase

/-!
# Universal Hom comparison: objectwise downstairs isomorphisms
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

local instance standardFormUniversalHomEquivDownstairsQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalHomEquivDownstairsArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The objectwise downstairs isomorphisms induce the next linear Hom
equivalence. -/
noncomputable def standardFormOrbitSkeletonPushdownHomLinearEquiv
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :
    let D := standardFormOppositeProjectiveDeckShift S p
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let R := S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite
    let EF := standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
      S p hconnected
    (EF.functor.obj (R.obj ((meshProjection S p).obj X)) ⟶
        EF.functor.obj (R.obj ((meshProjection S p).obj Y))) ≃ₗ[k]
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
          ((standardFormUniversalRestrictedYonedaFunctor S p).obj X) ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
          ((standardFormUniversalRestrictedYonedaFunctor S p).obj Y)) := by
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let eX := standardFormUniversalRestrictedYonedaPushdownDownstairsIso
    S p hconnected X
  let eY := standardFormUniversalRestrictedYonedaPushdownDownstairsIso
    S p hconnected Y
  exact (CategoryTheory.Linear.homCongr k eX eY).symm

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
