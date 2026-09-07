import MagnitudeConjecture.Algebra.RightModuleStandardFormCoverFiniteConvex
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalFull
import MagnitudeConjecture.CategoryTheory.AdmissibleModuleCategory

/-!
# Directedness of the concrete standard-form universal cover

The integer length on the universal mesh category makes its finite-support
module category directed using the full, faithful, and dense restricted-Yoneda
realization.  This terminal wrapper also assembles the admissibility package.
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

local instance standardFormUniversalDirectedFinalQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalDirectedFinalArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The category of finite-support modules on the opposite lifted-projective
category is directed. -/
theorem
    standardFormOppositeProjectiveSourceCategoryHasAcyclicFiniteModuleNonzeroNonisomorphisms
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p) :
    CoveringHom.HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) := by
  let U := standardFormUniversalRestrictedYonedaFunctor S p
  letI : U.Faithful :=
    standardFormUniversalRestrictedYonedaFunctor_faithful S p
  letI : U.Full :=
    standardFormUniversalRestrictedYonedaFunctor_full S p hconnected
  apply
    CoveringHom.hasAcyclicFiniteModuleNonzeroNonisomorphisms_of_ranked_realization
      U (standardFormUniversalObjectDegree S p)
  · intro X Y hXY
    exact standardFormUniversalObjectDegree_strict S p hXY
  · intro M hM
    exact exists_standardFormUniversalRestrictedYoneda_iso
      S p hconnected M hM

/-- The opposite lifted-projective category satisfies the complete
admissibility package used in the frozen manuscript. -/
theorem standardFormOppositeProjectiveSourceCategoryIsAdmissible
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p) :
    CoveringHom.IsAdmissible
      (k := k) (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) where
  locallyBounded :=
    standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S p
  locallyRepresentationFinite :=
    standardFormOppositeProjectiveSourceCategoryIsLocallyRepresentationFinite
      S p hconnected
  directed :=
    standardFormOppositeProjectiveSourceCategoryHasAcyclicFiniteModuleNonzeroNonisomorphisms
      S p hconnected
  finiteConvexNeighborhoods :=
    standardFormOppositeProjectiveSourceCategoryHasFiniteConvexObjectNeighborhoods
      S p

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
