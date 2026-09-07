import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleRightTau

/-!
# Right tau-data on the finite orbit module category

The constructed downstream indecomposable skeleton, finite representables,
and intrinsic finite radical evaluation assemble an actual finite right-tau
category under the manuscript's covering hypotheses.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.Iyama

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The finite deck-orbit module category carries literal finite right-tau
data under the manuscript's covering hypotheses. -/
noncomputable def finiteOrbitModuleRightTauCategoryData
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    FiniteRightTauCategoryData
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k)
      (Fin (D.finiteOrbitModuleIndecomposableSkeleton
        (k := k) hP hI hlocal hfree hrep).n) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let S := D.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep
  exact S.toFiniteRightTauCategoryData

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
