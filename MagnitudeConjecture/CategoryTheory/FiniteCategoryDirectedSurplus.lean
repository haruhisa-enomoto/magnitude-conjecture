import MagnitudeConjecture.CategoryTheory.FiniteDeletionSurplus
import MagnitudeConjecture.Algebra.RightModuleDirectedSurplus

/-! # Directed finite category surplus and zero-surplus thinness -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
universe v
variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type} [Category.{v} C] [Preadditive C] [Linear k C] [Fintype C]
variable (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))
variable (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
variable (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C))

include H

/-- Directed primitive induction gives nonnegative intrinsic surplus. -/
theorem finiteCategorySurplus_nonnegative : 0 ≤ finiteCategorySurplus hP hrep := by
  let A := finiteCategoryProjectiveGenerator.algebra hP
  let : FiniteDimensional k A := finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  let : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let hA := finiteCategoryProjectiveGenerator.algebra_isRepresentationFinite hP hrep
  let S := Classical.choice (RightModule.FiniteIndecomposableSkeleton.exists_of_isRepresentationFinite hA)
  let T := finiteCategoryModuleIndecomposableSkeleton hrep
  rw [finiteCategorySurplus_eq_skeleton hP hrep T,
    finiteCategoryProjectiveGenerator.categorySkeleton_surplus_eq_ambientARSurplus hP T S]
  exact S.ambientARSurplus_nonnegative_of_directed
    (finiteCategoryProjectiveGenerator.algebraSkeleton_hasAcyclicNonzeroNonisomorphisms hP H S)

/-- Every finite deletion of a directed category has nonnegative surplus. -/
theorem finiteDeletionSurplus_nonnegative (S : Set C) :
    0 ≤ ObjectDeletion.finiteDeletionSurplus hP hrep S :=
  finiteCategorySurplus_nonnegative _ _
    (ObjectDeletion.hasAcyclicFiniteModuleNonzeroNonisomorphisms_deletion (k := k) (C := C) S H)

variable (hlocal : ∀ X : C, IsLocalRing (End X)) (hskel : Skeletal C)

include hlocal hskel

/-- At zero surplus, all finite object deletions also have zero surplus. -/
theorem finiteDeletionSurplus_eq_zero (hz : finiteCategorySurplus hP hrep = 0) (S : Set C) :
    ObjectDeletion.finiteDeletionSurplus hP hrep S = 0 :=
  le_antisymm ((ObjectDeletion.finiteDeletionSurplus_le hP hrep hlocal hskel H S).trans_eq hz)
    (finiteDeletionSurplus_nonnegative hP hrep H S)

/-- Zero surplus forces each nonzero fiber of an indecomposable to be a line. -/
theorem finrank_obj_eq_one_of_finiteCategorySurplus_eq_zero
    (hz : finiteCategorySurplus hP hrep = 0)
    (M : FiniteDimensionalModuleCategory.{0, v, v, v} (C := C) k)
    (hM : Indecomposable M) (x : C) (hx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  have heq : ObjectDeletion.finiteDeletionSurplus hP hrep {x} = finiteCategorySurplus hP hrep :=
    (finiteDeletionSurplus_eq_zero hP hrep H hlocal hskel hz {x}).trans hz.symm
  exact finiteCategoryProjectiveGenerator.finrank_obj_eq_one_of_singletonDeletion_surplus_eq_of_fintype
    hP hlocal hskel hrep H x (finiteCategoryModuleIndecomposableSkeleton hrep)
    (finiteCategoryModuleIndecomposableSkeleton
      (ObjectDeletion.isLocallyRepresentationFinite_deletion (k := k) C {x} hrep)) heq M hM hx

/-- Every indecomposable in a directed zero-surplus category is pointwise thin. -/
theorem finrank_obj_le_one_of_finiteCategorySurplus_eq_zero
    (hz : finiteCategorySurplus hP hrep = 0)
    (M : FiniteDimensionalModuleCategory.{0, v, v, v} (C := C) k)
    (hM : Indecomposable M) (x : C) : Module.finrank k (M.obj.obj.obj x) ≤ 1 := by
  by_cases hx : IsZero (M.obj.obj.obj x)
  · let : Subsingleton (M.obj.obj.obj x) := ModuleCat.isZero_iff_subsingleton.mp hx
    rw [Module.finrank_zero_of_subsingleton]
    omega
  · exact le_of_eq (finrank_obj_eq_one_of_finiteCategorySurplus_eq_zero hP hrep H hlocal hskel hz M hM x hx)

end MagnitudeConjecture.CoveringHom
