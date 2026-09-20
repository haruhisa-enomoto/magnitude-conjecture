import MagnitudeConjecture.CategoryTheory.FiniteCategorySurplusInvariant

/-! # Surplus under finite object deletion -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.ObjectDeletion
open MagnitudeConjecture.CoveringHom
universe u v
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Fintype C]
variable (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))
variable (hrep : IsLocallyRepresentationFinite (k := k) (C := C))

/-- Surplus of the literal finite module category after object deletion. -/
def finiteDeletionSurplus (S : Set C) : ℤ :=
  finiteCategorySurplus
    (deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S)
    (isLocallyRepresentationFinite_deletion (k := k) C S hrep)

/-- Empty deletion preserves the intrinsic surplus. -/
theorem finiteDeletionSurplus_empty :
    finiteDeletionSurplus hP hrep ∅ = finiteCategorySurplus hP hrep := by
  let E := emptyDeletionEquivalence (k := k) C
  letI : E.functor.Additive := inferInstanceAs ((emptyDeletionFunctor (k := k) C).Additive)
  letI : E.functor.Linear k := inferInstanceAs ((emptyDeletionFunctor (k := k) C).Linear k)
  exact (finiteCategorySurplus_eq_of_equivalence hP _ hrep _ E).symm

/-- Successive deletion has the surplus of deletion by the union. -/
theorem finiteDeletionSurplus_iterated (S T : Set C) :
    finiteDeletionSurplus
      (deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S)
      (isLocallyRepresentationFinite_deletion (k := k) C S hrep)
      (AdditionalDeleted (k := k) C S T) = finiteDeletionSurplus hP hrep (S ∪ T) :=
  finiteCategorySurplus_eq_of_equivalence _ _ _ _
    (iteratedDeletionEquivalence (k := k) C S T)

variable [IsAlgClosed k]

/-- Directed singleton deletion cannot increase intrinsic surplus. -/
theorem finiteDeletionSurplus_singleton_le
    (hlocal : ∀ X : C, IsLocalRing (End X)) (hskel : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C)) (x : C) :
    finiteDeletionSurplus hP hrep {x} ≤ finiteCategorySurplus hP hrep :=
  finiteCategoryProjectiveGenerator.singletonDeletion_surplus_le_of_fintype
    hP hlocal hskel hrep H x (finiteCategoryModuleIndecomposableSkeleton hrep)
    (finiteCategoryModuleIndecomposableSkeleton
      (isLocallyRepresentationFinite_deletion (k := k) C {x} hrep))

/-- Deleting any set of objects from a finite directed category cannot
increase the module-category surplus. -/
theorem finiteDeletionSurplus_le
    (hlocal : ∀ X : C, IsLocalRing (End X)) (hskel : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C)) (S : Set C) :
    finiteDeletionSurplus hP hrep S ≤ finiteCategorySurplus hP hrep := by
  classical
  revert hP hrep hlocal hskel H S
  induction hn : Fintype.card C using Nat.strong_induction_on generalizing C with
  | h n ih =>
    intro hP hrep hlocal hskel H S
    by_cases hz : S = ∅
    · subst S
      exact le_of_eq (finiteDeletionSurplus_empty hP hrep)
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hz
      let D := DeletionCategory (k := k) C ({x} : Set C)
      let hPD := deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP ({x} : Set C)
      let hrepD := isLocallyRepresentationFinite_deletion (k := k) C ({x} : Set C) hrep
      have hlocalD := deletion_end_isLocalRing (k := k) C hskel hlocal ({x} : Set C)
      have hskelD := deletion_skeletal (k := k) C hskel hlocal ({x} : Set C)
      have HD := hasAcyclicFiniteModuleNonzeroNonisomorphisms_deletion
        (k := k) (C := C) ({x} : Set C) H
      have hlt : Fintype.card D < n := by
        rw [← hn]
        exact deletion_card_lt (k := k) C ({x} : Set C) (Set.mem_singleton x)
      have hstep := ih (Fintype.card D) hlt (C := D) rfl
        hPD hrepD hlocalD hskelD HD (AdditionalDeleted (k := k) C {x} S)
      have hunion : ({x} : Set C) ∪ S = S := Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hx)
      rw [finiteDeletionSurplus_iterated hP hrep, hunion] at hstep
      exact hstep.trans (finiteDeletionSurplus_singleton_le hP hrep hlocal hskel H x)

end MagnitudeConjecture.ObjectDeletion
