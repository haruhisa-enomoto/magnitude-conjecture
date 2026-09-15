import MagnitudeConjecture.CategoryTheory.F1FiniteDeletionSupport
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplus

/-!
# Finite-support monotonicity for the frozen deletion route

The finite object-support quotient in Section 9.2 is a finite directed
category.  This file records the exact consequence used by the averaging step:
the sum of the local changes on any finite selected set is nonnegative when
all complementary local changes vanish.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion.Frozen

open MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]

theorem finite_selected_localChange_nonnegative
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hskel : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (x : C)
    (S : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := C))
    (T : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C)))
    (W : Fin S.n → Prop) [DecidablePred W]
    (houtside : ∀ i : Fin S.n, ¬ W i →
      localChange (k := k) C hlocal ({x} : Set C)
        (S.obj i) (S.indecomposable i) = 0) :
    0 ≤ ∑ i : {i : Fin S.n // W i},
      localChange (k := k) C hlocal ({x} : Set C)
        (S.obj i.1) (S.indecomposable i.1) := by
  letI : EnoughProjectives
    (FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP ({x} : Set C) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  have hmono :=
    finiteCategoryProjectiveGenerator.singletonDeletion_surplus_le
      hP hlocalRing hskel hlocal H x S T
  have hsum : 0 ≤ ∑ i : Fin S.n,
      localChange (k := k) C hlocal ({x} : Set C)
        (S.obj i) (S.indecomposable i) := by
    rw [FiniteDeletionSkeleton.sum_localChange_eq_surplus_sub
      (k := k) ({x} : Set C) S T hlocal]
    exact sub_nonneg.mpr hmono
  let f : Fin S.n → ℤ := fun i ↦
    localChange (k := k) C hlocal ({x} : Set C)
      (S.obj i) (S.indecomposable i)
  have hzero : ∑ i : {i : Fin S.n // ¬ W i}, f i.1 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact houtside i.1 i.2
  have hpartition := Fintype.sum_subtype_add_sum_subtype W f
  calc
    0 ≤ ∑ i : Fin S.n, f i := hsum
    _ = (∑ i : {i : Fin S.n // W i}, f i.1) +
        ∑ i : {i : Fin S.n // ¬ W i}, f i.1 := hpartition.symm
    _ = ∑ i : {i : Fin S.n // W i}, f i.1 := by rw [hzero, add_zero]


/-- The total local-change certificate for a finite directed deletion. -/
theorem finite_localChange_sum_nonnegative
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hskel : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (x : C)
    (S : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := C))
    (T : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))) :
    0 ≤ ∑ i : Fin S.n,
      localChange (k := k) C hlocal ({x} : Set C)
        (S.obj i) (S.indecomposable i) := by
  letI : DecidablePred (fun _ : Fin S.n ↦ True) := Classical.decPred _
  let f : Fin S.n → ℤ := fun i ↦
    localChange (k := k) C hlocal ({x} : Set C)
      (S.obj i) (S.indecomposable i)
  have h := finite_selected_localChange_nonnegative
    (k := k) hP hlocal hlocalRing hskel H x S T
      (fun _ ↦ True) (by
        intro i hi
        exact False.elim (hi trivial))
  have hsum : (∑ i : Fin S.n, f i) =
      ∑ i : {i : Fin S.n // True}, f i.1 := by
    symm
    simpa using (Finset.sum_subtype (p := fun _ : Fin S.n => True)
      (Finset.univ : Finset (Fin S.n)) (fun _ => by simp) f).symm
  change 0 ≤ ∑ i : Fin S.n, f i
  rw [hsum]
  exact h

end MagnitudeConjecture.ObjectDeletion.Frozen
