import MagnitudeConjecture.Algebra.RightModuleStandardGradedSupport
import MagnitudeConjecture.Algebra.RightModuleStandardGradedDecomposition
import MagnitudeConjecture.CategoryTheory.GradedModuleSupport
import MagnitudeConjecture.Combinatorics.FiniteSupportWindow

/-! # Exactly which standard-form indecomposables are supported in an interval -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance intervalShiftsQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance intervalShiftsArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

theorem standardFormGradedFamily_support_nonempty (i : Fin S.n) :
    (S.standardFormGradedFamily i).grading.toVectorGrading.support.Nonempty := by
  have hn : ¬ Subsingleton (S.standardFormGradedFamily i).module :=
    (not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp
      (S.standardFormGradedFamily_indecomposable i).1
  letI : Nontrivial (S.standardFormGradedFamily i).module := not_subsingleton_iff_nontrivial.mp hn
  exact (S.standardFormGradedFamily i).grading.toVectorGrading.support_nonempty

/-- Exact least and greatest nonzero degrees of each standard-form representative. -/
def standardFormSupportWindow (i : Fin S.n) :
    GradedInterval.SupportWindow (S.standardFormGradedFamily i).grading.toVectorGrading.support :=
  GradedInterval.SupportWindow.ofNonnegative _ (S.standardFormGradedFamily_support_nonempty i)
    (fun d hd ↦ by
      obtain ⟨h, hh, hb⟩ := S.standardFormGraded_support_bound
      exact (hb (MeshCategory.obj (k := k) S.standardFormRightMeshData i) d hd).1)

/-- A common positive upper bound for every representative's support. -/
def standardFormSupportHeight : ℕ := S.standardFormGraded_support_bound.choose

theorem standardFormSupportWindow_upper_le (i : Fin S.n) :
    (S.standardFormSupportWindow i).upper ≤ S.standardFormSupportHeight := by
  have h := (S.standardFormGraded_support_bound.choose_spec.2
    (MeshCategory.obj (k := k) S.standardFormRightMeshData i)
      (S.standardFormSupportWindow i).upper (S.standardFormSupportWindow i).upper_mem).2
  exact_mod_cast h

/-- A shifted representative lies in [0,m] exactly at the explicitly counted shifts. -/
theorem standardFormGraded_supported_iff (i : Fin S.n) (s : ℤ) (m : ℕ) :
    Graded.FiniteGradedModule.SupportedIn m
      (⟨S.standardFormGradedFamily i, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ↔
    s ∈ GradedInterval.allowedShifts m (S.standardFormSupportWindow i).lower
      (S.standardFormSupportWindow i).upper := by
  rw [← (S.standardFormSupportWindow i).shift_supported_iff]
  constructor
  · intro h d hd
    exact h (d + s) (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
  · intro h d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    exact h j hj

/-- Every indecomposable supported graded module occurs at one of the allowed shifts. -/
theorem standardFormGraded_supported_classification (m : ℕ)
    (M : Graded.FiniteGradedModule.ShiftedModule
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite))
    (hM : Indecomposable M) (hs : Graded.FiniteGradedModule.SupportedIn m M) :
    ∃ i : Fin S.n, ∃ s ∈ GradedInterval.allowedShifts m
      (S.standardFormSupportWindow i).lower (S.standardFormSupportWindow i).upper,
      Nonempty (M ≅ ⟨S.standardFormGradedFamily i, s⟩) := by
  obtain ⟨i, s, ⟨e⟩⟩ := S.standardFormGraded_shifted_exists_iso M hM
  exact ⟨i, s, (S.standardFormGraded_supported_iff i s m).mp
    ((Graded.FiniteGradedModule.supportedIn_iff_of_iso e).mp hs), ⟨e⟩⟩

/-- The exact number of allowed labelled representatives has constant width correction. -/
theorem standardFormGraded_supported_label_count (m : ℕ) (hm : S.standardFormSupportHeight ≤ m) :
    ∑ i : Fin S.n, ((GradedInterval.allowedShifts m (S.standardFormSupportWindow i).lower
      (S.standardFormSupportWindow i).upper).card : ℤ) =
      (S.n : ℤ) * ((m : ℤ) + 1) -
        ∑ i : Fin S.n, (((S.standardFormSupportWindow i).upper : ℤ) - (S.standardFormSupportWindow i).lower) := by
  simpa using GradedInterval.sum_card_allowedShifts (Finset.univ : Finset (Fin S.n))
    (fun i ↦ (S.standardFormSupportWindow i).lower)
    (fun i ↦ (S.standardFormSupportWindow i).upper) m
    (fun i _ ↦ (S.standardFormSupportWindow_upper_le i).trans hm)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
