import MagnitudeConjecture.Algebra.RightModuleStandardIntervalShifts
import MagnitudeConjecture.CategoryTheory.GradedSupportedCategory

/-! # The intrinsic finite classification of supported standard-form graded modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Labels and exactly the shifts whose support stays in the interval. -/
abbrev standardFormSupportedLabel (m : ℕ) :=
  (i : Fin S.n) × ↥(GradedInterval.allowedShifts m (S.standardFormSupportWindow i).lower
    (S.standardFormSupportWindow i).upper)

abbrev standardFormSupportedCategory (m : ℕ) :=
  Graded.FiniteGradedModule.SupportedCategory
    (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite) m

/-- The supported representative attached to an allowed label. -/
def standardFormSupportedFamily (m : ℕ) (a : S.standardFormSupportedLabel m) :
    S.standardFormSupportedCategory m :=
  ⟨⟨S.standardFormGradedFamily a.1, a.2.val⟩,
    (S.standardFormGraded_supported_iff a.1 a.2.val m).mpr a.2.property⟩

theorem standardFormSupportedFamily_indecomposable (m : ℕ) (a : S.standardFormSupportedLabel m) :
    Indecomposable (S.standardFormSupportedFamily m a) :=
  (Graded.FiniteGradedModule.supported_indecomposable_iff _).mpr
    (S.standardFormGraded_shift_indecomposable a.1 a.2.val)

/-- Every indecomposable in the supported category occurs in the finite family. -/
theorem standardFormSupportedFamily_complete (m : ℕ) (X : S.standardFormSupportedCategory m)
    (hX : Indecomposable X) :
    ∃ a : S.standardFormSupportedLabel m, Nonempty (X ≅ S.standardFormSupportedFamily m a) := by
  obtain ⟨i, s, hs, ⟨e⟩⟩ := S.standardFormGraded_supported_classification m X.obj
    ((Graded.FiniteGradedModule.supported_indecomposable_iff X).mp hX) X.property
  exact ⟨⟨i, ⟨s, hs⟩⟩, ⟨(Graded.FiniteGradedModule.intervalSupport _).ι.preimageIso e⟩⟩

/-- Distinct supported labels represent distinct isomorphism classes. -/
theorem standardFormSupportedFamily_skeletal (m : ℕ) (a b : S.standardFormSupportedLabel m)
    (e : S.standardFormSupportedFamily m a ≅ S.standardFormSupportedFamily m b) : a = b := by
  have h := S.standardFormGraded_label_shift_unique
    ((Graded.FiniteGradedModule.intervalSupport _).ι.mapIso e)
  rcases a with ⟨i, s, hs⟩
  rcases b with ⟨j, t, ht⟩
  obtain ⟨hij, hst⟩ := h
  dsimp at hij hst
  subst j
  subst t
  rfl

/-- The cardinality is the exact number of supported graded indecomposable classes. -/
theorem standardFormSupportedLabel_card (m : ℕ) (hm : S.standardFormSupportHeight ≤ m) :
    (Fintype.card (S.standardFormSupportedLabel m) : ℤ) =
      (S.n : ℤ) * ((m : ℤ) + 1) -
        ∑ i : Fin S.n, (((S.standardFormSupportWindow i).upper : ℤ) -
          (S.standardFormSupportWindow i).lower) := by
  simpa only [Fintype.card_sigma, Fintype.card_coe, Nat.cast_sum] using
    S.standardFormGraded_supported_label_count m hm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
