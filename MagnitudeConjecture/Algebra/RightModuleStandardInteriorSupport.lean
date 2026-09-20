import MagnitudeConjecture.Algebra.RightModuleStandardIntervalControlHeight
import MagnitudeConjecture.Algebra.RightModuleStandardGradedIncomingBounds

/-! # Incoming indecomposables at interior targets remain supported -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance interiorSupportQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance interiorSupportArrowFintype (x y : Fin S.n) :
    Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- Every shifted representative mapping nontrivially to an interior target
has its whole support in the finite interval. -/
theorem standardFormGraded_interior_source_supported
    (m : ℕ) (i j : Fin S.n) (s t : ℤ)
    (ht0 : 0 ≤ t) (htm : t ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight)
    (f : (⟨S.standardFormGradedFamily i, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedFamily j, t⟩) (hf : f ≠ 0) :
    Graded.FiniteGradedModule.SupportedIn m
      (⟨S.standardFormGradedFamily i, s⟩ : Graded.FiniteGradedModule.ShiftedModule) := by
  have hs := S.standardFormGraded_incoming_shift_bounds S.standardFormIntervalControlHeight
    S.standardFormIntervalControlHeight_hom_bound
    (MeshCategory.obj (k := k) S.standardFormRightMeshData i)
    (MeshCategory.obj (k := k) S.standardFormRightMeshData j) s t f hf
  apply (S.standardFormGraded_supported_iff i s m).mpr
  exact GradedInterval.incoming_shift_allowed m S.standardFormIntervalControlHeight
    (S.standardFormSupportWindow i).lower (S.standardFormSupportWindow i).upper
    (S.standardFormSupportWindow_upper_le_control i) s t ht0 htm hs.1 hs.2

/-- The interior support statement applies to every graded indecomposable,
not just the chosen representatives. -/
theorem standardFormGraded_interior_indecomposable_supported
    (m : ℕ) (j : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (htm : t ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight)
    (M : Graded.FiniteGradedModule.ShiftedModule
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite))
    (hM : Indecomposable M)
    (f : M ⟶ ⟨S.standardFormGradedFamily j, t⟩) (hf : f ≠ 0) :
    Graded.FiniteGradedModule.SupportedIn m M := by
  obtain ⟨i, s, ⟨E⟩⟩ := S.standardFormGraded_shifted_exists_iso M hM
  have hg : E.inv ≫ f ≠ 0 := by
    intro hz
    apply hf
    have h := congrArg (fun g ↦ E.hom ≫ g) hz
    simpa using h
  exact (Graded.FiniteGradedModule.supportedIn_iff_of_iso E).mpr
    (S.standardFormGraded_interior_source_supported m i j s t ht0 htm (E.inv ≫ f) hg)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
