import MagnitudeConjecture.CategoryTheory.GradedModuleBiproducts
import MagnitudeConjecture.CategoryTheory.GradedModuleIdempotents
import MagnitudeConjecture.CategoryTheory.GradedModuleFiniteHom
import MagnitudeConjecture.CategoryTheory.IndecomposableFiniteEnd
import MagnitudeConjecture.CategoryTheory.GradedHomogeneousSplitting

/-! # Locality and homogeneous splitting for graded indecomposable modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v w
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- Graded indecomposability gives local graded endomorphisms without requiring
indecomposability of the underlying ungraded module. -/
theorem localEnd_of_indecomposable (X : ShiftedModule.{u,v} (R := R))
    (hX : Indecomposable X) : IsLocalRing (End X) := by
  let l : End X →ₗ[k] (X ⟶ X) :=
    { toFun := End.asHom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  letI : FiniteDimensional k (End X) := Module.Finite.of_injective l
    (fun _ _ h ↦ End.ext h)
  exact MagnitudeConjecture.CategoryTheory.end_isLocalRing_of_finiteDimensional_indecomposable
    (k := k) X hX

/-- Given a finite ungraded decomposition into modules with local endomorphisms,
a graded indecomposable is isomorphic to a shift of one of those modules. -/
theorem exists_iso_shift_of_decomposition {ι : Type w} (s : Finset ι)
    (X : FiniteGradedModule.{u,v} R) (Y : ι → FiniteGradedModule.{u,v} R)
    (f : ∀ j, X ⟶ Y j) (g : ∀ j, Y j ⟶ X)
    (hsum : ∑ j ∈ s, f j ≫ g j = 𝟙 X)
    (hX : Indecomposable (⟨X, 0⟩ : ShiftedModule (R := R)))
    (hY : ∀ j ∈ s, IsLocalRing (End (Y j))) :
    ∃ j ∈ s, ∃ d : ℤ,
      Nonempty ((⟨X, 0⟩ : ShiftedModule (R := R)) ≅ ⟨Y j, -d⟩) :=
  homGrading.exists_iso_shift_of_identity_of_local_targets s X Y f g hsum
    (localEnd_of_indecomposable _ hX) hY

end MagnitudeConjecture.Graded.FiniteGradedModule
