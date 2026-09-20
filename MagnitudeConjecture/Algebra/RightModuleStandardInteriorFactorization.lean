import MagnitudeConjecture.Algebra.RightModuleStandardInteriorSupport
import MagnitudeConjecture.CategoryTheory.IncomingDecompositionSum

/-! # Interior factorizations reduce to supported indecomposable intermediates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A factorization to an interior target is a finite sum through supported
indecomposables. The component maps are obtained by composing the original
factors with the displayed summand projections and inclusions. -/
theorem standardFormInterior_factorization_decomposition
    (m : ℕ) (j : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (htm : t ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight)
    {X M : Graded.FiniteGradedModule.ShiftedModule
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)}
    (a : X ⟶ M) (b : M ⟶ ⟨S.standardFormGradedFamily j, t⟩) :
    ∃ d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition M,
      (∀ q : d.IncomingIndex b,
        Graded.FiniteGradedModule.SupportedIn m (d.summand q.val)) ∧
      (letI : Fintype (d.IncomingIndex b) := Fintype.ofFinite _;
        a ≫ b = ∑ q : d.IncomingIndex b,
          d.outgoingComponent a q.val ≫ d.incomingComponent b q.val) :=
  MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.exists_factorization_decomposition
    (Graded.FiniteGradedModule.SupportedIn m)
    (fun Z hZ f hf ↦ S.standardFormGraded_interior_indecomposable_supported
      m j t ht0 htm Z hZ f hf)
    (Graded.FiniteGradedModule.finiteDecomposition M) a b

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
