import MagnitudeConjecture.Algebra.RightModuleStandardSupportedIrreducibleBounds
import MagnitudeConjecture.CategoryTheory.IrreducibleIncomingSum

/-! # Uniform total incoming irreducible dimension in supported intervals -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped BigOperators
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Total incoming irreducible dimension is bounded independently of the
interval length, including all boundary targets. -/
theorem standardFormSupported_uniform_indegree_bound :
    ∃ B : ℕ, ∀ m : ℕ, ∀ b : S.standardFormSupportedLabel m,
      (∑ a : S.standardFormSupportedLabel m,
        Module.finrank k (CategoricalIrreducible.Space k
          (S.standardFormSupportedFamily m a) (S.standardFormSupportedFamily m b))) ≤ B :=
  S.standardFormSupported_uniform_irreducible_bounds.elim fun h hh ↦
    hh.elim fun D hD ↦ ⟨S.n * (h + 1) * D, fun m b ↦
      (CategoricalIrreducible.sum_finrank_le_incoming_card_mul k
        (S.standardFormSupportedFamily m) (S.standardFormSupportedFamily m b) D
        (fun a ↦ (hD.2 m).2 a b)).trans
          (Nat.mul_le_mul_right D ((hD.2 m).1 b))⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
