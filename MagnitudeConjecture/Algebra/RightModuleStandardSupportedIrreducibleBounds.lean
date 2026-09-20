import MagnitudeConjecture.Algebra.RightModuleStandardSupportedUniformIncoming
import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace

/-! # Uniform irreducible-space bounds, including interval boundaries -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Interval irreducible dimensions are bounded by their actual Hom
dimensions even when restriction creates new irreducible maps. -/
theorem standardFormSupported_irreducible_finrank_le_hom
    {m : ℕ} (a b : S.standardFormSupportedLabel m) :
    Module.finrank k (CategoricalIrreducible.Space k
      (S.standardFormSupportedFamily m a) (S.standardFormSupportedFamily m b)) ≤
    Module.finrank k (S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b) := by
  letI : FiniteDimensional k
      (S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b) :=
    Module.Finite.equiv (S.standardFormSupportedHomEquiv a b).symm
  exact CategoricalIrreducible.finrank_le_hom k _ _

/-- The incoming-source and irreducible-dimension bounds use constants
independent of the interval length and the target's distance from its ends. -/
theorem standardFormSupported_uniform_irreducible_bounds :
    ∃ h D : ℕ, 1 ≤ h ∧ ∀ m : ℕ,
      (∀ b : S.standardFormSupportedLabel m,
        Nat.card (S.standardFormSupportedIncomingLabel b) ≤ S.n * (h + 1)) ∧
      (∀ a b : S.standardFormSupportedLabel m,
        Module.finrank k (CategoricalIrreducible.Space k
          (S.standardFormSupportedFamily m a) (S.standardFormSupportedFamily m b)) ≤ D) :=
  S.standardFormSupported_uniform_incoming_bounds.elim fun h hh ↦
    hh.elim fun D hD ↦ ⟨h, D, hD.1, fun m ↦ ⟨(hD.2 m).1, fun a b ↦
      (S.standardFormSupported_irreducible_finrank_le_hom a b).trans ((hD.2 m).2 a b)⟩⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
