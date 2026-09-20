import MagnitudeConjecture.Algebra.RightModuleStandardIntervalClassification
import MagnitudeConjecture.Algebra.RightModuleStandardSupportedDirected
import MagnitudeConjecture.CategoryTheory.RankedFamilyEquivalence

/-! # Directedness of the actual standard-form interval modules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

attribute [local irreducible] standardFormIntervalAlgebraEquivalence

/-- A nonzero nonisomorphism between actual interval modules strictly lowers the shift label. -/
theorem standardFormIntervalFamily_noniso_descent {m : ℕ} (a b : S.standardFormSupportedLabel m)
    (f : S.standardFormIntervalFamily m a ⟶ S.standardFormIntervalFamily m b)
    (hf : f ≠ 0) (hi : ¬ IsIso f) : b.2.val < a.2.val :=
  MagnitudeConjecture.CategoryTheory.ranked_family_of_equivalence
    (S.standardFormIntervalAlgebraEquivalence m) (S.standardFormSupportedFamily m)
    (fun a ↦ a.2.val) (fun a b f hf hi ↦ S.standardFormSupported_noniso_descent a b f hf hi)
    a b f hf hi

/-- Nonzero nonisomorphisms between the selected actual interval modules. -/
def standardFormIntervalEdge (m : ℕ) (a b : S.standardFormSupportedLabel m) : Prop :=
  ∃ f : S.standardFormIntervalFamily m a ⟶ S.standardFormIntervalFamily m b, f ≠ 0 ∧ ¬ IsIso f

/-- The complete indecomposable family of the interval algebra is directed. -/
theorem standardFormIntervalFamily_acyclic (m : ℕ) (a : S.standardFormSupportedLabel m) :
    ¬ Relation.TransGen (S.standardFormIntervalEdge m) a a := by
  have descent {b c} (h : Relation.TransGen (S.standardFormIntervalEdge m) b c) :
      c.2.val < b.2.val := by
    induction h with
    | single h =>
      obtain ⟨f, hf, hi⟩ := h
      exact S.standardFormIntervalFamily_noniso_descent _ _ f hf hi
    | tail h he ih =>
      obtain ⟨f, hf, hi⟩ := he
      exact lt_trans (S.standardFormIntervalFamily_noniso_descent _ _ f hf hi) ih
  intro h
  exact (lt_irrefl a.2.val) (descent h)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
