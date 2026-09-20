import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeleton
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalDirected
import MagnitudeConjecture.Algebra.RightModuleDirected

/-! # Representation-directedness of the actual finite interval algebra -/
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

local instance standardIntervalSkeletonDirectedFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) := S.standardFormIntervalAlgebra_finiteDimensional m
local instance standardIntervalSkeletonDirectedNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- The actual finite right-module skeleton of every standard-form interval is directed. -/
theorem standardFormIntervalSkeleton_acyclic (m : ℕ) :
    (S.standardFormIntervalSkeleton m).HasAcyclicNonzeroNonisomorphisms := by
  let K := S.standardFormIntervalSkeleton m
  let rank (i : Fin K.n) : ℤ := ((Fintype.equivFin (S.standardFormSupportedLabel m)).symm i).2.val
  have step {i j : Fin K.n} (h : K.NonzeroNonisomorphism i j) : rank j < rank i := by
    obtain ⟨f, hf, hi⟩ := h
    change S.standardFormIntervalFamily m ((Fintype.equivFin (S.standardFormSupportedLabel m)).symm i) ⟶
      S.standardFormIntervalFamily m ((Fintype.equivFin (S.standardFormSupportedLabel m)).symm j) at f
    exact S.standardFormIntervalFamily_noniso_descent _ _ f hf hi
  intro i h
  have descent {i j : Fin K.n} (h : Relation.TransGen K.NonzeroNonisomorphism i j) :
      rank j < rank i := by
    induction h with
    | single h => exact step h
    | tail h he ih => exact lt_trans (step he) ih
  exact (lt_irrefl (rank i)) (descent h)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
