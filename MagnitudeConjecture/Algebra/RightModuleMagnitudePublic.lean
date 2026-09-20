import MagnitudeConjecture.Algebra.RightModuleIntervalProof
import MagnitudeConjecture.Algebra.RightModuleSimpleCount

/-!
# The magnitude theorem with a direct simple-module count

The original endpoint computes the simple count using indecomposable
projectives. This public interface exposes module-theoretic simplicity
directly and uses the proved simple-top bijection to connect the two counts.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule

universe u
variable {k A : Type u} [Field k] [IsAlgClosed k]
  [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- The number of simple right-module isomorphism classes, counted by testing
module-theoretic simplicity on the complete indecomposable family. -/
def simpleModuleCount (hA : IsRepresentationFinite k A) : ℕ := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
  exact (representationFiniteSkeleton hA).simpleCount

omit [IsAlgClosed k] in
/-- The direct simple count agrees with the original projective-count interface. -/
theorem simpleModuleCount_eq_numberOfSimpleModules
    (hA : IsRepresentationFinite k A) :
    (simpleModuleCount hA : ℤ) = numberOfSimpleModules hA := by
  let : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
  exact (representationFiniteSkeleton hA).simpleCount_eq_projectiveCount

/-- The magnitude inequality and equality characterization with the simple
count defined directly through simple right modules. -/
theorem magnitudeConjecture_simpleCount (hA : IsRepresentationFinite k A) :
    (simpleModuleCount hA : ℚ) ≤ moduleCategoryMagnitude hA ∧
      (moduleCategoryMagnitude hA = (simpleModuleCount hA : ℚ) ↔
        BoundQuiver.IsSpecialBiserial k A) := by
  have hcount : (simpleModuleCount hA : ℚ) = (numberOfSimpleModules hA : ℚ) := by
    exact_mod_cast simpleModuleCount_eq_numberOfSimpleModules hA
  rw [hcount]
  exact magnitudeConjecture hA

namespace FiniteIndecomposableSkeleton

variable [IsNoetherianRing Aᵐᵒᵖ]

/-- The same theorem on any complete finite indecomposable family. -/
theorem magnitudeConjecture_simpleCount
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    (S.simpleCount : ℚ) ≤
        FiniteTauMatrix.categoryMagnitude (k := k) S.finiteTauCategoryData ∧
      (FiniteTauMatrix.categoryMagnitude (k := k) S.finiteTauCategoryData =
          (S.simpleCount : ℚ) ↔ BoundQuiver.IsSpecialBiserial k A) := by
  have hcount : (S.simpleCount : ℚ) =
      (@ARCount.projectiveCount (Fin S.n) inferInstance
        (fun i ↦ Projective (S.fgObj i)) (Classical.decPred _) : ℚ) := by
    exact_mod_cast S.simpleCount_eq_projectiveCount
  rw [hcount]
  exact S.magnitudeConjecture_of_finiteIndecomposableSkeleton

end FiniteIndecomposableSkeleton
end MagnitudeConjecture.RightModule
