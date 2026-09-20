import MagnitudeConjecture.Algebra.RightModuleDirectedFiniteKernel
import MagnitudeConjecture.Algebra.RightModulePrimitiveIdempotent

/-! # Primitive-coordinate boundary bounds from finite kernels -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable (S : FiniteIndecomposableSkeleton k A)

/-- If the last term of an almost-split sequence is killed by e, its first
term has primitive-coordinate dimension at most one. -/
theorem primitiveMultiplicity_rightTranslation_le_one_of_killed_finiteKernel
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hz : z.1 ∈ S.primitiveKilledLabels D) :
    S.primitiveMultiplicity D (S.rightTranslationLabel z) ≤ 1 := by
  letI := S.primitiveSink_injective D
  rw [S.primitiveMultiplicity_eq_sinkHom D]
  apply S.finrank_rightTranslation_hom_injective_le_one H z
  have hzero := (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D z.1).1 hz
  rw [S.primitiveMultiplicity_eq_sinkHom D] at hzero
  exact (finrank_zero_iff_forall_zero).1 hzero

/-- Every indecomposable injective has primitive-coordinate dimension at
most one, by the finite-kernel argument. -/
theorem primitiveMultiplicity_injective_le_one_finiteKernel
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (z : Fin S.n) [Injective (S.fgObj z)] :
    S.primitiveMultiplicity D z ≤ 1 := by
  letI := S.primitiveSink_injective D
  rw [S.primitiveMultiplicity_eq_sinkHom D]
  exact S.finrank_injective_hom_injective_le_one H z (S.primitiveSinkLabel D)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
