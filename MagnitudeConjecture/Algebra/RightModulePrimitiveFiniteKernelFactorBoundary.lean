import MagnitudeConjecture.Algebra.RightModulePrimitiveFiniteKernelDualBoundary

/-! # Multiplicity one on both primitive factor boundaries -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable (S : FiniteIndecomposableSkeleton k A)

/-- Finite kernels and duality give multiplicity one on the projective
boundary of the literal primitive factor. -/
theorem factorProjective_primitiveMultiplicity_eq_one_finiteKernel
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (p : S.FactorProjectiveLabel (S.primitiveKilledLabels D)) :
    S.primitiveMultiplicity D p.1.1 = 1 := by
  have hpos := PrimitiveMultiplicityInput.multiplicity_pos
    (S := S) (S.primitiveMultiplicityInput D) p.1
  change 0 < S.primitiveMultiplicity D p.1.1 at hpos
  rcases PrimitiveMultiplicityInput.factorProjective_ambient_projective_or_translation_killed
    (S := S) (S.primitiveMultiplicityInput D) p.1 p.2 with hp | ⟨hnp, hk⟩
  · letI := hp
    have hle := S.primitiveMultiplicity_projective_le_one_finiteKernel H D p.1.1
    omega
  · have hle := S.primitiveMultiplicity_le_one_of_rightTranslation_killed_finiteKernel
      H D ⟨p.1.1, hnp⟩ hk
    change S.primitiveMultiplicity D p.1.1 ≤ 1 at hle
    omega

/-- Finite kernels give multiplicity one on the injective boundary of the
literal primitive factor. -/
theorem factorInjective_primitiveMultiplicity_eq_one_finiteKernel
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (p : S.FactorInjectiveLabel (S.primitiveKilledLabels D)) :
    S.primitiveMultiplicity D p.1.1 = 1 := by
  have hpos := PrimitiveMultiplicityInput.multiplicity_pos
    (S := S) (S.primitiveMultiplicityInput D) p.1
  change 0 < S.primitiveMultiplicity D p.1.1 at hpos
  rcases PrimitiveMultiplicityInput.factorInjective_ambient_injective_or_inverse_translation_killed
    (S := S) (S.primitiveMultiplicityInput D) p.1 p.2 with hp | ⟨hni, hk⟩
  · letI := hp
    have hle := S.primitiveMultiplicity_injective_le_one_finiteKernel H D p.1.1
    omega
  · let x : {i : Fin S.n // ¬ Injective (S.fgObj i)} := ⟨p.1.1, hni⟩
    let z := S.rightTranslationEquiv.symm x
    have ht : S.rightTranslationLabel z = p.1.1 :=
      congrArg Subtype.val (S.rightTranslationEquiv.apply_symm_apply x)
    have hle := S.primitiveMultiplicity_rightTranslation_le_one_of_killed_finiteKernel
      H D z hk
    rw [ht] at hle
    omega

/-- The complete boundary input is supplied by finite kernels, independently
of the stronger translation-difference coordinate estimate. -/
theorem primitiveDirectedBoundaryData_finiteKernel
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e) :
    S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D) where
  acyclic := H
  projective_multiplicity_eq_one := S.factorProjective_primitiveMultiplicity_eq_one_finiteKernel H D
  injective_multiplicity_eq_one := S.factorInjective_primitiveMultiplicity_eq_one_finiteKernel H D

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
