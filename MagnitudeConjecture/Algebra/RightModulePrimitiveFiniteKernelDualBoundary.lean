import MagnitudeConjecture.Algebra.RightModulePrimitiveFiniteKernelBoundary
import MagnitudeConjecture.Algebra.RightModulePrimitiveContragredientBoundary

/-! # Dual primitive-coordinate bounds from finite kernels -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable (S : FiniteIndecomposableSkeleton k A)

/-- The dual finite-kernel argument bounds every indecomposable projective. -/
theorem primitiveMultiplicity_projective_le_one_finiteKernel
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (z : Fin S.n) [Projective (S.fgObj z)] :
    S.primitiveMultiplicity D z ≤ 1 := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let Sop := S.contragredientSkeleton
  letI : Injective (Sop.fgObj z) :=
    (S.contragredientAlignedBiduality.backward.injective_iff_projective_image
      S.contragredientAlmostSplitSkeleton S.almostSplitSkeleton z).2 (by
        change Projective (S.fgObj z)
        infer_instance)
  have h := Sop.primitiveMultiplicity_injective_le_one_finiteKernel
    (S.contragredientSkeleton_hasAcyclicNonzeroNonisomorphisms H) D.opposite z
  rwa [S.contragredient_primitiveMultiplicity_eq D z] at h

/-- If the first term of an almost-split sequence is killed, the last term
has primitive-coordinate dimension at most one. -/
theorem primitiveMultiplicity_le_one_of_rightTranslation_killed_finiteKernel
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hz : S.rightTranslationLabel z ∈ S.primitiveKilledLabels D) :
    S.primitiveMultiplicity D z.1 ≤ 1 := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let Sop := S.contragredientSkeleton
  let x := S.rightTranslationEquiv z
  let q := S.contragredientNonprojectiveLabel x
  have hq : q.1 = S.rightTranslationLabel z := rfl
  have hk : q.1 ∈ Sop.primitiveKilledLabels D.opposite := by
    apply (Sop.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D.opposite q.1).2
    rw [S.contragredient_primitiveMultiplicity_eq D q.1, hq]
    exact (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D _).1 hz
  have ht : Sop.rightTranslationLabel q = z.1 := by
    exact (S.contragredient_rightTranslationLabel_eq_inverse x).trans
      (congrArg Subtype.val (S.rightTranslationEquiv.symm_apply_apply z))
  have h := Sop.primitiveMultiplicity_rightTranslation_le_one_of_killed_finiteKernel
    (S.contragredientSkeleton_hasAcyclicNonzeroNonisomorphisms H) D.opposite q hk
  rw [ht, S.contragredient_primitiveMultiplicity_eq D z.1] at h
  exact h

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
