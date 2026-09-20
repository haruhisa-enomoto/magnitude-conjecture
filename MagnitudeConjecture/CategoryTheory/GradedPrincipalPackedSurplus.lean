import MagnitudeConjecture.CategoryTheory.GradedPrincipalRetainedBlockEquivalence
import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalSimpleCount

/-! # Surplus counts for the actual separated principal intervals -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

local instance packedSurplusIntervalFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m) :=
  inferInstanceAs (Fintype (ι × Fin (m + 1)))
local instance packedSurplusIntervalOpFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

include he in
/-- Representables on the literal retained category are finite dimensional. -/
theorem principalRetainedFiniteRepresentables (r h q : ℕ) :
    ∀ X : PrincipalRetainedCategory R hmul e he0 r h q,
      CoveringHom.IsFiniteDimensionalModule (C := PrincipalRetainedCategory R hmul e he0 r h q) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  let F := (ObjectDeletion.IsSurviving
    (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ
    (principalIntervalSeparatedDeleted R hmul e he0 h (GradedInterval.packingEnd r h q) r q)).ι
  exact CoveringHom.linearCoyonedaFiniteOfFullyFaithful F
    (principalIntervalFiniteRepresentables R hmul e he0 he (GradedInterval.packingEnd r h q))

/-- The literal retained category has q times the small interval's surplus. -/
theorem principalRetained_surplus_eq_q_mul_interval
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ)
    (hrep : CoveringHom.IsLocallyRepresentationFinite (k := k)
      (C := PrincipalRetainedCategory R hmul e he0 r h q))
    (hsmall : CoveringHom.IsLocallyRepresentationFinite (k := k)
      (C := (PrincipalIntervalCategory R hmul e he0 r)ᵒᵖ)) :
    CoveringHom.finiteCategorySurplus (principalRetainedFiniteRepresentables R hmul e he0 he r h q) hrep =
      (q : ℤ) * CoveringHom.finiteCategorySurplus
        (principalIntervalFiniteRepresentables R hmul e he0 he r) hsmall := by
  simpa only [Fintype.card_fin] using
    CoveringHom.finiteCategorySurplus_eq_card_mul_of_blockEquivalences
      (principalRetainedBlock R hmul e he0 r h q)
      (principalRetained_hom_eq_zero_of_block_ne R hmul e he0 he hneg h hupper r q)
      (principalRetainedFiniteRepresentables R hmul e he0 he r h q) hrep
      (principalIntervalFiniteRepresentables R hmul e he0 he r) hsmall
      (principalRetainedBlockDeletionEquivalence R hmul e he0 he hneg h hupper r q)

/-- The literal gap-deletion category has q times the small interval's surplus. -/
theorem principalPackedDeletion_surplus_eq_q_mul_interval
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ)
    (hambient : CoveringHom.IsLocallyRepresentationFinite (k := k)
      (C := (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ))
    (hsmall : CoveringHom.IsLocallyRepresentationFinite (k := k)
      (C := (PrincipalIntervalCategory R hmul e he0 r)ᵒᵖ)) :
    ObjectDeletion.finiteDeletionSurplus
      (principalIntervalFiniteRepresentables R hmul e he0 he (GradedInterval.packingEnd r h q))
      hambient (principalIntervalSeparatedDeleted R hmul e he0 h (GradedInterval.packingEnd r h q) r q) =
        (q : ℤ) * CoveringHom.finiteCategorySurplus
          (principalIntervalFiniteRepresentables R hmul e he0 he r) hsmall := by
  let C := (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ
  let D := principalIntervalSeparatedDeleted R hmul e he0 h (GradedInterval.packingEnd r h q) r q
  letI : Fintype (ObjectDeletion.SurvivingCategory C D) := principalRetainedFintype R hmul e he0 r h q
  let hP := principalIntervalFiniteRepresentables R hmul e he0 he (GradedInterval.packingEnd r h q)
  let hPD := ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP D
  let hrepD := ObjectDeletion.isLocallyRepresentationFinite_deletion (k := k) C D hambient
  let E := ObjectDeletion.survivingDeletionEquivalence (k := k) C D
    (principalIntervalSeparated_noDeletedFactorization R hmul e he0 he hneg h hupper
      (GradedInterval.packingEnd r h q) r q)
  let T := CoveringHom.finiteCategoryModuleIndecomposableSkeleton hrepD
  let EM := CoveringHom.finiteDimensionalModuleCongrEquivalenceOfFinite (k := k) E
  let hrep := (T.mapEquivalence EM).isLocallyRepresentationFinite
  have heq := CoveringHom.finiteCategorySurplus_eq_of_equivalence
    (principalRetainedFiniteRepresentables R hmul e he0 he r h q) hPD hrep hrepD E
  exact heq.symm.trans
    (principalRetained_surplus_eq_q_mul_interval R hmul e he0 he hneg h hupper r q hrep hsmall)

/-- Finite directed deletion gives the actual separated-interval packing inequality. -/
theorem principalInterval_surplus_packing [IsAlgClosed k]
    (hdiag : ∀ i, Module.finrank k (cornerComponent R (e i) (e i) 0) = 1)
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (hoff : ∀ i j, i ≠ j → cornerComponent R (e i) (e j) 0 = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ)
    (hambient : CoveringHom.IsLocallyRepresentationFinite (k := k)
      (C := (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ))
    (hsmall : CoveringHom.IsLocallyRepresentationFinite (k := k)
      (C := (PrincipalIntervalCategory R hmul e he0 r)ᵒᵖ))
    (H : CoveringHom.HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k)
      (C := (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ)) :
    (q : ℤ) * CoveringHom.finiteCategorySurplus
        (principalIntervalFiniteRepresentables R hmul e he0 he r) hsmall ≤
      CoveringHom.finiteCategorySurplus
        (principalIntervalFiniteRepresentables R hmul e he0 he (GradedInterval.packingEnd r h q)) hambient := by
  rw [← principalPackedDeletion_surplus_eq_q_mul_interval R hmul e he0 he hneg h hupper r q hambient hsmall]
  exact ObjectDeletion.finiteDeletionSurplus_le _ hambient
    (principalIntervalOp_end_isLocalRing R hmul e he0 he hdiag _)
    (principalIntervalOp_skeletal R hmul e he0 he hdiag hneg hoff _) H _

end MagnitudeConjecture.Graded.FiniteGradedModule
