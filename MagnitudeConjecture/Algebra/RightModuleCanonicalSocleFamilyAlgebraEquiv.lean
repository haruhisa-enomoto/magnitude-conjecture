import MagnitudeConjecture.Algebra.RightModuleSocleFamilyAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModuleSocleReductionString

/-!
# Canonical socle families under algebra equivalence

The family of nonuniserial indecomposable projective-injective right
modules is intrinsic.  Combining this observation with transport of the
embedded socle-family ideal gives an algebra equivalence between the two
literal canonical socle quotients.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A B : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]
  [IsNoetherianRing Bᵐᵒᵖ]

namespace PrimitiveProjectivePresentation

variable {S : RightModule.FiniteIndecomposableSkeleton k A}

/-- Transporting projective labels carries the canonical nonuniserial
projective-injective family exactly onto the canonical target family. -/
theorem mapAlgEquivProjectiveLabels_nonuniserialProjectiveInjectiveLabels
    (f : A ≃ₐ[k] B) :
    mapAlgEquivProjectiveLabels S f
        S.nonuniserialProjectiveInjectiveLabels =
      (S.mapAlgEquiv f).nonuniserialProjectiveInjectiveLabels := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_map.1 hq
    subst q
    rw [(S.mapAlgEquiv f).mem_nonuniserialProjectiveInjectiveLabels_iff]
    have hpData :=
      (S.mem_nonuniserialProjectiveInjectiveLabels_iff p).1 hp
    constructor
    · exact (mapAlgEquivProjectiveLabel_injective_iff f p).2 hpData.1
    · intro huni
      exact hpData.2
        ((mapAlgEquivProjectiveLabel_isUniserial_iff f p).1 huni)
  · intro hq
    let p := (S.mapAlgEquivProjectiveLabelEquiv f).symm q
    have hqp : S.mapAlgEquivProjectiveLabelEquiv f p = q :=
      (S.mapAlgEquivProjectiveLabelEquiv f).apply_symm_apply q
    have hqData :=
      ((S.mapAlgEquiv f).mem_nonuniserialProjectiveInjectiveLabels_iff q).1 hq
    rw [← hqp] at hqData
    apply Finset.mem_map.2
    refine ⟨p, ?_, hqp⟩
    rw [S.mem_nonuniserialProjectiveInjectiveLabels_iff]
    constructor
    · apply (mapAlgEquivProjectiveLabel_injective_iff f p).1
      exact hqData.1
    · intro huni
      have htransport :=
        (mapAlgEquivProjectiveLabel_isUniserial_iff f p).2 huni
      exact hqData.2 htransport

/-- The literal canonical simultaneous-socle quotient is invariant under
algebra equivalence. -/
def canonicalSocleFamilyQuotientAlgEquiv
    (P : S.PrimitiveProjectivePresentation) (f : A ≃ₐ[k] B) :
    RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonuniserialProjectiveInjectiveLabels
          S.nonuniserialProjectiveInjectiveLabels_injective) ≃ₐ[k]
      RightModule.idealQuotientAlgebra
        ((P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal
          (S.mapAlgEquiv f).nonuniserialProjectiveInjectiveLabels
          (S.mapAlgEquiv f
            ).nonuniserialProjectiveInjectiveLabels_injective) := by
  let T' := mapAlgEquivProjectiveLabels S f
    S.nonuniserialProjectiveInjectiveLabels
  let hInjective' := mapAlgEquivProjectiveLabels_injective S f
    S.nonuniserialProjectiveInjectiveLabels
    S.nonuniserialProjectiveInjectiveLabels_injective
  let J' := (P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal
    T' hInjective'
  let Jcanonical :=
    (P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal
      (S.mapAlgEquiv f).nonuniserialProjectiveInjectiveLabels
      (S.mapAlgEquiv f).nonuniserialProjectiveInjectiveLabels_injective
  have hT : T' =
      (S.mapAlgEquiv f).nonuniserialProjectiveInjectiveLabels :=
    mapAlgEquivProjectiveLabels_nonuniserialProjectiveInjectiveLabels f
  have hJ : J' = Jcanonical := by
    exact (P.mapAlgEquiv f).primitiveProjectiveSocleFamilyIdeal_congr
      hT hInjective'
        (S.mapAlgEquiv f).nonuniserialProjectiveInjectiveLabels_injective
  let e := P.primitiveProjectiveSocleFamilyQuotientAlgEquiv f
    S.nonuniserialProjectiveInjectiveLabels
    S.nonuniserialProjectiveInjectiveLabels_injective
  change RightModule.idealQuotientAlgebra
      (P.primitiveProjectiveSocleFamilyIdeal
        S.nonuniserialProjectiveInjectiveLabels
        S.nonuniserialProjectiveInjectiveLabels_injective) ≃ₐ[k]
    RightModule.idealQuotientAlgebra Jcanonical
  change RightModule.idealQuotientAlgebra
      (P.primitiveProjectiveSocleFamilyIdeal
        S.nonuniserialProjectiveInjectiveLabels
        S.nonuniserialProjectiveInjectiveLabels_injective) ≃ₐ[k]
    RightModule.idealQuotientAlgebra J' at e
  rw [hJ] at e
  exact e

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
