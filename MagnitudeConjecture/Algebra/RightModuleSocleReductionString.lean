import MagnitudeConjecture.Algebra.BiserialModule
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleFamily
import MagnitudeConjecture.Algebra.RightModuleSocleFamilyBeta
import MagnitudeConjecture.Algebra.RightModuleStringSurplus

/-!
# Socle reduction to a string algebra

This file isolates the axiom-free numerical consequence of the structural
socle-reduction theorem.  It selects all nonuniserial indecomposable
projective-injective right modules, rejects their socles simultaneously, and
uses a supplied string presentation of the quotient to force vanishing of the
ambient Auslander--Reiten surplus.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

/-- The canonical finite family of indecomposable projective-injective right
modules which are not uniserial. -/
def nonuniserialProjectiveInjectiveLabels
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    Finset S.ProjectiveLabel := by
  classical
  exact Finset.univ.filter fun p ↦
    Injective (S.fgObj p.label) ∧
      ¬ IsUniserialModule Aᵐᵒᵖ (S.fgObj p.label)

@[simp]
theorem mem_nonuniserialProjectiveInjectiveLabels_iff
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (p : S.ProjectiveLabel) :
    p ∈ S.nonuniserialProjectiveInjectiveLabels ↔
      Injective (S.fgObj p.label) ∧
        ¬ IsUniserialModule Aᵐᵒᵖ (S.fgObj p.label) := by
  classical
  simp [nonuniserialProjectiveInjectiveLabels]

/-- Every member of the canonical family is injective. -/
theorem nonuniserialProjectiveInjectiveLabels_injective
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (p : S.ProjectiveLabel)
    (hp : p ∈ S.nonuniserialProjectiveInjectiveLabels) :
    Injective (S.fgObj p.label) :=
  (S.mem_nonuniserialProjectiveInjectiveLabels_iff p).1 hp |>.1

/-- Every member of the canonical family is non-simple. -/
theorem nonuniserialProjectiveInjectiveLabels_notSimple
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (p : S.ProjectiveLabel)
    (hp : p ∈ S.nonuniserialProjectiveInjectiveLabels) :
    ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label) := by
  intro hsimple
  exact (S.mem_nonuniserialProjectiveInjectiveLabels_iff p).1 hp |>.2
    (IsBiserialModule.uniserial_of_simple hsimple)

namespace PrimitiveProjectivePresentation

variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable (P : S.PrimitiveProjectivePresentation)

include P in
/-- Simultaneous socle rejection preserves the categorical ambient
Auslander--Reiten surplus. -/
theorem primitiveProjectiveSocleFamily_ambientARSurplus_eq
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ] :
    S.ambientARSurplus =
      (S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
          ).ambientARSurplus := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let Q := S.idealQuotientFiniteIndecomposableSkeleton J
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TQ := Q.finiteTauCategoryData.toFiniteRightTauCategoryData
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra J)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
  have hsurplus :=
    (P.primitiveProjectiveSocleFamilyRejectionProfile
      T hInjective hNotSimple).surplus_eq
  have hAmbientProjective :
      TA.IsProjective = fun i ↦ Projective (S.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj TA i
  have hQuotientProjective :
      TQ.IsProjective = fun i ↦ Projective (Q.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj TQ i
  unfold ambientARSurplus
  exact ((congrArg (fun projective : Fin S.n → Prop ↦
      @ARCount.surplus (Fin S.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity TA)
        projective (Classical.decPred projective)) hAmbientProjective).symm).trans <|
    hsurplus.trans <|
      congrArg (fun projective : Fin Q.n → Prop ↦
        @ARCount.surplus (Fin Q.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity TQ)
          projective (Classical.decPred projective)) hQuotientProjective

include P in
/-- If the canonical simultaneous socle quotient is a string algebra, then
the original module category has zero Auslander--Reiten surplus.  This is the
axiom-free consequence consumed by the final converse. -/
theorem ambientARSurplus_eq_zero_of_socleFamilyQuotient_admitsStringPresentation
    (hString : BoundQuiver.AdmitsStringPresentation k
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonuniserialProjectiveInjectiveLabels
          S.nonuniserialProjectiveInjectiveLabels_injective))) :
    S.ambientARSurplus = 0 := by
  let T := S.nonuniserialProjectiveInjectiveLabels
  let hInjective := S.nonuniserialProjectiveInjectiveLabels_injective
  let hNotSimple := S.nonuniserialProjectiveInjectiveLabels_notSimple
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  letI : IsNoetherianRing (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  calc
    S.ambientARSurplus =
        (S.idealQuotientFiniteIndecomposableSkeleton J).ambientARSurplus :=
      P.primitiveProjectiveSocleFamily_ambientARSurplus_eq
        T hInjective hNotSimple
    _ = 0 :=
      (S.idealQuotientFiniteIndecomposableSkeleton J
        ).ambientARSurplus_eq_zero_of_admitsStringPresentation hString

include P in
/-- If the canonical simultaneous socle quotient is a string algebra, then
the original module category satisfies the sharp bound `beta ≤ 2`. -/
theorem beta_le_two_of_socleFamilyQuotient_admitsStringPresentation
    (hString : BoundQuiver.AdmitsStringPresentation k
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonuniserialProjectiveInjectiveLabels
          S.nonuniserialProjectiveInjectiveLabels_injective))) :
    FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
  let T := S.nonuniserialProjectiveInjectiveLabels
  let hInjective := S.nonuniserialProjectiveInjectiveLabels_injective
  let hNotSimple := S.nonuniserialProjectiveInjectiveLabels_notSimple
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  letI : IsNoetherianRing (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Q := S.idealQuotientFiniteIndecomposableSkeleton J
  apply P.beta_le_of_primitiveProjectiveSocleFamily_rightMiddleArity_le
    T hInjective hNotSimple 2
  intro j
  exact Q.rightMiddleArity_le_two_of_admitsStringPresentation hString j

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
