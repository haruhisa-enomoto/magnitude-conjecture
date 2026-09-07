import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleFamily
import MagnitudeConjecture.CategoryTheory.FiniteTauBeta

/-!
# The beta bound under projective-injective socle rejection

Simultaneous rejection removes projective-injective vertices and replaces
each of them by its socle quotient.  At an ordinary surviving endpoint the
right-mesh arity is unchanged.  At a replacement endpoint the ambient middle
term has one additional occurrence, but that occurrence is the deleted
projective itself and hence is not counted by `beta`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

include P in
/-- At a replacement endpoint, the nonprojective ambient middle
occurrences fit inside the rejected middle term: the single additional
ambient occurrence is the selected projective-injective itself. -/
theorem primitiveProjectiveSocleFamily_replacement_betaAt_le_rejected_arity
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    FiniteTauMatrix.betaAt
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.idealQuotientFiniteLabelEquiv
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
          (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
            T hInjective hNotSimple p hp)).1 ≤
      FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
            ).toFiniteRightTauCategoryData
        (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
          T hInjective hNotSimple p hp) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let j := P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
    T hInjective hNotSimple p hp
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p (hInjective p hp) (hNotSimple p hp)
  let B := S.minimalRightAlmostSplitAt z.1
  let dA := S.minimalRightAlmostSplitAtDecomposition z.1
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TQ := (idealQuotientFiniteTauCategoryData S J
    ).toFiniteRightTauCategoryData
  obtain ⟨t, ht⟩ := P.exists_projectiveInjectiveMiddleOccurrence_at_socleQuotient
    p (hInjective p hp) (hNotSimple p hp)
  let epsilon : B.index ≃ Fin dA.n := Fintype.equivFin B.index
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  have hprojective : TA.IsProjective
      (B.label (epsilon.symm (epsilon t))) := by
    rw [epsilon.symm_apply_apply, ht]
    rw [FiniteTauMatrix.isProjective_iff_projective_obj]
    exact p.projective
  have hbeta :=
    FiniteTauMatrix.betaAt_add_one_le_of_minimalRightAlmostSplitDecomposition_projective
      TA z.1 (fun i : Fin dA.n ↦ B.label (epsilon.symm i))
      ⟨dA.isoBiproduct⟩ B.rightAlmostSplit B.rightMinimal
      (epsilon t) hprojective
  have harity :=
    P.primitiveProjectiveSocleFamily_replacement_rightMiddleArity_add_one_eq_ambient
      T hInjective hNotSimple p hp
  have hj : S.idealQuotientFiniteLabelEquiv J j =
      P.primitiveProjectiveSocleFamilyReplacementLabel
        T hInjective hNotSimple p hp :=
    P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
      T hInjective hNotSimple p hp
  have hz :
      (S.idealQuotientFiniteLabelEquiv J j).1 = z.1 :=
    congrArg Subtype.val hj
  have hA : FiniteTauMatrix.rightMiddleArity TA z.1 = dA.n :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TA z.1 dA B.rightAlmostSplit B.rightMinimal
  have harity' : FiniteTauMatrix.rightMiddleArity TQ j + 1 = dA.n := by
    calc
      FiniteTauMatrix.rightMiddleArity TQ j + 1 =
          FiniteTauMatrix.rightMiddleArity TA
            (S.idealQuotientFiniteLabelEquiv J j).1 := harity
      _ = FiniteTauMatrix.rightMiddleArity TA z.1 := by rw [hz]
      _ = dA.n := hA
  change FiniteTauMatrix.betaAt TA
      (S.idealQuotientFiniteLabelEquiv J j).1 ≤
    FiniteTauMatrix.rightMiddleArity TQ j
  rw [hz]
  omega

include P in
/-- If every right-mesh middle term of the simultaneous socle quotient has
arity at most `bound`, then the ambient `beta` is at most `bound`.  Ordinary
surviving endpoints keep their arity; at a replacement endpoint the one
discarded occurrence is projective and therefore invisible to `beta`. -/
theorem beta_le_of_primitiveProjectiveSocleFamily_rightMiddleArity_le
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (bound : ℕ)
    (hbound : ∀ j,
      FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
            ).toFiniteRightTauCategoryData j ≤ bound) :
    FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ bound := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TQ := (idealQuotientFiniteTauCategoryData S J
    ).toFiniteRightTauCategoryData
  let q := S.idealQuotientFiniteLabelEquiv J
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  rw [FiniteTauMatrix.beta_le_iff]
  intro target htarget
  have hnotSelected : ∀ (p : S.ProjectiveLabel), p ∈ T →
      target ≠ p.label := by
    intro p hp htp
    apply htarget
    rw [htp, FiniteTauMatrix.isProjective_iff_projective_obj]
    exact p.projective
  have hAnnihilated : RightModule.IsAnnihilatedBy J (S.fgObj target) :=
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective target).2 hnotSelected
  let x : S.IdealQuotientLabel J := ⟨target, hAnnihilated⟩
  let j : Fin (S.idealQuotientFiniteIndecomposableSkeleton J).n :=
    q.symm x
  have hq : q j = x := q.apply_symm_apply x
  have hqval : (q j).1 = target := congrArg Subtype.val hq
  by_cases hreplacement :
      ∃ (p : S.ProjectiveLabel) (hp : p ∈ T),
        target = (P.socleQuotientReplacementLabel
          p (hInjective p hp) (hNotSimple p hp)).1
  · obtain ⟨p, hp, htargetReplacement⟩ := hreplacement
    let jr := P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
      T hInjective hNotSimple p hp
    have hqjr : q jr =
        P.primitiveProjectiveSocleFamilyReplacementLabel
          T hInjective hNotSimple p hp :=
      P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
        T hInjective hNotSimple p hp
    have hqjr_x : q jr = x := by
      apply Subtype.ext
      exact (congrArg Subtype.val hqjr).trans htargetReplacement.symm
    have hjr : jr = j := q.injective (hqjr_x.trans hq.symm)
    have hbeta :=
      P.primitiveProjectiveSocleFamily_replacement_betaAt_le_rejected_arity
        T hInjective hNotSimple p hp
    have hqjrval : (q jr).1 = target :=
      congrArg Subtype.val hqjr_x
    change FiniteTauMatrix.betaAt TA target ≤ bound
    calc
      FiniteTauMatrix.betaAt TA target =
          FiniteTauMatrix.betaAt TA (q jr).1 := by rw [hqjrval]
      _ ≤ FiniteTauMatrix.rightMiddleArity TQ jr := hbeta
      _ ≤ bound := hbound jr
  · have hordinary : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T),
        (q j).1 ≠ (P.socleQuotientReplacementLabel
          p (hInjective p hp) (hNotSimple p hp)).1 := by
      intro p hp heq
      apply hreplacement
      exact ⟨p, hp, hqval.symm.trans heq⟩
    have harity :=
      P.primitiveProjectiveSocleFamily_rightMiddleArity_eq_ambient
        T hInjective hNotSimple j hordinary
    change FiniteTauMatrix.betaAt TA target ≤ bound
    calc
      FiniteTauMatrix.betaAt TA target ≤
          FiniteTauMatrix.rightMiddleArity TA target :=
        FiniteTauMatrix.betaAt_le_rightMiddleArity TA target
      _ = FiniteTauMatrix.rightMiddleArity TA (q j).1 := by rw [hqval]
      _ = FiniteTauMatrix.rightMiddleArity TQ j := harity
      _ ≤ bound := hbound j

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
