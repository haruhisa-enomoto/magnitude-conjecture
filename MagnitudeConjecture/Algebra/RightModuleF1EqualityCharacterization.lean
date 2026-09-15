import MagnitudeConjecture.Algebra.RightModuleF1EqualityBiserialAlgebra
import MagnitudeConjecture.Algebra.RightModuleSocleReductionString
import MagnitudeConjecture.Algebra.RightModuleStandardFormBeta

/-!
# Conditional equality characterization

This file proves the magnitude equality characterization from two explicit
structural hypotheses.  It does not import the module which declares the two
accepted deferred inputs.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture

universe u

/-- The universe-local schema of the deferred representation-finite
Auslander--Reiten characterization. -/
def RepresentationFiniteSpecialBiserialBetaCharacterization
    (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ (B : Type u) [Ring B] [Algebra k B] [FiniteDimensional k B]
    [IsNoetherianRing Bᵐᵒᵖ],
    ∀ T : RightModule.FiniteIndecomposableSkeleton k B,
      BoundQuiver.IsSpecialBiserial k B ↔
        FiniteTauMatrix.beta
          T.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2

namespace RightModule.FiniteIndecomposableSkeleton

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

set_option maxHeartbeats 1000000 in
/-- Equality between categorical magnitude and the projective count is
equivalent to vanishing of the ambient Auslander--Reiten surplus. -/
theorem categoryMagnitude_eq_projectiveCount_iff_ambientARSurplus_eq_zero
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
        (k := k) S.finiteTauCategoryData =
      (@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
        (fun x : Fin S.n ↦ Projective (S.fgObj x))
        (Classical.decPred _) : ℚ) ↔
    S.ambientARSurplus = 0 := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let T := S.finiteTauCategoryData
  let hmono : ∀ x : Fin S.n, Mono (T.rightMesh (T.obj x)).f := by
    intro x
    change Mono (S.canonicalRightMesh (S.fgObj x)).f
    rw [S.canonicalRightMesh_at_label x]
    exact S.labelRightMesh_f_mono x
  let D : MagnitudeConjecture.FiniteTauMatrix.HomMeshInverseData
      (k := k) T :=
    MagnitudeConjecture.FiniteTauMatrix.HomMeshInverseData.ofIsAlgClosed
      T hmono
  letI : DecidablePred T.IsProjective := Classical.decPred _
  have hprojective :
      T.IsProjective = fun x : Fin S.n ↦ Projective (S.fgObj x) := by
    funext x
    apply propext
    exact MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj
      T.toFiniteRightTauCategoryData x
  have heuler :
      @MagnitudeConjecture.ARCount.eulerMagnitude (Fin S.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData)
          T.IsProjective (Classical.decPred _) =
        @MagnitudeConjecture.ARCount.eulerMagnitude (Fin S.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData)
          (fun x : Fin S.n ↦ Projective (S.fgObj x))
          (Classical.decPred _) :=
    congrArg (fun projective : Fin S.n → Prop ↦
      @MagnitudeConjecture.ARCount.eulerMagnitude (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData)
        projective (Classical.decPred projective)) hprojective
  rw [MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude_eq_eulerMagnitude
    T D, heuler]
  constructor
  · intro h
    have hInt :
        @MagnitudeConjecture.ARCount.eulerMagnitude (Fin S.n) inferInstance
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData)
            (fun x : Fin S.n ↦ Projective (S.fgObj x))
            (Classical.decPred _) =
          @MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
            (fun x : Fin S.n ↦ Projective (S.fgObj x))
            (Classical.decPred _) := by
      exact_mod_cast h
    rw [ambientARSurplus, MagnitudeConjecture.ARCount.surplus,
      hInt, sub_self]
  · intro h
    rw [ambientARSurplus, MagnitudeConjecture.ARCount.surplus,
      sub_eq_zero] at h
    exact_mod_cast h

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The `betaAt` value of a standard-form component algebra is the ambient
`betaAt` value at the corresponding original label. -/
theorem standardFormComponentAlgebra_betaAt_eq_original
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (c : S.StandardFormWalkComponent)
    [FiniteDimensional k (S.standardFormComponentAlgebra (k := k) c)]
    [IsNoetherianRing
      (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ]
    (target :
      Fin (S.standardFormComponentAlgebraIndecomposableSkeleton
        (k := k) c).n) :
    FiniteTauMatrix.betaAt
        (S.standardFormComponentAlgebraIndecomposableSkeleton
          (k := k) c).finiteTauCategoryData.toFiniteRightTauCategoryData
        target =
      FiniteTauMatrix.betaAt
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.standardFormComponentVertexEquivFin c target).1 := by
  classical
  let B := S.standardFormComponentAlgebra (k := k) c
  let C := S.standardFormComponentAlgebraIndecomposableSkeleton (k := k) c
  let TC := C.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let p : Fin S.n → Prop := fun i ↦ S.standardFormWalkComponentClass i = c
  let f : Fin S.n → ℕ := fun source ↦
    if TA.IsProjective source then 0
    else FiniteTauMatrix.arrowMultiplicity TA source
      (S.standardFormComponentVertexEquivFin c target).1
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory B) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  have hterm (source : Fin C.n) :
      (if TC.IsProjective source then 0
        else FiniteTauMatrix.arrowMultiplicity TC source target) =
      f (S.standardFormComponentVertexEquivFin c source).1 := by
    change (if TC.IsProjective source then 0
      else FiniteTauMatrix.arrowMultiplicity TC source target) =
        if TA.IsProjective
          (S.standardFormComponentVertexEquivFin c source).1 then 0
        else FiniteTauMatrix.arrowMultiplicity TA
          (S.standardFormComponentVertexEquivFin c source).1
          (S.standardFormComponentVertexEquivFin c target).1
    have hprojective : TC.IsProjective source ↔
        TA.IsProjective
          (S.standardFormComponentVertexEquivFin c source).1 := by
      rw [FiniteTauMatrix.isProjective_iff_projective_obj,
        FiniteTauMatrix.isProjective_iff_projective_obj]
      exact S.standardFormComponentAlgebraSkeleton_projective_iff_original
        (k := k) c source
    by_cases hsource : TC.IsProjective source
    · rw [if_pos hsource, if_pos (hprojective.1 hsource)]
    · rw [if_neg hsource,
        if_neg (fun h ↦ hsource (hprojective.2 h))]
      simpa only [TC, TA, C] using
        S.standardFormComponentAlgebra_arrowMultiplicity_eq_original
          (k := k) c source target
  have hinside :
      (∑ source : Fin C.n,
        if TC.IsProjective source then 0
        else FiniteTauMatrix.arrowMultiplicity TC source target) =
      ∑ source : {i : Fin S.n // p i}, f source.1 := by
    exact Fintype.sum_equiv (S.standardFormComponentVertexEquivFin c)
      (fun source : Fin C.n ↦
        if TC.IsProjective source then 0
        else FiniteTauMatrix.arrowMultiplicity TC source target)
      (fun source : {i : Fin S.n // p i} ↦ f source.1)
      hterm
  have houtside : ∑ source : {i : Fin S.n // ¬ p i}, f source.1 = 0 := by
    apply Finset.sum_eq_zero
    intro source _
    unfold f
    split_ifs
    · rfl
    · rw [S.standardForm_arrowMultiplicity_eq_zero_of_walkComponentClass_ne]
      intro heq
      exact source.2
        (heq.trans (S.standardFormComponentVertexEquivFin c target).2)
  unfold FiniteTauMatrix.betaAt
  rw [hinside]
  calc
    (∑ source : {i : Fin S.n // p i}, f source.1) =
        (∑ source : {i : Fin S.n // p i}, f source.1) +
          ∑ source : {i : Fin S.n // ¬ p i}, f source.1 := by
      rw [houtside, add_zero]
    _ = ∑ source : Fin S.n, f source :=
      Fintype.sum_subtype_add_sum_subtype p f
    _ = _ := rfl

/-- Relative to the deferred AR characterization, equality of the ambient
surplus forces the original `beta` bound. -/
theorem beta_le_two_of_ambientARSurplus_eq_zero
    (hBeta : RepresentationFiniteSpecialBiserialBetaCharacterization k)
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (hzero : S.ambientARSurplus = 0) :
    FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  rw [FiniteTauMatrix.beta_le_iff]
  intro target htarget
  let c := S.standardFormWalkComponentClass target
  let x : S.StandardFormWalkComponentVertex c := ⟨target, rfl⟩
  letI : Fintype (S.StandardFormWalkComponentVertex c) :=
    Fintype.ofFinite _
  let B := S.standardFormComponentAlgebra (k := k) c
  letI : FiniteDimensional k B :=
    S.standardFormComponentAlgebra_finiteDimensional (k := k) c
  letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let C := S.standardFormComponentAlgebraIndecomposableSkeleton (k := k) c
  let base : Fin C.n := (S.standardFormComponentVertexEquivFin c).symm x
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory B) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  letI : Quiver (Fin C.n) := C.standardFormQuiver
  letI (i j : Fin C.n) : Fintype (i ⟶ j) :=
    C.standardFormArrowFintype i j
  have hCzero : C.ambientARSurplus = 0 :=
    S.standardFormComponentAlgebra_ambientARSurplus_eq_zero_of_ambientARSurplus_eq_zero
      hzero c
  have hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        C.standardFormRightMeshData base :=
    S.standardFormComponentAlgebra_isWalkConnectedAt (k := k) c x
  let D := C.standardFormAlgebra C.standardFormMeshHomFinite
  letI : FiniteDimensional k D :=
    C.standardFormAlgebra_finiteDimensional C.standardFormMeshHomFinite
  letI : IsNoetherianRing Dᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let Cstd := C.standardFormAlgebraIndecomposableSkeleton (k := k)
  have hSpecial : BoundQuiver.IsSpecialBiserial k D :=
    UniversalCover.standardFormAlgebra_isSpecialBiserial_of_ambientARSurplus_eq_zero
      C
      base hconnected hCzero
  have hCstdBeta : FiniteTauMatrix.beta
      Cstd.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
    exact (hBeta D Cstd).1 hSpecial
  have hCBeta : FiniteTauMatrix.beta
      C.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
    rw [← C.standardFormAlgebra_beta_eq_original (k := k)]
    exact hCstdBeta
  have hAt := (FiniteTauMatrix.beta_le_iff
    C.finiteTauCategoryData.toFiniteRightTauCategoryData 2).1 hCBeta
  have hCtarget :
      ¬ C.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective base := by
    intro hprojective
    apply htarget
    rw [FiniteTauMatrix.isProjective_iff_projective_obj] at hprojective
    have hOriginal : Projective (S.fgObj target) := by
      have h :=
      (S.standardFormComponentAlgebraSkeleton_projective_iff_original
        (k := k) c base).1 hprojective
      simpa only [base, Equiv.apply_symm_apply] using h
    exact (FiniteTauMatrix.isProjective_iff_projective_obj
      S.finiteTauCategoryData.toFiniteRightTauCategoryData target).2 hOriginal
  have hle := hAt base hCtarget
  rw [S.standardFormComponentAlgebra_betaAt_eq_original c base] at hle
  simpa only [base, Equiv.apply_symm_apply] using hle

namespace PrimitiveProjectivePresentation

variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable (P : S.PrimitiveProjectivePresentation)

/-- The axiom-free conditional equality characterization for a basic algebra.
The two structural inputs appear as explicit hypotheses. -/
theorem ambientARSurplus_eq_zero_iff_isSpecialBiserial
    (hBeta : RepresentationFiniteSpecialBiserialBetaCharacterization k)
    (hSocle : BoundQuiver.IsSpecialBiserial k A →
      BoundQuiver.AdmitsStringPresentation k
        (RightModule.idealQuotientAlgebra
          (P.primitiveProjectiveSocleFamilyIdeal
            S.nonuniserialProjectiveInjectiveLabels
            S.nonuniserialProjectiveInjectiveLabels_injective))) :
    S.ambientARSurplus = 0 ↔ BoundQuiver.IsSpecialBiserial k A := by
  constructor
  · intro hzero
    exact (hBeta A S).2
      (S.beta_le_two_of_ambientARSurplus_eq_zero hBeta hzero)
  · intro hSpecial
    exact P.ambientARSurplus_eq_zero_of_socleFamilyQuotient_admitsStringPresentation
      (hSocle hSpecial)

end PrimitiveProjectivePresentation

end RightModule.FiniteIndecomposableSkeleton

end MagnitudeConjecture
