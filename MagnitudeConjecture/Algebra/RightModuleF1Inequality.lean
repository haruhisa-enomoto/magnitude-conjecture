import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentARIdentification
import MagnitudeConjecture.Algebra.RightModuleF1CoveringBridge
import MagnitudeConjecture.CategoryTheory.Magnitude
import MagnitudeConjecture.Combinatorics.F1FiniteDeletionAverage
import MagnitudeConjecture.CategoryTheory.F1FiniteSupportMonotonicity

/-!
# Frozen finite-deletion inequality route

This module is the F1 production layer for the lower-bound endpoint.  The
standard-form component induction calls the F1 covering bridge, while finite
support and positive deletion-order interfaces are exposed in the category
and combinatorics modules beside it.
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

set_option maxHeartbeats 5000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Frozen manuscript, the inequality half of the magnitude conjecture in
Auslander--Reiten surplus form. -/
theorem ambientARSurplus_nonnegative
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    0 ≤ S.ambientARSurplus := by
  induction hn : S.n using Nat.strong_induction_on generalizing A S with
  | h n ih =>
      apply S.ambientARSurplus_nonnegative_of_standardFormComponents_nonnegative
      intro c
      letI : Fintype (S.StandardFormWalkComponentVertex c) :=
        Fintype.ofFinite _
      letI : FiniteDimensional k
          (S.standardFormComponentAlgebra (k := k) c) :=
        S.standardFormComponentAlgebra_finiteDimensional (k := k) c
      letI : IsNoetherianRing
          (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ :=
        IsNoetherianRing.of_finite k _
      let Ask := S.standardFormComponentAlgebraIndecomposableSkeleton
        (k := k) c
      letI : Quiver (Fin Ask.n) := Ask.standardFormQuiver
      letI (i j : Fin Ask.n) : Fintype (i ⟶ j) :=
        Ask.standardFormArrowFintype i j
      let x₀ := Classical.choice (S.standardFormWalkComponentVertex_nonempty c)
      let base : Fin Ask.n :=
        (S.standardFormComponentVertexEquivFin c).symm x₀
      have hconnected :
          MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
            Ask.standardFormRightMeshData base := by
        exact S.standardFormComponentAlgebra_isWalkConnectedAt
          (k := k) c x₀
      let pComponent :=
        Classical.choice (S.standardFormComponentProjectiveVertex_nonempty
          (k := k) c)
      let p : Fin Ask.n :=
        (S.standardFormComponentVertexEquivFin c).symm pComponent.1
      have hp : Projective (Ask.fgObj p) := by
        apply (S.standardFormComponentAlgebraSkeleton_projective_iff_original
          (k := k) c p).2
        simpa only [p, Equiv.apply_symm_apply] using pComponent.2
      obtain ⟨walk⟩ := hconnected p
      let W := MeshCategory.RightMeshData.UniversalCover.walkVertex
        Ask.standardFormRightMeshData base walk
      let X : UniversalCover.SourceCategory Ask base :=
        MeshCategory.obj (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            Ask.standardFormRightMeshData base) W
      have hX : UniversalCover.standardFormProjectiveProperty Ask base X := by
        change Projective (Ask.fgObj W.1)
        exact hp
      let xProjective : UniversalCover.StandardFormProjectiveSourceCategory
          Ask base := ⟨X, hX⟩
      let x :
          (UniversalCover.StandardFormProjectiveSourceCategory Ask base)ᵒᵖ :=
        Opposite.op xProjective
      let P := UniversalCover.standardFormCoveringPrimitive
        Ask base hconnected x
      let B := Ask.standardFormAlgebra Ask.standardFormMeshHomFinite
      letI : FiniteDimensional k B :=
        Ask.standardFormAlgebra_finiteDimensional
          Ask.standardFormMeshHomFinite
      letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k _
      let Sstd := Ask.standardFormAlgebraIndecomposableSkeleton (k := k)
      let Bq := RightModule.primitiveQuotientAlgebra
        (UniversalCover.standardFormCoveringIdempotent
          Ask base hconnected x)
      letI : IsNoetherianRing Bqᵐᵒᵖ := IsNoetherianRing.of_finite k _
      let Q := Sstd.primitiveQuotientFiniteIndecomposableSkeleton P
      have hQltStd : Q.n < Sstd.n := by
        change Nat.card (Sstd.PrimitiveQuotientLabel P) < Sstd.n
        simpa only [Nat.card_fin] using
          (Finite.card_subtype_lt
            (Sstd.primitiveSource_not_mem_primitiveKilledLabels P))
      have hAskLe : Ask.n ≤ S.n := by
        change Fintype.card (S.StandardFormWalkComponentVertex c) ≤ S.n
        simpa only [Fintype.card_fin] using
          (Fintype.card_le_of_injective
            (f := fun x : S.StandardFormWalkComponentVertex c ↦ x.1)
              Subtype.val_injective)
      have hQlt : Q.n < n := by
        rw [← hn]
        exact hQltStd.trans_le hAskLe
      have hQnonnegative : 0 ≤ Q.ambientARSurplus :=
        ih Q.n hQlt Q rfl
      have hdeletion : Q.ambientARSurplus ≤ Sstd.ambientARSurplus :=
        UniversalCover.standardFormCoveringPrimitiveQuotient_ambientARSurplus_le
          Ask base hconnected x
      have hstandard : 0 ≤ Sstd.ambientARSurplus :=
        hQnonnegative.trans hdeletion
      have hcomponentAlgebra : 0 ≤ Ask.ambientARSurplus := by
        rw [← Ask.standardFormAlgebra_ambientARSurplus_eq_original
          (k := k)]
        exact hstandard
      rw [← S.standardFormComponentAlgebra_ambientARSurplus_eq_componentSurplus
        (k := k) c]
      exact hcomponentAlgebra

set_option maxHeartbeats 1000000 in
/-- Frozen manuscript, the magnitude inequality on the chosen duplicate-free
indecomposable right-module skeleton.  The projective count is the paper's
number of simple modules. -/
theorem categoryMagnitude_ge_projectiveCount
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    (@MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
        (fun x : Fin S.n ↦ Projective (S.fgObj x))
        (Classical.decPred _) : ℚ) ≤
      MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude
        (k := k) S.finiteTauCategoryData := by
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
  rw [MagnitudeConjecture.FiniteTauMatrix.categoryMagnitude_eq_eulerMagnitude
    T D]
  have hprojective (x : Fin S.n) : T.IsProjective x ↔
      Projective (S.fgObj x) :=
    MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj
      T.toFiniteRightTauCategoryData x
  letI : DecidablePred (fun x : Fin S.n ↦ Projective (S.fgObj x)) :=
    Classical.decPred _
  let projectiveComplementEquiv :
      {x : Fin S.n // ¬ T.IsProjective x} ≃
        {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
    { toFun := fun x ↦ ⟨x.1, fun hx ↦ x.2 ((hprojective x.1).2 hx)⟩
      invFun := fun x ↦ ⟨x.1, fun hx ↦ x.2 ((hprojective x.1).1 hx)⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl }
  have hmesh :
      @MagnitudeConjecture.ARCount.meshCount (Fin S.n) inferInstance
          T.IsProjective (Classical.decPred _) =
        @MagnitudeConjecture.ARCount.meshCount (Fin S.n) inferInstance
          (fun x : Fin S.n ↦ Projective (S.fgObj x))
          (Classical.decPred _) := by
    unfold MagnitudeConjecture.ARCount.meshCount
    exact_mod_cast Fintype.card_congr projectiveComplementEquiv
  rw [MagnitudeConjecture.ARCount.eulerMagnitude, hmesh]
  dsimp only [T]
  have hsurplus := S.ambientARSurplus_nonnegative
  rw [ambientARSurplus, MagnitudeConjecture.ARCount.surplus] at hsurplus
  exact_mod_cast (sub_nonneg.mp hsurplus)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
