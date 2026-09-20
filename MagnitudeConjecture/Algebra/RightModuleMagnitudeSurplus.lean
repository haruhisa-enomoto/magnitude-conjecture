import MagnitudeConjecture.Algebra.RightModuleIntervalInequality
import MagnitudeConjecture.CategoryTheory.Magnitude

/-! # Magnitude and the ambient Auslander--Reiten surplus -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

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


/-- The magnitude lower bound follows from nonnegative interval surplus.
The projective count equals the number of simple modules. -/
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
  have hsurplus := S.ambientARSurplus_nonnegative_by_intervals
  rw [ambientARSurplus, MagnitudeConjecture.ARCount.surplus] at hsurplus
  exact_mod_cast (sub_nonneg.mp hsurplus)


end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
