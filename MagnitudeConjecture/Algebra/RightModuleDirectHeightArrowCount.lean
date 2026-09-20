import MagnitudeConjecture.Algebra.RightModuleDirectBoundaryDegrees
import MagnitudeConjecture.Combinatorics.HeightBoundaryPointCount

/-! # The direct height formula for the actual factor's arrow count -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

theorem PrimitiveDirectedBoundaryData.directHeight_arrow_count
    (B : S.PrimitiveDirectedBoundaryData D) :
    (∑ X, ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ)) =
    2 * Fintype.card (S.SurvivingLabel K) - (B.directFactorHeight D.sink : ℤ) - 2 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let a := fun X Y ↦ (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
    T.toFiniteRightTauCategoryData X Y : ℤ)
  let h := fun X ↦ (B.directFactorHeight X : ℤ)
  let incoming := fun Y ↦ ∑ X, a X Y
  let outgoing := fun X ↦ ∑ Y, a X Y
  have he : ∀ X : T.Nonprojective, h X.1 = h (T.tauPlusEquiv X).1 + 2 := by
    intro X
    dsimp only [h]
    exact_mod_cast B.directFactorHeight_tauPlus X
  have ha : ∀ X : T.Nonprojective, incoming X.1 = outgoing (T.tauPlusEquiv X).1 := by
    intro X
    apply Finset.sum_congr rfl
    intro Y _
    have ht : T.tauMinus (T.tauPlusEquiv X) = X.1 :=
      congrArg Subtype.val (T.tauPlusEquiv.symm_apply_apply X)
    have hh := MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity_eq_translation
      T D.homMeshInverseData D.leftMesh_epi (T.tauPlusEquiv X) Y
    rw [ht] at hh
    dsimp only [a]
    exact_mod_cast hh.symm
  have hp : ∀ X : {X // T.IsProjective X}, incoming X.1 =
      if X = D.sourceProjectiveLabel then 0 else 1 := by
    intro X
    by_cases hx : X = D.sourceProjectiveLabel
    · subst X
      simp only [ite_true]
      dsimp only [incoming, a]
      exact_mod_cast B.directHeight_source_incoming_zero
    · rw [if_neg hx]
      exact B.directCount_incoming_eq_one X.1 X.2 (fun heq ↦ hx (Subtype.ext heq))
  have hi : ∀ X : {X // T.IsInjective X}, outgoing X.1 =
      if X = D.sinkInjectiveLabel then 0 else 1 := by
    intro X
    by_cases hx : X = D.sinkInjectiveLabel
    · subst X
      simp only [ite_true]
      apply Finset.sum_eq_zero
      intro Y _
      have hz : MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData D.sink Y = 0 := by
        by_contra hy
        exact B.directFactorArrow_sink_false Y hy
      change (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        T.toFiniteRightTauCategoryData D.sink Y : ℤ) = 0
      exact_mod_cast hz
    · rw [if_neg hx]
      exact B.directCount_outgoing_eq_one X.1 X.2 (fun heq ↦ hx (Subtype.ext heq))
  have hps := HeightArrowCount.boundary_sums D.sourceProjectiveLabel
    (fun X ↦ h X.1) (fun X ↦ incoming X.1) hp
  have his := HeightArrowCount.boundary_sums D.sinkInjectiveLabel
    (fun X ↦ h X.1) (fun X ↦ outgoing X.1) hi
  have hs : h D.source = 0 := by simp [h, B.directFactorHeight_source]
  have hpin : (∑ X : {X // T.IsProjective X}, h X.1 * incoming X.1) =
      ∑ X : {X // T.IsProjective X}, h X.1 := by
    have hpzero : h D.sourceProjectiveLabel.1 = 0 := hs
    simpa only [hpzero, sub_zero] using hps.2
  have hc := HeightArrowCount.boundary_card_eq T.IsProjective T.IsInjective T.tauPlusEquiv
  have hicount : (∑ X : {X // T.IsInjective X}, outgoing X.1) =
      (Fintype.card {X // T.IsProjective X} : ℤ) - 1 := by
    rw [hc]
    exact his.1
  exact (HeightArrowCount.count_of_boundary_sums T.IsProjective T.IsInjective
    T.tauPlusEquiv h incoming outgoing (∑ X, ∑ Y, a X Y) (h D.sink)
    he ha B.directHeight_weighted_arrow_count rfl hpin his.2 hicount).1

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
