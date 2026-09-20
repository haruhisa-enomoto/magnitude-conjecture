import MagnitudeConjecture.Algebra.RightModuleDirectHeightSource
import MagnitudeConjecture.Combinatorics.RankedSinkReachability

/-! # The unique sink and direct-height bounds -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- The only vertex without an outgoing official arrow is I. -/
theorem PrimitiveDirectedBoundaryData.directFactor_eq_sink_of_no_outgoing
    (_B : S.PrimitiveDirectedBoundaryData D) (X : S.SurvivingLabel K)
    (hX : ¬ ∃ Y, directFactorArrow X Y) : X = D.sink := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let w := fun Y : S.SurvivingLabel K ↦ (D.multiplicity Y.1 : ℤ)
  have ha : ∀ Y, MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      T.toFiniteRightTauCategoryData X Y = 0 := by
    intro Y
    by_contra hy
    exact hX ⟨Y, hy⟩
  have hu := D.meshUnitEquations.2 X
  change MagnitudeConjecture.FiniteTauMatrix.meshRowWeight T w X =
    if X = D.sink then 1 else 0 at hu
  have hpos : 0 < w X := by
    dsimp only [w]
    exact_mod_cast PrimitiveMultiplicityInput.multiplicity_pos (S := S) D X
  by_contra hne
  by_cases hi : T.IsInjective X
  · rw [MagnitudeConjecture.FiniteTauMatrix.meshRowWeight_eq_of_injective T w X hi] at hu
    simp [ha, hne] at hu
    omega
  · rw [MagnitudeConjecture.FiniteTauMatrix.meshRowWeight_eq_of_noninjective T w ⟨X, hi⟩] at hu
    have ht : 0 < w (T.tauMinus ⟨X, hi⟩) := by
      dsimp only [w]
      exact_mod_cast PrimitiveMultiplicityInput.multiplicity_pos (S := S) D _
    simp [ha, hne] at hu
    omega

/-- Every surviving vertex reaches I by official arrows. -/
theorem PrimitiveDirectedBoundaryData.directFactor_reaches_sink
    (B : S.PrimitiveDirectedBoundaryData D) (X : S.SurvivingLabel K) :
    Relation.ReflTransGen (directFactorArrow (S := S) (K := K)) X D.sink :=
  RankedReachability.reaches_sink B.directHeightRank _ B.directHeightRank_lt_of_arrow
    D.sink B.directFactor_eq_sink_of_no_outgoing X

/-- A nontrivial chain of official arrows strictly raises height. -/
theorem PrimitiveDirectedBoundaryData.directFactor_reaches_eq_or_height_lt
    (B : S.PrimitiveDirectedBoundaryData D)
    {X Y : S.SurvivingLabel K}
    (h : Relation.ReflTransGen (directFactorArrow (S := S) (K := K)) X Y) :
    X = Y ∨ B.directFactorHeight X < B.directFactorHeight Y := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail Y Z h hyz ih =>
    right
    have he := B.directFactorHeight_arrow Y Z hyz
    rcases ih with rfl | hi <;> omega

/-- Every direct height is bounded by the sink height. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_le_sink
    (B : S.PrimitiveDirectedBoundaryData D) (X : S.SurvivingLabel K) :
    B.directFactorHeight X ≤ B.directFactorHeight D.sink := by
  rcases B.directFactor_reaches_eq_or_height_lt (B.directFactor_reaches_sink X) with h | h
  · rw [h]
  · exact h.le

/-- The sink is the unique vertex at maximum direct height. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_eq_sink_iff
    (B : S.PrimitiveDirectedBoundaryData D) (X : S.SurvivingLabel K) :
    B.directFactorHeight X = B.directFactorHeight D.sink ↔ X = D.sink := by
  constructor
  · intro hx
    rcases B.directFactor_reaches_eq_or_height_lt (B.directFactor_reaches_sink X) with h | h
    · exact h
    · omega
  · rintro rfl
    rfl

/-- No official arrow leaves the distinguished sink. -/
theorem PrimitiveDirectedBoundaryData.directFactorArrow_sink_false
    (B : S.PrimitiveDirectedBoundaryData D) (Y : S.SurvivingLabel K) :
    ¬ directFactorArrow D.sink Y := by
  intro hy
  have he := B.directFactorHeight_arrow D.sink Y hy
  have hb := B.directFactorHeight_le_sink Y
  omega

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
