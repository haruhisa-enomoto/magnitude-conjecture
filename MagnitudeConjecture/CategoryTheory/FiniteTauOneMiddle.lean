import MagnitudeConjecture.CategoryTheory.FiniteTauIrreducible
import MagnitudeConjecture.CategoryTheory.FiniteTauOccurrences

/-!
# One-middle meshes in a finite tau-category

The frozen manuscript writes `E₁` for the number of almost split meshes whose
middle term has exactly one indecomposable occurrence.  This file packages
that literal finite type and records the numerical reduction of the AR
surplus when every nonprojective mesh has at most two middle occurrences.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.Iyama

namespace MagnitudeConjecture.FiniteTauMatrix

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteTauCategoryData C Ind)

local instance : DecidablePred T.IsProjective := Classical.decPred _

/-- Nonprojective right meshes having exactly one indecomposable middle-term
occurrence.  Repeated isomorphic summands would be separate occurrences, so
the equality to one has the manuscript's multiplicity convention. -/
abbrev OneMiddleMesh :=
  {Y : Ind // ¬ T.IsProjective Y ∧
    rightMiddleArity T.toFiniteRightTauCategoryData Y = 1}

/-- The manuscript's `E₁`. -/
def oneMiddleMeshCount : ℕ :=
  Nat.card (OneMiddleMesh T)

/-- Total incoming-arrow multiplicity at tau-projective targets. -/
def projectiveIncomingArity : ℕ := by
  classical
  exact ∑ Y : Ind,
    if T.IsProjective Y then
      rightMiddleArity T.toFiniteRightTauCategoryData Y
    else 0

/-- An explicit equivalence with the one-middle mesh type computes `E₁`. -/
theorem oneMiddleMeshCount_eq_natCard_of_equiv
    {α : Type*} [Finite α] (e : α ≃ OneMiddleMesh T) :
    oneMiddleMeshCount T = Nat.card α := by
  rw [oneMiddleMeshCount, Nat.card_congr e]

/-- The one-middle indicator sums to `E₁`. -/
theorem sum_oneMiddleIndicator_eq_oneMiddleMeshCount :
    (∑ Y : Ind,
      if ¬ T.IsProjective Y ∧
          rightMiddleArity T.toFiniteRightTauCategoryData Y = 1
        then (1 : ℤ) else 0) =
      (oneMiddleMeshCount T : ℤ) := by
  classical
  rw [oneMiddleMeshCount, Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype]
  simp

/-- The projective incoming-arity indicator sums to the integer form of the
projective incoming count. -/
theorem sum_projectiveIncomingIndicator_eq_projectiveIncomingArity :
    (∑ Y : Ind,
      if T.IsProjective Y then
        (rightMiddleArity T.toFiniteRightTauCategoryData Y : ℤ)
      else 0) =
      (projectiveIncomingArity T : ℤ) := by
  classical
  simp [projectiveIncomingArity]

/-- Under the two-middle bound, local AR density is `1` precisely at a
one-middle mesh, is minus the incoming arity at a projective, and is zero at
every other vertex. -/
theorem localDensity_eq_oneMiddleIndicator_sub_projectiveIncoming
    (hbound : ∀ Y : Ind, ¬ T.IsProjective Y →
      rightMiddleArity T.toFiniteRightTauCategoryData Y ≤ 2)
    (Y : Ind) :
    ARCount.localDensity
        (arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.IsProjective Y =
      (if ¬ T.IsProjective Y ∧
          rightMiddleArity T.toFiniteRightTauCategoryData Y = 1
        then 1 else 0) -
      (if T.IsProjective Y then
        (rightMiddleArity T.toFiniteRightTauCategoryData Y : ℤ)
      else 0) := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity
    T.toFiniteRightTauCategoryData Y
    (rightMiddleArity T.toFiniteRightTauCategoryData Y) rfl
    (T.IsProjective Y) Iff.rfl]
  unfold ARCount.localDensityOfIncomingArity
  by_cases hY : T.IsProjective Y
  · simp [hY]
  · have hpos :
        0 < rightMiddleArity T.toFiniteRightTauCategoryData Y :=
      rightMiddleArity_pos_of_nonprojective T ⟨Y, hY⟩
    have hle := hbound Y hY
    have hcases :
        rightMiddleArity T.toFiniteRightTauCategoryData Y = 1 ∨
          rightMiddleArity T.toFiniteRightTauCategoryData Y = 2 := by
      omega
    rcases hcases with h | h <;> simp [hY, h]

/-- If every nonprojective mesh has at most two middle occurrences, the AR
surplus is `E₁` minus the total incoming multiplicity at projectives.  This is
the manuscript's `E₁ - ell` reduction without introducing a separate `E₂`. -/
theorem surplus_eq_oneMiddleMeshCount_sub_projectiveIncomingArity
    (hbound : ∀ Y : Ind, ¬ T.IsProjective Y →
      rightMiddleArity T.toFiniteRightTauCategoryData Y ≤ 2) :
    ARCount.surplus
        (arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.IsProjective =
      (oneMiddleMeshCount T : ℤ) - projectiveIncomingArity T := by
  classical
  rw [← ARCount.sum_localDensity_eq_surplus]
  calc
    (∑ Y : Ind,
        ARCount.localDensity
          (arrowMultiplicity T.toFiniteRightTauCategoryData)
          T.IsProjective Y) =
        ∑ Y : Ind,
          ((if ¬ T.IsProjective Y ∧
              rightMiddleArity T.toFiniteRightTauCategoryData Y = 1
            then 1 else 0) -
          (if T.IsProjective Y then
            (rightMiddleArity T.toFiniteRightTauCategoryData Y : ℤ)
          else 0)) := by
      apply Finset.sum_congr rfl
      intro Y _
      exact localDensity_eq_oneMiddleIndicator_sub_projectiveIncoming
        T hbound Y
    _ = (∑ Y : Ind,
          if ¬ T.IsProjective Y ∧
              rightMiddleArity T.toFiniteRightTauCategoryData Y = 1
            then (1 : ℤ) else 0) -
        ∑ Y : Ind,
          if T.IsProjective Y then
            (rightMiddleArity T.toFiniteRightTauCategoryData Y : ℤ)
          else 0 := by rw [Finset.sum_sub_distrib]
    _ = (oneMiddleMeshCount T : ℤ) - projectiveIncomingArity T := by
      rw [sum_oneMiddleIndicator_eq_oneMiddleMeshCount T,
        sum_projectiveIncomingIndicator_eq_projectiveIncomingArity T]

end MagnitudeConjecture.FiniteTauMatrix
