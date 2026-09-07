import MagnitudeConjecture.CategoryTheory.FiniteTauLocalDensity
import MagnitudeConjecture.Combinatorics.OrbitQuotientLocalDensity

/-!
# Arrow occurrences of a finite tau-category

The displayed summands of all chosen right-mesh middle terms form a literal
finite type of arrow occurrences.  Its target fibre at a label is the finite
index type of that middle-term decomposition, so occurrence counting gives
exactly the finite-tau multiplicity matrix and local density.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.FiniteTauMatrix

open QuotientSubmoduleEquidistribution.Iyama

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteRightTauCategoryData C Ind)

/-- A right-arrow occurrence is a displayed indecomposable summand of the
chosen right-mesh middle term at its target label. -/
abbrev RightArrowOccurrence :=
  Σ Y : Ind, Fin (rightMiddleArity T Y)

/-- Source label of a displayed right-arrow occurrence. -/
def rightArrowSource (a : RightArrowOccurrence T) : Ind :=
  rightMiddleLabel T a.1 a.2

/-- Target label of a displayed right-arrow occurrence. -/
def rightArrowTarget (a : RightArrowOccurrence T) : Ind :=
  a.1

/-- The occurrences ending at `Y` are exactly the displayed summands of its
right-mesh middle term. -/
def rightArrowTargetFiberEquiv (Y : Ind) :
    {a : RightArrowOccurrence T // rightArrowTarget T a = Y} ≃
      Fin (rightMiddleArity T Y) where
  toFun a := Fin.cast
    (congrArg (rightMiddleArity T) a.property) a.1.2
  invFun i := ⟨⟨Y, i⟩, rfl⟩
  left_inv a := by
    rcases a with ⟨⟨Y', i⟩, h⟩
    change Y' = Y at h
    subst Y'
    rfl
  right_inv _ := rfl

/-- Fixing both source and target leaves precisely the displayed middle
indices carrying that source label. -/
def rightArrowSourceTargetFiberEquiv (X Y : Ind) :
    {a : RightArrowOccurrence T //
      rightArrowSource T a = X ∧ rightArrowTarget T a = Y} ≃
      {i : Fin (rightMiddleArity T Y) //
        rightMiddleLabel T Y i = X} := by
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨Y', i⟩, hs, ht⟩
    change Y' = Y at ht
    subst Y'
    exact ⟨i, hs⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨Y, i⟩, hi, rfl⟩
  · rintro ⟨⟨Y', i⟩, hs, ht⟩
    change Y' = Y at ht
    subst Y'
    rfl
  · rintro ⟨i, hi⟩
    rfl

/-- Counting canonical occurrences with fixed endpoints recovers the
finite-tau arrow multiplicity entry. -/
theorem arrowMultiplicityOfOccurrences_eq (X Y : Ind) :
    CoveringAction.arrowMultiplicityOfOccurrences
        (rightArrowSource T) (rightArrowTarget T) X Y =
      arrowMultiplicity T X Y := by
  classical
  rw [CoveringAction.arrowMultiplicityOfOccurrences, arrowMultiplicity,
    Nat.card_congr (rightArrowSourceTargetFiberEquiv T X Y),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- The occurrence indegree is the literal right-middle arity. -/
theorem occurrenceIndegree_rightArrowTarget_eq (Y : Ind) :
    CoveringAction.occurrenceIndegree (rightArrowTarget T) Y =
      (rightMiddleArity T Y : ℤ) := by
  rw [CoveringAction.occurrenceIndegree]
  exact congrArg (fun n : ℕ ↦ (n : ℤ))
    ((Nat.card_congr (rightArrowTargetFiberEquiv T Y)).trans
      (Nat.card_fin _))

/-- The occurrence form of local density for the canonical right-arrow type
is the incoming-arity form. -/
theorem occurrenceLocalDensity_rightArrowTarget_eq
    [DecidablePred T.IsProjective] (Y : Ind) :
    CoveringAction.occurrenceLocalDensity
        (rightArrowTarget T) T.IsProjective Y =
      ARCount.localDensityOfIncomingArity
        (rightMiddleArity T Y) (T.IsProjective Y) := by
  rw [CoveringAction.occurrenceLocalDensity,
    occurrenceIndegree_rightArrowTarget_eq]
  rfl

/-- The finite-tau multiplicity-matrix local density is exactly the local
density of its canonical right-arrow occurrence type. -/
theorem localDensity_eq_occurrenceLocalDensity
    [DecidablePred T.IsProjective] (Y : Ind) :
    ARCount.localDensity (arrowMultiplicity T) T.IsProjective Y =
      CoveringAction.occurrenceLocalDensity
        (rightArrowTarget T) T.IsProjective Y := by
  rw [localDensity_eq_localDensityOfIncomingArity T Y
      (rightMiddleArity T Y) rfl (T.IsProjective Y) Iff.rfl,
    occurrenceLocalDensity_rightArrowTarget_eq]

end MagnitudeConjecture.FiniteTauMatrix
