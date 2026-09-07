import MagnitudeConjecture.CategoryTheory.FiniteTauLocalDensity
import Mathlib.Data.Fintype.BigOperators

/-!
# The numerical profile of one Drozd--Kiričenko rejection

Removing a non-simple indecomposable projective-injective deletes one
projective vertex of incoming arity one.  Its unique successor becomes
projective and loses the deleted vertex from its incoming middle term; all
other projectivity predicates and incoming arities are unchanged.  This file
packages exactly that finite-tau profile and proves that it preserves the
Auslander--Reiten surplus.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.FiniteTauMatrix

open QuotientSubmoduleEquidistribution.Iyama

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasFiniteBiproducts D] [HasBinaryBiproducts D]
  [IsIdempotentComplete D]
variable {I : Type w₁} [Fintype I]
variable {J : Type w₂} [Fintype J]

/-- The exact finite-tau change caused by rejecting one non-simple
indecomposable projective-injective.  `ambient` is the category before
rejection and `rejected` is the category afterwards. -/
structure RejectionProfile
    (ambient : FiniteRightTauCategoryData C I)
    (rejected : FiniteRightTauCategoryData D J) where
  /-- The removed projective-injective label. -/
  deleted : I
  /-- The surviving label represented by `U / soc(U)`, which becomes
  projective after rejection. -/
  replacement : J
  /-- The rejected labels are exactly the ambient labels other than the
  deleted one. -/
  surviving : J ≃ {i : I // i ≠ deleted}
  deleted_projective : ambient.IsProjective deleted
  deleted_arity : rightMiddleArity ambient deleted = 1
  replacement_ambient_nonprojective :
    ¬ ambient.IsProjective (surviving replacement).1
  replacement_rejected_projective :
    rejected.IsProjective replacement
  projective_iff_of_ne : ∀ j : J, j ≠ replacement →
    (ambient.IsProjective (surviving j).1 ↔ rejected.IsProjective j)
  replacement_arity :
    rightMiddleArity rejected replacement + 1 =
      rightMiddleArity ambient (surviving replacement).1
  arity_eq_of_ne : ∀ j : J, j ≠ replacement →
    rightMiddleArity ambient (surviving j).1 =
      rightMiddleArity rejected j

namespace RejectionProfile

variable
    {ambient : FiniteRightTauCategoryData C I}
    {rejected : FiniteRightTauCategoryData D J}
    (R : RejectionProfile ambient rejected)

noncomputable local instance rejectionProfileAmbientProjectiveDecidable :
    DecidablePred ambient.IsProjective :=
  Classical.decPred _

noncomputable local instance rejectionProfileRejectedProjectiveDecidable :
    DecidablePred rejected.IsProjective :=
  Classical.decPred _

noncomputable local instance rejectionProfileDecidableEqI : DecidableEq I :=
  Classical.decEq _

noncomputable local instance rejectionProfileDecidableEqJ : DecidableEq J :=
  Classical.decEq _

/-- The removed projective vertex contributes local density `-1`. -/
theorem localDensity_deleted :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective R.deleted = -1 := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity ambient R.deleted 1
      R.deleted_arity (ambient.IsProjective R.deleted) Iff.rfl]
  simp [ARCount.localDensityOfIncomingArity, R.deleted_projective]

/-- The replacement vertex gains one unit of local density: it becomes
projective while losing one incoming occurrence. -/
theorem localDensity_surviving_replacement :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective (R.surviving R.replacement).1 =
      ARCount.localDensity (arrowMultiplicity rejected)
          rejected.IsProjective R.replacement + 1 := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity ambient
      (R.surviving R.replacement).1
      (rightMiddleArity rejected R.replacement + 1)
      R.replacement_arity.symm
      (ambient.IsProjective (R.surviving R.replacement).1) Iff.rfl,
    localDensity_eq_localDensityOfIncomingArity rejected R.replacement
      (rightMiddleArity rejected R.replacement) rfl
      (rejected.IsProjective R.replacement) Iff.rfl]
  simp [ARCount.localDensityOfIncomingArity,
    R.replacement_ambient_nonprojective,
    R.replacement_rejected_projective]
  omega

/-- Every other surviving vertex has unchanged local density. -/
theorem localDensity_surviving_of_ne
    (j : J) (hj : j ≠ R.replacement) :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective (R.surviving j).1 =
      ARCount.localDensity (arrowMultiplicity rejected)
        rejected.IsProjective j := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity ambient
      (R.surviving j).1 (rightMiddleArity rejected j)
      (R.arity_eq_of_ne j hj)
      (rejected.IsProjective j) (R.projective_iff_of_ne j hj),
    localDensity_eq_localDensityOfIncomingArity rejected j
      (rightMiddleArity rejected j) rfl
      (rejected.IsProjective j) Iff.rfl]

/-- Uniform indicator form of the local-density change on surviving
vertices. -/
theorem localDensity_surviving (j : J) :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective (R.surviving j).1 =
      ARCount.localDensity (arrowMultiplicity rejected)
          rejected.IsProjective j +
        if j = R.replacement then 1 else 0 := by
  classical
  by_cases hj : j = R.replacement
  · subst j
    simpa using R.localDensity_surviving_replacement
  · simpa [hj] using R.localDensity_surviving_of_ne j hj

/-- The projective indicator on surviving vertices gains exactly the
replacement vertex. -/
theorem projectiveIndicator_surviving (j : J) :
    (if ambient.IsProjective (R.surviving j).1 then (1 : ℤ) else 0) +
        (if j = R.replacement then 1 else 0) =
      if rejected.IsProjective j then 1 else 0 := by
  classical
  by_cases hj : j = R.replacement
  · subst j
    simp [R.replacement_ambient_nonprojective,
      R.replacement_rejected_projective]
  · have hp := R.projective_iff_of_ne j hj
    simp only [hj, if_false, add_zero]
    by_cases hpa : ambient.IsProjective (R.surviving j).1
    · simp [hpa, hp.mp hpa]
    · have hpr : ¬ rejected.IsProjective j := fun h ↦ hpa (hp.mpr h)
      simp [hpa, hpr]

include R in
/-- One rejection replaces the deleted projective by the newly projective
successor, so the number of projective vertices is unchanged. -/
theorem projectiveCount_eq :
    ARCount.projectiveCount ambient.IsProjective =
      ARCount.projectiveCount rejected.IsProjective := by
  classical
  rw [← ARCount.sum_projectiveIndicator_eq_projectiveCount,
    ← ARCount.sum_projectiveIndicator_eq_projectiveCount]
  calc
    (∑ i : I, if ambient.IsProjective i then (1 : ℤ) else 0) =
        (if ambient.IsProjective R.deleted then (1 : ℤ) else 0) +
          ∑ i : {i : I // i ≠ R.deleted},
            if ambient.IsProjective i.1 then (1 : ℤ) else 0 :=
      Fintype.sum_eq_add_sum_subtype_ne
        (fun i ↦ if ambient.IsProjective i then (1 : ℤ) else 0) R.deleted
    _ = 1 + ∑ j : J,
          (if ambient.IsProjective (R.surviving j).1 then (1 : ℤ) else 0) := by
      rw [if_pos R.deleted_projective,
        R.surviving.sum_comp
          (fun i : {i : I // i ≠ R.deleted} ↦
            if ambient.IsProjective i.1 then (1 : ℤ) else 0)]
    _ = ∑ j : J, if rejected.IsProjective j then (1 : ℤ) else 0 := by
      have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) ↦
        R.projectiveIndicator_surviving j)
      simp only [Finset.sum_add_distrib] at hsum
      have hindicator :
          (∑ j : J, if j = R.replacement then (1 : ℤ) else 0) = 1 := by
        simp
      rw [hindicator] at hsum
      omega

include R in
/-- The rejected category has exactly one fewer indecomposable label. -/
theorem vertexCount_eq_add_one :
    ARCount.vertexCount (ι := I) = ARCount.vertexCount (ι := J) + 1 := by
  classical
  change (Fintype.card I : ℤ) = (Fintype.card J : ℤ) + 1
  calc
    (Fintype.card I : ℤ) = ∑ _i : I, (1 : ℤ) := by simp
    _ = 1 + ∑ i : {i : I // i ≠ R.deleted}, (1 : ℤ) :=
      Fintype.sum_eq_add_sum_subtype_ne (fun _i : I ↦ (1 : ℤ)) R.deleted
    _ = 1 + ∑ _j : J, (1 : ℤ) := by
      rw [R.surviving.sum_comp (fun _i : {i : I // i ≠ R.deleted} ↦ (1 : ℤ))]
    _ = (Fintype.card J : ℤ) + 1 := by simp [add_comm]

include R in
/-- Exactly one almost-split mesh disappears under one rejection. -/
theorem meshCount_eq_add_one :
    ARCount.meshCount ambient.IsProjective =
      ARCount.meshCount rejected.IsProjective + 1 := by
  have hambient :=
    ARCount.vertexCount_eq_projectiveCount_add_meshCount ambient.IsProjective
  have hrejected :=
    ARCount.vertexCount_eq_projectiveCount_add_meshCount rejected.IsProjective
  have hvertex := R.vertexCount_eq_add_one
  have hprojective := R.projectiveCount_eq
  omega

include R in
/-- One Drozd--Kiričenko rejection preserves the total
Auslander--Reiten surplus. -/
theorem surplus_eq :
    ARCount.surplus (arrowMultiplicity ambient)
        ambient.IsProjective =
      ARCount.surplus (arrowMultiplicity rejected)
        rejected.IsProjective := by
  classical
  rw [← ARCount.sum_localDensity_eq_surplus,
    ← ARCount.sum_localDensity_eq_surplus]
  calc
    (∑ i : I, ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective i) =
        ARCount.localDensity (arrowMultiplicity ambient)
            ambient.IsProjective R.deleted +
          ∑ i : {i : I // i ≠ R.deleted},
            ARCount.localDensity (arrowMultiplicity ambient)
              ambient.IsProjective i.1 :=
      Fintype.sum_eq_add_sum_subtype_ne
        (fun i ↦ ARCount.localDensity (arrowMultiplicity ambient)
          ambient.IsProjective i) R.deleted
    _ = -1 + ∑ j : J,
          ARCount.localDensity (arrowMultiplicity ambient)
            ambient.IsProjective (R.surviving j).1 := by
      rw [R.localDensity_deleted,
        R.surviving.sum_comp
          (fun i : {i : I // i ≠ R.deleted} ↦
            ARCount.localDensity (arrowMultiplicity ambient)
              ambient.IsProjective i.1)]
    _ = -1 + ∑ j : J,
          (ARCount.localDensity (arrowMultiplicity rejected)
              rejected.IsProjective j +
            if j = R.replacement then 1 else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact R.localDensity_surviving j
    _ = ∑ j : J, ARCount.localDensity (arrowMultiplicity rejected)
          rejected.IsProjective j := by
      rw [Finset.sum_add_distrib]
      simp

include R in
/-- Exactly two Auslander--Reiten arrows disappear under one rejection. -/
theorem arrowCount_eq_add_two :
    ARCount.arrowCount (arrowMultiplicity ambient) =
      ARCount.arrowCount (arrowMultiplicity rejected) + 2 := by
  have hambient := ARCount.surplus_eq_two_mul_meshCount_sub_arrowCount
    (arrowMultiplicity ambient) ambient.IsProjective
  have hrejected := ARCount.surplus_eq_two_mul_meshCount_sub_arrowCount
    (arrowMultiplicity rejected) rejected.IsProjective
  have hsurplus := R.surplus_eq
  have hmesh := R.meshCount_eq_add_one
  omega

include R in
/-- Consequently one rejection preserves the Auslander--Reiten Euler
magnitude, not merely its surplus. -/
theorem eulerMagnitude_eq :
    ARCount.eulerMagnitude (arrowMultiplicity ambient)
        ambient.IsProjective =
      ARCount.eulerMagnitude (arrowMultiplicity rejected)
        rejected.IsProjective := by
  have hsurplus := R.surplus_eq
  have hprojective := R.projectiveCount_eq
  simpa [ARCount.surplus, hprojective] using hsurplus

end RejectionProfile

/-- The exact finite-tau change caused by simultaneously rejecting a finite
basic family of non-simple indecomposable projective-injectives. -/
structure FamilyRejectionProfile
    (ambient : FiniteRightTauCategoryData C I)
    (rejected : FiniteRightTauCategoryData D J) where
  /-- The removed projective-injective labels. -/
  deleted : Finset I
  /-- Each deleted label has its own surviving replacement. -/
  replacement : {i : I // i ∈ deleted} → J
  replacement_injective : Function.Injective replacement
  /-- The rejected labels are exactly the complement of the deleted family. -/
  surviving : J ≃ {i : I // i ∉ deleted}
  deleted_projective : ∀ i (hi : i ∈ deleted), ambient.IsProjective i
  deleted_arity : ∀ i (hi : i ∈ deleted), rightMiddleArity ambient i = 1
  replacement_ambient_nonprojective : ∀ d,
    ¬ ambient.IsProjective (surviving (replacement d)).1
  replacement_rejected_projective : ∀ d,
    rejected.IsProjective (replacement d)
  projective_iff_of_not_replacement : ∀ j : J,
    (∀ d, replacement d ≠ j) →
      (ambient.IsProjective (surviving j).1 ↔ rejected.IsProjective j)
  replacement_arity : ∀ d,
    rightMiddleArity rejected (replacement d) + 1 =
      rightMiddleArity ambient (surviving (replacement d)).1
  arity_eq_of_not_replacement : ∀ j : J,
    (∀ d, replacement d ≠ j) →
      rightMiddleArity ambient (surviving j).1 =
        rightMiddleArity rejected j

namespace FamilyRejectionProfile

variable
    {ambient : FiniteRightTauCategoryData C I}
    {rejected : FiniteRightTauCategoryData D J}
    (R : FamilyRejectionProfile ambient rejected)

noncomputable local instance familyRejectionProfileAmbientProjectiveDecidable :
    DecidablePred ambient.IsProjective :=
  Classical.decPred _

noncomputable local instance familyRejectionProfileRejectedProjectiveDecidable :
    DecidablePred rejected.IsProjective :=
  Classical.decPred _

noncomputable local instance familyRejectionProfileDecidableEqI : DecidableEq I :=
  Classical.decEq _

noncomputable local instance familyRejectionProfileDecidableEqJ : DecidableEq J :=
  Classical.decEq _

/-- Every deleted projective vertex contributes local density `-1`. -/
theorem localDensity_deleted (i : I) (hi : i ∈ R.deleted) :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective i = -1 := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity ambient i 1
      (R.deleted_arity i hi) (ambient.IsProjective i) Iff.rfl]
  simp [ARCount.localDensityOfIncomingArity, R.deleted_projective i hi]

/-- Every replacement gains one unit of local density. -/
theorem localDensity_surviving_replacement
    (d : {i : I // i ∈ R.deleted}) :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective (R.surviving (R.replacement d)).1 =
      ARCount.localDensity (arrowMultiplicity rejected)
          rejected.IsProjective (R.replacement d) + 1 := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity ambient
      (R.surviving (R.replacement d)).1
      (rightMiddleArity rejected (R.replacement d) + 1)
      (R.replacement_arity d).symm
      (ambient.IsProjective (R.surviving (R.replacement d)).1) Iff.rfl,
    localDensity_eq_localDensityOfIncomingArity rejected (R.replacement d)
      (rightMiddleArity rejected (R.replacement d)) rfl
      (rejected.IsProjective (R.replacement d)) Iff.rfl]
  simp [ARCount.localDensityOfIncomingArity,
    R.replacement_ambient_nonprojective d,
    R.replacement_rejected_projective d]
  omega

/-- Every surviving vertex outside the replacement family has unchanged
local density. -/
theorem localDensity_surviving_of_not_replacement
    (j : J) (hj : ∀ d, R.replacement d ≠ j) :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective (R.surviving j).1 =
      ARCount.localDensity (arrowMultiplicity rejected)
        rejected.IsProjective j := by
  classical
  rw [localDensity_eq_localDensityOfIncomingArity ambient
      (R.surviving j).1 (rightMiddleArity rejected j)
      (R.arity_eq_of_not_replacement j hj)
      (rejected.IsProjective j)
      (R.projective_iff_of_not_replacement j hj),
    localDensity_eq_localDensityOfIncomingArity rejected j
      (rightMiddleArity rejected j) rfl
      (rejected.IsProjective j) Iff.rfl]

/-- Uniform indicator form of the local-density change on surviving
vertices. -/
theorem localDensity_surviving (j : J) :
    ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective (R.surviving j).1 =
      ARCount.localDensity (arrowMultiplicity rejected)
          rejected.IsProjective j +
        if ∃ d, R.replacement d = j then 1 else 0 := by
  classical
  by_cases hj : ∃ d, R.replacement d = j
  · obtain ⟨d, hd⟩ := hj
    subst j
    simpa using R.localDensity_surviving_replacement d
  · have hj' : ∀ d, R.replacement d ≠ j := by
      intro d hd
      exact hj ⟨d, hd⟩
    simpa [hj] using R.localDensity_surviving_of_not_replacement j hj'

/-- Uniform projective-indicator change on surviving vertices. -/
theorem projectiveIndicator_surviving (j : J) :
    (if ambient.IsProjective (R.surviving j).1 then (1 : ℤ) else 0) +
        (if ∃ d, R.replacement d = j then 1 else 0) =
      if rejected.IsProjective j then 1 else 0 := by
  classical
  by_cases hj : ∃ d, R.replacement d = j
  · obtain ⟨d, hd⟩ := hj
    subst j
    simp [R.replacement_ambient_nonprojective d,
      R.replacement_rejected_projective d]
  · have hj' : ∀ d, R.replacement d ≠ j := by
      intro d hd
      exact hj ⟨d, hd⟩
    have hp := R.projective_iff_of_not_replacement j hj'
    simp only [hj, if_false, add_zero]
    by_cases hpa : ambient.IsProjective (R.surviving j).1
    · simp [hpa, hp.mp hpa]
    · have hpr : ¬ rejected.IsProjective j := fun h ↦ hpa (hp.mpr h)
      simp [hpa, hpr]

include R in
/-- The sum of replacement indicators is the size of the deleted family. -/
theorem sum_replacementIndicator :
    (∑ j : J, if ∃ d, R.replacement d = j then (1 : ℤ) else 0) =
      R.deleted.card := by
  classical
  let replacements : Finset J :=
    Finset.univ.image R.replacement
  have hindicator :
      (∑ j : J, if ∃ d, R.replacement d = j then (1 : ℤ) else 0) =
        ∑ j : J, if j ∈ replacements then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    simp [replacements, eq_comm]
  have hcard : replacements.card = R.deleted.card := by
    change (Finset.univ.image R.replacement).card = R.deleted.card
    rw [Finset.card_image_of_injective]
    · simp
    · exact R.replacement_injective
  rw [hindicator]
  simpa [hcard]

include R in
/-- Simultaneous rejection replaces all deleted projectives by the same
number of new projective replacement vertices. -/
theorem projectiveCount_eq :
    ARCount.projectiveCount ambient.IsProjective =
      ARCount.projectiveCount rejected.IsProjective := by
  classical
  letI : Fintype {i : I // i ∈ R.deleted} :=
    Subtype.fintype (fun i : I ↦ i ∈ R.deleted)
  rw [← ARCount.sum_projectiveIndicator_eq_projectiveCount,
    ← ARCount.sum_projectiveIndicator_eq_projectiveCount]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I ↦ i ∈ R.deleted)
    (fun i ↦ if ambient.IsProjective i then (1 : ℤ) else 0)
  have hdeleted :
      (∑ d : {i : I // i ∈ R.deleted},
        if ambient.IsProjective d.1 then (1 : ℤ) else 0) =
        R.deleted.card := by
    simpa [R.deleted_projective]
  calc
    (∑ i : I, if ambient.IsProjective i then (1 : ℤ) else 0) =
        (∑ d : {i : I // i ∈ R.deleted},
          if ambient.IsProjective d.1 then (1 : ℤ) else 0) +
          ∑ i : {i : I // i ∉ R.deleted},
            if ambient.IsProjective i.1 then (1 : ℤ) else 0 := hsplit.symm
    _ = R.deleted.card +
          ∑ i : {i : I // i ∉ R.deleted},
            if ambient.IsProjective i.1 then (1 : ℤ) else 0 := by
      rw [hdeleted]
    _ = R.deleted.card + ∑ j : J,
          (if ambient.IsProjective (R.surviving j).1 then (1 : ℤ) else 0) := by
      rw [R.surviving.sum_comp
        (fun i : {i : I // i ∉ R.deleted} ↦
          if ambient.IsProjective i.1 then (1 : ℤ) else 0)]
    _ = ∑ j : J, if rejected.IsProjective j then (1 : ℤ) else 0 := by
      have hsum := Finset.sum_congr rfl
        (fun j (_ : j ∈ Finset.univ) ↦ R.projectiveIndicator_surviving j)
      simp only [Finset.sum_add_distrib] at hsum
      rw [R.sum_replacementIndicator] at hsum
      omega

include R in
/-- Simultaneous rejection preserves the total Auslander--Reiten surplus. -/
theorem surplus_eq :
    ARCount.surplus (arrowMultiplicity ambient)
        ambient.IsProjective =
      ARCount.surplus (arrowMultiplicity rejected)
        rejected.IsProjective := by
  classical
  letI : Fintype {i : I // i ∈ R.deleted} :=
    Subtype.fintype (fun i : I ↦ i ∈ R.deleted)
  rw [← ARCount.sum_localDensity_eq_surplus,
    ← ARCount.sum_localDensity_eq_surplus]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I ↦ i ∈ R.deleted)
    (fun i ↦ ARCount.localDensity (arrowMultiplicity ambient)
      ambient.IsProjective i)
  have hdeleted :
      (∑ d : {i : I // i ∈ R.deleted},
        ARCount.localDensity (arrowMultiplicity ambient)
          ambient.IsProjective d.1) = -(R.deleted.card : ℤ) := by
    calc
      (∑ d : {i : I // i ∈ R.deleted},
          ARCount.localDensity (arrowMultiplicity ambient)
            ambient.IsProjective d.1) =
          ∑ _d : {i : I // i ∈ R.deleted}, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro d _
        exact R.localDensity_deleted d.1 d.2
      _ = -(R.deleted.card : ℤ) := by simp
  calc
    (∑ i : I, ARCount.localDensity (arrowMultiplicity ambient)
        ambient.IsProjective i) =
        (∑ d : {i : I // i ∈ R.deleted},
          ARCount.localDensity (arrowMultiplicity ambient)
            ambient.IsProjective d.1) +
          ∑ i : {i : I // i ∉ R.deleted},
            ARCount.localDensity (arrowMultiplicity ambient)
              ambient.IsProjective i.1 := hsplit.symm
    _ = -(R.deleted.card : ℤ) +
          ∑ i : {i : I // i ∉ R.deleted},
            ARCount.localDensity (arrowMultiplicity ambient)
              ambient.IsProjective i.1 := by
      rw [hdeleted]
    _ = -(R.deleted.card : ℤ) + ∑ j : J,
          ARCount.localDensity (arrowMultiplicity ambient)
            ambient.IsProjective (R.surviving j).1 := by
      rw [R.surviving.sum_comp
        (fun i : {i : I // i ∉ R.deleted} ↦
          ARCount.localDensity (arrowMultiplicity ambient)
            ambient.IsProjective i.1)]
    _ = -(R.deleted.card : ℤ) + ∑ j : J,
          (ARCount.localDensity (arrowMultiplicity rejected)
              rejected.IsProjective j +
            if ∃ d, R.replacement d = j then 1 else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : ∃ d, R.replacement d = j
      · simpa [h] using R.localDensity_surviving j
      · simpa [h] using R.localDensity_surviving j
    _ = ∑ j : J, ARCount.localDensity (arrowMultiplicity rejected)
          rejected.IsProjective j := by
      rw [Finset.sum_add_distrib]
      have hreplacement :
          (∑ j : J, if ∃ d, R.replacement d = j then (1 : ℤ) else 0) =
            R.deleted.card := by
        convert R.sum_replacementIndicator using 1
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : ∃ d, R.replacement d = j <;> simp [h]
      rw [hreplacement]
      omega

include R in
/-- A simultaneous finite family rejection preserves the
Auslander--Reiten Euler magnitude. -/
theorem eulerMagnitude_eq :
    ARCount.eulerMagnitude (arrowMultiplicity ambient)
        ambient.IsProjective =
      ARCount.eulerMagnitude (arrowMultiplicity rejected)
        rejected.IsProjective := by
  have hsurplus := R.surplus_eq
  have hprojective := R.projectiveCount_eq
  simpa [ARCount.surplus, hprojective] using hsurplus

end FamilyRejectionProfile

end MagnitudeConjecture.FiniteTauMatrix
