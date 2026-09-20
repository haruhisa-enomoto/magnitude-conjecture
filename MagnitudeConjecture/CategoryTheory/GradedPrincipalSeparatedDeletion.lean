import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalDeletion
import MagnitudeConjecture.Combinatorics.SeparatedIntervals

/-! # Deleting gaps between separated principal-projective intervals -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥)

include he hneg hupper in
/-- A nonzero map between shifted principal projectives decreases degree
by an amount between zero and the grading bound. -/
theorem principalDegree_bounds {p q : PrincipalDegreeCategory R hmul e he0}
    (f : p ⟶ q) (hf : f ≠ 0) : q.2 ≤ p.2 ∧ p.2 - q.2 ≤ h := by
  refine ⟨principalDegree_nonincreasing R hmul e he0 he hneg f hf, ?_⟩
  by_contra hn
  apply hf
  apply (principalDegreeHomEquiv R hmul e he0 he p q).injective
  apply Subtype.ext
  rw [map_zero]
  have hm := (principalDegreeHomEquiv R hmul e he0 he p q f).property.1
  rw [hupper (p.2 - q.2) (by omega)] at hm
  exact hm

include he hneg hupper in
/-- Morphisms between distinct separated blocks are zero. -/
theorem principalDegree_hom_eq_zero_of_separated
    (r : ℕ) {i j : ℕ} (hij : i ≠ j)
    {p q : PrincipalDegreeCategory R hmul e he0}
    (hp : GradedInterval.InBlock r h i p.2)
    (hq : GradedInterval.InBlock r h j q.2) (f : p ⟶ q) : f = 0 := by
  by_contra hf
  have hd := principalDegree_bounds R hmul e he0 he hneg h hupper f hf
  apply hij
  apply GradedInterval.block_index_eq_of_close r h hp hq
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hd.1)]
  exact hd.2

/-- Deleted objects are precisely the degrees outside the retained blocks. -/
def principalSeparatedDeleted (r q : ℕ) :
    Set (PrincipalDegreeCategory R hmul e he0)ᵒᵖ :=
  {X | ¬ GradedInterval.Retained r h q X.unop.2}

include he hneg hupper in
/-- A nonzero composite with retained endpoints cannot pass through a gap
or outside the retained block range. -/
theorem principalSeparated_noDeletedFactorization (r q : ℕ) :
    ObjectDeletion.NoDeletedFactorization (PrincipalDegreeCategory R hmul e he0)ᵒᵖ
      (principalSeparatedDeleted R hmul e he0 h r q) := by
  intro X Y Z hX hY hZ a b
  by_contra hab
  have ha : a.unop ≠ 0 := by
    intro hz
    have hz' : a = 0 := Quiver.Hom.unop_inj hz
    exact hab (by simp [hz'])
  have hb : b.unop ≠ 0 := by
    intro hz
    have hz' : b = 0 := Quiver.Hom.unop_inj hz
    exact hab (by simp [hz'])
  have hc : (a ≫ b).unop ≠ 0 := by
    intro hz
    exact hab (Quiver.Hom.unop_inj hz)
  have hda := principalDegree_nonincreasing R hmul e he0 he hneg a.unop ha
  have hdb := principalDegree_nonincreasing R hmul e he0 he hneg b.unop hb
  have hdc := principalDegree_bounds R hmul e he0 he hneg h hupper (a ≫ b).unop hc
  change ¬ ¬ GradedInterval.Retained r h q X.unop.2 at hX
  change ¬ ¬ GradedInterval.Retained r h q Y.unop.2 at hY
  change ¬ GradedInterval.Retained r h q Z.unop.2 at hZ
  apply hZ
  apply GradedInterval.retained_of_between_close r h q (not_not.mp hX) (not_not.mp hY)
    _ hda hdb
  rw [abs_of_nonneg (sub_nonneg.mpr hdc.1)]
  exact hdc.2

/-- The gap deletion inside a finite ambient interval. -/
def principalIntervalSeparatedDeleted (m r q : ℕ) :
    Set (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ :=
  {X | ¬ GradedInterval.Retained r h q (X.unop.2.val : ℤ)}

include he hneg hupper in
/-- The finite interval deletion ideal vanishes between retained objects. -/
theorem principalIntervalSeparated_noDeletedFactorization (m r q : ℕ) :
    ObjectDeletion.NoDeletedFactorization (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ
      (principalIntervalSeparatedDeleted R hmul e he0 h m r q) := by
  intro X Y Z hX hY hZ a b
  have hs := principalSeparated_noDeletedFactorization R hmul e he0 he hneg h hupper r q
    (X := op (intervalProjectiveLabel R hmul e he0 m X.unop))
    (Y := op (intervalProjectiveLabel R hmul e he0 m Y.unop))
    (Z := op (intervalProjectiveLabel R hmul e he0 m Z.unop))
    hX hY hZ a.unop.hom.op b.unop.hom.op
  apply Quiver.Hom.unop_inj
  apply InducedCategory.hom_ext
  exact congrArg Quiver.Hom.unop hs

/-- On the retained separated blocks, the literal finite deletion category
is equivalent to the full subcategory: quotienting introduces no new Hom
relations inside those blocks. -/
def principalIntervalSeparatedDeletionEquivalence (m r q : ℕ) :
    ObjectDeletion.SurvivingCategory (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ
        (principalIntervalSeparatedDeleted R hmul e he0 h m r q) ≌
      ObjectDeletion.DeletionCategory (k := k) (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ
        (principalIntervalSeparatedDeleted R hmul e he0 h m r q) :=
  ObjectDeletion.survivingDeletionEquivalence (k := k) _ _
    (principalIntervalSeparated_noDeletedFactorization R hmul e he0 he hneg h hupper m r q)

end MagnitudeConjecture.Graded.FiniteGradedModule
