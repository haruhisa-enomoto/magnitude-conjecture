import MagnitudeConjecture.CategoryTheory.GradedIntervalReconstructedModule

/-! # Idempotents project onto their reconstructed coordinate rows -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type v} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable (horth : Pairwise fun i j ↦ e i * e j = 0)
include he0 he horth

/-- A selected idempotent has only its own diagonal interval coefficients. -/
theorem intervalCorner_idempotent (m : ℕ) (p q : ι × Fin (m + 1)) (i : ι) :
    intervalCorner R e m p q (e i) = if p = q ∧ p.1 = i then e p.1 else 0 := by
  classical
  by_cases hd : p.2 = q.2
  · have hd' : (p.2.val : ℤ) - q.2.val = 0 := by rw [hd]; omega
    simp only [intervalCorner, hd', R.projection_of_mem (he0 i)]
    by_cases hpi : p.1 = i
    · rw [hpi, he i]
      by_cases hqi : q.1 = i
      · have hpq : p = q := Prod.ext (hpi.trans hqi.symm) hd
        simp only [hpq, hqi, he i, and_self, if_true]
      · have hpq : p ≠ q := fun h ↦ hqi ((congrArg Prod.fst h).symm.trans hpi)
        rw [horth (Ne.symm hqi), if_neg (fun h ↦ hpq h.1)]
    · rw [horth hpi, zero_mul, if_neg (fun h ↦ hpi h.2)]
  · have hdeg : (0 : ℤ) ≠ (p.2.val : ℤ) - q.2.val := by
      intro h
      apply hd
      apply Fin.ext
      omega
    have hpq : p ≠ q := fun h ↦ hd (congrArg Prod.snd h)
    simp only [intervalCorner, R.projection_of_mem_ne (he0 i) hdeg, mul_zero, zero_mul,
      hpq, false_and, if_false]

/-- Off-diagonal projective morphisms of an idempotent vanish. -/
theorem intervalActionCoefficient_idempotent_ne (m : ℕ) (p q : ι × Fin (m + 1))
    (i : ι) (hpq : p ≠ q) : intervalActionCoefficient R hmul e he0 he m p q (e i) = 0 := by
  apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
  rw [map_zero]
  apply Subtype.ext
  rw [intervalActionCoefficient_coord, intervalCorner_idempotent R e he0 he horth]
  simp only [hpq, false_and, if_false, ZeroMemClass.coe_zero]

/-- The diagonal morphism is identity precisely on the selected idempotent label. -/
theorem intervalActionCoefficient_idempotent_self (m : ℕ) (p : ι × Fin (m + 1)) (i : ι) :
    intervalActionCoefficient R hmul e he0 he m p p (e i) = if p.1 = i then 𝟙 _ else 0 := by
  classical
  apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
  apply Subtype.ext
  rw [intervalActionCoefficient_coord, intervalCorner_idempotent R e he0 he horth]
  have hiff : (p = p ∧ p.1 = i) ↔ p.1 = i := ⟨And.right, fun h ↦ ⟨rfl, h⟩⟩
  simp only [hiff, true_and]
  by_cases hi : p.1 = i
  · rw [if_pos hi, if_pos hi, principalDegreeHomEquiv_id]
    rfl
  · rw [if_neg hi, if_neg hi, map_zero]
    rfl

variable (F : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k)
variable [F.Additive] [F.Linear k]

/-- A selected idempotent acts as the projection onto its labelled coordinate row. -/
theorem intervalActionMap_idempotent (m : ℕ) (i : ι)
    (x : intervalCoordinateSpace R hmul e he0 F m) (p : ι × Fin (m + 1)) :
    intervalActionMap R hmul e he0 he F m (e i) x p = if p.1 = i then x p else 0 := by
  classical
  change (∑ q, (F.map (intervalActionCoefficient R hmul e he0 he m p q (e i)).op).hom (x q)) = _
  rw [Finset.sum_eq_single p]
  · rw [intervalActionCoefficient_idempotent_self R hmul e he0 he horth]
    split_ifs with h
    · rw [op_id, F.map_id]
      rfl
    · simp only [Limits.op_zero, F.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  · intro q hq hqp
    rw [intervalActionCoefficient_idempotent_ne R hmul e he0 he horth m p q i (Ne.symm hqp)]
    simp only [Limits.op_zero, F.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  · simp

end MagnitudeConjecture.Graded.FiniteGradedModule
