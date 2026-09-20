import MagnitudeConjecture.Graded.IdempotentCoordinateEquiv

/-! # The algebra action in homogeneous idempotent coordinates -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.ModuleGrading
variable {k A M : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable {R : VectorGrading k A} (G : ModuleGrading (M := M) R)

/-- For a homogeneous vector, the target projection selects one coefficient of the algebra element. -/
theorem projection_smul_of_mem {t : ℤ} {x : M} (hx : x ∈ G.component t)
    (s : ℤ) (a : A) : G.projection s (a • x) = R.projection (s - t) a • x := by
  classical
  letI := R.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := R.component)
    (motive := fun a ↦ G.projection s (a • x) = R.projection (s - t) a • x)
  · simp
  · intro d a
    by_cases hd : d = s - t
    · have hs : d + t = s := by omega
      rw [R.projection_of_mem (hd ▸ a.property),
        G.toVectorGrading.projection_of_mem (hs ▸ G.smul_mem a.property hx)]
    · rw [R.projection_of_mem_ne a.property hd,
        G.toVectorGrading.projection_of_mem_ne (G.smul_mem a.property hx) (by omega)]
      simp
  · intro a b ha hb
    simp only [add_smul, map_add, ha, hb]

variable {ι ν : Type*} [Fintype ι] [Fintype ν]
variable (e : ι → A) (he : ∀ i, e i * e i = e i)
variable (he0 : ∀ i, e i ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (δ : ν → ℤ) (hδ : Function.Injective δ)
variable (hcover : ∀ d, G.component d ≠ ⊥ → ∃ q, δ q = d)

include he he0 hsum hδ hcover in
/-- The action matrix is given by homogeneous corners of the algebra. -/
theorem idempotentProjection_smul (p : ι × ν) (a : A) (x : M) :
    G.idempotentProjection (e p.1) (δ p.2) (a • x) =
      ∑ q : ι × ν, (e p.1 * R.projection (δ p.2 - δ q.2) a * e q.1) •
        G.idempotentProjection (e q.1) (δ q.2) x := by
  conv_lhs => rw [← G.sum_idempotentProjection e hsum δ hδ hcover x]
  rw [Finset.smul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hx := G.idempotentProjection_mem (e q.1) (he q.1) (he0 q.1) (δ q.2) x
  change e p.1 • G.projection (δ p.2) (a • G.idempotentProjection (e q.1) (δ q.2) x) = _
  rw [G.projection_smul_of_mem hx.1, mul_smul, mul_smul, hx.2]

end MagnitudeConjecture.Graded.ModuleGrading
