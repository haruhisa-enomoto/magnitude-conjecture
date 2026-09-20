import MagnitudeConjecture.Graded.FiniteVectorGrading

/-! # Summing projections over an injective finite cover of the nonzero degrees -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.VectorGrading
variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
variable (G : VectorGrading k M)
variable {ν : Type*} [Fintype ν] (δ : ν → ℤ) (hδ : Function.Injective δ)
variable (hcover : ∀ d, G.component d ≠ ⊥ → ∃ q, δ q = d)

include hδ hcover in
/-- Only the nonzero degrees need to be covered, so extra zero coordinates cause no difficulty. -/
theorem sum_projection_of_cover (x : M) : ∑ q, G.projection (δ q) x = x := by
  classical
  letI := G.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component)
    (motive := fun x ↦ ∑ q, G.projection (δ q) x = x)
  · simp
  · intro d x
    by_cases hx : x.val = 0
    · simp [hx]
    · have hd : G.component d ≠ ⊥ := by
        intro hd
        exact hx (hd.le x.property)
      obtain ⟨q, hq⟩ := hcover d hd
      rw [Finset.sum_eq_single q, hq, G.projection_of_mem x.property]
      · intro q' hq' hne
        exact G.projection_of_mem_ne x.property (fun h ↦ hne (hδ (h.symm.trans hq.symm)))
      · simp
  · intro x y hx hy
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

end MagnitudeConjecture.Graded.VectorGrading
