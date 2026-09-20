import MagnitudeConjecture.Graded.ModuleMapComponents

/-! # Direct sums with shifted gradings -/

set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M]
variable [AddCommGroup N] [Module k N]
variable [FiniteDimensional k M] [FiniteDimensional k N]

namespace VectorGrading
variable (G : VectorGrading k M) (H : VectorGrading k N) (s t : ℤ)

/-- The componentwise product with degree offsets `s` and `t`. -/
def shiftedProduct : VectorGrading k (M × N) where
  component d := (G.component (d - s)).prod (H.component (d - t))
  internal := by
    let C := fun d ↦ (G.component (d - s)).prod (H.component (d - t))
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro d
      let p : (M × N) →ₗ[k] (M × N) :=
        (G.projection (d - s)).prodMap (H.projection (d - t))
      have hk : (⨆ e, ⨆ (_ : e ≠ d), C e) ≤ p.ker := by
        apply iSup_le
        intro e
        apply iSup_le
        intro hed x hx
        change (G.projection (d-s) x.1, H.projection (d-t) x.2) = 0
        exact Prod.ext (G.projection_of_mem_ne hx.1 (by omega))
          (H.projection_of_mem_ne hx.2 (by omega))
      apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hz := hk hy
      change (G.projection (d-s) x.1, H.projection (d-t) x.2) = 0 at hz
      rw [G.projection_of_mem hx.1, H.projection_of_mem hx.2] at hz
      exact hz
    · apply top_unique
      intro x hx
      have hleft : (x.1, (0 : N)) ∈ ⨆ d, C d := by
        have heq : (x.1, (0 : N)) = ∑ d ∈ G.degreeSupport, (G.projection d x.1, (0 : N)) := by
          apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum, G.sum_projection]
        rw [heq]
        apply Submodule.sum_mem
        intro d hd
        apply (le_iSup C (d + s))
        exact ⟨by simpa using G.projection_mem d x.1, (H.component _).zero_mem⟩
      have hright : ((0 : M), x.2) ∈ ⨆ d, C d := by
        have heq : ((0 : M), x.2) = ∑ d ∈ H.degreeSupport, ((0 : M), H.projection d x.2) := by
          apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum, H.sum_projection]
        rw [heq]
        apply Submodule.sum_mem
        intro d hd
        apply (le_iSup C (d + t))
        exact ⟨(G.component _).zero_mem, by simpa using H.projection_mem d x.2⟩
      simpa using (⨆ d, C d).add_mem hleft hright

end VectorGrading

variable {A : Type*} [Ring A] [Algebra k A]
variable [Module A M] [IsScalarTower k A M] [Module A N] [IsScalarTower k A N]
variable {R : VectorGrading k A}

/-- Shifted products retain the graded algebra action. -/
def ModuleGrading.shiftedProduct (G : ModuleGrading (M := M) R)
    (H : ModuleGrading (M := N) R) (s t : ℤ) : ModuleGrading (M := M × N) R where
  toVectorGrading := G.toVectorGrading.shiftedProduct H.toVectorGrading s t
  smul_mem := by
    intro i j a x ha hx
    constructor
    · change a • x.1 ∈ G.component (i + j - s)
      simpa only [add_sub_assoc] using G.smul_mem ha hx.1
    · change a • x.2 ∈ H.component (i + j - t)
      simpa only [add_sub_assoc] using H.smul_mem ha hx.2

end MagnitudeConjecture.Graded
