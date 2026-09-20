import MagnitudeConjecture.Graded.ModuleMapComponents

/-! # Internal grading of algebra-linear maps

The homogeneous module maps form an internal direct sum of the full Hom space.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MagnitudeConjecture.Graded.ModuleGrading

variable {k A M N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable {R : VectorGrading k A} (G : ModuleGrading (M := M) R)
variable (H : ModuleGrading (M := N) R)

/-- The subspace of algebra-linear maps of a given degree. -/
def homComponent (d : ℤ) : Submodule k (M →ₗ[A] N) where
  carrier := {f | G.Homogeneous H d f}
  zero_mem' := fun i x hx ↦ (H.component (i + d)).zero_mem
  add_mem' := fun hf hg i x hx ↦ (H.component (i + d)).add_mem (hf i x hx) (hg i x hx)
  smul_mem' := fun c f hf i x hx ↦ (H.component (i + d)).smul_mem c (hf i x hx)

variable [FiniteDimensional k M]

/-- Homogeneous projection is linear in the original module map. -/
def homProjection (d : ℤ) : (M →ₗ[A] N) →ₗ[k] (M →ₗ[A] N) where
  toFun := G.homPart H d
  map_add' := by
    intro f g
    ext x
    simp [homPart, VectorGrading.mapPart, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    ext x
    simp [homPart, VectorGrading.mapPart, Finset.smul_sum]

variable [FiniteDimensional k N]

/-- Every module map is uniquely a finite sum of homogeneous module maps. -/
theorem homComponent_isInternal : DirectSum.IsInternal (G.homComponent H) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro d
    have hker : (⨆ e, ⨆ (_ : e ≠ d), G.homComponent H e) ≤
        LinearMap.ker (G.homProjection H d) := by
      apply iSup_le
      intro e
      apply iSup_le
      intro hed f hf
      exact G.homPart_of_homogeneous_ne H hf hed
    apply Submodule.disjoint_def.mpr
    intro f hf hg
    have hzero := hker hg
    change G.homPart H d f = 0 at hzero
    rw [G.homPart_of_homogeneous H hf] at hzero
    exact hzero
  · apply top_unique
    intro f hf
    rw [← G.sum_homPart H f]
    apply Submodule.sum_mem
    intro d hd
    exact (le_iSup (G.homComponent H) d) (G.homPart_homogeneous H d f)

/-- The internal vector-space grading of the full module Hom space. -/
def homGrading : VectorGrading k (M →ₗ[A] N) where
  component := G.homComponent H
  internal := G.homComponent_isInternal H

end MagnitudeConjecture.Graded.ModuleGrading
