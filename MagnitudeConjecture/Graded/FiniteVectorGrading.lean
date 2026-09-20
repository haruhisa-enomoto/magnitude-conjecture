import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Finite support of an internal vector-space grading

A finite-dimensional internally graded space has only finitely many nonzero
degrees. We exhibit a support from the homogeneous supports of a finite basis,
so subsequent homogeneous map constructions use finite sums.
-/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace MagnitudeConjecture.Graded

variable (k M : Type*) [Field k] [AddCommGroup M] [Module k M]

structure VectorGrading where
  component : ℤ → Submodule k M
  internal : DirectSum.IsInternal component

namespace VectorGrading

variable {k M} (G : VectorGrading k M)

def decompose : M ≃ₗ[k] DirectSum ℤ (fun d ↦ G.component d) := by
  letI := G.internal.chooseDecomposition
  exact DirectSum.decomposeLinearEquiv G.component

def projection (d : ℤ) : M →ₗ[k] M :=
  (G.component d).subtype.comp
    ((DirectSum.component k ℤ (fun i ↦ G.component i) d).comp G.decompose.toLinearMap)

theorem projection_mem (d : ℤ) (x : M) : G.projection d x ∈ G.component d :=
  (G.decompose x d).property

theorem projection_of_mem {d : ℤ} {x : M} (hx : x ∈ G.component d) :
    G.projection d x = x := by
  letI := G.internal.chooseDecomposition
  exact DirectSum.decompose_of_mem_same G.component hx

theorem projection_of_mem_ne {d e : ℤ} {x : M} (hx : x ∈ G.component d)
    (hde : d ≠ e) : G.projection e x = 0 := by
  letI := G.internal.chooseDecomposition
  exact DirectSum.decompose_of_mem_ne G.component hx hde

variable [FiniteDimensional k M]

/-- A finite set containing the support of every vector. -/
def degreeSupport : Finset ℤ :=
  Finset.univ.biUnion fun i ↦ (G.decompose (Module.finBasis k M i)).support

theorem projection_eq_zero_outside {d : ℤ} (hd : d ∉ G.degreeSupport) :
    G.projection d = 0 := by
  apply (Module.finBasis k M).ext
  intro i
  have hdi : d ∉ (G.decompose (Module.finBasis k M i)).support := by
    intro hmem
    apply hd
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmem⟩
  have hz := DFinsupp.notMem_support_iff.mp hdi
  change (G.decompose (Module.finBasis k M i) d : M) = 0
  rw [hz]
  rfl

theorem component_eq_bot_outside {d : ℤ} (hd : d ∉ G.degreeSupport) :
    G.component d = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hp := G.projection_of_mem hx
  rw [G.projection_eq_zero_outside hd] at hp
  simpa using hp.symm

/-- The finite degree projections sum to the identity. -/
theorem sum_projection (x : M) :
    ∑ d ∈ G.degreeSupport, G.projection d x = x := by
  classical
  letI := G.internal.chooseDecomposition
  have hs : (G.decompose x).support ⊆ G.degreeSupport := by
    intro d hd
    by_contra hout
    have hz : G.decompose x d = 0 := by
      apply Subtype.ext
      change G.projection d x = 0
      rw [G.projection_eq_zero_outside hout]
      rfl
    exact (DFinsupp.mem_support_iff.mp hd) hz
  calc
    _ = ∑ d ∈ (G.decompose x).support, G.projection d x := by
      symm
      apply Finset.sum_subset hs
      intro d _ hd
      have hz := DFinsupp.notMem_support_iff.mp hd
      change (G.decompose x d : M) = 0
      rw [hz]
      rfl
    _ = x := DirectSum.sum_support_decompose G.component x

end VectorGrading

end MagnitudeConjecture.Graded
