import MagnitudeConjecture.Combinatorics.DirectedDeletion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Euler excess of a category with tree slices

This file formalizes the numerical part of the factor-excess argument in the
frozen manuscript.  Suppose a graded translation quiver has levels
`0,...,L`, singleton source and sink levels, and every bipartite arrow slice
is a tree.  If `v j` is the number of vertices at level `j`, the number of
arrows in slice `j` is `v j + v (j+1) - 1`.  Summing gives

`arrows = 2 * vertices - L - 2`.

With one mesh for each nonprojective and `p` projective vertices, the intrinsic
Euler excess is therefore `L - (p - 1)`.  Positivity is reduced exactly to the
realization-theoretic bound `p - 1 ≤ L`.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.GradedTreeExcess

open MagnitudeConjecture.ARCount
open MagnitudeConjecture.DirectedDeletion

universe u

/-- Total number of graded vertices, represented in `ℤ`. -/
def vertexTotal {L : ℕ} (verticesAt : Fin (L + 1) → ℤ) : ℤ :=
  ∑ j, verticesAt j

/-- Total arrow multiplicity across adjacent graded slices. -/
def arrowTotal {L : ℕ} (arrowsAt : Fin L → ℤ) : ℤ :=
  ∑ j, arrowsAt j

/-- Summing the tree edge formula over all slices. -/
theorem arrowTotal_eq_two_mul_vertexTotal_sub_length_sub_two
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1) :
    arrowTotal arrowsAt =
      2 * vertexTotal verticesAt - (L : ℤ) - 2 := by
  have hCast := Fin.sum_univ_castSucc verticesAt
  have hSucc := Fin.sum_univ_succ verticesAt
  rw [vertexTotal]
  rw [arrowTotal]
  simp_rw [slice_tree_edges]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  omega

/-- Euler expression with one mesh for each of the `vertices - projectives`
nonprojective vertices, followed by the `-1` normalization in the intrinsic
factor excess. -/
def intrinsicExcessFromCounts
    (vertices arrows projectives : ℤ) : ℤ :=
  vertices - arrows + (vertices - projectives) - 1

/-- The tree-slice count identifies intrinsic excess with the difference
between grading length and the number of non-root projectives. -/
theorem intrinsicExcessFromCounts_eq_length_sub_projectives_sub_one
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ) (projectives : ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1) :
    intrinsicExcessFromCounts
        (vertexTotal verticesAt) (arrowTotal arrowsAt) projectives =
      (L : ℤ) - (projectives - 1) := by
  rw [arrowTotal_eq_two_mul_vertexTotal_sub_length_sub_two
    verticesAt arrowsAt source_singleton sink_singleton slice_tree_edges]
  simp only [intrinsicExcessFromCounts]
  ring

/-- The realization bound `projectives - 1 ≤ L` is precisely what makes the
intrinsic factor excess nonnegative. -/
theorem intrinsicExcessFromCounts_nonnegative
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ) (projectives : ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1)
    (realization_length_bound : projectives - 1 ≤ (L : ℤ)) :
    0 ≤ intrinsicExcessFromCounts
      (vertexTotal verticesAt) (arrowTotal arrowsAt) projectives := by
  rw [intrinsicExcessFromCounts_eq_length_sub_projectives_sub_one
    verticesAt arrowsAt projectives source_singleton sink_singleton
      slice_tree_edges]
  omega

/-- Under the tree-slice hypotheses, vanishing of the factor excess is
equivalent to sharpness of the realization length bound. -/
theorem intrinsicExcessFromCounts_eq_zero_iff
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ) (projectives : ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1) :
    intrinsicExcessFromCounts
        (vertexTotal verticesAt) (arrowTotal arrowsAt) projectives = 0 ↔
      (L : ℤ) = projectives - 1 := by
  rw [intrinsicExcessFromCounts_eq_length_sub_projectives_sub_one
    verticesAt arrowsAt projectives source_singleton sink_singleton
      slice_tree_edges]
  omega

/-- The strengthened bound `projectives ≤ L`, supplied in the manuscript by a
thick indecomposable poset-space, makes the intrinsic excess strictly positive.
-/
theorem intrinsicExcessFromCounts_pos
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ) (projectives : ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1)
    (thick_length_bound : projectives ≤ (L : ℤ)) :
    0 < intrinsicExcessFromCounts
      (vertexTotal verticesAt) (arrowTotal arrowsAt) projectives := by
  rw [intrinsicExcessFromCounts_eq_length_sub_projectives_sub_one
    verticesAt arrowsAt projectives source_singleton sink_singleton
      slice_tree_edges]
  omega

/-- Bridge from the graded count to the matrix-defined intrinsic factor
excess used by directed deletion. -/
theorem matrixIntrinsicEulerExcess_eq_length_sub_projectives_sub_one
    {ι : Type u} [Fintype ι] (Phi : Matrix ι ι ℤ)
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ) (projectives : ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1)
    (meshEulerTotal :
      matrixTotal Phi =
        vertexTotal verticesAt - arrowTotal arrowsAt +
          (vertexTotal verticesAt - projectives)) :
    intrinsicEulerExcess Phi = (L : ℤ) - (projectives - 1) := by
  rw [intrinsicEulerExcess, meshEulerTotal]
  exact intrinsicExcessFromCounts_eq_length_sub_projectives_sub_one
    verticesAt arrowsAt projectives source_singleton sink_singleton
      slice_tree_edges

/-- Matrix form of nonnegative intrinsic factor excess. -/
theorem matrixIntrinsicEulerExcess_nonnegative
    {ι : Type u} [Fintype ι] (Phi : Matrix ι ι ℤ)
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ) (projectives : ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1)
    (meshEulerTotal :
      matrixTotal Phi =
        vertexTotal verticesAt - arrowTotal arrowsAt +
          (vertexTotal verticesAt - projectives))
    (realization_length_bound : projectives - 1 ≤ (L : ℤ)) :
    0 ≤ intrinsicEulerExcess Phi := by
  rw [matrixIntrinsicEulerExcess_eq_length_sub_projectives_sub_one
    Phi verticesAt arrowsAt projectives source_singleton sink_singleton
      slice_tree_edges meshEulerTotal]
  omega

/-- Matrix form of the sharp equality criterion for the length bound. -/
theorem matrixIntrinsicEulerExcess_eq_zero_iff
    {ι : Type u} [Fintype ι] (Phi : Matrix ι ι ℤ)
    {L : ℕ} (verticesAt : Fin (L + 1) → ℤ)
    (arrowsAt : Fin L → ℤ) (projectives : ℤ)
    (source_singleton : verticesAt 0 = 1)
    (sink_singleton : verticesAt (Fin.last L) = 1)
    (slice_tree_edges :
      ∀ j : Fin L,
        arrowsAt j =
          verticesAt j.castSucc + verticesAt j.succ - 1)
    (meshEulerTotal :
      matrixTotal Phi =
        vertexTotal verticesAt - arrowTotal arrowsAt +
          (vertexTotal verticesAt - projectives)) :
    intrinsicEulerExcess Phi = 0 ↔
      (L : ℤ) = projectives - 1 := by
  rw [matrixIntrinsicEulerExcess_eq_length_sub_projectives_sub_one
    Phi verticesAt arrowsAt projectives source_singleton sink_singleton
      slice_tree_edges meshEulerTotal]
  omega

end MagnitudeConjecture.GradedTreeExcess
