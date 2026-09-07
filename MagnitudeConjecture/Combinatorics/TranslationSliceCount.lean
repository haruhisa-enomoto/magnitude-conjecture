import MagnitudeConjecture.Combinatorics.GradedTreeExcess
import MagnitudeConjecture.Combinatorics.PosetSpaceSharpEquality

/-!
# Translation recurrence for graded slice counts

The frozen manuscript proves that every adjacent level slice in the finite
strict tau-factor has the edge count of a tree.  Its induction has a purely
numerical core: remove the tau-injective leaves from one slice, translate the
remaining arrows, and attach the new tau-projective leaves in the next slice.

This file proves that the corresponding arrow and vertex recurrences propagate
the tree edge formula.  It then feeds that formula into the intrinsic Euler
excess theorems.  Establishing the two recurrences from an actual translation
quiver remains a separate categorical obligation.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.GradedTreeExcess

open MagnitudeConjecture.ARCount
open MagnitudeConjecture.DirectedDeletion

universe u w

/-- The pruning/translation/attachment recurrence propagates the tree edge
count from the first slice to every slice below `L`. -/
theorem sliceEdgeCount_of_translationRecurrence
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2)) :
    ∀ j, j < L → arrows j = vertices j + vertices (j + 1) - 1 := by
  intro j hj
  induction j with
  | zero => exact firstSlice
  | succ j ih =>
      have hj_lt : j < L := Nat.lt_trans (Nat.lt_succ_self j) hj
      rw [arrowStep j hj, ih hj_lt, vertexStep j hj]
      ring

/-- Finite-level form of the propagated slice edge count. -/
theorem finiteSliceEdgeCount_of_translationRecurrence
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2)) :
    ∀ j : Fin L,
      arrows j.val = vertices j.castSucc.val + vertices j.succ.val - 1 := by
  intro j
  simpa using sliceEdgeCount_of_translationRecurrence vertices arrows
    tauInjectives tauProjectives firstSlice arrowStep vertexStep j.val j.isLt

/-- The translation recurrence gives the manuscript's total arrow count. -/
theorem arrowTotal_eq_of_translationRecurrence
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (source_singleton : vertices 0 = 1)
    (sink_singleton : vertices L = 1)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2)) :
    arrowTotal (fun j : Fin L ↦ arrows j.val) =
      2 * vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) - (L : ℤ) - 2 := by
  apply arrowTotal_eq_two_mul_vertexTotal_sub_length_sub_two
  · simpa using source_singleton
  · simpa using sink_singleton
  · exact finiteSliceEdgeCount_of_translationRecurrence vertices arrows
      tauInjectives tauProjectives firstSlice arrowStep vertexStep

/-- Under the translation recurrence, the intrinsic factor excess is the
grading length minus the number of non-root projectives. -/
theorem intrinsicExcessFromCounts_eq_of_translationRecurrence
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    (source_singleton : vertices 0 = 1)
    (sink_singleton : vertices L = 1)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2)) :
    intrinsicExcessFromCounts
        (vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val))
        (arrowTotal (fun j : Fin L ↦ arrows j.val)) projectives =
      (L : ℤ) - (projectives - 1) := by
  apply intrinsicExcessFromCounts_eq_length_sub_projectives_sub_one
  · simpa using source_singleton
  · simpa using sink_singleton
  · exact finiteSliceEdgeCount_of_translationRecurrence vertices arrows
      tauInjectives tauProjectives firstSlice arrowStep vertexStep

/-- Matrix form: the translation recurrence and realization-length bound
discharge the intrinsic nonnegativity hypothesis of directed deletion. -/
theorem matrixIntrinsicEulerExcess_nonnegative_of_translationRecurrence
    {ι : Type u} [Fintype ι] (Phi : Matrix ι ι ℤ)
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    (source_singleton : vertices 0 = 1)
    (sink_singleton : vertices L = 1)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2))
    (meshEulerTotal :
      matrixTotal Phi =
        vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) -
          arrowTotal (fun j : Fin L ↦ arrows j.val) +
            (vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) - projectives))
    (realization_length_bound : projectives - 1 ≤ (L : ℤ)) :
    0 ≤ intrinsicEulerExcess Phi := by
  apply matrixIntrinsicEulerExcess_nonnegative Phi
    (fun j : Fin (L + 1) ↦ vertices j.val)
    (fun j : Fin L ↦ arrows j.val) projectives
  · simpa using source_singleton
  · simpa using sink_singleton
  · exact finiteSliceEdgeCount_of_translationRecurrence vertices arrows
      tauInjectives tauProjectives firstSlice arrowStep vertexStep
  · exact meshEulerTotal
  · exact realization_length_bound

/-- Matrix equality criterion under the translation recurrence. -/
theorem matrixIntrinsicEulerExcess_eq_zero_iff_of_translationRecurrence
    {ι : Type u} [Fintype ι] (Phi : Matrix ι ι ℤ)
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    (source_singleton : vertices 0 = 1)
    (sink_singleton : vertices L = 1)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2))
    (meshEulerTotal :
      matrixTotal Phi =
        vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) -
          arrowTotal (fun j : Fin L ↦ arrows j.val) +
            (vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) - projectives)) :
    intrinsicEulerExcess Phi = 0 ↔ (L : ℤ) = projectives - 1 := by
  apply matrixIntrinsicEulerExcess_eq_zero_iff Phi
    (fun j : Fin (L + 1) ↦ vertices j.val)
    (fun j : Fin L ↦ arrows j.val) projectives
  · simpa using source_singleton
  · simpa using sink_singleton
  · exact finiteSliceEdgeCount_of_translationRecurrence vertices arrows
      tauInjectives tauProjectives firstSlice arrowStep vertexStep
  · exact meshEulerTotal

/-- The poset-space realization and its positive grading construct the
realization-length bound, so the translation recurrence alone then gives
nonnegative intrinsic factor excess. -/
theorem matrixIntrinsicEulerExcess_nonnegative_of_translationRecurrence_and_posetSpace
    {ι : Type u} [Fintype ι] (Phi : Matrix ι ι ℤ)
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    {k T : Type w} [Field k] [PartialOrder T] [Fintype T]
    (projectives_eq : projectives = (Fintype.card T : ℤ) + 1)
    (grading : PosetSpace.PositiveGrading
      (PosetSpace.Obj k T) (PosetSpace.IsSchur k T) L)
    (source_singleton : vertices 0 = 1)
    (sink_singleton : vertices L = 1)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2))
    (meshEulerTotal :
      matrixTotal Phi =
        vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) -
          arrowTotal (fun j : Fin L ↦ arrows j.val) +
            (vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) - projectives)) :
    0 ≤ intrinsicEulerExcess Phi := by
  have hcard : Fintype.card T ≤ L :=
    PosetSpace.card_le_of_schurPositiveGrading k T grading
  have hcardZ : (Fintype.card T : ℤ) ≤ (L : ℤ) := by
    exact_mod_cast hcard
  apply matrixIntrinsicEulerExcess_nonnegative_of_translationRecurrence
    Phi vertices arrows tauInjectives tauProjectives projectives
    source_singleton sink_singleton firstSlice arrowStep vertexStep
    meshEulerTotal
  rw [projectives_eq]
  omega

/-- Vanishing intrinsic excess makes the realization bound sharp and hence
forces every Schur poset space to be one-dimensional. -/
theorem finrank_eq_one_of_matrixIntrinsicEulerExcess_eq_zero_of_translationRecurrence_and_posetSpace
    {ι : Type u} [Fintype ι] (Phi : Matrix ι ι ℤ)
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    {k T : Type w} [Field k] [PartialOrder T] [Fintype T]
    (projectives_eq : projectives = (Fintype.card T : ℤ) + 1)
    (grading : PosetSpace.PositiveGrading
      (PosetSpace.Obj k T) (PosetSpace.IsSchur k T) L)
    (source_singleton : vertices 0 = 1)
    (sink_singleton : vertices L = 1)
    (firstSlice : arrows 0 = vertices 0 + vertices 1 - 1)
    (arrowStep : ∀ j, j + 1 < L →
      arrows (j + 1) =
        arrows j - tauInjectives j + tauProjectives (j + 2))
    (vertexStep : ∀ j, j + 1 < L →
      vertices (j + 2) =
        vertices j - tauInjectives j + tauProjectives (j + 2))
    (meshEulerTotal :
      matrixTotal Phi =
        vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) -
          arrowTotal (fun j : Fin L ↦ arrows j.val) +
            (vertexTotal (fun j : Fin (L + 1) ↦ vertices j.val) - projectives))
    (hzero : intrinsicEulerExcess Phi = 0)
    (X : PosetSpace.Obj k T) (hX : PosetSpace.IsSchur k T X) :
    Module.finrank k X = 1 := by
  have hsharpZ : (L : ℤ) = projectives - 1 :=
    (matrixIntrinsicEulerExcess_eq_zero_iff_of_translationRecurrence
      Phi vertices arrows tauInjectives tauProjectives projectives
      source_singleton sink_singleton firstSlice arrowStep vertexStep
      meshEulerTotal).mp hzero
  have hsharp : L = Fintype.card T := by
    rw [projectives_eq] at hsharpZ
    exact_mod_cast (by omega : (L : ℤ) = (Fintype.card T : ℤ))
  exact PosetSpace.finrank_eq_one_of_isSchur_of_positiveGrading_of_le_card
    k T grading (by omega) X hX

end MagnitudeConjecture.GradedTreeExcess
