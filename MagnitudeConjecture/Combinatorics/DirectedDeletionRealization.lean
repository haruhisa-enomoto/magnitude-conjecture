import MagnitudeConjecture.Combinatorics.TranslationSliceCount
import MagnitudeConjecture.Combinatorics.PosetSpaceSharpEquality

/-!
# Directed deletion from the direct count and graded factor positivity

This file combines the live manuscript's vertex--arrow--mesh deletion count
with the graded translation-slice proof that the factor Euler excess is
nonnegative.  The remaining representation-theoretic input is visible:
new meshes must inject into gained arrow occurrences.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.DirectedDeletion

open MagnitudeConjecture.ARCount
open MagnitudeConjecture.GradedTreeExcess

universe v w

variable {H : Type v} [Fintype H]

/-- The directed-deletion inequality after supplying the literal direct
counts and replacing abstract factor-excess nonnegativity by the graded
translation recurrence and realization bound. -/
theorem translationQuiverSurplus_difference_nonnegative_of_translationRecurrence
    (Phi : Matrix H H ℤ)
    (vA nA aA vB nB aB q a0 aH z newArrows newMeshes : ℤ)
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    (vertexCount : vA = vB + q)
    (simpleCount : nA = nB + 1)
    (ambientArrowCount : aA = a0 + aH + z)
    (quotientArrowCount : aB = a0 + newArrows)
    (factorEulerCount :
      intrinsicEulerExcess Phi = 2 * q - aH - projectives - 1)
    (newMeshCount : newMeshes = z - (projectives - 1))
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
    (realization_length_bound : projectives - 1 ≤ (L : ℤ))
    (newMeshes_le_newArrows : newMeshes ≤ newArrows) :
    0 ≤ translationQuiverSurplus vA nA aA -
      translationQuiverSurplus vB nB aB := by
  apply translationQuiverSurplus_difference_nonnegative Phi
    vA nA aA vB nB aB q a0 aH z projectives newArrows newMeshes vertexCount
      simpleCount ambientArrowCount quotientArrowCount factorEulerCount
      newMeshCount
  · exact matrixIntrinsicEulerExcess_nonnegative_of_translationRecurrence
      Phi vertices arrows tauInjectives tauProjectives projectives
      source_singleton sink_singleton firstSlice arrowStep vertexStep
      meshEulerTotal realization_length_bound
  · exact newMeshes_le_newArrows

/-- The sharp directed-deletion equality criterion under the same direct
count and graded translation hypotheses.  Equality separates into sharp
realization length and bijectivity of the new-mesh/new-arrow injection. -/
theorem translationQuiverSurplus_difference_eq_zero_iff_of_translationRecurrence
    (Phi : Matrix H H ℤ)
    (vA nA aA vB nB aB q a0 aH z newArrows newMeshes : ℤ)
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    (vertexCount : vA = vB + q)
    (simpleCount : nA = nB + 1)
    (ambientArrowCount : aA = a0 + aH + z)
    (quotientArrowCount : aB = a0 + newArrows)
    (factorEulerCount :
      intrinsicEulerExcess Phi = 2 * q - aH - projectives - 1)
    (newMeshCount : newMeshes = z - (projectives - 1))
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
    (realization_length_bound : projectives - 1 ≤ (L : ℤ))
    (newMeshes_le_newArrows : newMeshes ≤ newArrows) :
    translationQuiverSurplus vA nA aA -
          translationQuiverSurplus vB nB aB = 0 ↔
      (L : ℤ) = projectives - 1 ∧ newArrows = newMeshes := by
  have hFactorNonnegative : 0 ≤ intrinsicEulerExcess Phi :=
    matrixIntrinsicEulerExcess_nonnegative_of_translationRecurrence
      Phi vertices arrows tauInjectives tauProjectives projectives
      source_singleton sink_singleton firstSlice arrowStep vertexStep
      meshEulerTotal realization_length_bound
  rw [translationQuiverSurplus_difference_eq_deletionCost Phi
    vA nA aA vB nB aB q a0 aH z projectives newArrows newMeshes vertexCount
      simpleCount ambientArrowCount quotientArrowCount factorEulerCount
      newMeshCount,
    equality_iff_zero_factorExcess_and_equal_correction Phi newArrows newMeshes
      hFactorNonnegative newMeshes_le_newArrows,
    matrixIntrinsicEulerExcess_eq_zero_iff_of_translationRecurrence
      Phi vertices arrows tauInjectives tauProjectives projectives
      source_singleton sink_singleton firstSlice arrowStep vertexStep meshEulerTotal]

/-- Equality in the complete direct deletion count makes the poset-space
realization sharp, so every Schur realization object is one-dimensional. -/
theorem finrank_eq_one_of_translationQuiverSurplus_difference_eq_zero_of_translationRecurrence_and_posetSpace
    (Phi : Matrix H H ℤ)
    (vA nA aA vB nB aB q a0 aH z newArrows newMeshes : ℤ)
    {L : ℕ} (vertices arrows tauInjectives tauProjectives : ℕ → ℤ)
    (projectives : ℤ)
    {k T : Type w} [Field k] [PartialOrder T] [Fintype T]
    (projectives_eq : projectives = (Fintype.card T : ℤ) + 1)
    (grading : PosetSpace.PositiveGrading
      (PosetSpace.Obj k T) (PosetSpace.IsSchur k T) L)
    (vertexCount : vA = vB + q)
    (simpleCount : nA = nB + 1)
    (ambientArrowCount : aA = a0 + aH + z)
    (quotientArrowCount : aB = a0 + newArrows)
    (factorEulerCount :
      intrinsicEulerExcess Phi = 2 * q - aH - projectives - 1)
    (newMeshCount : newMeshes = z - (projectives - 1))
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
    (realization_length_bound : projectives - 1 ≤ (L : ℤ))
    (newMeshes_le_newArrows : newMeshes ≤ newArrows)
    (hzero :
      translationQuiverSurplus vA nA aA -
        translationQuiverSurplus vB nB aB = 0)
    (X : PosetSpace.Obj k T) (hX : PosetSpace.IsSchur k T X) :
    Module.finrank k X = 1 := by
  have hsharpZ : (L : ℤ) = projectives - 1 :=
    ((translationQuiverSurplus_difference_eq_zero_iff_of_translationRecurrence
      Phi vA nA aA vB nB aB q a0 aH z newArrows newMeshes
      vertices arrows tauInjectives tauProjectives projectives
      vertexCount simpleCount ambientArrowCount quotientArrowCount
      factorEulerCount newMeshCount source_singleton sink_singleton firstSlice
      arrowStep vertexStep meshEulerTotal realization_length_bound
      newMeshes_le_newArrows).mp hzero).1
  have hsharp : L = Fintype.card T := by
    rw [projectives_eq] at hsharpZ
    exact_mod_cast (by omega : (L : ℤ) = (Fintype.card T : ℤ))
  exact PosetSpace.finrank_eq_one_of_isSchur_of_positiveGrading_of_le_card
    k T grading (by omega) X hX

end MagnitudeConjecture.DirectedDeletion
