import MagnitudeConjecture.Combinatorics.MeshMatrix

/-!
# Numerical kernel of directed primitive deletion

This file formalizes the live manuscript's direct vertex--arrow--mesh count.
If `q` vertices are deleted, `aH` arrows have both endpoints in the deleted
part, `z` arrows cross the boundary, `p` objects of the deleted factor are
tau-projective, `newArrows` arrows are gained downstairs, and `newMeshes`
meshes are new downstairs, then

```text
epsilon = 2*q - aH - p - 1,
newMeshes = z - (p - 1),
sigma(A) - sigma(B) = epsilon + newArrows - newMeshes.
```

No block inverse or Schur complement enters this count.  Nonnegativity is
exposed as the two representation-theoretic obligations `0 ≤ epsilon` and
`newMeshes ≤ newArrows`.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.DirectedDeletion

open MagnitudeConjecture.ARCount

universe v

variable {H : Type v} [Fintype H]

/-- Intrinsic Euler excess of the finite strict tau-factor. -/
def intrinsicEulerExcess (Phi : Matrix H H ℤ) : ℤ :=
  matrixTotal Phi - 1

/-- The directed-deletion correction in the live manuscript. -/
def deletionCost (Phi : Matrix H H ℤ) (newArrows newMeshes : ℤ) : ℤ :=
  intrinsicEulerExcess Phi + newArrows - newMeshes

/-- Surplus expressed using the vertex, simple, and arrow counts of a finite
Auslander--Reiten translation quiver. -/
def translationQuiverSurplus (vertices simples arrows : ℤ) : ℤ :=
  2 * (vertices - simples) - arrows

/-- The usual Auslander--Reiten surplus is the translation-quiver surplus
formed from its literal vertex, projective, and arrow counts. -/
theorem surplus_eq_translationQuiverSurplus
    (arrowMultiplicity : H → H → ℕ)
    (IsProjective : H → Prop) [DecidablePred IsProjective] :
    surplus arrowMultiplicity IsProjective =
      translationQuiverSurplus
        (vertexCount (ι := H))
        (projectiveCount IsProjective)
        (arrowCount arrowMultiplicity) := by
  rw [surplus, eulerMagnitude, translationQuiverSurplus,
    vertexCount_eq_projectiveCount_add_meshCount IsProjective]
  ring

/-- The live manuscript's direct deletion identity.  The hypotheses are the
literal vertex, simple, ambient-arrow, quotient-arrow, factor-Euler, and
crossing-mesh counts appearing in the proof. -/
theorem translationQuiverSurplus_difference_eq_deletionCost
    (Phi : Matrix H H ℤ)
    (vA nA aA vB nB aB q a0 aH z p newArrows newMeshes : ℤ)
    (vertexCount : vA = vB + q)
    (simpleCount : nA = nB + 1)
    (ambientArrowCount : aA = a0 + aH + z)
    (quotientArrowCount : aB = a0 + newArrows)
    (factorEulerCount : intrinsicEulerExcess Phi = 2 * q - aH - p - 1)
    (newMeshCount : newMeshes = z - (p - 1)) :
    translationQuiverSurplus vA nA aA -
        translationQuiverSurplus vB nB aB =
      deletionCost Phi newArrows newMeshes := by
  rw [translationQuiverSurplus, translationQuiverSurplus, deletionCost,
    factorEulerCount]
  omega

/-- The directed deletion is monotone once the factor Euler excess is
nonnegative and new meshes inject into gained arrow occurrences. -/
theorem translationQuiverSurplus_difference_nonnegative
    (Phi : Matrix H H ℤ)
    (vA nA aA vB nB aB q a0 aH z p newArrows newMeshes : ℤ)
    (vertexCount : vA = vB + q)
    (simpleCount : nA = nB + 1)
    (ambientArrowCount : aA = a0 + aH + z)
    (quotientArrowCount : aB = a0 + newArrows)
    (factorEulerCount : intrinsicEulerExcess Phi = 2 * q - aH - p - 1)
    (newMeshCount : newMeshes = z - (p - 1))
    (factorExcess_nonnegative : 0 ≤ intrinsicEulerExcess Phi)
    (newMeshes_le_newArrows : newMeshes ≤ newArrows) :
    0 ≤ translationQuiverSurplus vA nA aA -
      translationQuiverSurplus vB nB aB := by
  rw [translationQuiverSurplus_difference_eq_deletionCost Phi
    vA nA aA vB nB aB q a0 aH z p newArrows newMeshes vertexCount
      simpleCount ambientArrowCount quotientArrowCount factorEulerCount
      newMeshCount]
  simp only [deletionCost]
  omega

/-- Equality in a directed deletion forces both nonnegative contributions to
vanish separately. -/
theorem equality_iff_zero_factorExcess_and_equal_correction
    (Phi : Matrix H H ℤ) (newArrows newMeshes : ℤ)
    (factorExcess_nonnegative : 0 ≤ intrinsicEulerExcess Phi)
    (newMeshes_le_newArrows : newMeshes ≤ newArrows) :
    deletionCost Phi newArrows newMeshes = 0 ↔
      intrinsicEulerExcess Phi = 0 ∧ newArrows = newMeshes := by
  simp only [deletionCost]
  constructor
  · intro h
    constructor <;> omega
  · rintro ⟨hFactor, hCorrection⟩
    omega

end MagnitudeConjecture.DirectedDeletion
