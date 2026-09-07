import MagnitudeConjecture.Combinatorics.OrbitQuotientAction
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

/-!
# Finite carriers from finite orbit quotients

A finite group acting with finitely many orbits acts on a finite carrier.
Applied to the residual finite quotient `G / N`, this shows that a finite-index
subgroup orbit set is finite whenever the original `G`-orbit set is finite.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.CoveringAction

universe u v

variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X]

private def finiteOrbitCover [Finite G] :
    G × MulAction.orbitRel.Quotient G X → X :=
  fun p ↦ p.1 • Quotient.out p.2

private theorem finiteOrbitCover_surjective [Finite G] :
    Function.Surjective (finiteOrbitCover (G := G) (X := X)) := by
  intro x
  have hrel : (MulAction.orbitRel G X).r
      (Quotient.out (Quotient.mk'' x : MulAction.orbitRel.Quotient G X)) x :=
    Quotient.exact (Quotient.out_eq _)
  rw [MulAction.orbitRel_apply] at hrel
  obtain ⟨g, hg⟩ := hrel
  refine ⟨⟨g⁻¹, Quotient.mk'' x⟩, ?_⟩
  dsimp only [finiteOrbitCover]
  rw [← hg]
  simp

/-- A finite group with a finite orbit set acts on a finite carrier. -/
theorem finite_of_finite_orbitQuotient
    [Finite G] [Finite (MulAction.orbitRel.Quotient G X)] :
    Finite X :=
  Finite.of_surjective (finiteOrbitCover (G := G) (X := X))
    finiteOrbitCover_surjective

/-- If the original orbit set is finite, then the orbit set of every
finite-index normal subgroup is finite. -/
theorem finite_subgroupOrbitQuotient_of_finiteIndex
    [Finite (MulAction.orbitRel.Quotient G X)]
    (N : FiniteIndexNormalSubgroup G) :
    Finite (MulAction.orbitRel.Quotient N X) := by
  let N₀ : Subgroup G := N
  letI : MulAction (G ⧸ N₀) (MulAction.orbitRel.Quotient N₀ X) :=
    orbitQuotientMulAction N₀
  letI : Finite
      (MulAction.orbitRel.Quotient (G ⧸ N₀)
        (MulAction.orbitRel.Quotient N₀ X)) :=
    Finite.of_equiv (MulAction.orbitRel.Quotient G X)
      (orbitTowerEquiv N₀).symm
  exact finite_of_finite_orbitQuotient
    (G := G ⧸ N₀) (X := MulAction.orbitRel.Quotient N₀ X)

end MagnitudeConjecture.CoveringAction
