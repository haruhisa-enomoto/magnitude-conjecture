import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStages
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageSuccessorTransport
import MagnitudeConjecture.Combinatorics.CoveringAverage

/-!
# The finite quotient deletion telescope

This file specializes the numerical covering-average kernel to the ordered
finite quotient representatives used by the object-deletion stages.  The
covering degree is the literal order of `G / N`, and the equality case singles
out the first stage, whose chosen representative is the group identity.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.ObjectDeletion.FiniteQuotientRepresentatives

open scoped BigOperators

universe w

variable {G : Type w} [Group G]
variable {N : Subgroup G} [N.Normal] [Fintype (G ⧸ N)]

/-- The downstairs difference is the average of the adjacent changes in the
ordered quotient-representative deletion chain. -/
theorem downstairs_difference_eq_quotientAverage
    (R : FiniteQuotientRepresentatives N)
    (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (R.m + 1) → ℤ) (localChange : Fin R.m → ℤ)
    (localChange_eq :
      ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 =
      (Fintype.card (G ⧸ N) : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last R.m) =
      (Fintype.card (G ⧸ N) : ℤ) * finalDownstairs) :
    ((initialDownstairs - finalDownstairs : ℤ) : ℚ) =
      (1 / (Fintype.card (G ⧸ N) : ℚ)) *
        ∑ j, (localChange j : ℚ) := by
  have hCardZ : (R.m : ℤ) = (Fintype.card (G ⧸ N) : ℤ) := by
    exact_mod_cast R.m_eq_card
  have hInitial : surplusAt 0 = (R.m : ℤ) * initialDownstairs := by
    exact initial_scale.trans (by rw [hCardZ])
  have hFinal : surplusAt (Fin.last R.m) =
      (R.m : ℤ) * finalDownstairs := by
    exact final_scale.trans (by rw [hCardZ])
  have hAverage :=
    MagnitudeConjecture.CoveringAverage.downstairs_difference_eq_average_localChange
      R.positive initialDownstairs finalDownstairs surplusAt localChange
      localChange_eq hInitial hFinal
  have hCardQ : (R.m : ℚ) = (Fintype.card (G ⧸ N) : ℚ) := by
    exact_mod_cast R.m_eq_card
  exact hAverage.trans (congrArg
    (fun d : ℚ ↦ (1 / d) * ∑ j, (localChange j : ℚ)) hCardQ)

/-- Nonnegative adjacent changes imply monotonicity between the two
downstairs endpoints. -/
theorem downstairs_difference_nonnegative
    (R : FiniteQuotientRepresentatives N)
    (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (R.m + 1) → ℤ) (localChange : Fin R.m → ℤ)
    (localChange_eq :
      ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 =
      (Fintype.card (G ⧸ N) : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last R.m) =
      (Fintype.card (G ⧸ N) : ℤ) * finalDownstairs)
    (localChange_nonnegative : ∀ j, 0 ≤ localChange j) :
    0 ≤ initialDownstairs - finalDownstairs := by
  have hCardZ : (R.m : ℤ) = (Fintype.card (G ⧸ N) : ℤ) := by
    exact_mod_cast R.m_eq_card
  have hInitial : surplusAt 0 = (R.m : ℤ) * initialDownstairs := by
    exact initial_scale.trans (by rw [hCardZ])
  have hFinal : surplusAt (Fin.last R.m) =
      (R.m : ℤ) * finalDownstairs := by
    exact final_scale.trans (by rw [hCardZ])
  exact MagnitudeConjecture.CoveringAverage.downstairs_difference_nonnegative
    R.positive initialDownstairs finalDownstairs surplusAt localChange
    localChange_eq hInitial hFinal localChange_nonnegative

/-- Equality downstairs forces every adjacent local change in the chosen
representative chain to vanish. -/
theorem localChange_eq_zero_of_downstairs_eq
    (R : FiniteQuotientRepresentatives N)
    (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (R.m + 1) → ℤ) (localChange : Fin R.m → ℤ)
    (localChange_eq :
      ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 =
      (Fintype.card (G ⧸ N) : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last R.m) =
      (Fintype.card (G ⧸ N) : ℤ) * finalDownstairs)
    (localChange_nonnegative : ∀ j, 0 ≤ localChange j)
    (downstairs_eq : initialDownstairs = finalDownstairs) :
    ∀ j, localChange j = 0 := by
  have hCardZ : (R.m : ℤ) = (Fintype.card (G ⧸ N) : ℤ) := by
    exact_mod_cast R.m_eq_card
  have hInitial : surplusAt 0 = (R.m : ℤ) * initialDownstairs := by
    exact initial_scale.trans (by rw [hCardZ])
  have hFinal : surplusAt (Fin.last R.m) =
      (R.m : ℤ) * finalDownstairs := by
    exact final_scale.trans (by rw [hCardZ])
  exact MagnitudeConjecture.CoveringAverage.localChange_eq_zero_of_downstairs_eq
    initialDownstairs finalDownstairs surplusAt localChange localChange_eq
    hInitial hFinal localChange_nonnegative downstairs_eq

/-- In particular, equality makes the local change at the identity-first
stage vanish. -/
theorem localChange_first_eq_zero_of_downstairs_eq
    (R : FiniteQuotientRepresentatives N)
    (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (R.m + 1) → ℤ) (localChange : Fin R.m → ℤ)
    (localChange_eq :
      ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 =
      (Fintype.card (G ⧸ N) : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last R.m) =
      (Fintype.card (G ⧸ N) : ℤ) * finalDownstairs)
    (localChange_nonnegative : ∀ j, 0 ≤ localChange j)
    (downstairs_eq : initialDownstairs = finalDownstairs) :
    localChange R.firstIndex = 0 :=
  R.localChange_eq_zero_of_downstairs_eq initialDownstairs finalDownstairs
    surplusAt localChange localChange_eq initial_scale final_scale
    localChange_nonnegative downstairs_eq R.firstIndex

end MagnitudeConjecture.ObjectDeletion.FiniteQuotientRepresentatives

namespace MagnitudeConjecture.ObjectDeletion

open _root_.CategoryTheory
open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [CategoryTheory.Category.{v} C]
  [CategoryTheory.Preadditive C] [CategoryTheory.Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- Summing the literal local changes along all ordered quotient
representatives telescopes to the difference between the first and last
finite-orbit Auslander--Reiten surpluses. -/
theorem stageLocalChangeTotal_eq_stageFiniteOrbitSurplus_sub
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C)
    (havoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    MagnitudeConjecture.CoveringAverage.localChangeTotal
        (fun i ↦ stageLocalChange (k := k) hrep R x i) =
      stageFiniteOrbitSurplus
          (k := k) C D hC hP hI hlocal hrep N R x 0 -
        stageFiniteOrbitSurplus
          (k := k) C D hC hP hI hlocal hrep N R x (Fin.last R.m) := by
  exact MagnitudeConjecture.CoveringAverage.localChangeTotal_eq_first_sub_last
    (fun j ↦ stageFiniteOrbitSurplus
      (k := k) C D hC hP hI hlocal hrep N R x j)
    (fun j ↦ stageLocalChange (k := k) hrep R x j)
    (fun j ↦ stageLocalChange_eq_stageFiniteOrbitSurplus_sub
      (k := k) (C := C) D hC hP hI hlocal hrep N R x j (havoid j))

end MagnitudeConjecture.ObjectDeletion
