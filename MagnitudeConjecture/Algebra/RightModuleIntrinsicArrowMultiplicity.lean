import MagnitudeConjecture.CategoryTheory.ModuleIrreducibleSpaceComparison
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedOccurrenceBasis
import MagnitudeConjecture.Algebra.RightModulePrimitiveDeletion

/-! # Intrinsic irreducible quotients compute the official arrow multiplicity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Over an algebraically closed field the dimension of the intrinsic
categorical irreducible quotient is the literal finite-tau arrow multiplicity,
including arrows into projective vertices. -/
theorem intrinsicIrreducible_finrank_eq_arrowMultiplicity
    (source target : Fin S.n) :
    Module.finrank k (CategoricalIrreducible.Space k (S.fgObj source) (S.fgObj target)) =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target := by
  classical
  let sigma := S.almostSplitSkeleton
  let : ∀ i : Fin S.n, Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  let : ∀ i : Fin S.n, IsScalarTower k Aᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  refine (sigma.intrinsicIrreducibleEquiv (k := k) source target).finrank_eq.trans ?_
  let B := S.meshRightAlmostSplitAt target
  letI : Fintype B.index := Fintype.ofFinite _
  rw [sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
    (K := k) B source]
  rw [← S.indecomposableMultiplicity_meshRightMiddle source target,
    S.indecomposableMultiplicity_eq_of_fintype_decomposition
      source B.middle B.decomposition]
  change Nat.card {i : B.index // B.label i = source} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
