import MagnitudeConjecture.Algebra.RightModuleStandardFormMesh
import MagnitudeConjecture.CategoryTheory.FiniteTauBeta
import MagnitudeConjecture.CategoryTheory.FGExtRealization

/-! # Nonprojective incoming occurrences in the standard-form quiver -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance incomingCountQuiver : Quiver (Fin S.n) := S.standardFormQuiver
local instance incomingCountArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y
local instance : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
  MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ

/-- Incoming arrow occurrences with nonprojective source are exactly those
counted by the original right beta invariant, with all multiplicities retained. -/
theorem standardFormIncoming_nonprojective_card_eq_betaAt (z : Fin S.n) :
    Nat.card {a : MeshCategory.RightMeshData.IncomingArrow z // ¬ Projective (S.fgObj a.1)} =
      FiniteTauMatrix.betaAt S.finiteTauCategoryData.toFiniteRightTauCategoryData z := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  change (∑ a : (Σ y : Fin S.n, S.StandardFormArrow z y),
    if ¬ Projective (S.fgObj a.1) then 1 else 0) = _
  rw [Fintype.sum_sigma]
  unfold FiniteTauMatrix.betaAt
  apply Finset.sum_congr rfl
  intro y hy
  have hp := FiniteTauMatrix.isProjective_iff_projective_obj
    S.finiteTauCategoryData.toFiniteRightTauCategoryData y
  change S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective y ↔ Projective (S.fgObj y) at hp
  by_cases h : Projective (S.fgObj y)
  · simp [h, hp.mpr h]
  · have hn : ¬ S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective y :=
      fun hh ↦ h (hp.mp hh)
    simp [h, hn, StandardFormArrow]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
