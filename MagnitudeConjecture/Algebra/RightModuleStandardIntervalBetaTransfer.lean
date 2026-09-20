import MagnitudeConjecture.Algebra.RightModuleStandardIntervalIncomingDecomposition
import MagnitudeConjecture.Algebra.RightModuleStandardIncomingCount
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteTauBetaDisplayed

/-! # One-sided beta transfer to the single control interval -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance intervalBetaQuiver : Quiver (Fin S.n) := S.standardFormQuiver
local instance intervalBetaArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y
local instance intervalBetaBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
local instance intervalBetaFinite (m : ℕ) : FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalBetaNoetherian (m : ℕ) : IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _
local instance intervalBetaEnoughProjectives (m : ℕ) :
    EnoughProjectives (FGModuleCat.{u} (S.standardFormIntervalAlgebra m)ᵐᵒᵖ) :=
  MagnitudeConjecture.fgModuleCat_enoughProjectives _
local instance : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
  MagnitudeConjecture.fgModuleCat_enoughProjectives _
attribute [local irreducible] standardFormIntervalAlgebraEquivalence standardFormIntervalSkeleton

/-- Each original nonprojective endpoint's beta count is bounded by the
single interval's beta, using the actual graded incoming sequence. -/
theorem standardFormInterval_betaAt_le (z : Fin S.n) (hz : ¬ Projective (S.fgObj z)) :
    FiniteTauMatrix.betaAt S.finiteTauCategoryData.toFiniteRightTauCategoryData z ≤
      FiniteTauMatrix.beta
        (Ind := Fin (S.standardFormIntervalSkeleton (S.standardFormIntervalControlHeight + 2)).n)
        (S.standardFormIntervalSkeleton (S.standardFormIntervalControlHeight + 2)).finiteTauCategoryData.toFiniteRightTauCategoryData := by
  let m := S.standardFormIntervalControlHeight + 2
  let T := (S.standardFormIntervalSkeleton m).finiteTauCategoryData.toFiniteRightTauCategoryData
  let E := (S.standardFormIntervalAlgebraEquivalence m).symm
  let : E.functor.Additive := S.standardFormIntervalEquivalence_inverse_additive m
  let V := S.standardFormIntervalIncomingSummand z
  have hY : Indecomposable (S.standardFormIntervalIncomingTarget z 0 (by omega) (by omega)) := by
    apply MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
      (Graded.FiniteGradedModule.intervalSupport _).ι
    exact Graded.FiniteGradedModule.indecomposable_of_underlying
      (S.standardFormGradedFamily z) 0 (S.standardFormGradedFamily_indecomposable z)
  have hb := FiniteTauMatrix.nonprojective_card_le_beta_of_equivalence T E
    (FiniteTauMatrix.isProjective_iff_projective_obj T)
    (S.standardFormIntervalIncomingMap z 0 (by omega) (by omega))
    (S.standardFormIntervalIncomingMap_rightAlmostSplit z 0 (by omega) (by omega))
    (S.standardFormIntervalIncomingMap_rightMinimal z 0 (by omega) (by omega)) hY
    (S.standardFormIntervalIncomingTarget_not_projective z hz 0 (by omega) (by omega))
    V (S.standardFormIntervalIncomingSummand_indecomposable z)
    (S.standardFormIntervalIncomingBiproductIso z)
  apply (S.standardFormIncoming_nonprojective_card_eq_betaAt z).ge.trans
  apply le_trans _ hb
  let j : {a : MeshCategory.RightMeshData.IncomingArrow z // ¬ Projective (S.fgObj a.1)} →
      {a : MeshCategory.RightMeshData.IncomingArrow z // ¬ Projective (V a)} :=
    fun a ↦ ⟨a.val, S.standardFormIntervalIncomingSummand_not_projective z a.val a.property⟩
  apply Nat.card_le_card_of_injective j
  intro a b hab
  apply Subtype.ext
  exact congrArg
    (fun c : {a : MeshCategory.RightMeshData.IncomingArrow z // ¬ Projective (V a)} ↦ c.val) hab

/-- The manuscript's one-sided transfer, with the original algebra's beta
already identified with its standard form by the arrow occurrence labels. -/
theorem beta_le_standardFormInterval_beta :
    FiniteTauMatrix.beta S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤
      FiniteTauMatrix.beta
        (Ind := Fin (S.standardFormIntervalSkeleton (S.standardFormIntervalControlHeight + 2)).n)
        (S.standardFormIntervalSkeleton (S.standardFormIntervalControlHeight + 2)).finiteTauCategoryData.toFiniteRightTauCategoryData := by
  apply (FiniteTauMatrix.beta_le_iff _ _).mpr
  intro z hz
  apply S.standardFormInterval_betaAt_le z
  intro hp
  exact hz ((FiniteTauMatrix.isProjective_iff_projective_obj _ z).mpr hp)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
