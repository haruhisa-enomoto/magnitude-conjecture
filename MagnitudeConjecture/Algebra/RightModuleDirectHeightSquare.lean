import MagnitudeConjecture.Algebra.RightModuleDirectHeightIrreducible
import MagnitudeConjecture.CategoryTheory.FiniteTauSquareTranslate

/-! # Commutative squares for the direct height -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
namespace PrimitiveDirectedBoundaryData

/-- A square of nonzero adjacent-height maps with distinct middle labels
identifies the source with the target's AR translate. -/
theorem directHeight_square_tauPlus
    (B : S.PrimitiveDirectedBoundaryData D)
    {X V W Y : S.SurvivingLabel K} (hVW : V ≠ W)
    (hV : B.directFactorHeight V = B.directFactorHeight X + 1)
    (hW : B.directFactorHeight W = B.directFactorHeight X + 1)
    (hY : B.directFactorHeight Y = B.directFactorHeight V + 1)
    (a : S.factorObject K X ⟶ S.factorObject K V)
    (b : S.factorObject K V ⟶ S.factorObject K Y)
    (c : S.factorObject K X ⟶ S.factorObject K W)
    (d : S.factorObject K W ⟶ S.factorObject K Y)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (hsquare : a ≫ b = c ≫ d) :
    ∃ hn : ¬ (S.factorFiniteTauCategoryData K).IsProjective Y,
      (S.factorFiniteTauCategoryData K).tauPlus ⟨Y, hn⟩ = X := by
  apply MagnitudeConjecture.FiniteTauMatrix.tauPlus_eq_source_of_height_square
    (S.factorFiniteTauCategoryData K) B.directFactorHeight
    (fun f hf hn ↦ B.directFactorHeight_lt_of_hom f hf hn)
    B.directFactorHeight_tauPlus hVW (by omega) (by omega) a b c d ha
    (B.directHeight_isIrreducible_of_eq_add_one hY b hb)
    (B.directHeight_isIrreducible_of_eq_add_one (by omega) d hd).not_isSplitEpi hsquare

/-- Translation injectivity makes a square's target unique once its source
has been identified as the translate. -/
theorem directHeight_square_target_unique
    (B : S.PrimitiveDirectedBoundaryData D)
    {X Y Z : S.SurvivingLabel K}
    (hY : ∃ hn : ¬ (S.factorFiniteTauCategoryData K).IsProjective Y,
      (S.factorFiniteTauCategoryData K).tauPlus ⟨Y, hn⟩ = X)
    (hZ : ∃ hn : ¬ (S.factorFiniteTauCategoryData K).IsProjective Z,
      (S.factorFiniteTauCategoryData K).tauPlus ⟨Z, hn⟩ = X) : Y = Z := by
  obtain ⟨hy, hty⟩ := hY
  obtain ⟨hz, htz⟩ := hZ
  have he : (S.factorFiniteTauCategoryData K).tauPlusEquiv ⟨Y, hy⟩ =
      (S.factorFiniteTauCategoryData K).tauPlusEquiv ⟨Z, hz⟩ :=
    Subtype.ext (hty.trans htz.symm)
  exact congrArg Subtype.val ((S.factorFiniteTauCategoryData K).tauPlusEquiv.injective he)

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
