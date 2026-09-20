import MagnitudeConjecture.Algebra.RightModuleDirectHeightIrreducible
import MagnitudeConjecture.CategoryTheory.FiniteTauHeightRadicalPowers

/-! # Full radical concentration in the primitive factor's direct height -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
namespace PrimitiveDirectedBoundaryData

/-- At positive height difference, the full Hom space is concentrated in that radical layer. -/
theorem directHeight_radical_concentration
    (B : S.PrimitiveDirectedBoundaryData D) {X Y : S.SurvivingLabel K}
    (hxy : B.directFactorHeight X < B.directFactorHeight Y) :
    ((S.factorFiniteTauCategoryData K).radical.ideal.pow
      (B.directFactorHeight Y - B.directFactorHeight X)).hom
        (S.factorObject K X) (S.factorObject K Y) = ⊤ ∧
    ((S.factorFiniteTauCategoryData K).radical.ideal.pow
      (B.directFactorHeight Y - B.directFactorHeight X + 1)).hom
        (S.factorObject K X) (S.factorObject K Y) = ⊥ := by
  let T := (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
  constructor
  · apply top_le_iff.mp
    intro f hf
    exact MagnitudeConjecture.FiniteTauMatrix.hom_mem_radical_pow_of_height_gap T B.directFactorHeight
      (fun y i ↦ (B.directFactorHeight_arrow _ y (directFactorArrow_rightMiddleLabel y i)).symm)
      _ (by omega) f
  · apply le_bot_iff.mp
    intro f hf
    apply AddSubgroup.mem_bot.mpr
    exact MagnitudeConjecture.FiniteTauMatrix.radical_pow_eq_zero_of_height_gap T B.directFactorHeight
      (fun f hf hn ↦ B.directFactorHeight_lt_of_hom f hf hn) _ (by omega) f hf


/-- For distinct labels with a nonzero map, the height difference is positive,
the corresponding radical power is the whole Hom group, and the next vanishes. -/
theorem directHeight_radical_concentration_of_hom
    (B : S.PrimitiveDirectedBoundaryData D) {X Y : S.SurvivingLabel K}
    (hXY : X ≠ Y) (f : S.factorObject K X ⟶ S.factorObject K Y) (hf : f ≠ 0) :
    0 < B.directFactorHeight Y - B.directFactorHeight X ∧
    ((S.factorFiniteTauCategoryData K).radical.ideal.pow
      (B.directFactorHeight Y - B.directFactorHeight X)).hom
        (S.factorObject K X) (S.factorObject K Y) = ⊤ ∧
    ((S.factorFiniteTauCategoryData K).radical.ideal.pow
      (B.directFactorHeight Y - B.directFactorHeight X + 1)).hom
        (S.factorObject K X) (S.factorObject K Y) = ⊥ := by
  let T := (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
  have hn : ¬ IsIso f := by
    intro hI
    letI : IsIso f := hI
    let e : S.factorObject K X ≅ S.factorObject K Y := asIso f
    exact hXY (T.obj_skeletal ⟨e⟩)
  have hxy := B.directFactorHeight_lt_of_hom f hf hn
  exact ⟨by omega, B.directHeight_radical_concentration hxy⟩

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
