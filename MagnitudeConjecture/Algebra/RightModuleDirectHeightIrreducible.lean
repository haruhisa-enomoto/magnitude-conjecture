import MagnitudeConjecture.Algebra.RightModuleDirectHeightHom
import MagnitudeConjecture.CategoryTheory.FiniteTauHeightIrreducible

/-! # Irreducibility across a single direct-height step -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
namespace PrimitiveDirectedBoundaryData

/-- The composite of two radical maps vanishes across at most one height step. -/
theorem directHeight_radical_comp_eq_zero
    (B : S.PrimitiveDirectedBoundaryData D)
    {X Y : S.SurvivingLabel K}
    (hgap : B.directFactorHeight Y ≤ B.directFactorHeight X + 1)
    {M : S.FactorCategory K} (g : S.factorObject K X ⟶ M) (h : M ⟶ S.factorObject K Y)
    (hg : IsRadicalMorphism g) (hh : IsRadicalMorphism h) : g ≫ h = 0 :=
  MagnitudeConjecture.FiniteTauMatrix.radical_comp_eq_zero_of_height_gap
    (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData B.directFactorHeight
    (fun f hf hn ↦ B.directFactorHeight_lt_of_hom f hf hn) hgap g h hg hh

/-- In particular, the radical square vanishes across at most one height step. -/
theorem directHeight_radicalSquare_eq_zero
    (B : S.PrimitiveDirectedBoundaryData D)
    {X Y : S.SurvivingLabel K}
    (hgap : B.directFactorHeight Y ≤ B.directFactorHeight X + 1)
    (f : S.factorObject K X ⟶ S.factorObject K Y)
    (hf : f ∈ ((S.factorFiniteTauCategoryData K).radical.ideal ⋆ᵢ
      (S.factorFiniteTauCategoryData K).radical.ideal).hom
        (S.factorObject K X) (S.factorObject K Y)) : f = 0 := by
  obtain ⟨M, g, h, hg, hh, heq⟩ :=
    MagnitudeConjecture.FiniteTauMatrix.exists_radical_factorization_of_mem_mul
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData hf
  rw [← heq]
  exact B.directHeight_radical_comp_eq_zero hgap g h
    (((S.factorFiniteTauCategoryData K).radical.mem_ideal_iff g).1 hg)
    (((S.factorFiniteTauCategoryData K).radical.mem_ideal_iff h).1 hh)

/-- Nonzero maps across adjacent direct heights are irreducible. -/
theorem directHeight_isIrreducible_of_eq_add_one
    (B : S.PrimitiveDirectedBoundaryData D)
    {X Y : S.SurvivingLabel K}
    (hgap : B.directFactorHeight Y = B.directFactorHeight X + 1)
    (f : S.factorObject K X ⟶ S.factorObject K Y) (hf : f ≠ 0) :
    IsIrreducibleMorphism f :=
  MagnitudeConjecture.FiniteTauMatrix.isIrreducible_of_height_eq_add_one
    (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData B.directFactorHeight
    (fun f hf hn ↦ B.directFactorHeight_lt_of_hom f hf hn) hgap f hf

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
