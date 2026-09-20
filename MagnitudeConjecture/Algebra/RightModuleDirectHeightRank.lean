import MagnitudeConjecture.Algebra.RightModuleDirectHeightBoundary
import MagnitudeConjecture.CategoryTheory.FiniteTauIrreducible

/-! # A finite rank increasing along primitive factor arrows -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- Number of ambient labels strictly earlier in the directed order. -/
def PrimitiveDirectedBoundaryData.directHeightRank
    (B : S.PrimitiveDirectedBoundaryData D) (x : S.SurvivingLabel K) : ℕ := by
  classical
  exact (Finset.univ.filter (fun z ↦ (S.directedLinearOrder B.acyclic).lt z x.1)).card

/-- A nonzero nonisomorphism of the factor strictly increases ambient rank. -/
theorem PrimitiveDirectedBoundaryData.directHeightRank_lt_of_hom
    (B : S.PrimitiveDirectedBoundaryData D)
    {x y : S.SurvivingLabel K}
    (f : S.factorObject K x ⟶ S.factorObject K y)
    (hf : f ≠ 0) (hniso : ¬ IsIso f) :
    B.directHeightRank x < B.directHeightRank y := by
  classical
  have hxy : x ≠ y := by
    intro hxy
    subst y
    obtain ⟨c, hc⟩ := B.acyclic.factorObject_endomorphism_eq_smul_id S K x f
    have hc0 : c ≠ 0 := by
      intro hz
      apply hf
      rw [← hc, hz, zero_smul]
    apply hniso
    rw [← hc]
    exact ⟨⟨c⁻¹ • 𝟙 (S.factorObject K x), by simp [hc0], by simp [hc0]⟩⟩
  let F := S.factorFunctor K
  obtain ⟨g, rfl⟩ := F.map_surjective f
  have hg : g.hom ≠ 0 := by
    intro hz
    apply hf
    rw [show g = 0 by
      apply ObjectProperty.hom_ext
      exact hz]
    exact F.map_zero _ _
  have hlt := S.directedLinearOrder_hom_lt B.acyclic g.hom hg
    (fun h ↦ hxy (Subtype.ext h))
  let O := S.directedLinearOrder B.acyclic
  change (Finset.univ.filter (fun z ↦ O.lt z x.1)).card <
    (Finset.univ.filter (fun z ↦ O.lt z y.1)).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact @lt_trans (Fin S.n) O.toPreorder z x.1 y.1 hz hlt
  · intro heq
    have hm : x.1 ∈ Finset.univ.filter (fun z ↦ O.lt z y.1) := by simp [hlt]
    rw [← heq] at hm
    have hh : O.lt x.1 x.1 := (Finset.mem_filter.mp hm).2
    have hc := (O.lt_iff_le_not_ge _ _).1 hh
    exact hc.2 hc.1

/-- Each nonzero official arrow multiplicity supplies an irreducible
component, hence strictly increases the rank. -/
theorem PrimitiveDirectedBoundaryData.directHeightRank_lt_of_arrow
    (B : S.PrimitiveDirectedBoundaryData D)
    (x y : S.SurvivingLabel K)
    (h : MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData x y ≠ 0) :
    B.directHeightRank x < B.directHeightRank y := by
  classical
  let T := S.factorFiniteTauCategoryData K
  have hex : ∃ i, MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel
      T.toFiniteRightTauCategoryData y i = x := by
    by_contra hn
    push_neg at hn
    apply h
    simp [MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity, T, hn]
  obtain ⟨i, hi⟩ := hex
  have hf := MagnitudeConjecture.FiniteTauMatrix.rightMiddleComponent_isIrreducible T y i
  have hniso : ¬ IsIso (MagnitudeConjecture.FiniteTauMatrix.rightMiddleComponent T y i) := by
    intro hi
    letI := hi
    exact hf.not_isSplitMono inferInstance
  have hne : MagnitudeConjecture.FiniteTauMatrix.rightMiddleComponent T y i ≠ 0 := by
    intro hz
    rw [hz] at hf
    exact (MagnitudeConjecture.FiniteTauMatrix.not_isIrreducibleMorphism_of_mem_radical_mul
      T.toFiniteRightTauCategoryData (zero_mem _)) hf
  have hr := B.directHeightRank_lt_of_hom
    (MagnitudeConjecture.FiniteTauMatrix.rightMiddleComponent T y i)
    hne hniso
  simpa only [hi] using hr

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
