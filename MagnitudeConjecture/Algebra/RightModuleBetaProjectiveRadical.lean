import MagnitudeConjecture.Algebra.FiniteModuleDecomposition
import MagnitudeConjecture.Algebra.RightModuleBetaBoundary
import MagnitudeConjecture.Algebra.RightModuleStandardFormArrowRealization

/-!
# Beta bounds at a projective radical boundary

For a noninjective indecomposable projective `P`, every irreducible map into
`P` has noninjective source: an irreducible map from an injective object to a
projective object would split whether it were monic or epic.  Simultaneous
inverse Auslander--Reiten translation therefore identifies all incoming
arrow occurrences at `P` with the nonprojective occurrences in the right
mesh ending at `τ⁻¹P`.  Consequently the number of indecomposable summands
of `rad P` is bounded by the ordinary beta invariant.

This is the decomposition-count part of Auslander--Reiten's projective
radical argument.  The later uniseriality of the resulting one or two
summands is not asserted here.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- There is no irreducible map from an injective selected indecomposable
to a projective selected indecomposable. -/
theorem arrowMultiplicity_eq_zero_of_injective_source_of_projective_target
    (source target : Fin S.n)
    (hsource : Injective (S.fgObj source))
    (htarget : Projective (S.fgObj target)) :
    FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target = 0 := by
  by_contra hne
  have hpos : 0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData source target :=
    Nat.pos_of_ne_zero hne
  let a : S.StandardFormArrow target source := ⟨0, hpos⟩
  let f : S.fgObj source ⟶ S.fgObj target := S.standardFormArrowMap a
  have hf : IsIrreducibleMorphism f :=
    S.standardFormArrowMap_isIrreducible a
  rcases hf.mono_or_epi with hmono | hepi
  · letI : Mono f := hmono
    letI : Injective (S.fgObj source) := hsource
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := Injective.factorThru (𝟙 (S.fgObj source)) f
        id := Injective.comp_factorThru (𝟙 (S.fgObj source)) f }
  · letI : Epi f := hepi
    letI : Projective (S.fgObj target) := htarget
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := Projective.factorThru (𝟙 (S.fgObj target)) f
        id := Projective.factorThru_comp (𝟙 (S.fgObj target)) f }

/-- At a noninjective projective boundary, total incoming middle arity is
the beta count at the inverse translate. -/
theorem projective_rightMiddleArity_eq_betaAt_inverseTranslation
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hpNotInjective : ¬ Injective (S.fgObj p)) :
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p =
      FiniteTauMatrix.betaAt
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
          ((S.rightTranslationEquiv).symm ⟨p, hpNotInjective⟩).1 := by
  classical
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let e := S.rightTranslationEquiv.symm
  let pni : {i : Fin S.n // ¬ Injective (S.fgObj i)} :=
    ⟨p, hpNotInjective⟩
  rw [← FiniteTauMatrix.sum_arrowMultiplicity_source T p]
  unfold FiniteTauMatrix.betaAt
  calc
    (∑ source, FiniteTauMatrix.arrowMultiplicity T source p) =
        ∑ source, if Injective (S.fgObj source) then 0 else
          FiniteTauMatrix.arrowMultiplicity T source p := by
      apply Finset.sum_congr rfl
      intro source _
      by_cases hsource : Injective (S.fgObj source)
      · rw [if_pos hsource,
          S.arrowMultiplicity_eq_zero_of_injective_source_of_projective_target
            source p hsource hp]
      · rw [if_neg hsource]
    _ = ∑ source ∈ Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Injective (S.fgObj i)),
        FiniteTauMatrix.arrowMultiplicity T source p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro source _
      by_cases hsource : Injective (S.fgObj source) <;> simp [hsource]
    _ = ∑ source : {i : Fin S.n // ¬ Injective (S.fgObj i)},
        FiniteTauMatrix.arrowMultiplicity T source.1 p := by
      exact Finset.sum_subtype
        (Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Injective (S.fgObj i)))
        (by simp) _
    _ = ∑ source : {i : Fin S.n // ¬ Projective (S.fgObj i)},
        FiniteTauMatrix.arrowMultiplicity T source.1 (e pni).1 := by
      exact Fintype.sum_equiv e
        (fun source : {i : Fin S.n // ¬ Injective (S.fgObj i)} ↦
          FiniteTauMatrix.arrowMultiplicity T source.1 p)
        (fun source : {i : Fin S.n // ¬ Projective (S.fgObj i)} ↦
          FiniteTauMatrix.arrowMultiplicity T source.1 (e pni).1)
        (fun source ↦ by
          simpa only [e, pni] using
            (S.arrowMultiplicity_inverseTranslation_pair source pni).symm)
    _ = ∑ source ∈ Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Projective (S.fgObj i)),
        FiniteTauMatrix.arrowMultiplicity T source (e pni).1 := by
      exact (Finset.sum_subtype
        (p := fun i : Fin S.n ↦ ¬ Projective (S.fgObj i))
        (Finset.univ.filter
          (fun i : Fin S.n ↦ ¬ Projective (S.fgObj i)))
        (by simp)
        (fun source : Fin S.n ↦
          FiniteTauMatrix.arrowMultiplicity T source (e pni).1)).symm
    _ = ∑ source, if Projective (S.fgObj source) then 0 else
        FiniteTauMatrix.arrowMultiplicity T source (e pni).1 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro source _
      by_cases hsource : Projective (S.fgObj source) <;> simp [hsource]
    _ = ∑ source, if T.IsProjective source then 0 else
        FiniteTauMatrix.arrowMultiplicity T source (e pni).1 := by
      apply Finset.sum_congr rfl
      intro source _
      rw [FiniteTauMatrix.isProjective_iff_projective_obj]
      rfl

/-- The projective-boundary arity of a noninjective projective is bounded
by the global beta invariant. -/
theorem projective_rightMiddleArity_le_beta
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hpNotInjective : ¬ Injective (S.fgObj p)) :
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p ≤
      FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let z := (S.rightTranslationEquiv).symm ⟨p, hpNotInjective⟩
  rw [S.projective_rightMiddleArity_eq_betaAt_inverseTranslation
    p hp hpNotInjective]
  apply (FiniteTauMatrix.beta_le_iff T (FiniteTauMatrix.beta T)).1 le_rfl
  rw [FiniteTauMatrix.isProjective_iff_projective_obj]
  exact z.2

/-- Under `beta ≤ 2`, the radical of a noninjective indecomposable
projective admits an indecomposable decomposition with at most two
occurrences. -/
theorem exists_projectiveBoundaryRadical_decomposition_le_two
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hpNotInjective : ¬ Injective (S.fgObj p))
    (hbeta : FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    ∃ d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
        (S.projectiveBoundaryRadical p),
      d.n ≤ 2 := by
  letI : Module.Finite k (S.projectiveBoundaryRadical p) := by
    exact RightModule.finite_over_field_of_finitelyGenerated k A
      (S.projectiveBoundaryRadical p)
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) (S.projectiveBoundaryRadical p)
  refine ⟨d, ?_⟩
  have harity : FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p = d.n :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p d
        (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp)
        (S.projectiveBoundaryRadicalInclusion_isRightMinimal p)
  rw [← harity]
  exact (S.projective_rightMiddleArity_le_beta p hp hpNotInjective).trans hbeta

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
