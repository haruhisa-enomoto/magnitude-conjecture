import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.SocleModule

/-!
# Simple socles in almost-split sources

If the source of a right almost-split sequence has simple socle, some
displayed component of its monic left map must itself be monic.  Otherwise
every component kills the socle, contradicting monicity of the total map.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A simple socle in the source of a chosen right almost-split sequence
forces at least one displayed left component to be monic. -/
theorem exists_rightSequenceLeftComponent_mono_of_simpleSocle
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hsocle : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ (S.fgObj (S.rightTranslationLabel z)))) :
    ∃ i : (S.minimalRightAlmostSplitAt z.1).index,
      Mono ((S.rightSequenceLeftDecomposition z).component
        S.almostSplitSkeleton i) := by
  have hTlength :=
    fgModule_isFiniteLength (k := k) (A := A)
      (S.fgObj (S.rightTranslationLabel z))
  letI : IsArtinian Aᵐᵒᵖ (S.fgObj (S.rightTranslationLabel z)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hTlength).2
  by_contra hnone
  push Not at hnone
  let J := moduleSocle Aᵐᵒᵖ (S.fgObj (S.rightTranslationLabel z))
  letI : Module.Finite Aᵐᵒᵖ (S.fgObj (S.rightTranslationLabel z)) :=
    (S.fgObj (S.rightTranslationLabel z)).2
  letI : Module.Finite Aᵐᵒᵖ J := inferInstance
  let Jfg : FGModuleCat.{u} Aᵐᵒᵖ := FGModuleCat.of Aᵐᵒᵖ J
  let j : Jfg ⟶ S.fgObj (S.rightTranslationLabel z) :=
    ConcreteCategory.ofHom J.subtype
  letI : IsSimpleModule Aᵐᵒᵖ J := hsocle
  letI : Nontrivial J := IsSimpleModule.nontrivial Aᵐᵒᵖ J
  have hjne : j ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ : ∃ x : J, x ≠ 0 := exists_ne 0
    apply hx
    have hvalue := congrArg
      (fun f : Jfg ⟶ S.fgObj (S.rightTranslationLabel z) ↦
        f.hom.hom x) hzero
    apply Subtype.ext
    dsimp only [j, Jfg] at hvalue
    exact hvalue
  have hjcomponent
      (i : (S.minimalRightAlmostSplitAt z.1).index) :
      j ≫ (S.rightSequenceLeftDecomposition z).component
        S.almostSplitSkeleton i = 0 := by
    have hnotinj : ¬ Function.Injective
        ((S.rightSequenceLeftDecomposition z).component
          S.almostSplitSkeleton i).hom.hom := by
      intro hinj
      exact hnone i
        ((IndecomposableSkeleton.fg_mono_iff_injective
          ((S.rightSequenceLeftDecomposition z).component
            S.almostSplitSkeleton i)).2 hinj)
    have hle : J ≤ LinearMap.ker
        ((S.rightSequenceLeftDecomposition z).component
          S.almostSplitSkeleton i).hom.hom :=
      moduleSocle_le_ker_of_not_injective hsocle _ hnotinj
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hxJ : j.hom.hom x ∈ J := by
      dsimp only [j, Jfg]
      exact x.2
    exact LinearMap.mem_ker.mp (hle hxJ)
  have hjmap : j ≫ (S.rightSequenceLeftDecomposition z).map = 0 := by
    apply (cancel_mono
      (S.rightSequenceLeftDecomposition z).decomposition.hom).1
    apply biproduct.hom_ext
    intro i
    convert hjcomponent i using 1 <;>
      simp only [zero_comp, Category.assoc,
        IndecomposableSkeleton.MinimalLeftAlmostSplitDecomposition.component]
    rfl
  have hLmono : Mono (S.rightSequenceLeftDecomposition z).map := by
    change Mono (S.rightKernelMap z)
    dsimp [rightKernelMap]
    infer_instance
  apply hjne
  exact (Preadditive.mono_iff_cancel_zero _).1 hLmono Jfg j hjmap

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
