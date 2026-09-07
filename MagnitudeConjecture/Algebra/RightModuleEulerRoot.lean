import MagnitudeConjecture.Algebra.RightModuleCoxeter
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Euler roots for directed finite module categories

This file identifies the inverse-Cartan quadratic form of a module admitting
a length-one projective resolution with its self-Euler characteristic.  The
degree-one self-Ext vanishing supplied by directedness then makes each such
indecomposable dimension vector a positive root.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture

universe u

namespace TwoStepMinimalProjectivePresentation

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable {X : FGModuleCat.{u} Bᵐᵒᵖ}
variable [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]

/-- If the first projective differential is monic and `Ext¹(X,X)` vanishes,
then applying `Hom(-,X)` to the projective presentation is right exact. -/
theorem differentialPrecompLinear_surjective_of_extOne_self_eq_zero
    (P : TwoStepMinimalProjectivePresentation X)
    (hmono : Mono P.differential)
    (hext : ∀ xi : Ext.{u} X X 1, xi = 0) :
    Function.Surjective (P.differentialPrecompLinear (k := k) X) := by
  letI : Mono P.presentationComplex.f := by
    dsimp only [presentationComplex]
    exact hmono
  letI : Epi P.presentationComplex.g := by
    dsimp only [presentationComplex]
    infer_instance
  have hshort : P.presentationComplex.ShortExact :=
    { exact := P.presentationComplex_exact }
  intro f
  let fExt : Ext.{u} P.syzygyPresentation.p X 0 := Ext.mk₀ f
  have hboundary : hshort.extClass.comp fExt rfl = 0 :=
    hext _
  obtain ⟨gExt, hgExt⟩ :=
    Ext.contravariant_sequence_exact₁ hshort X fExt rfl hboundary
  let g : P.augmentation.p ⟶ X := Ext.homEquiv₀ gExt
  refine ⟨g, ?_⟩
  apply (Ext.mk₀_bijective P.syzygyPresentation.p X).injective
  change Ext.mk₀ (P.differential ≫ g) = Ext.mk₀ f
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact hgExt

end TwoStepMinimalProjectivePresentation

namespace RightModule.FiniteIndecomposableSkeleton

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k B)

/-- Pairing a module vector with the inverse-Cartan image of a projective
vector computes the corresponding Hom dimension. -/
theorem dotProduct_projectiveCartanInverse_mulVec_projectiveHomVectorFGObj
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (M P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    S.projectiveHomVectorFGObj M ⬝ᵥ
        S.projectiveCartanInverse.mulVec
          (S.projectiveHomVectorFGObj P) =
      (Module.finrank k (P ⟶ M) : ℤ) := by
  classical
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition P
  have hprojective (j : Fin n) : Projective (S.fgObj (label j)) := by
    let i : S.fgObj (label j) ⟶ P :=
      biproduct.ι (fun t ↦ S.fgObj (label t)) j ≫ e.inv
    let r : P ⟶ S.fgObj (label j) :=
      e.hom ≫ biproduct.π (fun t ↦ S.fgObj (label t)) j
    apply projective_of_retract_of_projective
      (inferInstance : Projective P) i r
    simp [i, r]
  let projectiveLabel : Fin n → S.ProjectiveLabel :=
    fun j ↦ ⟨label j, hprojective j⟩
  have hincoming : S.projectiveHomVectorFGObj P =
      ∑ j, S.projectiveCartanMatrix.col (projectiveLabel j) := by
    funext p
    simp only [projectiveHomVectorFGObj, Finset.sum_apply]
    dsimp only [projectiveLabel]
    change (Module.finrank k (S.fgObj p.label ⟶ P) : ℤ) =
      ∑ j, (Module.finrank k
        (S.fgObj p.label ⟶ S.fgObj (label j)) : ℤ)
    exact_mod_cast
      (CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
        k (S.fgObj p.label) P (fun j ↦ S.fgObj (label j)) e)
  have hcolumn (j : Fin n) :
      S.projectiveCartanInverse.mulVec
          (S.projectiveCartanMatrix.col (projectiveLabel j)) =
        Pi.single (projectiveLabel j) 1 := by
    rw [← show S.projectiveCartanMatrix.mulVec
        (Pi.single (projectiveLabel j) 1) =
          S.projectiveCartanMatrix.col (projectiveLabel j) by
      simpa using Matrix.mulVec_single S.projectiveCartanMatrix
        (projectiveLabel j) (1 : ℤ)]
    rw [Matrix.mulVec_mulVec, S.projectiveCartanInverse_mul H]
    ext i
    by_cases hi : i = projectiveLabel j <;> simp [hi]
  have hmulVecSum :
      S.projectiveCartanInverse.mulVec
          (∑ j, S.projectiveCartanMatrix.col (projectiveLabel j)) =
        ∑ j, S.projectiveCartanInverse.mulVec
          (S.projectiveCartanMatrix.col (projectiveLabel j)) := by
    simpa using Matrix.mulVec_sum S.projectiveCartanInverse Finset.univ
      (fun j ↦ S.projectiveCartanMatrix.col (projectiveLabel j))
  rw [hincoming, hmulVecSum, dotProduct_sum]
  simp_rw [hcolumn, dotProduct_single, mul_one]
  change (∑ j, (Module.finrank k
      (S.fgObj (label j) ⟶ M) : ℤ)) =
    (Module.finrank k (P ⟶ M) : ℤ)
  exact_mod_cast
    (CategoryTheory.finrank_hom_eq_sum_of_biproduct_iso
      k P M (fun j ↦ S.fgObj (label j)) e).symm

/-- A length-one projective resolution identifies the inverse-Cartan
quadratic form with the alternating Hom dimension of its two projectives. -/
theorem quadraticForm_projectiveHomVectorFGObj_eq_sub
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {X : FGModuleCat.{u} Bᵐᵒᵖ}
    (P : TwoStepMinimalProjectivePresentation X)
    (hmono : Mono P.differential) :
    CartanCoordinate.quadraticForm S.projectiveCartanInverse
        (S.projectiveHomVectorFGObj X) =
      (Module.finrank k (P.augmentation.p ⟶ X) : ℤ) -
        (Module.finrank k (P.syzygyPresentation.p ⟶ X) : ℤ) := by
  have hvector := P.projectiveHomVectorFGObj_eq_sub_of_mono_differential
    S hmono
  unfold CartanCoordinate.quadraticForm
  calc
    S.projectiveHomVectorFGObj X ⬝ᵥ
        S.projectiveCartanInverse.mulVec
          (S.projectiveHomVectorFGObj X) =
      S.projectiveHomVectorFGObj X ⬝ᵥ
        S.projectiveCartanInverse.mulVec
          (S.projectiveHomVectorFGObj P.augmentation.p -
            S.projectiveHomVectorFGObj P.syzygyPresentation.p) := by
        rw [← hvector]
    _ = S.projectiveHomVectorFGObj X ⬝ᵥ
          S.projectiveCartanInverse.mulVec
            (S.projectiveHomVectorFGObj P.augmentation.p) -
        S.projectiveHomVectorFGObj X ⬝ᵥ
          S.projectiveCartanInverse.mulVec
            (S.projectiveHomVectorFGObj P.syzygyPresentation.p) := by
        rw [Matrix.mulVec_sub, dotProduct_sub]
    _ = _ := by
      rw [S.dotProduct_projectiveCartanInverse_mulVec_projectiveHomVectorFGObj
          H X P.augmentation.p,
        S.dotProduct_projectiveCartanInverse_mulVec_projectiveHomVectorFGObj
          H X P.syzygyPresentation.p]

/-- A selected indecomposable with projective dimension at most one has a
positive-root projective-Hom vector. -/
theorem projectiveHomVector_quadraticForm_eq_one_of_mono_differential
    [IsAlgClosed k]
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : Fin S.n)
    (P : TwoStepMinimalProjectivePresentation (S.fgObj x))
    (hmono : Mono P.differential) :
    CartanCoordinate.quadraticForm S.projectiveCartanInverse
      (S.projectiveHomVector x) = 1 := by
  have hsurjective :=
    P.differentialPrecompLinear_surjective_of_extOne_self_eq_zero
      (k := k) hmono (S.extOne_self_eq_zero H x)
  have hexact : Function.Exact
      (P.augmentationPrecompLinear (k := k) (S.fgObj x))
      (P.differentialPrecompLinear (k := k) (S.fgObj x)) := by
    intro y
    change y ∈ LinearMap.ker
        (P.differentialPrecompLinear (k := k) (S.fgObj x)) ↔
      y ∈ LinearMap.range
        (P.augmentationPrecompLinear (k := k) (S.fgObj x))
    rw [P.range_augmentationPrecompLinear (k := k) (S.fgObj x)]
  have hrank := CategoryTheory.finrank_middle_eq_add_of_exact k
    (P.augmentationPrecompLinear (k := k) (S.fgObj x))
    (P.differentialPrecompLinear (k := k) (S.fgObj x))
    hexact (P.augmentationPrecompLinear_injective (k := k) (S.fgObj x))
    hsurjective
  have hscalar : Module.finrank k (S.fgObj x ⟶ S.fgObj x) = 1 :=
    H.finrank_endomorphism_eq_one S x
  have hquad := S.quadraticForm_projectiveHomVectorFGObj_eq_sub H P hmono
  rw [S.projectiveHomVectorFGObj_fgObj] at hquad
  rw [hquad]
  omega

namespace PrimitiveProjectivePresentation

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable (P : S.PrimitiveProjectivePresentation)

/-- The endpoint of the literal middle-support Auslander--Reiten sequence is
a positive root for the support algebra's inverse-Cartan quadratic form. -/
theorem rightSequenceSupportTarget_quadraticForm_eq_one
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    let T := P.rightSequenceMiddleSupportSkeleton hA z
    CartanCoordinate.quadraticForm T.projectiveCartanInverse
      (T.projectiveHomVector
        (P.rightSequenceSupportTargetLabel hA z)) = 1 := by
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.rightSequenceMiddleSupportSkeleton hA z
  letI : EnoughProjectives
      (FGModuleCat.{u} (P.SupportAlgebra X)ᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      ((P.SupportAlgebra X)ᵐᵒᵖ)
  letI : HasExt.{u}
      (FGModuleCat.{u} (P.SupportAlgebra X)ᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  obtain ⟨Q⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (P.rightSequenceSupportEndpointFGObj hA z)
  obtain ⟨e⟩ :=
    P.rightSequenceSupportKernelIso_nakayamaKernel hA H z Q
  have hzeroNak : ∀ q :
      RightModule.injectiveCogeneratorFGObj (k := k)
          (B := P.SupportAlgebra X) ⟶ Q.nakayamaKernel (k := k),
      q = 0 := by
    intro q
    apply (cancel_mono e.inv).1
    simpa using
      P.hom_from_supportInjectiveCogenerator_to_rightKernel_eq_zero
        hA H z (q ≫ e.inv)
  have hmono : Mono Q.differential :=
    RightModule.mono_of_hom_from_injectiveCogenerator_to_nakayamaKernel_eq_zero
      (k := k) Q.differential inferInstance hzeroNak
  exact T.projectiveHomVector_quadraticForm_eq_one_of_mono_differential
    (P.rightSequenceMiddleSupportAcyclic hA H z)
    (P.rightSequenceSupportTargetLabel hA z) Q hmono

end PrimitiveProjectivePresentation

end RightModule.FiniteIndecomposableSkeleton

end MagnitudeConjecture
