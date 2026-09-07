import MagnitudeConjecture.Algebra.RightModuleNakayamaARIdentification
import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModuleMiddleSupportCartan
import MagnitudeConjecture.CategoryTheory.LinearBiproduct
import MagnitudeConjecture.CategoryTheory.TauExactDimension

/-!
# The Coxeter vector of a Nakayama kernel

This file proves the coordinate calculation in Ringel Section 2.4(4) for the
right-module convention used by the manuscript.  A finite projective is first
decomposed into the selected indecomposable projectives.  The two exact
sequences attached to a length-one projective presentation then identify the
Nakayama kernel vector with the Coxeter transform of the endpoint vector.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- A Cartan column, viewed as a row vector, is carried to the corresponding
Cartan row by `Cinvᵀ C`. -/
theorem projectiveColumn_vecMul_inverseTranspose_mul
    (C Cinv : Matrix I I ℤ) (hinv : Cinv * C = 1) (p : I) :
    Matrix.vecMul (C.col p) (Cinv.transpose * C) = C.row p := by
  change Matrix.vecMul (C.transpose.row p) (Cinv.transpose * C) = C.row p
  rw [← Matrix.single_one_vecMul p C.transpose]
  rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc]
  rw [← Matrix.transpose_mul, hinv]
  simp

/-- The same Cartan identity summed over a finite family of projective
summands. -/
theorem projectiveColumnSum_vecMul_inverseTranspose_mul
    {J : Type u} [Fintype J]
    (C Cinv : Matrix I I ℤ) (hinv : Cinv * C = 1) (label : J → I) :
    Matrix.vecMul (∑ j, C.col (label j)) (Cinv.transpose * C) =
      ∑ j, C.row (label j) := by
  change (Cinv.transpose * C).vecMulLinear
      (∑ j, C.col (label j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact projectiveColumn_vecMul_inverseTranspose_mul
    C Cinv hinv (label j)

namespace RightModule.FiniteIndecomposableSkeleton

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k B)

/-- The projective-Hom dimension vector of an arbitrary finite module. -/
def projectiveHomVectorFGObj (M : FGModuleCat.{u} Bᵐᵒᵖ) :
    S.ProjectiveLabel → ℤ :=
  fun p ↦ Module.finrank k (S.fgObj p.label ⟶ M)

/-- The opposite Hom vector of an arbitrary finite module, evaluated on the
selected indecomposable projectives. -/
def projectiveCohomVectorFGObj (M : FGModuleCat.{u} Bᵐᵒᵖ) :
    S.ProjectiveLabel → ℤ :=
  fun p ↦ Module.finrank k (M ⟶ S.fgObj p.label)

omit [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
@[simp] theorem projectiveHomVectorFGObj_fgObj (x : Fin S.n) :
    S.projectiveHomVectorFGObj (S.fgObj x) =
      S.projectiveHomVector x := rfl

/-- Nakayama--Hom duality exchanges the two projective Hom vectors. -/
theorem projectiveHomVectorFGObj_projectiveNakayama
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    S.projectiveHomVectorFGObj
        (RightModule.projectiveNakayamaFGObj (k := k) P) =
      S.projectiveCohomVectorFGObj P := by
  funext p
  change (Module.finrank k
      (S.fgObj p.label ⟶
        RightModule.projectiveNakayamaFGObj (k := k) P) : ℤ) =
    (Module.finrank k (P ⟶ S.fgObj p.label) : ℤ)
  exact_mod_cast
    (calc
      Module.finrank k
          (S.fgObj p.label ⟶
            RightModule.projectiveNakayamaFGObj (k := k) P) =
          Module.finrank k
            ((P ⟶ S.fgObj p.label) →ₗ[k] k) :=
        (RightModule.fieldNakayamaHomEquiv
          (k := k) P (S.fgObj p.label)).finrank_eq
      _ = Module.finrank k (P ⟶ S.fgObj p.label) :=
        Subspace.dual_finrank_eq)

omit [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
/-- Projective-Hom vectors are invariant under isomorphism of their target
module. -/
theorem projectiveHomVectorFGObj_iso
    {M N : FGModuleCat.{u} Bᵐᵒᵖ} (e : M ≅ N) :
    S.projectiveHomVectorFGObj M = S.projectiveHomVectorFGObj N := by
  funext p
  change (Module.finrank k (S.fgObj p.label ⟶ M) : ℤ) =
    (Module.finrank k (S.fgObj p.label ⟶ N) : ℤ)
  exact_mod_cast
    (CategoryTheory.Linear.homCongr k (Iso.refl _) e).finrank_eq

/-- For every finite projective, multiplication by `Cinvᵀ C` exchanges its
incoming and outgoing projective Hom vectors. -/
theorem projectiveHomVectorFGObj_vecMul_inverseTranspose_mul
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P] :
    Matrix.vecMul (S.projectiveHomVectorFGObj P)
        (S.projectiveCartanInverse.transpose *
          S.projectiveCartanMatrix) =
      S.projectiveCohomVectorFGObj P := by
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
  have houtgoing : S.projectiveCohomVectorFGObj P =
      ∑ j, S.projectiveCartanMatrix.row (projectiveLabel j) := by
    funext p
    simp only [projectiveCohomVectorFGObj, Finset.sum_apply]
    dsimp only [projectiveLabel]
    change (Module.finrank k (P ⟶ S.fgObj p.label) : ℤ) =
      ∑ j, (Module.finrank k
        (S.fgObj (label j) ⟶ S.fgObj p.label) : ℤ)
    exact_mod_cast
      (CategoryTheory.finrank_hom_eq_sum_of_biproduct_iso
        k P (S.fgObj p.label) (fun j ↦ S.fgObj (label j)) e)
  rw [hincoming, houtgoing]
  exact projectiveColumnSum_vecMul_inverseTranspose_mul
    S.projectiveCartanMatrix S.projectiveCartanInverse
      (S.projectiveCartanInverse_mul H) projectiveLabel

end RightModule.FiniteIndecomposableSkeleton

namespace TwoStepMinimalProjectivePresentation

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable {X : FGModuleCat.{u} Bᵐᵒᵖ}

/-- If the presented module has no map to the regular module, precomposition
by the first projective differential is injective on regular-valued Hom. -/
theorem regularHomDualMap_mono_of_hom_to_regular_eq_zero
    (P : TwoStepMinimalProjectivePresentation X)
    (hzero : ∀ q : X ⟶ RightModule.rightRegularFGObj (B := B), q = 0) :
    Mono (RightModule.regularHomDualMap (k := k) P.differential) := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite k B
  letI : Module.Finite Bᵐᵒᵖ B :=
    Module.Finite.equiv RightModule.rightRegularLinearEquiv
  apply (IndecomposableSkeleton.fg_mono_iff_injective _).2
  intro phi psi hphi
  let q : P.augmentation.p ⟶ RightModule.rightRegularFGObj (B := B) :=
    FGModuleCat.ofHom (phi - psi)
  have hqd : P.differential ≫ q = 0 := by
    apply FGModuleCat.hom_ext
    dsimp only [q]
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hphi x
    change phi (P.differential.hom.hom x) =
      psi (P.differential.hom.hom x) at hx
    change phi (P.differential.hom.hom x) -
      psi (P.differential.hom.hom x) = 0
    rw [hx, sub_self]
  letI : Epi P.presentationComplex.g := by
    dsimp only [presentationComplex]
    infer_instance
  let descended := CokernelCofork.IsColimit.desc'
    P.presentationComplex_exact.gIsCokernel q hqd
  have hdescZero : descended.1 = 0 := hzero descended.1
  change descended.1 =
    (0 : X ⟶ RightModule.rightRegularFGObj (B := B)) at hdescZero
  have hqzero : q = 0 := by
    have hfac := descended.2
    change P.augmentation.f ≫ descended.1 = q at hfac
    calc
      q = P.augmentation.f ≫ descended.1 := hfac.symm
      _ = P.augmentation.f ≫ 0 := by rw [hdescZero]
      _ = 0 := comp_zero
  apply sub_eq_zero.mp
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun f : P.augmentation.p ⟶ RightModule.rightRegularFGObj (B := B) ↦
      f.hom.hom x) hqzero
  change (phi - psi) x = 0 at hx
  exact hx

/-- The same regular-module vanishing makes the Nakayama differential epic. -/
theorem nakayamaDifferential_epi_of_hom_to_regular_eq_zero
    (P : TwoStepMinimalProjectivePresentation X)
    (hzero : ∀ q : X ⟶ RightModule.rightRegularFGObj (B := B), q = 0) :
    Epi (P.nakayamaDifferential (k := k)) := by
  letI : Mono (RightModule.regularHomDualMap (k := k) P.differential) :=
    P.regularHomDualMap_mono_of_hom_to_regular_eq_zero (k := k) hzero
  let E :=
    QuotientSubmoduleEquidistribution.Contragredient.dualityEquivalence k B
  change Epi (E.functor.map
    (RightModule.regularHomDualMap (k := k) P.differential).op)
  infer_instance

/-- A monic first differential gives the dimension-vector equation for the
projective presentation. -/
theorem projectiveHomVectorFGObj_eq_sub_of_mono_differential
    (S : RightModule.FiniteIndecomposableSkeleton k B)
    (P : TwoStepMinimalProjectivePresentation X)
    (hmono : Mono P.differential) :
    S.projectiveHomVectorFGObj X =
      S.projectiveHomVectorFGObj P.augmentation.p -
        S.projectiveHomVectorFGObj P.syzygyPresentation.p := by
  letI : Mono P.differential := hmono
  funext p
  letI : Projective (S.fgObj p.label) := p.2
  let f : (S.fgObj p.label ⟶ P.syzygyPresentation.p) →ₗ[k]
      (S.fgObj p.label ⟶ P.augmentation.p) :=
    CategoryTheory.Linear.rightComp k (S.fgObj p.label) P.differential
  let g : (S.fgObj p.label ⟶ P.augmentation.p) →ₗ[k]
      (S.fgObj p.label ⟶ X) :=
    CategoryTheory.Linear.rightComp k (S.fgObj p.label) P.augmentation.f
  have hfInjective : Function.Injective f := by
    intro a b hab
    change a ≫ P.differential = b ≫ P.differential at hab
    exact (cancel_mono P.differential).1 hab
  have hgSurjective : Function.Surjective g := by
    intro b
    obtain ⟨a, ha⟩ := Projective.factors b P.augmentation.f
    exact ⟨a, ha⟩
  have hfgExact : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      change b ≫ P.augmentation.f = 0 at hb
      letI : Mono P.presentationComplex.f := by
        dsimp only [presentationComplex]
        infer_instance
      letI : Epi P.presentationComplex.g := by
        dsimp only [presentationComplex]
        infer_instance
      have hshort : P.presentationComplex.ShortExact :=
        { exact := P.presentationComplex_exact }
      let lifted := KernelFork.IsLimit.lift' hshort.fIsKernel b hb
      exact ⟨lifted.1, lifted.2⟩
    · rintro ⟨a, rfl⟩
      change (a ≫ P.differential) ≫ P.augmentation.f = 0
      rw [Category.assoc, P.differential_comp_augmentation, comp_zero]
  have hRank := CategoryTheory.finrank_middle_eq_add_of_exact
    k f g hfgExact hfInjective hgSurjective
  change (Module.finrank k (S.fgObj p.label ⟶ X) : ℤ) =
    (Module.finrank k (S.fgObj p.label ⟶ P.augmentation.p) : ℤ) -
      (Module.finrank k
        (S.fgObj p.label ⟶ P.syzygyPresentation.p) : ℤ)
  have hRankInt :
      (Module.finrank k
        (S.fgObj p.label ⟶ P.augmentation.p) : ℤ) =
        (Module.finrank k
          (S.fgObj p.label ⟶ P.syzygyPresentation.p) : ℤ) +
          (Module.finrank k (S.fgObj p.label ⟶ X) : ℤ) := by
    exact_mod_cast hRank
  omega

/-- The regular-module vanishing gives the exact Nakayama-kernel vector
equation. -/
theorem nakayamaKernel_projectiveHomVector_eq_sub
    (S : RightModule.FiniteIndecomposableSkeleton k B)
    (P : TwoStepMinimalProjectivePresentation X)
    (hzero : ∀ q : X ⟶ RightModule.rightRegularFGObj (B := B), q = 0) :
    S.projectiveHomVectorFGObj (P.nakayamaKernel (k := k)) =
      S.projectiveHomVectorFGObj
          (RightModule.projectiveNakayamaFGObj (k := k)
            P.syzygyPresentation.p) -
        S.projectiveHomVectorFGObj
          (RightModule.projectiveNakayamaFGObj (k := k)
            P.augmentation.p) := by
  letI : Epi (P.nakayamaDifferential (k := k)) :=
    P.nakayamaDifferential_epi_of_hom_to_regular_eq_zero (k := k) hzero
  funext p
  letI : Projective (S.fgObj p.label) := p.2
  let f : (S.fgObj p.label ⟶ P.nakayamaKernel (k := k)) →ₗ[k]
      (S.fgObj p.label ⟶
        RightModule.projectiveNakayamaFGObj (k := k)
          P.syzygyPresentation.p) :=
    CategoryTheory.Linear.rightComp k (S.fgObj p.label)
      (kernel.ι (P.nakayamaDifferential (k := k)))
  let g : (S.fgObj p.label ⟶
        RightModule.projectiveNakayamaFGObj (k := k)
          P.syzygyPresentation.p) →ₗ[k]
      (S.fgObj p.label ⟶
        RightModule.projectiveNakayamaFGObj (k := k) P.augmentation.p) :=
    CategoryTheory.Linear.rightComp k (S.fgObj p.label)
      (P.nakayamaDifferential (k := k))
  have hfInjective : Function.Injective f := by
    intro a b hab
    change a ≫ kernel.ι (P.nakayamaDifferential (k := k)) =
      b ≫ kernel.ι (P.nakayamaDifferential (k := k)) at hab
    exact (cancel_mono (kernel.ι (P.nakayamaDifferential (k := k)))).1 hab
  have hgSurjective : Function.Surjective g := by
    intro b
    obtain ⟨a, ha⟩ := Projective.factors b
      (P.nakayamaDifferential (k := k))
    exact ⟨a, ha⟩
  have hfgExact : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      change b ≫ P.nakayamaDifferential (k := k) = 0 at hb
      let lifted := KernelFork.IsLimit.lift'
        (kernelIsKernel (P.nakayamaDifferential (k := k))) b hb
      exact ⟨lifted.1, lifted.2⟩
    · rintro ⟨a, rfl⟩
      change (a ≫ kernel.ι (P.nakayamaDifferential (k := k))) ≫
        P.nakayamaDifferential (k := k) = 0
      rw [Category.assoc, kernel.condition, comp_zero]
  have hRank := CategoryTheory.finrank_middle_eq_add_of_exact
    k f g hfgExact hfInjective hgSurjective
  change (Module.finrank k
      (S.fgObj p.label ⟶ P.nakayamaKernel (k := k)) : ℤ) =
    (Module.finrank k
      (S.fgObj p.label ⟶
        RightModule.projectiveNakayamaFGObj (k := k)
          P.syzygyPresentation.p) : ℤ) -
      (Module.finrank k
        (S.fgObj p.label ⟶
          RightModule.projectiveNakayamaFGObj (k := k)
            P.augmentation.p) : ℤ)
  have hRankInt :
      (Module.finrank k
        (S.fgObj p.label ⟶
          RightModule.projectiveNakayamaFGObj (k := k)
            P.syzygyPresentation.p) : ℤ) =
        (Module.finrank k
          (S.fgObj p.label ⟶ P.nakayamaKernel (k := k)) : ℤ) +
          (Module.finrank k
            (S.fgObj p.label ⟶
              RightModule.projectiveNakayamaFGObj (k := k)
                P.augmentation.p) : ℤ) := by
    exact_mod_cast hRank
  omega

/-- Ringel Section 2.4(4) in the manuscript's row-vector convention: under
the length-one and regular-Hom vanishings, the Nakayama kernel vector is the
Coxeter transform of the presented module vector. -/
theorem nakayamaKernel_projectiveHomVector_eq_coxeter
    [IsAlgClosed k]
    (S : RightModule.FiniteIndecomposableSkeleton k B)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (P : TwoStepMinimalProjectivePresentation X)
    (hmono : Mono P.differential)
    (hzero : ∀ q : X ⟶ RightModule.rightRegularFGObj (B := B), q = 0) :
    S.projectiveHomVectorFGObj (P.nakayamaKernel (k := k)) =
      Matrix.vecMul (S.projectiveHomVectorFGObj X)
        (CartanCoordinate.coxeterMatrix
          S.projectiveCartanMatrix S.projectiveCartanInverse) := by
  have hX := P.projectiveHomVectorFGObj_eq_sub_of_mono_differential
    S hmono
  have hT := P.nakayamaKernel_projectiveHomVector_eq_sub
    (k := k) S hzero
  have hP₀ := S.projectiveHomVectorFGObj_vecMul_inverseTranspose_mul
    H P.augmentation.p
  have hP₁ := S.projectiveHomVectorFGObj_vecMul_inverseTranspose_mul
    H P.syzygyPresentation.p
  rw [hT,
    S.projectiveHomVectorFGObj_projectiveNakayama
      P.syzygyPresentation.p,
    S.projectiveHomVectorFGObj_projectiveNakayama P.augmentation.p,
    hX]
  unfold CartanCoordinate.coxeterMatrix
  rw [Matrix.vecMul_neg, Matrix.sub_vecMul, hP₀, hP₁]
  simp [sub_eq_add_neg]

end TwoStepMinimalProjectivePresentation

namespace RightModule.FiniteIndecomposableSkeleton

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- The translated source of the chosen sequence, as an object of the full
middle-support subcategory. -/
def rightSequenceSourceSupportObj
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    SupportSubcategory (S := S)
      (S.minimalRightAlmostSplitAt z.1).middle :=
  ⟨S.fgObj (S.rightTranslationLabel z),
    (S.rightSequence_endpointSupport_subset_middle z).1⟩

/-- The chosen kernel inclusion inside the full middle-support
subcategory. -/
def rightSequenceSupportSourceKernelMap
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    rightSequenceSourceSupportObj (S := S) z ⟶
      rightSequenceMiddleSupportObj (S := S) z :=
  ObjectProperty.homMk (S.rightKernelMap z)

/-- The supported source map followed by the supported almost-split map is
zero. -/
theorem rightSequenceSupportSourceKernelMap_comp
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    rightSequenceSupportSourceKernelMap (S := S) z ≫
      rightSequenceSupportMap (S := S) z = 0 := by
  apply ObjectProperty.hom_ext
  change S.rightKernelMap z ≫
    (S.minimalRightAlmostSplitAt z.1).map = 0
  simp [RightModule.FiniteIndecomposableSkeleton.rightKernelMap,
    Category.assoc]

/-- The supported translated source is the actual kernel of the supported
almost-split map. -/
def rightSequenceSupportSourceKernelIsLimit
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    IsLimit (KernelFork.ofι
      (rightSequenceSupportSourceKernelMap (S := S) z)
      (rightSequenceSupportSourceKernelMap_comp (S := S) z)) := by
  let B := S.minimalRightAlmostSplitAt z.1
  let e := S.rightTranslationKernelIso z
  let hAmbient : IsLimit (KernelFork.ofι (S.rightKernelMap z) (by
      change ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map) ≫
        B.map = 0
      simp)) :=
    IsLimit.ofIsoLimit (kernelIsKernel B.map)
      (Fork.ext e (by
        change e.hom ≫ ((S.rightTranslationKernelIso z).inv ≫
          kernel.ι B.map) = kernel.ι B.map
        simp [e]))
  refine Fork.IsLimit.mk' _ fun s ↦ ?_
  have hs : (Fork.ι s).hom ≫ B.map = 0 := by
    have hs' := congrArg (fun f ↦ f.hom) (KernelFork.condition s)
    exact hs'
  let lifted := KernelFork.IsLimit.lift' hAmbient (Fork.ι s).hom hs
  refine ⟨ObjectProperty.homMk lifted.1, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    exact lifted.2
  · intro m hm
    apply ObjectProperty.hom_ext
    apply Fork.IsLimit.hom_ext hAmbient
    have hm' := congrArg (fun f ↦ f.hom) hm
    exact hm'.trans lifted.2.symm

/-- The skeleton representative of the supported translated source is the
selected representative of the support almost-split kernel. -/
def rightSequenceSupportKernelIsoSource
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (P.rightSequenceMiddleSupportSkeleton hA z).fgObj
        (P.rightSequenceSupportKernelLabel hA z) ≅
      (P.rightSequenceMiddleSupportSkeleton hA z).fgObj
        (P.rightSequenceSupportSourceLabel hA z) := by
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let F := (P.supportEquivalence X).functor
  let f := rightSequenceSupportMap (S := S) z
  let c : KernelFork f := KernelFork.ofι
    (rightSequenceSupportSourceKernelMap (S := S) z)
    (rightSequenceSupportSourceKernelMap_comp (S := S) z)
  let hc : IsLimit c :=
    rightSequenceSupportSourceKernelIsLimit (S := S) z
  letI : HasLimit (parallelPair f 0) := HasLimit.mk ⟨c, hc⟩
  let eSub : rightSequenceSourceSupportObj (S := S) z ≅ kernel f :=
    IsLimit.conePointUniqueUpToIso
      (rightSequenceSupportSourceKernelIsLimit (S := S) z)
      (limit.isLimit (parallelPair f 0))
  let eMapped :
      F.obj (rightSequenceSourceSupportObj (S := S) z) ≅
        kernel (F.map f) :=
    (F.mapIso eSub).trans (PreservesKernel.iso F f)
  let ePost : kernel (F.map f) ≅
      kernel (P.rightSequenceSupportSkeletonMap hA z) :=
    kernel.mapIso (F.map f)
      (P.rightSequenceSupportSkeletonMap hA z)
      (Iso.refl _)
      (P.rightSequenceSupportTargetIsoSkeletonFG hA z)
      (by
        simp [rightSequenceSupportSkeletonMap,
          rightSequenceSupportAlgebraMap, f, F, X])
  let eSourceKernel :
      P.supportFGObj X
          (S.fgObj (S.rightTranslationLabel z))
          (S.rightSequence_endpointSupport_subset_middle z).1 ≅
        (P.rightSequenceMiddleSupportSkeleton hA z).fgObj
          (P.rightSequenceSupportKernelLabel hA z) :=
    eMapped.trans (ePost.trans (P.rightSequenceSupportKernelIso hA z))
  exact eSourceKernel.symm.trans
    (P.rightSequenceSupportSourceIsoSkeletonFG hA z)

/-- The selected literal support kernel has the Coxeter transform of the
support endpoint's projective-Hom vector. -/
theorem rightSequenceSupportKernel_coxeter_translate
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (Q : TwoStepMinimalProjectivePresentation
      (P.rightSequenceSupportEndpointFGObj hA z)) :
    let T := P.rightSequenceMiddleSupportSkeleton hA z
    T.projectiveHomVector (P.rightSequenceSupportKernelLabel hA z) =
      Matrix.vecMul
        (T.projectiveHomVector (P.rightSequenceSupportTargetLabel hA z))
        (CartanCoordinate.coxeterMatrix
          T.projectiveCartanMatrix T.projectiveCartanInverse) := by
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.rightSequenceMiddleSupportSkeleton hA z
  have HT : T.HasAcyclicNonzeroNonisomorphisms :=
    P.rightSequenceMiddleSupportAcyclic hA H z
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
  have hcox := Q.nakayamaKernel_projectiveHomVector_eq_coxeter
    (k := k) T HT hmono
      (P.hom_from_rightTarget_to_supportRegular_eq_zero hA H z)
  have he := T.projectiveHomVectorFGObj_iso e
  change T.projectiveHomVectorFGObj
      (P.rightSequenceSupportKernelFGObj hA z) = _
  rw [he]
  exact hcox

/-- Ringel Section 2.4(4) for the literal middle-support quotient: the
projective-Hom vector of the translated source is the Coxeter transform of
the endpoint vector. -/
theorem rightSequenceSupportSource_coxeter_translate
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    let T := P.rightSequenceMiddleSupportSkeleton hA z
    T.projectiveHomVector (P.rightSequenceSupportSourceLabel hA z) =
      Matrix.vecMul
        (T.projectiveHomVector (P.rightSequenceSupportTargetLabel hA z))
        (CartanCoordinate.coxeterMatrix
          T.projectiveCartanMatrix T.projectiveCartanInverse) := by
  let T := P.rightSequenceMiddleSupportSkeleton hA z
  obtain ⟨Q⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (P.rightSequenceSupportEndpointFGObj hA z)
  have hKernel := P.rightSequenceSupportKernel_coxeter_translate hA H z Q
  have he := T.projectiveHomVectorFGObj_iso
    (P.rightSequenceSupportKernelIsoSource hA z)
  change T.projectiveHomVectorFGObj
      (T.fgObj (P.rightSequenceSupportSourceLabel hA z)) = _
  rw [← he]
  exact hKernel

end PrimitiveProjectivePresentation

end RightModule.FiniteIndecomposableSkeleton

end MagnitudeConjecture
