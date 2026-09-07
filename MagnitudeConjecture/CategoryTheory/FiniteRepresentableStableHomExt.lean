import MagnitudeConjecture.Algebra.CoefficientDual
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableAuslanderTranspose
import MagnitudeConjecture.CategoryTheory.ProjectiveStableHom
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Stable Hom--Ext duality for finite linear-module categories

For a literal two-step finite-representable projective presentation

`P₁ ⟶ P₀ ⟶ M`,

this file proves the presentation-dependent Auslander--Reiten formula

`Ext¹(Y, ker(νP₁ ⟶ νP₀)) ≃ Dₖ stableHom(M,Y)`.

The proof uses the finite-matrix Nakayama--Hom equivalence and the one-sided
categorical projective-stable quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.CoveringHom
namespace TwoStepMinimalFiniteRepresentablePresentation

universe u v w

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable
  {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (linearCoyonedaLinearModule (k := k) X)}
  (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (dualLinearYonedaLinearModule (k := k) X))
variable
  {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}

local instance : Module.Injective k k :=
  Module.injective_of_isSemisimpleRing k k

/-- Precomposition with the augmentation `P₀ ⟶ M`. -/
def augmentationPrecompLinear
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (M ⟶ Y) →ₗ[k] (P.augmentation.source ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y P.augmentation.f

/-- Precomposition with the first differential `P₁ ⟶ P₀`. -/
def differentialPrecompLinear
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (P.augmentation.source ⟶ Y) →ₗ[k]
      (P.syzygyPresentation.source ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y
    P.toTwoStepFiniteRepresentablePresentation.differential

@[simp]
theorem augmentationPrecompLinear_apply
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (f : M ⟶ Y) :
    P.augmentationPrecompLinear Y f = P.augmentation.f ≫ f :=
  rfl

@[simp]
theorem differentialPrecompLinear_apply
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (f : P.augmentation.source ⟶ Y) :
    P.differentialPrecompLinear Y f =
      P.toTwoStepFiniteRepresentablePresentation.differential ≫ f :=
  rfl

/-- Precomposition with the epimorphic augmentation is injective. -/
theorem augmentationPrecompLinear_injective
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Function.Injective (P.augmentationPrecompLinear Y) := by
  intro f g h
  apply (cancel_epi P.augmentation.f).1
  exact h

/-- Applying `Hom(-,Y)` to the projective presentation is exact at
`Hom(P₀,Y)`. -/
theorem range_augmentationPrecompLinear
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    LinearMap.range (P.augmentationPrecompLinear Y) =
      LinearMap.ker (P.differentialPrecompLinear Y) := by
  let Q := P.toTwoStepMinimalProjectivePresentation
  change LinearMap.range
      (CategoryTheory.Linear.leftComp k Y Q.augmentation.f) =
    LinearMap.ker
      (CategoryTheory.Linear.leftComp k Y Q.differential)
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    change Q.differential ≫ Q.augmentation.f ≫ f = 0
    rw [← Category.assoc, Q.differential_comp_augmentation, zero_comp]
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    letI : Epi Q.presentationComplex.g := by
      dsimp [TwoStepMinimalProjectivePresentation.presentationComplex]
      infer_instance
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc'
      (Q.presentationComplex_exact.gIsCokernel) f hf
    exact ⟨g, hg⟩

/-- The Nakayama boundary pairing before quotienting either variable. -/
def ordinaryBoundaryLinear
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (Y ⟶ P.nakayamaCokernel hI) →ₗ[k] ((M ⟶ Y) →ₗ[k] k) :=
  (LinearMap.lcomp k k (P.augmentationPrecompLinear Y)).comp
    ((finiteRepresentableSumNakayamaHomEquiv hP hI
      P.augmentation.toFiniteRepresentablePresentation.matrixObject Y).toLinearMap.comp
      (CategoryTheory.Linear.rightComp k Y (P.nakayamaCokernelι hI)))

@[simp]
theorem ordinaryBoundaryLinear_apply
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (c : Y ⟶ P.nakayamaCokernel hI) (f : M ⟶ Y) :
    P.ordinaryBoundaryLinear hI Y c f =
      finiteRepresentableSumNakayamaHomEquiv hP hI
        P.augmentation.toFiniteRepresentablePresentation.matrixObject Y
        (c ≫ P.nakayamaCokernelι hI) (P.augmentation.f ≫ f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projective matrix functor sends the named representing differential
to the actual first differential of the presentation. -/
theorem map_representingDifferential
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    (finiteProjectiveRepresentableSumFunctor (k := k) hP).map
        P.representingDifferential =
      P.toTwoStepFiniteRepresentablePresentation.differential := by
  exact P.toTwoStepFiniteRepresentablePresentation.map_matrixDifferential

set_option backward.isDefEq.respectTransparency false in
/-- The mapped representing differential followed by the augmentation is
zero. -/
theorem map_representingDifferential_comp_augmentation
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    (finiteProjectiveRepresentableSumFunctor (k := k) hP).map
      P.representingDifferential ≫ P.augmentation.f = 0 := by
  rw [P.map_representingDifferential]
  exact P.toTwoStepFiniteRepresentablePresentation.differential_comp_augmentation

/-- The finite-matrix Nakayama--Hom comparison intertwines the displayed
projective and Nakayama differentials. -/
theorem finiteRepresentableSumNakayamaHomEquiv_differential
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (a : Y ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject)
    (f : P.augmentation.source ⟶ Y) :
    finiteRepresentableSumNakayamaHomEquiv hP hI
        P.augmentation.toFiniteRepresentablePresentation.matrixObject Y
        (a ≫ P.nakayamaDifferential hI) f =
      finiteRepresentableSumNakayamaHomEquiv hP hI
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject Y
        a ((finiteProjectiveRepresentableSumFunctor (k := k) hP).map
          P.representingDifferential ≫ f) := by
  exact finiteRepresentableSumNakayamaHomEquiv_projectiveNaturality
    hP hI P.representingDifferential Y a f

/-- Naturality of the unquotiented boundary pairing in the variable module. -/
theorem ordinaryBoundaryLinear_naturality
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    {Y Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (g : Y ⟶ Z) (c : Z ⟶ P.nakayamaCokernel hI) (f : M ⟶ Y) :
    P.ordinaryBoundaryLinear hI Y (g ≫ c) f =
      P.ordinaryBoundaryLinear hI Z c (f ≫ g) := by
  exact finiteRepresentableSumNakayamaHomEquiv_naturality
    hP hI P.augmentation.toFiniteRepresentablePresentation.matrixObject g
    (c ≫ P.nakayamaCokernelι hI) (P.augmentation.f ≫ f)

/-- The pairing kills the displayed injective-presentation coboundaries. -/
theorem ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (c : Y ⟶ P.nakayamaCokernel hI)
    (hc : c ∈ P.nakayamaExtPresentationRange hI Y) :
    P.ordinaryBoundaryLinear hI Y c = 0 := by
  obtain ⟨a, rfl⟩ :=
    (P.mem_nakayamaExtPresentationRange_iff hI Y c).mp hc
  apply LinearMap.ext
  intro f
  rw [ordinaryBoundaryLinear_apply, Category.assoc,
    P.nakayamaCokernelπ_comp_ι]
  rw [P.finiteRepresentableSumNakayamaHomEquiv_differential hI]
  rw [← Category.assoc,
    P.map_representingDifferential_comp_augmentation]
  simp

/-- The pairing kills maps from `M` which factor through a projective. -/
theorem ordinaryBoundaryLinear_apply_eq_zero_of_factorsThroughProjective
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (c : Y ⟶ P.nakayamaCokernel hI) {f : M ⟶ Y}
    (hf : ProjectiveStable.FactorsThroughProjective f) :
    P.ordinaryBoundaryLinear hI Y c f = 0 := by
  letI : Projective hf.middle := hf.projective
  let a : hf.middle ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject :=
    Projective.factorThru (hf.right ≫ c) (P.nakayamaCokernelπ hI)
  have ha : a ≫ P.nakayamaCokernelπ hI = hf.right ≫ c :=
    Projective.factorThru_comp _ _
  rw [ordinaryBoundaryLinear_apply, ← hf.fac, ← Category.assoc]
  rw [← finiteRepresentableSumNakayamaHomEquiv_naturality
    hP hI P.augmentation.toFiniteRepresentablePresentation.matrixObject
    hf.right (c ≫ P.nakayamaCokernelι hI)
    (P.augmentation.f ≫ hf.left)]
  rw [← Category.assoc, ← ha, Category.assoc,
    P.nakayamaCokernelπ_comp_ι]
  rw [P.finiteRepresentableSumNakayamaHomEquiv_differential hI]
  rw [← Category.assoc,
    P.map_representingDifferential_comp_augmentation]
  simp

/-- The boundary functional descended to projective-stable Hom. -/
def stableBoundary
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (c : Y ⟶ P.nakayamaCokernel hI) :
    ProjectiveStable.Hom (k := k) M Y →ₗ[k] k :=
  (ProjectiveStable.factorSubmodule (k := k) M Y).liftQ
    (P.ordinaryBoundaryLinear hI Y c) (by
      intro f hf
      rw [LinearMap.mem_ker]
      obtain ⟨hfactor⟩ := hf
      exact P.ordinaryBoundaryLinear_apply_eq_zero_of_factorsThroughProjective
        hI Y c hfactor)

@[simp]
theorem stableBoundary_mk
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (c : Y ⟶ P.nakayamaCokernel hI) (f : M ⟶ Y) :
    P.stableBoundary hI Y c (ProjectiveStable.mk (k := k) f) =
      P.ordinaryBoundaryLinear hI Y c f :=
  rfl

/-- The stable boundary, linear in its presentation representative. -/
def stableBoundaryLinear
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (Y ⟶ P.nakayamaCokernel hI) →ₗ[k]
      (ProjectiveStable.Hom (k := k) M Y →ₗ[k] k) where
  toFun := P.stableBoundary hI Y
  map_add' c c' := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change P.ordinaryBoundaryLinear hI Y (c + c') f =
      P.ordinaryBoundaryLinear hI Y c f +
        P.ordinaryBoundaryLinear hI Y c' f
    simp
  map_smul' a c := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change P.ordinaryBoundaryLinear hI Y (a • c) f =
      a * P.ordinaryBoundaryLinear hI Y c f
    simp

variable [HasExt.{w}
  (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]

/-- The pairing after quotienting its presentation variable. -/
def boundaryQuotientLinear
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    ((Y ⟶ P.nakayamaCokernel hI) ⧸
        P.nakayamaExtPresentationRange hI Y) →ₗ[k]
      (ProjectiveStable.Hom (k := k) M Y →ₗ[k] k) :=
  (P.nakayamaExtPresentationRange hI Y).liftQ
    (P.stableBoundaryLinear hI Y) (by
      intro c hc
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro q
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact LinearMap.congr_fun
        (P.ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange
          hI Y c hc) f)

@[simp]
theorem boundaryQuotientLinear_mk_mk
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (c : Y ⟶ P.nakayamaCokernel hI) (f : M ⟶ Y) :
    P.boundaryQuotientLinear hI Y (Submodule.Quotient.mk c)
        (ProjectiveStable.mk (k := k) f) =
      P.ordinaryBoundaryLinear hI Y c f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the unquotiented boundary is exactly the displayed
injective-presentation range. -/
theorem ker_ordinaryBoundaryLinear
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    LinearMap.ker (P.ordinaryBoundaryLinear hI Y) =
      P.nakayamaExtPresentationRange hI Y := by
  apply le_antisymm
  · intro c hc
    let phi : (P.augmentation.source ⟶ Y) →ₗ[k] k :=
      finiteRepresentableSumNakayamaHomEquiv hP hI
        P.augmentation.toFiniteRepresentablePresentation.matrixObject Y
        (c ≫ P.nakayamaCokernelι hI)
    have hphi : phi ∈ CoefficientDual.annihilator
        (E := k) (LinearMap.ker (P.differentialPrecompLinear Y)) := by
      rw [← P.range_augmentationPrecompLinear Y]
      rw [CoefficientDual.mem_annihilator_iff]
      intro f hf
      obtain ⟨g, rfl⟩ := hf
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hc) g
    have hphiRange : phi ∈ LinearMap.range
        (LinearMap.lcomp k k (P.differentialPrecompLinear Y)) := by
      rw [CoefficientDual.range_lcomp_eq_annihilator_ker]
      exact hphi
    obtain ⟨psi, hpsi⟩ := hphiRange
    let a : Y ⟶
        (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
          P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject :=
      (finiteRepresentableSumNakayamaHomEquiv hP hI
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
        Y).symm psi
    have ha : a ≫ P.nakayamaDifferential hI =
        c ≫ P.nakayamaCokernelι hI := by
      apply (finiteRepresentableSumNakayamaHomEquiv hP hI
        P.augmentation.toFiniteRepresentablePresentation.matrixObject
        Y).injective
      apply LinearMap.ext
      intro f
      rw [P.finiteRepresentableSumNakayamaHomEquiv_differential hI]
      rw [P.map_representingDifferential]
      rw [show finiteRepresentableSumNakayamaHomEquiv hP hI
          P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
          Y a = psi by simp [a]]
      change psi (P.differentialPrecompLinear Y f) = phi f
      exact LinearMap.congr_fun hpsi f
    rw [P.mem_nakayamaExtPresentationRange_iff hI Y]
    refine ⟨a, ?_⟩
    apply (cancel_mono (P.nakayamaCokernelι hI)).1
    rw [Category.assoc, P.nakayamaCokernelπ_comp_ι]
    exact ha
  · intro c hc
    rw [LinearMap.mem_ker]
    exact P.ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange
      hI Y c hc

/-- The descended boundary is injective. -/
theorem boundaryQuotientLinear_injective
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Function.Injective (P.boundaryQuotientLinear hI Y) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.Quotient.mk_eq_zero]
  rw [← P.ker_ordinaryBoundaryLinear hI Y]
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro f
  have hvalue := LinearMap.congr_fun hq
    (ProjectiveStable.mk (k := k) f)
  exact hvalue

set_option backward.isDefEq.respectTransparency false in
/-- Every functional on projective-stable Hom is a boundary functional. -/
theorem boundaryQuotientLinear_surjective
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Function.Surjective (P.boundaryQuotientLinear hI Y) := by
  intro lambda
  let phiM : (M ⟶ Y) →ₗ[k] k :=
    lambda.comp (ProjectiveStable.mk (k := k))
  obtain ⟨phi₀, hphi₀⟩ := Module.Injective.extension_property k k
    (M ⟶ Y) (P.augmentation.source ⟶ Y)
    (P.augmentationPrecompLinear Y)
    (P.augmentationPrecompLinear_injective Y) phiM
  let a₀ : Y ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.augmentation.toFiniteRepresentablePresentation.matrixObject :=
    (finiteRepresentableSumNakayamaHomEquiv hP hI
      P.augmentation.toFiniteRepresentablePresentation.matrixObject Y).symm
        phi₀
  let Q : FiniteRepresentablePresentation hP Y :=
    Classical.choice (finiteRepresentablePresentation_nonempty hP Y)
  let psi₀ : (P.augmentation.source ⟶ Q.source) →ₗ[k] k :=
    finiteRepresentableSumNakayamaHomEquiv hP hI
      P.augmentation.toFiniteRepresentablePresentation.matrixObject
      Q.source (Q.f ≫ a₀)
  have hpsi₀ : psi₀ ∈ CoefficientDual.annihilator
      (E := k) (LinearMap.ker
        (P.differentialPrecompLinear Q.source)) := by
    rw [← P.range_augmentationPrecompLinear Q.source]
    rw [CoefficientDual.mem_annihilator_iff]
    intro b hb
    obtain ⟨f, rfl⟩ := hb
    have hstable : ProjectiveStable.mk (k := k) (f ≫ Q.f) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero
        (ProjectiveStable.factorSubmodule (k := k) M Y)).2
      exact ⟨{
        middle := Q.source
        projective := inferInstance
        left := f
        right := Q.f
        fac := rfl }⟩
    calc
      psi₀ (P.augmentationPrecompLinear Q.source f) =
          finiteRepresentableSumNakayamaHomEquiv hP hI
            P.augmentation.toFiniteRepresentablePresentation.matrixObject
            Y a₀ ((P.augmentation.f ≫ f) ≫ Q.f) := by
        exact finiteRepresentableSumNakayamaHomEquiv_naturality
          hP hI
          P.augmentation.toFiniteRepresentablePresentation.matrixObject
          Q.f a₀ (P.augmentation.f ≫ f)
      _ = phi₀ (P.augmentationPrecompLinear Y (f ≫ Q.f)) := by
        simp only [a₀, LinearEquiv.apply_symm_apply,
          augmentationPrecompLinear_apply, Category.assoc]
        rfl
      _ = phiM (f ≫ Q.f) := LinearMap.congr_fun hphi₀ (f ≫ Q.f)
      _ = lambda (ProjectiveStable.mk (k := k) (f ≫ Q.f)) := rfl
      _ = 0 := by rw [hstable, map_zero]
  have hpsi₀Range : psi₀ ∈ LinearMap.range
      (LinearMap.lcomp k k (P.differentialPrecompLinear Q.source)) := by
    rw [CoefficientDual.range_lcomp_eq_annihilator_ker]
    exact hpsi₀
  obtain ⟨psi₁, hpsi₁⟩ := hpsi₀Range
  let a₁ : Q.source ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject :=
    (finiteRepresentableSumNakayamaHomEquiv hP hI
      P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
      Q.source).symm psi₁
  have ha₁ : a₁ ≫ P.nakayamaDifferential hI = Q.f ≫ a₀ := by
    apply (finiteRepresentableSumNakayamaHomEquiv hP hI
      P.augmentation.toFiniteRepresentablePresentation.matrixObject
      Q.source).injective
    apply LinearMap.ext
    intro f
    rw [P.finiteRepresentableSumNakayamaHomEquiv_differential hI]
    rw [P.map_representingDifferential]
    rw [show finiteRepresentableSumNakayamaHomEquiv hP hI
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
        Q.source a₁ = psi₁ by simp [a₁]]
    change psi₁ (P.differentialPrecompLinear Q.source f) = psi₀ f
    exact LinearMap.congr_fun hpsi₁ f
  have ha₀zero : a₀ ≫ cokernel.π (P.nakayamaCokernelι hI) = 0 := by
    apply (cancel_epi Q.f).1
    simp only [comp_zero]
    calc
      Q.f ≫ a₀ ≫ cokernel.π (P.nakayamaCokernelι hI) =
          (Q.f ≫ a₀) ≫ cokernel.π (P.nakayamaCokernelι hI) :=
        (Category.assoc _ _ _).symm
      _ = (a₁ ≫ P.nakayamaDifferential hI) ≫
          cokernel.π (P.nakayamaCokernelι hI) := by rw [ha₁]
      _ = 0 := by
        rw [← P.nakayamaCokernelπ_comp_ι]
        simp only [Category.assoc, cokernel.condition, comp_zero]
  let c : Y ⟶ P.nakayamaCokernel hI :=
    Abelian.monoLift (P.nakayamaCokernelι hI) a₀ ha₀zero
  refine ⟨Submodule.Quotient.mk c, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change P.ordinaryBoundaryLinear hI Y c f =
    lambda (ProjectiveStable.mk (k := k) f)
  rw [ordinaryBoundaryLinear_apply]
  rw [show c ≫ P.nakayamaCokernelι hI = a₀ by
    exact Abelian.monoLift_comp _ _ _]
  rw [show finiteRepresentableSumNakayamaHomEquiv hP hI
      P.augmentation.toFiniteRepresentablePresentation.matrixObject Y a₀ =
        phi₀ by simp [a₀]]
  exact LinearMap.congr_fun hphi₀ f

/-- The concrete Ext presentation quotient is the coefficient dual of
projective-stable Hom. -/
def boundaryQuotientLinearEquiv
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    ((Y ⟶ P.nakayamaCokernel hI) ⧸
        P.nakayamaExtPresentationRange hI Y) ≃ₗ[k]
      (ProjectiveStable.Hom (k := k) M Y →ₗ[k] k) :=
  LinearEquiv.ofBijective (P.boundaryQuotientLinear hI Y)
    ⟨P.boundaryQuotientLinear_injective hI Y,
      P.boundaryQuotientLinear_surjective hI Y⟩

/-- The fixed-presentation stable Auslander--Reiten formula in the finite
linear-module category. -/
def stableHomExtLinearEquiv
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Ext.{w} Y (P.nakayamaKernel hI) 1 ≃ₗ[k]
      (ProjectiveStable.Hom (k := k) M Y →ₗ[k] k) :=
  (P.nakayamaExtOneQuotientLinearEquiv hI Y).symm.trans
    (P.boundaryQuotientLinearEquiv hI Y)

/-- Naturality of the stable Auslander--Reiten formula under pullback. -/
theorem stableHomExtLinearEquiv_naturality
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    {Y Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (g : Y ⟶ Z) (xi : Ext.{w} Z (P.nakayamaKernel hI) 1)
    (a : ProjectiveStable.Hom (k := k) M Y) :
    P.stableHomExtLinearEquiv hI Y
        ((Ext.mk₀ g).comp xi (zero_add 1)) a =
      P.stableHomExtLinearEquiv hI Z xi
        (ProjectiveStable.postcomp (k := k) M g a) := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    ((P.nakayamaExtOneQuotientLinearEquiv hI Z).symm xi)
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [stableHomExtLinearEquiv, LinearEquiv.trans_apply,
    P.nakayamaExtOneQuotientLinearEquiv_symm_pullback hI]
  rw [← hc]
  change P.boundaryQuotientLinearEquiv hI Y
      (Submodule.Quotient.mk (g ≫ c))
        (ProjectiveStable.mk (k := k) f) = _
  rw [show P.stableHomExtLinearEquiv hI Z xi =
      P.boundaryQuotientLinearEquiv hI Z
        (Submodule.Quotient.mk c) by
    simp [stableHomExtLinearEquiv, ← hc]]
  change P.boundaryQuotientLinear hI Y
      (Submodule.Quotient.mk (g ≫ c))
        (ProjectiveStable.mk (k := k) f) =
    P.boundaryQuotientLinear hI Z
      (Submodule.Quotient.mk c)
        (ProjectiveStable.mk (k := k) (f ≫ g))
  rw [boundaryQuotientLinear_mk_mk, boundaryQuotientLinear_mk_mk]
  exact P.ordinaryBoundaryLinear_naturality hI g c f

end TwoStepMinimalFiniteRepresentablePresentation
end MagnitudeConjecture.CoveringHom
