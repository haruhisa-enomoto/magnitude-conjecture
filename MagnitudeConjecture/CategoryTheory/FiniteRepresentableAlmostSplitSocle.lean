import MagnitudeConjecture.CategoryTheory.ExtOneRealization
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableStableHomExt
import MagnitudeConjecture.LinearAlgebra.LocalAlgebraResidue
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The distinguished stable socle extension in a finite functor category

At a nonprojective indecomposable endpoint over an algebraically closed field,
the residue map of the local endomorphism algebra descends to projective-stable
endomorphisms and takes the stable identity to one.  The finite-representable
stable Hom--Ext formula transports this functional to a nonzero extension
class.  Pullback along every nonretraction kills that class, so every short
exact realization has a right almost-split terminal map.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

abbrev FiniteModule :=
  FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k

/-- If a composite is a retraction, its right factor is a retraction. -/
theorem isSplitEpi_right_of_comp
    {W X Y : FiniteModule (k := k) (C := C)}
    (f : W ⟶ X) (g : X ⟶ Y)
    (hfg : IsSplitEpi (f ≫ g)) : IsSplitEpi g := by
  letI : IsSplitEpi (f ≫ g) := hfg
  exact IsSplitEpi.mk'
    { section_ := section_ (f ≫ g) ≫ f
      id := by
        rw [Category.assoc]
        exact IsSplitEpi.id (f ≫ g) }

/-- A nonzero scalar multiple of the identity is a retraction. -/
theorem isSplitEpi_smul_id_of_ne_zero
    (X : FiniteModule (k := k) (C := C)) {c : k} (hc : c ≠ 0) :
    IsSplitEpi (c • 𝟙 X) := by
  exact IsSplitEpi.mk'
    { section_ := c⁻¹ • 𝟙 X
      id := by simp [smul_smul, hc] }

/-- At a scalar-endomorphism object, every nonretraction endomorphism is
zero. -/
theorem endomorphism_eq_zero_of_not_isSplitEpi_of_eq_smul_id
    (X : FiniteModule (k := k) (C := C))
    (hscalar : ∀ r : X ⟶ X, ∃ c : k, c • 𝟙 X = r)
    (r : X ⟶ X) (hr : ¬ IsSplitEpi r) : r = 0 := by
  obtain ⟨c, hc⟩ := hscalar r
  by_cases hczero : c = 0
  · rw [← hc, hczero, zero_smul]
  · exact (hr (hc ▸ isSplitEpi_smul_id_of_ne_zero X hczero)).elim

namespace TwoStepMinimalFiniteRepresentablePresentation

variable
  {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (linearCoyonedaLinearModule (k := k) X)}
  (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (dualLinearYonedaLinearModule (k := k) X))
  {M : FiniteModule (k := k) (C := C)}
  [IsAlgClosed k]
  [HasExt.{w} (FiniteModule (k := k) (C := C))]

/-- The local endomorphism-algebra residue descends to projective-stable
endomorphisms of a nonprojective indecomposable. -/
def stableIdentityFunctional
    (_P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    ProjectiveStable.Hom (k := k) M M →ₗ[k] k :=
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hMind
  (ProjectiveStable.factorSubmodule (k := k) M M).liftQ
    (LocalAlgebraResidue.residueLinearMap k (End M)) (by
      intro f hf
      rw [LinearMap.mem_ker]
      apply (LocalAlgebraResidue.mem_ker_residueLinearMap_iff
        (k := k) (E := End M) f).2
      intro hunit
      letI : IsIso f := (isUnit_iff_isIso f).1 hunit
      obtain ⟨F⟩ := hf
      apply hM
      apply ProjectiveStable.projective_of_id_factorsThroughProjective M
      simpa using F.precomp (inv f))

omit [HasExt.{w} (FiniteModule (k := k) (C := C))] in
@[simp]
theorem stableIdentityFunctional_id
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    P.stableIdentityFunctional hM hMind
        (ProjectiveStable.mk (k := k) (𝟙 M)) = 1 := by
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hMind
  change LocalAlgebraResidue.residueScalar k (1 : End M) = 1
  simpa using LocalAlgebraResidue.residueScalar_algebraMap
    (k := k) (E := End M) 1

/-- The distinguished extension class selected by the stable identity. -/
def stableSocleClass
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    Ext.{w} M (P.nakayamaKernel hI) 1 :=
  (P.stableHomExtLinearEquiv hI M).symm
    (P.stableIdentityFunctional hM hMind)

/-- The distinguished class is nonzero. -/
theorem stableSocleClass_ne_zero
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    P.stableSocleClass hI hM hMind ≠ 0 := by
  intro hzero
  have hvalue := LinearMap.congr_fun
    (congrArg (P.stableHomExtLinearEquiv hI M) hzero)
    (ProjectiveStable.mk (k := k) (𝟙 M))
  rw [stableSocleClass, LinearEquiv.apply_symm_apply] at hvalue
  simp only [map_zero, LinearMap.zero_apply] at hvalue
  rw [P.stableIdentityFunctional_id hM hMind] at hvalue
  exact one_ne_zero hvalue

/-- Every nonretraction pullback of the distinguished class vanishes. -/
theorem pullback_stableSocleClass_eq_zero_of_not_isSplitEpi
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {Y : FiniteModule (k := k) (C := C)} (g : Y ⟶ M)
    (hg : ¬ IsSplitEpi g) :
    (Ext.mk₀ g).comp (P.stableSocleClass hI hM hMind)
      (zero_add 1) = 0 := by
  apply (P.stableHomExtLinearEquiv hI Y).injective
  apply LinearMap.ext
  intro a
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [P.stableHomExtLinearEquiv_naturality hI]
  simp only [map_zero, LinearMap.zero_apply]
  rw [stableSocleClass, LinearEquiv.apply_symm_apply]
  have hcomp : ¬ IsSplitEpi (f ≫ g) := by
    intro hsplit
    exact hg (isSplitEpi_right_of_comp f g hsplit)
  change P.stableIdentityFunctional hM hMind
    (ProjectiveStable.mk (k := k) (f ≫ g)) = 0
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hMind
  change LocalAlgebraResidue.residueScalar k (End.of (f ≫ g)) = 0
  exact (LinearMap.mem_ker.mp
    ((LocalAlgebraResidue.mem_ker_residueLinearMap_iff
      (k := k) (E := End M) (End.of (f ≫ g))).2 (by
        intro hunit
        letI : IsIso (f ≫ g) := (isUnit_iff_isIso (f ≫ g)).1 hunit
        exact hcomp inferInstance)))

omit [IsAlgClosed k] in
/-- A nonzero extension class annihilated by all nonretraction pullbacks
makes every representing short exact sequence right almost split. -/
theorem ShortComplex.ShortExact.isRightAlmostSplit_of_extClass_annihilator
    {S : ShortComplex (FiniteModule (k := k) (C := C))}
    (hS : S.ShortExact)
    (hne : hS.extClass ≠ 0)
    (hannihilates :
      ∀ {Y : FiniteModule (k := k) (C := C)} (g : Y ⟶ S.X₃),
        ¬ IsSplitEpi g →
          (Ext.mk₀ g).comp hS.extClass (zero_add 1) = 0) :
    IsRightAlmostSplit S.g := by
  constructor
  · intro hsplit
    letI : IsSplitEpi S.g := hsplit
    apply hne
    calc
      hS.extClass =
          (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) := by simp
      _ = (Ext.mk₀ (section_ S.g ≫ S.g)).comp
          hS.extClass (zero_add 1) := by rw [IsSplitEpi.id S.g]
      _ = (Ext.mk₀ (section_ S.g)).comp
          ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1))
          (zero_add 1) := by rw [Ext.mk₀_comp_mk₀_assoc]
      _ = 0 := by simp
  · intro Y g hg
    obtain ⟨x₂, hx₂⟩ :=
      Ext.covariant_sequence_exact₃
        (X := Y) hS (Ext.mk₀ g)
        (rfl : 0 + 1 = 1) (hannihilates g hg)
    refine ⟨Ext.addEquiv₀ x₂, ?_⟩
    apply (Ext.mk₀_bijective Y S.X₃).1
    rw [← Ext.mk₀_comp_mk₀]
    simpa using hx₂

/-- A realization of the distinguished stable socle class has right
almost-split quotient map. -/
theorem stableSocleClass_realization_isRightAlmostSplit
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {E : FiniteModule (k := k) (C := C)}
    (i : P.nakayamaKernel hI ⟶ E) (q : E ⟶ M)
    (zero : i ≫ q = 0)
    (hS : (ShortComplex.mk i q zero).ShortExact)
    (hclass : hS.extClass = P.stableSocleClass hI hM hMind) :
    IsRightAlmostSplit q := by
  apply ShortComplex.ShortExact.isRightAlmostSplit_of_extClass_annihilator hS
  · rw [hclass]
    exact P.stableSocleClass_ne_zero hI hM hMind
  · intro Y g hg
    rw [hclass]
    exact P.pullback_stableSocleClass_eq_zero_of_not_isSplitEpi
      hI hM hMind g hg

/-- The distinguished class has a realization whose quotient map is right
almost split. -/
theorem exists_stableSocleClass_realization_rightAlmostSplit
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    ∃ (E : FiniteModule (k := k) (C := C))
      (i : P.nakayamaKernel hI ⟶ E) (q : E ⟶ M)
      (zero : i ≫ q = 0)
      (hS : (ShortComplex.mk i q zero).ShortExact),
      hS.extClass = P.stableSocleClass hI hM hMind ∧
        IsRightAlmostSplit q := by
  letI : EnoughProjectives (FiniteModule (k := k) (C := C)) :=
    enoughProjectives_of_finiteRepresentables hP
  obtain ⟨E, i, q, zero, hS, hclass⟩ :=
    ExtOneRealization.exists_shortExact_with_extClass_eq M
      (P.nakayamaKernel hI) (P.stableSocleClass hI hM hMind)
  exact ⟨E, i, q, zero, hS, hclass,
    P.stableSocleClass_realization_isRightAlmostSplit
      hI hM hMind i q zero hS hclass⟩

end TwoStepMinimalFiniteRepresentablePresentation
end MagnitudeConjecture.CoveringHom
