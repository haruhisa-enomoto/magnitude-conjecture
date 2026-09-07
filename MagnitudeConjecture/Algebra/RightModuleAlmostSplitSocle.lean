import MagnitudeConjecture.Algebra.RightModuleStableHomExt
import MagnitudeConjecture.Algebra.RightModuleFiniteType
import MagnitudeConjecture.CategoryTheory.FGExtRealization
import MagnitudeConjecture.LinearAlgebra.LocalAlgebraResidue
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The distinguished stable socle extension

At a nonprojective indecomposable endpoint over an algebraically closed
field, the residue map of the local endomorphism algebra descends to stable
endomorphisms and takes the stable identity to one.  Stable Hom--Ext duality
transports this functional to a nonzero extension class whose pullback along
every nonretraction vanishes.  Consequently every short exact sequence
realizing the class has right almost-split terminal map.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture

universe u w

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

/-- If a composite is a retraction, its right factor is a retraction. -/
theorem isSplitEpi_right_of_comp
    {W X Y : FGModuleCat.{u} Bᵐᵒᵖ} (f : W ⟶ X) (g : X ⟶ Y)
    (hfg : IsSplitEpi (f ≫ g)) : IsSplitEpi g := by
  letI : IsSplitEpi (f ≫ g) := hfg
  exact IsSplitEpi.mk'
    { section_ := section_ (f ≫ g) ≫ f
      id := by
        rw [Category.assoc]
        exact IsSplitEpi.id (f ≫ g) }

/-- Over a field, a nonzero scalar multiple of the identity is a split
epimorphism. -/
theorem isSplitEpi_smul_id_of_ne_zero
    (X : FGModuleCat.{u} Bᵐᵒᵖ) {c : k} (hc : c ≠ 0) :
    IsSplitEpi (c • 𝟙 X) := by
  exact IsSplitEpi.mk'
    { section_ := c⁻¹ • 𝟙 X
      id := by simp [smul_smul, hc] }

noncomputable local instance fgEndFiniteDimensional
    (X : FGModuleCat.{u} Bᵐᵒᵖ) :
    FiniteDimensional k (End X) := by
  change FiniteDimensional k (X ⟶ X)
  exact
    RightModule.FiniteIndecomposableSkeleton.fgModuleCatHomFinite
      (k := k) (A := B) X X

include k in
/-- A finitely generated module with indecomposable underlying object has
local categorical endomorphism ring. -/
theorem fgEnd_isLocalRing_of_indecomposable
    (X : FGModuleCat.{u} Bᵐᵒᵖ) (hX : Indecomposable X) :
    IsLocalRing (End X) := by
  have hModule :=
    (RightModule.FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := B) X).2 hX
  have hlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := B) X
  letI : Nontrivial X := hModule.nontrivial
  letI : IsLocalRing (Module.End Bᵐᵒᵖ X) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      hlength hModule
  exact RingEquiv.isLocalRing_noncomm
    (RightModule.FiniteIndecomposableSkeleton.fgEndModuleEndRingEquiv
      (A := B) X).symm

namespace TwoStepMinimalProjectivePresentation

variable {X : FGModuleCat.{u} Bᵐᵒᵖ}
variable [HasExt.{w} (FGModuleCat.{u} Bᵐᵒᵖ)]
variable [IsAlgClosed k]

/-- The local endomorphism-algebra residue descends to projective-stable
endomorphisms of a nonprojective indecomposable module. -/
def stableIdentityFunctional
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X) (hXind : Indecomposable X) :
    RightModule.projectiveStableHom (k := k) X X →ₗ[k] k :=
  letI : IsLocalRing (End X) :=
    fgEnd_isLocalRing_of_indecomposable (k := k) X hXind
  (RightModule.projectiveFactorSubmodule (k := k) X X).liftQ
    (LocalAlgebraResidue.residueLinearMap k (End X)) (by
      intro f hf
      rw [LinearMap.mem_ker]
      apply (LocalAlgebraResidue.mem_ker_residueLinearMap_iff
        (k := k) (E := End X) f).2
      intro hunit
      letI : IsIso f := (isUnit_iff_isIso f).1 hunit
      obtain ⟨F⟩ := hf
      apply hX
      apply RightModule.projective_of_id_factorsThroughProjective X
      simpa using F.precomp (inv f))

@[simp]
theorem stableIdentityFunctional_id
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X) (hXind : Indecomposable X) :
    P.stableIdentityFunctional (k := k) hX hXind
        (RightModule.projectiveStableClass (k := k) (𝟙 X)) = 1 := by
  letI : IsLocalRing (End X) :=
    fgEnd_isLocalRing_of_indecomposable (k := k) X hXind
  change LocalAlgebraResidue.residueScalar k (1 : End X) = 1
  simpa using LocalAlgebraResidue.residueScalar_algebraMap
    (k := k) (E := End X) 1

/-- The distinguished extension class selected by the stable identity. -/
def stableSocleClass
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X) (hXind : Indecomposable X) :
    Ext.{w} X (P.nakayamaKernel (k := k)) 1 :=
  (P.stableHomExtLinearEquiv (k := k) X).symm
    (P.stableIdentityFunctional (k := k) hX hXind)

/-- The distinguished class is nonzero. -/
theorem stableSocleClass_ne_zero
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X) (hXind : Indecomposable X) :
    P.stableSocleClass (k := k) hX hXind ≠ 0 := by
  intro hzero
  have hvalue := LinearMap.congr_fun
    (congrArg (P.stableHomExtLinearEquiv (k := k) X) hzero)
    (RightModule.projectiveStableClass (k := k) (𝟙 X))
  rw [stableSocleClass, LinearEquiv.apply_symm_apply] at hvalue
  simp only [map_zero, LinearMap.zero_apply] at hvalue
  rw [P.stableIdentityFunctional_id (k := k) hX hXind] at hvalue
  exact one_ne_zero hvalue

/-- Every nonretraction pullback of the distinguished class vanishes. -/
theorem pullback_stableSocleClass_eq_zero_of_not_isSplitEpi
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X) (hXind : Indecomposable X)
    {Y : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ X)
    (hg : ¬ IsSplitEpi g) :
    (Ext.mk₀ g).comp (P.stableSocleClass (k := k) hX hXind)
      (zero_add 1) = 0 := by
  apply (P.stableHomExtLinearEquiv (k := k) Y).injective
  apply LinearMap.ext
  intro a
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [P.stableHomExtLinearEquiv_naturality (k := k)]
  simp only [map_zero, LinearMap.zero_apply]
  rw [stableSocleClass, LinearEquiv.apply_symm_apply]
  have hcomp : ¬ IsSplitEpi (f ≫ g) := by
    intro hsplit
    exact hg (isSplitEpi_right_of_comp f g hsplit)
  change P.stableIdentityFunctional (k := k) hX hXind
    (RightModule.projectiveStableClass (k := k) (f ≫ g)) = 0
  letI : IsLocalRing (End X) :=
    fgEnd_isLocalRing_of_indecomposable (k := k) X hXind
  change LocalAlgebraResidue.residueScalar k (End.of (f ≫ g)) = 0
  exact LinearMap.mem_ker.mp
    ((LocalAlgebraResidue.mem_ker_residueLinearMap_iff
      (k := k) (E := End X) (End.of (f ≫ g))).2 (by
        intro hunit
        letI : IsIso (f ≫ g) := (isUnit_iff_isIso (f ≫ g)).1 hunit
        exact hcomp inferInstance))

/-- A nonzero extension class annihilated by all nonretraction pullbacks
makes every representing short exact sequence right almost split. -/
theorem ShortComplex.ShortExact.isRightAlmostSplit_of_extClass_annihilator
    {S : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ)} (hS : S.ShortExact)
    (hne : hS.extClass ≠ 0)
    (hannihilates :
      ∀ {Y : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ S.X₃),
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
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X) (hXind : Indecomposable X)
    {E : FGModuleCat.{u} Bᵐᵒᵖ}
    (i : P.nakayamaKernel (k := k) ⟶ E) (q : E ⟶ X)
    (zero : i ≫ q = 0)
    (hS : (ShortComplex.mk i q zero).ShortExact)
    (hclass : hS.extClass = P.stableSocleClass (k := k) hX hXind) :
    IsRightAlmostSplit q := by
  apply ShortComplex.ShortExact.isRightAlmostSplit_of_extClass_annihilator hS
  · rw [hclass]
    exact P.stableSocleClass_ne_zero (k := k) hX hXind
  · intro Y g hg
    rw [hclass]
    exact P.pullback_stableSocleClass_eq_zero_of_not_isSplitEpi
      (k := k) hX hXind g hg

/-- The distinguished class has a finite realization, and its quotient map is
right almost split. -/
theorem exists_stableSocleClass_realization_rightAlmostSplit
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X) (hXind : Indecomposable X) :
    ∃ (E : FGModuleCat.{u} Bᵐᵒᵖ)
      (i : P.nakayamaKernel (k := k) ⟶ E) (q : E ⟶ X)
      (zero : i ≫ q = 0)
      (hS : (ShortComplex.mk i q zero).ShortExact),
      hS.extClass = P.stableSocleClass (k := k) hX hXind ∧
        IsRightAlmostSplit q := by
  obtain ⟨E, i, q, zero, hS, hclass⟩ :=
    FGExtRealization.exists_shortExact_with_extClass_eq X
      (P.nakayamaKernel (k := k))
        (P.stableSocleClass (k := k) hX hXind)
  exact ⟨E, i, q, zero, hS, hclass,
    P.stableSocleClass_realization_isRightAlmostSplit
      (k := k) hX hXind i q zero hS hclass⟩

end TwoStepMinimalProjectivePresentation

end MagnitudeConjecture
