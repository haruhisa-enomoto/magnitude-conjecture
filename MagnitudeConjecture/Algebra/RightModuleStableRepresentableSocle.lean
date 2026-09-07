import MagnitudeConjecture.Algebra.RightModuleStableRepresentableSuccessor
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDualSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleInjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableInjectiveBoundary
import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope

/-!
# Simple socles of stable representables

Pointwise coefficient duality embeds the dual of a stable representable into
the dual corepresentable at the same indecomposable.  This is the injective
envelope used in Auslander--Reiten's socle-series proof of Corollary 3.8.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture

universe u₀ v₀

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀]

/-- A simple subobject remains essential after restricting an
indecomposable injective to any intermediate subobject containing it. -/
theorem isEssentialMono_of_simple_comp_mono_into_injective_local_end
    {T H I : C₀} [Simple T] [Injective I] [IsLocalRing (End I)]
    (t : T ⟶ H) (m : H ⟶ I) [Mono m]
    (s : T ⟶ I) [Mono s] (hs : s ≠ 0) (htm : t ≫ m = s) :
    IsEssentialMono t := by
  constructor
  · exact mono_of_mono_fac htm
  · intro Z g htg
    letI : Mono (t ≫ g) := htg
    apply Abelian.mono_of_kernel_ι_eq_zero
    by_contra hq
    let q := kernel.ι g
    have hqm : q ≫ m ≠ 0 := by
      intro hzero
      apply hq
      apply (cancel_mono m).1
      simpa [q] using hzero
    haveI : Mono (q ≫ m) := inferInstance
    have hessential : IsEssentialMono (q ≫ m) :=
      isEssentialMono_of_mono_nonzero_of_injective_local_end (q ≫ m) hqm
    obtain ⟨a, ha⟩ := exists_factor_thru_of_isEssentialMono_of_simple
      (q ≫ m) hessential s hs
    have hat : a ≫ q = t := by
      apply (cancel_mono m).1
      rw [Category.assoc, ha, htm]
    have hzero : t ≫ g = 0 := by
      rw [← hat, Category.assoc, show q ≫ g = 0 from kernel.condition g,
        comp_zero]
    apply CategoryTheory.id_nonzero T
    apply (cancel_mono (t ≫ g)).1
    rw [Category.id_comp, zero_comp, hzero]

end MagnitudeConjecture

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Pointwise coefficient duality in the direction from modules on the
opposite indecomposable skeleton back to modules on the skeleton. -/
def finiteReverseCoefficientDualMap
    {M N : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} (f : M ⟶ N) :
    CoveringHom.reverseFiniteCoefficientDual (k := k) N ⟶
      CoveringHom.reverseFiniteCoefficientDual (k := k) M :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { app := fun X ↦ ModuleCat.ofHom
        (f.hom.hom.app (Opposite.op X)).hom.dualMap
      naturality := by
        intro X Y q
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change Module.Dual k (N.obj.obj.obj (Opposite.op X)) at φ
        apply LinearMap.ext
        intro x
        have h := ConcreteCategory.congr_hom
          (f.hom.hom.naturality q.op) x
        change φ (N.obj.obj.map q.op (f.hom.hom.app (Opposite.op Y) x)) =
          φ (f.hom.hom.app (Opposite.op X) (M.obj.obj.map q.op x))
        exact congrArg φ h.symm })

instance finiteReverseCoefficientDualMap_mono
    {M N : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} (f : M ⟶ N) [Epi f] :
    Mono (S.finiteReverseCoefficientDualMap f) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategory) k).ι
  let J₀ := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  let I₀ := (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  letI : J₀.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (CoveringHom.IsFiniteDimensionalModule
        (C := S.IndecCategoryᵒᵖ) k)
  letI : I₀.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (CoveringHom.IsLinearModule
        (C := S.IndecCategoryᵒᵖ) k)
  have happ (X : S.IndecCategory) : Mono
      ((I.map (J.map (S.finiteReverseCoefficientDualMap f))).app X) := by
    rw [ModuleCat.mono_iff_injective]
    apply LinearMap.dualMap_injective_of_surjective
    haveI : Epi (I₀.map (J₀.map f)) := I₀.map_epi (J₀.map f)
    haveI : Epi ((I₀.map (J₀.map f)).app (Opposite.op X)) :=
      (NatTrans.epi_iff_epi_app (I₀.map (J₀.map f))).mp inferInstance
        (Opposite.op X)
    have hsurjective : Function.Surjective
        ((I₀.map (J₀.map f)).app (Opposite.op X)) :=
      (ModuleCat.epi_iff_surjective
        ((I₀.map (J₀.map f)).app (Opposite.op X))).mp inferInstance
    change Function.Surjective
      (f.hom.hom.app (Opposite.op X)) at hsurjective
    exact hsurjective
  have hnat : Mono (I.map (J.map (S.finiteReverseCoefficientDualMap f))) :=
    NatTrans.mono_of_mono_app _
  have hlinear : Mono (J.map (S.finiteReverseCoefficientDualMap f)) :=
    I.mono_of_mono_map hnat
  exact J.mono_of_mono_map hlinear

/-- Over a field, coefficient duality detects whether a natural
transformation of finite modules is zero. -/
theorem finiteReverseCoefficientDualMap_ne_zero
    {M N : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} (f : M ⟶ N) (hf : f ≠ 0) :
    S.finiteReverseCoefficientDualMap f ≠ 0 := by
  intro hdual
  apply hf
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_contra hx
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hx
  have happ := congrArg
    (fun g : CoveringHom.reverseFiniteCoefficientDual (k := k) N ⟶
        CoveringHom.reverseFiniteCoefficientDual (k := k) M ↦
      g.hom.hom.app X.unop φ) hdual
  have heval := congrArg
    (fun ψ : Module.Dual k (M.obj.obj.obj X) ↦ ψ x) happ
  change φ (f.hom.hom.app X x) = 0 at heval
  exact hφ heval

/-- Dual corepresentables on the finite indecomposable skeleton satisfy the
finite-module condition. -/
def indecDualCorepresentableFinite (i : S.IndecCategory) :
    CoveringHom.IsFiniteDimensionalModule
      (C := S.IndecCategory) k
      (CoveringHom.dualLinearYonedaLinearModule (k := k) i) := by
  constructor
  · intro X
    letI : Module.Finite k (S.inclusion.obj X) :=
      S.indecCategory_obj_finite X
    letI : Module.Finite k (S.inclusion.obj i) :=
      S.indecCategory_obj_finite i
    letI : Module.Finite k
        (S.inclusion.obj X ⟶ S.inclusion.obj i) :=
      moduleCat_hom_finite (k := k) (A := A)
        (S.inclusion.obj X) (S.inclusion.obj i)
    let e : (X ⟶ i) ≃ₗ[k]
        (S.inclusion.obj X ⟶ S.inclusion.obj i) :=
      InducedCategory.homLinearEquiv (R := k)
    letI : FiniteDimensional k (X ⟶ i) := e.symm.finiteDimensional
    change Module.Finite k (Module.Dual k (X ⟶ i))
    infer_instance
  · exact Set.toFinite _

/-- The reverse coefficient dual of a restricted ambient representable is
naturally the dual corepresentable of the corresponding skeleton object. -/
def reverseFiniteCoefficientDualRestrictedRepresentableIso
    (i : S.IndecCategory) :
    CoveringHom.reverseFiniteCoefficientDual (k := k)
        (S.finiteRestrictedContravariantRepresentable (S.fgObj i)) ≅
      CoveringHom.finiteDimensionalDualLinearYoneda
        (k := k) i (S.indecDualCorepresentableFinite i) := by
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · let e : (X ⟶ i) ≃ₗ[k]
        (S.inclusion.obj X ⟶ S.inclusion.obj i) :=
      InducedCategory.homLinearEquiv (R := k)
    exact e.dualMap.toModuleIso
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change Module.Dual k
    (S.inclusion.obj X ⟶ S.inclusion.obj i) at φ
  apply LinearMap.ext
  intro q
  rfl

/-- The coefficient dual of a stable representable. -/
def finiteDualProjectiveStableRepresentable
    (C : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  CoveringHom.reverseFiniteCoefficientDual (k := k)
    (S.finiteProjectiveStableContravariantRepresentable C)

/-- Dualizing the stable quotient gives its canonical inclusion into the
dual of the ordinary restricted representable. -/
def finiteDualProjectiveStableInclusion
    (C : RightModule.FinitelyGeneratedCategory A) :
    S.finiteDualProjectiveStableRepresentable C ⟶
      CoveringHom.reverseFiniteCoefficientDual (k := k)
        (S.finiteRestrictedContravariantRepresentable C) :=
  S.finiteReverseCoefficientDualMap
    (S.finiteProjectiveStableQuotient C)

instance finiteDualProjectiveStableInclusion_mono
    (C : RightModule.FinitelyGeneratedCategory A) :
    Mono (S.finiteDualProjectiveStableInclusion C) := by
  letI : Epi (S.finiteProjectiveStableQuotient C) :=
    S.finiteProjectiveStableQuotient_epi C
  dsimp only [finiteDualProjectiveStableInclusion]
  exact S.finiteReverseCoefficientDualMap_mono
    (S.finiteProjectiveStableQuotient C)

/-- At a chosen indecomposable, the dual stable representable embeds in the
standard dual corepresentable. -/
def finiteDualProjectiveStableCorepresentableInclusion
    (i : S.IndecCategory) :
    S.finiteDualProjectiveStableRepresentable (S.fgObj i) ⟶
      CoveringHom.finiteDimensionalDualLinearYoneda
        (k := k) i (S.indecDualCorepresentableFinite i) :=
  S.finiteDualProjectiveStableInclusion (S.fgObj i) ≫
    (S.reverseFiniteCoefficientDualRestrictedRepresentableIso i).hom

instance finiteDualProjectiveStableCorepresentableInclusion_mono
    (i : S.IndecCategory) :
    Mono (S.finiteDualProjectiveStableCorepresentableInclusion i) := by
  dsimp only [finiteDualProjectiveStableCorepresentableInclusion]
  infer_instance

/-- The dual stable embedding is nonzero at a nonprojective
indecomposable. -/
theorem finiteDualProjectiveStableCorepresentableInclusion_ne_zero
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    S.finiteDualProjectiveStableCorepresentableInclusion i ≠ 0 := by
  intro hzero
  apply S.finiteReverseCoefficientDualMap_ne_zero
    (S.finiteProjectiveStableQuotient (S.fgObj i))
    (S.finiteProjectiveStableQuotient_fgObj_ne_zero i hi)
  change S.finiteReverseCoefficientDualMap
      (S.finiteProjectiveStableQuotient (S.fgObj i)) ≫
        (S.reverseFiniteCoefficientDualRestrictedRepresentableIso i).hom = 0
    at hzero
  apply (cancel_mono
    (S.reverseFiniteCoefficientDualRestrictedRepresentableIso i).hom).1
  simpa using hzero

/-- The dual stable representable is an essential subobject of its ambient
indecomposable injective dual corepresentable. -/
theorem finiteDualProjectiveStableCorepresentableInclusion_isEssential
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    IsEssentialMono
      (S.finiteDualProjectiveStableCorepresentableInclusion i) := by
  let hI : ∀ X : S.IndecCategory,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.IndecCategory) k
        (CoveringHom.dualLinearYonedaLinearModule (k := k) X) :=
    S.indecDualCorepresentableFinite
  letI : Injective
      (CoveringHom.finiteDimensionalDualLinearYoneda
        (k := k) i (S.indecDualCorepresentableFinite i)) :=
    CoveringHom.finiteDimensionalDualLinearYoneda_injective i
      (S.indecDualCorepresentableFinite i)
  letI : IsLocalRing
      (End (CoveringHom.finiteDimensionalDualLinearYoneda
        (k := k) i (S.indecDualCorepresentableFinite i))) :=
    CoveringHom.finiteDimensionalDualLinearYoneda_end_isLocalRing
      hI S.indecCategory_obj_end_isLocalRing i
  exact isEssentialMono_of_mono_nonzero_of_injective_local_end
    (S.finiteDualProjectiveStableCorepresentableInclusion i)
    (S.finiteDualProjectiveStableCorepresentableInclusion_ne_zero i hi)

/-- The canonical simple socle of the ambient dual corepresentable. -/
noncomputable abbrev finiteDualProjectiveStableSocle
    (i : S.IndecCategory) :=
  CoveringHom.finiteDimensionalDualLinearYonedaSocle
    (k := k) i (S.indecDualCorepresentableFinite i)

/-- The canonical ambient socle factors through every nonzero dual stable
representable subobject. -/
noncomputable def finiteDualProjectiveStableSocleInclusion
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    S.finiteDualProjectiveStableSocle i ⟶
      S.finiteDualProjectiveStableRepresentable (S.fgObj i) := by
  letI : Simple (S.finiteDualProjectiveStableSocle i) :=
    CoveringHom.finiteDimensionalDualLinearYonedaSocle_simple
      S.indecDualCorepresentableFinite
      S.indecCategory_obj_end_isLocalRing i
  exact Classical.choose (exists_factor_thru_of_isEssentialMono_of_simple
      (S.finiteDualProjectiveStableCorepresentableInclusion i)
      (S.finiteDualProjectiveStableCorepresentableInclusion_isEssential i hi)
      (CoveringHom.finiteDimensionalDualLinearYonedaSocleInclusion
        (k := k) i (S.indecDualCorepresentableFinite i))
      (CoveringHom.finiteDimensionalDualLinearYonedaSocleInclusion_ne_zero
        S.indecDualCorepresentableFinite
        S.indecCategory_obj_end_isLocalRing i))

@[reassoc]
theorem finiteDualProjectiveStableSocleInclusion_comp
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    S.finiteDualProjectiveStableSocleInclusion i hi ≫
        S.finiteDualProjectiveStableCorepresentableInclusion i =
      CoveringHom.finiteDimensionalDualLinearYonedaSocleInclusion
        (k := k) i (S.indecDualCorepresentableFinite i) := by
  letI : Simple (S.finiteDualProjectiveStableSocle i) :=
    CoveringHom.finiteDimensionalDualLinearYonedaSocle_simple
      S.indecDualCorepresentableFinite
      S.indecCategory_obj_end_isLocalRing i
  exact Classical.choose_spec (exists_factor_thru_of_isEssentialMono_of_simple
      (S.finiteDualProjectiveStableCorepresentableInclusion i)
      (S.finiteDualProjectiveStableCorepresentableInclusion_isEssential i hi)
      (CoveringHom.finiteDimensionalDualLinearYonedaSocleInclusion
        (k := k) i (S.indecDualCorepresentableFinite i))
      (CoveringHom.finiteDimensionalDualLinearYonedaSocleInclusion_ne_zero
        S.indecDualCorepresentableFinite
        S.indecCategory_obj_end_isLocalRing i))

instance finiteDualProjectiveStableSocleInclusion_mono
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    Mono (S.finiteDualProjectiveStableSocleInclusion i hi) := by
  apply mono_of_mono_fac
    (S.finiteDualProjectiveStableSocleInclusion_comp i hi)

theorem finiteDualProjectiveStableSocle_simple
    (i : S.IndecCategory) :
    Simple (S.finiteDualProjectiveStableSocle i) :=
  CoveringHom.finiteDimensionalDualLinearYonedaSocle_simple
    S.indecDualCorepresentableFinite
    S.indecCategory_obj_end_isLocalRing i

/-- For a nonprojective indecomposable, the dual stable representable has
the canonical ambient simple as an essential socle. -/
theorem finiteDualProjectiveStableSocleInclusion_isEssential
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    IsEssentialMono (S.finiteDualProjectiveStableSocleInclusion i hi) := by
  let hI : ∀ X : S.IndecCategory,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.IndecCategory) k
        (CoveringHom.dualLinearYonedaLinearModule (k := k) X) :=
    S.indecDualCorepresentableFinite
  letI : Simple (S.finiteDualProjectiveStableSocle i) :=
    S.finiteDualProjectiveStableSocle_simple i
  letI : Injective
      (CoveringHom.finiteDimensionalDualLinearYoneda
        (k := k) i (S.indecDualCorepresentableFinite i)) :=
    CoveringHom.finiteDimensionalDualLinearYoneda_injective i
      (S.indecDualCorepresentableFinite i)
  letI : IsLocalRing
      (End (CoveringHom.finiteDimensionalDualLinearYoneda
        (k := k) i (S.indecDualCorepresentableFinite i))) :=
    CoveringHom.finiteDimensionalDualLinearYoneda_end_isLocalRing
      hI S.indecCategory_obj_end_isLocalRing i
  exact isEssentialMono_of_simple_comp_mono_into_injective_local_end
    (S.finiteDualProjectiveStableSocleInclusion i hi)
    (S.finiteDualProjectiveStableCorepresentableInclusion i)
    (CoveringHom.finiteDimensionalDualLinearYonedaSocleInclusion
      (k := k) i (S.indecDualCorepresentableFinite i))
    (CoveringHom.finiteDimensionalDualLinearYonedaSocleInclusion_ne_zero
      S.indecDualCorepresentableFinite
      S.indecCategory_obj_end_isLocalRing i)
    (S.finiteDualProjectiveStableSocleInclusion_comp i hi)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
