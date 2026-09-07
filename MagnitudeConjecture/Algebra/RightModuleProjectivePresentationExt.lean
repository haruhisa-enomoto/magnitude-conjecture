import MagnitudeConjecture.Algebra.RightModuleProjectiveStableCovariantRepresentable
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDualUniserial
import MagnitudeConjecture.CategoryTheory.FGExtRealization
import MagnitudeConjecture.CategoryTheory.ProjectivePresentationExt

/-!
# Ext from a projective presentation on the finite module skeleton

This file restricts `Ext¹(X,-)` to the finite indecomposable skeleton and
packages the canonical natural epimorphism

`Ext¹(X,-) ⟶ \underline{Hom}(ΩX,-)`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

abbrev FG := RightModule.FinitelyGeneratedCategory A

variable [HasExt.{u} (FG (A := A))]

/-- The short exact sequence defined by a projective cover. -/
abbrev projectiveCoverShortComplex {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) : ShortComplex (FG (A := A)) :=
  ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)

/-- The projective-cover sequence is short exact. -/
theorem projectiveCoverShortComplex_shortExact {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    (projectiveCoverShortComplex P).ShortExact := by
  dsimp [projectiveCoverShortComplex]
  exact
    { exact := ShortComplex.exact_kernel P.f
      mono_f := inferInstance
      epi_g := inferInstance }

/-- A skeleton morphism bundled in the finitely generated module category. -/
def fgMap {Y Z : S.IndecCategory} (f : Y ⟶ Z) :
    S.fgObj Y ⟶ S.fgObj Z :=
  ObjectProperty.homMk (S.inclusion.map f)

/-- The restriction of `Ext¹(X,-)` to the finite skeleton of indecomposable
right modules. -/
def restrictedExtOne {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    S.IndecCategory ⥤ ModuleCat.{u} k where
  obj Y := ModuleCat.of k (Ext.{u} X (S.fgObj Y) 1)
  map f := ModuleCat.ofHom <|
    ProjectivePresentationExt.pushforwardLinear
      (k := k) (projectiveCoverShortComplex P) (S.fgMap f)
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro xi
    change Ext.{u} X (S.fgObj Y) 1 at xi
    change xi.comp (Ext.mk₀ (S.fgMap (𝟙 Y))) (add_zero 1) = xi
    rw [show S.fgMap (𝟙 Y) = 𝟙 (S.fgObj Y) by
      apply ObjectProperty.hom_ext
      exact S.inclusion.map_id Y]
    exact Ext.comp_mk₀_id xi
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro xi
    change xi.comp (Ext.mk₀ (S.fgMap (f ≫ g))) (add_zero 1) =
      (xi.comp (Ext.mk₀ (S.fgMap f)) (add_zero 1)).comp
        (Ext.mk₀ (S.fgMap g)) (add_zero 1)
    rw [show S.fgMap (f ≫ g) = S.fgMap f ≫ S.fgMap g by
      apply ObjectProperty.hom_ext
      exact S.inclusion.map_comp f g, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc_of_third_deg_zero]

instance restrictedExtOne_additive {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    (S.restrictedExtOne P).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro xi
    change Ext.{u} X (S.fgObj Y) 1 at xi
    change xi.comp (Ext.mk₀ (S.fgMap (f + g))) (add_zero 1) =
      xi.comp (Ext.mk₀ (S.fgMap f)) (add_zero 1) +
        xi.comp (Ext.mk₀ (S.fgMap g)) (add_zero 1)
    rw [show S.fgMap (f + g) = S.fgMap f + S.fgMap g by
      apply ObjectProperty.hom_ext
      rfl, Ext.mk₀_add]
    simp

instance restrictedExtOne_linear {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    (S.restrictedExtOne P).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro xi
    change Ext.{u} X (S.fgObj _) 1 at xi
    change xi.comp (Ext.mk₀ (S.fgMap (r • f))) (add_zero 1) =
      r • xi.comp (Ext.mk₀ (S.fgMap f)) (add_zero 1)
    rw [show S.fgMap (r • f) = r • S.fgMap f by
      apply ObjectProperty.hom_ext
      rfl, Ext.mk₀_smul]
    simp

/-- Restricted degree-one Ext as a linear module. -/
def restrictedExtOneLinearModule {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    CoveringHom.LinearModuleCategory (C := S.IndecCategory) k :=
  ⟨S.restrictedExtOne P, inferInstance, inferInstance⟩

/-- Restricted degree-one Ext is pointwise finite-dimensional and has finite
support. -/
theorem restrictedExtOne_isFiniteDimensional {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
      (S.restrictedExtOneLinearModule P) := by
  constructor
  · intro Y
    let K := projectiveCoverShortComplex P
    letI : Module.Finite k K.X₁.obj :=
      RightModule.finite_over_field_of_finitelyGenerated k A K.X₁
    letI : Module.Finite k (S.fgObj Y).obj := S.obj_finite Y
    letI : Module.Finite k (K.X₁ ⟶ S.fgObj Y) := by
      exact (moduleCat_hom_finite (k := k) (A := A) K.X₁.obj
        (S.fgObj Y).obj).equiv
          (InducedCategory.homLinearEquiv (R := k)).symm
    letI : Module.Finite k
        ((K.X₁ ⟶ S.fgObj Y) ⧸
          ProjectivePresentationExt.presentationRange
            (k := k) K (S.fgObj Y)) :=
      Module.Finite.quotient k _
    exact Module.Finite.equiv
      (ProjectivePresentationExt.quotientLinearEquivExtOne
        (k := k) (projectiveCoverShortComplex_shortExact P)
          (S.fgObj Y))
  · exact Set.toFinite _

/-- Restricted degree-one Ext in the finite functor category. -/
def finiteRestrictedExtOne {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  ⟨S.restrictedExtOneLinearModule P,
    S.restrictedExtOne_isFiniteDimensional P⟩

/-- Bundle an ambient module morphism between finitely generated objects. -/
def fgHomLinear (U V : FG (A := A)) :
    (U.obj ⟶ V.obj) →ₗ[k] (U ⟶ V) where
  toFun f := ObjectProperty.homMk f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forget the finite-generation property on a morphism, as a linear map. -/
def forgetFGHomLinear (U V : FG (A := A)) :
    (U ⟶ V) →ₗ[k] (U.obj ⟶ V.obj) where
  toFun f := f.hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projective-presentation connecting map, with its source written as
ambient module morphisms. -/
def ambientConnectingLinear
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : FG (A := A)) :
    ((kernel P.f).obj ⟶ Y.obj) →ₗ[k] Ext.{u} X Y 1 := by
  let d :=
    (ProjectivePresentationExt.connectingLinear
      (k := k) (projectiveCoverShortComplex_shortExact P) Y).comp
        (fgHomLinear (k := k) (kernel P.f) Y)
  simpa only [projectiveCoverShortComplex] using d

@[simp]
theorem ambientConnectingLinear_apply
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : FG (A := A)) (f : (kernel P.f).obj ⟶ Y.obj) :
    ambientConnectingLinear (k := k) P Y f =
      ProjectivePresentationExt.connectingLinear
        (k := k) (projectiveCoverShortComplex_shortExact P) Y
          (ObjectProperty.homMk f) :=
  rfl

/-- Naturality of the ambient-source connecting map. -/
theorem ambientConnectingLinear_postcomp
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    {Y Z : FG (A := A)} (a : Y ⟶ Z)
    (f : (kernel P.f).obj ⟶ Y.obj) :
    ambientConnectingLinear (k := k) P Z (f ≫ a.hom) =
      ProjectivePresentationExt.pushforwardLinear
        (k := k) (projectiveCoverShortComplex P) a
          (ambientConnectingLinear (k := k) P Y f) := by
  exact ProjectivePresentationExt.connectingLinear_postcomp
    (k := k) (projectiveCoverShortComplex_shortExact P) a
      (ObjectProperty.homMk f)

/-- The connecting morphism `Hom(ΩX,-) ⟶ Ext¹(X,-)` on the finite
indecomposable skeleton. -/
def finiteRestrictedCovariantConnecting
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    S.finiteRestrictedCovariantRepresentable (kernel P.f) ⟶
      S.finiteRestrictedExtOne P :=
  ObjectProperty.homMk <| ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom <|
        ambientConnectingLinear (k := k) P (S.fgObj Y)
      naturality := by
        intro Y Z a
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        exact ambientConnectingLinear_postcomp
          (k := k) P (S.fgMap a) f }

/-- The connecting morphism is pointwise surjective. -/
theorem finiteRestrictedCovariantConnecting_app_surjective
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : S.IndecCategory) :
    Function.Surjective
      ((S.finiteRestrictedCovariantConnecting P).hom.hom.app Y) := by
  intro xi
  obtain ⟨f, hf⟩ := ProjectivePresentationExt.connectingLinear_surjective
    (k := k) (projectiveCoverShortComplex_shortExact P) (S.fgObj Y) xi
  exact ⟨f.hom, hf⟩

instance finiteRestrictedCovariantConnecting_epi
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    Epi (S.finiteRestrictedCovariantConnecting P) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule (C := S.IndecCategory) k).ι
  have happ (Y : S.IndecCategory) : Epi
      ((I.map (J.map (S.finiteRestrictedCovariantConnecting P))).app Y) := by
    rw [ModuleCat.epi_iff_surjective]
    exact S.finiteRestrictedCovariantConnecting_app_surjective P Y
  have hnat : Epi (I.map (J.map
      (S.finiteRestrictedCovariantConnecting P))) :=
    NatTrans.epi_of_epi_app _
  have hlinear : Epi (J.map (S.finiteRestrictedCovariantConnecting P)) :=
    I.epi_of_epi_map hnat
  exact J.epi_of_epi_map hlinear

/-- The first two maps in the source exact sequence compose to zero. -/
theorem finiteRestrictedCovariantRepresentableMap_projectiveCover_comp_kernel
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    S.finiteRestrictedCovariantRepresentableMap P.f ≫
        S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f) = 0 := by
  rw [← S.finiteRestrictedCovariantRepresentableMap_comp,
    kernel.condition,
    S.finiteRestrictedCovariantRepresentableMap_zero]

/-- Exactness of `Hom(X,-) ⟶ Hom(P,-) ⟶ Hom(ΩX,-)` on the finite
indecomposable skeleton. -/
theorem finiteRestrictedCovariantProjectiveCover_exact
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    (ShortComplex.mk
      (S.finiteRestrictedCovariantRepresentableMap P.f)
      (S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f))
      (S.finiteRestrictedCovariantRepresentableMap_projectiveCover_comp_kernel P)).Exact := by
  let T := ShortComplex.mk
    (S.finiteRestrictedCovariantRepresentableMap P.f)
    (S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f))
    (S.finiteRestrictedCovariantRepresentableMap_projectiveCover_comp_kernel P)
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule (C := S.IndecCategory) k).ι
  apply J.reflects_exact_of_faithful T
  apply I.reflects_exact_of_faithful (T.map J)
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro Y
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    let a' : X.obj ⟶ (S.fgObj Y).obj := a
    change (kernel.ι P.f).hom ≫ (P.f.hom ≫ a') = 0
    rw [← Category.assoc]
    have hcond := congrArg
      (fun q : kernel P.f ⟶ X ↦ q.hom) (kernel.condition P.f)
    change (kernel.ι P.f).hom ≫ P.f.hom = 0 at hcond
    rw [hcond, zero_comp]
  · intro hf
    rw [LinearMap.mem_ker] at hf
    let f' : P.p.obj ⟶ (S.fgObj Y).obj := f
    have hfzero : kernel.ι P.f ≫
        (ObjectProperty.homMk f' : P.p ⟶ S.fgObj Y) = 0 := by
      apply ObjectProperty.hom_ext
      exact hf
    obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc'
      (ShortComplex.exact_kernel P.f).gIsCokernel
      (ObjectProperty.homMk f') hfzero
    exact ⟨a.hom,
      congrArg (fun q : P.p ⟶ S.fgObj Y ↦ q.hom) ha⟩

/-- Precomposition from the projective term lands in the kernel of the
connecting morphism. -/
theorem finiteRestrictedCovariantRepresentableMap_kernel_comp_connecting
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f) ≫
        S.finiteRestrictedCovariantConnecting P = 0 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  let f' : P.p.obj ⟶ (S.fgObj Y).obj := f
  change ambientConnectingLinear (k := k) P (S.fgObj Y)
      ((kernel.ι P.f).hom ≫ f') = 0
  rw [ambientConnectingLinear_apply]
  apply LinearMap.mem_ker.mp
  rw [← ProjectivePresentationExt.presentationRange_eq_connectingLinear_ker
    (k := k) (projectiveCoverShortComplex_shortExact P) (S.fgObj Y)]
  exact ⟨ObjectProperty.homMk f', rfl⟩

/-- The connecting morphism realizes `Ext¹(X,-)` as the cokernel of
`Hom(P,-) ⟶ Hom(ΩX,-)` in the finite functor category. -/
theorem finiteRestrictedCovariantConnecting_exact
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    (ShortComplex.mk
      (S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f))
      (S.finiteRestrictedCovariantConnecting P)
      (S.finiteRestrictedCovariantRepresentableMap_kernel_comp_connecting P)).Exact := by
  let T := ShortComplex.mk
    (S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f))
    (S.finiteRestrictedCovariantConnecting P)
    (S.finiteRestrictedCovariantRepresentableMap_kernel_comp_connecting P)
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule (C := S.IndecCategory) k).ι
  apply J.reflects_exact_of_faithful T
  apply I.reflects_exact_of_faithful (T.map J)
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro Y
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change ambientConnectingLinear (k := k) P (S.fgObj Y)
      ((kernel.ι P.f).hom ≫ a) = 0
    rw [ambientConnectingLinear_apply]
    apply LinearMap.mem_ker.mp
    rw [← ProjectivePresentationExt.presentationRange_eq_connectingLinear_ker
      (k := k) (projectiveCoverShortComplex_shortExact P) (S.fgObj Y)]
    exact ⟨ObjectProperty.homMk a, rfl⟩
  · intro hf
    rw [LinearMap.mem_ker] at hf
    let f' : (kernel P.f).obj ⟶ (S.fgObj Y).obj := f
    have hfzero : ambientConnectingLinear (k := k) P (S.fgObj Y) f' = 0 := hf
    rw [ambientConnectingLinear_apply] at hfzero
    have hfrange : (ObjectProperty.homMk f' : kernel P.f ⟶ S.fgObj Y) ∈
        ProjectivePresentationExt.presentationRange
          (k := k) (projectiveCoverShortComplex P) (S.fgObj Y) := by
      rw [ProjectivePresentationExt.presentationRange_eq_connectingLinear_ker
        (k := k) (projectiveCoverShortComplex_shortExact P) (S.fgObj Y)]
      exact LinearMap.mem_ker.mpr hfzero
    obtain ⟨a, ha⟩ := hfrange
    exact ⟨a.hom, congrArg (fun q : kernel P.f ⟶ S.fgObj Y ↦ q.hom) ha⟩

/-- The source-shaped cokernel presentation defining the coherent dual of
the stable contravariant representable. -/
noncomputable def finiteRestrictedCovariantConnecting_isCokernel
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    IsColimit (CokernelCofork.ofπ
      (S.finiteRestrictedCovariantConnecting P)
      (S.finiteRestrictedCovariantRepresentableMap_kernel_comp_connecting P)) := by
  let T := ShortComplex.mk
    (S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f))
    (S.finiteRestrictedCovariantConnecting P)
    (S.finiteRestrictedCovariantRepresentableMap_kernel_comp_connecting P)
  exact Classical.choice
    (T.exact_and_epi_g_iff_g_is_cokernel.1 ⟨
      S.finiteRestrictedCovariantConnecting_exact P, inferInstance⟩)

/-- The projective-presentation quotient maps onto stable Hom after
forgetting finite generation. -/
def presentationToAmbientProjectiveStable
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : S.IndecCategory) :
    (((kernel P.f) ⟶ S.fgObj Y) ⧸
        ProjectivePresentationExt.presentationRange
          (k := k) (projectiveCoverShortComplex P) (S.fgObj Y)) →ₗ[k]
      ProjectiveStable.Hom (k := k) (kernel P.f).obj
        (S.inclusion.obj Y) :=
  (ProjectivePresentationExt.presentationRange
      (k := k) (projectiveCoverShortComplex P) (S.fgObj Y)).mapQ
    (ProjectiveStable.factorSubmodule (k := k)
      (kernel P.f).obj (S.inclusion.obj Y))
    (forgetFGHomLinear (k := k) (kernel P.f) (S.fgObj Y)) (by
      intro f hf
      obtain ⟨v, rfl⟩ := hf
      exact ⟨{
        middle := P.p.obj
        projective :=
          (FGExtRealization.inclusion (R := Aᵐᵒᵖ)).projective_obj_of_projective
            inferInstance
        left := (kernel.ι P.f).hom
        right := v.hom
        fac := rfl }⟩)

@[simp]
theorem presentationToAmbientProjectiveStable_mk
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : S.IndecCategory) (f : kernel P.f ⟶ S.fgObj Y) :
    S.presentationToAmbientProjectiveStable P Y
        (Submodule.Quotient.mk f) =
      ProjectiveStable.mk (k := k) f.hom := by
  rfl

/-- The presentation-to-ambient-stable map is surjective. -/
theorem presentationToAmbientProjectiveStable_surjective
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : S.IndecCategory) :
    Function.Surjective (S.presentationToAmbientProjectiveStable P Y) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Submodule.Quotient.mk (ObjectProperty.homMk f), rfl⟩

/-- The presentation-to-ambient-stable map commutes with a skeleton
morphism. -/
theorem presentationToAmbientProjectiveStable_postcomp
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    {Y Z : S.IndecCategory} (a : Y ⟶ Z)
    (q : ((kernel P.f ⟶ S.fgObj Y) ⧸
      ProjectivePresentationExt.presentationRange
        (k := k) (projectiveCoverShortComplex P) (S.fgObj Y))) :
    S.presentationToAmbientProjectiveStable P Z
        (ProjectivePresentationExt.postcompQuotient
          (k := k) (projectiveCoverShortComplex P) (S.fgMap a) q) =
      ProjectiveStable.postcomp (k := k) (kernel P.f).obj
        (S.inclusion.map a)
        (S.presentationToAmbientProjectiveStable P Y q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- The objectwise canonical quotient from degree-one Ext to ambient
projective-stable Hom. -/
def extOneToAmbientProjectiveStable
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : S.IndecCategory) :
    Ext.{u} X (S.fgObj Y) 1 →ₗ[k]
      ProjectiveStable.Hom (k := k) (kernel P.f).obj
        (S.inclusion.obj Y) :=
  (S.presentationToAmbientProjectiveStable P Y).comp
    (ProjectivePresentationExt.quotientLinearEquivExtOne
      (k := k) (projectiveCoverShortComplex_shortExact P)
      (S.fgObj Y)).symm.toLinearMap

/-- The objectwise Ext-to-stable quotient is surjective. -/
theorem extOneToAmbientProjectiveStable_surjective
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (Y : S.IndecCategory) :
    Function.Surjective (S.extOneToAmbientProjectiveStable P Y) :=
  (S.presentationToAmbientProjectiveStable_surjective P Y).comp
    (ProjectivePresentationExt.quotientLinearEquivExtOne
      (k := k) (projectiveCoverShortComplex_shortExact P)
      (S.fgObj Y)).symm.surjective

/-- Naturality of the Ext-to-ambient-stable quotient. -/
theorem extOneToAmbientProjectiveStable_naturality
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    {Y Z : S.IndecCategory} (a : Y ⟶ Z)
    (xi : Ext.{u} X (S.fgObj Y) 1) :
    S.extOneToAmbientProjectiveStable P Z
        (ProjectivePresentationExt.pushforwardLinear
          (k := k) (projectiveCoverShortComplex P) (S.fgMap a) xi) =
      ProjectiveStable.postcomp (k := k) (kernel P.f).obj
        (S.inclusion.map a)
        (S.extOneToAmbientProjectiveStable P Y xi) := by
  obtain ⟨q, rfl⟩ :=
    (ProjectivePresentationExt.quotientLinearEquivExtOne
      (k := k) (projectiveCoverShortComplex_shortExact P)
      (S.fgObj Y)).surjective xi
  rw [← ProjectivePresentationExt.quotientLinearEquivExtOne_postcompQuotient
    (k := k) (projectiveCoverShortComplex_shortExact P) (S.fgMap a) q]
  change S.presentationToAmbientProjectiveStable P Z
      ((ProjectivePresentationExt.quotientLinearEquivExtOne
        (k := k) (projectiveCoverShortComplex_shortExact P)
        (S.fgObj Z)).symm
          ((ProjectivePresentationExt.quotientLinearEquivExtOne
            (k := k) (projectiveCoverShortComplex_shortExact P)
            (S.fgObj Z))
            (ProjectivePresentationExt.postcompQuotient
              (k := k) (projectiveCoverShortComplex P) (S.fgMap a) q))) = _
  rw [LinearEquiv.symm_apply_apply]
  change _ = ProjectiveStable.postcomp (k := k) (kernel P.f).obj
    (S.inclusion.map a)
      (S.presentationToAmbientProjectiveStable P Y
        ((ProjectivePresentationExt.quotientLinearEquivExtOne
          (k := k) (projectiveCoverShortComplex_shortExact P)
          (S.fgObj Y)).symm
            ((ProjectivePresentationExt.quotientLinearEquivExtOne
              (k := k) (projectiveCoverShortComplex_shortExact P)
              (S.fgObj Y)) q)))
  rw [LinearEquiv.symm_apply_apply]
  exact S.presentationToAmbientProjectiveStable_postcomp P a q

/-- The objectwise canonical quotient
`Ext¹(X,-) ⟶ \underline{Hom}(ΩX,-)`. -/
def extOneToProjectiveStableLinearModule {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    (S.finiteRestrictedExtOne P).obj ⟶
      (S.finiteProjectiveStableCovariantRepresentable
        (kernel P.f)).obj :=
  ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom <|
        S.extOneToAmbientProjectiveStable P Y
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro xi
        exact S.extOneToAmbientProjectiveStable_naturality P f xi }

/-- The canonical quotient from degree-one Ext to stable Hom in the finite
functor category. -/
def finiteExtOneToProjectiveStable {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    S.finiteRestrictedExtOne P ⟶
      S.finiteProjectiveStableCovariantRepresentable (kernel P.f) :=
  ObjectProperty.homMk (S.extOneToProjectiveStableLinearModule P)

instance finiteExtOneToProjectiveStable_epi {X : FG (A := A)}
    (P : MinimalProjectivePresentation X) :
    Epi (S.finiteExtOneToProjectiveStable P) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule (C := S.IndecCategory) k).ι
  have happ (Y : S.IndecCategory) : Epi
      ((I.map (J.map (S.finiteExtOneToProjectiveStable P))).app Y) := by
    rw [ModuleCat.epi_iff_surjective]
    exact S.extOneToAmbientProjectiveStable_surjective P Y
  have hnat : Epi (I.map (J.map
      (S.finiteExtOneToProjectiveStable P))) :=
    NatTrans.epi_of_epi_app _
  have hlinear : Epi (J.map (S.finiteExtOneToProjectiveStable P)) :=
    I.epi_of_epi_map hnat
  exact J.epi_of_epi_map hlinear

/-- Uniseriality passes from degree-one Ext to the projective-stable
representable of the first syzygy. -/
theorem finiteProjectiveStableCovariantRepresentable_isUniserial_of_extOne
    {X : FG (A := A)} (P : MinimalProjectivePresentation X)
    (hExt : IsUniserialObject (S.finiteRestrictedExtOne P)) :
    IsUniserialObject
      (S.finiteProjectiveStableCovariantRepresentable (kernel P.f)) :=
  IsUniserialObject.of_epi hExt (S.finiteExtOneToProjectiveStable P)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
