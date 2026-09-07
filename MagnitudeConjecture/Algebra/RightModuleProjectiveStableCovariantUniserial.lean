import MagnitudeConjecture.Algebra.RightModuleProjectiveStableCovariantRepresentable
import MagnitudeConjecture.Algebra.FiniteModuleDecomposition
import MagnitudeConjecture.Algebra.UniserialModule
import MagnitudeConjecture.CategoryTheory.FiniteCoordinateFunctor

/-!
# Uniserial projective-stable covariant representables

This file formalizes the module-theoretic input used in
Auslander--Reiten, Proposition 1.1(a).  The first step is the finite-density
extension of covariant Yoneda projectivity from chosen indecomposables to
arbitrary finitely generated modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Restricted covariant Yoneda, regarded as an additive functor from the
opposite of finitely generated modules. -/
def finiteRestrictedCovariantRepresentableFunctor :
    (RightModule.FinitelyGeneratedCategory A)ᵒᵖ ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k where
  obj X := S.finiteRestrictedCovariantRepresentable X.unop
  map f := S.finiteRestrictedCovariantRepresentableMap f.unop
  map_id X := by
    change S.finiteRestrictedCovariantRepresentableMap (𝟙 X.unop) = 𝟙 _
    exact S.finiteRestrictedCovariantRepresentableMap_id X.unop
  map_comp f g := by
    change S.finiteRestrictedCovariantRepresentableMap (g.unop ≫ f.unop) =
      S.finiteRestrictedCovariantRepresentableMap f.unop ≫
        S.finiteRestrictedCovariantRepresentableMap g.unop
    exact S.finiteRestrictedCovariantRepresentableMap_comp g.unop f.unop

instance finiteRestrictedCovariantRepresentableFunctor_additive :
    S.finiteRestrictedCovariantRepresentableFunctor.Additive where
  map_add := by
    intro X Y f g
    change S.finiteRestrictedCovariantRepresentableMap (f.unop + g.unop) =
      S.finiteRestrictedCovariantRepresentableMap f.unop +
        S.finiteRestrictedCovariantRepresentableMap g.unop
    exact S.finiteRestrictedCovariantRepresentableMap_add f.unop g.unop

/-- Restricted covariant representables of arbitrary finitely generated
modules are projective.  Decompose the representing module into the chosen
indecomposables and apply additivity of covariant Yoneda on the opposite
category. -/
theorem finiteRestrictedCovariantRepresentable_projective
    (C : RightModule.FinitelyGeneratedCategory A) :
    Projective (S.finiteRestrictedCovariantRepresentable C) := by
  letI : Module.Finite k C :=
    RightModule.finite_over_field_of_finitelyGenerated k A C
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) C
  have hdense (j : Fin d.n) :
      ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
    S.fgObj_complete (d.summand j) (d.indecomposable j)
  choose i e using hdense
  let chosen : Fin d.n → RightModule.FinitelyGeneratedCategory A :=
    fun j ↦ S.fgObj (i j)
  let eModule : C ≅ ⨁ chosen :=
    d.isoBiproduct ≪≫ biproduct.mapIso (fun j ↦ Classical.choice (e j))
  let F := S.finiteRestrictedCovariantRepresentableFunctor
  let eOpposite : Opposite.op C ≅ ⨁ fun j ↦ Opposite.op (chosen j) :=
    eModule.op.symm ≪≫
      (biproduct.isoCoproduct chosen).op.symm ≪≫
      opCoproductIsoProduct chosen ≪≫
      (biproduct.isoProduct (fun j ↦ Opposite.op (chosen j))).symm
  let eRepresentable : F.obj (Opposite.op C) ≅
      ⨁ fun j ↦ F.obj (Opposite.op (chosen j)) :=
    F.mapIso eOpposite ≪≫
      F.mapBiproduct (fun j ↦ Opposite.op (chosen j))
  have hProjective : Projective
      (⨁ fun j ↦ F.obj (Opposite.op (chosen j))) := by
    constructor
    intro E X f q hq
    letI : Epi q := hq
    have hfactor (j : Fin d.n) :
        ∃ l : F.obj (Opposite.op (chosen j)) ⟶ E,
          l ≫ q = biproduct.ι
            (fun j ↦ F.obj (Opposite.op (chosen j))) j ≫ f := by
      letI : Projective (F.obj (Opposite.op (chosen j))) := by
        change Projective
          (S.finiteRestrictedCovariantRepresentable (S.fgObj (i j)))
        infer_instance
      exact Projective.factors
        (biproduct.ι (fun j ↦ F.obj (Opposite.op (chosen j))) j ≫ f) q
    choose l hl using hfactor
    refine ⟨biproduct.desc l, ?_⟩
    apply biproduct.hom_ext'
    intro j
    rw [biproduct.ι_desc_assoc, hl]
  exact Projective.of_iso eRepresentable.symm hProjective

/-- Finite additive density upgrades covariant Yoneda fullness on the chosen
indecomposables to fullness on all finitely generated modules. -/
theorem finiteRestrictedCovariantRepresentableFunctor_full :
    S.finiteRestrictedCovariantRepresentableFunctor.Full := by
  let F := S.finiteRestrictedCovariantRepresentableFunctor
  change F.Full
  refine MagnitudeConjecture.CategoryTheory.functor_full_of_finite_coordinates
    (C := (RightModule.FinitelyGeneratedCategory A)ᵒᵖ)
    (D := CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k)
    (P := S.IndecCategory) (fun i ↦ Opposite.op (S.fgObj i)) F ?_ ?_
  · intro X
    letI : Module.Finite k X.unop :=
      RightModule.finite_over_field_of_finitelyGenerated k A X.unop
    obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
      (k := k) X.unop
    have hdense (j : Fin d.n) :
        ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
      S.fgObj_complete (d.summand j) (d.indecomposable j)
    choose i e using hdense
    let chosen : Fin d.n → RightModule.FinitelyGeneratedCategory A :=
      fun j ↦ S.fgObj (i j)
    let eModule : X.unop ≅ ⨁ chosen :=
      d.isoBiproduct ≪≫ biproduct.mapIso (fun j ↦ Classical.choice (e j))
    let eOpposite : X ≅ ⨁ fun j ↦ Opposite.op (chosen j) :=
      eModule.op.symm ≪≫
        (biproduct.isoCoproduct chosen).op.symm ≪≫
        opCoproductIsoProduct chosen ≪≫
        (biproduct.isoProduct (fun j ↦ Opposite.op (chosen j))).symm
    exact ⟨d.n, i, ⟨eOpposite.symm⟩⟩
  · intro i j a
    let f : S.fgObj j ⟶ S.fgObj i := ObjectProperty.homMk (by
      change S.obj j ⟶ S.obj i
      exact a.hom.hom.app i (𝟙 (S.inclusion.obj i)))
    refine ⟨f.op, ?_⟩
    change S.finiteRestrictedCovariantRepresentableMap f = a
    exact S.finiteRestrictedCovariantRepresentableMap_fgObj_eq i j a

/-- Every natural map between restricted covariant representables is induced
by a unique-variance module map. -/
theorem exists_eq_finiteRestrictedCovariantRepresentableMap
    (B C : RightModule.FinitelyGeneratedCategory A)
    (p : S.finiteRestrictedCovariantRepresentable B ⟶
      S.finiteRestrictedCovariantRepresentable C) :
    ∃ h : C ⟶ B,
      S.finiteRestrictedCovariantRepresentableMap h = p := by
  let F := S.finiteRestrictedCovariantRepresentableFunctor
  letI : F.Full := S.finiteRestrictedCovariantRepresentableFunctor_full
  obtain ⟨h, hh⟩ := F.map_surjective p
  exact ⟨h.unop, hh⟩

/-- A module map `f : X ⟶ Y` generates a map from covariant `Hom(Y,-)` to
projective-stable `Hom(X,-)`. -/
def finiteRestrictedToProjectiveStableCovariantMap
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    S.finiteRestrictedCovariantRepresentable Y ⟶
      S.finiteProjectiveStableCovariantRepresentable X :=
  S.finiteRestrictedCovariantRepresentableMap f ≫
    S.finiteProjectiveStableCovariantQuotient X

@[simp]
theorem finiteRestrictedToProjectiveStableCovariantMap_app_apply
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (Z : S.IndecCategory) (g : Y.obj ⟶ S.inclusion.obj Z) :
    (S.finiteRestrictedToProjectiveStableCovariantMap f).hom.hom.app Z g =
      ProjectiveStable.mk (k := k) (f.hom ≫ g) :=
  rfl

/-- The stable covariant image subobject generated by a module map. -/
def finiteProjectiveStableCovariantImageSubobject
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    Subobject (S.finiteProjectiveStableCovariantRepresentable X) :=
  imageSubobject (S.finiteRestrictedToProjectiveStableCovariantMap f)

/-- The object underlying the stable covariant image generated by a module
map. -/
def finiteProjectiveStableCovariantImage
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  S.finiteProjectiveStableCovariantImageSubobject f

/-- Inclusion of a generated stable covariant image into the represented
stable functor. -/
def finiteProjectiveStableCovariantImageInclusion
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    S.finiteProjectiveStableCovariantImage f ⟶
      S.finiteProjectiveStableCovariantRepresentable X :=
  (imageSubobject
    (S.finiteRestrictedToProjectiveStableCovariantMap f)).arrow

/-- Presentation of a generated stable covariant image by the corresponding
ordinary representable. -/
def finiteProjectiveStableCovariantImagePresentation
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    S.finiteRestrictedCovariantRepresentable Y ⟶
      S.finiteProjectiveStableCovariantImage f :=
  factorThruImageSubobject
    (S.finiteRestrictedToProjectiveStableCovariantMap f)

instance finiteProjectiveStableCovariantImagePresentation_epi
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    Epi (S.finiteProjectiveStableCovariantImagePresentation f) := by
  change Epi (factorThruImageSubobject
    (S.finiteRestrictedToProjectiveStableCovariantMap f))
  infer_instance

@[reassoc]
theorem finiteProjectiveStableCovariantImagePresentation_comp_inclusion
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    S.finiteProjectiveStableCovariantImagePresentation f ≫
        S.finiteProjectiveStableCovariantImageInclusion f =
      S.finiteRestrictedToProjectiveStableCovariantMap f :=
  imageSubobject_arrow_comp _

/-- Inclusion of generated image subfunctors lifts to factorization of the
generating module maps after passage to projective-stable Hom. -/
theorem exists_stableFactor_of_covariantImage_le
    {X Y Z : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y) (g : X ⟶ Z)
    (hfg : S.finiteProjectiveStableCovariantImageSubobject f ≤
      S.finiteProjectiveStableCovariantImageSubobject g) :
    ∃ t : Z ⟶ Y,
      S.finiteRestrictedToProjectiveStableCovariantMap (g ≫ t) =
        S.finiteRestrictedToProjectiveStableCovariantMap f := by
  let pf := S.finiteRestrictedToProjectiveStableCovariantMap f
  let pg := S.finiteRestrictedToProjectiveStableCovariantMap g
  let If := imageSubobject pf
  let Ig := imageSubobject pg
  have hfg' : If ≤ Ig := by
    exact hfg
  let qf : S.finiteRestrictedCovariantRepresentable Y ⟶ (If :
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k) :=
    factorThruImageSubobject pf
  let qg : S.finiteRestrictedCovariantRepresentable Z ⟶ (Ig :
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k) :=
    factorThruImageSubobject pg
  let j : (If : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k) ⟶ (Ig :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategory) k) :=
    Subobject.ofLE _ _ hfg'
  let b : S.finiteRestrictedCovariantRepresentable Y ⟶
      (Ig : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k) := qf ≫ j
  letI : Projective (S.finiteRestrictedCovariantRepresentable Y) :=
    S.finiteRestrictedCovariantRepresentable_projective Y
  let l : S.finiteRestrictedCovariantRepresentable Y ⟶
      S.finiteRestrictedCovariantRepresentable Z :=
    Projective.factorThru b qg
  have hl : l ≫ pg = pf := by
    rw [← imageSubobject_arrow_comp pg, ← Category.assoc,
      Projective.factorThru_comp]
    dsimp only [b, j, qf, If, Ig]
    rw [Category.assoc, Subobject.ofLE_arrow,
      imageSubobject_arrow_comp]
  obtain ⟨t, ht⟩ :=
    S.exists_eq_finiteRestrictedCovariantRepresentableMap Y Z l
  refine ⟨t, ?_⟩
  rw [finiteRestrictedToProjectiveStableCovariantMap,
    S.finiteRestrictedCovariantRepresentableMap_comp, ht]
  exact hl

/-- Uniseriality of the represented projective-stable covariant functor
makes the images generated by any two maps out of the represented module
comparable. -/
theorem finiteProjectiveStableCovariantImages_comparable
    {X : RightModule.FinitelyGeneratedCategory A}
    (hX : IsUniserialObject
      (S.finiteProjectiveStableCovariantRepresentable X))
    {Y Z : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y) (g : X ⟶ Z) :
    S.finiteProjectiveStableCovariantImageSubobject f ≤
        S.finiteProjectiveStableCovariantImageSubobject g ∨
      S.finiteProjectiveStableCovariantImageSubobject g ≤
        S.finiteProjectiveStableCovariantImageSubobject f :=
  hX.total _ _

/-- Vanishing of the restricted natural map into projective-stable covariant
Hom detects an actual factorization through a projective module.  Finite
additive density lets the chosen indecomposables test every target module. -/
theorem factorsThroughProjective_of_covariantStableMap_eq_zero
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (hf : S.finiteRestrictedToProjectiveStableCovariantMap f = 0) :
    Nonempty (ProjectiveStable.FactorsThroughProjective f.hom) := by
  letI : Module.Finite k Y :=
    RightModule.finite_over_field_of_finitelyGenerated k A Y
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) Y
  have hdense (j : Fin d.n) :
      ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
    S.fgObj_complete (d.summand j) (d.indecomposable j)
  choose i e using hdense
  let ej (j : Fin d.n) : d.summand j ≅ S.fgObj (i j) :=
    Classical.choice (e j)
  let q (j : Fin d.n) : Y ⟶ S.fgObj (i j) :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand j ≫ (ej j).hom
  let s (j : Fin d.n) : S.fgObj (i j) ⟶ Y :=
    (ej j).inv ≫ biproduct.ι d.summand j ≫ d.isoBiproduct.inv
  have hcomponent (j : Fin d.n) :
      Nonempty (ProjectiveStable.FactorsThroughProjective (f ≫ q j).hom) := by
    have hj := congrArg
      (fun a ↦ a.hom.hom.app (i j) (q j).hom) hf
    change ProjectiveStable.mk (k := k) ((f ≫ q j).hom) = 0 at hj
    have hmem : (f ≫ q j).hom ∈
        ProjectiveStable.factorSubmodule (k := k) X.obj
          (S.fgObj (i j)).obj :=
      (Submodule.Quotient.mk_eq_zero
        (ProjectiveStable.factorSubmodule (k := k) X.obj
          (S.fgObj (i j)).obj)).1 hj
    obtain ⟨hfactor⟩ := hmem
    exact ⟨hfactor⟩
  have hterm (j : Fin d.n) :
      (f ≫ q j ≫ s j).hom ∈
        ProjectiveStable.factorSubmodule (k := k) X.obj Y.obj := by
    obtain ⟨hj⟩ := hcomponent j
    exact ⟨hj.postcomp (s j).hom⟩
  have htotal : ∑ j, q j ≫ s j = 𝟙 Y := by
    calc
      ∑ j, q j ≫ s j =
          d.isoBiproduct.hom ≫
            (∑ j, biproduct.π d.summand j ≫
              biproduct.ι d.summand j) ≫ d.isoBiproduct.inv := by
        simp only [q, s, Category.assoc, Iso.hom_inv_id_assoc,
          Preadditive.comp_sum, Preadditive.sum_comp]
      _ = 𝟙 Y := by rw [biproduct.total]; simp
  have hsum : (∑ j, (f ≫ q j ≫ s j).hom) ∈
      ProjectiveStable.factorSubmodule (k := k) X.obj Y.obj :=
    Submodule.sum_mem _ (fun j _ ↦ hterm j)
  have htotalUnderlying : ∑ j, (q j ≫ s j).hom = 𝟙 Y.obj := by
    have hmap :
        (∑ j, q j ≫ s j).hom = ∑ j, (q j ≫ s j).hom :=
      map_sum
        (InducedCategory.homAddEquiv :
          (Y ⟶ Y) ≃+ (Y.obj ⟶ Y.obj))
        (fun j ↦ q j ≫ s j) Finset.univ
    calc
      ∑ j, (q j ≫ s j).hom = (∑ j, q j ≫ s j).hom := hmap.symm
      _ = (𝟙 Y : Y ⟶ Y).hom :=
        congrArg (fun a : Y ⟶ Y ↦ a.hom) htotal
      _ = 𝟙 Y.obj := rfl
  have heq : ∑ j, (f ≫ q j ≫ s j).hom = f.hom := by
    calc
      ∑ j, (f ≫ q j ≫ s j).hom =
          ∑ j, f.hom ≫ (q j ≫ s j).hom := by
        rfl
      _ = f.hom ≫ ∑ j, (q j ≫ s j).hom := by
        rw [Preadditive.comp_sum]
      _ = f.hom := by rw [htotalUnderlying, Category.comp_id]
  rw [heq] at hsum
  exact hsum

@[simp]
theorem finiteRestrictedToProjectiveStableCovariantMap_sub
    {X Y : RightModule.FinitelyGeneratedCategory A} (f g : X ⟶ Y) :
    S.finiteRestrictedToProjectiveStableCovariantMap (f - g) =
      S.finiteRestrictedToProjectiveStableCovariantMap f -
        S.finiteRestrictedToProjectiveStableCovariantMap g := by
  let F := S.finiteRestrictedCovariantRepresentableFunctor
  have hmap :
      S.finiteRestrictedCovariantRepresentableMap (f - g) =
        S.finiteRestrictedCovariantRepresentableMap f -
          S.finiteRestrictedCovariantRepresentableMap g := by
    change F.map ((f - g).op) = F.map f.op - F.map g.op
    simpa using F.map_sub f.op g.op
  rw [finiteRestrictedToProjectiveStableCovariantMap,
    finiteRestrictedToProjectiveStableCovariantMap,
    finiteRestrictedToProjectiveStableCovariantMap, hmap,
    Preadditive.sub_comp]

/-- Equality of the induced stable natural maps means that the difference
of the underlying module maps factors through a projective. -/
theorem factorsThroughProjective_of_covariantStableMaps_eq
    {X Y : RightModule.FinitelyGeneratedCategory A} (f g : X ⟶ Y)
    (hfg : S.finiteRestrictedToProjectiveStableCovariantMap f =
      S.finiteRestrictedToProjectiveStableCovariantMap g) :
    Nonempty (ProjectiveStable.FactorsThroughProjective (f - g).hom) := by
  apply S.factorsThroughProjective_of_covariantStableMap_eq_zero
  rw [S.finiteRestrictedToProjectiveStableCovariantMap_sub, hfg, sub_self]

/-- The comparison conclusion used in Auslander--Reiten, Proposition 1.1(a):
for two maps out of `X`, one differs stably from a composite through the
other. -/
theorem stableFactorization_dichotomy_of_covariantUniserial
    {X : RightModule.FinitelyGeneratedCategory A}
    (hX : IsUniserialObject
      (S.finiteProjectiveStableCovariantRepresentable X))
    {Y Z : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y) (g : X ⟶ Z) :
    (∃ t : Z ⟶ Y,
        Nonempty (ProjectiveStable.FactorsThroughProjective
          (f - g ≫ t).hom)) ∨
      (∃ t : Y ⟶ Z,
        Nonempty (ProjectiveStable.FactorsThroughProjective
          (g - f ≫ t).hom)) := by
  rcases S.finiteProjectiveStableCovariantImages_comparable hX f g with
      hfg | hgf
  · obtain ⟨t, ht⟩ := S.exists_stableFactor_of_covariantImage_le f g hfg
    left
    refine ⟨t, ?_⟩
    exact S.factorsThroughProjective_of_covariantStableMaps_eq
      f (g ≫ t) ht.symm
  · obtain ⟨t, ht⟩ := S.exists_stableFactor_of_covariantImage_le g f hgf
    right
    refine ⟨t, ?_⟩
    exact S.factorsThroughProjective_of_covariantStableMaps_eq
      g (f ≫ t) ht.symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
