import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Restricted linear Yoneda modules

For a linear functor `J : P ⥤ C`, restriction of the contravariant
representable `C(-, X)` to `P` is a covariant linear module on `Pᵒᵖ`.
Bundling these restricted representables functorially in `X` is the formal
core of the Bongartz--Gabriel recovery functor

`C ⟶ mod(P),    X ↦ C(-, X)|_P`.

This file only constructs the functor and its finite-dimensional restriction.
Full faithfulness and essential surjectivity are the substantive Auslander-
category assertions and are deliberately not assumed here.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {P : Type w} [Category.{v} P] [Preadditive P] [Linear k P]
variable (J : P ⥤ C) [J.Additive] [J.Linear k]

noncomputable local instance [Fintype P] : Fintype Pᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

/-- The contravariant representable `C(-, X)`, restricted along `J`, as a
module on `Pᵒᵖ`. -/
def restrictedLinearYoneda (X : C) : Pᵒᵖ ⥤ ModuleCat k :=
  J.op ⋙ (linearYoneda k C).obj X

noncomputable instance restrictedLinearYoneda_additive (X : C) :
    (restrictedLinearYoneda (k := k) J X).Additive := by
  dsimp only [restrictedLinearYoneda]
  infer_instance

noncomputable instance restrictedLinearYoneda_linear (X : C) :
    (restrictedLinearYoneda (k := k) J X).Linear k := by
  constructor
  intro Y Z f r
  apply ModuleCat.hom_ext
  ext h
  change J.map ((r • f).unop) ≫ h = r • (J.map f.unop ≫ h)
  rw [opposite_unop_smul, J.map_smul, CategoryTheory.Linear.smul_comp]

/-- Bundled additive linear-module form of a restricted representable. -/
def restrictedLinearYonedaLinearModule (X : C) :
    LinearModuleCategory (C := Pᵒᵖ) k :=
  ⟨restrictedLinearYoneda (k := k) J X, inferInstance, inferInstance⟩

/-- A map of representing objects induces the corresponding map of
restricted representables. -/
def restrictedLinearYonedaLinearModuleMap {X Y : C} (f : X ⟶ Y) :
    restrictedLinearYonedaLinearModule (k := k) J X ⟶
      restrictedLinearYonedaLinearModule (k := k) J Y :=
  ObjectProperty.homMk
    (Functor.whiskerLeft J.op ((linearYoneda k C).map f))

@[simp]
theorem restrictedLinearYonedaLinearModuleMap_id (X : C) :
    restrictedLinearYonedaLinearModuleMap (k := k) J (𝟙 X) =
      𝟙 (restrictedLinearYonedaLinearModule (k := k) J X) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  ext h
  change h ≫ 𝟙 X = h
  simp

@[simp]
theorem restrictedLinearYonedaLinearModuleMap_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrictedLinearYonedaLinearModuleMap (k := k) J (f ≫ g) =
      restrictedLinearYonedaLinearModuleMap (k := k) J f ≫
        restrictedLinearYonedaLinearModuleMap (k := k) J g := by
  apply ObjectProperty.hom_ext
  change Functor.whiskerLeft J.op ((linearYoneda k C).map (f ≫ g)) =
    Functor.whiskerLeft J.op ((linearYoneda k C).map f) ≫
      Functor.whiskerLeft J.op ((linearYoneda k C).map g)
  rw [Functor.map_comp, Functor.whiskerLeft_comp]

/-- The restricted Yoneda realization, before imposing any finiteness
condition on its values. -/
def restrictedLinearYonedaFunctor :
    C ⥤ LinearModuleCategory (C := Pᵒᵖ) k where
  obj X := restrictedLinearYonedaLinearModule (k := k) J X
  map f := restrictedLinearYonedaLinearModuleMap (k := k) J f
  map_id := restrictedLinearYonedaLinearModuleMap_id (k := k) J
  map_comp := restrictedLinearYonedaLinearModuleMap_comp (k := k) J

noncomputable instance restrictedLinearYonedaFunctor_additive :
    (restrictedLinearYonedaFunctor (k := k) J).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    ext h
    change h ≫ (f + g) = h ≫ f + h ≫ g
    rw [Preadditive.comp_add]

noncomputable instance restrictedLinearYonedaFunctor_linear :
    (restrictedLinearYonedaFunctor (k := k) J).Linear k where
  map_smul := by
    intro X Y f r
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    ext h
    change h ≫ (r • f) = r • (h ≫ f)
    rw [CategoryTheory.Linear.comp_smul]

/-- Restricted Yoneda is faithful as soon as the selected source objects
detect every nonzero ambient morphism by precomposition. -/
theorem restrictedLinearYonedaFunctor_faithful_of_sourceDetection
    (hdetect : ∀ {X Y : C} (f : X ⟶ Y), f ≠ 0 →
      ∃ (Z : P) (g : J.obj Z ⟶ X), g ≫ f ≠ 0) :
    (restrictedLinearYonedaFunctor (k := k) J).Faithful where
  map_injective := by
    intro X Y f g hfg
    apply sub_eq_zero.mp
    by_contra hne
    obtain ⟨Z, q, hq⟩ := hdetect (f - g) hne
    have happ := congrArg
      (fun t ↦ t.hom.app (Opposite.op Z)) hfg
    have hvalue := ConcreteCategory.congr_hom happ q
    change q ≫ f = q ≫ g at hvalue
    apply hq
    rw [Preadditive.comp_sub, hvalue, sub_self]

@[simp]
theorem restrictedLinearYoneda_obj_obj
    (X : C) (Y : Pᵒᵖ) :
    ((restrictedLinearYonedaLinearModule (k := k) J X).obj.obj Y) =
      ModuleCat.of k (J.obj Y.unop ⟶ X) :=
  rfl

@[simp]
theorem restrictedLinearYoneda_map_app_apply
    {X Y : C} (f : X ⟶ Y) (W : Pᵒᵖ)
    (h : J.obj W.unop ⟶ X) :
    (restrictedLinearYonedaLinearModuleMap (k := k) J f).hom.app W h =
      h ≫ f :=
  rfl

/-- Pointwise finite-dimensional ambient Hom spaces and finite incoming
support make a restricted representable a finite-dimensional module. -/
theorem restrictedLinearYoneda_isFiniteDimensional_of_finite_support
    (X : C)
    (hfinite : ∀ Y : P, FiniteDimensional k (J.obj Y ⟶ X)) :
    {Y : Pᵒᵖ | Nontrivial (J.obj Y.unop ⟶ X)}.Finite →
    IsFiniteDimensionalModule (C := Pᵒᵖ) k
      (restrictedLinearYonedaLinearModule (k := k) J X) := by
  intro hsupport
  constructor
  · intro Y
    change FiniteDimensional k (J.obj Y.unop ⟶ X)
    exact hfinite Y.unop
  · exact hsupport

/-- On a finite source subcategory, finite-dimensional ambient Hom spaces
make a restricted representable a finite-dimensional module. -/
theorem restrictedLinearYoneda_isFiniteDimensional
    [Fintype P] (X : C)
    (hfinite : ∀ Y : P, FiniteDimensional k (J.obj Y ⟶ X)) :
    IsFiniteDimensionalModule (C := Pᵒᵖ) k
      (restrictedLinearYonedaLinearModule (k := k) J X) :=
  restrictedLinearYoneda_isFiniteDimensional_of_finite_support
    (k := k) J X hfinite (Set.toFinite _)

/-- Restricted Yoneda with a finite-dimensional target, using finite incoming
support rather than finiteness of the entire source category. -/
def finiteSupportRestrictedLinearYonedaFunctor
    (hproperty : ∀ X : C,
      IsFiniteDimensionalModule (C := Pᵒᵖ) k
        (restrictedLinearYonedaLinearModule (k := k) J X)) :
    C ⥤ FiniteDimensionalModuleCategory (C := Pᵒᵖ) k :=
  (IsFiniteDimensionalModule (C := Pᵒᵖ) k).lift
    (restrictedLinearYonedaFunctor (k := k) J)
    hproperty

noncomputable instance finiteSupportRestrictedLinearYonedaFunctor_additive
    (hproperty : ∀ X : C,
      IsFiniteDimensionalModule (C := Pᵒᵖ) k
        (restrictedLinearYonedaLinearModule (k := k) J X)) :
    (finiteSupportRestrictedLinearYonedaFunctor
      (k := k) J hproperty).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change (restrictedLinearYonedaFunctor (k := k) J).map (f + g) =
      (restrictedLinearYonedaFunctor (k := k) J).map f +
        (restrictedLinearYonedaFunctor (k := k) J).map g
    exact (restrictedLinearYonedaFunctor (k := k) J).map_add

noncomputable instance finiteSupportRestrictedLinearYonedaFunctor_linear
    (hproperty : ∀ X : C,
      IsFiniteDimensionalModule (C := Pᵒᵖ) k
        (restrictedLinearYonedaLinearModule (k := k) J X)) :
    (finiteSupportRestrictedLinearYonedaFunctor
      (k := k) J hproperty).Linear k where
  map_smul := by
    intro X Y f r
    apply ObjectProperty.hom_ext
    change (restrictedLinearYonedaFunctor (k := k) J).map (r • f) =
      r • (restrictedLinearYonedaFunctor (k := k) J).map f
    exact (restrictedLinearYonedaFunctor (k := k) J).map_smul r f

/-- The finite-support target restriction preserves the source-detection
criterion for faithfulness. -/
theorem finiteSupportRestrictedLinearYonedaFunctor_faithful_of_sourceDetection
    (hproperty : ∀ X : C,
      IsFiniteDimensionalModule (C := Pᵒᵖ) k
        (restrictedLinearYonedaLinearModule (k := k) J X))
    (hdetect : ∀ {X Y : C} (f : X ⟶ Y), f ≠ 0 →
      ∃ (Z : P) (g : J.obj Z ⟶ X), g ≫ f ≠ 0) :
    (finiteSupportRestrictedLinearYonedaFunctor
      (k := k) J hproperty).Faithful where
  map_injective := by
    intro X Y f g hfg
    let F := restrictedLinearYonedaFunctor (k := k) J
    let hF : F.Faithful :=
      restrictedLinearYonedaFunctor_faithful_of_sourceDetection
        (k := k) J hdetect
    apply hF.map_injective
    exact congrArg (fun t ↦ t.hom) hfg

/-- The finite-dimensional restricted Yoneda realization. -/
def finiteRestrictedLinearYonedaFunctor
    [Fintype P]
    (hfinite : ∀ (X : C) (Y : P),
      FiniteDimensional k (J.obj Y ⟶ X)) :
    C ⥤ FiniteDimensionalModuleCategory (C := Pᵒᵖ) k :=
  (IsFiniteDimensionalModule (C := Pᵒᵖ) k).lift
    (restrictedLinearYonedaFunctor (k := k) J)
    (fun X ↦ restrictedLinearYoneda_isFiniteDimensional
      (k := k) J X (hfinite X))

noncomputable instance finiteRestrictedLinearYonedaFunctor_additive
    [Fintype P]
    (hfinite : ∀ (X : C) (Y : P),
      FiniteDimensional k (J.obj Y ⟶ X)) :
    (finiteRestrictedLinearYonedaFunctor (k := k) J hfinite).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change (restrictedLinearYonedaFunctor (k := k) J).map (f + g) =
      (restrictedLinearYonedaFunctor (k := k) J).map f +
        (restrictedLinearYonedaFunctor (k := k) J).map g
    exact (restrictedLinearYonedaFunctor (k := k) J).map_add

noncomputable instance finiteRestrictedLinearYonedaFunctor_linear
    [Fintype P]
    (hfinite : ∀ (X : C) (Y : P),
      FiniteDimensional k (J.obj Y ⟶ X)) :
    (finiteRestrictedLinearYonedaFunctor (k := k) J hfinite).Linear k where
  map_smul := by
    intro X Y f r
    apply ObjectProperty.hom_ext
    change (restrictedLinearYonedaFunctor (k := k) J).map (r • f) =
      r • (restrictedLinearYonedaFunctor (k := k) J).map f
    exact (restrictedLinearYonedaFunctor (k := k) J).map_smul r f

/-- The finite-dimensional target restriction preserves the preceding
source-detection criterion for faithfulness. -/
theorem finiteRestrictedLinearYonedaFunctor_faithful_of_sourceDetection
    [Fintype P]
    (hfinite : ∀ (X : C) (Y : P),
      FiniteDimensional k (J.obj Y ⟶ X))
    (hdetect : ∀ {X Y : C} (f : X ⟶ Y), f ≠ 0 →
      ∃ (Z : P) (g : J.obj Z ⟶ X), g ≫ f ≠ 0) :
    (finiteRestrictedLinearYonedaFunctor (k := k) J hfinite).Faithful where
  map_injective := by
    intro X Y f g hfg
    let F := restrictedLinearYonedaFunctor (k := k) J
    let hF : F.Faithful :=
      restrictedLinearYonedaFunctor_faithful_of_sourceDetection
        (k := k) J hdetect
    apply hF.map_injective
    exact congrArg (fun t ↦ t.hom) hfg

end MagnitudeConjecture.CoveringHom
