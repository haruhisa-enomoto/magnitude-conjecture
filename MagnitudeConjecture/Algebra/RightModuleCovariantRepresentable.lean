import MagnitudeConjecture.Algebra.RightModuleStableRepresentable

/-!
# Covariant representables on the finite module skeleton

This file packages the ordinary functor `Hom(X, -)` restricted to the finite
skeleton of indecomposable right modules. Stable and costable quotients are
built in separate leaf files.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The ordinary covariant representable `Hom(X, -)` restricted to the
finite indecomposable skeleton. -/
def restrictedCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.IndecCategory ⥤ ModuleCat.{u} k where
  obj Y := ModuleCat.of k (X.obj ⟶ S.inclusion.obj Y)
  map f := ModuleCat.ofHom <| CategoryTheory.Linear.rightComp k X.obj
    (S.inclusion.map f)
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change h ≫ S.inclusion.map (f ≫ g) =
      (h ≫ S.inclusion.map f) ≫ S.inclusion.map g
    rw [Functor.map_comp]
    rw [Category.assoc]

instance restrictedCovariantRepresentable_additive
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.restrictedCovariantRepresentable X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    let h' : X.obj ⟶ S.inclusion.obj Y := h
    change h' ≫ (S.inclusion.map f + S.inclusion.map g) =
      h' ≫ S.inclusion.map f + h' ≫ S.inclusion.map g
    rw [Preadditive.comp_add]

instance restrictedCovariantRepresentable_linear
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.restrictedCovariantRepresentable X).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    let h' : X.obj ⟶ S.inclusion.obj _ := h
    change h' ≫ (r • S.inclusion.map f) = r • (h' ≫ S.inclusion.map f)
    rw [CategoryTheory.Linear.comp_smul]

/-- The ordinary restricted covariant representable as a linear module. -/
def restrictedCovariantRepresentableLinearModule
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.LinearModuleCategory (C := S.IndecCategory) k :=
  ⟨S.restrictedCovariantRepresentable X, inferInstance, inferInstance⟩

/-- The ordinary restricted covariant representable is finite-dimensional on
the finite indecomposable skeleton. -/
theorem restrictedCovariantRepresentable_isFiniteDimensional
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
      (S.restrictedCovariantRepresentableLinearModule X) := by
  constructor
  · intro Y
    letI : Module.Finite k X.obj :=
      RightModule.finite_over_field_of_finitelyGenerated k A X
    letI : Module.Finite k (S.inclusion.obj Y) :=
      S.indecCategory_obj_finite Y
    exact moduleCat_hom_finite (k := k) (A := A) X.obj
      (S.inclusion.obj Y)
  · exact Set.toFinite _

/-- The ordinary restricted covariant representable in the finite functor
category. -/
def finiteRestrictedCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  ⟨S.restrictedCovariantRepresentableLinearModule X,
    S.restrictedCovariantRepresentable_isFiniteDimensional X⟩

/-- The covariant representable of a chosen skeleton object is
finite-dimensional. -/
def indecCovariantRepresentableFinite (i : S.IndecCategory) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
      (CoveringHom.linearCoyonedaLinearModule (k := k) i) := by
  constructor
  · intro Y
    letI : Module.Finite k (S.inclusion.obj i) :=
      S.indecCategory_obj_finite i
    letI : Module.Finite k (S.inclusion.obj Y) :=
      S.indecCategory_obj_finite Y
    exact (moduleCat_hom_finite (k := k) (A := A)
      (S.inclusion.obj i) (S.inclusion.obj Y)).equiv
        (InducedCategory.homLinearEquiv (R := k)).symm
  · exact Set.toFinite _

/-- Ambient morphisms out of a chosen skeleton object are the intrinsic
morphisms of the induced skeleton. -/
def restrictedFgObjHomLinearEquiv
    (i Y : S.IndecCategory) :
    ((S.fgObj i).obj ⟶ S.inclusion.obj Y) ≃ₗ[k] (i ⟶ Y) where
  toFun f := InducedCategory.homMk f
  invFun f := f.hom
  left_inv _ := rfl
  right_inv f := by
    apply InducedCategory.hom_ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricted ambient covariant Yoneda at a chosen indecomposable agrees
naturally with intrinsic covariant Yoneda on the finite skeleton. -/
def restrictedCovariantRepresentableFgObjRawIso
    (i : S.IndecCategory) :
    S.restrictedCovariantRepresentable (S.fgObj i) ≅
      (CategoryTheory.linearCoyoneda k S.IndecCategory).obj
        (Opposite.op i) := by
  refine NatIso.ofComponents (fun Y ↦
    (S.restrictedFgObjHomLinearEquiv i Y).toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  rfl

/-- Linear-module form of restricted covariant Yoneda on a chosen
indecomposable. -/
def restrictedCovariantRepresentableFgObjLinearIso
    (i : S.IndecCategory) :
    S.restrictedCovariantRepresentableLinearModule (S.fgObj i) ≅
      CoveringHom.linearCoyonedaLinearModule (k := k) i :=
  ObjectProperty.isoMk _
    (S.restrictedCovariantRepresentableFgObjRawIso i)

/-- Finite-module form of restricted covariant Yoneda on a chosen
indecomposable. -/
def finiteRestrictedCovariantRepresentableFgObjIso
    (i : S.IndecCategory) :
    S.finiteRestrictedCovariantRepresentable (S.fgObj i) ≅
      CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) i (S.indecCovariantRepresentableFinite i) :=
  ObjectProperty.isoMk _
    (S.restrictedCovariantRepresentableFgObjLinearIso i)

instance finiteRestrictedCovariantRepresentableFgObj_projective
    (i : S.IndecCategory) :
    Projective (S.finiteRestrictedCovariantRepresentable (S.fgObj i)) :=
  Projective.of_iso
    (S.finiteRestrictedCovariantRepresentableFgObjIso i).symm
      inferInstance

/-- Precomposition gives the expected variance-reversing map between
restricted covariant representables. -/
def finiteRestrictedCovariantRepresentableMap
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) :
    S.finiteRestrictedCovariantRepresentable Y ⟶
      S.finiteRestrictedCovariantRepresentable X :=
  ObjectProperty.homMk <| ObjectProperty.homMk
    { app := fun Z ↦ ModuleCat.ofHom <|
        CategoryTheory.Linear.leftComp k (S.inclusion.obj Z) f.hom
      naturality := by
        intro Z W g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro h
        exact (Category.assoc f.hom h (S.inclusion.map g)).symm }

@[simp]
theorem finiteRestrictedCovariantRepresentableMap_app_apply
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (Z : S.IndecCategory) (g : Y.obj ⟶ S.inclusion.obj Z) :
    (S.finiteRestrictedCovariantRepresentableMap f).hom.hom.app Z g =
      f.hom ≫ g :=
  rfl

/-- Restricted covariant Yoneda is full on chosen indecomposables.  The
variance reversal recovers a module map by evaluating at the identity. -/
theorem finiteRestrictedCovariantRepresentableMap_fgObj_eq
    (i j : S.IndecCategory)
    (a : S.finiteRestrictedCovariantRepresentable (S.fgObj i) ⟶
      S.finiteRestrictedCovariantRepresentable (S.fgObj j)) :
    let f : S.fgObj j ⟶ S.fgObj i := ObjectProperty.homMk (by
      change S.obj j ⟶ S.obj i
      exact a.hom.hom.app i (𝟙 (S.inclusion.obj i)))
    S.finiteRestrictedCovariantRepresentableMap f = a := by
  dsimp
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  let q' : i ⟶ X := InducedCategory.homMk q
  have h := ConcreteCategory.congr_hom (a.hom.hom.naturality q')
    (𝟙 (S.inclusion.obj i))
  exact h.symm

@[simp]
theorem finiteRestrictedCovariantRepresentableMap_comp
    {X Y Z : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.finiteRestrictedCovariantRepresentableMap (f ≫ g) =
      S.finiteRestrictedCovariantRepresentableMap g ≫
        S.finiteRestrictedCovariantRepresentableMap f := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  exact Category.assoc f.hom g.hom h

@[simp]
theorem finiteRestrictedCovariantRepresentableMap_id
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.finiteRestrictedCovariantRepresentableMap (𝟙 X) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  exact Category.id_comp h

@[simp]
theorem finiteRestrictedCovariantRepresentableMap_add
    {X Y : RightModule.FinitelyGeneratedCategory A} (f g : X ⟶ Y) :
    S.finiteRestrictedCovariantRepresentableMap (f + g) =
      S.finiteRestrictedCovariantRepresentableMap f +
        S.finiteRestrictedCovariantRepresentableMap g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  let h' : Y.obj ⟶ S.inclusion.obj Z := h
  change (f.hom + g.hom) ≫ h' = f.hom ≫ h' + g.hom ≫ h'
  rw [Preadditive.add_comp]

@[simp]
theorem finiteRestrictedCovariantRepresentableMap_zero
    (X Y : RightModule.FinitelyGeneratedCategory A) :
    S.finiteRestrictedCovariantRepresentableMap (0 : X ⟶ Y) = 0 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  let h' : Y.obj ⟶ S.inclusion.obj Z := h
  change (0 : X.obj ⟶ Y.obj) ≫ h' = 0
  rw [CategoryTheory.Limits.zero_comp]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
