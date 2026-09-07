import MagnitudeConjecture.CategoryTheory.OrbitPushdownCommShift
import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso
import MagnitudeConjecture.LinearAlgebra.DirectSumFubini
import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive

/-!
# Descent of shift-compatible functors through shift-orbit categories

A functor commuting coherently with shifts acts on homogeneous shifted
morphisms and hence on their finite-support direct sums.  If its target has
the trivial shift, summing the target degree components gives a descended
functor from the source shift-orbit category.  The final section applies this
construction to Gabriel orbit push-down.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.DirectSumFubini

namespace MagnitudeConjecture.CoveringHom

universe uC vC uD vD w uK

variable {k : Type uK} [CommSemiring k]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable {E : Type uD} [Category.{vD} E] [Preadditive E]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k E]
variable {A : Type w} [AddMonoid A] [HasShift C A] [HasShift E A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]
variable [∀ a : A, (shiftFunctor E a).Additive]
variable [∀ a : A, (shiftFunctor E a).Linear k]
variable (F : CategoryTheory.Functor C E) [F.Additive] [F.Linear k]
variable [F.CommShift A]

/-- The image of a homogeneous shifted morphism under a shift-compatible
functor. -/
def shiftOrbitDescendHomogeneousMap
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    ShiftHom (F.obj X) (F.obj Y) a :=
  F.map f ≫ (F.commShiftIso a).hom.app Y

set_option backward.isDefEq.respectTransparency false in
omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor E a).Additive] [F.Additive]
  [Preadditive C] [Preadditive E] in
@[simp]
theorem shiftOrbitDescendHomogeneousMap_id (X : C) :
    shiftOrbitDescendHomogeneousMap F (0 : A) (shiftHomId (A := A) X) =
      shiftHomId (A := A) (F.obj X) := by
  simp [shiftOrbitDescendHomogeneousMap, shiftHomId,
    F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
    ← F.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor E a).Additive] [F.Additive]
  [Preadditive C] [Preadditive E] in
theorem shiftOrbitDescendHomogeneousMap_comp
    {X Y Z : C} {a b : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftOrbitDescendHomogeneousMap F (b + a) (shiftHomComp f g) =
      shiftHomComp (shiftOrbitDescendHomogeneousMap F a f)
        (shiftOrbitDescendHomogeneousMap F b g) := by
  unfold shiftOrbitDescendHomogeneousMap shiftHomComp shiftHomComp'
  rw [F.map_comp, F.map_comp]
  have hadd := congrArg Iso.hom (F.commShiftIso_add b a)
  have haddZ := NatTrans.congr_app hadd Z
  simp only [Functor.CommShift.isoAdd_hom_app] at haddZ
  rw [haddZ]
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc]
  rw [← F.map_comp_assoc
    ((shiftFunctorAdd C b a).inv.app Z)
    ((shiftFunctorAdd C b a).hom.app Z)]
  simp only [Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [F.commShiftIso_hom_naturality_assoc g a]
  simp only [Functor.map_comp, Category.assoc]

/-- The homogeneous action of a shift-compatible linear functor is linear. -/
def shiftOrbitDescendHomogeneousLinearMap
    {X Y : C} (a : A) :
    ShiftHom X Y a →ₗ[k] ShiftHom (F.obj X) (F.obj Y) a where
  toFun := shiftOrbitDescendHomogeneousMap F a
  map_add' f g := by
    simp [shiftOrbitDescendHomogeneousMap, F.map_add,
      Preadditive.add_comp]
  map_smul' r f := by
    simp [shiftOrbitDescendHomogeneousMap, F.map_smul,
      CategoryTheory.Linear.smul_comp]

/-- A full and faithful shift-compatible linear functor gives a linear
equivalence on every homogeneous shifted Hom module. -/
noncomputable def shiftOrbitDescendHomogeneousLinearEquiv
    [F.Full] [F.Faithful] (X Y : C) (a : A) :
    ShiftHom X Y a ≃ₗ[k] ShiftHom (F.obj X) (F.obj Y) a :=
  (LinearEquiv.ofBijective (F.mapLinearMap k)
    ⟨F.map_injective, F.map_surjective⟩).trans
      (CategoryTheory.Linear.homCongr k (Iso.refl (F.obj X))
        ((F.commShiftIso a).app Y))

/-- The induced map on shift-orbit Hom modules is a linear equivalence when
the original functor is full and faithful. -/
noncomputable def shiftOrbitMapHomLinearEquiv
    [F.Full] [F.Faithful] (X Y : C) :
    ShiftOrbitHom A X Y ≃ₗ[k]
      ShiftOrbitHom A (F.obj X) (F.obj Y) :=
  mapRangeLinearEquiv fun a ↦
    shiftOrbitDescendHomogeneousLinearEquiv F X Y a

/-- The induced linear map on finite-support shift-orbit morphisms. -/
noncomputable def shiftOrbitDescendMapLinear
    {X Y : C} :
    ShiftOrbitHom A X Y →ₗ[k]
      ShiftOrbitHom A (F.obj X) (F.obj Y) := by
  classical
  exact DirectSum.toModule k A _ fun a ↦
    (shiftOrbitLof (k := k) (F.obj X) (F.obj Y) a).comp
      (shiftOrbitDescendHomogeneousLinearMap F a)

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [∀ a : A, (shiftFunctor E a).Additive]
  [∀ a : A, (shiftFunctor E a).Linear k] in
@[simp]
theorem shiftOrbitDescendMapLinear_of
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    shiftOrbitDescendMapLinear (k := k) F (shiftOrbitOf X Y a f) =
      shiftOrbitOf (F.obj X) (F.obj Y) a
        (shiftOrbitDescendHomogeneousMap F a f) := by
  classical
  change shiftOrbitDescendMapLinear (k := k) F
      (DirectSum.lof k A (fun c ↦ ShiftHom X Y c) a f) = _
  simp [shiftOrbitDescendMapLinear,
    shiftOrbitDescendHomogeneousLinearMap]

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor E a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [∀ a : A, (shiftFunctor E a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftOrbitMapHomLinearEquiv_apply
    [F.Full] [F.Faithful] {X Y : C} (f : ShiftOrbitHom A X Y) :
    shiftOrbitMapHomLinearEquiv (k := k) F X Y f =
      shiftOrbitDescendMapLinear (k := k) F f := by
  classical
  apply LinearMap.congr_fun
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro fa
  change shiftOrbitMapHomLinearEquiv (k := k) F X Y
      (DirectSum.of (fun c : A ↦ ShiftHom X Y c) a fa) =
    shiftOrbitDescendMapLinear (k := k) F
      (DirectSum.of (fun c : A ↦ ShiftHom X Y c) a fa)
  unfold shiftOrbitMapHomLinearEquiv
  rw [mapRangeLinearEquiv_of]
  rw [← shiftOrbitOf_eq_directSumOf X Y a fa,
    shiftOrbitDescendMapLinear_of]
  rw [shiftOrbitOf_eq_directSumOf]
  simp [shiftOrbitDescendHomogeneousLinearEquiv,
    shiftOrbitDescendHomogeneousMap,
    CategoryTheory.Linear.homCongr]

omit [∀ a : A, (shiftFunctor C a).Linear k]
  [∀ a : A, (shiftFunctor E a).Linear k] in
/-- The induced map respects finite-support convolution. -/
theorem shiftOrbitDescendMapLinear_comp
    {X Y Z : C} (f : ShiftOrbitHom A X Y) (g : ShiftOrbitHom A Y Z) :
    shiftOrbitDescendMapLinear (k := k) F (shiftOrbitCompHom f g) =
      shiftOrbitCompHom (shiftOrbitDescendMapLinear (k := k) F f)
        (shiftOrbitDescendMapLinear (k := k) F g) := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro b gb
      change shiftOrbitDescendMapLinear (k := k) F
          (shiftOrbitCompHom (shiftOrbitOf X Y a fa)
            (shiftOrbitOf Y Z b gb)) =
        shiftOrbitCompHom
          (shiftOrbitDescendMapLinear (k := k) F
            (shiftOrbitOf X Y a fa))
          (shiftOrbitDescendMapLinear (k := k) F
            (shiftOrbitOf Y Z b gb))
      rw [shiftOrbitCompHom_of_of, shiftOrbitDescendMapLinear_of,
        shiftOrbitDescendMapLinear_of, shiftOrbitDescendMapLinear_of,
        shiftOrbitCompHom_of_of, shiftOrbitDescendHomogeneousMap_comp]
    · intro g₁ g₂ hg₁ hg₂
      simpa only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using
        congrArg₂ (.+.) hg₁ hg₂
  · intro f₁ f₂ hf₁ hf₂
    simpa only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using
      congrArg₂ (.+.) hf₁ hf₂

/-- A shift-compatible linear functor induces a linear functor between its
source and target shift-orbit categories. -/
noncomputable def shiftOrbitMapFunctor :
    CategoryTheory.Functor (ShiftOrbitCategory C A) (ShiftOrbitCategory E A) where
  obj X := F.obj (show C from X)
  map f := shiftOrbitDescendMapLinear (k := k) F f
  map_id X := by
    change shiftOrbitDescendMapLinear (k := k) F
        (shiftOrbitId (show C from X)) =
      shiftOrbitId (F.obj (show C from X))
    rw [shiftOrbitId, shiftOrbitDescendMapLinear_of,
      shiftOrbitDescendHomogeneousMap_id]
    rfl
  map_comp f g := shiftOrbitDescendMapLinear_comp F f g

instance shiftOrbitMapFunctor_additive :
    (shiftOrbitMapFunctor (k := k) (A := A) F).Additive where
  map_add := by
    intro X Y f g
    exact (shiftOrbitDescendMapLinear (k := k) F).map_add f g

instance shiftOrbitMapFunctor_linear :
    (shiftOrbitMapFunctor (k := k) (A := A) F).Linear k where
  map_smul f r :=
    (shiftOrbitDescendMapLinear (k := k) F).map_smul r f

instance shiftOrbitMapFunctor_full [F.Full] [F.Faithful] :
    (shiftOrbitMapFunctor (k := k) (A := A) F).Full where
  map_surjective {X Y} f := by
    let e := shiftOrbitMapHomLinearEquiv
      (k := k) (A := A) F (show C from X) (show C from Y)
    refine ⟨e.symm f, ?_⟩
    change shiftOrbitDescendMapLinear (k := k) F (e.symm f) = f
    rw [← shiftOrbitMapHomLinearEquiv_apply (k := k) (A := A) F]
    exact e.apply_symm_apply f

instance shiftOrbitMapFunctor_faithful [F.Full] [F.Faithful] :
    (shiftOrbitMapFunctor (k := k) (A := A) F).Faithful where
  map_injective {X Y} f g h := by
    let e := shiftOrbitMapHomLinearEquiv
      (k := k) (A := A) F (show C from X) (show C from Y)
    apply e.injective
    rw [shiftOrbitMapHomLinearEquiv_apply,
      shiftOrbitMapHomLinearEquiv_apply]
    exact h

section TrivialShiftFold

variable {T : Type uD} [Category.{vD} T] [Preadditive T]
variable [CategoryTheory.Linear k T]

local instance : HasShift T A := trivialHasShift T A

local instance (a : A) : (shiftFunctor T a).Additive := by
  change (CategoryTheory.Functor.id T).Additive
  infer_instance

local instance (a : A) : (shiftFunctor T a).Linear k := by
  change (CategoryTheory.Functor.id T).Linear k
  infer_instance

/-- In a trivially shifted category, a degree-indexed shifted morphism is an
ordinary morphism. -/
def trivialShiftHomLinearMap (X Y : T) (a : A) :
    ShiftHom X Y a →ₗ[k] (X ⟶ Y) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem trivialShiftHomLinearMap_id (X : T) :
    trivialShiftHomLinearMap (k := k) (A := A) X X 0
        (shiftHomId (A := A) X) = 𝟙 X := by
  simp [trivialShiftHomLinearMap, shiftHomId, trivialShiftMkCore,
    ShiftMkCore.shiftFunctorZero_eq]

set_option backward.isDefEq.respectTransparency false in
theorem trivialShiftHomLinearMap_comp
    {X Y Z : T} {a b : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    trivialShiftHomLinearMap (k := k) (A := A) X Z (b + a)
        (shiftHomComp f g) =
      trivialShiftHomLinearMap (k := k) (A := A) X Y a f ≫
        trivialShiftHomLinearMap (k := k) (A := A) Y Z b g := by
  simp [trivialShiftHomLinearMap, shiftHomComp, shiftHomComp',
    shiftFunctorAdd'_eq_shiftFunctorAdd, trivialShiftMkCore,
    ShiftMkCore.shiftFunctor_eq,
    ShiftMkCore.shiftFunctorAdd_eq]

/-- Sum all finitely many degree components in a trivially shifted target. -/
noncomputable def trivialShiftOrbitFoldMapLinear (X Y : T) :
    ShiftOrbitHom A X Y →ₗ[k] (X ⟶ Y) := by
  classical
  exact DirectSum.toModule k A _ fun a ↦
    trivialShiftHomLinearMap (k := k) (A := A) X Y a

@[simp]
theorem trivialShiftOrbitFoldMapLinear_of
    {X Y : T} (a : A) (f : ShiftHom X Y a) :
    trivialShiftOrbitFoldMapLinear (k := k) (A := A) X Y
        (shiftOrbitOf X Y a f) =
      trivialShiftHomLinearMap (k := k) (A := A) X Y a f := by
  classical
  change trivialShiftOrbitFoldMapLinear (k := k) (A := A) X Y
      (DirectSum.lof k A (fun c ↦ ShiftHom X Y c) a f) = _
  simp [trivialShiftOrbitFoldMapLinear]

theorem trivialShiftOrbitFoldMapLinear_comp
    {X Y Z : T} (f : ShiftOrbitHom A X Y) (g : ShiftOrbitHom A Y Z) :
    trivialShiftOrbitFoldMapLinear (k := k) (A := A) X Z
        (shiftOrbitCompHom f g) =
      trivialShiftOrbitFoldMapLinear (k := k) (A := A) X Y f ≫
        trivialShiftOrbitFoldMapLinear (k := k) (A := A) Y Z g := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro b gb
      change trivialShiftOrbitFoldMapLinear (k := k) (A := A) X Z
          (shiftOrbitCompHom (shiftOrbitOf X Y a fa)
            (shiftOrbitOf Y Z b gb)) =
        trivialShiftOrbitFoldMapLinear (k := k) (A := A) X Y
            (shiftOrbitOf X Y a fa) ≫
          trivialShiftOrbitFoldMapLinear (k := k) (A := A) Y Z
            (shiftOrbitOf Y Z b gb)
      rw [shiftOrbitCompHom_of_of, trivialShiftOrbitFoldMapLinear_of,
        trivialShiftOrbitFoldMapLinear_of,
        trivialShiftOrbitFoldMapLinear_of,
        trivialShiftHomLinearMap_comp]
    · intro g₁ g₂ hg₁ hg₂
      simpa only [map_add, AddMonoidHom.add_apply,
        Preadditive.comp_add] using congrArg₂ (.+.) hg₁ hg₂
  · intro f₁ f₂ hf₁ hf₂
    simpa only [map_add, AddMonoidHom.add_apply,
      Preadditive.add_comp] using congrArg₂ (.+.) hf₁ hf₂

/-- The augmentation of the shift-orbit category of a trivially shifted
linear category, obtained by summing its finite degree support. -/
noncomputable def trivialShiftOrbitFoldFunctor :
    CategoryTheory.Functor (ShiftOrbitCategory T A) T where
  obj X := show T from X
  map f := trivialShiftOrbitFoldMapLinear (k := k) (A := A) _ _ f
  map_id X := by
    change trivialShiftOrbitFoldMapLinear (k := k) (A := A)
        (show T from X) (show T from X) (shiftOrbitId (show T from X)) =
      𝟙 (show T from X)
    rw [shiftOrbitId, trivialShiftOrbitFoldMapLinear_of,
      trivialShiftHomLinearMap_id]
  map_comp f g := trivialShiftOrbitFoldMapLinear_comp
    (k := k) (A := A) f g

instance trivialShiftOrbitFoldFunctor_additive :
    (trivialShiftOrbitFoldFunctor (k := k) (A := A) (T := T)).Additive where
  map_add := by
    intro X Y f g
    exact (trivialShiftOrbitFoldMapLinear
      (k := k) (A := A) (show T from X) (show T from Y)).map_add f g

instance trivialShiftOrbitFoldFunctor_linear :
    (trivialShiftOrbitFoldFunctor (k := k) (A := A) (T := T)).Linear k where
  map_smul f r :=
    (trivialShiftOrbitFoldMapLinear (k := k) (A := A) _ _).map_smul r f

end TrivialShiftFold

section DescendedFunctor

variable {S : Type uC} [Category.{vC} S] [Preadditive S]
variable {T : Type uD} [Category.{vD} T] [Preadditive T]
variable [CategoryTheory.Linear k S] [CategoryTheory.Linear k T]
variable [HasShift S A]
variable [∀ a : A, (shiftFunctor S a).Additive]
variable [∀ a : A, (shiftFunctor S a).Linear k]
variable (G : CategoryTheory.Functor S T) [G.Additive] [G.Linear k]

local instance : HasShift T A := trivialHasShift T A

local instance (a : A) : (shiftFunctor T a).Additive := by
  change (CategoryTheory.Functor.id T).Additive
  infer_instance

local instance (a : A) : (shiftFunctor T a).Linear k := by
  change (CategoryTheory.Functor.id T).Linear k
  infer_instance

variable [G.CommShift A]

/-- A shift-compatible linear functor to a trivially shifted target descends
to the source shift-orbit category. -/
noncomputable def shiftOrbitDescendedFunctor :
    CategoryTheory.Functor (ShiftOrbitCategory S A) T :=
  shiftOrbitMapFunctor (k := k) (A := A) G ⋙
    trivialShiftOrbitFoldFunctor (k := k) (A := A) (T := T)

instance shiftOrbitDescendedFunctor_additive :
    (shiftOrbitDescendedFunctor (k := k) (A := A) G).Additive where
  map_add := by
    intro X Y f g
    change trivialShiftOrbitFoldMapLinear (k := k) (A := A)
        (G.obj (show S from X)) (G.obj (show S from Y))
        (shiftOrbitDescendMapLinear (k := k) G (f + g)) =
      trivialShiftOrbitFoldMapLinear (k := k) (A := A)
          (G.obj (show S from X)) (G.obj (show S from Y))
          (shiftOrbitDescendMapLinear (k := k) G f) +
        trivialShiftOrbitFoldMapLinear (k := k) (A := A)
          (G.obj (show S from X)) (G.obj (show S from Y))
          (shiftOrbitDescendMapLinear (k := k) G g)
    rw [map_add, map_add]

instance shiftOrbitDescendedFunctor_linear :
    (shiftOrbitDescendedFunctor (k := k) (A := A) G).Linear k where
  map_smul f r := by
    change trivialShiftOrbitFoldMapLinear (k := k) (A := A) _ _
        (shiftOrbitDescendMapLinear (k := k) G (r • f)) =
      r • trivialShiftOrbitFoldMapLinear (k := k) (A := A) _ _
        (shiftOrbitDescendMapLinear (k := k) G f)
    rw [map_smul, map_smul]

omit [∀ a : A, (shiftFunctor S a).Linear k] in
@[simp]
theorem shiftOrbitDescendedFunctor_map_of
    {X Y : S} (a : A) (f : ShiftHom X Y a) :
    (shiftOrbitDescendedFunctor (k := k) (A := A) G).map
        (shiftOrbitOf X Y a f) =
      shiftOrbitDescendHomogeneousMap G a f := by
  change trivialShiftOrbitFoldMapLinear (k := k) (A := A)
      (G.obj X) (G.obj Y)
      (shiftOrbitDescendMapLinear (k := k) G (shiftOrbitOf X Y a f)) = _
  rw [shiftOrbitDescendMapLinear_of,
    trivialShiftOrbitFoldMapLinear_of]
  rfl

omit [∀ a : A, (shiftFunctor S a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- The descended functor restricts along the degree-zero inclusion to the
original shift-compatible functor. -/
theorem shiftOrbitDescendedFunctor_map_identityComponent
    {X Y : S} (f : X ⟶ Y) :
    (shiftOrbitDescendedFunctor (k := k) (A := A) G).map
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := S) (A := A)).map f) =
      G.map f := by
  change (shiftOrbitDescendedFunctor (k := k) (A := A) G).map
      (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)) = G.map f
  rw [shiftOrbitDescendedFunctor_map_of]
  have h := CategoryTheory.ShiftedHom.map_mk₀
    (X := X) (Y := Y) (0 : A) rfl f G
  have hzero : CategoryTheory.ShiftedHom.mk₀
      (C := T) (M := A) 0 rfl (G.map f) = G.map f := by
    unfold CategoryTheory.ShiftedHom.mk₀ shiftFunctorZero'
    rw [(trivialShiftMkCore T A).shiftFunctorZero_eq]
    simp [trivialShiftMkCore]
  rw [hzero] at h
  exact h

end DescendedFunctor

section DescendedFunctorFromShift

variable {S : Type uC} [Category.{vC} S] [Preadditive S]
variable {T : Type uD} [Category.{vD} T] [Preadditive T]
variable [CategoryTheory.Linear k S] [CategoryTheory.Linear k T]
variable {B : Type w} [AddGroup B] [HasShift S B]
variable [∀ b : B, (shiftFunctor S b).Additive]
variable (G : CategoryTheory.Functor S T) [G.Additive] [G.Linear k]

local instance : HasShift T B := trivialHasShift T B

local instance (b : B) : (shiftFunctor T b).Additive := by
  change (CategoryTheory.Functor.id T).Additive
  infer_instance

local instance (b : B) : (shiftFunctor T b).Linear k := by
  change (CategoryTheory.Functor.id T).Linear k
  infer_instance

variable [G.CommShift B]

set_option backward.isDefEq.respectTransparency false in
/-- The descended functor sends the canonical path from a shifted object to
the corresponding commutation isomorphism. -/
theorem shiftOrbitDescendedFunctor_map_fromShift (X : S) (b : B) :
    (shiftOrbitDescendedFunctor (k := k) (A := B) G).map
        (shiftOrbitFromShift X b) =
      (G.commShiftIso b).hom.app X := by
  rw [shiftOrbitFromShift, shiftOrbitDescendedFunctor_map_of]
  simp [shiftOrbitDescendHomogeneousMap]

end DescendedFunctorFromShift

section OrbitPushdownDescended

universe uM

variable {R : Type uK} [CommRing R]
variable {B : Type uC} [Category.{vC} B] [Preadditive B]
variable [CategoryTheory.Linear R B]
variable {H : Type w} [AddGroup H]
variable (D : ShiftMkCore B H)
variable [∀ a : H, (D.F a).Additive]
variable [∀ a : H, (D.F a).Linear R]

/-- The induced shifts on linear modules are additive. -/
theorem linearModuleCategoryAdditiveShift :
    letI := hasShiftMk B H D
    letI := linearModuleCategoryHasShift (k := R) D
    ∀ a : H,
      (shiftFunctor
        (LinearModuleCategory.{uC, vC, uK, uM} (C := B) R) a).Additive := by
  letI := hasShiftMk B H D
  letI := functorCategoryHasShift (E := ModuleCat.{uM} R) D
  letI (a : H) :
      (shiftFunctor
        (CategoryTheory.Functor B (ModuleCat.{uM} R)) a).Additive := by
    change (functorPrecomposition (E := ModuleCat.{uM} R)
      (D.F (-a))).Additive
    infer_instance
  letI := isLinearModule_stableUnderShift (k := R) D
  letI := linearModuleCategoryHasShift (k := R) D
  intro a
  infer_instance

/-- The induced shifts on linear modules are linear. -/
theorem linearModuleCategoryLinearShift :
    letI := hasShiftMk B H D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := R) D
    letI := linearModuleCategoryHasShift (k := R) D
    ∀ a : H,
      (shiftFunctor
        (LinearModuleCategory.{uC, vC, uK, uM} (C := B) R) a).Linear R := by
  letI := hasShiftMk B H D
  letI := functorCategoryHasShift (E := ModuleCat.{uM} R) D
  letI := isLinearModule_stableUnderShift (k := R) D
  letI := linearModuleCategoryHasShift (k := R) D
  let J := (IsLinearModule (C := B) R).ι
  letI (a : H) :
      (shiftFunctor (CategoryTheory.Functor B (ModuleCat.{uM} R)) a).Linear R := by
    change (functorPrecomposition (E := ModuleCat.{uM} R)
      (D.F (-a))).Linear R
    constructor
    intro X Y f r
    rfl
  intro a
  letI : (shiftFunctor
      (LinearModuleCategory.{uC, vC, uK, uM} (C := B) R) a ⋙ J).Linear R :=
    Functor.linear_of_iso R (J.commShiftIso a).symm
  constructor
  intro X Y f r
  apply J.map_injective
  rw [J.map_smul]
  change (shiftFunctor
      (LinearModuleCategory.{uC, vC, uK, uM} (C := B) R) a ⋙ J).map
        (r • f) =
    r • (shiftFunctor
      (LinearModuleCategory.{uC, vC, uK, uM} (C := B) R) a ⋙ J).map f
  exact (shiftFunctor
    (LinearModuleCategory.{uC, vC, uK, uM} (C := B) R) a ⋙ J).map_smul r f

/-- Gabriel push-down descended from the shift-orbit category of upstairs
linear modules to linear modules on the base orbit category. -/
noncomputable def linearModuleOrbitPushdownDescended :
    letI := hasShiftMk B H D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := R) D
    letI := linearModuleCategoryHasShift (k := R) D
    letI := linearModuleCategoryAdditiveShift (R := R) D
    letI := linearModuleCategoryLinearShift (R := R) D
    letI := trivialHasShift
      (LinearModuleCategory.{uC, max vC w, uK, max w uM}
        (C := ShiftOrbitCategory B H) R) H
    CategoryTheory.Functor
        (ShiftOrbitCategory
          (LinearModuleCategory.{uC, vC, uK, uM} (C := B) R) H)
        (LinearModuleCategory.{uC, max vC w, uK, max w uM}
          (C := ShiftOrbitCategory B H) R) := by
  letI := hasShiftMk B H D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := R) D
  letI := isLinearModule_stableUnderShift (k := R) D
  letI := linearModuleCategoryHasShift (k := R) D
  letI := linearModuleCategoryAdditiveShift (R := R) D
  letI := linearModuleCategoryLinearShift (R := R) D
  letI := trivialHasShift
    (LinearModuleCategory.{uC, max vC w, uK, max w uM}
      (C := ShiftOrbitCategory B H) R) H
  letI := linearModuleOrbitPushdownCommShift (k := R) D
  exact shiftOrbitDescendedFunctor
    (k := R) (A := H)
    (linearModuleOrbitPushdown (k := R) (C := B) (A := H))

@[simp]
theorem linearModuleOrbitPushdownDescended_map_of :
    letI := hasShiftMk B H D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := R) D
    letI := linearModuleCategoryHasShift (k := R) D
    letI := linearModuleCategoryAdditiveShift (R := R) D
    letI := linearModuleCategoryLinearShift (R := R) D
    letI := trivialHasShift
      (LinearModuleCategory.{uC, max vC w, uK, max w uM}
        (C := ShiftOrbitCategory B H) R) H
    ∀ (M N : LinearModuleCategory.{uC, vC, uK, uM} (C := B) R)
      (a : H) (f : ShiftHom M N a),
    (linearModuleOrbitPushdownDescended (R := R) D).map
        (shiftOrbitOf M N a f) =
      (linearModuleOrbitPushdown (k := R) (C := B) (A := H)).map f ≫
        (linearModuleOrbitPushdownCommShiftIso (k := R) D a).hom.app N := by
  letI := hasShiftMk B H D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := R) D
  letI := isLinearModule_stableUnderShift (k := R) D
  letI := linearModuleCategoryHasShift (k := R) D
  letI := linearModuleCategoryAdditiveShift (R := R) D
  letI := linearModuleCategoryLinearShift (R := R) D
  letI := trivialHasShift
    (LinearModuleCategory.{uC, max vC w, uK, max w uM}
      (C := ShiftOrbitCategory B H) R) H
  letI := linearModuleOrbitPushdownCommShift (k := R) D
  intro M N a f
  change (shiftOrbitDescendedFunctor (k := R) (A := H)
      (linearModuleOrbitPushdown (k := R) (C := B) (A := H))).map
        (shiftOrbitOf M N a f) = _
  rw [shiftOrbitDescendedFunctor_map_of]
  rfl

instance linearModuleOrbitPushdownDescended_additive :
    letI := hasShiftMk B H D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := R) D
    letI := linearModuleCategoryHasShift (k := R) D
    letI := linearModuleCategoryAdditiveShift (R := R) D
    letI := linearModuleCategoryLinearShift (R := R) D
    letI := trivialHasShift
      (LinearModuleCategory.{uC, max vC w, uK, max w uM}
        (C := ShiftOrbitCategory B H) R) H
    (linearModuleOrbitPushdownDescended (R := R) D).Additive := by
  letI := hasShiftMk B H D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := R) D
  letI := linearModuleCategoryHasShift (k := R) D
  letI := linearModuleCategoryAdditiveShift (R := R) D
  letI := linearModuleCategoryLinearShift (R := R) D
  letI := trivialHasShift
    (LinearModuleCategory.{uC, max vC w, uK, max w uM}
      (C := ShiftOrbitCategory B H) R) H
  dsimp only [linearModuleOrbitPushdownDescended]
  infer_instance

instance linearModuleOrbitPushdownDescended_linear :
    letI := hasShiftMk B H D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := R) D
    letI := linearModuleCategoryHasShift (k := R) D
    letI := linearModuleCategoryAdditiveShift (R := R) D
    letI := linearModuleCategoryLinearShift (R := R) D
    letI := trivialHasShift
      (LinearModuleCategory.{uC, max vC w, uK, max w uM}
        (C := ShiftOrbitCategory B H) R) H
    (linearModuleOrbitPushdownDescended (R := R) D).Linear R := by
  letI := hasShiftMk B H D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := R) D
  letI := linearModuleCategoryHasShift (k := R) D
  letI := linearModuleCategoryAdditiveShift (R := R) D
  letI := linearModuleCategoryLinearShift (R := R) D
  letI := trivialHasShift
    (LinearModuleCategory.{uC, max vC w, uK, max w uM}
      (C := ShiftOrbitCategory B H) R) H
  dsimp only [linearModuleOrbitPushdownDescended]
  infer_instance

end OrbitPushdownDescended

end MagnitudeConjecture.CoveringHom
