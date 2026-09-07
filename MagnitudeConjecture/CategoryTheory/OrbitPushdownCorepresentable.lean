import MagnitudeConjecture.CategoryTheory.OrbitPushdownRepresentable
import MagnitudeConjecture.CategoryTheory.OrbitPushdownAdjunction
import MagnitudeConjecture.CategoryTheory.ShiftOrbitDecomposition
import MagnitudeConjecture.CategoryTheory.ShiftOrbitFactorization
import MagnitudeConjecture.LinearAlgebra.FiniteDirectSumDual
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Orbit push-down of dual corepresentable modules

This file develops the injective-representable half of Gabriel's Nakayama
comparison.  The coefficient dual of `Hom(-, X)` is a covariant module, and
shifting its source reindexes the orbit Hom decomposition by negation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- The coefficient dual of the contravariant representable `Hom(-, X)`,
regarded as a covariant linear module. -/
noncomputable def dualLinearYoneda (X : C) : C ⥤ ModuleCat k where
  obj Y := ModuleCat.of k (Module.Dual k (Y ⟶ X))
  map {Y Z} f := ModuleCat.ofHom (Linear.leftComp k X f).dualMap
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro g
    simp
  map_comp {Y Z W} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro h
    simp [Category.assoc]

instance dualLinearYoneda_additive (X : C) :
    (dualLinearYoneda (k := k) X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change (Linear.leftComp k X (f + g)).dualMap phi =
      (Linear.leftComp k X f).dualMap phi +
        (Linear.leftComp k X g).dualMap phi
    apply LinearMap.ext
    intro h
    simp [Preadditive.add_comp]

instance dualLinearYoneda_linear (X : C) :
    (dualLinearYoneda (k := k) X).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change (Linear.leftComp k X (r • f)).dualMap phi =
      r • (Linear.leftComp k X f).dualMap phi
    apply LinearMap.ext
    intro h
    simp [CategoryTheory.Linear.smul_comp]

/-- The dual corepresentable bundled as an additive linear module. -/
noncomputable def dualLinearYonedaLinearModule (X : C) :
    LinearModuleCategory (C := C) k :=
  ⟨dualLinearYoneda (k := k) X, inferInstance, inferInstance⟩

/-- A morphism of representing objects acts covariantly on coefficient-dual
corepresentables. -/
noncomputable def dualLinearYonedaMap {X X' : C} (f : X ⟶ X') :
    dualLinearYoneda (k := k) X' ⟶ dualLinearYoneda (k := k) X := by
  refine
    { app := fun Y ↦ ModuleCat.ofHom
        (CategoryTheory.Linear.rightComp k Y f).dualMap
      naturality := ?_ }
  intro Y Z g
  apply ModuleCat.hom_ext
  change (CategoryTheory.Linear.rightComp k Z f).dualMap.comp
      (CategoryTheory.Linear.leftComp k X' g).dualMap =
    (CategoryTheory.Linear.leftComp k X g).dualMap.comp
      (CategoryTheory.Linear.rightComp k Y f).dualMap
  rw [LinearMap.dualMap_comp_dualMap,
    LinearMap.dualMap_comp_dualMap]
  congr 1
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply,
    CategoryTheory.Linear.leftComp_apply,
    CategoryTheory.Linear.rightComp_apply]
  rw [Category.assoc]

/-- Bundled linear-module form of the map induced by a morphism of
representing objects. -/
noncomputable def dualLinearYonedaLinearModuleMap
    {X X' : C} (f : X ⟶ X') :
    dualLinearYonedaLinearModule (k := k) X' ⟶
      dualLinearYonedaLinearModule (k := k) X :=
  ObjectProperty.homMk (dualLinearYonedaMap (k := k) f)

@[simp]
theorem dualLinearYonedaMap_id (X : C) :
    dualLinearYonedaMap (k := k) (𝟙 X) =
      𝟙 (dualLinearYoneda (k := k) X) := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change Module.Dual k (Y ⟶ X) at phi
  apply LinearMap.ext
  intro q
  change phi (q ≫ 𝟙 X) = phi q
  rw [Category.comp_id]

@[simp]
theorem dualLinearYonedaMap_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualLinearYonedaMap (k := k) (f ≫ g) =
      dualLinearYonedaMap (k := k) g ≫
        dualLinearYonedaMap (k := k) f := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change Module.Dual k (W ⟶ Z) at phi
  apply LinearMap.ext
  intro q
  change phi (q ≫ (f ≫ g)) = phi ((q ≫ f) ≫ g)
  rw [Category.assoc]

/-- Right composition with the inverse of an isomorphism, bundled as the
linear equivalence in the direction used by coefficient duality. -/
def rightCompInvLinearEquiv (Y : C) {X X' : C} (e : X ≅ X') :
    (Y ⟶ X') ≃ₗ[k] (Y ⟶ X) where
  toLinearMap := CategoryTheory.Linear.rightComp k Y e.inv
  invFun := CategoryTheory.Linear.rightComp k Y e.hom
  left_inv q := by simp [Category.assoc]
  right_inv q := by simp [Category.assoc]

/-- Coefficient-dual corepresentables are naturally invariant under changing
their representing object by an isomorphism. -/
noncomputable def dualLinearYonedaMapIso {X X' : C} (e : X ≅ X') :
    dualLinearYoneda (k := k) X ≅ dualLinearYoneda (k := k) X' := by
  refine NatIso.ofComponents (fun Y ↦
    (rightCompInvLinearEquiv (k := k) Y e).dualMap.toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  change (CategoryTheory.Linear.rightComp k Z e.inv).dualMap.comp
      (CategoryTheory.Linear.leftComp k X f).dualMap =
    (CategoryTheory.Linear.leftComp k X' f).dualMap.comp
      (CategoryTheory.Linear.rightComp k Y e.inv).dualMap
  rw [LinearMap.dualMap_comp_dualMap,
    LinearMap.dualMap_comp_dualMap]
  congr 1
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply,
    CategoryTheory.Linear.leftComp_apply,
    CategoryTheory.Linear.rightComp_apply]
  rw [Category.assoc]

@[simp]
theorem dualLinearYonedaMapIso_hom {X X' : C} (e : X ≅ X') :
    (dualLinearYonedaMapIso (k := k) e).hom =
      dualLinearYonedaMap (k := k) e.inv := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  rfl

/-- A dual corepresentable known to be pointwise finite-dimensional with
finite object support. -/
noncomputable def finiteDimensionalDualLinearYoneda (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    FiniteDimensionalModuleCategory (C := C) k :=
  ⟨dualLinearYonedaLinearModule (k := k) X, hX⟩

/-- Bundled finite-dimensional form of the map induced by a morphism of
representing objects. -/
noncomputable def finiteDimensionalDualLinearYonedaMap
    {X X' : C} (f : X ⟶ X')
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hX' : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X')) :
    finiteDimensionalDualLinearYoneda (k := k) X' hX' ⟶
      finiteDimensionalDualLinearYoneda (k := k) X hX :=
  ObjectProperty.homMk (dualLinearYonedaLinearModuleMap (k := k) f)

variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- Moving a shift from the source of a Hom space to the target gives a
linear equivalence, with the degree written explicitly for later dependent
reindexing. -/
noncomputable def shiftSourceHomLinearEquiv
    (Y X : C) (b a : A) (hba : -b = a) :
    (((shiftFunctor C b).obj Y) ⟶ X) ≃ₗ[k] ShiftHom Y X a := by
  subst a
  letI : (shiftEquiv C b).functor.Additive :=
    (inferInstance : (shiftFunctor C b).Additive)
  letI : (shiftEquiv C b).inverse.Additive :=
    (inferInstance : (shiftFunctor C (-b)).Additive)
  letI : (shiftEquiv C b).functor.Linear k :=
    (inferInstance : (shiftFunctor C b).Linear k)
  letI : (shiftEquiv C b).inverse.Linear k :=
    (inferInstance : (shiftFunctor C (-b)).Linear k)
  let adj := (shiftEquiv C b).toAdjunction
  let e := adj.homEquiv Y X
  exact
    { toEquiv := e
      map_add' := by
        intro f g
        exact (adj.homAddEquiv Y X).map_add f g
      map_smul' := by
        intro r f
        change adj.homEquiv Y X (r • f) = r • adj.homEquiv Y X f
        simp only [Adjunction.homEquiv_unit, Functor.map_smul,
          CategoryTheory.Linear.comp_smul] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftSourceHomLinearEquiv_apply
    (Y X : C) (b : A)
    (g : (shiftFunctor C b).obj Y ⟶ X) :
    shiftSourceHomLinearEquiv (k := k) Y X b (-b) rfl g =
      (shiftEquiv C b).unit.app Y ≫ (shiftFunctor C (-b)).map g := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftSourceHomLinearEquiv_symm_apply
    (Y X : C) (b : A) (q : ShiftHom Y X (-b)) :
    (shiftSourceHomLinearEquiv (k := k) Y X b (-b) rfl).symm q =
      (shiftFunctor C b).map q ≫
        (shiftEquiv C b).counit.app X := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The source-shift equivalence is composition in the orbit category with
the canonical morphism from an object to its shift. -/
theorem shiftSourceHomLinearEquiv_apply_eq_shiftHomComp
    (Y X : C) (b : A) (g : (shiftFunctor C b).obj Y ⟶ X) :
    shiftSourceHomLinearEquiv (k := k) Y X b (-b) rfl g =
      shiftHomComp' (zero_add (-b)) (shiftShiftNeg Y b).inv
        (shiftHomZero (A := A) g) := by
  rw [shiftSourceHomLinearEquiv_apply]
  change (shiftShiftNeg Y b).inv ≫ (shiftFunctor C (-b)).map g =
    CategoryTheory.ShiftedHom.comp (shiftShiftNeg Y b).inv
      (CategoryTheory.ShiftedHom.mk₀ 0 rfl g) (zero_add (-b))
  exact (CategoryTheory.ShiftedHom.comp_mk₀
    (f := (shiftShiftNeg Y b).inv) (0 : A) rfl g).symm

theorem neg_negEquiv_symm (a : A) : -((Equiv.neg A).symm a) = a := by
  simpa only [Equiv.neg_apply] using (Equiv.neg A).apply_symm_apply a

/-- The source-shifted Hom direct sum is the usual target-shifted orbit Hom
direct sum.  The reindexing is `b ↦ -b`. -/
noncomputable def shiftSourceHomDirectSumEquiv (Y X : C) :
    DirectSum A (fun b ↦ ((shiftFunctor C b).obj Y ⟶ X)) ≃ₗ[k]
      ShiftOrbitHom A Y X :=
  DirectSum.lequivCongrLeft k (Equiv.neg A) ≪≫ₗ
    directSumLinearEquivCongrRight (k := k)
      (fun a ↦
        ((shiftFunctor C ((Equiv.neg A).symm a)).obj Y ⟶ X))
      (fun a ↦ shiftSourceHomLinearEquiv (k := k) Y X
        ((Equiv.neg A).symm a) a (neg_negEquiv_symm a))

set_option backward.isDefEq.respectTransparency false in
/-- On the summand indexed by `-a`, the source-shifted Hom equivalence is
the homogeneous degree-`a` inclusion. -/
theorem shiftSourceHomDirectSumEquiv_inclusion_neg
    (Y X : C) (a : A)
    (g : (shiftFunctor C ((Equiv.neg A).symm a)).obj Y ⟶ X) :
    shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X
        (directSumInclusion (k := k)
          (fun b ↦ ((shiftFunctor C b).obj Y ⟶ X))
          ((Equiv.neg A).symm a) g) =
      shiftOrbitLof (k := k) Y X a
        (shiftSourceHomLinearEquiv (k := k)
          Y X ((Equiv.neg A).symm a) a
            (neg_negEquiv_symm a) g) := by
  classical
  change directSumLinearEquivCongrRight (k := k)
      (fun a ↦
        ((shiftFunctor C ((Equiv.neg A).symm a)).obj Y ⟶ X))
      (fun a ↦ shiftSourceHomLinearEquiv (k := k) Y X
        ((Equiv.neg A).symm a) a (neg_negEquiv_symm a))
      (DirectSum.lequivCongrLeft k (Equiv.neg A)
        (DirectSum.lof k A
          (fun b ↦ ((shiftFunctor C b).obj Y ⟶ X))
          ((Equiv.neg A).symm a) g)) = _
  have hreindex :
      DirectSum.lequivCongrLeft k (Equiv.neg A)
          (DirectSum.lof k A
            (fun b ↦ ((shiftFunctor C b).obj Y ⟶ X))
            ((Equiv.neg A).symm a) g) =
        DirectSum.lof k A
          (fun a ↦
            ((shiftFunctor C ((Equiv.neg A).symm a)).obj Y ⟶ X))
          a g := by
    exact DirectSum.lequivCongrLeft_lof k
      (M := fun b ↦ ((shiftFunctor C b).obj Y ⟶ X))
      (e := Equiv.neg A) (i := (Equiv.neg A).symm a)
        (k := a) (hik := rfl) (x := g) (y := g) (hxy := by rfl)
  rw [hreindex]
  change DirectSum.lmap
      (fun a ↦ (shiftSourceHomLinearEquiv (k := k)
        Y X ((Equiv.neg A).symm a) a
          (neg_negEquiv_symm a)).toLinearMap)
      (DirectSum.lof k A
        (fun a ↦ ((shiftFunctor C ((Equiv.neg A).symm a)).obj Y ⟶ X)) a g) = _
  rw [DirectSum.lmap_lof]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inverse formula on a homogeneous orbit morphism. -/
theorem shiftSourceHomDirectSumEquiv_symm_shiftOrbitLof
    (Y X : C) (a : A) (q : ShiftHom Y X a) :
    (shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X).symm
        (shiftOrbitLof (k := k) Y X a q) =
      directSumInclusion (k := k)
        (fun b ↦ ((shiftFunctor C b).obj Y ⟶ X))
        ((Equiv.neg A).symm a)
        ((shiftSourceHomLinearEquiv (k := k) Y X
          ((Equiv.neg A).symm a) a (neg_negEquiv_symm a)).symm q) := by
  apply (shiftSourceHomDirectSumEquiv
    (k := k) (A := A) Y X).injective
  rw [LinearEquiv.apply_symm_apply,
    shiftSourceHomDirectSumEquiv_inclusion_neg,
    LinearEquiv.apply_symm_apply]

/-- Projection of an orbit Hom to its ordinary degree-zero component. -/
noncomputable def shiftOrbitZeroComponentLinearMap (Y X : C) :
    ShiftOrbitHom A Y X →ₗ[k] (Y ⟶ X) :=
  (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm.toLinearMap.comp
    (DirectSum.component k A (fun a ↦ ShiftHom Y X a) 0)

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftOrbitZeroComponentLinearMap_shiftOrbitLof_zero
    (Y X : C) (g : ShiftHom Y X (0 : A)) :
    shiftOrbitZeroComponentLinearMap (k := k) (A := A) Y X
        (shiftOrbitLof (k := k) Y X 0 g) =
      (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm g := by
  classical
  change (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm
      (DirectSum.component k A (fun a ↦ ShiftHom Y X a) 0
        (DirectSum.lof k A (fun a ↦ ShiftHom Y X a) 0 g)) = _
  rw [DirectSum.component.lof_self]

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitZeroComponentLinearMap_shiftOrbitLof_ne
    (Y X : C) {a : A} (ha : a ≠ 0) (g : ShiftHom Y X a) :
    shiftOrbitZeroComponentLinearMap (k := k) (A := A) Y X
      (shiftOrbitLof (k := k) Y X a g) = 0 := by
  classical
  change (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm
      (DirectSum.component k A (fun a ↦ ShiftHom Y X a) 0
        (DirectSum.lof k A (fun a ↦ ShiftHom Y X a) a g)) = 0
  rw [DirectSum.component.of]
  simp [ha]

omit [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero projection intertwines left composition by an ordinary
upstairs morphism with left composition in the orbit category. -/
theorem shiftOrbitZeroComponentLinearMap_comp_identityComponent
    {Y Z : C} (X : C) (f : Y ⟶ Z) (q : ShiftOrbitHom A Z X) :
    shiftOrbitZeroComponentLinearMap (k := k) (A := A) Y X
        (shiftOrbitCompHom
          (shiftOrbitLof (k := k) Y Z 0
            (shiftHomZero (A := A) f)) q) =
      f ≫ shiftOrbitZeroComponentLinearMap
        (k := k) (A := A) Z X q := by
  change (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm
      ((shiftOrbitCompHom
        (shiftOrbitOf Y Z 0 (shiftHomZero (A := A) f)) q) 0) =
    f ≫ (shiftHomZeroLinearEquiv (k := k) (A := A) Z X).symm (q 0)
  have hcomp := shiftOrbitComp_zero_left_component_zero
    (A := A) (k := k) f q
  calc
    _ = (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm
        (shiftHomZero (A := A)
          (f ≫ (shiftHomZeroLinearEquiv
            (k := k) (A := A) Z X).symm (q 0))) := congrArg _ hcomp
    _ = _ := (shiftHomZeroLinearEquiv
      (k := k) (A := A) Y X).symm_apply_apply _

omit [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero projection intertwines right composition by an ordinary
upstairs morphism with right composition in the orbit category. -/
theorem shiftOrbitZeroComponentLinearMap_identityComponent_comp
    (Y : C) {X Z : C} (q : ShiftOrbitHom A Y X) (f : X ⟶ Z) :
    shiftOrbitZeroComponentLinearMap (k := k) (A := A) Y Z
        (shiftOrbitCompHom q
          (shiftOrbitLof (k := k) X Z 0
            (shiftHomZero (A := A) f))) =
      shiftOrbitZeroComponentLinearMap
        (k := k) (A := A) Y X q ≫ f := by
  change (shiftHomZeroLinearEquiv (k := k) (A := A) Y Z).symm
      ((shiftOrbitCompHom q
        (shiftOrbitOf X Z 0 (shiftHomZero (A := A) f))) 0) =
    (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm (q 0) ≫ f
  have hcomp := shiftOrbitComp_zero_right_component_zero
    (A := A) (k := k) q f
  calc
    _ = (shiftHomZeroLinearEquiv (k := k) (A := A) Y Z).symm
        (shiftHomZero (A := A)
          ((shiftHomZeroLinearEquiv
            (k := k) (A := A) Y X).symm (q 0) ≫ f)) := congrArg _ hcomp
    _ = _ := (shiftHomZeroLinearEquiv
      (k := k) (A := A) Y Z).symm_apply_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing a homogeneous orbit morphism of degree `a = -b` by the
canonical morphism from the `b`-shift recovers the inverse source-shift
adjunction in degree zero. -/
theorem shiftOrbitZeroComponentLinearMap_fromShift_comp
    (Y X : C) (b a : A) (hba : -b = a) (q : ShiftHom Y X a) :
    shiftOrbitZeroComponentLinearMap
        (k := k) (A := A) ((shiftFunctor C b).obj Y) X
        (shiftOrbitCompHom (shiftOrbitFromShift Y b)
          (shiftOrbitLof (k := k) Y X a q)) =
      (shiftSourceHomLinearEquiv
        (k := k) Y X b a hba).symm q := by
  classical
  subst a
  rw [shiftOrbitFromShift, shiftOrbitLof_apply,
    shiftOrbitCompHom_of_of]
  have horbit :
      shiftOrbitOf ((shiftFunctor C b).obj Y) X ((-b) + b)
          (shiftHomComp (𝟙 ((shiftFunctor C b).obj Y)) q) =
        shiftOrbitLof (k := k) ((shiftFunctor C b).obj Y) X 0
          (shiftHomComp' (neg_add_cancel b)
            (𝟙 ((shiftFunctor C b).obj Y)) q) := by
    rw [shiftOrbitLof_apply]
    apply DFinsupp.single_eq_of_sigma_eq
    apply Sigma.ext (neg_add_cancel b)
    exact shiftHomComp_heq_shiftHomComp' (neg_add_cancel b)
      (𝟙 ((shiftFunctor C b).obj Y)) q
  rw [horbit,
    shiftOrbitZeroComponentLinearMap_shiftOrbitLof_zero,
    shiftSourceHomLinearEquiv_symm_apply]
  have hz : shiftFunctorZero' C 0 rfl = shiftFunctorZero C A := by
    ext
    simp [shiftFunctorZero']
  dsimp [shiftHomComp', shiftHomZeroLinearEquiv,
    CategoryTheory.ShiftedHom.homEquiv]
  rw [hz, Category.id_comp]
  change
    ((shiftFunctor C b).map q ≫
        (shiftFunctorAdd' C (-b) b 0 (neg_add_cancel b)).inv.app X) ≫
      (shiftFunctorZero C A).hom.app X =
    (shiftFunctor C b).map q ≫
      (shiftFunctorCompIsoId C (-b) b (neg_add_cancel b)).hom.app X
  rw [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `b`-component of the inverse source-shift decomposition is obtained
by precomposing downstairs with the canonical morphism from the `b`-shift
and then taking degree zero. -/
theorem shiftSourceHomDirectSumEquiv_symm_apply_component
    (Y X : C) (b : A) (q : ShiftOrbitHom A Y X) :
    DirectSum.component k A
        (fun c ↦ ((shiftFunctor C c).obj Y ⟶ X)) b
        ((shiftSourceHomDirectSumEquiv
          (k := k) (A := A) Y X).symm q) =
      shiftOrbitZeroComponentLinearMap
        (k := k) (A := A) ((shiftFunctor C b).obj Y) X
        (shiftOrbitCompHom (shiftOrbitFromShift Y b) q) := by
  classical
  induction q using DirectSum.induction_on with
  | zero => simp
  | of a g =>
      have hgen : DirectSum.of (fun a ↦ ShiftHom Y X a) a g =
          shiftOrbitOf Y X a g := by
        ext d
        by_cases had : a = d
        · subst d
          simp [shiftOrbitOf]
        · simp [shiftOrbitOf, DirectSum.of_apply, had]
      rw [hgen, ← shiftOrbitLof_apply (k := k) (A := A),
        shiftSourceHomDirectSumEquiv_symm_shiftOrbitLof]
      by_cases hb : (Equiv.neg A).symm a = b
      · subst b
        rw [directSumInclusion, DirectSum.component.lof_self]
        exact (shiftOrbitZeroComponentLinearMap_fromShift_comp
          (k := k) (A := A) Y X ((Equiv.neg A).symm a) a
            (neg_negEquiv_symm a) g).symm
      · have ha : a ≠ -b := by
          intro h
          apply hb
          apply (Equiv.neg A).injective
          change -((Equiv.neg A).symm a) = -b
          rw [neg_negEquiv_symm]
          exact h
        simp only [directSumInclusion, DirectSum.component.of, hb,
          ↓reduceDIte]
        rw [shiftOrbitLof_apply, shiftOrbitFromShift,
          shiftOrbitCompHom_of_of,
          ← shiftOrbitLof_apply (k := k) (A := A)]
        apply (shiftOrbitZeroComponentLinearMap_shiftOrbitLof_ne
          (k := k) (A := A) _ _ ?_ _).symm
        intro hab
        exact ha (eq_neg_of_add_eq_zero_left hab)
  | add q r hq hr =>
      rw [map_add, map_add, map_add, hq, hr]
      exact (shiftOrbitZeroComponentLinearMap
        (k := k) (A := A) ((shiftFunctor C b).obj Y) X).map_add _ _ |>.symm

/-- A functional on ordinary `Hom(Y, X)` extends to orbit Hom by reading its
degree-zero component. -/
noncomputable def dualLinearYonedaOrbitPullupApp (X Y : C) :
    Module.Dual k (Y ⟶ X) →ₗ[k] Module.Dual k (ShiftOrbitHom A Y X) :=
  (shiftOrbitZeroComponentLinearMap (k := k) (A := A) Y X).dualMap

/-- The degree-zero extension is natural for ordinary upstairs morphisms.
The statement is pointwise because its source and target module categories
live in the Hom universes of `C` and of the orbit category, respectively. -/
theorem dualLinearYonedaOrbitPullupApp_naturality
    (X : C) {Y Z : C} (f : Y ⟶ Z) (phi : Module.Dual k (Y ⟶ X)) :
    dualLinearYonedaOrbitPullupApp (k := k) (A := A) X Z
        ((dualLinearYoneda (k := k) X).map f phi) =
      (dualLinearYoneda (k := k)
          (C := ShiftOrbitCategory C A)
          (show ShiftOrbitCategory C A from X)).map
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := A)).map f)
        (dualLinearYonedaOrbitPullupApp (k := k) (A := A) X Y phi) := by
  apply LinearMap.ext
  intro q
  exact congrArg phi
    (shiftOrbitZeroComponentLinearMap_comp_identityComponent
      (k := k) (A := A) X f q).symm

/-- The degree-zero extension is natural in the representing object. -/
theorem dualLinearYonedaOrbitPullupApp_representing_naturality
    {X Z : C} (f : X ⟶ Z) (Y : C) (phi : Module.Dual k (Y ⟶ Z)) :
    dualLinearYonedaOrbitPullupApp (k := k) (A := A) X Y
        ((dualLinearYonedaMap (k := k) f).app Y phi) =
      (dualLinearYonedaMap (k := k)
          ((ShiftOrbitCategory.identityComponentFunctor
            (C := C) (A := A)).map f)).app
        (show ShiftOrbitCategory C A from Y)
        (dualLinearYonedaOrbitPullupApp (k := k) (A := A) Z Y phi) := by
  apply LinearMap.ext
  intro q
  exact congrArg phi
    (shiftOrbitZeroComponentLinearMap_identityComponent_comp
      (k := k) (A := A) Y q f).symm

/-- The adjointly assembled comparison from push-down of a dual
corepresentable to the downstairs dual corepresentable. -/
noncomputable def orbitPushdownDualLinearYonedaComparisonApp (X Y : C) :
    orbitPushdownValue (A := A) (dualLinearYoneda (k := k) X) Y →ₗ[k]
      Module.Dual k (ShiftOrbitHom A Y X) := by
  classical
  exact DirectSum.toModule k A _ fun b ↦
    ((dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
      (shiftOrbitFromShift Y b)).hom.comp
        (dualLinearYonedaOrbitPullupApp
          (k := k) (A := A) X ((shiftFunctor C b).obj Y))

@[simp]
theorem orbitPushdownDualLinearYonedaComparisonApp_lof
    (X Y : C) (b : A)
    (phi : Module.Dual k (((shiftFunctor C b).obj Y) ⟶ X)) :
    orbitPushdownDualLinearYonedaComparisonApp
        (k := k) (A := A) X Y
        (orbitPushdownLof (dualLinearYoneda (k := k) X) Y b phi) =
      (dualLinearYoneda (k := k)
          (C := ShiftOrbitCategory C A)
          (show ShiftOrbitCategory C A from X)).map
        (shiftOrbitFromShift Y b)
        (dualLinearYonedaOrbitPullupApp
          (k := k) (A := A) X ((shiftFunctor C b).obj Y) phi) := by
  classical
  rw [orbitPushdownDualLinearYonedaComparisonApp, orbitPushdownLof,
    DirectSum.toModule_lof]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The assembled comparison is natural for a homogeneous orbit morphism. -/
theorem orbitPushdownDualLinearYonedaComparisonApp_naturality_homogeneous
    (X : C) {Y Z : C} (a : A) (f : ShiftHom Y Z a) :
    (orbitPushdownDualLinearYonedaComparisonApp
      (k := k) (A := A) X Z).comp
        (orbitPushdownHomogeneousMap
          (dualLinearYoneda (k := k) X) a f) =
      ((dualLinearYoneda (k := k)
          (C := ShiftOrbitCategory C A)
          (show ShiftOrbitCategory C A from X)).map
        (shiftOrbitOf Y Z a f)).hom.comp
          (orbitPushdownDualLinearYonedaComparisonApp
            (k := k) (A := A) X Y) := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro phi
  simp only [LinearMap.comp_apply]
  change orbitPushdownDualLinearYonedaComparisonApp
      (k := k) (A := A) X Z
      (orbitPushdownHomogeneousMap
        (dualLinearYoneda (k := k) X) a f
        (orbitPushdownLof (dualLinearYoneda (k := k) X) Y b phi)) =
    (dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
      (shiftOrbitOf Y Z a f)
      (orbitPushdownDualLinearYonedaComparisonApp
        (k := k) (A := A) X Y
        (orbitPushdownLof (dualLinearYoneda (k := k) X) Y b phi))
  rw [orbitPushdownHomogeneousMap_lof,
    orbitPushdownDualLinearYonedaComparisonApp_lof,
    orbitPushdownDualLinearYonedaComparisonApp_lof]
  let h := orbitPushdownArrow' (rfl : a + b = a + b) f
  change
    (dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
      (shiftOrbitFromShift Z (a + b))
      (dualLinearYonedaOrbitPullupApp
        (k := k) (A := A) X ((shiftFunctor C (a + b)).obj Z)
        ((dualLinearYoneda (k := k) X).map h phi)) =
    (dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
      (shiftOrbitOf Y Z a f)
      ((dualLinearYoneda (k := k)
          (C := ShiftOrbitCategory C A)
          (show ShiftOrbitCategory C A from X)).map
        (shiftOrbitFromShift Y b)
        (dualLinearYonedaOrbitPullupApp
          (k := k) (A := A) X ((shiftFunctor C b).obj Y) phi))
  rw [dualLinearYonedaOrbitPullupApp_naturality
    (k := k) (A := A) X h phi]
  change
    ((dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
      ((ShiftOrbitCategory.identityComponentFunctor
        (C := C) (A := A)).map h) ≫
      (dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
          (shiftOrbitFromShift Z (a + b))) _ =
    ((dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
          (shiftOrbitFromShift Y b) ≫
      (dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map
          (shiftOrbitOf Y Z a f)) _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun q ↦
    (dualLinearYoneda (k := k)
      (C := ShiftOrbitCategory C A)
      (show ShiftOrbitCategory C A from X)).map q _)
      (orbitPushdownArrow_comp_fromShift a b f)

/-- The assembled comparison is natural for every orbit morphism. -/
theorem orbitPushdownDualLinearYonedaComparisonApp_naturality
    (X : C) {Y Z : C} (f : ShiftOrbitHom A Y Z) :
    (orbitPushdownDualLinearYonedaComparisonApp
      (k := k) (A := A) X Z).comp
        (orbitPushdownMapLinear (dualLinearYoneda (k := k) X) f) =
      ((dualLinearYoneda (k := k)
          (C := ShiftOrbitCategory C A)
          (show ShiftOrbitCategory C A from X)).map f).hom.comp
        (orbitPushdownDualLinearYonedaComparisonApp
          (k := k) (A := A) X Y) := by
  classical
  let N := dualLinearYoneda (k := k)
    (C := ShiftOrbitCategory C A)
    (show ShiftOrbitCategory C A from X)
  change (orbitPushdownDualLinearYonedaComparisonApp
      (k := k) (A := A) X Z).comp
        (orbitPushdownMapLinear (dualLinearYoneda (k := k) X) f) =
    (N.map f).hom.comp
      (orbitPushdownDualLinearYonedaComparisonApp
        (k := k) (A := A) X Y)
  induction f using DirectSum.induction_on with
  | zero =>
      rw [map_zero, N.map_zero]
      rfl
  | of a g =>
      change (orbitPushdownDualLinearYonedaComparisonApp
          (k := k) (A := A) X Z).comp
            (orbitPushdownMapLinear (dualLinearYoneda (k := k) X)
              (shiftOrbitOf Y Z a g)) = _
      rw [orbitPushdownMapLinear_of]
      exact orbitPushdownDualLinearYonedaComparisonApp_naturality_homogeneous
        (k := k) (A := A) X a g
  | add f g hf hg =>
      rw [map_add, N.map_add]
      apply LinearMap.ext
      intro phi
      change orbitPushdownDualLinearYonedaComparisonApp
          (k := k) (A := A) X Z
            ((orbitPushdownMapLinear (dualLinearYoneda (k := k) X) f) phi +
              (orbitPushdownMapLinear
                (dualLinearYoneda (k := k) X) g) phi) =
        N.map f
            (orbitPushdownDualLinearYonedaComparisonApp
              (k := k) (A := A) X Y phi) +
          N.map g
            (orbitPushdownDualLinearYonedaComparisonApp
              (k := k) (A := A) X Y phi)
      rw [map_add]
      exact congrArg₂ (.+.) (LinearMap.congr_fun hf phi)
        (LinearMap.congr_fun hg phi)

/-- Orbit push-down of a dual corepresentable maps naturally to the
downstairs dual corepresentable. -/
noncomputable def orbitPushdownDualLinearYonedaComparison (X : C) :
    orbitPushdown (A := A) (dualLinearYoneda (k := k) X) ⟶
      dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X) where
  app Y := ModuleCat.ofHom
    (orbitPushdownDualLinearYonedaComparisonApp
      (k := k) (A := A) X (show C from Y))
  naturality {Y Z} f := by
    apply ModuleCat.hom_ext
    exact orbitPushdownDualLinearYonedaComparisonApp_naturality
      (k := k) (A := A) X f

/-- The push-down comparison commutes with morphisms of representing
objects.  This is the square needed to transport a projective-presentation
differential through the Nakayama construction. -/
theorem orbitPushdownDualLinearYonedaComparison_representing_naturality
    {X Z : C} (f : X ⟶ Z) :
    orbitPushdownNatTrans (A := A) (dualLinearYonedaMap (k := k) f) ≫
        orbitPushdownDualLinearYonedaComparison (k := k) (A := A) X =
      orbitPushdownDualLinearYonedaComparison (k := k) (A := A) Z ≫
        dualLinearYonedaMap (k := k)
          ((ShiftOrbitCategory.identityComponentFunctor
            (C := C) (A := A)).map f) := by
  classical
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro phi
  change orbitPushdownDualLinearYonedaComparisonApp
      (k := k) (A := A) X (show C from Y)
        (orbitPushdownNatTransAppLinear (A := A)
          (dualLinearYonedaMap (k := k) f) (show C from Y)
          (orbitPushdownLof (dualLinearYoneda (k := k) Z)
            (show C from Y) b phi)) =
    (dualLinearYonedaMap (k := k)
      ((ShiftOrbitCategory.identityComponentFunctor
        (C := C) (A := A)).map f)).app Y
      (orbitPushdownDualLinearYonedaComparisonApp
        (k := k) (A := A) Z (show C from Y)
        (orbitPushdownLof (dualLinearYoneda (k := k) Z)
          (show C from Y) b phi))
  rw [orbitPushdownNatTransAppLinear_lof,
    orbitPushdownDualLinearYonedaComparisonApp_lof,
    orbitPushdownDualLinearYonedaComparisonApp_lof,
    dualLinearYonedaOrbitPullupApp_representing_naturality
      (k := k) (A := A) f]
  have hnat := (dualLinearYonedaMap (k := k)
    ((ShiftOrbitCategory.identityComponentFunctor
      (C := C) (A := A)).map f)).naturality (shiftOrbitFromShift (show C from Y) b)
  exact congrArg (fun h ↦ h.hom
    (dualLinearYonedaOrbitPullupApp
      (k := k) (A := A) Z ((shiftFunctor C b).obj (show C from Y)) phi)) hnat.symm

/-- The objectwise finite-duality comparison underlying push-down of a dual
corepresentable. -/
noncomputable def orbitPushdownDualLinearYonedaValueEquiv
    (X Y : C)
    (hY : {b : A | Nontrivial
      (Module.Dual k (((shiftFunctor C b).obj Y ⟶ X)))}.Finite) :
    orbitPushdownValue (A := A) (dualLinearYoneda (k := k) X) Y ≃ₗ[k]
      Module.Dual k (ShiftOrbitHom A Y X) :=
  directSumDualEquivDualOfFiniteDual (k := k)
      (fun b ↦ ((shiftFunctor C b).obj Y ⟶ X)) hY ≪≫ₗ
    (shiftSourceHomDirectSumEquiv (k := k) (A := A) Y X).symm.dualMap

@[simp]
theorem orbitPushdownDualLinearYonedaValueEquiv_apply
    (X Y : C)
    (hY : {b : A | Nontrivial
      (Module.Dual k (((shiftFunctor C b).obj Y ⟶ X)))}.Finite)
    (Phi : orbitPushdownValue (A := A)
      (dualLinearYoneda (k := k) X) Y)
    (q : ShiftOrbitHom A Y X) :
    orbitPushdownDualLinearYonedaValueEquiv
        (k := k) X Y hY Phi q =
      directSumDualToDual (k := k)
        (fun b ↦ ((shiftFunctor C b).obj Y ⟶ X)) Phi
        ((shiftSourceHomDirectSumEquiv
          (k := k) (A := A) Y X).symm q) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Under finite support, the naturally assembled comparison is exactly the
basis-free direct-sum duality equivalence. -/
theorem orbitPushdownDualLinearYonedaComparisonApp_eq_valueEquiv
    (X Y : C)
    (hY : {b : A | Nontrivial
      (Module.Dual k (((shiftFunctor C b).obj Y ⟶ X)))}.Finite) :
    orbitPushdownDualLinearYonedaComparisonApp
        (k := k) (A := A) X Y =
      (orbitPushdownDualLinearYonedaValueEquiv
        (k := k) X Y hY).toLinearMap := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro phi
  change Module.Dual k (((shiftFunctor C b).obj Y ⟶ X)) at phi
  apply LinearMap.ext
  intro q
  change orbitPushdownDualLinearYonedaComparisonApp
      (k := k) (A := A) X Y
        (orbitPushdownLof (dualLinearYoneda (k := k) X) Y b phi) q =
    orbitPushdownDualLinearYonedaValueEquiv
      (k := k) X Y hY
        (orbitPushdownLof (dualLinearYoneda (k := k) X) Y b phi) q
  rw [orbitPushdownDualLinearYonedaComparisonApp_lof,
    orbitPushdownDualLinearYonedaValueEquiv_apply]
  change phi
      (shiftOrbitZeroComponentLinearMap
        (k := k) (A := A) ((shiftFunctor C b).obj Y) X
        (shiftOrbitCompHom (shiftOrbitFromShift Y b) q)) =
    directSumDualToDual (k := k)
      (fun c ↦ ((shiftFunctor C c).obj Y ⟶ X))
      (directSumInclusion (k := k)
        (fun c ↦ Module.Dual k ((shiftFunctor C c).obj Y ⟶ X))
        b phi)
      ((shiftSourceHomDirectSumEquiv
        (k := k) (A := A) Y X).symm q)
  rw [directSumDualToDual_lof_apply]
  exact congrArg phi
    (shiftSourceHomDirectSumEquiv_symm_apply_component
      (k := k) (A := A) Y X b q).symm

/-- If the translated dual Hom values have finite support at every object,
orbit push-down of a dual corepresentable is naturally isomorphic to the
downstairs dual corepresentable. -/
noncomputable def orbitPushdownDualLinearYonedaIso
    (X : C)
    (hX : ∀ Y : C, {b : A | Nontrivial
      (Module.Dual k (((shiftFunctor C b).obj Y ⟶ X)))}.Finite) :
    orbitPushdown (A := A) (dualLinearYoneda (k := k) X) ≅
      dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X) := by
  refine NatIso.ofComponents (fun Y ↦
    (orbitPushdownDualLinearYonedaValueEquiv
      (k := k) X (show C from Y) (hX (show C from Y))).toModuleIso) ?_
  intro Y Z f
  have hnat := (orbitPushdownDualLinearYonedaComparison
    (k := k) (A := A) X).naturality f
  apply ModuleCat.hom_ext
  change (orbitPushdownDualLinearYonedaValueEquiv
      (k := k) X (show C from Z) (hX (show C from Z))).toLinearMap.comp
        (orbitPushdownMapLinear (dualLinearYoneda (k := k) X) f) =
    ((dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C A)
        (show ShiftOrbitCategory C A from X)).map f).hom.comp
      (orbitPushdownDualLinearYonedaValueEquiv
        (k := k) X (show C from Y) (hX (show C from Y))).toLinearMap
  rw [← orbitPushdownDualLinearYonedaComparisonApp_eq_valueEquiv,
    ← orbitPushdownDualLinearYonedaComparisonApp_eq_valueEquiv]
  exact congrArg ModuleCat.Hom.hom hnat

/-- The forward map of the finite dual-corepresentable isomorphism is the
unrestricted natural comparison constructed above. -/
theorem orbitPushdownDualLinearYonedaIso_hom_eq_comparison
    (X : C)
    (hX : ∀ Y : C, {b : A | Nontrivial
      (Module.Dual k (((shiftFunctor C b).obj Y ⟶ X)))}.Finite) :
    (orbitPushdownDualLinearYonedaIso
      (k := k) (A := A) X hX).hom =
      orbitPushdownDualLinearYonedaComparison
        (k := k) (A := A) X := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  exact (orbitPushdownDualLinearYonedaComparisonApp_eq_valueEquiv
    (k := k) (A := A) X (show C from Y) (hX (show C from Y))).symm

/-- The finite push-down isomorphisms commute with morphisms of representing
objects. -/
theorem orbitPushdownDualLinearYonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z)
    (hX : ∀ Y : C, {b : A | Nontrivial
      (Module.Dual k (((shiftFunctor C b).obj Y ⟶ X)))}.Finite)
    (hZ : ∀ Y : C, {b : A | Nontrivial
      (Module.Dual k (((shiftFunctor C b).obj Y ⟶ Z)))}.Finite) :
    orbitPushdownNatTrans (A := A) (dualLinearYonedaMap (k := k) f) ≫
        (orbitPushdownDualLinearYonedaIso
          (k := k) (A := A) X hX).hom =
      (orbitPushdownDualLinearYonedaIso
        (k := k) (A := A) Z hZ).hom ≫
        dualLinearYonedaMap (k := k)
          ((ShiftOrbitCategory.identityComponentFunctor
            (C := C) (A := A)).map f) := by
  rw [orbitPushdownDualLinearYonedaIso_hom_eq_comparison,
    orbitPushdownDualLinearYonedaIso_hom_eq_comparison]
  exact orbitPushdownDualLinearYonedaComparison_representing_naturality
    (k := k) (A := A) f

section DeckAction

variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

omit [IsCancelSMul G C] in
set_option backward.isDefEq.respectTransparency false in
/-- Changing an upstairs representing object and then moving it to the chosen
orbit representative agrees with first moving both objects and then applying
the induced skeletal morphism. -/
theorem CoherentDeckShift.dualLinearYonedaMap_objectIsoDeckOrbitRepresentative_naturality
    {X Z : C} (f : X ⟶ Z) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    dualLinearYonedaMap (k := k)
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := Additive G)).map f) ≫
      (dualLinearYonedaMapIso (k := k)
        (D.objectIsoDeckOrbitRepresentative X)).hom =
    (dualLinearYonedaMapIso (k := k)
      (D.objectIsoDeckOrbitRepresentative Z)).hom ≫
      dualLinearYonedaMap (k := k)
        ((deckOrbitRepresentativeFunctor (C := C) (G := G)).map
          (D.orbitSkeletonMap f)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  rw [dualLinearYonedaMapIso_hom, dualLinearYonedaMapIso_hom,
    ← dualLinearYonedaMap_comp, ← dualLinearYonedaMap_comp]
  congr 1
  rw [D.deckOrbitRepresentativeFunctor_map_orbitSkeletonMap]
  simp [Category.assoc]

/-- Restricting the orbit dual corepresentable at a chosen representative
gives the literal dual corepresentable on the induced orbit skeleton. -/
noncomputable def CoherentDeckShift.deckOrbitRepresentativeDualLinearYonedaIso
    (q : MulAction.orbitRel.Quotient G C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    deckOrbitRepresentativeFunctor (C := C) (G := G) ⋙
        dualLinearYoneda (k := k)
          (C := ShiftOrbitCategory C (Additive G))
          (show ShiftOrbitCategory C (Additive G) from
            deckOrbitRepresentative (C := C) (G := G) q) ≅
      dualLinearYoneda (k := k)
        (C := DeckOrbitSkeleton C G) q := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  refine NatIso.ofComponents (fun Y ↦
    (InducedCategory.homLinearEquiv
      (R := k) (X := Y) (Y := q)).dualMap.toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  let eZ := (InducedCategory.homLinearEquiv
    (R := k) (X := Z) (Y := q)).toLinearMap
  let eY := (InducedCategory.homLinearEquiv
    (R := k) (X := Y) (Y := q)).toLinearMap
  let L := CategoryTheory.Linear.leftComp k
    (C := ShiftOrbitCategory C (Additive G))
    (show ShiftOrbitCategory C (Additive G) from
      deckOrbitRepresentative (C := C) (G := G) q)
    ((deckOrbitRepresentativeFunctor (C := C) (G := G)).map f)
  let L' := CategoryTheory.Linear.leftComp k
    (C := DeckOrbitSkeleton C G)
    (show DeckOrbitSkeleton C G from q) f
  change eZ.dualMap.comp L.dualMap = L'.dualMap.comp eY.dualMap
  calc
    _ = (L.comp eZ).dualMap :=
      LinearMap.dualMap_comp_dualMap eZ L
    _ = (eY.comp L').dualMap := by
      congr 1
    _ = _ := (LinearMap.dualMap_comp_dualMap L' eY).symm

omit [IsCancelSMul G C] in
/-- Restriction from the shift-orbit category to the chosen orbit skeleton
commutes with morphisms of representing objects. -/
theorem CoherentDeckShift.deckOrbitRepresentativeDualLinearYonedaIso_representing_naturality
    {q r : MulAction.orbitRel.Quotient G C}
    (f :
      letI := D.hasShift
      letI := D.additiveShift
      (show DeckOrbitSkeleton C G from q) ⟶
        (show DeckOrbitSkeleton C G from r)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (dualLinearYonedaMap (k := k)
          ((deckOrbitRepresentativeFunctor (C := C) (G := G)).map f)) ≫
      (D.deckOrbitRepresentativeDualLinearYonedaIso (k := k) q).hom =
    (D.deckOrbitRepresentativeDualLinearYonedaIso (k := k) r).hom ≫
      dualLinearYonedaMap (k := k) f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  let eQ := (InducedCategory.homLinearEquiv
    (R := k) (X := Y) (Y := q)).toLinearMap
  let eR := (InducedCategory.homLinearEquiv
    (R := k) (X := Y) (Y := r)).toLinearMap
  let R := CategoryTheory.Linear.rightComp k
    (C := ShiftOrbitCategory C (Additive G))
    (show ShiftOrbitCategory C (Additive G) from
      deckOrbitRepresentative (C := C) (G := G) Y)
    ((deckOrbitRepresentativeFunctor (C := C) (G := G)).map f)
  let R' := CategoryTheory.Linear.rightComp k
    (C := DeckOrbitSkeleton C G)
    (show DeckOrbitSkeleton C G from Y) f
  change eQ.dualMap.comp R.dualMap = R'.dualMap.comp eR.dualMap
  calc
    _ = (R.comp eQ).dualMap :=
      LinearMap.dualMap_comp_dualMap eQ R
    _ = (eR.comp R').dualMap := by
      congr 1
    _ = _ := (LinearMap.dualMap_comp_dualMap R' eR).symm

/-- For a finite dual corepresentable, the objectwise comparison is
available at every upstairs object from literal finite support and freeness
of the deck action. -/
noncomputable def CoherentDeckShift.orbitPushdownDualLinearYonedaValueEquiv
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    orbitPushdownValue (A := Additive G)
        (dualLinearYoneda (k := k) X) Y ≃ₗ[k]
      Module.Dual k (ShiftOrbitHom (Additive G) Y X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let M := finiteDimensionalDualLinearYoneda (k := k) X hX
  exact MagnitudeConjecture.CoveringHom.orbitPushdownDualLinearYonedaValueEquiv
    (k := k) X Y
    (D.finite_nontrivial_shift_values (k := k) M Y)

/-- Deck freeness and finite support make the objectwise comparison a
natural isomorphism on the full shift-orbit category. -/
noncomputable def CoherentDeckShift.orbitPushdownDualLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    orbitPushdown (A := Additive G) (dualLinearYoneda (k := k) X) ≅
      dualLinearYoneda (k := k)
        (C := ShiftOrbitCategory C (Additive G))
        (show ShiftOrbitCategory C (Additive G) from X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let M := finiteDimensionalDualLinearYoneda (k := k) X hX
  exact MagnitudeConjecture.CoveringHom.orbitPushdownDualLinearYonedaIso
    (k := k) X (fun Y ↦
      D.finite_nontrivial_shift_values (k := k) M Y)

/-- The deck-finite orbit-category comparison commutes with morphisms of
representing objects. -/
theorem CoherentDeckShift.orbitPushdownDualLinearYonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) Z)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    orbitPushdownNatTrans (A := Additive G)
        (dualLinearYonedaMap (k := k) f) ≫
      (D.orbitPushdownDualLinearYonedaIso (k := k) X hX).hom =
    (D.orbitPushdownDualLinearYonedaIso (k := k) Z hZ).hom ≫
      dualLinearYonedaMap (k := k)
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := Additive G)).map f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let MX := finiteDimensionalDualLinearYoneda (k := k) X hX
  let MZ := finiteDimensionalDualLinearYoneda (k := k) Z hZ
  exact MagnitudeConjecture.CoveringHom.orbitPushdownDualLinearYonedaIso_representing_naturality
    (k := k) (A := Additive G) f
      (fun Y ↦ D.finite_nontrivial_shift_values (k := k) MX Y)
      (fun Y ↦ D.finite_nontrivial_shift_values (k := k) MZ Y)

/-- Skeletal Gabriel push-down sends a finite dual corepresentable to the
dual corepresentable at the strict orbit of its representing object. -/
noncomputable def CoherentDeckShift.orbitSkeletonPushdownDualLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    orbitSkeletonPushdown (G := G) (dualLinearYoneda (k := k) X) ≅
      dualLinearYoneda (k := k)
        (C := DeckOrbitSkeleton C G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let q : MulAction.orbitRel.Quotient G C := Quotient.mk'' X
  exact Functor.isoWhiskerLeft J
      (D.orbitPushdownDualLinearYonedaIso (k := k) X hX) ≪≫
    Functor.isoWhiskerLeft J
      (dualLinearYonedaMapIso (k := k)
        (D.objectIsoDeckOrbitRepresentative X)) ≪≫
    D.deckOrbitRepresentativeDualLinearYonedaIso (k := k) q

set_option backward.isDefEq.respectTransparency false in
/-- The skeletal dual-corepresentable isomorphisms commute with the morphism
between strict deck orbits induced by an upstairs representing morphism. -/
theorem CoherentDeckShift.orbitSkeletonPushdownDualLinearYonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) Z)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G)
          (dualLinearYonedaMap (k := k) f)) ≫
      (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) X hX).hom =
    (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) Z hZ).hom ≫
      dualLinearYonedaMap (k := k) (D.orbitSkeletonMap f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let p := Functor.whiskerLeft J
    (orbitPushdownNatTrans (A := Additive G)
      (dualLinearYonedaMap (k := k) f))
  let aX := Functor.whiskerLeft J
    (D.orbitPushdownDualLinearYonedaIso (k := k) X hX).hom
  let aZ := Functor.whiskerLeft J
    (D.orbitPushdownDualLinearYonedaIso (k := k) Z hZ).hom
  let m := Functor.whiskerLeft J
    (dualLinearYonedaMap (k := k)
      ((ShiftOrbitCategory.identityComponentFunctor
        (C := C) (A := Additive G)).map f))
  let bX := Functor.whiskerLeft J
    (dualLinearYonedaMapIso (k := k)
      (D.objectIsoDeckOrbitRepresentative X)).hom
  let bZ := Functor.whiskerLeft J
    (dualLinearYonedaMapIso (k := k)
      (D.objectIsoDeckOrbitRepresentative Z)).hom
  let n := Functor.whiskerLeft J
    (dualLinearYonedaMap (k := k) (J.map (D.orbitSkeletonMap f)))
  let cX := (D.deckOrbitRepresentativeDualLinearYonedaIso
    (k := k) (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)).hom
  let cZ := (D.deckOrbitRepresentativeDualLinearYonedaIso
    (k := k) (Quotient.mk'' Z : MulAction.orbitRel.Quotient G C)).hom
  let d := dualLinearYonedaMap (k := k) (D.orbitSkeletonMap f)
  change p ≫ aX ≫ bX ≫ cX = (aZ ≫ bZ ≫ cZ) ≫ d
  have h₁ : p ≫ aX = aZ ≫ m := by
    dsimp only [p, aX, aZ, m, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (D.orbitPushdownDualLinearYonedaIso_representing_naturality
        (k := k) f hX hZ)
  have h₂ : m ≫ bX = bZ ≫ n := by
    dsimp only [m, bX, bZ, n, J]
    simpa only [Functor.whiskerLeft_comp] using congrArg
      (Functor.whiskerLeft J)
      (D.dualLinearYonedaMap_objectIsoDeckOrbitRepresentative_naturality
        (k := k) f)
  have h₃ : n ≫ cX = cZ ≫ d := by
    exact D.deckOrbitRepresentativeDualLinearYonedaIso_representing_naturality
      (k := k) (D.orbitSkeletonMap f)
  calc
    p ≫ aX ≫ bX ≫ cX = (p ≫ aX) ≫ bX ≫ cX := by
      simp only [Category.assoc]
    _ = (aZ ≫ m) ≫ bX ≫ cX := by rw [h₁]
    _ = aZ ≫ (m ≫ bX) ≫ cX := by simp only [Category.assoc]
    _ = aZ ≫ (bZ ≫ n) ≫ cX := by rw [h₂]
    _ = aZ ≫ bZ ≫ (n ≫ cX) := by simp only [Category.assoc]
    _ = aZ ≫ bZ ≫ (cZ ≫ d) := by rw [h₃]
    _ = (aZ ≫ bZ ≫ cZ) ≫ d := by simp only [Category.assoc]

/-- Bundled linear-module form of skeletal push-down preserving a finite
dual corepresentable. -/
noncomputable def CoherentDeckShift.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (linearModuleOrbitSkeletonPushdown
      (k := k) (C := C) (G := G)).obj
        (dualLinearYonedaLinearModule (k := k) X) ≅
      dualLinearYonedaLinearModule (k := k)
        (C := DeckOrbitSkeleton C G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (IsLinearModule (C := DeckOrbitSkeleton C G) k).ι.preimageIso
    (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) X hX)

@[simp]
theorem CoherentDeckShift.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) X hX).hom.hom =
      (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) X hX).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := (IsLinearModule.{u, max v w, uK, max uK (max v w)}
    (C := DeckOrbitSkeleton C G) k).ι
  let LX := (linearModuleOrbitSkeletonPushdown
    (k := k) (C := C) (G := G)).obj
      (dualLinearYonedaLinearModule (k := k) X)
  let RX := dualLinearYonedaLinearModule (k := k)
    (C := DeckOrbitSkeleton C G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
  change (J.preimage (X := LX) (Y := RX)
      (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) X hX).hom).hom =
    (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) X hX).hom
  exact J.map_preimage (X := LX) (Y := RX)
    (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) X hX).hom

set_option backward.isDefEq.respectTransparency false in
/-- The skeletal comparison is natural in the representing object inside the
literal category of additive linear modules. -/
theorem CoherentDeckShift.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) Z)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).map
        (dualLinearYonedaLinearModuleMap (k := k) f) ≫
      (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k) X hX).hom =
    (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) Z hZ).hom ≫
      dualLinearYonedaLinearModuleMap (k := k) (D.orbitSkeletonMap f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  apply ObjectProperty.hom_ext
  change ((linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).map
        (dualLinearYonedaLinearModuleMap (k := k) f)).hom ≫
      (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k) X hX).hom.hom =
    (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) Z hZ).hom.hom ≫
      (dualLinearYonedaLinearModuleMap
        (k := k) (D.orbitSkeletonMap f)).hom
  rw [linearModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom,
    linearModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom]
  change Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G)
          (dualLinearYonedaMap (k := k) f)) ≫
      (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) X hX).hom =
    (D.orbitSkeletonPushdownDualLinearYonedaIso (k := k) Z hZ).hom ≫
      dualLinearYonedaMap (k := k) (D.orbitSkeletonMap f)
  exact D.orbitSkeletonPushdownDualLinearYonedaIso_representing_naturality
    (k := k) f hX hZ

/-- The downstairs skeletal dual corepresentable, with finiteness transported
from its finite upstairs source through skeletal push-down. -/
noncomputable def CoherentDeckShift.orbitSkeletonFiniteDimensionalDualLinearYoneda
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    FiniteDimensionalModuleCategory
      (C := DeckOrbitSkeleton C G) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let MX := finiteDimensionalDualLinearYoneda (k := k) X hX
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let e := D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
    (k := k) X hX
  exact ⟨dualLinearYonedaLinearModule (k := k)
      (C := DeckOrbitSkeleton C G)
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C),
    (IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k).prop_of_iso
      e (P.obj MX).property⟩

/-- The finite-dimensional skeletal dual corepresentables inherit the map
induced by a morphism of upstairs representing objects. -/
noncomputable def CoherentDeckShift.orbitSkeletonFiniteDimensionalDualLinearYonedaMap
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) Z)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    D.orbitSkeletonFiniteDimensionalDualLinearYoneda (k := k) Z hZ ⟶
      D.orbitSkeletonFiniteDimensionalDualLinearYoneda (k := k) X hX := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact ObjectProperty.homMk
    (dualLinearYonedaLinearModuleMap (k := k) (D.orbitSkeletonMap f))

/-- Literal finite-dimensional skeletal push-down preserves a finite dual
corepresentable. -/
noncomputable def CoherentDeckShift.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (finiteDimensionalDualLinearYoneda (k := k) X hX) ≅
      D.orbitSkeletonFiniteDimensionalDualLinearYoneda
        (k := k) X hX := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (IsFiniteDimensionalModule
    (C := DeckOrbitSkeleton C G) k).ι.preimageIso
      (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k) X hX)

@[simp]
theorem CoherentDeckShift.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) X hX).hom.hom =
      (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k) X hX).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let J := (IsFiniteDimensionalModule.{u, max v w, uK,
    max uK (max v w)} (C := DeckOrbitSkeleton C G) k).ι
  let LX := (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
    (finiteDimensionalDualLinearYoneda (k := k) X hX)
  let RX := D.orbitSkeletonFiniteDimensionalDualLinearYoneda
    (k := k) X hX
  change (J.preimage (X := LX) (Y := RX)
      (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k) X hX).hom).hom =
    (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) X hX).hom
  exact J.map_preimage (X := LX) (Y := RX)
    (D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) X hX).hom

set_option backward.isDefEq.respectTransparency false in
/-- The literal finite-dimensional skeletal push-down comparison commutes
with maps of representing objects. -/
theorem CoherentDeckShift.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso_representing_naturality
    {X Z : C} (f : X ⟶ Z)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hZ : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) Z)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map
        (finiteDimensionalDualLinearYonedaMap (k := k) f hX hZ) ≫
      (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k) X hX).hom =
    (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) Z hZ).hom ≫
      D.orbitSkeletonFiniteDimensionalDualLinearYonedaMap
        (k := k) f hX hZ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  apply ObjectProperty.hom_ext
  change ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map
        (finiteDimensionalDualLinearYonedaMap (k := k) f hX hZ)).hom ≫
      (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
        (k := k) X hX).hom.hom =
    (D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
      (k := k) Z hZ).hom.hom ≫
      (D.orbitSkeletonFiniteDimensionalDualLinearYonedaMap
        (k := k) f hX hZ).hom
  rw [finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom,
    finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso_hom_hom]
  exact D.linearModuleOrbitSkeletonPushdownDualLinearYonedaIso_representing_naturality
    (k := k) f hX hZ

end DeckAction

end MagnitudeConjecture.CoveringHom
