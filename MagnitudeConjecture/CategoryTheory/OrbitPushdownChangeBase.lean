import MagnitudeConjecture.CategoryTheory.OrbitPushdownDescent

/-!
# Change of base for orbit push-down

A linear functor commuting coherently with shifts induces a functor between
the corresponding shift-orbit categories.  This file proves that Gabriel
push-down after precomposition by such a functor is naturally isomorphic to
push-down after applying the induced orbit functor.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.DirectSumFubini

namespace MagnitudeConjecture.CoveringHom

universe u₁ v₁ u₂ v₂ w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable {A : Type w} [AddGroup A]
variable [HasShift C A] [HasShift D A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor D a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]
variable [∀ a : A, (shiftFunctor D a).Linear k]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] [F.CommShift A]
variable (M : D ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]

/-- On push-down values, change of base applies the shift-commutation
isomorphism independently on every degree summand. -/
noncomputable def orbitPushdownCommShiftLinearEquiv (X : C) :
    orbitPushdownValue (A := A) (F ⋙ M) X ≃ₗ[k]
      orbitPushdownValue (A := A) M (F.obj X) :=
  mapRangeLinearEquiv fun a ↦
    (M.mapIso ((F.commShiftIso a).app X)).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor D a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [∀ a : A, (shiftFunctor D a).Linear k]
  [F.Additive] [F.Linear k] [M.Additive] [M.Linear k] in
@[simp]
theorem orbitPushdownCommShiftLinearEquiv_lof
    (X : C) (b : A) (x : M.obj (F.obj ((shiftFunctor C b).obj X))) :
    orbitPushdownCommShiftLinearEquiv F M X
        (orbitPushdownLof (F ⋙ M) X b x) =
      orbitPushdownLof M (F.obj X) b
        (M.map ((F.commShiftIso b).hom.app X) x) := by
  classical
  rw [orbitPushdownLof_eq_directSumOf,
    orbitPushdownLof_eq_directSumOf]
  unfold orbitPushdownCommShiftLinearEquiv
  rw [mapRangeLinearEquiv_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [Preadditive D]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor D a).Additive] [F.Additive] in
/-- Change of base intertwines the component arrows defining push-down. -/
theorem map_orbitPushdownArrow_comp_commShift
    {X Y : C} (a b : A) (f : ShiftHom X Y a) :
    F.map (orbitPushdownArrow' (C := C) rfl f) ≫
        (F.commShiftIso (a + b)).hom.app Y =
      (F.commShiftIso b).hom.app X ≫
        orbitPushdownArrow' (C := D) rfl
          (shiftOrbitDescendHomogeneousMap F a f) := by
  unfold orbitPushdownArrow' shiftOrbitDescendHomogeneousMap
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd]
  erw [F.map_comp]
  have hadd := congrArg Iso.hom (F.commShiftIso_add a b)
  have haddY := NatTrans.congr_app hadd Y
  simp only [Functor.CommShift.isoAdd_hom_app] at haddY
  rw [haddY]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc
    ((shiftFunctorAdd C a b).inv.app Y)
    ((shiftFunctorAdd C a b).hom.app Y)]
  rw [Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [F.commShiftIso_hom_naturality_assoc f b]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor D a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [∀ a : A, (shiftFunctor D a).Linear k]
  [F.Additive] [F.Linear k] [M.Additive] [M.Linear k] in
/-- The value equivalence is natural for a homogeneous orbit morphism. -/
theorem orbitPushdownCommShiftLinearEquiv_naturality_homogeneous
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    (orbitPushdownCommShiftLinearEquiv F M Y).toLinearMap.comp
        (orbitPushdownHomogeneousMap (F ⋙ M) a f) =
      (orbitPushdownHomogeneousMap M a
        (shiftOrbitDescendHomogeneousMap F a f)).comp
          (orbitPushdownCommShiftLinearEquiv F M X).toLinearMap := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change orbitPushdownCommShiftLinearEquiv F M Y
      (orbitPushdownHomogeneousMap (F ⋙ M) a f
        (orbitPushdownLof (F ⋙ M) X b x)) =
    orbitPushdownHomogeneousMap M a
      (shiftOrbitDescendHomogeneousMap F a f)
      (orbitPushdownCommShiftLinearEquiv F M X
        (orbitPushdownLof (F ⋙ M) X b x))
  rw [orbitPushdownHomogeneousMap_lof,
    orbitPushdownCommShiftLinearEquiv_lof,
    orbitPushdownCommShiftLinearEquiv_lof,
    orbitPushdownHomogeneousMap_lof]
  apply congrArg (orbitPushdownLof M (F.obj Y) (a + b))
  simp only [orbitPushdownComponent, orbitPushdownComponent',
    Functor.comp_map]
  have hmap :
      M.map (F.map (orbitPushdownArrow' (C := C) rfl f)) ≫
          M.map ((F.commShiftIso (a + b)).hom.app Y) =
        M.map ((F.commShiftIso b).hom.app X) ≫
          M.map (orbitPushdownArrow' (C := D) rfl
            (shiftOrbitDescendHomogeneousMap F a f)) := by
    rw [← M.map_comp,
      map_orbitPushdownArrow_comp_commShift,
      M.map_comp]
  exact congr($(hmap) x)

/-- The value equivalence is natural for every finite-support orbit
morphism. -/
theorem orbitPushdownCommShiftLinearEquiv_naturality
    {X Y : C} (f : ShiftOrbitHom A X Y) :
    (orbitPushdownCommShiftLinearEquiv F M Y).toLinearMap.comp
        (orbitPushdownMapLinear (F ⋙ M) f) =
      (orbitPushdownMapLinear M
        (shiftOrbitDescendMapLinear (k := k) F f)).comp
          (orbitPushdownCommShiftLinearEquiv F M X).toLinearMap := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · ext x
    simp
  · intro a fa
    have hfa :
        DirectSum.of (fun c : A ↦ ShiftHom X Y c) a fa =
          shiftOrbitOf X Y a fa :=
      (shiftOrbitOf_eq_directSumOf X Y a fa).symm
    rw [hfa]
    rw [shiftOrbitDescendMapLinear_of,
      orbitPushdownMapLinear_of, orbitPushdownMapLinear_of]
    exact orbitPushdownCommShiftLinearEquiv_naturality_homogeneous
      F M a fa
  · intro f g hf hg
    rw [map_add, map_add, map_add]
    apply LinearMap.ext
    intro x
    simpa using congrArg₂ (.+.)
      (LinearMap.congr_fun hf x) (LinearMap.congr_fun hg x)

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor D a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [∀ a : A, (shiftFunctor D a).Linear k]
  [F.Additive] [F.Linear k] in
/-- The change-of-base equivalence is natural in the module. -/
theorem orbitPushdownCommShiftLinearEquiv_module_naturality
    {M L : D ⥤ ModuleCat.{uM} k}
    [M.Additive] [M.Linear k] [L.Additive] [L.Linear k]
    (α : M ⟶ L) (X : C) :
    (orbitPushdownCommShiftLinearEquiv F L X).toLinearMap.comp
        (orbitPushdownNatTransAppLinear (A := A)
          (Functor.whiskerLeft F α) X) =
      (orbitPushdownNatTransAppLinear (A := A) α (F.obj X)).comp
        (orbitPushdownCommShiftLinearEquiv F M X).toLinearMap := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change orbitPushdownCommShiftLinearEquiv F L X
      (orbitPushdownNatTransAppLinear (A := A)
        (Functor.whiskerLeft F α) X
        (orbitPushdownLof (F ⋙ M) X b x)) =
    orbitPushdownNatTransAppLinear (A := A) α (F.obj X)
      (orbitPushdownCommShiftLinearEquiv F M X
        (orbitPushdownLof (F ⋙ M) X b x))
  rw [orbitPushdownNatTransAppLinear_lof,
    orbitPushdownCommShiftLinearEquiv_lof,
    orbitPushdownCommShiftLinearEquiv_lof,
    orbitPushdownNatTransAppLinear_lof]
  apply congrArg (orbitPushdownLof L (F.obj X) b)
  have hα :
      α.app (F.obj ((shiftFunctor C b).obj X)) ≫
          L.map ((F.commShiftIso b).hom.app X) =
        M.map ((F.commShiftIso b).hom.app X) ≫
          α.app ((shiftFunctor D b).obj (F.obj X)) := by
    exact (α.naturality ((F.commShiftIso b).hom.app X)).symm
  exact congr($(hα) x)

/-- Push-down commutes with change of base along a shift-compatible linear
functor. -/
noncomputable def orbitPushdownCommShiftIso :
    orbitPushdown (A := A) (F ⋙ M) ≅
      shiftOrbitMapFunctor (k := k) (A := A) F ⋙
        orbitPushdown (A := A) M :=
  NatIso.ofComponents
    (fun X ↦ (orbitPushdownCommShiftLinearEquiv F M
      (show C from X)).toModuleIso)
    (fun {X Y} f ↦ by
      apply ModuleCat.hom_ext
      change
        (orbitPushdownCommShiftLinearEquiv F M
          (show C from Y)).toLinearMap.comp
            (orbitPushdownMapLinear (F ⋙ M) f) =
          (orbitPushdownMapLinear M
            (shiftOrbitDescendMapLinear (k := k) F f)).comp
              (orbitPushdownCommShiftLinearEquiv F M
                (show C from X)).toLinearMap
      exact orbitPushdownCommShiftLinearEquiv_naturality F M f)

end MagnitudeConjecture.CoveringHom
