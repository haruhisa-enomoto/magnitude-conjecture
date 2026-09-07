import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.ObjectDeletionComparison

/-!
# Extending modules across object deletion

A module over `C/(S)` is viewed in the manuscript as an ambient `C`-module
which vanishes on every deleted object.  This file constructs that ambient
module.  Its value at `X` is the dependent product over proofs that `X`
survives.  Thus it is canonically the original value when `X ∉ S`, and is a
zero object when `X ∈ S`.  Maps between survivors are induced by the deletion
quotient, while maps out of a deleted object are zero.

The construction preserves linearity and finite-dimensional finite support.
It is the stage-to-ambient bridge used by the common finite control window in
the covering average.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v w uM

variable {k : Type w} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable (S : Set C)

local instance deletionMembershipDecidable : DecidablePred (fun X : C ↦ X ∈ S) :=
  Classical.decPred _

/-- The value of extension by zero at an ambient object.  The indexing
proposition is empty precisely at a deleted object. -/
abbrev moduleExtensionByZeroObj
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k) (X : C) :
    ModuleCat.{uM} k :=
  ModuleCat.of k
    ((hX : PLift (X ∉ S)) → M.obj (survivingObj (k := k) C S hX.down))

/-- At a surviving object, the dependent-product model of extension by zero
is canonically the original module value. -/
def moduleExtensionByZeroObjIso
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    {X : C} (hX : X ∉ S) :
    moduleExtensionByZeroObj (k := k) C S M X ≅
      M.obj (survivingObj (k := k) C S hX) := by
  letI : Unique (PLift (X ∉ S)) :=
    { default := PLift.up hX
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  exact (LinearEquiv.piUnique k
    (fun h : PLift (X ∉ S) ↦
      M.obj (survivingObj (k := k) C S h.down))).toModuleIso

@[simp]
theorem moduleExtensionByZeroObjIso_hom_apply
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    {X : C} (hX : X ∉ S)
    (m : moduleExtensionByZeroObj (k := k) C S M X) :
    (moduleExtensionByZeroObjIso (k := k) C S M hX).hom.hom m =
      m (PLift.up hX) := by
  rfl

@[simp]
theorem moduleExtensionByZeroObjIso_inv_apply
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    {X : C} (hX : X ∉ S)
    (m : M.obj (survivingObj (k := k) C S hX))
    (h : PLift (X ∉ S)) :
    (moduleExtensionByZeroObjIso (k := k) C S M hX).inv.hom m h = m := by
  have hh : h = PLift.up hX := Subsingleton.elim _ _
  cases hh
  rfl

/-- Every object of the deletion category is canonically isomorphic to the
surviving object represented by its underlying ambient object. -/
def survivingObjIso (X : DeletionCategory (k := k) C S) :
    survivingObj (k := k) C S X.property ≅ X := by
  rcases X with ⟨⟨X⟩, hX⟩
  exact Iso.refl _

@[simp]
theorem survivingObjIso_survivingObj {X : C} (hX : X ∉ S) :
    survivingObjIso (k := k) C S (survivingObj (k := k) C S hX) =
      Iso.refl _ := by
  rfl

/-- The surviving-value identification, expressed at an arbitrary object of
the deletion category. -/
def moduleExtensionByZeroObjIsoAt
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    (X : DeletionCategory (k := k) C S) :
    moduleExtensionByZeroObj (k := k) C S M X.obj.as ≅ M.obj X :=
  moduleExtensionByZeroObjIso (k := k) C S M X.property ≪≫
    M.mapIso (survivingObjIso (k := k) C S X)

/-- The action of extension by zero on an ambient morphism. -/
def moduleExtensionByZeroMap
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    {X Y : C} (f : X ⟶ Y) :
    moduleExtensionByZeroObj (k := k) C S M X ⟶
      moduleExtensionByZeroObj (k := k) C S M Y :=
  ModuleCat.ofHom
    { toFun := fun m hY ↦ if hX : X ∉ S then
        (M.map (survivingMap (k := k) C S hX hY.down f)).hom (m ⟨hX⟩)
      else 0
      map_add' := by
        intro m n
        funext hY
        by_cases hX : X ∉ S <;> simp [hX]
      map_smul' := by
        intro r m
        funext hY
        by_cases hX : X ∉ S <;> simp [hX] }

@[simp]
theorem moduleExtensionByZeroMap_apply_of_not_mem
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    {X Y : C} (f : X ⟶ Y) (hX : X ∉ S)
    (m : moduleExtensionByZeroObj (k := k) C S M X)
    (hY : PLift (Y ∉ S)) :
    (moduleExtensionByZeroMap (k := k) C S M f).hom m hY =
      (M.map (survivingMap (k := k) C S hX hY.down f)).hom (m ⟨hX⟩) := by
  change (if h : X ∉ S then
    (M.map (survivingMap (k := k) C S h hY.down f)).hom (m ⟨h⟩)
    else 0) = _
  simp [hX]

@[simp]
theorem moduleExtensionByZeroMap_apply_of_mem
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    {X Y : C} (f : X ⟶ Y) (hX : X ∈ S)
    (m : moduleExtensionByZeroObj (k := k) C S M X)
    (hY : PLift (Y ∉ S)) :
    (moduleExtensionByZeroMap (k := k) C S M f).hom m hY = 0 := by
  change (if h : X ∉ S then
    (M.map (survivingMap (k := k) C S h hY.down f)).hom (m ⟨h⟩)
    else 0) = 0
  simp [hX]

/-- Extension by zero from modules on the object-deletion category to
ambient modules. -/
def moduleExtensionByZero
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k) [M.Additive] :
    C ⥤ ModuleCat.{uM} k where
  obj := moduleExtensionByZeroObj (k := k) C S M
  map := moduleExtensionByZeroMap (k := k) C S M
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply funext
    intro hX
    change (moduleExtensionByZeroMap (k := k) C S M (𝟙 X)).hom m hX = m hX
    have hid : survivingMap (k := k) C S hX.down hX.down (𝟙 X) = 𝟙 _ := by
      apply ObjectProperty.hom_ext
      exact (rawFunctor (k := k) C S).map_id X
    rw [moduleExtensionByZeroMap_apply_of_not_mem
      (k := k) C S M (𝟙 X) hX.down m hX, hid, M.map_id]
    have hh : PLift.up hX.down = hX := Subsingleton.elim _ _
    cases hh
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply funext
    intro hZ
    by_cases hX : X ∉ S
    · by_cases hY : Y ∉ S
      · change (moduleExtensionByZeroMap (k := k) C S M (f ≫ g)).hom m hZ =
          (moduleExtensionByZeroMap (k := k) C S M g).hom
            ((moduleExtensionByZeroMap (k := k) C S M f).hom m) hZ
        rw [moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M (f ≫ g) hX m hZ,
          moduleExtensionByZeroMap_apply_of_not_mem
            (k := k) C S M g hY _ hZ,
          moduleExtensionByZeroMap_apply_of_not_mem
            (k := k) C S M f hX m (PLift.up hY),
          survivingMap_comp (k := k) C S hX hY hZ.down f g,
          M.map_comp]
        rfl
      · have hzero : survivingMap (k := k) C S hX hZ.down (f ≫ g) = 0 := by
          apply ObjectProperty.hom_ext
          exact ((ideal (k := k) C S).map_eq_zero_iff (f ≫ g)).2
            (comp_mem_ideal (k := k) C S (not_not.mp hY) f g)
        change (moduleExtensionByZeroMap (k := k) C S M (f ≫ g)).hom m hZ =
          (moduleExtensionByZeroMap (k := k) C S M g).hom
            ((moduleExtensionByZeroMap (k := k) C S M f).hom m) hZ
        rw [moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M (f ≫ g) hX m hZ, hzero, M.map_zero,
          moduleExtensionByZeroMap_apply_of_mem
            (k := k) C S M g (not_not.mp hY) _ hZ]
        rfl
    · have hfzero : (moduleExtensionByZeroMap (k := k) C S M f).hom m = 0 := by
        apply funext
        intro hY
        exact moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S M f (not_not.mp hX) m hY
      change (moduleExtensionByZeroMap (k := k) C S M (f ≫ g)).hom m hZ =
        (moduleExtensionByZeroMap (k := k) C S M g).hom
          ((moduleExtensionByZeroMap (k := k) C S M f).hom m) hZ
      rw [moduleExtensionByZeroMap_apply_of_mem
        (k := k) C S M (f ≫ g) (not_not.mp hX) m hZ, hfzero]
      have hmapzero := congrFun
        (moduleExtensionByZeroMap (k := k) C S M g).hom.map_zero hZ
      exact (hmapzero.trans (Pi.zero_apply hZ)).symm

/-- Evaluation at surviving objects intertwines the extended action with the
original deletion-category action. -/
theorem moduleExtensionByZeroObjIso_map
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k) [M.Additive]
    {X Y : C} (hX : X ∉ S) (hY : Y ∉ S) (f : X ⟶ Y) :
    (moduleExtensionByZero (k := k) C S M).map f ≫
        (moduleExtensionByZeroObjIso (k := k) C S M hY).hom =
      (moduleExtensionByZeroObjIso (k := k) C S M hX).hom ≫
        M.map (survivingMap (k := k) C S hX hY f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (moduleExtensionByZeroObjIso (k := k) C S M hY).hom.hom
      ((moduleExtensionByZeroMap (k := k) C S M f).hom m) =
    (M.map (survivingMap (k := k) C S hX hY f)).hom
      ((moduleExtensionByZeroObjIso (k := k) C S M hX).hom.hom m)
  rw [moduleExtensionByZeroObjIso_hom_apply,
    moduleExtensionByZeroMap_apply_of_not_mem,
    moduleExtensionByZeroObjIso_hom_apply]

/-- A deleted object has zero value in the extended module. -/
theorem moduleExtensionByZero_obj_isZero_of_mem
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k) [M.Additive]
    {X : C} (hX : X ∈ S) :
    IsZero ((moduleExtensionByZero (k := k) C S M).obj X) := by
  letI : Subsingleton ((moduleExtensionByZero (k := k) C S M).obj X) :=
    ⟨fun m n ↦ by
      change ((h : PLift (X ∉ S)) →
        M.obj (survivingObj (k := k) C S h.down)) at m n
      funext h
      exact (h.down hX).elim⟩
  exact ModuleCat.isZero_of_subsingleton _

noncomputable instance moduleExtensionByZero_additive
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k) [M.Additive] :
    (moduleExtensionByZero (k := k) C S M).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change moduleExtensionByZeroObj (k := k) C S M X at m
    apply funext
    intro hY
    by_cases hX : X ∉ S
    · change (moduleExtensionByZeroMap (k := k) C S M (f + g)).hom m hY =
        ((moduleExtensionByZeroMap (k := k) C S M f) +
          moduleExtensionByZeroMap (k := k) C S M g).hom m hY
      rw [ModuleCat.hom_add, LinearMap.add_apply, Pi.add_apply,
        moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M (f + g) hX m hY,
        survivingMap_add, M.map_add, ModuleCat.hom_add, LinearMap.add_apply,
        moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M f hX m hY,
        moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M g hX m hY]
    · change (moduleExtensionByZeroMap (k := k) C S M (f + g)).hom m hY =
        ((moduleExtensionByZeroMap (k := k) C S M f) +
          moduleExtensionByZeroMap (k := k) C S M g).hom m hY
      rw [ModuleCat.hom_add, LinearMap.add_apply, Pi.add_apply,
        moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S M (f + g) (not_not.mp hX) m hY,
        moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S M f (not_not.mp hX) m hY,
        moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S M g (not_not.mp hX) m hY,
        add_zero]

noncomputable instance moduleExtensionByZero_linear
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k)
    [M.Additive] [M.Linear k] :
    (moduleExtensionByZero (k := k) C S M).Linear k where
  map_smul := by
    intro X Y f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change moduleExtensionByZeroObj (k := k) C S M X at m
    apply funext
    intro hY
    by_cases hX : X ∉ S
    · change (moduleExtensionByZeroMap (k := k) C S M (r • f)).hom m hY =
        (r • moduleExtensionByZeroMap (k := k) C S M f).hom m hY
      rw [ModuleCat.hom_smul, LinearMap.smul_apply, Pi.smul_apply,
        moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M (r • f) hX m hY,
        survivingMap_smul, M.map_smul, ModuleCat.hom_smul,
        LinearMap.smul_apply,
        moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M f hX m hY]
    · change (moduleExtensionByZeroMap (k := k) C S M (r • f)).hom m hY =
        (r • moduleExtensionByZeroMap (k := k) C S M f).hom m hY
      rw [ModuleCat.hom_smul, LinearMap.smul_apply, Pi.smul_apply,
        moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S M (r • f) (not_not.mp hX) m hY,
        moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S M f (not_not.mp hX) m hY,
        smul_zero]

/-- The component of extension by zero on a natural transformation. -/
def moduleExtensionByZeroNatTransApp
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (α : M ⟶ N) (X : C) :
    moduleExtensionByZeroObj (k := k) C S M X ⟶
      moduleExtensionByZeroObj (k := k) C S N X :=
  ModuleCat.ofHom
    { toFun := fun m hX ↦
        (α.app (survivingObj (k := k) C S hX.down)).hom (m hX)
      map_add' := by
        intro m n
        funext hX
        simp
      map_smul' := by
        intro r m
        funext hX
        simp }

@[simp]
theorem moduleExtensionByZeroNatTransApp_apply
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (α : M ⟶ N) (X : C)
    (m : moduleExtensionByZeroObj (k := k) C S M X)
    (hX : PLift (X ∉ S)) :
    (moduleExtensionByZeroNatTransApp (k := k) C S α X).hom m hX =
      (α.app (survivingObj (k := k) C S hX.down)).hom (m hX) := by
  change (α.app (survivingObj (k := k) C S hX.down)).hom (m hX) = _
  rfl

/-- Extension by zero of a natural transformation. -/
def moduleExtensionByZeroNatTrans
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (α : M ⟶ N) :
    moduleExtensionByZero (k := k) C S M ⟶
      moduleExtensionByZero (k := k) C S N where
  app X := moduleExtensionByZeroNatTransApp (k := k) C S α X
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change moduleExtensionByZeroObj (k := k) C S M X at m
    apply funext
    intro hY
    by_cases hX : X ∉ S
    · have hnat := congrArg (fun q ↦ q.hom (m ⟨hX⟩))
          (α.naturality (survivingMap (k := k) C S hX hY.down f))
      change (moduleExtensionByZeroNatTransApp (k := k) C S α Y).hom
          ((moduleExtensionByZeroMap (k := k) C S M f).hom m) hY =
        (moduleExtensionByZeroMap (k := k) C S N f).hom
          ((moduleExtensionByZeroNatTransApp (k := k) C S α X).hom m) hY
      rw [moduleExtensionByZeroNatTransApp_apply,
        moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S M f hX m hY,
        moduleExtensionByZeroMap_apply_of_not_mem
          (k := k) C S N f hX _ hY,
        moduleExtensionByZeroNatTransApp_apply]
      exact hnat
    · change (moduleExtensionByZeroNatTransApp (k := k) C S α Y).hom
          ((moduleExtensionByZeroMap (k := k) C S M f).hom m) hY =
        (moduleExtensionByZeroMap (k := k) C S N f).hom
          ((moduleExtensionByZeroNatTransApp (k := k) C S α X).hom m) hY
      rw [moduleExtensionByZeroNatTransApp_apply,
        moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S M f (not_not.mp hX) m hY,
        map_zero,
        moduleExtensionByZeroMap_apply_of_mem
          (k := k) C S N f (not_not.mp hX) _ hY]

/-- Evaluation at a surviving object also intertwines extended natural
transformations with their original components. -/
theorem moduleExtensionByZeroObjIso_naturality
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (α : M ⟶ N) {X : C} (hX : X ∉ S) :
    (moduleExtensionByZeroNatTrans (k := k) C S α).app X ≫
        (moduleExtensionByZeroObjIso (k := k) C S N hX).hom =
      (moduleExtensionByZeroObjIso (k := k) C S M hX).hom ≫
        α.app (survivingObj (k := k) C S hX) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (moduleExtensionByZeroObjIso (k := k) C S N hX).hom.hom
      ((moduleExtensionByZeroNatTransApp (k := k) C S α X).hom m) =
    (α.app (survivingObj (k := k) C S hX)).hom
      ((moduleExtensionByZeroObjIso (k := k) C S M hX).hom.hom m)
  rw [moduleExtensionByZeroObjIso_hom_apply,
    moduleExtensionByZeroNatTransApp_apply,
    moduleExtensionByZeroObjIso_hom_apply]

/-- Conjugating an ambient morphism between two extensions by the surviving
evaluation isomorphisms recovers a morphism between the original values. -/
def moduleExtensionByZeroConjugateApp
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (β : moduleExtensionByZero (k := k) C S M ⟶
      moduleExtensionByZero (k := k) C S N)
    {X : C} (hX : X ∉ S) :
    M.obj (survivingObj (k := k) C S hX) ⟶
      N.obj (survivingObj (k := k) C S hX) :=
  (moduleExtensionByZeroObjIso (k := k) C S M hX).inv ≫
    β.app X ≫
    (moduleExtensionByZeroObjIso (k := k) C S N hX).hom

/-- The conjugated components of an ambient natural transformation are
natural for every morphism between surviving ambient objects. -/
theorem moduleExtensionByZeroConjugateApp_naturality
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (β : moduleExtensionByZero (k := k) C S M ⟶
      moduleExtensionByZero (k := k) C S N)
    {X Y : C} (hX : X ∉ S) (hY : Y ∉ S) (f : X ⟶ Y) :
    M.map (survivingMap (k := k) C S hX hY f) ≫
        moduleExtensionByZeroConjugateApp (k := k) C S β hY =
      moduleExtensionByZeroConjugateApp (k := k) C S β hX ≫
        N.map (survivingMap (k := k) C S hX hY f) := by
  have hMapM :
      moduleExtensionByZeroMap (k := k) C S M f ≫
          (moduleExtensionByZeroObjIso (k := k) C S M hY).hom =
        (moduleExtensionByZeroObjIso (k := k) C S M hX).hom ≫
          M.map (survivingMap (k := k) C S hX hY f) := by
    simpa only [moduleExtensionByZero] using
      moduleExtensionByZeroObjIso_map (k := k) C S M hX hY f
  have hMapN :
      moduleExtensionByZeroMap (k := k) C S N f ≫
          (moduleExtensionByZeroObjIso (k := k) C S N hY).hom =
        (moduleExtensionByZeroObjIso (k := k) C S N hX).hom ≫
          N.map (survivingMap (k := k) C S hX hY f) := by
    simpa only [moduleExtensionByZero] using
      moduleExtensionByZeroObjIso_map (k := k) C S N hX hY f
  have hβ :
      moduleExtensionByZeroMap (k := k) C S M f ≫ β.app Y =
        β.app X ≫ moduleExtensionByZeroMap (k := k) C S N f := by
    simpa only [moduleExtensionByZero] using β.naturality f
  have hM :
      M.map (survivingMap (k := k) C S hX hY f) ≫
          (moduleExtensionByZeroObjIso (k := k) C S M hY).inv =
        (moduleExtensionByZeroObjIso (k := k) C S M hX).inv ≫
          moduleExtensionByZeroMap (k := k) C S M f := by
    apply (Iso.comp_inv_eq
      (moduleExtensionByZeroObjIso (k := k) C S M hY)).2
    rw [Category.assoc]
    apply (Iso.eq_inv_comp
      (moduleExtensionByZeroObjIso (k := k) C S M hX)).2
    exact hMapM.symm
  have hTail :
      moduleExtensionByZeroMap (k := k) C S M f ≫
          (β.app Y ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hY).hom) =
        (β.app X ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hX).hom) ≫
          N.map (survivingMap (k := k) C S hX hY f) := by
    calc
      moduleExtensionByZeroMap (k := k) C S M f ≫
          (β.app Y ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hY).hom) =
          (moduleExtensionByZeroMap (k := k) C S M f ≫ β.app Y) ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hY).hom :=
        (Category.assoc _ _ _).symm
      _ = (β.app X ≫ moduleExtensionByZeroMap (k := k) C S N f) ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hY).hom := by
        exact congrArg (fun q ↦ q ≫
          (moduleExtensionByZeroObjIso (k := k) C S N hY).hom) hβ
      _ = β.app X ≫
          (moduleExtensionByZeroMap (k := k) C S N f ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hY).hom) :=
        Category.assoc _ _ _
      _ = β.app X ≫
          ((moduleExtensionByZeroObjIso (k := k) C S N hX).hom ≫
            N.map (survivingMap (k := k) C S hX hY f)) := by
        exact congrArg (fun q ↦ β.app X ≫ q) hMapN
      _ = (β.app X ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hX).hom) ≫
          N.map (survivingMap (k := k) C S hX hY f) :=
        (Category.assoc _ _ _).symm
  unfold moduleExtensionByZeroConjugateApp
  calc
    M.map (survivingMap (k := k) C S hX hY f) ≫
        ((moduleExtensionByZeroObjIso (k := k) C S M hY).inv ≫
          β.app Y ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hY).hom) =
      (M.map (survivingMap (k := k) C S hX hY f) ≫
          (moduleExtensionByZeroObjIso (k := k) C S M hY).inv) ≫
        (β.app Y ≫
          (moduleExtensionByZeroObjIso (k := k) C S N hY).hom) :=
      (Category.assoc _ _ _).symm
    _ = ((moduleExtensionByZeroObjIso (k := k) C S M hX).inv ≫
          moduleExtensionByZeroMap (k := k) C S M f) ≫
        (β.app Y ≫
          (moduleExtensionByZeroObjIso (k := k) C S N hY).hom) := by
      rw [hM]
    _ = (moduleExtensionByZeroObjIso (k := k) C S M hX).inv ≫
        (moduleExtensionByZeroMap (k := k) C S M f ≫
          (β.app Y ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hY).hom)) :=
      Category.assoc _ _ _
    _ = (moduleExtensionByZeroObjIso (k := k) C S M hX).inv ≫
        ((β.app X ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hX).hom) ≫
          N.map (survivingMap (k := k) C S hX hY f)) := by
      exact congrArg (fun q ↦
        (moduleExtensionByZeroObjIso (k := k) C S M hX).inv ≫ q) hTail
    _ = ((moduleExtensionByZeroObjIso (k := k) C S M hX).inv ≫
          β.app X ≫
            (moduleExtensionByZeroObjIso (k := k) C S N hX).hom) ≫
        N.map (survivingMap (k := k) C S hX hY f) := by
      simp only [Category.assoc]

/-- Restrict an ambient morphism between two extensions back to the deletion
category.  The object is first moved to its canonical surviving
representative, where the ambient component can be conjugated by evaluation,
and then moved back. -/
def moduleExtensionByZeroPreimageApp
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (β : moduleExtensionByZero (k := k) C S M ⟶
      moduleExtensionByZero (k := k) C S N)
    (X : DeletionCategory (k := k) C S) :
    M.obj X ⟶ N.obj X :=
  M.map (survivingObjIso (k := k) C S X).inv ≫
    moduleExtensionByZeroConjugateApp (k := k) C S β X.property ≫
    N.map (survivingObjIso (k := k) C S X).hom

@[simp]
theorem moduleExtensionByZeroPreimageApp_survivingObj
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (β : moduleExtensionByZero (k := k) C S M ⟶
      moduleExtensionByZero (k := k) C S N)
    {X : C} (hX : X ∉ S) :
    moduleExtensionByZeroPreimageApp (k := k) C S β
        (survivingObj (k := k) C S hX) =
      moduleExtensionByZeroConjugateApp (k := k) C S β hX := by
  simp only [moduleExtensionByZeroPreimageApp,
    survivingObjIso_survivingObj, Iso.refl_inv, Iso.refl_hom]
  change M.map (𝟙 (survivingObj (k := k) C S hX)) ≫
      moduleExtensionByZeroConjugateApp (k := k) C S β hX ≫
        N.map (𝟙 (survivingObj (k := k) C S hX)) =
    moduleExtensionByZeroConjugateApp (k := k) C S β hX
  simp

/-- Restriction of an ambient morphism between extensions is natural on the
object-deletion category. -/
def moduleExtensionByZeroPreimage
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (β : moduleExtensionByZero (k := k) C S M ⟶
      moduleExtensionByZero (k := k) C S N) :
    M ⟶ N where
  app X := moduleExtensionByZeroPreimageApp (k := k) C S β X
  naturality := by
    intro X Y f
    let eX := survivingObjIso (k := k) C S X
    let eY := survivingObjIso (k := k) C S Y
    let q : survivingObj (k := k) C S X.property ⟶
        survivingObj (k := k) C S Y.property :=
      eX.hom ≫ f ≫ eY.inv
    obtain ⟨g, hg⟩ := (rawFunctor (k := k) C S).map_surjective q.hom
    have hq : survivingMap (k := k) C S X.property Y.property g = q := by
      apply ObjectProperty.hom_ext
      exact hg
    have hnat := moduleExtensionByZeroConjugateApp_naturality
      (k := k) C S β X.property Y.property g
    rw [hq] at hnat
    apply (cancel_epi (M.mapIso eX).hom).1
    apply (cancel_mono (N.mapIso eY).inv).1
    simpa only [moduleExtensionByZeroPreimageApp, eX, eY, q,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
      ← M.map_comp, ← N.map_comp, ← M.map_comp_assoc, ← N.map_comp_assoc,
      Iso.hom_inv_id, Iso.inv_hom_id,
      M.map_id, N.map_id, Category.id_comp, Category.comp_id] using hnat

theorem moduleExtensionByZeroNatTrans_id
    (M : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k) [M.Additive] :
    moduleExtensionByZeroNatTrans (k := k) C S (𝟙 M) =
      𝟙 (moduleExtensionByZero (k := k) C S M) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change moduleExtensionByZeroObj (k := k) C S M X at m
  apply funext
  intro hX
  change (moduleExtensionByZeroNatTransApp (k := k) C S (𝟙 M) X).hom m hX = m hX
  rw [moduleExtensionByZeroNatTransApp_apply]
  rfl

theorem moduleExtensionByZeroNatTrans_comp
    {M N P : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive] [P.Additive]
    (α : M ⟶ N) (β : N ⟶ P) :
    moduleExtensionByZeroNatTrans (k := k) C S (α ≫ β) =
      moduleExtensionByZeroNatTrans (k := k) C S α ≫
        moduleExtensionByZeroNatTrans (k := k) C S β := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change moduleExtensionByZeroObj (k := k) C S M X at m
  apply funext
  intro hX
  change (moduleExtensionByZeroNatTransApp (k := k) C S (α ≫ β) X).hom m hX =
    ((moduleExtensionByZeroNatTransApp (k := k) C S α X) ≫
      moduleExtensionByZeroNatTransApp (k := k) C S β X).hom m hX
  rw [moduleExtensionByZeroNatTransApp_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, moduleExtensionByZeroNatTransApp_apply,
    moduleExtensionByZeroNatTransApp_apply]
  rfl

theorem moduleExtensionByZeroNatTrans_add
    {M N : DeletionCategory (k := k) C S ⥤ ModuleCat.{uM} k}
    [M.Additive] [N.Additive]
    (α β : M ⟶ N) :
    moduleExtensionByZeroNatTrans (k := k) C S (α + β) =
      moduleExtensionByZeroNatTrans (k := k) C S α +
        moduleExtensionByZeroNatTrans (k := k) C S β := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change moduleExtensionByZeroObj (k := k) C S M X at m
  apply funext
  intro hX
  change (moduleExtensionByZeroNatTransApp (k := k) C S (α + β) X).hom m hX =
    (moduleExtensionByZeroNatTransApp (k := k) C S α X +
      moduleExtensionByZeroNatTransApp (k := k) C S β X).hom m hX
  rw [moduleExtensionByZeroNatTransApp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, Pi.add_apply, moduleExtensionByZeroNatTransApp_apply,
    moduleExtensionByZeroNatTransApp_apply]
  rfl

/-- Extension by zero restricts to linear modules. -/
def linearModuleExtensionByZero :
    LinearModuleCategory.{u, v, w, uM}
        (C := DeletionCategory (k := k) C S) k ⥤
      LinearModuleCategory.{u, v, w, uM} (C := C) k where
  obj M := ⟨moduleExtensionByZero (k := k) C S M.obj,
    ⟨inferInstance, inferInstance⟩⟩
  map α := ObjectProperty.homMk
    (moduleExtensionByZeroNatTrans (k := k) C S α.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact moduleExtensionByZeroNatTrans_id (k := k) C S M.obj
  map_comp α β := by
    apply ObjectProperty.hom_ext
    exact moduleExtensionByZeroNatTrans_comp
      (k := k) C S α.hom β.hom

noncomputable instance linearModuleExtensionByZero_additive :
    (linearModuleExtensionByZero (k := k) C S).Additive := by
  constructor
  intro M N α β
  apply ObjectProperty.hom_ext
  exact moduleExtensionByZeroNatTrans_add (k := k) C S α.hom β.hom

noncomputable instance linearModuleExtensionByZero_faithful :
    (linearModuleExtensionByZero (k := k) C S).Faithful where
  map_injective {M N} := by
    intro α β hαβ
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    let eX := survivingObjIso (k := k) C S X
    have hmap :
        (moduleExtensionByZeroNatTrans (k := k) C S α.hom).app X.obj.as =
          (moduleExtensionByZeroNatTrans (k := k) C S β.hom).app X.obj.as := by
      exact congrArg (fun q ↦ q.hom.app X.obj.as) hαβ
    have hsurv :
        α.hom.app (survivingObj (k := k) C S X.property) =
          β.hom.app (survivingObj (k := k) C S X.property) := by
      apply (cancel_epi
        (moduleExtensionByZeroObjIso (k := k) C S M.obj X.property).hom).1
      rw [← moduleExtensionByZeroObjIso_naturality
          (k := k) C S α.hom X.property,
        ← moduleExtensionByZeroObjIso_naturality
          (k := k) C S β.hom X.property,
        hmap]
    apply (cancel_epi (M.obj.mapIso eX).hom).1
    rw [Functor.mapIso_hom]
    change M.obj.map (survivingObjIso (k := k) C S X).hom ≫ α.hom.app X =
      M.obj.map (survivingObjIso (k := k) C S X).hom ≫ β.hom.app X
    rw [α.hom.naturality, β.hom.naturality, hsurv]

noncomputable instance linearModuleExtensionByZero_full :
    (linearModuleExtensionByZero (k := k) C S).Full where
  map_surjective {M N} β := by
    let α : M ⟶ N := ObjectProperty.homMk
      (moduleExtensionByZeroPreimage (k := k) C S β.hom)
    refine ⟨α, ?_⟩
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    by_cases hX : X ∈ S
    · exact (moduleExtensionByZero_obj_isZero_of_mem
        (k := k) C S M.obj hX).eq_of_src _ _
    · apply (cancel_mono
        (moduleExtensionByZeroObjIso (k := k) C S N.obj hX).hom).1
      change (moduleExtensionByZeroNatTrans (k := k) C S α.hom).app X ≫
          (moduleExtensionByZeroObjIso (k := k) C S N.obj hX).hom =
        β.hom.app X ≫
          (moduleExtensionByZeroObjIso (k := k) C S N.obj hX).hom
      rw [moduleExtensionByZeroObjIso_naturality
        (k := k) C S α.hom hX]
      change (moduleExtensionByZeroObjIso (k := k) C S M.obj hX).hom ≫
          moduleExtensionByZeroPreimageApp (k := k) C S β.hom
            (survivingObj (k := k) C S hX) =
        β.hom.app X ≫
          (moduleExtensionByZeroObjIso (k := k) C S N.obj hX).hom
      rw [moduleExtensionByZeroPreimageApp_survivingObj]
      unfold moduleExtensionByZeroConjugateApp
      simp only [Iso.hom_inv_id_assoc]
      rfl

/-- The support of an extended module is contained in the image of the
original support under the surviving-object inclusion. -/
theorem moduleSupport_moduleExtensionByZero_subset
    (M : LinearModuleCategory.{u, v, w, uM}
      (C := DeletionCategory (k := k) C S) k) :
    MagnitudeConjecture.CoveringHom.moduleSupport k
        (moduleExtensionByZero (k := k) C S M.obj) ⊆
      (fun X : DeletionCategory (k := k) C S ↦ X.obj.as) ''
        MagnitudeConjecture.CoveringHom.moduleSupport k M.obj := by
  intro X hnontrivial
  by_cases hXS : X ∈ S
  · have hzero := moduleExtensionByZero_obj_isZero_of_mem
      (k := k) C S M.obj hXS
    letI : Subsingleton
        ((moduleExtensionByZero (k := k) C S M.obj).obj X) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact (not_nontrivial _ hnontrivial).elim
  · let Y := survivingObj (k := k) C S hXS
    refine ⟨Y, ?_, rfl⟩
    change Nontrivial (M.obj.obj Y)
    by_contra htrivial
    letI : Subsingleton (M.obj.obj Y) :=
      not_nontrivial_iff_subsingleton.mp htrivial
    haveI : Subsingleton
        ((moduleExtensionByZero (k := k) C S M.obj).obj X) :=
      ⟨fun m n ↦ by
        change ((h : PLift (X ∉ S)) →
          M.obj.obj (survivingObj (k := k) C S h.down)) at m n
        funext h
        exact Subsingleton.elim (m h) (n h)⟩
    exact not_nontrivial _ hnontrivial

/-- A support point of a deletion-stage module remains a support point after
extension by zero, at its underlying ambient object. -/
theorem mem_moduleSupport_moduleExtensionByZero_of_mem
    (M : LinearModuleCategory.{u, v, w, uM}
      (C := DeletionCategory (k := k) C S) k)
    (X : DeletionCategory (k := k) C S)
    (hX : X ∈ MagnitudeConjecture.CoveringHom.moduleSupport k M.obj) :
    X.obj.as ∈ MagnitudeConjecture.CoveringHom.moduleSupport k
      (moduleExtensionByZero (k := k) C S M.obj) := by
  exact (moduleExtensionByZeroObjIsoAt (k := k) C S M.obj X).toLinearEquiv.toEquiv.nontrivial_congr.mpr
    hX

/-- Extension by zero preserves pointwise finite dimension and finite object
support. -/
theorem linearModuleExtensionByZero_isFiniteDimensional
    (M : LinearModuleCategory.{u, v, w, uM}
      (C := DeletionCategory (k := k) C S) k)
    (hM : MagnitudeConjecture.CoveringHom.IsFiniteDimensionalModule
      (C := DeletionCategory (k := k) C S) k M) :
    MagnitudeConjecture.CoveringHom.IsFiniteDimensionalModule (C := C) k
      ((linearModuleExtensionByZero (k := k) C S).obj M) := by
  constructor
  · intro X
    change FiniteDimensional k
      ((hX : PLift (X ∉ S)) →
        M.obj.obj (survivingObj (k := k) C S hX.down))
    by_cases hXS : X ∈ S
    · letI : Subsingleton
          ((hX : PLift (X ∉ S)) →
            M.obj.obj (survivingObj (k := k) C S hX.down)) :=
        ⟨fun m n ↦ by
          funext h
          exact (h.down hXS).elim⟩
      infer_instance
    · letI : Unique (PLift (X ∉ S)) :=
        { default := PLift.up hXS
          uniq := fun _ ↦ Subsingleton.elim _ _ }
      letI : FiniteDimensional k
          (M.obj.obj (survivingObj (k := k) C S
            (default : PLift (X ∉ S)).down)) :=
        hM.1 (survivingObj (k := k) C S
          (default : PLift (X ∉ S)).down)
      exact (LinearEquiv.piUnique k
        (fun hX : PLift (X ∉ S) ↦
          M.obj.obj (survivingObj (k := k) C S hX.down))).symm.finiteDimensional
  · apply hM.2.image (fun X : DeletionCategory (k := k) C S ↦ X.obj.as) |>.subset
    exact moduleSupport_moduleExtensionByZero_subset (k := k) C S M

/-- Extension by zero restricts to finite-dimensional modules with finite
object support. -/
def finiteDimensionalModuleExtensionByZero :
    MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory.{u, v, w, uM}
        (C := DeletionCategory (k := k) C S) k ⥤
      MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory.{u, v, w, uM}
        (C := C) k where
  obj M := ⟨(linearModuleExtensionByZero (k := k) C S).obj M.obj,
    linearModuleExtensionByZero_isFiniteDimensional
      (k := k) C S M.obj M.property⟩
  map α := ObjectProperty.homMk
    ((linearModuleExtensionByZero (k := k) C S).map α.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact (linearModuleExtensionByZero (k := k) C S).map_id M.obj
  map_comp α β := by
    apply ObjectProperty.hom_ext
    exact (linearModuleExtensionByZero (k := k) C S).map_comp α.hom β.hom

noncomputable instance finiteDimensionalModuleExtensionByZero_additive :
    (finiteDimensionalModuleExtensionByZero (k := k) C S).Additive := by
  constructor
  intro M N α β
  apply ObjectProperty.hom_ext
  exact (linearModuleExtensionByZero (k := k) C S).map_add

noncomputable instance finiteDimensionalModuleExtensionByZero_faithful :
    (finiteDimensionalModuleExtensionByZero (k := k) C S).Faithful where
  map_injective {M N} := by
    intro α β hαβ
    apply ObjectProperty.hom_ext
    apply (linearModuleExtensionByZero (k := k) C S).map_injective
    exact congrArg (fun q ↦ q.hom) hαβ

noncomputable instance finiteDimensionalModuleExtensionByZero_full :
    (finiteDimensionalModuleExtensionByZero (k := k) C S).Full where
  map_surjective {M N} β := by
    obtain ⟨α, hα⟩ :=
      (linearModuleExtensionByZero (k := k) C S).map_surjective β.hom
    refine ⟨ObjectProperty.homMk α, ?_⟩
    apply ObjectProperty.hom_ext
    exact hα

/-- A finite-dimensional indecomposable module remains indecomposable after
extension by zero to the ambient category. -/
theorem finiteDimensionalModuleExtensionByZero_indec
    (M :
      MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory.{u, v, w, uM}
        (C := DeletionCategory (k := k) C S) k)
    (hM : Indecomposable M) :
    Indecomposable
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M) := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  letI : IsLocalRing (End M) :=
    MagnitudeConjecture.CoveringHom.finiteDimensionalModule_end_isLocalRing
      k M hM
  letI : IsLocalRing (End (F.obj M)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (CategoryTheory.Functor.endRingEquivOfFullyFaithful F M)
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end
    (F.obj M)

/-- Extension by zero identifies indecomposability of finite-dimensional
modules on the deletion category with indecomposability of their ambient
extensions. -/
theorem finiteDimensionalModuleExtensionByZero_indec_iff
    (M :
      MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory.{u, v, w, uM}
        (C := DeletionCategory (k := k) C S) k) :
    Indecomposable
        ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M) ↔
      Indecomposable M := by
  constructor
  · exact
      MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
        (finiteDimensionalModuleExtensionByZero (k := k) C S) M
  · exact finiteDimensionalModuleExtensionByZero_indec (k := k) C S M

end MagnitudeConjecture.ObjectDeletion
