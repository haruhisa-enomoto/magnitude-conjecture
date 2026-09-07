import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleInheritance

/-!
# Adjoint module truncations for object deletion

For a set `S` of deleted objects, ambient modules vanishing on `S` form the
essential image of extension by zero.  This file constructs the two adjoints
to their inclusion.  The right adjoint takes the largest submodule vanishing
on `S`; the left adjoint takes the largest quotient vanishing on `S`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable (S : Set C)

/-- At `X`, the elements of an ambient module killed by every map from `X`
to a deleted object. -/
def maximalVanishingSubmoduleObj
    (M : C ⥤ ModuleCat.{v} k) (X : C) : Submodule k (M.obj X) where
  carrier := {x | ∀ (Y : C), Y ∈ S → ∀ (f : X ⟶ Y), M.map f x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy Z hZ f
    rw [map_add, hx Z hZ f, hy Z hZ f, add_zero]
  smul_mem' := by
    intro a x hx Z hZ f
    rw [map_smul, hx Z hZ f, smul_zero]

/-- A module map carries maximal vanishing submodules into one another. -/
def maximalVanishingSubmoduleNatMap
    {M N : C ⥤ ModuleCat.{v} k} (a : M ⟶ N) (X : C) :
    maximalVanishingSubmoduleObj (k := k) C S M X →ₗ[k]
      maximalVanishingSubmoduleObj (k := k) C S N X where
  toFun x := ⟨a.app X x.1, by
    intro Y hY f
    change (N.map f).hom (a.app X x.1) = 0
    rw [← ModuleCat.comp_apply, ← a.naturality]
    change a.app Y (M.map f x.1) = 0
    rw [x.2 Y hY f, map_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    exact (a.app X).hom.map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (a.app X).hom.map_smul r x.1

/-- The maximal submodule of `M` which vanishes on all deleted objects. -/
def maximalVanishingSubmodule
    (M : C ⥤ ModuleCat.{v} k) : C ⥤ ModuleCat.{v} k where
  obj X := ModuleCat.of k (maximalVanishingSubmoduleObj (k := k) C S M X)
  map {X Y} f := ModuleCat.ofHom {
    toFun := fun x ↦ ⟨M.map f x.1, by
      intro Z hZ g
      change (M.map g).hom (M.map f x.1) = 0
      rw [← ModuleCat.comp_apply, ← M.map_comp]
      exact x.2 Z hZ (f ≫ g)⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact (M.map f).hom.map_add x.1 y.1
    map_smul' := by
      intro r x
      apply Subtype.ext
      exact (M.map f).hom.map_smul r x.1 }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (M.map (𝟙 X)).hom x.1 = x.1
    rw [M.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (M.map (f ≫ g)).hom x.1 =
      (M.map g).hom ((M.map f).hom x.1)
    rw [M.map_comp, ModuleCat.comp_apply]

/-- The maximal vanishing submodule includes naturally into the ambient
module. -/
def maximalVanishingSubmoduleInclusion
    (M : C ⥤ ModuleCat.{v} k) :
    maximalVanishingSubmodule (k := k) C S M ⟶ M where
  app X := ModuleCat.ofHom
    (maximalVanishingSubmoduleObj (k := k) C S M X).subtype
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance maximalVanishingSubmoduleInclusion_mono
    (M : C ⥤ ModuleCat.{v} k) :
    Mono (maximalVanishingSubmoduleInclusion (k := k) C S M) := by
  haveI hmonoApp (X : C) : Mono
      ((maximalVanishingSubmoduleInclusion (k := k) C S M).app X) := by
    rw [ModuleCat.mono_iff_injective]
    exact (maximalVanishingSubmoduleObj
      (k := k) C S M X).subtype_injective
  exact NatTrans.mono_of_mono_app _

/-- The maximal vanishing submodule is additive. -/
instance maximalVanishingSubmodule_additive
    (M : C ⥤ ModuleCat.{v} k) [M.Additive] :
    (maximalVanishingSubmodule (k := k) C S M).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (M.map (f + g)).hom x.1 =
      ((M.map f) + (M.map g)).hom x.1
    rw [M.map_add]

/-- The maximal vanishing submodule is linear. -/
instance maximalVanishingSubmodule_linear
    (M : C ⥤ ModuleCat.{v} k) [M.Linear k] :
    (maximalVanishingSubmodule (k := k) C S M).Linear k where
  map_smul := by
    intro X Y f a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (M.map (a • f)).hom x.1 =
      (a • M.map f).hom x.1
    rw [M.map_smul]

/-- A morphism of ambient modules restricts to their maximal vanishing
submodules. -/
def maximalVanishingSubmoduleMap
    {M N : C ⥤ ModuleCat.{v} k} (a : M ⟶ N) :
    maximalVanishingSubmodule (k := k) C S M ⟶
      maximalVanishingSubmodule (k := k) C S N where
  app X := ModuleCat.ofHom
    (maximalVanishingSubmoduleNatMap (k := k) C S a X)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (a.app Y).hom ((M.map f).hom x.1) =
      (N.map f).hom ((a.app X).hom x.1)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      a.naturality]

omit [Preadditive C] [Linear k C] in
@[simp]
theorem maximalVanishingSubmoduleMap_comp_inclusion
    {M N : C ⥤ ModuleCat.{v} k} (a : M ⟶ N) :
    maximalVanishingSubmoduleMap (k := k) C S a ≫
        maximalVanishingSubmoduleInclusion (k := k) C S N =
      maximalVanishingSubmoduleInclusion (k := k) C S M ≫ a := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The maximal-vanishing-submodule construction is functorial on ambient
module-valued functors. -/
def maximalVanishingSubmoduleFunctor :
    (C ⥤ ModuleCat.{v} k) ⥤ (C ⥤ ModuleCat.{v} k) where
  obj M := maximalVanishingSubmodule (k := k) C S M
  map a := maximalVanishingSubmoduleMap (k := k) C S a
  map_id M := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp a b := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- The maximal-vanishing-submodule inclusions form a natural transformation
to the identity functor. -/
def maximalVanishingSubmoduleInclusionNatTrans :
    maximalVanishingSubmoduleFunctor (k := k) C S ⟶
      𝟭 (C ⥤ ModuleCat.{v} k) where
  app M := maximalVanishingSubmoduleInclusion (k := k) C S M
  naturality := by
    intro M N a
    change maximalVanishingSubmoduleMap (k := k) C S a ≫
        maximalVanishingSubmoduleInclusion (k := k) C S N =
      maximalVanishingSubmoduleInclusion (k := k) C S M ≫ a
    exact maximalVanishingSubmoduleMap_comp_inclusion (k := k) C S a

omit [Preadditive C] [Linear k C] in
/-- The maximal vanishing submodule does vanish at every deleted object. -/
theorem maximalVanishingSubmodule_vanishesOnDeleted
    (M : C ⥤ ModuleCat.{v} k) :
    ModuleVanishesOnDeleted (k := k) C S
      (maximalVanishingSubmodule (k := k) C S M) := by
  intro X hX
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro x y
  apply Subtype.ext
  have hx := x.2 X hX (𝟙 X)
  have hy := y.2 X hX (𝟙 X)
  change (M.map (𝟙 X)).hom x.1 = 0 at hx
  change (M.map (𝟙 X)).hom y.1 = 0 at hy
  rw [M.map_id] at hx hy
  exact hx.trans hy.symm

/-- Every map from a module vanishing on the deleted objects factors through
the maximal vanishing submodule of its target. -/
def maximalVanishingSubmoduleLift
    {E M : C ⥤ ModuleCat.{v} k}
    (hE : ModuleVanishesOnDeleted (k := k) C S E)
    (a : E ⟶ M) :
    E ⟶ maximalVanishingSubmodule (k := k) C S M where
  app X := ModuleCat.ofHom {
    toFun := fun x ↦ ⟨a.app X x, by
      intro Y hY f
      change (M.map f).hom (a.app X x) = 0
      rw [← ModuleCat.comp_apply, ← a.naturality]
      have hf : E.map f = 0 := (hE Y hY).eq_of_tgt _ _
      rw [hf, zero_comp]
      rfl⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact (a.app X).hom.map_add x y
    map_smul' := by
      intro r x
      apply Subtype.ext
      exact (a.app X).hom.map_smul r x }
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (a.app Y).hom ((E.map f).hom x) =
      (M.map f).hom ((a.app X).hom x)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      a.naturality]

omit [Preadditive C] [Linear k C] in
@[simp]
theorem maximalVanishingSubmoduleLift_comp_inclusion
    {E M : C ⥤ ModuleCat.{v} k}
    (hE : ModuleVanishesOnDeleted (k := k) C S E)
    (a : E ⟶ M) :
    maximalVanishingSubmoduleLift (k := k) C S hE a ≫
        maximalVanishingSubmoduleInclusion (k := k) C S M = a := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Preadditive C] [Linear k C] in
/-- Factorization through the maximal vanishing submodule is unique. -/
theorem maximalVanishingSubmoduleLift_unique
    {E M : C ⥤ ModuleCat.{v} k}
    (hE : ModuleVanishesOnDeleted (k := k) C S E)
    (a : E ⟶ M)
    (b : E ⟶ maximalVanishingSubmodule (k := k) C S M)
    (hb : b ≫ maximalVanishingSubmoduleInclusion (k := k) C S M = a) :
    b = maximalVanishingSubmoduleLift (k := k) C S hE a := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hbX := congrArg (fun q ↦ q.app X) hb
  have hbApply := congrFun
    (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom hbX)) x
  exact hbApply

/-- The maximal vanishing submodule of a linear module, bundled as a linear
module. -/
def linearMaximalVanishingSubmodule
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) :
    LinearModuleCategory.{u, v, v, v} (C := C) k :=
  ⟨maximalVanishingSubmodule (k := k) C S M.obj,
    ⟨inferInstance, inferInstance⟩⟩

/-- Taking the maximal vanishing submodule preserves pointwise finite
dimension and finite object support. -/
theorem linearMaximalVanishingSubmodule_isFiniteDimensional
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    IsFiniteDimensionalModule (C := C) k
      (linearMaximalVanishingSubmodule (k := k) C S M.obj) := by
  constructor
  · intro X
    exact FiniteDimensional.of_injective
      (maximalVanishingSubmoduleObj
        (k := k) C S M.obj.obj X).subtype
      (maximalVanishingSubmoduleObj
        (k := k) C S M.obj.obj X).subtype_injective
  · refine M.property.2.subset ?_
    intro X hX
    change Nontrivial
      (maximalVanishingSubmoduleObj (k := k) C S M.obj.obj X) at hX
    letI : Nontrivial
        (maximalVanishingSubmoduleObj (k := k) C S M.obj.obj X) := hX
    exact (maximalVanishingSubmoduleObj
      (k := k) C S M.obj.obj X).subtype_injective.nontrivial

/-- The maximal vanishing submodule of a finite-dimensional module. -/
def finiteMaximalVanishingSubmodule
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  ⟨linearMaximalVanishingSubmodule (k := k) C S M.obj,
    linearMaximalVanishingSubmodule_isFiniteDimensional
      (k := k) C S M⟩

/-- The full category of ambient finite-dimensional modules vanishing on the
deleted objects. -/
abbrev VanishingFiniteModuleCategory :=
  (finiteModuleVanishesOnDeleted (k := k) C S).FullSubcategory

/-- The maximal vanishing submodule, bundled in the vanishing full
subcategory. -/
def finiteMaximalVanishingSubmoduleObj
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    VanishingFiniteModuleCategory (k := k) C S :=
  ⟨finiteMaximalVanishingSubmodule (k := k) C S M,
    maximalVanishingSubmodule_vanishesOnDeleted
      (k := k) C S M.obj.obj⟩

/-- The maximal-vanishing-submodule construction as a functor from ambient
finite modules to the vanishing full subcategory. -/
def finiteMaximalVanishingSubmoduleFunctor :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ⥤
      VanishingFiniteModuleCategory (k := k) C S where
  obj M := finiteMaximalVanishingSubmoduleObj (k := k) C S M
  map a := ObjectProperty.homMk <| ObjectProperty.homMk <|
    ObjectProperty.homMk <|
      maximalVanishingSubmoduleMap (k := k) C S a.hom.hom
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (maximalVanishingSubmoduleFunctor (k := k) C S).map_id M.obj.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (maximalVanishingSubmoduleFunctor (k := k) C S).map_comp
      a.hom.hom b.hom.hom

/-- The maximal vanishing submodule includes into its ambient module. -/
def finiteMaximalVanishingSubmoduleInclusion
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (finiteModuleVanishesOnDeleted (k := k) C S).ι.obj
        ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj M) ⟶
      M :=
  ObjectProperty.homMk <| ObjectProperty.homMk <|
    maximalVanishingSubmoduleInclusion (k := k) C S M.obj.obj

instance finiteMaximalVanishingSubmoduleInclusion_mono
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Mono (finiteMaximalVanishingSubmoduleInclusion (k := k) C S M) := by
  let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C) k).ι
  let K := (IsLinearModule.{u, v, v, v} (C := C) k).ι
  haveI : Mono (K.map
      (J.map (finiteMaximalVanishingSubmoduleInclusion
        (k := k) C S M))) := by
    change Mono (maximalVanishingSubmoduleInclusion
      (k := k) C S M.obj.obj)
    infer_instance
  haveI : Mono (J.map (finiteMaximalVanishingSubmoduleInclusion
      (k := k) C S M)) :=
    K.mono_of_mono_map
      (show Mono (K.map
        (J.map (finiteMaximalVanishingSubmoduleInclusion
          (k := k) C S M))) from inferInstance)
  exact J.mono_of_mono_map
    (show Mono (J.map (finiteMaximalVanishingSubmoduleInclusion
      (k := k) C S M)) from inferInstance)

/-- A morphism from a vanishing finite module to an ambient module lifts to
the maximal vanishing submodule of its target. -/
def finiteMaximalVanishingSubmoduleLift
    {E : VanishingFiniteModuleCategory (k := k) C S}
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (a : E.obj ⟶ M) :
    E ⟶ (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj M :=
  ObjectProperty.homMk <| ObjectProperty.homMk <|
    ObjectProperty.homMk <|
      maximalVanishingSubmoduleLift (k := k) C S E.property a.hom.hom

@[simp]
theorem finiteMaximalVanishingSubmoduleLift_comp_inclusion
    {E : VanishingFiniteModuleCategory (k := k) C S}
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (a : E.obj ⟶ M) :
    (finiteMaximalVanishingSubmoduleLift (k := k) C S a).hom ≫
        finiteMaximalVanishingSubmoduleInclusion (k := k) C S M = a := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact maximalVanishingSubmoduleLift_comp_inclusion
    (k := k) C S E.property a.hom.hom

/-- If an ambient finite module already vanishes on the deleted objects, its
maximal vanishing submodule is the whole module. -/
theorem finiteMaximalVanishingSubmoduleInclusion_isIso_of_vanishesOnDeleted
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : ModuleVanishesOnDeleted (k := k) C S M.obj.obj) :
    IsIso (finiteMaximalVanishingSubmoduleInclusion (k := k) C S M) := by
  let E : VanishingFiniteModuleCategory (k := k) C S := ⟨M, hM⟩
  let a : E.obj ⟶ M := 𝟙 M
  let r : M ⟶
      (finiteModuleVanishesOnDeleted (k := k) C S).ι.obj
        ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj M) :=
    (finiteMaximalVanishingSubmoduleLift (k := k) C S a).hom
  have hri : r ≫
      finiteMaximalVanishingSubmoduleInclusion (k := k) C S M = 𝟙 M := by
    change (finiteMaximalVanishingSubmoduleLift
      (k := k) C S a).hom ≫
        finiteMaximalVanishingSubmoduleInclusion (k := k) C S M = a
    exact finiteMaximalVanishingSubmoduleLift_comp_inclusion
      (k := k) C S a
  apply IsIso.mk
  refine ⟨r, ?_, hri⟩
  apply (cancel_mono
    (finiteMaximalVanishingSubmoduleInclusion (k := k) C S M)).1
  simp only [Category.assoc, hri, Category.comp_id, Category.id_comp]

/-- Universal Hom equivalence for the maximal vanishing submodule. -/
def finiteMaximalVanishingSubmoduleHomEquiv
    (E : VanishingFiniteModuleCategory (k := k) C S)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    ((finiteModuleVanishesOnDeleted (k := k) C S).ι.obj E ⟶ M) ≃
      (E ⟶ (finiteMaximalVanishingSubmoduleFunctor
        (k := k) C S).obj M) where
  toFun a := finiteMaximalVanishingSubmoduleLift (k := k) C S a
  invFun b := b.hom ≫
    finiteMaximalVanishingSubmoduleInclusion (k := k) C S M
  left_inv a := finiteMaximalVanishingSubmoduleLift_comp_inclusion
    (k := k) C S a
  right_inv b := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- Inclusion of the vanishing full subcategory is left adjoint to the
maximal-vanishing-submodule functor. -/
def finiteMaximalVanishingSubmoduleAdjunction :
    (finiteModuleVanishesOnDeleted (k := k) C S).ι ⊣
      finiteMaximalVanishingSubmoduleFunctor (k := k) C S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := finiteMaximalVanishingSubmoduleHomEquiv
        (k := k) C S
      homEquiv_naturality_left_symm := by
        intro E' E M f g
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl
      homEquiv_naturality_right := by
        intro E M N f g
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        rfl }

/-- At `X`, the trace generated by all maps from deleted objects into `X`. -/
def deletedTraceSubmoduleObj
    (M : C ⥤ ModuleCat.{v} k) (X : C) : Submodule k (M.obj X) :=
  ⨆ (Y : C) (_ : Y ∈ S) (f : Y ⟶ X), LinearMap.range (M.map f).hom

omit [Preadditive C] [Linear k C] in
/-- The deleted trace is preserved by the structure maps of the module. -/
theorem deletedTraceSubmoduleObj_map_le
    (M : C ⥤ ModuleCat.{v} k) {X Z : C} (h : X ⟶ Z) :
    deletedTraceSubmoduleObj (k := k) C S M X ≤
      (deletedTraceSubmoduleObj (k := k) C S M Z).comap (M.map h).hom := by
  refine iSup_le fun Y ↦ iSup_le fun hY ↦ iSup_le fun f ↦ ?_
  rintro x ⟨y, rfl⟩
  change (M.map h).hom ((M.map f).hom y) ∈
    deletedTraceSubmoduleObj (k := k) C S M Z
  rw [← ModuleCat.comp_apply, ← M.map_comp]
  exact Submodule.mem_iSup_of_mem Y <|
    Submodule.mem_iSup_of_mem hY <|
      Submodule.mem_iSup_of_mem (f ≫ h) ⟨y, rfl⟩

/-- The largest quotient of `M` which vanishes on all deleted objects. -/
def maximalVanishingQuotient
    (M : C ⥤ ModuleCat.{v} k) : C ⥤ ModuleCat.{v} k where
  obj X := ModuleCat.of k
    (M.obj X ⧸ deletedTraceSubmoduleObj (k := k) C S M X)
  map {X Z} h := ModuleCat.ofHom <|
    Submodule.mapQ
      (deletedTraceSubmoduleObj (k := k) C S M X)
      (deletedTraceSubmoduleObj (k := k) C S M Z)
      (M.map h).hom
      (deletedTraceSubmoduleObj_map_le (k := k) C S M h)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp [Submodule.mapQ_apply, M.map_comp]

/-- The ambient module projects naturally onto its maximal vanishing
quotient. -/
def maximalVanishingQuotientProjection
    (M : C ⥤ ModuleCat.{v} k) :
    M ⟶ maximalVanishingQuotient (k := k) C S M where
  app X := ModuleCat.ofHom
    (deletedTraceSubmoduleObj (k := k) C S M X).mkQ
  naturality := by
    intro X Z h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance maximalVanishingQuotientProjection_epi
    (M : C ⥤ ModuleCat.{v} k) :
    Epi (maximalVanishingQuotientProjection (k := k) C S M) := by
  haveI hepiApp (X : C) : Epi
      ((maximalVanishingQuotientProjection (k := k) C S M).app X) := by
    rw [ModuleCat.epi_iff_surjective]
    exact (deletedTraceSubmoduleObj (k := k) C S M X).mkQ_surjective
  exact NatTrans.epi_of_epi_app _

/-- The maximal vanishing quotient is additive. -/
instance maximalVanishingQuotient_additive
    (M : C ⥤ ModuleCat.{v} k) [M.Additive] :
    (maximalVanishingQuotient (k := k) C S M).Additive where
  map_add := by
    intro X Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (deletedTraceSubmoduleObj (k := k) C S M Z).mkQ
          ((M.map (f + g)).hom x) =
        (deletedTraceSubmoduleObj (k := k) C S M Z).mkQ
            ((M.map f).hom x) +
          (deletedTraceSubmoduleObj (k := k) C S M Z).mkQ
            ((M.map g).hom x)
      rw [M.map_add]
      rfl

/-- The maximal vanishing quotient is linear. -/
instance maximalVanishingQuotient_linear
    (M : C ⥤ ModuleCat.{v} k) [M.Linear k] :
    (maximalVanishingQuotient (k := k) C S M).Linear k where
  map_smul := by
    intro X Z f a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (deletedTraceSubmoduleObj (k := k) C S M Z).mkQ
          ((M.map (a • f)).hom x) =
        a • (deletedTraceSubmoduleObj (k := k) C S M Z).mkQ
          ((M.map f).hom x)
      rw [M.map_smul]
      rfl

omit [Preadditive C] [Linear k C] in
/-- At a deleted object, the deleted trace is the whole module. -/
theorem deletedTraceSubmoduleObj_eq_top_of_mem
    (M : C ⥤ ModuleCat.{v} k) {X : C} (hX : X ∈ S) :
    deletedTraceSubmoduleObj (k := k) C S M X = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ LinearMap.range (M.map (𝟙 X)).hom := by
    refine ⟨x, ?_⟩
    rw [M.map_id]
    rfl
  exact Submodule.mem_iSup_of_mem X <|
    Submodule.mem_iSup_of_mem hX <|
      Submodule.mem_iSup_of_mem (𝟙 X) hx

omit [Preadditive C] [Linear k C] in
/-- The maximal vanishing quotient vanishes at every deleted object. -/
theorem maximalVanishingQuotient_vanishesOnDeleted
    (M : C ⥤ ModuleCat.{v} k) :
    ModuleVanishesOnDeleted (k := k) C S
      (maximalVanishingQuotient (k := k) C S M) := by
  intro X hX
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton
    (M.obj X ⧸ deletedTraceSubmoduleObj (k := k) C S M X)
  rw [Submodule.Quotient.subsingleton_iff,
    deletedTraceSubmoduleObj_eq_top_of_mem (k := k) C S M hX]

omit [Preadditive C] [Linear k C] in
/-- Every map from an ambient module to a module vanishing on the deleted
objects kills the deleted trace. -/
theorem deletedTraceSubmoduleObj_le_ker
    {M E : C ⥤ ModuleCat.{v} k}
    (hE : ModuleVanishesOnDeleted (k := k) C S E)
    (a : M ⟶ E) (X : C) :
    deletedTraceSubmoduleObj (k := k) C S M X ≤
      LinearMap.ker (a.app X).hom := by
  refine iSup_le fun Y ↦ iSup_le fun hY ↦ iSup_le fun f ↦ ?_
  rintro x ⟨y, rfl⟩
  change (a.app X).hom ((M.map f).hom y) = 0
  rw [← ModuleCat.comp_apply, a.naturality]
  have haY : a.app Y = 0 := (hE Y hY).eq_of_tgt _ _
  rw [haY, zero_comp]
  rfl

/-- Every map from an ambient module to a module vanishing on the deleted
objects descends through the maximal vanishing quotient. -/
def maximalVanishingQuotientDescend
    {M E : C ⥤ ModuleCat.{v} k}
    (hE : ModuleVanishesOnDeleted (k := k) C S E)
    (a : M ⟶ E) :
    maximalVanishingQuotient (k := k) C S M ⟶ E where
  app X := ModuleCat.ofHom <|
    (deletedTraceSubmoduleObj (k := k) C S M X).liftQ
      (a.app X).hom
      (deletedTraceSubmoduleObj_le_ker (k := k) C S hE a X)
  naturality := by
    intro X Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (a.app Z).hom ((M.map f).hom x) =
        (E.map f).hom ((a.app X).hom x)
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
        a.naturality]

omit [Preadditive C] [Linear k C] in
@[simp]
theorem projection_comp_maximalVanishingQuotientDescend
    {M E : C ⥤ ModuleCat.{v} k}
    (hE : ModuleVanishesOnDeleted (k := k) C S E)
    (a : M ⟶ E) :
    maximalVanishingQuotientProjection (k := k) C S M ≫
        maximalVanishingQuotientDescend (k := k) C S hE a = a := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Preadditive C] [Linear k C] in
/-- Descent through the maximal vanishing quotient is unique. -/
theorem maximalVanishingQuotientDescend_unique
    {M E : C ⥤ ModuleCat.{v} k}
    (hE : ModuleVanishesOnDeleted (k := k) C S E)
    (a : M ⟶ E)
    (b : maximalVanishingQuotient (k := k) C S M ⟶ E)
    (hb : maximalVanishingQuotientProjection (k := k) C S M ≫ b = a) :
    b = maximalVanishingQuotientDescend (k := k) C S hE a := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    have hbX := congrArg (fun q ↦ q.app X) hb
    have hbApply := congrFun
      (congrArg DFunLike.coe (congrArg ModuleCat.Hom.hom hbX)) x
    exact hbApply

/-- A morphism of ambient modules descends to their maximal vanishing
quotients. -/
def maximalVanishingQuotientMap
    {M N : C ⥤ ModuleCat.{v} k} (a : M ⟶ N) :
    maximalVanishingQuotient (k := k) C S M ⟶
      maximalVanishingQuotient (k := k) C S N :=
  maximalVanishingQuotientDescend (k := k) C S
    (maximalVanishingQuotient_vanishesOnDeleted (k := k) C S N)
    (a ≫ maximalVanishingQuotientProjection (k := k) C S N)

omit [Preadditive C] [Linear k C] in
@[simp]
theorem projection_comp_maximalVanishingQuotientMap
    {M N : C ⥤ ModuleCat.{v} k} (a : M ⟶ N) :
    maximalVanishingQuotientProjection (k := k) C S M ≫
        maximalVanishingQuotientMap (k := k) C S a =
      a ≫ maximalVanishingQuotientProjection (k := k) C S N :=
  projection_comp_maximalVanishingQuotientDescend
    (k := k) C S
    (maximalVanishingQuotient_vanishesOnDeleted (k := k) C S N)
    (a ≫ maximalVanishingQuotientProjection (k := k) C S N)

/-- The maximal-vanishing-quotient construction is functorial on ambient
module-valued functors. -/
def maximalVanishingQuotientFunctor :
    (C ⥤ ModuleCat.{v} k) ⥤ (C ⥤ ModuleCat.{v} k) where
  obj M := maximalVanishingQuotient (k := k) C S M
  map a := maximalVanishingQuotientMap (k := k) C S a
  map_id M := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp a b := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- The quotient projections form a natural transformation from the identity
functor. -/
def maximalVanishingQuotientProjectionNatTrans :
    𝟭 (C ⥤ ModuleCat.{v} k) ⟶
      maximalVanishingQuotientFunctor (k := k) C S where
  app M := maximalVanishingQuotientProjection (k := k) C S M
  naturality := by
    intro M N a
    exact projection_comp_maximalVanishingQuotientMap (k := k) C S a

/-- The maximal vanishing quotient of a linear module, bundled as a linear
module. -/
def linearMaximalVanishingQuotient
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) :
    LinearModuleCategory.{u, v, v, v} (C := C) k :=
  ⟨maximalVanishingQuotient (k := k) C S M.obj,
    ⟨inferInstance, inferInstance⟩⟩

/-- Taking the maximal vanishing quotient preserves pointwise finite
dimension and finite object support. -/
theorem linearMaximalVanishingQuotient_isFiniteDimensional
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    IsFiniteDimensionalModule (C := C) k
      (linearMaximalVanishingQuotient (k := k) C S M.obj) := by
  constructor
  · intro X
    exact Module.Finite.of_surjective
      (deletedTraceSubmoduleObj (k := k) C S M.obj.obj X).mkQ
      (deletedTraceSubmoduleObj (k := k) C S M.obj.obj X).mkQ_surjective
  · refine M.property.2.subset ?_
    intro X hX
    change Nontrivial
      ((M.obj.obj).obj X ⧸
        deletedTraceSubmoduleObj (k := k) C S M.obj.obj X) at hX
    letI : Nontrivial
        ((M.obj.obj).obj X ⧸
          deletedTraceSubmoduleObj (k := k) C S M.obj.obj X) := hX
    exact (deletedTraceSubmoduleObj
      (k := k) C S M.obj.obj X).mkQ_surjective.nontrivial

/-- The maximal vanishing quotient of a finite-dimensional module. -/
def finiteMaximalVanishingQuotient
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  ⟨linearMaximalVanishingQuotient (k := k) C S M.obj,
    linearMaximalVanishingQuotient_isFiniteDimensional (k := k) C S M⟩

/-- The maximal vanishing quotient, bundled in the vanishing full
subcategory. -/
def finiteMaximalVanishingQuotientObj
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    VanishingFiniteModuleCategory (k := k) C S :=
  ⟨finiteMaximalVanishingQuotient (k := k) C S M,
    maximalVanishingQuotient_vanishesOnDeleted (k := k) C S M.obj.obj⟩

/-- The maximal-vanishing-quotient construction as a functor from ambient
finite modules to the vanishing full subcategory. -/
def finiteMaximalVanishingQuotientFunctor :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ⥤
      VanishingFiniteModuleCategory (k := k) C S where
  obj M := finiteMaximalVanishingQuotientObj (k := k) C S M
  map a := ObjectProperty.homMk <| ObjectProperty.homMk <|
    ObjectProperty.homMk <|
      maximalVanishingQuotientMap (k := k) C S a.hom.hom
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (maximalVanishingQuotientFunctor (k := k) C S).map_id M.obj.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (maximalVanishingQuotientFunctor (k := k) C S).map_comp
      a.hom.hom b.hom.hom

/-- The ambient finite module projects onto its maximal vanishing quotient. -/
def finiteMaximalVanishingQuotientProjection
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    M ⟶ (finiteModuleVanishesOnDeleted (k := k) C S).ι.obj
      ((finiteMaximalVanishingQuotientFunctor (k := k) C S).obj M) :=
  ObjectProperty.homMk <| ObjectProperty.homMk <|
    maximalVanishingQuotientProjection (k := k) C S M.obj.obj

instance finiteMaximalVanishingQuotientProjection_epi
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Epi (finiteMaximalVanishingQuotientProjection (k := k) C S M) := by
  let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C) k).ι
  let K := (IsLinearModule.{u, v, v, v} (C := C) k).ι
  haveI : Epi (K.map
      (J.map (finiteMaximalVanishingQuotientProjection
        (k := k) C S M))) := by
    change Epi (maximalVanishingQuotientProjection
      (k := k) C S M.obj.obj)
    infer_instance
  haveI : Epi (J.map (finiteMaximalVanishingQuotientProjection
      (k := k) C S M)) :=
    K.epi_of_epi_map
      (show Epi (K.map
        (J.map (finiteMaximalVanishingQuotientProjection
          (k := k) C S M))) from inferInstance)
  exact J.epi_of_epi_map
    (show Epi (J.map (finiteMaximalVanishingQuotientProjection
      (k := k) C S M)) from inferInstance)

/-- A morphism from an ambient finite module to a vanishing finite module
descends through the maximal vanishing quotient. -/
def finiteMaximalVanishingQuotientDescend
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {E : VanishingFiniteModuleCategory (k := k) C S}
    (a : M ⟶ E.obj) :
    (finiteMaximalVanishingQuotientFunctor (k := k) C S).obj M ⟶ E :=
  ObjectProperty.homMk <| ObjectProperty.homMk <|
    ObjectProperty.homMk <|
      maximalVanishingQuotientDescend (k := k) C S E.property a.hom.hom

@[simp]
theorem projection_comp_finiteMaximalVanishingQuotientDescend
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {E : VanishingFiniteModuleCategory (k := k) C S}
    (a : M ⟶ E.obj) :
    finiteMaximalVanishingQuotientProjection (k := k) C S M ≫
        (finiteMaximalVanishingQuotientDescend (k := k) C S a).hom = a := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact projection_comp_maximalVanishingQuotientDescend
    (k := k) C S E.property a.hom.hom

/-- Universal Hom equivalence for the maximal vanishing quotient. -/
def finiteMaximalVanishingQuotientHomEquiv
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (E : VanishingFiniteModuleCategory (k := k) C S) :
    ((finiteMaximalVanishingQuotientFunctor (k := k) C S).obj M ⟶ E) ≃
      (M ⟶ (finiteModuleVanishesOnDeleted (k := k) C S).ι.obj E) where
  toFun b := finiteMaximalVanishingQuotientProjection (k := k) C S M ≫ b.hom
  invFun a := finiteMaximalVanishingQuotientDescend (k := k) C S a
  left_inv b := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  right_inv a := projection_comp_finiteMaximalVanishingQuotientDescend
    (k := k) C S a

/-- The maximal-vanishing-quotient functor is left adjoint to inclusion of
the vanishing full subcategory. -/
def finiteMaximalVanishingQuotientAdjunction :
    finiteMaximalVanishingQuotientFunctor (k := k) C S ⊣
      (finiteModuleVanishesOnDeleted (k := k) C S).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := finiteMaximalVanishingQuotientHomEquiv (k := k) C S
      homEquiv_naturality_left_symm := by
        intro M' M E f g
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        rintro x
        induction x using Submodule.Quotient.induction_on with
        | _ x => rfl
      homEquiv_naturality_right := by
        intro M E E' f g
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl }

end MagnitudeConjecture.ObjectDeletion
