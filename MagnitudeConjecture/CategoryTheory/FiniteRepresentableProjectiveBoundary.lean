import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.FiniteNeighborhoodAlmostSplit
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The projective boundary of the finite functor category

For an object with local endomorphism ring, the categorical radical
`rad(X,-)` is a linear subfunctor of the covariant representable `Hom(X,-)`.
When the representable is finite, its inclusion is the canonical right
almost-split morphism ending at that indecomposable projective.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- The covariant categorical-radical subfunctor of a representable. -/
noncomputable def radicalLinearCoyoneda (X : C) : C ⥤ ModuleCat.{v} k where
  obj Y := ModuleCat.of k
    (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Y)
  map {Y Z} f := ModuleCat.ofHom
    { toFun := fun q ↦
        ⟨q.1 ≫ f, isRadicalMorphism_postcomp f q.2⟩
      map_add' := by
        intro q r
        apply Subtype.ext
        change (q.1 + r.1) ≫ f = q.1 ≫ f + r.1 ≫ f
        simp
      map_smul' := by
        intro a q
        apply Subtype.ext
        change (a • q.1) ≫ f = a • (q.1 ≫ f)
        simp }
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    simp [Category.assoc]

instance radicalLinearCoyoneda_additive (X : C) :
    (radicalLinearCoyoneda (k := k) X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change
      (⟨q.1 ≫ (f + g), by
          exact isRadicalMorphism_postcomp (f + g) q.2⟩ :
        MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Z) =
      ⟨q.1 ≫ f + q.1 ≫ g, by
          exact (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule
            k X Z).add_mem
            (isRadicalMorphism_postcomp f q.2)
            (isRadicalMorphism_postcomp g q.2)⟩
    apply Subtype.ext
    simp

instance radicalLinearCoyoneda_linear (X : C) :
    (radicalLinearCoyoneda (k := k) X).Linear k where
  map_smul := by
    intro Y Z f a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change
      (⟨q.1 ≫ (a • f), by
          exact isRadicalMorphism_postcomp (a • f) q.2⟩ :
        MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Z) =
      ⟨a • (q.1 ≫ f), by
          exact (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule
            k X Z).smul_mem a
            (isRadicalMorphism_postcomp f q.2)⟩
    apply Subtype.ext
    simp

/-- The radical representable bundled as an additive linear module. -/
noncomputable def radicalLinearCoyonedaLinearModule (X : C) :
    LinearModuleCategory (C := C) k :=
  ⟨radicalLinearCoyoneda (k := k) X, inferInstance, inferInstance⟩

/-- The canonical inclusion `rad(X,-) ⟶ Hom(X,-)` as an ordinary natural
transformation. -/
noncomputable def radicalLinearCoyonedaInclusionNatTrans (X : C) :
    radicalLinearCoyoneda (k := k) X ⟶
      (linearCoyoneda k C).obj (Opposite.op X) where
  app Y := ModuleCat.ofHom
    (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Y).subtype
  naturality := by
    intro Y Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    rfl

/-- Precomposition by an isomorphism transports the radical Hom subspace. -/
def radicalLinearCoyonedaSourceEquiv (Y : C) {X Z : C} (e : X ≅ Z) :
    MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Y ≃ₗ[k]
      MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k Z Y where
  toFun f := ⟨e.inv ≫ f.1, isRadicalMorphism_precomp e.inv f.2⟩
  invFun f := ⟨e.hom ≫ f.1, isRadicalMorphism_precomp e.hom f.2⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv f := by apply Subtype.ext; simp
  map_add' f g := by apply Subtype.ext; simp
  map_smul' r f := by apply Subtype.ext; simp

@[simp]
theorem radicalLinearCoyonedaSourceEquiv_apply_val
    (Y : C) {X Z : C} (e : X ≅ Z)
    (f : MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Y) :
    ((radicalLinearCoyonedaSourceEquiv (k := k) Y e) f).1 =
      e.inv ≫ f.1 :=
  rfl

@[simp]
theorem radicalLinearCoyoneda_map_apply_val
    (X : C) {Y Z : C} (f : Y ⟶ Z)
    (q : MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Y) :
    ((radicalLinearCoyoneda (k := k) X).map f q).1 = q.1 ≫ f :=
  rfl

/-- An isomorphism of representing objects transports their radical
representables by precomposition. -/
noncomputable def radicalLinearCoyonedaMapIso {X Z : C} (e : X ≅ Z) :
    radicalLinearCoyoneda (k := k) X ≅
      radicalLinearCoyoneda (k := k) Z := by
  refine NatIso.ofComponents (fun Y ↦
    (radicalLinearCoyonedaSourceEquiv (k := k) Y e).toModuleIso) ?_
  intro Y W f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  apply Subtype.ext
  change
    ((radicalLinearCoyonedaSourceEquiv (k := k) W e)
      ((radicalLinearCoyoneda (k := k) X).map f q)).1 =
    ((radicalLinearCoyonedaSourceEquiv (k := k) Y e) q).1 ≫ f
  simp [Category.assoc]

/-- Transport of a radical representable along a representing-object
isomorphism commutes with its inclusion into the full representable. -/
theorem radicalLinearCoyonedaMapIso_hom_comp_inclusion
    {X Z : C} (e : X ≅ Z) :
    (radicalLinearCoyonedaMapIso (k := k) e).hom ≫
        radicalLinearCoyonedaInclusionNatTrans (k := k) Z =
      radicalLinearCoyonedaInclusionNatTrans (k := k) X ≫
        ((linearCoyoneda k C).mapIso e.symm.op).hom := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  rfl

/-- The canonical inclusion `rad(X,-) ⟶ Hom(X,-)`, bundled in the category
of additive linear modules. -/
noncomputable def radicalLinearCoyonedaInclusion (X : C) :
    radicalLinearCoyonedaLinearModule (k := k) X ⟶
      linearCoyonedaLinearModule (k := k) X :=
  ObjectProperty.homMk (radicalLinearCoyonedaInclusionNatTrans (k := k) X)

instance radicalLinearCoyonedaInclusion_mono (X : C) :
    Mono (radicalLinearCoyonedaInclusion (k := k) X) := by
  let J := (IsLinearModule (C := C) k).ι
  haveI hmonoApp (Y : C) : Mono
      ((J.map (radicalLinearCoyonedaInclusion (k := k) X)).app Y) := by
    rw [ModuleCat.mono_iff_injective]
    exact (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule
      k X Y).subtype_injective
  haveI : Mono (J.map (radicalLinearCoyonedaInclusion (k := k) X)) :=
    NatTrans.mono_of_mono_app _
  exact J.mono_of_mono_map
    (show Mono (J.map (radicalLinearCoyonedaInclusion (k := k) X)) from
      inferInstance)

/-- The radical subfunctor of a finite representable is again a finite
module. -/
theorem radicalLinearCoyoneda_isFiniteDimensionalModule
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    IsFiniteDimensionalModule (C := C) k
      (radicalLinearCoyonedaLinearModule (k := k) X) := by
  constructor
  · intro Y
    letI : FiniteDimensional k (X ⟶ Y) := hX.1 Y
    exact FiniteDimensional.of_injective
      (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Y).subtype
      (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule
        k X Y).subtype_injective
  · apply hX.2.subset
    intro Y hY
    letI : Nontrivial
        (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X Y) := hY
    exact (MagnitudeConjecture.CategoryTheory.radicalHomSubmodule
      k X Y).subtype_injective.nontrivial

/-- The finite categorical radical of a finite representable. -/
noncomputable def finiteDimensionalLinearCoyonedaRadical
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  ⟨radicalLinearCoyonedaLinearModule (k := k) X,
    radicalLinearCoyoneda_isFiniteDimensionalModule X hX⟩

/-- The finite radical inclusion into a finite representable. -/
noncomputable def finiteDimensionalLinearCoyonedaRadicalInclusion
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    finiteDimensionalLinearCoyonedaRadical (k := k) X hX ⟶
      finiteDimensionalLinearCoyoneda (k := k) X hX :=
  ObjectProperty.homMk (radicalLinearCoyonedaInclusion (k := k) X)

instance finiteDimensionalLinearCoyonedaRadicalInclusion_mono
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    Mono (finiteDimensionalLinearCoyonedaRadicalInclusion (k := k) X hX) := by
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  haveI : Mono
      (J.map (finiteDimensionalLinearCoyonedaRadicalInclusion
        (k := k) X hX)) := by
    change Mono (radicalLinearCoyonedaInclusion (k := k) X)
    infer_instance
  exact J.mono_of_mono_map
    (show Mono
      (J.map (finiteDimensionalLinearCoyonedaRadicalInclusion
        (k := k) X hX)) from inferInstance)

/-- A nonsplit map into a representable has pointwise radical image. -/
private theorem map_into_representable_mem_radical
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (X Y : C)
    (N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (g : N ⟶ finiteDimensionalLinearCoyoneda (k := k) X (hP X))
    (hg : ¬ IsSplitEpi g) (y : N.obj.obj.obj Y) :
    IsRadicalMorphism (g.hom.hom.app Y y) := by
  letI : IsLocalRing (End X) := hlocal X
  have hXzero : ¬ IsZero X := by
    intro hzero
    apply (zero_ne_one : (0 : End X) ≠ 1)
    change (0 : X ⟶ X) = 𝟙 X
    exact hzero.eq_of_src _ _
  rw [MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
    (X := X) (Y := Y) hXzero]
  intro hsplit
  letI : IsSplitMono (g.hom.hom.app Y y) := hsplit
  let r : Y ⟶ X := retraction (g.hom.hom.app Y y)
  let x : N.obj.obj.obj X := N.obj.obj.map r y
  let s : finiteDimensionalLinearCoyoneda (k := k) X (hP X) ⟶ N :=
    ObjectProperty.homMk (linearCoyonedaHom N.obj X x)
  have hx : g.hom.hom.app X x = 𝟙 X := by
    have hn := ConcreteCategory.congr_hom (g.hom.hom.naturality r) y
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hn
    change g.hom.hom.app X (N.obj.obj.map r y) =
      (g.hom.hom.app Y y) ≫ r at hn
    exact hn.trans (IsSplitMono.id (g.hom.hom.app Y y))
  apply hg
  apply IsSplitEpi.mk'
  exact
    { section_ := s
      id := by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext Z
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        change g.hom.hom.app Z (N.obj.obj.map q x) = q
        have hn := ConcreteCategory.congr_hom
          (g.hom.hom.naturality q) x
        rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hn
        change g.hom.hom.app Z (N.obj.obj.map q x) =
          (g.hom.hom.app X x) ≫ q at hn
        simpa [hx] using hn }

/-- The radical inclusion of an indecomposable finite representable is right
almost split. -/
theorem finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    IsRightAlmostSplit
      (finiteDimensionalLinearCoyonedaRadicalInclusion
        (k := k) X (hP X)) := by
  constructor
  · intro hsplit
    letI : IsSplitEpi
        (finiteDimensionalLinearCoyonedaRadicalInclusion
          (k := k) X (hP X)) := hsplit
    let inc := finiteDimensionalLinearCoyonedaRadicalInclusion
      (k := k) X (hP X)
    let q : MagnitudeConjecture.CategoryTheory.radicalHomSubmodule k X X :=
      (section_ inc).hom.hom.app X (𝟙 X)
    have hidRad : IsRadicalMorphism (𝟙 X) := by
      have hs := congrArg
        (fun t : finiteDimensionalLinearCoyoneda (k := k) X (hP X) ⟶
            finiteDimensionalLinearCoyoneda (k := k) X (hP X) ↦
          t.hom.hom.app X (𝟙 X)) (IsSplitEpi.id inc)
      have hq : q.1 = 𝟙 X := hs
      exact hq ▸ q.2
    letI : IsLocalRing (End X) := hlocal X
    have hXzero : ¬ IsZero X := by
      intro hzero
      apply (zero_ne_one : (0 : End X) ≠ 1)
      change (0 : X ⟶ X) = 𝟙 X
      exact hzero.eq_of_src _ _
    exact
      (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
        (X := X) (Y := X) hXzero (𝟙 X)).mp hidRad inferInstance
  · intro N g hg
    let hLinear : N.obj ⟶ radicalLinearCoyonedaLinearModule (k := k) X :=
      ObjectProperty.homMk
        { app := fun Y ↦ ModuleCat.ofHom
            { toFun := fun y ↦
                ⟨g.hom.hom.app Y y,
                  map_into_representable_mem_radical hP hlocal X Y N g hg y⟩
              map_add' := by
                intro y z
                apply Subtype.ext
                exact map_add (g.hom.hom.app Y).hom y z
              map_smul' := by
                intro a y
                apply Subtype.ext
                exact map_smul (g.hom.hom.app Y).hom a y }
          naturality := by
            intro Y Z f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro y
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (g.hom.hom.naturality f) y }
    let h : N ⟶ finiteDimensionalLinearCoyonedaRadical (k := k) X (hP X) :=
      ObjectProperty.homMk hLinear
    refine ⟨h, ?_⟩
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext Y
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    dsimp [h, hLinear, finiteDimensionalLinearCoyonedaRadicalInclusion,
      radicalLinearCoyonedaInclusion]
    rfl

end MagnitudeConjecture.CoveringHom
