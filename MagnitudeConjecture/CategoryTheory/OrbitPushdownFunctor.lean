import MagnitudeConjecture.CategoryTheory.OrbitPushdown
import MagnitudeConjecture.CategoryTheory.LinearModuleDeckShift

/-!
# Gabriel push-down as a functor on linear modules

The objectwise direct-sum module constructed in `OrbitPushdown` is natural
in the upstairs module. This file sends a module natural transformation
diagonally across the translated summands, proves naturality for arbitrary
orbit morphisms, and bundles the construction as an additive linear functor
between linear-module categories.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

variable {M N P : C ⥤ ModuleCat.{uM} k}
variable [M.Additive] [M.Linear k]
variable [N.Additive] [N.Linear k]
variable [P.Additive] [P.Linear k]

/-- A module natural transformation acts diagonally on the translated
summands of push-down. -/
noncomputable def orbitPushdownNatTransAppLinear
    (α : M ⟶ N) (X : C) :
    orbitPushdownValue (A := A) M X →ₗ[k]
      orbitPushdownValue (A := A) N X := by
  classical
  exact DirectSum.toModule k A _ fun b ↦
    (orbitPushdownLof N X b).comp (α.app ((shiftFunctor C b).obj X)).hom

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] [N.Additive] [N.Linear k] in
@[simp]
theorem orbitPushdownNatTransAppLinear_lof
    (α : M ⟶ N) (X : C) (b : A)
    (x : M.obj ((shiftFunctor C b).obj X)) :
    orbitPushdownNatTransAppLinear (A := A) α X
        (orbitPushdownLof M X b x) =
      orbitPushdownLof N X b
        (α.app ((shiftFunctor C b).obj X) x) := by
  classical
  simp [orbitPushdownNatTransAppLinear, orbitPushdownLof]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] [N.Additive] [N.Linear k] in
/-- Diagonal action of a module map commutes with every homogeneous
push-down morphism. -/
theorem orbitPushdownNatTransAppLinear_naturality_homogeneous
    (α : M ⟶ N) {X Y : C} (a : A) (f : ShiftHom X Y a) :
    (orbitPushdownNatTransAppLinear (A := A) α Y).comp
        (orbitPushdownHomogeneousMap M a f) =
      (orbitPushdownHomogeneousMap N a f).comp
        (orbitPushdownNatTransAppLinear (A := A) α X) := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change orbitPushdownNatTransAppLinear (A := A) α Y
      (orbitPushdownHomogeneousMap M a f
        (orbitPushdownLof M X b x)) =
    orbitPushdownHomogeneousMap N a f
      (orbitPushdownNatTransAppLinear (A := A) α X
        (orbitPushdownLof M X b x))
  rw [orbitPushdownHomogeneousMap_lof,
    orbitPushdownNatTransAppLinear_lof,
    orbitPushdownNatTransAppLinear_lof,
    orbitPushdownHomogeneousMap_lof]
  change DirectSum.of
      (fun e ↦ N.obj ((shiftFunctor C e).obj Y)) (a + b)
        (α.app ((shiftFunctor C (a + b)).obj Y)
          (orbitPushdownComponent M a b f x)) =
    DirectSum.of (fun e ↦ N.obj ((shiftFunctor C e).obj Y)) (a + b)
      (orbitPushdownComponent N a b f
        (α.app ((shiftFunctor C b).obj X) x))
  apply congrArg (DirectSum.of
    (fun e ↦ N.obj ((shiftFunctor C e).obj Y)) (a + b))
  simpa only [orbitPushdownComponent, orbitPushdownComponent',
    ModuleCat.comp_apply] using
      congr($(α.naturality (orbitPushdownArrow' rfl f)) x)

/-- Diagonal action of a module map commutes with arbitrary finite-support
orbit morphisms. -/
theorem orbitPushdownNatTransAppLinear_naturality
    (α : M ⟶ N) {X Y : C} (f : ShiftOrbitHom A X Y) :
    (orbitPushdownNatTransAppLinear (A := A) α Y).comp
        (orbitPushdownMapLinear M f) =
      (orbitPushdownMapLinear N f).comp
        (orbitPushdownNatTransAppLinear (A := A) α X) := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · ext x
    simp
  · intro a fa
    change (orbitPushdownNatTransAppLinear (A := A) α Y).comp
        (orbitPushdownMapLinear M (shiftOrbitOf X Y a fa)) =
      (orbitPushdownMapLinear N (shiftOrbitOf X Y a fa)).comp
        (orbitPushdownNatTransAppLinear (A := A) α X)
    rw [orbitPushdownMapLinear_of, orbitPushdownMapLinear_of]
    exact orbitPushdownNatTransAppLinear_naturality_homogeneous α a fa
  · intro f g hf hg
    rw [map_add, map_add]
    apply LinearMap.ext
    intro x
    simpa using congrArg₂ (.+.) (LinearMap.congr_fun hf x)
      (LinearMap.congr_fun hg x)

/-- Push-down of a natural transformation of upstairs modules. -/
noncomputable def orbitPushdownNatTrans (α : M ⟶ N) :
    orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) N where
  app X := ModuleCat.ofHom
    (orbitPushdownNatTransAppLinear (A := A) α (show C from X))
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    change (orbitPushdownNatTransAppLinear (A := A) α (show C from Y)).comp
        (orbitPushdownMapLinear M f) =
      (orbitPushdownMapLinear N f).comp
        (orbitPushdownNatTransAppLinear (A := A) α (show C from X))
    exact orbitPushdownNatTransAppLinear_naturality α f

@[simp]
theorem orbitPushdownNatTrans_id :
    orbitPushdownNatTrans (A := A) (𝟙 M) = 𝟙 (orbitPushdown (A := A) M) := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  change orbitPushdownNatTransAppLinear (A := A) (𝟙 M) (show C from X)
      (orbitPushdownLof M (show C from X) b x) =
    orbitPushdownLof M (show C from X) b x
  rw [orbitPushdownNatTransAppLinear_lof]
  simp

@[simp]
theorem orbitPushdownNatTrans_comp (α : M ⟶ N) (β : N ⟶ P) :
    orbitPushdownNatTrans (A := A) (α ≫ β) =
      orbitPushdownNatTrans (A := A) α ≫
        orbitPushdownNatTrans (A := A) β := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  change orbitPushdownNatTransAppLinear (A := A) (α ≫ β) (show C from X)
      (orbitPushdownLof M (show C from X) b x) =
    orbitPushdownNatTransAppLinear (A := A) β (show C from X)
      (orbitPushdownNatTransAppLinear (A := A) α (show C from X)
        (orbitPushdownLof M (show C from X) b x))
  rw [orbitPushdownNatTransAppLinear_lof,
    orbitPushdownNatTransAppLinear_lof,
    orbitPushdownNatTransAppLinear_lof]
  rfl

@[simp]
theorem orbitPushdownNatTrans_add (α β : M ⟶ N) :
    orbitPushdownNatTrans (A := A) (α + β) =
      orbitPushdownNatTrans (A := A) α +
        orbitPushdownNatTrans (A := A) β := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  change orbitPushdownNatTransAppLinear (A := A) (α + β) (show C from X)
      (orbitPushdownLof M (show C from X) b x) =
    orbitPushdownNatTransAppLinear (A := A) α (show C from X)
        (orbitPushdownLof M (show C from X) b x) +
      orbitPushdownNatTransAppLinear (A := A) β (show C from X)
        (orbitPushdownLof M (show C from X) b x)
  rw [orbitPushdownNatTransAppLinear_lof,
    orbitPushdownNatTransAppLinear_lof,
    orbitPushdownNatTransAppLinear_lof]
  simp

@[simp]
theorem orbitPushdownNatTrans_smul (r : k) (α : M ⟶ N) :
    orbitPushdownNatTrans (A := A) (r • α) =
      r • orbitPushdownNatTrans (A := A) α := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  change orbitPushdownNatTransAppLinear (A := A) (r • α) (show C from X)
      (orbitPushdownLof M (show C from X) b x) =
    r • orbitPushdownNatTransAppLinear (A := A) α (show C from X)
      (orbitPushdownLof M (show C from X) b x)
  rw [orbitPushdownNatTransAppLinear_lof,
    orbitPushdownNatTransAppLinear_lof]
  simp

/-- Gabriel push-down as a functor from linear modules upstairs to linear
modules over the shift-orbit category. -/
noncomputable def linearModuleOrbitPushdown :
    LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k where
  obj M := ⟨orbitPushdown (A := A) M.obj, inferInstance, inferInstance⟩
  map {M N} α := by
    exact ObjectProperty.homMk
      (orbitPushdownNatTrans (A := A) α.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    change orbitPushdownNatTrans (A := A) (𝟙 M.obj) =
      𝟙 (orbitPushdown (A := A) M.obj)
    exact orbitPushdownNatTrans_id (A := A) (M := M.obj)
  map_comp {M N P} α β := by
    apply ObjectProperty.hom_ext
    change orbitPushdownNatTrans (A := A) (α.hom ≫ β.hom) =
      orbitPushdownNatTrans (A := A) α.hom ≫
        orbitPushdownNatTrans (A := A) β.hom
    exact orbitPushdownNatTrans_comp (A := A) α.hom β.hom

instance linearModuleOrbitPushdown_additive :
    (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).Additive where
  map_add := by
    intro M N α β
    apply ObjectProperty.hom_ext
    change orbitPushdownNatTrans (A := A) (α.hom + β.hom) =
      orbitPushdownNatTrans (A := A) α.hom +
        orbitPushdownNatTrans (A := A) β.hom
    exact orbitPushdownNatTrans_add α.hom β.hom

instance linearModuleOrbitPushdown_linear :
    (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).Linear k where
  map_smul α r := by
    apply ObjectProperty.hom_ext
    change orbitPushdownNatTrans (A := A) (r • α.hom) =
      r • orbitPushdownNatTrans (A := A) α.hom
    exact orbitPushdownNatTrans_smul r α.hom

end MagnitudeConjecture.CoveringHom
