import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Direct-sum push-down to a shift-orbit category

For a linear module `M : C ⥤ ModuleCat k`, its push-down to the
shift-orbit category has value `⨁ b, M(X⟦b⟧)` at `X`. A homogeneous
map of degree `a` sends the `b`-summand to the `(a + b)`-summand.

This file constructs that action, verifies its unit and composition laws
from Mathlib's shift coherence, and packages it as an additive linear
module over the orbit category. The construction is generic; covering-specific
finite-support hypotheses enter only when restricting its values to
finite-dimensional modules.
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

variable (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]

/-- The value of the push-down module at an object of the orbit category. -/
abbrev orbitPushdownValue (X : C) :=
  DirectSum A (fun b ↦ M.obj ((shiftFunctor C b).obj X))

/-- Inclusion of one translated value into the push-down direct sum. -/
noncomputable def orbitPushdownLof (X : C) (b : A) :
    M.obj ((shiftFunctor C b).obj X) →ₗ[k]
      orbitPushdownValue (A := A) M X := by
  classical
  exact DirectSum.lof k A
    (fun c ↦ M.obj ((shiftFunctor C c).obj X)) b

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- The push-down summand inclusion is the standard direct-sum generator. -/
theorem orbitPushdownLof_eq_directSumOf [DecidableEq A]
    (X : C) (b : A) (x : M.obj ((shiftFunctor C b).obj X)) :
    orbitPushdownLof M X b x =
      DirectSum.of
        (fun c : A ↦ M.obj ((shiftFunctor C c).obj X)) b x := by
  unfold orbitPushdownLof
  rw [DirectSum.lof_eq_of]
  have h : (fun c d : A ↦ Classical.propDecidable (c = d)) =
      (inferInstance : DecidableEq A) :=
    Subsingleton.elim _ _
  rw [h]

/-- The map from the `b`-summand induced by a homogeneous orbit morphism of
degree `a`, with an explicitly chosen output degree. -/
def orbitPushdownArrow'
    {X Y : C} {a b c : A} (h : a + b = c) (f : ShiftHom X Y a) :
    (shiftFunctor C b).obj X ⟶ (shiftFunctor C c).obj Y :=
  (shiftFunctor C b).map f ≫
    (shiftFunctorAdd' C a b c h).inv.app Y

/-- Applying the upstairs module to the component arrow. -/
def orbitPushdownComponent'
    {X Y : C} {a b c : A} (h : a + b = c) (f : ShiftHom X Y a) :
    M.obj ((shiftFunctor C b).obj X) →ₗ[k]
      M.obj ((shiftFunctor C c).obj Y) :=
  (M.map (orbitPushdownArrow' h f)).hom

/-- The component map with its canonical output degree. -/
def orbitPushdownComponent
    {X Y : C} (a b : A) (f : ShiftHom X Y a) :
    M.obj ((shiftFunctor C b).obj X) →ₗ[k]
      M.obj ((shiftFunctor C (a + b)).obj Y) :=
  orbitPushdownComponent' M rfl f

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- The canonical component map agrees heterogeneously with the component
map at any propositionally equal output degree. -/
theorem orbitPushdownComponent_apply_heq_component'_apply
    {X Y : C} {a b c : A} (h : a + b = c)
    (f : ShiftHom X Y a)
    (x : M.obj ((shiftFunctor C b).obj X)) :
    HEq (orbitPushdownComponent M a b f x)
      (orbitPushdownComponent' M h f x) := by
  subst c
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
@[simp]
theorem orbitPushdownComponent'_id
    (X : C) (b : A) :
    orbitPushdownComponent' M (zero_add b)
        (shiftHomId (A := A) X) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [orbitPushdownComponent', orbitPushdownArrow', shiftHomId,
    shiftFunctorAdd'_zero_add_inv_app]
  rw [← Functor.map_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive] in
/-- Component arrows respect homogeneous composition, including all degree
reassociations. -/
theorem orbitPushdownArrow'_comp
    {X Y Z : C} {a c b ab ca d : A}
    (hab : a + b = ab) (hca : c + a = ca)
    (hleft : ca + b = d) (hright : c + ab = d)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z c) :
    orbitPushdownArrow' hleft (shiftHomComp' hca f g) =
      orbitPushdownArrow' hab f ≫ orbitPushdownArrow' hright g := by
  have htotal : c + a + b = d := by rw [hca, hleft]
  simp only [orbitPushdownArrow', shiftHomComp', Functor.map_comp,
    Category.assoc]
  rw [shiftFunctorAdd'_assoc_inv_app c a b ca ab d hca hab htotal]
  have hn := (shiftFunctorAdd' C a b ab hab).inv.naturality_assoc g
    ((shiftFunctorAdd' C c ab d hright).inv.app Z)
  simp only [Functor.comp_map] at hn
  rw [hn]

set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous component arrow followed by the canonical path from its
target translate equals the canonical path from the source translate followed
by the original orbit morphism. -/
theorem orbitPushdownArrow_comp_fromShift
    {X Y : C} (a b : A) (f : ShiftHom X Y a) :
    shiftOrbitCompHom
        (shiftOrbitOf ((shiftFunctor C b).obj X)
          ((shiftFunctor C (a + b)).obj Y) 0
          (shiftHomZero (A := A) (orbitPushdownArrow' rfl f)))
        (shiftOrbitFromShift Y (a + b)) =
      shiftOrbitCompHom (shiftOrbitFromShift X b)
        (shiftOrbitOf X Y a f) := by
  classical
  rw [shiftOrbitFromShift, shiftOrbitFromShift,
    shiftOrbitCompHom_of_of, shiftOrbitCompHom_of_of]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_zero (a + b))
  refine (shiftHomComp_heq_shiftHomComp' (add_zero (a + b))
    (shiftHomZero (A := A) (orbitPushdownArrow' rfl f)) (𝟙 _)).trans
      (heq_of_eq ?_)
  simp [shiftHomComp, shiftHomComp', shiftHomZero, orbitPushdownArrow',
    CategoryTheory.ShiftedHom.mk₀, shiftFunctorAdd'_add_zero_inv_app]
  have hz (h0 : (0 : A) = 0) :
      shiftFunctorZero' C 0 h0 = shiftFunctorZero C A := by
    rw [Subsingleton.elim h0 rfl]
    ext
    simp [shiftFunctorZero']
  rw [hz]
  simp

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- Applying the module turns composition of component arrows into
composition of component linear maps. -/
theorem orbitPushdownComponent'_comp
    {X Y Z : C} {a c b ab ca d : A}
    (hab : a + b = ab) (hca : c + a = ca)
    (hleft : ca + b = d) (hright : c + ab = d)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z c) :
    orbitPushdownComponent' M hleft (shiftHomComp' hca f g) =
      (orbitPushdownComponent' M hright g).comp
        (orbitPushdownComponent' M hab f) := by
  apply LinearMap.ext
  intro x
  simp only [orbitPushdownComponent', LinearMap.comp_apply]
  rw [orbitPushdownArrow'_comp hab hca hleft hright f g,
    M.map_comp, ModuleCat.comp_apply]

/-- A homogeneous orbit morphism acts on the direct sum by translating the
summand index on the left by its degree. -/
def orbitPushdownHomogeneousMap
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    orbitPushdownValue (A := A) M X →ₗ[k]
      orbitPushdownValue (A := A) M Y := by
  classical
  exact DirectSum.toModule k A _ fun b ↦
    (orbitPushdownLof M Y (a + b)).comp
      (orbitPushdownComponent M a b f)

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
@[simp]
theorem orbitPushdownHomogeneousMap_lof
    {X Y : C} (a b : A) (f : ShiftHom X Y a)
    (x : M.obj ((shiftFunctor C b).obj X)) :
    orbitPushdownHomogeneousMap M a f
        (orbitPushdownLof M X b x) =
      orbitPushdownLof M Y (a + b)
        (orbitPushdownComponent M a b f x) := by
  classical
  simp [orbitPushdownHomogeneousMap, orbitPushdownLof]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- Homogeneous push-down maps respect homogeneous composition. -/
theorem orbitPushdownHomogeneousMap_comp
    {X Y Z : C} {a c : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z c) :
    orbitPushdownHomogeneousMap M (c + a) (shiftHomComp f g) =
      (orbitPushdownHomogeneousMap M c g).comp
        (orbitPushdownHomogeneousMap M a f) := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change orbitPushdownHomogeneousMap M (c + a) (shiftHomComp f g)
      (orbitPushdownLof M X b x) =
    orbitPushdownHomogeneousMap M c g
      (orbitPushdownHomogeneousMap M a f
        (orbitPushdownLof M X b x))
  rw [orbitPushdownHomogeneousMap_lof,
    orbitPushdownHomogeneousMap_lof,
    orbitPushdownHomogeneousMap_lof]
  change DirectSum.of
      (fun e ↦ M.obj ((shiftFunctor C e).obj Z)) ((c + a) + b)
        (orbitPushdownComponent M (c + a) b (shiftHomComp f g) x) =
    DirectSum.of (fun e ↦ M.obj ((shiftFunctor C e).obj Z))
      (c + (a + b))
      (orbitPushdownComponent M c (a + b) g
        (orbitPushdownComponent M a b f x))
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_assoc c a b)
  exact
    (orbitPushdownComponent_apply_heq_component'_apply M
      (add_assoc c a b) (shiftHomComp f g) x).trans
      (heq_of_eq (DFunLike.congr_fun
        (orbitPushdownComponent'_comp M rfl rfl
          (add_assoc c a b) rfl f g) x))

/-- The action of degree-`a` homogeneous morphisms is linear in the
morphism. -/
def orbitPushdownHomogeneousLinearMap
    {X Y : C} (a : A) :
    ShiftHom X Y a →ₗ[k]
      (orbitPushdownValue (A := A) M X →ₗ[k]
        orbitPushdownValue (A := A) M Y) where
  toFun := orbitPushdownHomogeneousMap M a
  map_add' f g := by
    classical
    apply DirectSum.linearMap_ext
    intro b
    apply LinearMap.ext
    intro x
    simp [orbitPushdownHomogeneousMap, orbitPushdownLof,
      orbitPushdownComponent, orbitPushdownComponent', Functor.map_add,
      orbitPushdownArrow', Preadditive.add_comp]
  map_smul' r f := by
    classical
    apply DirectSum.linearMap_ext
    intro b
    apply LinearMap.ext
    intro x
    simp [orbitPushdownHomogeneousMap, orbitPushdownLof,
      orbitPushdownComponent, orbitPushdownComponent', Functor.map_smul,
      orbitPushdownArrow', CategoryTheory.Linear.smul_comp]

/-- The linear action of all finite-support orbit morphisms. -/
def orbitPushdownMapLinear
    {X Y : C} :
    ShiftOrbitHom A X Y →ₗ[k]
      (orbitPushdownValue (A := A) M X →ₗ[k]
        orbitPushdownValue (A := A) M Y) := by
  classical
  exact DirectSum.toModule k A _ fun a ↦
    orbitPushdownHomogeneousLinearMap M a

@[simp]
theorem orbitPushdownMapLinear_of
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    orbitPushdownMapLinear M (shiftOrbitOf X Y a f) =
      orbitPushdownHomogeneousMap M a f := by
  classical
  change orbitPushdownMapLinear M
      (DirectSum.lof k A (fun c ↦ ShiftHom X Y c) a f) = _
  simp [orbitPushdownMapLinear]
  rfl

/-- The action of arbitrary finite-support orbit morphisms respects orbit
composition. -/
theorem orbitPushdownMapLinear_comp
    {X Y Z : C} (f : ShiftOrbitHom A X Y) (g : ShiftOrbitHom A Y Z) :
    orbitPushdownMapLinear M (shiftOrbitCompHom f g) =
      (orbitPushdownMapLinear M g).comp (orbitPushdownMapLinear M f) := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro c gc
      change orbitPushdownMapLinear M
          (shiftOrbitCompHom (shiftOrbitOf X Y a fa)
            (shiftOrbitOf Y Z c gc)) =
        (orbitPushdownMapLinear M (shiftOrbitOf Y Z c gc)).comp
          (orbitPushdownMapLinear M (shiftOrbitOf X Y a fa))
      rw [shiftOrbitCompHom_of_of, orbitPushdownMapLinear_of,
        orbitPushdownMapLinear_of, orbitPushdownMapLinear_of]
      exact orbitPushdownHomogeneousMap_comp M fa gc
    · intro g₁ g₂ hg₁ hg₂
      change orbitPushdownMapLinear M
          (shiftOrbitCompHom (shiftOrbitOf X Y a fa) g₁) =
        (orbitPushdownMapLinear M g₁).comp
          (orbitPushdownMapLinear M (shiftOrbitOf X Y a fa)) at hg₁
      change orbitPushdownMapLinear M
          (shiftOrbitCompHom (shiftOrbitOf X Y a fa) g₂) =
        (orbitPushdownMapLinear M g₂).comp
          (orbitPushdownMapLinear M (shiftOrbitOf X Y a fa)) at hg₂
      change orbitPushdownMapLinear M
          (shiftOrbitCompHom (shiftOrbitOf X Y a fa) (g₁ + g₂)) =
        (orbitPushdownMapLinear M (g₁ + g₂)).comp
          (orbitPushdownMapLinear M (shiftOrbitOf X Y a fa))
      rw [(shiftOrbitCompHom (shiftOrbitOf X Y a fa)).map_add,
        map_add, map_add, hg₁, hg₂]
      ext x
      rfl
  · intro f₁ f₂ hf₁ hf₂
    rw [shiftOrbitCompHom.map_add, AddMonoidHom.add_apply,
      map_add, map_add, hf₁, hf₂]
    ext x
    simp

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
@[simp]
theorem orbitPushdownHomogeneousMap_id (X : C) :
    orbitPushdownHomogeneousMap M (0 : A) (shiftHomId (A := A) X) =
      LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  change orbitPushdownHomogeneousMap M (0 : A)
      (shiftHomId (A := A) X) (orbitPushdownLof M X b x) =
    orbitPushdownLof M X b x
  rw [orbitPushdownHomogeneousMap_lof]
  change DirectSum.of
      (fun c ↦ M.obj ((shiftFunctor C c).obj X)) (0 + b)
        (orbitPushdownComponent M 0 b (shiftHomId (A := A) X) x) =
    DirectSum.of (fun c ↦ M.obj ((shiftFunctor C c).obj X)) b x
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add b)
  exact
    (orbitPushdownComponent_apply_heq_component'_apply M
      (zero_add b) (shiftHomId (A := A) X) x).trans
      (heq_of_eq (DFunLike.congr_fun
        (orbitPushdownComponent'_id M X b) x))

/-- Gabriel's direct-sum push-down of a linear module along the canonical
projection to the shift-orbit category. -/
noncomputable def orbitPushdown :
    ShiftOrbitCategory C A ⥤ ModuleCat.{max w uM} k where
  obj X := ModuleCat.of k
    (orbitPushdownValue (A := A) M (show C from X))
  map {X Y} f := ModuleCat.ofHom (orbitPushdownMapLinear M f)
  map_id X := by
    apply ModuleCat.hom_ext
    change orbitPushdownMapLinear M (shiftOrbitId (show C from X)) =
      LinearMap.id
    rw [shiftOrbitId, orbitPushdownMapLinear_of,
      orbitPushdownHomogeneousMap_id]
  map_comp f g := by
    apply ModuleCat.hom_ext
    change orbitPushdownMapLinear M (shiftOrbitCompHom f g) =
      (orbitPushdownMapLinear M g).comp (orbitPushdownMapLinear M f)
    exact orbitPushdownMapLinear_comp M f g

instance orbitPushdown_additive : (orbitPushdown (A := A) M).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    exact (orbitPushdownMapLinear M).map_add f g

instance orbitPushdown_linear : (orbitPushdown (A := A) M).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    exact (orbitPushdownMapLinear M).map_smul r f

end MagnitudeConjecture.CoveringHom
