import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Homogeneous morphisms for a shift orbit category

Mathlib's `HasShift` is a coherent action of an additive monoid by
endofunctors.  For a group action written additively, the homogeneous
degree-`a` orbit morphisms from `X` to `Y` are the morphisms
`X ⟶ Y⟦a⟧`.  This file defines their identity and composition and proves
the unit and associativity laws before passing to direct sums.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [AddMonoid A] [HasShift C A]

/-- Homogeneous orbit morphisms of degree `a`. -/
abbrev ShiftHom (X Y : C) (a : A) := X ⟶ (shiftFunctor C a).obj Y

/-- The degree-zero homogeneous identity. -/
def shiftHomId (X : C) : ShiftHom X X (0 : A) :=
  (shiftFunctorZero C A).inv.app X

/-- An ordinary morphism regarded as a degree-zero homogeneous morphism. -/
def shiftHomZero {X Y : C} (f : X ⟶ Y) : ShiftHom X Y (0 : A) :=
  CategoryTheory.ShiftedHom.mk₀ 0 rfl f

@[simp]
theorem shiftHomZero_id (X : C) :
    shiftHomZero (A := A) (𝟙 X) = shiftHomId X := by
  simp [shiftHomZero, shiftHomId, CategoryTheory.ShiftedHom.mk₀,
    shiftFunctorZero']

/-- Composition of homogeneous orbit morphisms, with an explicitly chosen
output degree.  The order `b + a` comes from applying the degree-`a` shift to
a degree-`b` second morphism. -/
def shiftHomComp'
    {X Y Z : C} {a b c : A} (h : b + a = c)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) : ShiftHom X Z c :=
  f ≫ (shiftFunctor C a).map g ≫
    (shiftFunctorAdd' C b a c h).inv.app Z

/-- Composition with its canonical output degree. -/
def shiftHomComp
    {X Y Z : C} {a b : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    ShiftHom X Z (b + a) :=
  shiftHomComp' rfl f g

/-- Canonical homogeneous composition agrees heterogeneously with composition
at any propositionally equal output degree. -/
theorem shiftHomComp_heq_shiftHomComp'
    {X Y Z : C} {a b c : A} (h : b + a = c)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    HEq (shiftHomComp f g) (shiftHomComp' h f g) := by
  subst c
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftHomComp'_zero_zero
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    shiftHomComp' (zero_add (0 : A))
        (shiftHomZero (A := A) f) (shiftHomZero (A := A) g) =
      shiftHomZero (A := A) (f ≫ g) := by
  simpa [shiftHomComp', shiftHomZero, CategoryTheory.ShiftedHom.comp] using
    CategoryTheory.ShiftedHom.mk₀_comp_mk₀ f g (zero_add (0 : A)) rfl rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftHomComp'_id_left
    {X Y : C} {a : A} (f : ShiftHom X Y a) :
    shiftHomComp' (add_zero a) (shiftHomId X) f = f := by
  simp only [shiftHomComp', shiftHomId,
    shiftFunctorAdd'_add_zero_inv_app]
  rw [(shiftFunctorZero C A).hom.naturality]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftHomComp'_id_right
    {X Y : C} {a : A} (f : ShiftHom X Y a) :
    shiftHomComp' (zero_add a) f (shiftHomId Y) = f := by
  simp only [shiftHomComp', shiftHomId,
    shiftFunctorAdd'_zero_add_inv_app]
  rw [← Functor.map_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of homogeneous composition, including all degree
reassociations. -/
theorem shiftHomComp'_assoc
    {W X Y Z : C} {a b c ba cb d : A}
    (hba : b + a = ba) (hcb : c + b = cb)
    (hleft : c + ba = d) (hright : cb + a = d)
    (f : ShiftHom W X a) (g : ShiftHom X Y b)
    (h : ShiftHom Y Z c) :
    shiftHomComp' hleft (shiftHomComp' hba f g) h =
      shiftHomComp' hright f (shiftHomComp' hcb g h) := by
  subst ba
  subst cb
  subst d
  have hright_eq : hright = add_assoc c b a := Subsingleton.elim _ _
  rw [hright_eq]
  simp only [shiftHomComp', Functor.map_comp, Category.assoc]
  rw [← (shiftFunctorAdd' C b a (b + a) rfl).inv.naturality_assoc h]
  rw [shiftFunctorAdd'_assoc_inv_app c b a (c + b) (b + a)
    (c + (b + a)) rfl rfl (add_assoc c b a)]
  rfl

section DirectSum

variable [Preadditive C]
variable [∀ a : A, (shiftFunctor C a).Additive]

/-- The finite-support direct sum of all homogeneous shift morphisms. -/
abbrev ShiftOrbitHom (A : Type w) [AddMonoid A] [HasShift C A]
    (X Y : C) := DirectSum A (fun a ↦ ShiftHom X Y a)

/-- Inclusion of one homogeneous component into the orbit Hom direct sum. -/
noncomputable def shiftOrbitOf (X Y : C) (a : A) :
    ShiftHom X Y a →+ ShiftOrbitHom A X Y := by
  classical
  exact DirectSum.of (fun c : A ↦ ShiftHom X Y c) a

omit [∀ a : A, (shiftFunctor C a).Additive] in
/-- With a fixed decidable equality on the degree monoid, the homogeneous
inclusion is the corresponding direct-sum generator. -/
theorem shiftOrbitOf_eq_directSumOf [DecidableEq A]
    (X Y : C) (a : A) (f : ShiftHom X Y a) :
    shiftOrbitOf X Y a f =
      DirectSum.of (fun c : A ↦ ShiftHom X Y c) a f := by
  unfold shiftOrbitOf
  have h : (fun b c : A ↦ Classical.propDecidable (b = c)) =
      (inferInstance : DecidableEq A) :=
    Subsingleton.elim _ _
  rw [h]

/-- Homogeneous composition as a homomorphism in both variables. -/
def shiftHomCompAddHom
    {X Y Z : C} {a b : A} :
    ShiftHom X Y a →+ ShiftHom Y Z b →+ ShiftHom X Z (b + a) where
  toFun f :=
    { toFun := fun g ↦ shiftHomComp f g
      map_zero' := by simp [shiftHomComp, shiftHomComp']
      map_add' := by
        intro g h
        simp [shiftHomComp, shiftHomComp', Functor.map_add,
          Preadditive.comp_add] }
  map_zero' := by
    ext g
    simp [shiftHomComp, shiftHomComp']
  map_add' := by
    intro f g
    ext h
    simp [shiftHomComp, shiftHomComp', Preadditive.add_comp]

section Linear

variable {k : Type*} [CommSemiring k] [CategoryTheory.Linear k C]
variable [∀ a : A, (shiftFunctor C a).Linear k]

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
@[simp]
theorem shiftHomZero_smul
    {X Y : C} (r : k) (f : X ⟶ Y) :
    shiftHomZero (A := A) (r • f) = r • shiftHomZero (A := A) f := by
  simp [shiftHomZero, CategoryTheory.ShiftedHom.mk₀,
    CategoryTheory.Linear.smul_comp]

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
@[simp]
theorem shiftHomComp_smul_left
    {X Y Z : C} {a b : A} (r : k)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftHomComp (r • f) g = r • shiftHomComp f g := by
  simp [shiftHomComp, shiftHomComp', CategoryTheory.Linear.smul_comp]

omit [∀ a : A, (shiftFunctor C a).Additive] in
@[simp]
theorem shiftHomComp_smul_right
    {X Y Z : C} {a b : A} (r : k)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftHomComp f (r • g) = r • shiftHomComp f g := by
  simp [shiftHomComp, shiftHomComp', Functor.map_smul,
    CategoryTheory.Linear.comp_smul]

/-- Homogeneous composition as a linear map in both variables. -/
def shiftHomCompLinearMap
    {X Y Z : C} {a b : A} :
    ShiftHom X Y a →ₗ[k] ShiftHom Y Z b →ₗ[k] ShiftHom X Z (b + a) :=
  LinearMap.mk₂ k shiftHomComp
    (fun f g h ↦ DFunLike.congr_fun (shiftHomCompAddHom.map_add f g) h)
    (fun r _ _ ↦ shiftHomComp_smul_left r _ _)
    (fun f g h ↦ (shiftHomCompAddHom f).map_add g h)
    (fun r _ _ ↦ shiftHomComp_smul_right r _ _)

/-- Linear inclusion of one homogeneous component into the orbit Hom direct
sum. -/
noncomputable def shiftOrbitLof (X Y : C) (a : A) :
    ShiftHom X Y a →ₗ[k] ShiftOrbitHom A X Y := by
  classical
  exact DirectSum.lof k A (fun c : A ↦ ShiftHom X Y c) a

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
@[simp]
theorem shiftOrbitLof_apply
    {X Y : C} {a : A} (f : ShiftHom X Y a) :
    shiftOrbitLof (k := k) X Y a f = shiftOrbitOf X Y a f := by
  rfl

/-- Homogeneous composition followed by inclusion in the output direct sum. -/
def shiftHomCompLofLinearMap
    {X Y Z : C} (a b : A) :
    ShiftHom X Y a →ₗ[k] ShiftHom Y Z b →ₗ[k] ShiftOrbitHom A X Z :=
  LinearMap.mk₂ k
    (fun f g ↦ shiftOrbitLof (k := k) X Z (b + a) (shiftHomComp f g))
    (fun f₁ f₂ g ↦ by
      rw [show shiftHomComp (f₁ + f₂) g =
        shiftHomComp f₁ g + shiftHomComp f₂ g from
          DFunLike.congr_fun (shiftHomCompAddHom.map_add f₁ f₂) g]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_add _ _)
    (fun r f g ↦ by
      rw [shiftHomComp_smul_left]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_smul r _)
    (fun f g₁ g₂ ↦ by
      have hcomp : shiftHomComp f (g₁ + g₂) =
          shiftHomComp f g₁ + shiftHomComp f g₂ :=
        (shiftHomCompAddHom f).map_add g₁ g₂
      rw [hcomp]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_add _ _)
    (fun r f g ↦ by
      rw [shiftHomComp_smul_right]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_smul r _)

/-- Convolution as a linear map in both direct-sum variables. -/
noncomputable def shiftOrbitCompLinearMap
    {X Y Z : C} :
    ShiftOrbitHom A X Y →ₗ[k]
      ShiftOrbitHom A Y Z →ₗ[k] ShiftOrbitHom A X Z := by
  classical
  exact
    DirectSum.toModule k A _ fun a ↦
      (DirectSum.toModule k A _ fun b ↦
        (shiftHomCompLofLinearMap (k := k) (X := X) (Y := Y) (Z := Z) a b).flip).flip

@[simp]
theorem shiftOrbitCompLinearMap_of_of
    {X Y Z : C} {a b : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftOrbitCompLinearMap (k := k)
        (shiftOrbitOf X Y a f) (shiftOrbitOf Y Z b g) =
      shiftOrbitOf X Z (b + a) (shiftHomComp f g) := by
  classical
  change shiftOrbitCompLinearMap (k := k)
      (DirectSum.lof k A (fun c : A ↦ ShiftHom X Y c) a f)
      (DirectSum.lof k A (fun c : A ↦ ShiftHom Y Z c) b g) =
    shiftOrbitLof (k := k) X Z (b + a) (shiftHomComp f g)
  simp [shiftOrbitCompLinearMap, shiftHomCompLofLinearMap]

end Linear

/-- Convolution composition on finite-support direct sums of homogeneous
morphisms. -/
def shiftOrbitCompHom
    {X Y Z : C} :
    ShiftOrbitHom A X Y →+ ShiftOrbitHom A Y Z →+ ShiftOrbitHom A X Z := by
  classical
  exact
    DirectSum.toAddMonoid fun a ↦
      AddMonoidHom.flip <|
        DirectSum.toAddMonoid fun b ↦
          AddMonoidHom.flip <|
            (shiftOrbitOf X Z (b + a)).compHom.comp shiftHomCompAddHom

@[simp]
theorem shiftOrbitCompHom_of_of
    {X Y Z : C} {a b : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftOrbitCompHom
        (shiftOrbitOf X Y a f) (shiftOrbitOf Y Z b g) =
      shiftOrbitOf X Z (b + a) (shiftHomComp f g) := by
  classical
  simp [shiftOrbitCompHom, shiftOrbitOf, shiftHomCompAddHom]

section LinearComparison

variable {k : Type*} [CommSemiring k] [CategoryTheory.Linear k C]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- The separately bundled bilinear convolution has the same underlying
operation as the additive convolution used by the category structure. -/
theorem shiftOrbitCompLinearMap_apply
    {X Y Z : C} (f : ShiftOrbitHom A X Y) (g : ShiftOrbitHom A Y Z) :
    shiftOrbitCompLinearMap (k := k) f g = shiftOrbitCompHom f g := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro b gb
      change shiftOrbitCompLinearMap (k := k)
          (shiftOrbitOf X Y a fa) (shiftOrbitOf Y Z b gb) =
        shiftOrbitCompHom (shiftOrbitOf X Y a fa) (shiftOrbitOf Y Z b gb)
      rw [shiftOrbitCompLinearMap_of_of, shiftOrbitCompHom_of_of]
    · intro g₁ g₂ hg₁ hg₂
      simpa only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using
        congrArg₂ (.+.) hg₁ hg₂
  · intro f₁ f₂ hf₁ hf₂
    simpa only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using
      congrArg₂ (.+.) hf₁ hf₂

end LinearComparison

@[simp]
theorem shiftOrbitComp_zero_zero
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    shiftOrbitCompHom
        (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f))
        (shiftOrbitOf Y Z 0 (shiftHomZero (A := A) g)) =
      shiftOrbitOf X Z 0 (shiftHomZero (A := A) (f ≫ g)) := by
  classical
  rw [shiftOrbitCompHom_of_of]
  change DirectSum.of (fun d : A ↦ ShiftHom X Z d) (0 + 0)
      (shiftHomComp (shiftHomZero (A := A) f)
        (shiftHomZero (A := A) g)) =
    DirectSum.of (fun d : A ↦ ShiftHom X Z d) 0
      (shiftHomZero (A := A) (f ≫ g))
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add (0 : A))
  exact
    (shiftHomComp_heq_shiftHomComp' (zero_add (0 : A))
      (shiftHomZero (A := A) f) (shiftHomZero (A := A) g)).trans
      (heq_of_eq (shiftHomComp'_zero_zero f g))

/-- Identity morphism in the shift-orbit Hom direct sum. -/
def shiftOrbitId (X : C) : ShiftOrbitHom A X X :=
  shiftOrbitOf X X 0 (shiftHomId X)

@[simp]
theorem shiftOrbitComp_id_left
    {X Y : C} (f : ShiftOrbitHom A X Y) :
    shiftOrbitCompHom (shiftOrbitId X) f = f := by
  classical
  suffices shiftOrbitCompHom (shiftOrbitId X) =
      AddMonoidHom.id (ShiftOrbitHom A X Y) from
    DFunLike.congr_fun this f
  apply DirectSum.addHom_ext
  intro a g
  change shiftOrbitCompHom (shiftOrbitOf X X 0 (shiftHomId X))
      (shiftOrbitOf X Y a g) = shiftOrbitOf X Y a g
  rw [shiftOrbitCompHom_of_of]
  change DirectSum.of (fun c : A ↦ ShiftHom X Y c) (a + 0)
      (shiftHomComp (shiftHomId X) g) =
    DirectSum.of (fun c : A ↦ ShiftHom X Y c) a g
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_zero a)
  exact (shiftHomComp_heq_shiftHomComp' (add_zero a) (shiftHomId X) g).trans
    (heq_of_eq (shiftHomComp'_id_left g))

@[simp]
theorem shiftOrbitComp_id_right
    {X Y : C} (f : ShiftOrbitHom A X Y) :
    shiftOrbitCompHom f (shiftOrbitId Y) = f := by
  classical
  suffices shiftOrbitCompHom.flip (shiftOrbitId Y) =
      AddMonoidHom.id (ShiftOrbitHom A X Y) from
    DFunLike.congr_fun this f
  apply DirectSum.addHom_ext
  intro a g
  change shiftOrbitCompHom (shiftOrbitOf X Y a g)
      (shiftOrbitOf Y Y 0 (shiftHomId Y)) = shiftOrbitOf X Y a g
  rw [shiftOrbitCompHom_of_of]
  change DirectSum.of (fun c : A ↦ ShiftHom X Y c) (0 + a)
      (shiftHomComp g (shiftHomId Y)) =
    DirectSum.of (fun c : A ↦ ShiftHom X Y c) a g
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add a)
  exact (shiftHomComp_heq_shiftHomComp' (zero_add a) g (shiftHomId Y)).trans
    (heq_of_eq (shiftHomComp'_id_right g))

theorem shiftOrbitComp_assoc_of_of_of
    {W X Y Z : C} {a b c : A}
    (f : ShiftHom W X a) (g : ShiftHom X Y b)
    (h : ShiftHom Y Z c) :
    shiftOrbitCompHom
        (shiftOrbitCompHom (shiftOrbitOf W X a f) (shiftOrbitOf X Y b g))
        (shiftOrbitOf Y Z c h) =
      shiftOrbitCompHom (shiftOrbitOf W X a f)
        (shiftOrbitCompHom (shiftOrbitOf X Y b g) (shiftOrbitOf Y Z c h)) := by
  classical
  rw [shiftOrbitCompHom_of_of, shiftOrbitCompHom_of_of,
    shiftOrbitCompHom_of_of, shiftOrbitCompHom_of_of]
  change DirectSum.of (fun d : A ↦ ShiftHom W Z d) (c + (b + a))
      (shiftHomComp (shiftHomComp f g) h) =
    DirectSum.of (fun d : A ↦ ShiftHom W Z d) ((c + b) + a)
      (shiftHomComp f (shiftHomComp g h))
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_assoc c b a).symm
  exact
    (shiftHomComp_heq_shiftHomComp' rfl (shiftHomComp f g) h).trans <|
      (heq_of_eq (shiftHomComp'_assoc rfl rfl rfl (add_assoc c b a) f g h)).trans <|
        (shiftHomComp_heq_shiftHomComp' (add_assoc c b a) f
          (shiftHomComp g h)).symm

/-- Associativity of convolution on the full finite-support direct sums. -/
theorem shiftOrbitComp_assoc
    {W X Y Z : C}
    (f : ShiftOrbitHom A W X) (g : ShiftOrbitHom A X Y)
    (h : ShiftOrbitHom A Y Z) :
    shiftOrbitCompHom (shiftOrbitCompHom f g) h =
      shiftOrbitCompHom f (shiftOrbitCompHom g h) := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro b gb
      refine DirectSum.induction_on h ?_ ?_ ?_
      · simp
      · intro c hc
        exact shiftOrbitComp_assoc_of_of_of fa gb hc
      · intro h₁ h₂ hh₁ hh₂
        simpa only [map_add, AddMonoidHom.add_apply] using congrArg₂ (.+.) hh₁ hh₂
    · intro g₁ g₂ hg₁ hg₂
      simpa only [map_add, AddMonoidHom.add_apply] using congrArg₂ (.+.) hg₁ hg₂
  · intro f₁ f₂ hf₁ hf₂
    simpa only [map_add, AddMonoidHom.add_apply] using congrArg₂ (.+.) hf₁ hf₂

/-- The shift-orbit category has the same objects as `C` and finite-support
direct sums of shifted Hom spaces as morphisms. -/
@[nolint unusedArguments]
def ShiftOrbitCategory (C : Type u) (_A : Type w) := C

namespace ShiftOrbitCategory

instance categoryStruct : CategoryStruct.{max v w} (ShiftOrbitCategory C A) where
  Hom X Y := ShiftOrbitHom (C := C) A (show C from X) (show C from Y)
  id X := shiftOrbitId (C := C) (A := A) (show C from X)
  comp f g := shiftOrbitCompHom (C := C) (A := A) f g

instance category : Category.{max v w} (ShiftOrbitCategory C A) where
  id_comp := by
    intro X Y f
    exact shiftOrbitComp_id_left (C := C) (A := A) f
  comp_id := by
    intro X Y f
    exact shiftOrbitComp_id_right (C := C) (A := A) f
  assoc := by
    intro W X Y Z f g h
    exact shiftOrbitComp_assoc (C := C) (A := A) f g h

/-- The canonical functor into the shift-orbit category, supported in degree
zero on every morphism. -/
noncomputable def identityComponentFunctor :
    C ⥤ ShiftOrbitCategory C A where
  obj X := X
  map {X Y} f := shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)
  map_id X := by
    change shiftOrbitOf X X 0 (shiftHomZero (A := A) (𝟙 X)) =
      shiftOrbitId X
    rw [shiftHomZero_id]
    rfl
  map_comp f g := by
    exact (shiftOrbitComp_zero_zero f g).symm

/-- The degree-zero component inclusion is injective on every Hom space. -/
theorem identityComponentFunctor_map_injective (X Y : C) :
    Function.Injective
      ((identityComponentFunctor (C := C) (A := A)).map :
        (X ⟶ Y) →
          ((identityComponentFunctor (C := C) (A := A)).obj X ⟶
            (identityComponentFunctor (C := C) (A := A)).obj Y)) := by
  classical
  intro f g hfg
  apply (CategoryTheory.ShiftedHom.homEquiv (0 : A) rfl).injective
  exact DirectSum.of_injective (0 : A) hfg

/-- The canonical degree-zero functor is faithful without any translate
orthogonality hypothesis. -/
theorem identityComponentFunctor_faithful :
    (identityComponentFunctor (C := C) (A := A)).Faithful where
  map_injective := fun {X Y} ↦ identityComponentFunctor_map_injective X Y

instance preadditive : Preadditive (ShiftOrbitCategory C A) where
  homGroup X Y := inferInstanceAs <|
    AddCommGroup (ShiftOrbitHom (C := C) A (show C from X) (show C from Y))
  add_comp _ _ _ f g h := by
    exact DFunLike.congr_fun
      (shiftOrbitCompHom (C := C) (A := A) |>.map_add f g) h
  comp_add _ _ _ f g h := by
    exact (shiftOrbitCompHom (C := C) (A := A) f).map_add g h

instance identityComponentFunctor_additive :
    (identityComponentFunctor (C := C) (A := A)).Additive where
  map_add {X Y} f g := by
    change shiftOrbitOf X Y 0 (shiftHomZero (A := A) (f + g)) =
      shiftOrbitOf X Y 0 (shiftHomZero (A := A) f) +
        shiftOrbitOf X Y 0 (shiftHomZero (A := A) g)
    simp [shiftHomZero, CategoryTheory.ShiftedHom.mk₀_add]

section LinearCategory

variable {k : Type*} [CommSemiring k] [CategoryTheory.Linear k C]
variable [∀ a : A, (shiftFunctor C a).Linear k]

instance homModule (X Y : ShiftOrbitCategory C A) : Module k (X ⟶ Y) :=
  inferInstanceAs <|
    Module k (ShiftOrbitHom (C := C) A (show C from X) (show C from Y))

instance linear : CategoryTheory.Linear k (ShiftOrbitCategory C A) where
  homModule X Y := homModule (C := C) (A := A) X Y
  smul_comp _ _ _ r f g := by
    change shiftOrbitCompHom (r • f) g = r • shiftOrbitCompHom f g
    rw [← shiftOrbitCompLinearMap_apply (k := k) (r • f) g,
      ← shiftOrbitCompLinearMap_apply (k := k) f g]
    exact DFunLike.congr_fun (shiftOrbitCompLinearMap (k := k) |>.map_smul r f) g
  comp_smul _ _ _ f r g := by
    change shiftOrbitCompHom f (r • g) = r • shiftOrbitCompHom f g
    rw [← shiftOrbitCompLinearMap_apply (k := k) f (r • g),
      ← shiftOrbitCompLinearMap_apply (k := k) f g]
    exact (shiftOrbitCompLinearMap (k := k) f).map_smul r g

instance identityComponentFunctor_linear :
    (identityComponentFunctor (C := C) (A := A)).Linear k where
  map_smul {X Y} f r := by
    change shiftOrbitOf X Y 0 (shiftHomZero (A := A) (r • f)) =
      r • shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)
    change shiftOrbitLof (k := k) X Y 0
        (shiftHomZero (A := A) (r • f)) =
      r • shiftOrbitLof (k := k) X Y 0 (shiftHomZero (A := A) f)
    rw [shiftHomZero_smul]
    exact (shiftOrbitLof (k := k) X Y 0).map_smul r _

end LinearCategory

end ShiftOrbitCategory

end DirectSum

end MagnitudeConjecture.CoveringHom
