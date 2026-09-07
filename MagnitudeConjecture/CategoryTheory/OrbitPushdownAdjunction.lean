import MagnitudeConjecture.CategoryTheory.OrbitPushdownDegree
import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso

/-!
# Gabriel push-down is left adjoint to pull-up

Pull-up is restriction along the degree-zero functor from the covering
category to its shift-orbit category.  A map from a push-down module is
determined by its value on the normalized degree-zero summands.  Conversely,
a map to pull-up extends over every translated summand by the canonical orbit
isomorphism from that translate to the original object.

These constructions are mutually inverse and natural in both module
variables.  They give the push-down/pull-up adjunction used in Gabriel's
proof that push-down preserves Auslander--Reiten sequences.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- Pull-up along the degree-zero orbit functor. -/
noncomputable def linearModuleOrbitPullup :
    LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k ⥤
      LinearModuleCategory.{u, v, uK, max w uM} (C := C) k where
  obj N := ⟨ShiftOrbitCategory.identityComponentFunctor ⋙ N.obj,
    inferInstance, inferInstance⟩
  map α := ObjectProperty.homMk
    (Functor.whiskerLeft ShiftOrbitCategory.identityComponentFunctor α.hom)
  map_id N := by
    apply ObjectProperty.hom_ext
    exact Functor.whiskerLeft_id _
  map_comp α β := by
    apply ObjectProperty.hom_ext
    exact Functor.whiskerLeft_comp _ _ _

instance linearModuleOrbitPullup_additive :
    (linearModuleOrbitPullup
      (k := k) (C := C) (A := A)).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    rfl

instance linearModuleOrbitPullup_linear :
    (linearModuleOrbitPullup
      (k := k) (C := C) (A := A)).Linear k where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    rfl

omit [Preadditive C] [∀ a : A, (shiftFunctor C a).Additive] in
set_option backward.isDefEq.respectTransparency false in
theorem shiftFunctorZero_inv_comp_orbitPushdownArrow_zero_of_hasShift
    {X Y : C} (h : X ⟶ Y) :
    (shiftFunctorZero C A).inv.app X ≫
        orbitPushdownArrow' (zero_add 0) (shiftHomZero (A := A) h) =
      h ≫ (shiftFunctorZero C A).inv.app Y := by
  simp only [orbitPushdownArrow', shiftHomZero,
    CategoryTheory.ShiftedHom.mk₀,
    shiftFunctorAdd'_zero_add_inv_app]
  have hz (h0 : (0 : A) = 0) :
      shiftFunctorZero' C 0 h0 = shiftFunctorZero C A := by
    rw [Subsingleton.elim h0 rfl]
    ext
    simp [shiftFunctorZero']
  rw [hz]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simpa using ((shiftFunctorZero C A).inv.naturality h).symm

set_option backward.isDefEq.respectTransparency false in
theorem orbitPushdownZeroMap_inclusion_of_hasShift
    {M : C ⥤ ModuleCat.{uM} k} [M.Additive] [M.Linear k]
    {X Y : C} (h : X ⟶ Y) (x : M.obj X) :
    orbitPushdownMapLinear M
        (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
        (orbitPushdownLof M X 0
          (M.map ((shiftFunctorZero C A).inv.app X) x)) =
      orbitPushdownLof M Y 0
        (M.map ((shiftFunctorZero C A).inv.app Y) (M.map h x)) := by
  classical
  rw [orbitPushdownMapLinear_of, orbitPushdownHomogeneousMap_lof]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add (0 : A))
  apply (orbitPushdownComponent_apply_heq_component'_apply M
    (zero_add (0 : A)) (shiftHomZero (A := A) h)
      (M.map ((shiftFunctorZero C A).inv.app X) x)).trans
  apply heq_of_eq
  have hmap := congrArg (fun q ↦ M.map q)
    (shiftFunctorZero_inv_comp_orbitPushdownArrow_zero_of_hasShift
      (A := A) h)
  simp only [M.map_comp] at hmap
  exact congr($(hmap) x)

variable {M : C ⥤ ModuleCat.{max w uM} k} [M.Additive] [M.Linear k]
variable {N : ShiftOrbitCategory C A ⥤ ModuleCat.{max w uM} k}
variable [N.Additive] [N.Linear k]

/-- Restrict a map out of push-down to the degree-zero input summand. -/
noncomputable def orbitPushdownToPullup
    (α : orbitPushdown (A := A) M ⟶ N) :
    M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N := by
  exact
    { app := fun X ↦ ModuleCat.ofHom <|
        (α.app X).hom.comp <|
          (orbitPushdownLof M X 0).comp
            (M.map ((shiftFunctorZero C A).inv.app X)).hom
      naturality := fun {X Y} h ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change
          (α.app Y).hom
              (orbitPushdownLof M Y 0
                (M.map ((shiftFunctorZero C A).inv.app Y) (M.map h x))) =
            N.map (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
              ((α.app X).hom
                (orbitPushdownLof M X 0
                  (M.map ((shiftFunctorZero C A).inv.app X) x)))
        rw [← orbitPushdownZeroMap_inclusion_of_hasShift (A := A) h x]
        exact congrArg (fun f ↦ f.hom
          (orbitPushdownLof M X 0
            (M.map ((shiftFunctorZero C A).inv.app X) x)))
              (α.naturality
                (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))) }

/-- Extend a map to pull-up over every translated summand. -/
noncomputable def orbitPullupToPushdownAppLinear
    (β : M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N)
    (X : C) :
    orbitPushdownValue (A := A) M X →ₗ[k] N.obj X := by
  classical
  exact DirectSum.toModule k A _ fun b ↦
    (N.map (shiftOrbitFromShift X b)).hom.comp
      (β.app ((shiftFunctor C b).obj X)).hom

omit [∀ a : A, (shiftFunctor C a).Linear k]
  [CategoryTheory.Linear k C]
  [M.Additive] [M.Linear k] [N.Additive] [N.Linear k] in
@[simp]
theorem orbitPullupToPushdownAppLinear_lof
    (β : M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N)
    (X : C) (b : A) (x : M.obj ((shiftFunctor C b).obj X)) :
    orbitPullupToPushdownAppLinear β X (orbitPushdownLof M X b x) =
      N.map (shiftOrbitFromShift X b)
        (β.app ((shiftFunctor C b).obj X) x) := by
  classical
  rw [orbitPullupToPushdownAppLinear, orbitPushdownLof,
    DirectSum.toModule_lof]
  rfl

omit [∀ a : A, (shiftFunctor C a).Linear k]
  [CategoryTheory.Linear k C]
  [M.Additive] [M.Linear k] [N.Additive] [N.Linear k] in
theorem orbitPullupToPushdownAppLinear_naturality_homogeneous
    (β : M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N)
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    (orbitPullupToPushdownAppLinear β Y).comp
        (orbitPushdownHomogeneousMap M a f) =
      (N.map (shiftOrbitOf X Y a f)).hom.comp
        (orbitPullupToPushdownAppLinear β X) := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change orbitPullupToPushdownAppLinear β Y
      (orbitPushdownHomogeneousMap M a f
        (orbitPushdownLof M X b x)) =
    N.map (shiftOrbitOf X Y a f)
      (orbitPullupToPushdownAppLinear β X
        (orbitPushdownLof M X b x))
  rw [orbitPushdownHomogeneousMap_lof,
    orbitPullupToPushdownAppLinear_lof,
    orbitPullupToPushdownAppLinear_lof]
  let h := orbitPushdownArrow' (rfl : a + b = a + b) f
  have hβ := congrArg (fun q ↦ q.hom x) (β.naturality h)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hβ
  change
    N.map (shiftOrbitFromShift Y (a + b))
        (β.app ((shiftFunctor C (a + b)).obj Y) (M.map h x)) =
      N.map (shiftOrbitOf X Y a f)
        (N.map (shiftOrbitFromShift X b)
          (β.app ((shiftFunctor C b).obj X) x))
  rw [hβ]
  change
    (N.map
        (shiftOrbitOf ((shiftFunctor C b).obj X)
          ((shiftFunctor C (a + b)).obj Y) 0
          (shiftHomZero (A := A) h)) ≫
      N.map (shiftOrbitFromShift Y (a + b)))
        (β.app ((shiftFunctor C b).obj X) x) =
      (N.map (shiftOrbitFromShift X b) ≫
        N.map (shiftOrbitOf X Y a f))
          (β.app ((shiftFunctor C b).obj X) x)
  rw [← N.map_comp, ← N.map_comp]
  exact congrArg (fun q ↦ N.map q
    (β.app ((shiftFunctor C b).obj X) x))
      (orbitPushdownArrow_comp_fromShift a b f)

omit [N.Linear k] in
theorem orbitPullupToPushdownAppLinear_naturality
    (β : M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N)
    {X Y : C} (f : ShiftOrbitHom A X Y) :
    (orbitPullupToPushdownAppLinear β Y).comp
        (orbitPushdownMapLinear M f) =
      (N.map f).hom.comp (orbitPullupToPushdownAppLinear β X) := by
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · ext x
    simp
  · intro a fa
    change (orbitPullupToPushdownAppLinear β Y).comp
        (orbitPushdownMapLinear M (shiftOrbitOf X Y a fa)) =
      (N.map (shiftOrbitOf X Y a fa)).hom.comp
        (orbitPullupToPushdownAppLinear β X)
    rw [orbitPushdownMapLinear_of]
    exact orbitPullupToPushdownAppLinear_naturality_homogeneous β a fa
  · intro f g hf hg
    rw [map_add, N.map_add]
    apply LinearMap.ext
    intro x
    simpa using congrArg₂ (.+.) (LinearMap.congr_fun hf x)
      (LinearMap.congr_fun hg x)

/-- The extension of a pull-up map is a natural transformation out of
push-down. -/
noncomputable def orbitPullupToPushdown
    (β : M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N) :
    orbitPushdown (A := A) M ⟶ N where
  app X := ModuleCat.ofHom (orbitPullupToPushdownAppLinear β X)
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    exact orbitPullupToPushdownAppLinear_naturality β f

set_option backward.isDefEq.respectTransparency false in
theorem orbitPushdownFromShift_zero_lof_of_hasShift
    (M : C ⥤ ModuleCat.{max w uM} k) [M.Additive] [M.Linear k]
    (X : C) (b : A) (x : M.obj ((shiftFunctor C b).obj X)) :
    orbitPushdownMapLinear M (shiftOrbitFromShift X b)
        (orbitPushdownLof M ((shiftFunctor C b).obj X) 0
          (M.map ((shiftFunctorZero C A).inv.app
            ((shiftFunctor C b).obj X)) x)) =
      orbitPushdownLof M X b x := by
  classical
  let x₀ : M.obj ((Functor.id C).obj
      ((shiftFunctor C b).obj X)) := x
  rw [shiftOrbitFromShift, orbitPushdownMapLinear_of]
  change
    orbitPushdownHomogeneousMap M b (𝟙 ((shiftFunctor C b).obj X))
        (orbitPushdownLof M ((shiftFunctor C b).obj X) 0
          (M.map ((shiftFunctorZero C A).inv.app
            ((shiftFunctor C b).obj X)) x₀)) =
      orbitPushdownLof M X b x₀
  rw [orbitPushdownHomogeneousMap_lof]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_zero b)
  apply (orbitPushdownComponent_apply_heq_component'_apply M
    (add_zero b) (𝟙 ((shiftFunctor C b).obj X))
      (M.map ((shiftFunctorZero C A).inv.app
        ((shiftFunctor C b).obj X)) x)).trans
  apply heq_of_eq
  change M.map
      (orbitPushdownArrow' (add_zero b) (𝟙 ((shiftFunctor C b).obj X)))
        (M.map ((shiftFunctorZero C A).inv.app
          ((shiftFunctor C b).obj X)) x) = x
  simp only [orbitPushdownArrow', shiftFunctorAdd'_add_zero_inv_app]
  rw [(shiftFunctor C 0).map_id, Category.id_comp]
  change (M.map ((shiftFunctorZero C A).inv.app
      ((shiftFunctor C b).obj X)) ≫
    M.map ((shiftFunctorZero C A).hom.app
      ((shiftFunctor C b).obj X))) x = x
  rw [← M.map_comp, Iso.inv_hom_id_app, M.map_id]
  rfl

omit [N.Additive] [N.Linear k] in
/-- Maps out of push-down are determined by their restrictions to normalized
degree-zero summands. -/
theorem orbitPushdownNatTrans_ext_zero_target
    (α β : orbitPushdown (A := A) M ⟶ N)
    (hzero : ∀ (X : C) (x : M.obj X),
      α.app X
          (orbitPushdownLof M X 0
            (M.map ((shiftFunctorZero C A).inv.app X) x)) =
        β.app X
          (orbitPushdownLof M X 0
            (M.map ((shiftFunctorZero C A).inv.app X) x))) :
    α = β := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  let Y := (shiftFunctor C b).obj X
  let q : ShiftOrbitHom A Y X := shiftOrbitFromShift (C := C) X b
  let z := orbitPushdownLof M Y 0
    (M.map ((shiftFunctorZero C A).inv.app Y) x)
  have hM : orbitPushdownMapLinear M q z =
      orbitPushdownLof M X b x :=
    by simpa [q, z, Y] using
      orbitPushdownFromShift_zero_lof_of_hasShift M X b x
  have hα := congrArg (fun f ↦ f.hom z) (α.naturality q)
  have hβ := congrArg (fun f ↦ f.hom z) (β.naturality q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hα hβ
  change α.app X (orbitPushdownLof M X b x) =
    β.app X (orbitPushdownLof M X b x)
  calc
    _ = α.app X (orbitPushdownMapLinear M q z) :=
      congrArg (α.app X) hM.symm
    _ = N.map q (α.app Y z) := hα
    _ = N.map q (β.app Y z) := by
      apply congrArg (N.map q)
      exact hzero Y x
    _ = β.app X (orbitPushdownMapLinear M q z) := hβ.symm
    _ = _ := congrArg (β.app X) hM

omit [N.Linear k] in
theorem orbitPullupToPushdown_orbitPushdownToPullup
    (α : orbitPushdown (A := A) M ⟶ N) :
    orbitPullupToPushdown (orbitPushdownToPullup α) = α := by
  apply orbitPushdownNatTrans_ext_zero_target
  intro X x
  change orbitPullupToPushdownAppLinear (orbitPushdownToPullup α) X
      (orbitPushdownLof M X 0
        (M.map ((shiftFunctorZero C A).inv.app X) x)) =
    α.app X
      (orbitPushdownLof M X 0
        (M.map ((shiftFunctorZero C A).inv.app X) x))
  rw [orbitPullupToPushdownAppLinear_lof]
  let x₀ := M.map ((shiftFunctorZero C A).inv.app X) x
  let Y := (shiftFunctor C (0 : A)).obj X
  let q : ShiftOrbitHom A Y X := shiftOrbitFromShift (C := C) X (0 : A)
  let z := orbitPushdownLof M Y 0
    (M.map ((shiftFunctorZero C A).inv.app Y) x₀)
  have hM : orbitPushdownMapLinear M q z =
      orbitPushdownLof M X 0 x₀ := by
    simpa [q, z, Y] using
      orbitPushdownFromShift_zero_lof_of_hasShift M X (0 : A) x₀
  have hα := congrArg (fun f ↦ f.hom z) (α.naturality q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hα
  change N.map q (α.app Y z) = α.app X (orbitPushdownLof M X 0 x₀)
  calc
    _ = α.app X (orbitPushdownMapLinear M q z) := hα.symm
    _ = _ := congrArg (α.app X) hM

set_option backward.isDefEq.respectTransparency false in
theorem identityZeroInv_comp_shiftOrbitFromShift (X : C) :
    shiftOrbitCompHom
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := A)).map
            ((shiftFunctorZero C A).inv.app X))
        (shiftOrbitFromShift X (0 : A)) =
      shiftOrbitId X := by
  classical
  change shiftOrbitCompHom
      (shiftOrbitOf X ((shiftFunctor C (0 : A)).obj X) 0
        (shiftHomZero (A := A) ((shiftFunctorZero C A).inv.app X)))
      (shiftOrbitOf ((shiftFunctor C (0 : A)).obj X) X 0 (𝟙 _)) =
    shiftOrbitOf X X 0 (shiftHomId X)
  rw [shiftOrbitCompHom_of_of]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add (0 : A))
  refine (shiftHomComp_heq_shiftHomComp' (zero_add (0 : A))
    (shiftHomZero (A := A) ((shiftFunctorZero C A).inv.app X))
      (𝟙 _)).trans (heq_of_eq ?_)
  simp [shiftHomComp', shiftHomZero, shiftHomId,
    CategoryTheory.ShiftedHom.mk₀,
    shiftFunctorAdd'_zero_add_inv_app]
  have hz (h0 : (0 : A) = 0) :
      shiftFunctorZero' C 0 h0 = shiftFunctorZero C A := by
    rw [Subsingleton.elim h0 rfl]
    ext
    simp [shiftFunctorZero']
  rw [hz]
  rw [← (shiftFunctorZero C A).inv.naturality]
  simp

omit [N.Linear k] in
theorem orbitPushdownToPullup_orbitPullupToPushdown
    (β : M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N) :
    orbitPushdownToPullup (orbitPullupToPushdown β) = β := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change orbitPullupToPushdownAppLinear β X
      (orbitPushdownLof M X 0
        (M.map ((shiftFunctorZero C A).inv.app X) x)) =
    β.app X x
  rw [orbitPullupToPushdownAppLinear_lof]
  let h := (shiftFunctorZero C A).inv.app X
  have hβ := congrArg (fun q ↦ q.hom x) (β.naturality h)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hβ
  rw [hβ]
  change
    (N.map
        ((ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := A)).map h) ≫
      N.map (shiftOrbitFromShift X (0 : A))) (β.app X x) = β.app X x
  rw [← N.map_comp]
  have hcomp := identityZeroInv_comp_shiftOrbitFromShift
    (A := A) X
  change N.map
      (((ShiftOrbitCategory.identityComponentFunctor
        (C := C) (A := A)).map h) ≫
        shiftOrbitFromShift X (0 : A)) (β.app X x) = β.app X x
  have hcomp' :
      (ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := A)).map ((shiftFunctorZero C A).inv.app X) ≫
        shiftOrbitFromShift X (0 : A) =
      𝟙 (show ShiftOrbitCategory C A from X) := hcomp
  rw [show h = (shiftFunctorZero C A).inv.app X by rfl, hcomp']
  have hn := N.map_id (show ShiftOrbitCategory C A from X)
  exact congrArg (fun q ↦ q.hom (β.app X x)) hn

/-- The push-down/pull-up Hom correspondence. -/
noncomputable def orbitPushdownPullupEquiv :
    (orbitPushdown (A := A) M ⟶ N) ≃
      (M ⟶ ShiftOrbitCategory.identityComponentFunctor ⋙ N) where
  toFun := orbitPushdownToPullup
  invFun := orbitPullupToPushdown
  left_inv := orbitPullupToPushdown_orbitPushdownToPullup
  right_inv := orbitPushdownToPullup_orbitPullupToPushdown

omit [N.Additive] [N.Linear k] in
theorem orbitPushdownToPullup_comp
    {P : ShiftOrbitCategory C A ⥤ ModuleCat.{max w uM} k}
    [P.Additive] [P.Linear k]
    (α : orbitPushdown (A := A) M ⟶ N) (g : N ⟶ P) :
    orbitPushdownToPullup (α ≫ g) =
      orbitPushdownToPullup α ≫
        Functor.whiskerLeft
          ShiftOrbitCategory.identityComponentFunctor g := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  rfl

omit [N.Additive] [N.Linear k] in
theorem orbitPushdownToPullup_orbitPushdownNatTrans_comp
    {L : C ⥤ ModuleCat.{max w uM} k} [L.Additive] [L.Linear k]
    (f : L ⟶ M) (α : orbitPushdown (A := A) M ⟶ N) :
    orbitPushdownToPullup (orbitPushdownNatTrans (A := A) f ≫ α) =
      f ≫ orbitPushdownToPullup α := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    α.app X
        (orbitPushdownNatTransAppLinear (A := A) f X
          (orbitPushdownLof L X 0
            (L.map ((shiftFunctorZero C A).inv.app X) x))) =
      (orbitPushdownToPullup α).app X (f.app X x)
  rw [orbitPushdownNatTransAppLinear_lof]
  have hf := congrArg (fun q ↦ q.hom x)
    (f.naturality ((shiftFunctorZero C A).inv.app X))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hf
  change α.app X
      (orbitPushdownLof M X 0
        (f.app ((shiftFunctor C 0).obj X)
          (L.map ((shiftFunctorZero C A).inv.app X) x))) =
    α.app X
      (orbitPushdownLof M X 0
        (M.map ((shiftFunctorZero C A).inv.app X) (f.app X x)))
  exact congrArg (fun y ↦ α.app X (orbitPushdownLof M X 0 y)) hf

/-- The Hom correspondence lifted to the full subcategories of additive
linear modules. -/
noncomputable def linearModuleOrbitPushdownPullupEquiv
    (M₀ : LinearModuleCategory.{u, v, uK, max w uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) :
    ((linearModuleOrbitPushdown
        (k := k) (C := C) (A := A)).obj M₀ ⟶ N₀) ≃
      (M₀ ⟶ (linearModuleOrbitPullup
        (k := k) (C := C) (A := A)).obj N₀) where
  toFun α := ObjectProperty.homMk (orbitPushdownToPullup α.hom)
  invFun β := ObjectProperty.homMk (orbitPullupToPushdown β.hom)
  left_inv α := by
    apply ObjectProperty.hom_ext
    exact orbitPullupToPushdown_orbitPushdownToPullup α.hom
  right_inv β := by
    apply ObjectProperty.hom_ext
    exact orbitPushdownToPullup_orbitPullupToPushdown β.hom

/-- Gabriel push-down is left adjoint to pull-up along the degree-zero orbit
functor. -/
noncomputable def linearModuleOrbitPushdownPullupAdjunction :
    (linearModuleOrbitPushdown
        (k := k) (C := C) (A := A) :
      LinearModuleCategory.{u, v, uK, max w uM} (C := C) k ⥤
        LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := ShiftOrbitCategory C A) k) ⊣
      linearModuleOrbitPullup (k := k) (C := C) (A := A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := linearModuleOrbitPushdownPullupEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply (linearModuleOrbitPushdownPullupEquiv X' Y).injective
        rw [Equiv.apply_symm_apply]
        apply ObjectProperty.hom_ext
        change f.hom ≫ g.hom =
          orbitPushdownToPullup
            (orbitPushdownNatTrans (A := A) f.hom ≫
              orbitPullupToPushdown g.hom)
        rw [orbitPushdownToPullup_orbitPushdownNatTrans_comp,
          orbitPushdownToPullup_orbitPullupToPushdown]
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply ObjectProperty.hom_ext
        exact orbitPushdownToPullup_comp f.hom g.hom }

end MagnitudeConjecture.CoveringHom
