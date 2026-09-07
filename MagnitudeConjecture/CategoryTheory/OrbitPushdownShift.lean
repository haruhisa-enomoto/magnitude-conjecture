import MagnitudeConjecture.CategoryTheory.OrbitPushdownFunctor
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Translation invariance of Gabriel push-down

The push-down of a translated module is canonically isomorphic to the
push-down of the original module.  For a possibly noncommutative additive
group, the `b`-summand of the translated push-down is reindexed as the
`(b-a)`-summand of the original push-down.  Shift associativity proves that
this right reindexing commutes with the left degree translation used by
orbit morphisms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

section Reindex

variable {R : Type uK} [Semiring R]
variable {B : Type w} [AddGroup B]
variable (V : B → Type uM)
variable [∀ b, AddCommMonoid (V b)] [∀ b, Module R (V b)]

/-- Reindex a direct sum by right subtraction in an additive group. -/
noncomputable def directSumAddRightEquiv (a : B) :
    (DirectSum B fun b ↦ V (b + -a)) ≃ₗ[R]
      DirectSum B (fun b ↦ V b) := by
  let e := (DirectSum.lequivCongrLeft R
    (M := V) (Equiv.addRight a)).symm
  refine
    { toFun := fun x ↦ e x
      invFun := fun y ↦ e.symm y
      left_inv := fun x ↦ e.left_inv x
      right_inv := fun y ↦ e.right_inv y
      map_add' := fun x y ↦ e.map_add x y
      map_smul' := fun r x ↦ e.map_smul r x }

@[simp]
theorem directSumAddRightEquiv_lof [DecidableEq B]
    (a b : B) (x : V (b + -a)) :
    directSumAddRightEquiv (R := R) V a
        (DirectSum.lof R B (fun c ↦ V (c + -a)) b x) =
      DirectSum.lof R B (fun c ↦ V c) (b + -a) x := by
  classical
  unfold directSumAddRightEquiv
  exact DirectSum.lequivCongrLeft_symm_lof R

end Reindex

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A]
variable (D : ShiftMkCore C A)
variable [∀ a : A, (D.F a).Additive]
variable [∀ a : A, (D.F a).Linear k]

variable (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)

/-- A shift constructed from an additive `ShiftMkCore` has additive shift
functors. -/
theorem shiftMkCoreAdditiveShift :
    letI := hasShiftMk C A D
    ∀ a : A, (shiftFunctor C a).Additive := by
  letI := hasShiftMk C A D
  intro a
  change (D.F a).Additive
  infer_instance

omit [∀ a : A, (D.F a).Additive] in
/-- A shift constructed from a linear `ShiftMkCore` has linear shift
functors. -/
theorem shiftMkCoreLinearShift :
    letI := hasShiftMk C A D
    ∀ a : A, (shiftFunctor C a).Linear k := by
  letI := hasShiftMk C A D
  intro a
  change (D.F a).Linear k
  infer_instance

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [∀ a : A, (D.F a).Additive]
  [∀ a : A, (D.F a).Linear k] in
/-- Shift associativity is exactly the arrow compatibility needed by the
right-reindexing of push-down summands. -/
theorem orbitPushdownArrow_shift_reindex
    {X Y : C} (a c b : A) :
    letI := hasShiftMk C A D
    ∀ (f : ShiftHom X Y c),
    (shiftFunctor C (-a)).map (orbitPushdownArrow' rfl f) ≫
        (shiftFunctorAdd' C (c + b) (-a) (c + b + -a) rfl).inv.app Y =
      (shiftFunctorAdd' C b (-a) (b + -a) rfl).inv.app X ≫
        orbitPushdownArrow' (add_assoc c b (-a)).symm f := by
  letI := hasShiftMk C A D
  intro f
  simp only [orbitPushdownArrow', Functor.map_comp, Category.assoc]
  rw [shiftFunctorAdd'_assoc_inv_app c b (-a)
    (c + b) (b + -a) (c + b + -a) rfl rfl rfl]
  have hn :=
    (shiftFunctorAdd' C b (-a) (b + -a) rfl).inv.naturality_assoc f
      ((shiftFunctorAdd' C c (b + -a) (c + b + -a)
        (add_assoc c b (-a)).symm).inv.app Y)
  simp only [Functor.comp_map] at hn
  rw [hn]

/-- The value of a shifted module at the `b`-translated object is the
`(b-a)`-translated value of the original module. -/
noncomputable def shiftedOrbitSummandEquiv (a b : A) (X : C) :
    letI := linearModuleCategoryHasShift (k := k) D
    ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
        ((D.F b).obj X) ≃ₗ[k]
      M.obj.obj ((D.F (b + -a)).obj X) := by
  letI := linearModuleCategoryHasShift (k := k) D
  exact (((linearModuleShiftUnderlyingIso (k := k) D M a).app
    ((D.F b).obj X)).trans
      (M.obj.mapIso ((D.add b (-a)).symm.app X))).toLinearEquiv

/-- Objectwise reindexing isomorphism between the push-down of a shift and
the push-down of the original module. -/
noncomputable def shiftedOrbitPushdownValueEquiv (a : A) (X : C) :
    letI := hasShiftMk C A D
    letI := linearModuleCategoryHasShift (k := k) D
    orbitPushdownValue (A := A)
        ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X ≃ₗ[k]
      orbitPushdownValue (A := A) M.obj X := by
  letI := hasShiftMk C A D
  letI := linearModuleCategoryHasShift (k := k) D
  let e₁ :
      orbitPushdownValue (A := A)
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X ≃ₗ[k]
        (DirectSum A fun b ↦
          M.obj.obj ((shiftFunctor C (b + -a)).obj X)) :=
    DFinsupp.mapRange.linearEquiv fun b ↦
      shiftedOrbitSummandEquiv D M a b X
  let e₂ :
      (DirectSum A fun b ↦
        M.obj.obj ((shiftFunctor C (b + -a)).obj X)) ≃ₗ[k]
        orbitPushdownValue (A := A) M.obj X :=
    directSumAddRightEquiv
      (fun c ↦ M.obj.obj ((shiftFunctor C c).obj X)) a
  exact e₁.trans e₂

@[simp]
theorem shiftedOrbitPushdownValueEquiv_lof
    (a b : A) (X : C) :
    letI := hasShiftMk C A D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (x : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
      ((D.F b).obj X)),
    shiftedOrbitPushdownValueEquiv D M a X
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X b x) =
      orbitPushdownLof M.obj X (b + -a)
        (shiftedOrbitSummandEquiv D M a b X x) := by
  letI := hasShiftMk C A D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  intro x
  change directSumAddRightEquiv
      (fun c ↦ M.obj.obj ((shiftFunctor C c).obj X)) a
      ((DFinsupp.mapRange.linearEquiv fun c ↦
        shiftedOrbitSummandEquiv D M a c X)
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X b x)) = _
  rw [show
    (DFinsupp.mapRange.linearEquiv fun c ↦
      shiftedOrbitSummandEquiv D M a c X)
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X b x) =
      DirectSum.lof k A
        (fun c ↦ M.obj.obj ((shiftFunctor C (c + -a)).obj X)) b
        (shiftedOrbitSummandEquiv D M a b X x) by
          change DFinsupp.mapRange
              (fun c y ↦ shiftedOrbitSummandEquiv D M a c X y)
              (fun c ↦ (shiftedOrbitSummandEquiv D M a c X).map_zero)
              (DFinsupp.single b x) =
            DFinsupp.single b (shiftedOrbitSummandEquiv D M a b X x)
          exact DFinsupp.mapRange_single]
  exact directSumAddRightEquiv_lof
    (R := k) (fun c ↦ M.obj.obj ((shiftFunctor C c).obj X)) a b _

set_option backward.isDefEq.respectTransparency false in
/-- The summand reindexing intertwines a homogeneous push-down component. -/
theorem shiftedOrbitComponent_reindex
    {X Y : C} (a c b : A) :
    letI := hasShiftMk C A D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (f : ShiftHom X Y c),
    (shiftedOrbitSummandEquiv D M a (c + b) Y).toLinearMap.comp
        (orbitPushdownComponent
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) c b f) =
      (orbitPushdownComponent' M.obj (add_assoc c b (-a)).symm f).comp
        (shiftedOrbitSummandEquiv D M a b X).toLinearMap := by
  letI := hasShiftMk C A D
  letI := linearModuleCategoryHasShift (k := k) D
  intro f
  let U := linearModuleShiftUnderlyingIso (k := k) D M a
  let q : (shiftFunctor C b).obj X ⟶
      (shiftFunctor C (c + b)).obj Y :=
    orbitPushdownArrow' rfl f
  let q' : (shiftFunctor C (b + -a)).obj X ⟶
      (shiftFunctor C (c + b + -a)).obj Y :=
    orbitPushdownArrow' (add_assoc c b (-a)).symm f
  have hcat :
      ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).map q ≫
          U.hom.app ((shiftFunctor C (c + b)).obj Y) ≫
          M.obj.map ((D.add (c + b) (-a)).inv.app Y) =
        U.hom.app ((shiftFunctor C b).obj X) ≫
          M.obj.map ((D.add b (-a)).inv.app X) ≫
          M.obj.map q' := by
    have hq :
        (D.F (-a)).map q ≫ (D.add (c + b) (-a)).inv.app Y =
          (D.add b (-a)).inv.app X ≫ q' := by
      simpa only [q, q', shiftFunctorAdd'_eq_shiftFunctorAdd,
        D.shiftFunctorAdd_eq, D.shiftFunctor_eq] using
          orbitPushdownArrow_shift_reindex D a c b f
    rw [U.hom.naturality_assoc]
    simp only [Functor.comp_map, ← M.obj.map_comp]
    rw [hq]
  have hlin := congrArg (fun h ↦ h.hom) hcat
  simp only [ModuleCat.hom_comp] at hlin
  simpa [shiftedOrbitSummandEquiv, orbitPushdownComponent,
    orbitPushdownComponent', LinearMap.comp_assoc, D.shiftFunctor_eq,
    q, q', U] using hlin

/-- The value reindexing commutes with each homogeneous morphism in the
shift-orbit category. -/
theorem shiftedOrbitPushdownValueEquiv_naturality_homogeneous
    {X Y : C} (a c : A) :
    letI := hasShiftMk C A D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (f : ShiftHom X Y c),
    (shiftedOrbitPushdownValueEquiv D M a Y).toLinearMap.comp
        (orbitPushdownHomogeneousMap
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) c f) =
      (orbitPushdownHomogeneousMap M.obj c f).comp
        (shiftedOrbitPushdownValueEquiv D M a X).toLinearMap := by
  letI := hasShiftMk C A D
  letI := linearModuleCategoryHasShift (k := k) D
  intro f
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change shiftedOrbitPushdownValueEquiv D M a Y
      (orbitPushdownHomogeneousMap
        ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) c f
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X b x)) =
    orbitPushdownHomogeneousMap M.obj c f
      (shiftedOrbitPushdownValueEquiv D M a X
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X b x))
  rw [orbitPushdownHomogeneousMap_lof,
    shiftedOrbitPushdownValueEquiv_lof,
    shiftedOrbitPushdownValueEquiv_lof,
    orbitPushdownHomogeneousMap_lof]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_assoc c b (-a))
  exact
    (heq_of_eq (DFunLike.congr_fun
      (shiftedOrbitComponent_reindex D M a c b f) x)).trans
      (orbitPushdownComponent_apply_heq_component'_apply M.obj
        (add_assoc c b (-a)).symm f
        (shiftedOrbitSummandEquiv D M a b X x)).symm

/-- The value reindexing is natural for every finite-support orbit
morphism. -/
theorem shiftedOrbitPushdownValueEquiv_naturality
    {X Y : C} (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
      (M⟦a⟧).property.1
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
      (M⟦a⟧).property.2
    ∀ (f : ShiftOrbitHom A X Y),
    (shiftedOrbitPushdownValueEquiv D M a Y).toLinearMap.comp
        (orbitPushdownMapLinear
          ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) f) =
      (orbitPushdownMapLinear M.obj f).comp
        (shiftedOrbitPushdownValueEquiv D M a X).toLinearMap := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
    (M⟦a⟧).property.1
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
    (M⟦a⟧).property.2
  intro f
  classical
  induction f using DirectSum.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      apply LinearMap.ext
      intro x
      change shiftedOrbitPushdownValueEquiv D M a Y 0 = 0
      exact map_zero _
  | of c fc =>
      change
        (shiftedOrbitPushdownValueEquiv D M a Y).toLinearMap.comp
            (orbitPushdownMapLinear
              ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧))
              (shiftOrbitOf X Y c fc)) =
          (orbitPushdownMapLinear M.obj (shiftOrbitOf X Y c fc)).comp
            (shiftedOrbitPushdownValueEquiv D M a X).toLinearMap
      rw [orbitPushdownMapLinear_of, orbitPushdownMapLinear_of]
      exact shiftedOrbitPushdownValueEquiv_naturality_homogeneous
        D M a c fc
  | add f g hf hg =>
      rw [map_add, map_add]
      apply LinearMap.ext
      intro x
      simpa only [LinearMap.comp_apply, LinearMap.add_apply, map_add] using
        congrArg₂ (.+.) (LinearMap.congr_fun hf x)
          (LinearMap.congr_fun hg x)

/-- Push-down is invariant under translating the upstairs module. -/
noncomputable def shiftedOrbitPushdownIso (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
      (M⟦a⟧).property.1
    letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
      (M⟦a⟧).property.2
    orbitPushdown (A := A)
        ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) ≅
      orbitPushdown (A := A) M.obj := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Additive :=
    (M⟦a⟧).property.1
  letI : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).Linear k :=
    (M⟦a⟧).property.2
  exact NatIso.ofComponents
    (fun X ↦ (shiftedOrbitPushdownValueEquiv D M a
      (show C from X)).toModuleIso)
    (fun {X Y} f ↦ by
      apply ModuleCat.hom_ext
      change
        (shiftedOrbitPushdownValueEquiv D M a
          (show C from Y)).toLinearMap.comp
            (orbitPushdownMapLinear
              ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) f) =
          (orbitPushdownMapLinear M.obj f).comp
            (shiftedOrbitPushdownValueEquiv D M a
              (show C from X)).toLinearMap
      exact shiftedOrbitPushdownValueEquiv_naturality D M a f)

end MagnitudeConjecture.CoveringHom
