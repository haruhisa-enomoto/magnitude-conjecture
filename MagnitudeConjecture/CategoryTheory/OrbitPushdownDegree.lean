import MagnitudeConjecture.CategoryTheory.OrbitPushdownDescent

/-!
# Degree extraction from Gabriel push-down transformations

A natural transformation between two orbit push-down modules has a component
in every deck degree.  This file extracts the degree-`a` component by inserting
the source module in degree zero, applying the transformation, and projecting
to degree `-a`.  Naturality for zero-degree orbit arrows turns the extracted
component into an upstairs module map, and the inverse-precomposition
translation isomorphism turns it into a genuine shifted morphism.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A]
variable (D : ShiftMkCore C A)
variable [∀ a : A, (D.F a).Additive]
variable [∀ a : A, (D.F a).Linear k]

variable {M N : CategoryTheory.Functor C (ModuleCat.{uM} k)}
variable [M.Additive] [M.Linear k] [N.Additive] [N.Linear k]

/-- The `(-a)` output component of a push-down transformation, evaluated on
the zero input component. -/
noncomputable def orbitPushdownNatTransDegreeAppLinear
    (a : A) (X : C) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    (orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) N) →
      (M.obj X →ₗ[k] N.obj ((D.F (-a)).obj X)) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  intro α
  exact (DirectSum.component k A
    (fun b ↦ N.obj ((D.F b).obj X)) (-a)).comp
        ((α.app X).hom.comp
        ((orbitPushdownLof M X 0).comp
          (M.map ((shiftFunctorZero C A).inv.app X)).hom))

omit [Preadditive C] [∀ a : A, (D.F a).Additive] in
set_option backward.isDefEq.respectTransparency false in
theorem shiftFunctorZero_inv_comp_orbitPushdownArrow_zero
    {X Y : C} (h : X ⟶ Y) :
    letI := hasShiftMk C A D
    (shiftFunctorZero C A).inv.app X ≫
        orbitPushdownArrow' (zero_add 0) (shiftHomZero (A := A) h) =
      h ≫ (shiftFunctorZero C A).inv.app Y := by
  letI := hasShiftMk C A D
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
theorem orbitPushdownZeroMap_inclusion
    {X Y : C} (h : X ⟶ Y) (x : M.obj X) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    orbitPushdownMapLinear M
        (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))
        (orbitPushdownLof M X 0
          (M.map ((shiftFunctorZero C A).inv.app X) x)) =
      orbitPushdownLof M Y 0
        (M.map ((shiftFunctorZero C A).inv.app Y) (M.map h x)) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  rw [orbitPushdownMapLinear_of, orbitPushdownHomogeneousMap_lof]
  change DirectSum.of (fun e ↦ M.obj ((D.F e).obj Y)) (0 + 0)
      (M.map (orbitPushdownArrow' rfl (shiftHomZero (A := A) h))
        (M.map ((shiftFunctorZero C A).inv.app X) x)) = _
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add (0 : A))
  apply (orbitPushdownComponent_apply_heq_component'_apply M
    (zero_add (0 : A)) (shiftHomZero (A := A) h)
      (M.map ((shiftFunctorZero C A).inv.app X) x)).trans
  apply heq_of_eq
  change M.map
      (orbitPushdownArrow' (zero_add 0) (shiftHomZero (A := A) h))
        (M.map ((shiftFunctorZero C A).inv.app X) x) = _
  have hmap := congrArg (fun q ↦ M.map q)
    (shiftFunctorZero_inv_comp_orbitPushdownArrow_zero D h)
  simp only [M.map_comp] at hmap
  exact congr($(hmap) x)

omit [Preadditive C] [∀ a : A, (D.F a).Additive] in
set_option backward.isDefEq.respectTransparency false in
theorem orbitPushdownArrow_zero
    {X Y : C} (h : X ⟶ Y) (b : A) :
    letI := hasShiftMk C A D
    orbitPushdownArrow' (zero_add b) (shiftHomZero (A := A) h) =
      (shiftFunctor C b).map h := by
  letI := hasShiftMk C A D
  simp only [orbitPushdownArrow', shiftHomZero,
    CategoryTheory.ShiftedHom.mk₀,
    shiftFunctorAdd'_zero_add_inv_app, Functor.map_comp,
    Category.assoc]
  have hz (h0 : (0 : A) = 0) :
      shiftFunctorZero' C 0 h0 = shiftFunctorZero C A := by
    rw [Subsingleton.elim h0 rfl]
    ext
    simp [shiftFunctorZero']
  rw [hz]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  apply congrArg (fun q ↦ (shiftFunctor C b).map q)
  exact Category.comp_id h

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (D.F a).Additive] [∀ a : A, (D.F a).Linear k]
  [N.Additive] [N.Linear k] in
set_option backward.isDefEq.respectTransparency false in
theorem orbitPushdownHomogeneousMap_zero_lof
    {X Y : C} (h : X ⟶ Y) (b : A)
    (x : N.obj ((D.F b).obj X)) :
    letI := hasShiftMk C A D
    orbitPushdownHomogeneousMap N 0 (shiftHomZero (A := A) h)
        (orbitPushdownLof N X b x) =
      orbitPushdownLof N Y b
        (N.map ((shiftFunctor C b).map h) x) := by
  letI := hasShiftMk C A D
  classical
  rw [orbitPushdownHomogeneousMap_lof]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add b)
  exact
    (orbitPushdownComponent_apply_heq_component'_apply N
      (zero_add b) (shiftHomZero (A := A) h) x).trans
      (heq_of_eq (by
        change N.map
            (orbitPushdownArrow' (zero_add b)
              (shiftHomZero (A := A) h)) x = _
        rw [orbitPushdownArrow_zero D]))

set_option backward.isDefEq.respectTransparency false in
theorem orbitPushdownZeroMap_component
    {X Y : C} (h : X ⟶ Y) (b : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    (DirectSum.component k A
        (fun c ↦ N.obj ((shiftFunctor C c).obj Y)) b).comp
        (orbitPushdownMapLinear N
          (shiftOrbitOf X Y 0 (shiftHomZero (A := A) h))) =
      (N.map ((shiftFunctor C b).map h)).hom.comp
        (DirectSum.component k A
          (fun c ↦ N.obj ((shiftFunctor C c).obj X)) b) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  apply DirectSum.linearMap_ext
  intro c
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [orbitPushdownMapLinear_of]
  change DirectSum.component k A
      (fun c ↦ N.obj ((shiftFunctor C c).obj Y)) b
      (orbitPushdownHomogeneousMap N 0 (shiftHomZero (A := A) h)
        (orbitPushdownLof N X c x)) = _
  rw [orbitPushdownHomogeneousMap_zero_lof D]
  by_cases hcb : c = b
  · subst c
    simp [orbitPushdownLof]
  · simp [orbitPushdownLof, DirectSum.component.of, hcb]

set_option backward.isDefEq.respectTransparency false in
theorem orbitPushdownNatTransDegreeAppLinear_naturality
    (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    ∀ (α : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) N)
      {X Y : C} (h : X ⟶ Y),
      (orbitPushdownNatTransDegreeAppLinear D a Y α).comp
          (M.map h).hom =
        (N.map ((D.F (-a)).map h)).hom.comp
          (orbitPushdownNatTransDegreeAppLinear D a X α) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  intro α X Y h
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change DirectSum.component k A
      (fun b ↦ N.obj ((D.F b).obj Y)) (-a)
      ((α.app Y).hom
        (orbitPushdownLof M Y 0
          (M.map ((shiftFunctorZero C A).inv.app Y) (M.map h x)))) = _
  rw [← orbitPushdownZeroMap_inclusion D h x]
  let q := shiftOrbitOf X Y 0 (shiftHomZero (A := A) h)
  let z := orbitPushdownLof M X 0
    (M.map ((shiftFunctorZero C A).inv.app X) x)
  have hnat :
      (α.app Y).hom (orbitPushdownMapLinear M q z) =
        orbitPushdownMapLinear N q ((α.app X).hom z) := by
    exact congrArg (fun f ↦ f.hom z) (α.naturality q)
  rw [hnat]
  exact LinearMap.congr_fun (orbitPushdownZeroMap_component D h (-a))
    ((α.app X).hom z)

/-- The degree-`a` part recovered from a transformation between two Gabriel
push-down modules, before identifying inverse precomposition with module
translation. -/
noncomputable def orbitPushdownNatTransDegreeRaw (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    (orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) N) →
      (M ⟶ D.F (-a) ⋙ N) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  intro α
  exact
    { app := fun X ↦ ModuleCat.ofHom
        (orbitPushdownNatTransDegreeAppLinear D a X α)
      naturality := fun {X Y} h ↦ by
        apply ModuleCat.hom_ext
        exact orbitPushdownNatTransDegreeAppLinear_naturality D a α h }

/-- The degree-`a` upstairs module map recovered from a transformation between
Gabriel push-downs. -/
noncomputable def linearModuleOrbitPushdownDegree
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀ ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀) →
      ShiftHom M₀ N₀ a := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  intro α
  let β := orbitPushdownNatTransDegreeRaw D a α.hom
  let U := linearModuleShiftUnderlyingIso (k := k) D N₀ a
  exact ObjectProperty.homMk (β ≫ U.inv)

/-- Degree extraction at one object is linear in the push-down
transformation. -/
noncomputable def orbitPushdownNatTransDegreeAppLinearMap
    (a : A) (X : C) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    (orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) N) →ₗ[k]
      (M.obj X →ₗ[k] N.obj ((D.F (-a)).obj X)) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  exact
    { toFun := orbitPushdownNatTransDegreeAppLinear D a X
      map_add' := by
        intro α β
        apply LinearMap.ext
        intro x
        let z := orbitPushdownLof M X 0
          (M.map ((shiftFunctorZero C A).inv.app X) x)
        change (DirectSum.component k A
            (fun b ↦ N.obj ((D.F b).obj X)) (-a))
              ((α.app X).hom z + (β.app X).hom z) = _
        exact (DirectSum.component k A
          (fun b ↦ N.obj ((D.F b).obj X)) (-a)).map_add _ _
      map_smul' := by
        intro r α
        apply LinearMap.ext
        intro x
        let z := orbitPushdownLof M X 0
          (M.map ((shiftFunctorZero C A).inv.app X) x)
        change (DirectSum.component k A
            (fun b ↦ N.obj ((D.F b).obj X)) (-a))
              (r • (α.app X).hom z) = _
        exact (DirectSum.component k A
          (fun b ↦ N.obj ((D.F b).obj X)) (-a)).map_smul r _ }

/-- Extraction of one shifted module map is linear. -/
noncomputable def linearModuleOrbitPushdownDegreeLinear
    (M₀ N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀ ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀) →ₗ[k]
      ShiftHom M₀ N₀ a := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  exact
    { toFun := linearModuleOrbitPushdownDegree D M₀ N₀ a
      map_add' := by
        intro α β
        have hraw :
            orbitPushdownNatTransDegreeRaw D a (α + β).hom =
              orbitPushdownNatTransDegreeRaw D a α.hom +
                orbitPushdownNatTransDegreeRaw D a β.hom := by
          apply NatTrans.ext
          funext X
          apply ModuleCat.hom_ext
          exact (orbitPushdownNatTransDegreeAppLinearMap D a X).map_add
            α.hom β.hom
        apply ObjectProperty.hom_ext
        change orbitPushdownNatTransDegreeRaw D a (α + β).hom ≫
            (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv =
          orbitPushdownNatTransDegreeRaw D a α.hom ≫
              (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv +
            orbitPushdownNatTransDegreeRaw D a β.hom ≫
              (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv
        rw [hraw, Preadditive.add_comp]
      map_smul' := by
        intro r α
        have hraw :
            orbitPushdownNatTransDegreeRaw D a (r • α).hom =
              r • orbitPushdownNatTransDegreeRaw D a α.hom := by
          apply NatTrans.ext
          funext X
          apply ModuleCat.hom_ext
          exact (orbitPushdownNatTransDegreeAppLinearMap D a X).map_smul
            r α.hom
        apply ObjectProperty.hom_ext
        change orbitPushdownNatTransDegreeRaw D a (r • α).hom ≫
            (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv =
          r • (orbitPushdownNatTransDegreeRaw D a α.hom ≫
            (linearModuleShiftUnderlyingIso (k := k) D N₀ a).inv)
        rw [hraw, CategoryTheory.Linear.smul_comp] }

end MagnitudeConjecture.CoveringHom
