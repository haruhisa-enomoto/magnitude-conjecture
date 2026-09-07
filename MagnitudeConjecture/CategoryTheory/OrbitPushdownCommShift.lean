import MagnitudeConjecture.CategoryTheory.OrbitPushdownShift

/-!
# Orbit push-down commutes with deck translations

The target module category is equipped with the trivial shift.  Reindexing
direct-sum components then identifies the push-down of a translated module
with the original push-down.  This file proves naturality and the zero and
addition coherence laws, and packages them as a `Functor.CommShift` structure.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

/-- The coherent trivial shift on a category. -/
def trivialShiftMkCore (E : Type u) [Category.{v} E]
    (A : Type w) [AddMonoid A] : ShiftMkCore E A where
  F _ := Functor.id E
  zero := Iso.refl _
  add _ _ := (Functor.rightUnitor (Functor.id E)).symm
  assoc_hom_app := by simp
  zero_add_hom_app := by simp
  add_zero_hom_app := by simp

/-- A category equipped with the coherent trivial shift. -/
@[implicit_reducible]
def trivialHasShift (E : Type u) [Category.{v} E]
    (A : Type w) [AddMonoid A] : HasShift E A :=
  hasShiftMk E A (trivialShiftMkCore E A)

/-- Any functor between categories carrying the trivial shift commutes with
that shift. -/
@[implicit_reducible]
noncomputable def trivialFunctorCommShift
    {B : Type u} [Category.{v} B]
    {E : Type uM} [Category.{uK} E]
    {A : Type w} [AddMonoid A] (F : B ⥤ E) :
    letI := trivialHasShift B A
    letI := trivialHasShift E A
    F.CommShift A := by
  letI := trivialHasShift B A
  letI := trivialHasShift E A
  refine
    { commShiftIso := fun _ ↦ Functor.CommShift.isoZero F A
      commShiftIso_zero := rfl
      commShiftIso_add := ?_ }
  intro a b
  change Functor.CommShift.isoZero F A =
    Functor.CommShift.isoAdd (Functor.CommShift.isoZero F A)
      (Functor.CommShift.isoZero F A)
  symm
  convert (Functor.CommShift.isoZero_isoAdd'_
    (F := F) (A := A) (a := (0 : A))
    (Functor.CommShift.isoZero F A)) using 1
  unfold Functor.CommShift.isoAdd
  congr

set_option backward.isDefEq.respectTransparency false in
/-- The commutation map for a functor between trivially shifted categories is
the identity on every object. -/
theorem trivialFunctorCommShift_hom_app
    {B : Type u} [Category.{v} B]
    {E : Type uM} [Category.{uK} E]
    {A : Type w} [AddMonoid A]
    (F : B ⥤ E) (a : A) (X : B) :
    letI := trivialHasShift B A
    letI := trivialHasShift E A
    letI : F.CommShift A := trivialFunctorCommShift F
    (F.commShiftIso a).hom.app X = 𝟙 (F.obj X) := by
  letI := trivialHasShift B A
  letI := trivialHasShift E A
  letI : F.CommShift A := trivialFunctorCommShift F
  unfold Functor.commShiftIso
  dsimp [trivialFunctorCommShift, Functor.CommShift.isoZero,
    trivialShiftMkCore, ShiftMkCore.shiftFunctor_eq]
  rw [(trivialShiftMkCore B A).shiftFunctorZero_eq,
    (trivialShiftMkCore E A).shiftFunctorZero_eq]
  simp [trivialShiftMkCore]

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A]
variable (D : ShiftMkCore C A)
variable [∀ a : A, (D.F a).Additive]
variable [∀ a : A, (D.F a).Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing a shifted summand is natural in the linear module. -/
theorem shiftedOrbitSummandEquiv_naturality
    {M N : LinearModuleCategory.{u, v, uK, uM} (C := C) k}
    (f : M ⟶ N) (a b : A) (X : C) :
    letI := hasShiftMk C A D
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (x : ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)).obj
      ((D.F b).obj X)),
    shiftedOrbitSummandEquiv D N a b X
        (((shiftFunctor
          (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a).map f).hom.app
            ((D.F b).obj X) x) =
      f.hom.app ((D.F (b + -a)).obj X)
        (shiftedOrbitSummandEquiv D M a b X x) := by
  letI := hasShiftMk C A D
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  intro x
  let UM := linearModuleShiftUnderlyingIso (k := k) D M a
  let UN := linearModuleShiftUnderlyingIso (k := k) D N a
  let U := (IsLinearModule (C := C) k).ι.commShiftIso a
  have hshift := NatTrans.congr_app (U.hom.naturality f) ((D.F b).obj X)
  change
    (((IsLinearModule (C := C) k).ι.map
      ((shiftFunctor
        (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a).map f)).app
          ((D.F b).obj X)) ≫
        UN.hom.app ((D.F b).obj X) =
      UM.hom.app ((D.F b).obj X) ≫
        f.hom.app ((D.F (-a)).obj ((D.F b).obj X)) at hshift
  have hf := f.hom.naturality ((D.add b (-a)).inv.app X)
  change
    M.obj.map ((D.add b (-a)).inv.app X) ≫
        f.hom.app ((D.F (b + -a)).obj X) =
      f.hom.app ((D.F (-a)).obj ((D.F b).obj X)) ≫
        N.obj.map ((D.add b (-a)).inv.app X) at hf
  have hcat :
      (((IsLinearModule (C := C) k).ι).map
          ((shiftFunctor
            (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a).map f)).app
            ((D.F b).obj X) ≫
        UN.hom.app ((D.F b).obj X) ≫
        N.obj.map ((D.add b (-a)).inv.app X) =
      UM.hom.app ((D.F b).obj X) ≫
        M.obj.map ((D.add b (-a)).inv.app X) ≫
        f.hom.app ((D.F (b + -a)).obj X) := by
    rw [← Category.assoc, hshift]
    simp only [Category.assoc]
    rw [← hf]
  exact congr($(hcat) x)

/-- The direct-sum reindexing is natural in the linear module. -/
theorem shiftedOrbitPushdownValueEquiv_module_naturality
    {M N : LinearModuleCategory.{u, v, uK, uM} (C := C) k}
    (f : M ⟶ N) (a : A) (X : C) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    (shiftedOrbitPushdownValueEquiv D N a X).toLinearMap.comp
        (orbitPushdownNatTransAppLinear (A := A)
          (((shiftFunctor
            (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a).map f).hom) X) =
      (orbitPushdownNatTransAppLinear (A := A) f.hom X).comp
        (shiftedOrbitPushdownValueEquiv D M a X).toLinearMap := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  let sf := ((shiftFunctor
    (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a).map f).hom
  calc
    _ = shiftedOrbitPushdownValueEquiv D N a X
        (orbitPushdownLof
          ((IsLinearModule (C := C) k).ι.obj (N⟦a⟧)) X b
          (sf.app ((D.F b).obj X) x)) :=
      congrArg (shiftedOrbitPushdownValueEquiv D N a X)
        (orbitPushdownNatTransAppLinear_lof
          (A := A) sf X b x)
    _ = orbitPushdownLof N.obj X (b + -a)
        (shiftedOrbitSummandEquiv D N a b X
          (sf.app ((D.F b).obj X) x)) :=
      shiftedOrbitPushdownValueEquiv_lof D N a b X _
    _ = orbitPushdownLof N.obj X (b + -a)
        (f.hom.app ((D.F (b + -a)).obj X)
          (shiftedOrbitSummandEquiv D M a b X x)) :=
      congrArg (orbitPushdownLof N.obj X (b + -a))
        (shiftedOrbitSummandEquiv_naturality D f a b X x)
    _ = orbitPushdownNatTransAppLinear (A := A) f.hom X
        (orbitPushdownLof M.obj X (b + -a)
          (shiftedOrbitSummandEquiv D M a b X x)) :=
      (orbitPushdownNatTransAppLinear_lof
        (A := A) f.hom X (b + -a) _).symm
    _ = orbitPushdownNatTransAppLinear (A := A) f.hom X
        (shiftedOrbitPushdownValueEquiv D M a X
          (orbitPushdownLof
            ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧)) X b x)) :=
      congrArg (orbitPushdownNatTransAppLinear (A := A) f.hom X)
        (shiftedOrbitPushdownValueEquiv_lof D M a b X x).symm

/-- Push-down commutes with a fixed deck translation, before imposing the
zero and addition coherence laws. -/
noncomputable def linearModuleOrbitPushdownCommShiftIso (a : A) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    shiftFunctor
        (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a ⋙
        linearModuleOrbitPushdown (k := k) (C := C) (A := A) ≅
      linearModuleOrbitPushdown (k := k) (C := C) (A := A) ⋙
        shiftFunctor
          (LinearModuleCategory.{u, max v w, uK, max w uM}
            (C := ShiftOrbitCategory C A) k) a := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  classical
  refine NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk
      (P := IsLinearModule (C := ShiftOrbitCategory C A) k)
      (shiftedOrbitPushdownIso D M a)) (naturality := ?_)
  intro M N f
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  change
    (shiftedOrbitPushdownValueEquiv D N a (show C from X)).toLinearMap.comp
        (orbitPushdownNatTransAppLinear (A := A)
          (((shiftFunctor
            (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a).map f).hom)
          (show C from X)) =
      (orbitPushdownNatTransAppLinear (A := A) f.hom
          (show C from X)).comp
        (shiftedOrbitPushdownValueEquiv D M a
          (show C from X)).toLinearMap
  exact shiftedOrbitPushdownValueEquiv_module_naturality
    D f a (show C from X)

set_option backward.isDefEq.respectTransparency false in
/-- The push-down translation isomorphism preserves the zero shift. -/
theorem shiftedOrbitPushdownValueEquiv_zero
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k) (X : C) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    (shiftedOrbitPushdownValueEquiv D M 0 X).toLinearMap =
      orbitPushdownNatTransAppLinear (A := A)
        (((shiftFunctorZero
          (LinearModuleCategory.{u, v, uK, uM} (C := C) k) A).hom.app M).hom) X := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  apply DirectSum.linearMap_ext
  intro c
  apply LinearMap.ext
  intro x
  change ((IsLinearModule (C := C) k).ι.obj (M⟦0⟧)).obj
    ((D.F c).obj X) at x
  change shiftedOrbitPushdownValueEquiv D M 0 X
      (orbitPushdownLof
        ((IsLinearModule (C := C) k).ι.obj (M⟦0⟧)) X c x) =
    orbitPushdownNatTransAppLinear (A := A)
      (((shiftFunctorZero
        (LinearModuleCategory.{u, v, uK, uM} (C := C) k) A).hom.app M).hom) X
      (orbitPushdownLof
        ((IsLinearModule (C := C) k).ι.obj (M⟦0⟧)) X c x)
  rw [shiftedOrbitPushdownValueEquiv_lof]
  let α := ((shiftFunctorZero
    (LinearModuleCategory.{u, v, uK, uM} (C := C) k) A).hom.app M).hom
  have hα := orbitPushdownNatTransAppLinear_lof
    (A := A) α X c x
  apply Eq.trans ?_ hα.symm
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (by simp)
  let U := linearModuleShiftUnderlyingIso (k := k) D M 0
  have hzero := congrArg Iso.hom
    ((IsLinearModule (C := C) k).ι.commShiftIso_zero A)
  have hzeroM := NatTrans.congr_app hzero M
  have hzeroX := NatTrans.congr_app hzeroM ((D.F c).obj X)
  simp only [Functor.CommShift.isoZero_hom_app] at hzeroX
  change U.hom.app ((D.F c).obj X) =
    α.app ((D.F c).obj X) ≫
      ((shiftFunctorZero (C ⥤ ModuleCat.{uM} k) A).inv.app M.obj).app
        ((D.F c).obj X) at hzeroX
  have hzeroApply := congr($(hzeroX) x)
  change HEq
    (M.obj.map ((D.add c (-0)).inv.app X)
      (U.hom.app ((D.F c).obj X) x))
    (α.app ((D.F c).obj X) x)
  rw [hzeroApply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact functorCategory_shiftFunctorZero_inv_add_apply
    (k := k) D M.obj c X (α.app ((D.F c).obj X) x)

set_option backward.isDefEq.respectTransparency false in
/-- The push-down translation isomorphisms preserve addition of shifts. -/
theorem shiftedOrbitPushdownValueEquiv_add
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (a b : A) (X : C) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    (shiftedOrbitPushdownValueEquiv D M (a + b) X).toLinearMap =
      (shiftedOrbitPushdownValueEquiv D M a X).toLinearMap.comp
        ((shiftedOrbitPushdownValueEquiv D (M⟦a⟧) b X).toLinearMap.comp
          (orbitPushdownNatTransAppLinear (A := A)
            (((shiftFunctorAdd
              (LinearModuleCategory.{u, v, uK, uM} (C := C) k)
              a b).hom.app M).hom) X)) := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  apply DirectSum.linearMap_ext
  intro c
  apply LinearMap.ext
  intro x
  change ((IsLinearModule (C := C) k).ι.obj (M⟦a + b⟧)).obj
    ((D.F c).obj X) at x
  simp only [LinearMap.comp_apply]
  change shiftedOrbitPushdownValueEquiv D M (a + b) X
      (orbitPushdownLof
        ((IsLinearModule (C := C) k).ι.obj (M⟦a + b⟧)) X c x) =
    shiftedOrbitPushdownValueEquiv D M a X
      (shiftedOrbitPushdownValueEquiv D (M⟦a⟧) b X
        (orbitPushdownNatTransAppLinear (A := A)
          (((shiftFunctorAdd
            (LinearModuleCategory.{u, v, uK, uM} (C := C) k)
            a b).hom.app M).hom) X
          (orbitPushdownLof
            ((IsLinearModule (C := C) k).ι.obj (M⟦a + b⟧)) X c x)))
  let s := (((shiftFunctorAdd
    (LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    a b).hom.app M).hom)
  have hs := orbitPushdownNatTransAppLinear_lof
    (A := A) s X c x
  let Uab := linearModuleShiftUnderlyingIso (k := k) D M (a + b)
  let Ua := linearModuleShiftUnderlyingIso (k := k) D M a
  let Ub := linearModuleShiftUnderlyingIso (k := k) D (M⟦a⟧) b
  have hadd := congrArg Iso.hom
    ((IsLinearModule (C := C) k).ι.commShiftIso_add a b)
  have haddM := NatTrans.congr_app hadd M
  have haddX := NatTrans.congr_app haddM ((D.F c).obj X)
  simp only [Functor.CommShift.isoAdd_hom_app] at haddX
  calc
    _ = orbitPushdownLof M.obj X (c + -(a + b))
        (shiftedOrbitSummandEquiv D M (a + b) c X x) :=
      shiftedOrbitPushdownValueEquiv_lof D M (a + b) c X x
    _ = orbitPushdownLof M.obj X (c + -b + -a)
        (shiftedOrbitSummandEquiv D M a (c + -b) X
          (shiftedOrbitSummandEquiv D (M⟦a⟧) b c X
            (s.app ((D.F c).obj X) x))) := by
      apply DFinsupp.single_eq_of_sigma_eq
      apply Sigma.ext
        (show c + -(a + b) = c + -b + -a by
          rw [neg_add_rev, add_assoc])
      have haddApply := congr($(haddX) x)
      simp only [NatTrans.comp_app, ModuleCat.hom_comp,
        LinearMap.comp_apply] at haddApply
      change HEq
        (M.obj.map ((D.add c (-(a + b))).inv.app X)
          (Uab.hom.app ((D.F c).obj X) x))
        (M.obj.map ((D.add (c + -b) (-a)).inv.app X)
          (Ua.hom.app ((D.F (c + -b)).obj X)
            ((M⟦a⟧).obj.map ((D.add c (-b)).inv.app X)
              (Ub.hom.app ((D.F c).obj X)
                (s.app ((D.F c).obj X) x)))))
      change Uab.hom.app ((D.F c).obj X) x = _ at haddApply
      rw [haddApply]
      let z := Ub.hom.app ((D.F c).obj X)
        (s.app ((D.F c).obj X) x)
      let y := Ua.hom.app ((D.F (-b)).obj ((D.F c).obj X)) z
      change HEq
        (M.obj.map ((D.add c (-(a + b))).inv.app X)
          (((shiftFunctorAdd (C ⥤ ModuleCat.{uM} k) a b).inv.app M.obj).app
            ((D.F c).obj X) y))
        (M.obj.map ((D.add (c + -b) (-a)).inv.app X)
          (Ua.hom.app ((D.F (c + -b)).obj X)
            ((M⟦a⟧).obj.map ((D.add c (-b)).inv.app X) z)))
      have hcoh := functorCategory_shiftFunctorAdd_inv_add_apply
        (k := k) D M.obj c a b X y
      have hnat := congr($(Ua.hom.naturality
        ((D.add c (-b)).inv.app X)) z)
      simp only [Functor.comp_map, ModuleCat.hom_comp,
        LinearMap.comp_apply] at hnat
      have hout := congrArg
        (fun q ↦ M.obj.map ((D.add (c + -b) (-a)).inv.app X) q) hnat
      exact hcoh.trans (heq_of_eq hout.symm)
    _ = shiftedOrbitPushdownValueEquiv D M a X
        (orbitPushdownLof (M⟦a⟧).obj X (c + -b)
          (shiftedOrbitSummandEquiv D (M⟦a⟧) b c X
            (s.app ((D.F c).obj X) x))) :=
      (shiftedOrbitPushdownValueEquiv_lof D M a (c + -b) X _).symm
    _ = shiftedOrbitPushdownValueEquiv D M a X
        (shiftedOrbitPushdownValueEquiv D (M⟦a⟧) b X
          (orbitPushdownLof ((M⟦a⟧)⟦b⟧).obj X c
            (s.app ((D.F c).obj X) x))) :=
      congrArg (shiftedOrbitPushdownValueEquiv D M a X)
        (shiftedOrbitPushdownValueEquiv_lof D (M⟦a⟧) b c X _).symm
    _ = shiftedOrbitPushdownValueEquiv D M a X
        (shiftedOrbitPushdownValueEquiv D (M⟦a⟧) b X
          (orbitPushdownNatTransAppLinear (A := A) s X
            (orbitPushdownLof (M⟦a + b⟧).obj X c x))) :=
      congrArg (shiftedOrbitPushdownValueEquiv D M a X)
        (congrArg (shiftedOrbitPushdownValueEquiv D (M⟦a⟧) b X) hs.symm)

/-- Gabriel orbit push-down commutes coherently with deck translations when
the target is equipped with the trivial shift. -/
@[implicit_reducible]
noncomputable def linearModuleOrbitPushdownCommShift :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C A) k) A
    (linearModuleOrbitPushdown
      (k := k) (C := C) (A := A)).CommShift A := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C A) k) A
  classical
  refine
    { commShiftIso := linearModuleOrbitPushdownCommShiftIso D
      commShiftIso_zero := ?_
      commShiftIso_add := ?_ }
  · apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    change (shiftedOrbitPushdownValueEquiv D M 0
        (show C from X)).toLinearMap =
      orbitPushdownNatTransAppLinear (A := A)
        (((shiftFunctorZero
          (LinearModuleCategory.{u, v, uK, uM} (C := C) k) A).hom.app M).hom)
        (show C from X)
    exact shiftedOrbitPushdownValueEquiv_zero D M (show C from X)
  · intro a b
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    simp only [Functor.CommShift.isoAdd_hom_app]
    simp only [trivialShiftMkCore, ShiftMkCore.shiftFunctor_eq,
      ShiftMkCore.shiftFunctorAdd_eq]
    simp only [Functor.id_map]
    change (shiftedOrbitPushdownValueEquiv D M (a + b)
        (show C from X)).toLinearMap =
      (shiftedOrbitPushdownValueEquiv D M a
        (show C from X)).toLinearMap.comp
        ((shiftedOrbitPushdownValueEquiv D (M⟦a⟧) b
          (show C from X)).toLinearMap.comp
          (orbitPushdownNatTransAppLinear (A := A)
            (((shiftFunctorAdd
              (LinearModuleCategory.{u, v, uK, uM} (C := C) k)
              a b).hom.app M).hom) (show C from X)))
    exact shiftedOrbitPushdownValueEquiv_add
      D M a b (show C from X)

end MagnitudeConjecture.CoveringHom
