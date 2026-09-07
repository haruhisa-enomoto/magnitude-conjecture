import MagnitudeConjecture.CategoryTheory.DeckShiftAction
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Shift.Pullback
import Mathlib.CategoryTheory.Whiskering

/-!
# Deck translations on linear module categories

Precomposition reverses the order of coherent endofunctor composition.  We
therefore first construct a shift by the additive opposite group and then
reindex it along negation.  The shift of a functor `M` in degree `a` is
literally `D.F (-a) ⋙ M`.

For a coherent left deck action, degree `g` on modules consequently has value
`M (g • X)` at `X`.  This is Gabriel's inverse module translate: if his
translated module is written `gM(X) = M(g⁻¹X)`, then Mathlib shift degree `g`
is the module `g⁻¹M`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v uE vE w

attribute [local instance] endofunctorMonoidalCategory

variable {C : Type u} [Category.{v} C]
variable {E : Type uE} [Category.{vE} E]
variable {A : Type w} [AddGroup A]

/-- Precomposition by an endofunctor, regarded as an endofunctor of a functor
category. -/
abbrev functorPrecomposition (F : C ⥤ C) : (C ⥤ E) ⥤ (C ⥤ E) :=
  (Functor.whiskeringLeft C C E).obj F

/-- Precomposition sends an isomorphism of endofunctors to an isomorphism of
endofunctors of the functor category. -/
def functorPrecompositionIso {F F' : C ⥤ C} (e : F ≅ F') :
    functorPrecomposition (E := E) F ≅ functorPrecomposition (E := E) F' :=
  (Functor.whiskeringLeft C C E).mapIso e

attribute [local simp] eqToHom_map

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Precomposition converts a coherent additive shift on the source into a
shift by the additive opposite group on the functor category. -/
def functorCategoryOppositeShiftCore (D : ShiftMkCore C A) :
    ShiftMkCore (C ⥤ E) Aᵃᵒᵖ where
  F a := functorPrecomposition (E := E) (D.F a.unop)
  zero := by
    change functorPrecomposition (E := E) (D.F 0) ≅
      functorPrecomposition (E := E) (𝟭 C)
    exact functorPrecompositionIso (E := E) D.zero
  add a b := by
    change functorPrecomposition (E := E) (D.F (b.unop + a.unop)) ≅
      functorPrecomposition (E := E) (D.F a.unop) ⋙
        functorPrecomposition (E := E) (D.F b.unop)
    exact functorPrecompositionIso (E := E) (D.add b.unop a.unop)
  assoc_hom_app a b c M := by
    ext X
    simp only [functorPrecompositionIso, functorPrecomposition,
      Functor.mapIso_hom, Functor.whiskeringLeft_map_app_app,
      NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
      Functor.whiskerLeft_app, Functor.whiskeringLeft_obj_obj,
      Functor.comp_obj, Functor.comp_map, AddOpposite.unop_add, id_eq,
      eqToHom_app]
    rw [← M.map_comp]
    rw [← M.map_comp]
    rw [D.assoc_hom_app c.unop b.unop a.unop X]
    simp only [M.map_comp, eqToHom_map, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  zero_add_hom_app a M := by
    ext X
    simp only [functorPrecompositionIso, functorPrecomposition,
      Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.whiskeringLeft_map_app_app, NatTrans.comp_app,
      Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
      Functor.whiskeringLeft_obj_obj, Functor.comp_obj,
      AddOpposite.unop_add, AddOpposite.unop_zero, id_eq, eqToHom_app]
    simpa only [M.map_comp, eqToHom_map] using
      congrArg M.map (D.add_zero_hom_app a.unop X)
  add_zero_hom_app a M := by
    ext X
    simp only [functorPrecompositionIso, functorPrecomposition,
      Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.whiskeringLeft_map_app_app, NatTrans.comp_app,
      Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Functor.comp_map,
      AddOpposite.unop_add, AddOpposite.unop_zero, id_eq, eqToHom_app]
    simpa only [M.map_comp, eqToHom_map, Functor.comp_map] using
      congrArg M.map (D.zero_add_hom_app a.unop X)

/-- A coherent shift on `C` induces inverse-precomposition shifts on the
whole functor category `C ⥤ E`. -/
@[implicit_reducible]
def functorCategoryHasShift (D : ShiftMkCore C A) : HasShift (C ⥤ E) A := by
  letI : HasShift (C ⥤ E) Aᵃᵒᵖ :=
    hasShiftMk (C ⥤ E) Aᵃᵒᵖ (functorCategoryOppositeShiftCore D)
  exact
    { shift := Discrete.addMonoidalFunctor (AddEquiv.neg' A).toAddMonoidHom ⋙
        shiftMonoidalFunctor (C ⥤ E) Aᵃᵒᵖ }

/-- The induced degree-`a` shift is literally precomposition by the
degree-`-a` source shift. -/
theorem functorCategory_shiftFunctor_eq (D : ShiftMkCore C A) (a : A) :
    letI := functorCategoryHasShift (E := E) D
    shiftFunctor (C ⥤ E) a =
      functorPrecomposition (E := E) (D.F (-a)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The zero-shift comparison on the induced functor-category shift is
pointwise application of the source zero comparison. -/
theorem functorCategory_shiftFunctorZero_hom_app
    (D : ShiftMkCore C A) (M : C ⥤ E) (X : C) :
    letI := functorCategoryHasShift (E := E) D
    HEq (((shiftFunctorZero (C ⥤ E) A).hom.app M).app X)
      (M.map (D.zero.hom.app X)) := by
  letI : HasShift (C ⥤ E) Aᵃᵒᵖ :=
    hasShiftMk (C ⥤ E) Aᵃᵒᵖ
      (functorCategoryOppositeShiftCore (E := E) D)
  letI := functorCategoryHasShift (E := E) D
  change HEq
    (((Functor.OplaxMonoidal.η
      (Discrete.addMonoidalFunctor (AddEquiv.neg' A).toAddMonoidHom ⋙
        shiftMonoidalFunctor (C ⥤ E) Aᵃᵒᵖ)).app M).app X)
    (M.map (D.zero.hom.app X))
  rw [Functor.OplaxMonoidal.comp_η]
  rw [Discrete.addMonoidalFunctor_η]
  dsimp [Discrete.eqToHom]
  simp only [eqToHom_map, eqToHom_app]
  apply (eqToHom_comp_heq _ _).trans
  change HEq
    (((shiftFunctorZero (C ⥤ E) Aᵃᵒᵖ).hom.app M).app X)
    (M.map (D.zero.hom.app X))
  rw [(functorCategoryOppositeShiftCore
    (E := E) D).shiftFunctorZero_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse zero-shift comparison on the induced functor-category shift
is pointwise application of the inverse source zero comparison. -/
theorem functorCategory_shiftFunctorZero_inv_app
    (D : ShiftMkCore C A) (M : C ⥤ E) (X : C) :
    letI := functorCategoryHasShift (E := E) D
    HEq (((shiftFunctorZero (C ⥤ E) A).inv.app M).app X)
      (M.map (D.zero.inv.app X)) := by
  letI : HasShift (C ⥤ E) Aᵃᵒᵖ :=
    hasShiftMk (C ⥤ E) Aᵃᵒᵖ
      (functorCategoryOppositeShiftCore (E := E) D)
  letI := functorCategoryHasShift (E := E) D
  change HEq
    (((Functor.LaxMonoidal.ε
      (Discrete.addMonoidalFunctor (AddEquiv.neg' A).toAddMonoidHom ⋙
        shiftMonoidalFunctor (C ⥤ E) Aᵃᵒᵖ)).app M).app X)
    (M.map (D.zero.inv.app X))
  rw [Functor.LaxMonoidal.comp_ε]
  rw [Discrete.addMonoidalFunctor_ε]
  dsimp [Discrete.eqToHom]
  simp only [eqToHom_map, eqToHom_app]
  apply (comp_eqToHom_heq _ _).trans
  change HEq
    (((shiftFunctorZero (C ⥤ E) Aᵃᵒᵖ).inv.app M).app X)
    (M.map (D.zero.inv.app X))
  rw [(functorCategoryOppositeShiftCore
    (E := E) D).shiftFunctorZero_eq]
  rfl

section LinearModule

universe uK uM

variable (k : Type uK) [CommRing k]
variable [Preadditive C] [CategoryTheory.Linear k C]

private theorem moduleCatEqToHomApplyHEq
    {M N : ModuleCat.{uM} k} (h : M = N) (x : M) :
    HEq ((eqToHom h : M ⟶ N).hom x) x := by
  subst h
  rfl

omit [Preadditive C] [CategoryTheory.Linear k C] in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise form of
`functorCategory_shiftFunctorZero_inv_app`, retaining the dependent equality
forced by the proof that negation preserves zero. -/
theorem functorCategory_shiftFunctorZero_inv_app_apply
    (D : ShiftMkCore C A) (M : C ⥤ ModuleCat.{uM} k)
    (X : C) (x : M.obj X) :
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    HEq
      (((shiftFunctorZero (C ⥤ ModuleCat.{uM} k) A).inv.app M).app X x)
      (M.map (D.zero.inv.app X) x) := by
  letI : HasShift (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ :=
    hasShiftMk (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ
      (functorCategoryOppositeShiftCore (E := ModuleCat.{uM} k) D)
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  change HEq
    (((Functor.LaxMonoidal.ε
      (Discrete.addMonoidalFunctor (AddEquiv.neg' A).toAddMonoidHom ⋙
        shiftMonoidalFunctor (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ)).app M).app X x)
    (M.map (D.zero.inv.app X) x)
  rw [Functor.LaxMonoidal.comp_ε]
  rw [Discrete.addMonoidalFunctor_ε]
  dsimp [Discrete.eqToHom]
  simp only [eqToHom_map, eqToHom_app]
  apply (moduleCatEqToHomApplyHEq (k := k) _ _).trans
  change HEq
    (((shiftFunctorZero (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ).inv.app M).app X x)
    (M.map (D.zero.inv.app X) x)
  rw [(functorCategoryOppositeShiftCore
    (E := ModuleCat.{uM} k) D).shiftFunctorZero_eq]
  rfl

omit [Preadditive C] [CategoryTheory.Linear k C] in
set_option backward.isDefEq.respectTransparency false in
private theorem functorCategoryZeroAddCastApply
    (D : ShiftMkCore C A) (M : C ⥤ ModuleCat.{uM} k)
    (c a : A) (ha : a = 0) (X : C)
    (x : M.obj ((D.F c).obj X)) :
    HEq
      (M.map ((D.add c a).inv.app X)
        ((eqToHom (by rw [ha]) :
          M.obj ((D.F 0).obj ((D.F c).obj X)) ⟶
            M.obj ((D.F a).obj ((D.F c).obj X))).hom
          (M.map (D.zero.inv.app ((D.F c).obj X)) x)))
      x := by
  subst a
  rw [D.add_zero_inv_app]
  simp only [eqToHom_refl, Functor.map_comp, ModuleCat.hom_comp,
    ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
  have hcancel :
      M.map (D.zero.hom.app ((D.F c).obj X))
          (M.map (D.zero.inv.app ((D.F c).obj X)) x) = x := by
    change (M.map (D.zero.inv.app ((D.F c).obj X)) ≫
      M.map (D.zero.hom.app ((D.F c).obj X))) x = x
    rw [← M.map_comp, Iso.inv_hom_id_app, M.map_id]
    rfl
  rw [eqToHom_map]
  apply (moduleCatEqToHomApplyHEq (k := k) _ _).trans
  exact heq_of_eq hcancel

omit [Preadditive C] [CategoryTheory.Linear k C] in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse zero comparison for inverse-precomposition shifts cancels
the deck reindexing used by orbit push-down. -/
theorem functorCategory_shiftFunctorZero_inv_add_apply
    (D : ShiftMkCore C A) (M : C ⥤ ModuleCat.{uM} k)
    (c : A) (X : C) (x : M.obj ((D.F c).obj X)) :
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    HEq
      (M.map ((D.add c (-0)).inv.app X)
        (((shiftFunctorZero (C ⥤ ModuleCat.{uM} k) A).inv.app M).app
          ((D.F c).obj X) x))
      x := by
  letI : HasShift (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ :=
    hasShiftMk (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ
      (functorCategoryOppositeShiftCore (E := ModuleCat.{uM} k) D)
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  change HEq
    (M.map ((D.add c (-0)).inv.app X)
      (((Functor.LaxMonoidal.ε
        (Discrete.addMonoidalFunctor (AddEquiv.neg' A).toAddMonoidHom ⋙
          shiftMonoidalFunctor (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ)).app M).app
        ((D.F c).obj X) x))
    x
  rw [Functor.LaxMonoidal.comp_ε]
  rw [Discrete.addMonoidalFunctor_ε]
  dsimp [Discrete.eqToHom]
  simp only [eqToHom_map, eqToHom_app]
  change HEq
    (M.map ((D.add c (-0)).inv.app X)
      ((eqToHom _ : M.obj ((D.F 0).obj ((D.F c).obj X)) ⟶
          M.obj ((D.F (-0)).obj ((D.F c).obj X))).hom
        (((shiftFunctorZero (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ).inv.app M).app
          ((D.F c).obj X) x)))
    x
  rw [(functorCategoryOppositeShiftCore
    (E := ModuleCat.{uM} k) D).shiftFunctorZero_eq]
  simp only [functorCategoryOppositeShiftCore, functorPrecompositionIso]
  dsimp
  exact functorCategoryZeroAddCastApply (k := k) D M c (-0) neg_zero X x

omit [Preadditive C] [CategoryTheory.Linear k C] in
set_option backward.isDefEq.respectTransparency false in
private theorem functorCategoryNegAddCastApply
    (D : ShiftMkCore C A) (M : C ⥤ ModuleCat.{uM} k)
    (c a b d : A) (hd : d = -b + -a) (X : C)
    (x : M.obj ((D.F (-a)).obj ((D.F (-b)).obj ((D.F c).obj X)))) :
    HEq
      (M.map ((D.add c d).inv.app X)
        ((eqToHom (by rw [hd]) :
          M.obj ((D.F (-b + -a)).obj ((D.F c).obj X)) ⟶
            M.obj ((D.F d).obj ((D.F c).obj X))).hom
          (M.map ((D.add (-b) (-a)).inv.app ((D.F c).obj X)) x)))
      (M.map ((D.add c (-b + -a)).inv.app X)
        (M.map ((D.add (-b) (-a)).inv.app ((D.F c).obj X)) x)) := by
  subst d
  simp only [eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

omit [Preadditive C] [CategoryTheory.Linear k C] in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse additive comparison for inverse-precomposition shifts is
compatible with the two successive deck reindexings used by orbit push-down. -/
theorem functorCategory_shiftFunctorAdd_inv_add_apply
    (D : ShiftMkCore C A) (M : C ⥤ ModuleCat.{uM} k)
    (c a b : A) (X : C)
    (x : M.obj ((D.F (-a)).obj ((D.F (-b)).obj ((D.F c).obj X)))) :
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    HEq
      (M.map ((D.add c (-(a + b))).inv.app X)
        (((shiftFunctorAdd (C ⥤ ModuleCat.{uM} k) a b).inv.app M).app
          ((D.F c).obj X) x))
      (M.map ((D.add (c + -b) (-a)).inv.app X)
        (M.map ((D.F (-a)).map ((D.add c (-b)).inv.app X)) x)) := by
  letI : HasShift (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ :=
    hasShiftMk (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ
      (functorCategoryOppositeShiftCore (E := ModuleCat.{uM} k) D)
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  change HEq
    (M.map ((D.add c (-(a + b))).inv.app X)
      (((Functor.LaxMonoidal.μ
        (Discrete.addMonoidalFunctor (AddEquiv.neg' A).toAddMonoidHom ⋙
          shiftMonoidalFunctor (C ⥤ ModuleCat.{uM} k) Aᵃᵒᵖ)
        ⟨a⟩ ⟨b⟩).app M).app ((D.F c).obj X) x))
    (M.map ((D.add (c + -b) (-a)).inv.app X)
      (M.map ((D.F (-a)).map ((D.add c (-b)).inv.app X)) x))
  rw [Functor.LaxMonoidal.comp_μ]
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  simp only [eqToHom_map, eqToHom_app]
  change HEq
    (M.map ((D.add c (-(a + b))).inv.app X)
      ((eqToHom (by rw [neg_add_rev]) :
        M.obj ((D.F (-b + -a)).obj ((D.F c).obj X)) ⟶
          M.obj ((D.F (-(a + b))).obj ((D.F c).obj X))).hom
        (M.map ((D.add (-b) (-a)).inv.app ((D.F c).obj X)) x)))
    (M.map ((D.add (c + -b) (-a)).inv.app X)
      (M.map ((D.F (-a)).map ((D.add c (-b)).inv.app X)) x))
  apply (functorCategoryNegAddCastApply
    (k := k) D M c a b (-(a + b)) (neg_add_rev a b) X x).trans
  have hassoc := D.assoc_inv_app c (-b) (-a) X
  have hmap := congrArg M.map hassoc
  have hassocApply := congr($(hmap) x)
  simp only [Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at hassocApply
  rw [eqToHom_map] at hassocApply
  exact (moduleCatEqToHomApplyHEq (k := k) _ _).symm.trans
    (heq_of_eq hassocApply.symm)

/-- A module over a linear category is a covariant functor to `ModuleCat`
which preserves addition and scalar multiplication. -/
def IsLinearModule : ObjectProperty (C ⥤ ModuleCat.{uM} k) :=
  fun M => M.Additive ∧ M.Linear k

/-- The full category of covariant linear modules over `C`. -/
abbrev LinearModuleCategory :=
  (IsLinearModule (C := C) k).FullSubcategory

instance (M : LinearModuleCategory (C := C) k) : M.obj.Additive :=
  M.property.1

instance (M : LinearModuleCategory (C := C) k) : M.obj.Linear k :=
  M.property.2

instance : (IsLinearModule (C := C) k).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hM := by
    letI : X.Additive := hM.1
    letI : X.Linear k := hM.2
    exact ⟨Functor.additive_of_iso e, Functor.linear_of_iso k e⟩

variable (D : ShiftMkCore C A)
variable [∀ a : A, (D.F a).Additive]
variable [∀ a : A, (D.F a).Linear k]

instance isLinearModule_stableUnderShift :
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
    (IsLinearModule (C := C) k).IsStableUnderShift A := by
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  refine ⟨fun a => ⟨?_⟩⟩
  rintro M ⟨hAdd, hLinear⟩
  letI : M.Additive := hAdd
  letI : M.Linear k := hLinear
  change (D.F (-a) ⋙ M).Additive ∧ (D.F (-a) ⋙ M).Linear k
  exact ⟨inferInstance, inferInstance⟩

/-- Coherent inverse-precomposition translation on linear modules. -/
@[implicit_reducible]
noncomputable def linearModuleCategoryHasShift :
    HasShift (LinearModuleCategory (C := C) k) A := by
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  infer_instance

/-- Forgetting linearity identifies the underlying translated module with
inverse precomposition. -/
noncomputable def linearModuleShiftUnderlyingIso
    (M : LinearModuleCategory (C := C) k) (a : A) :
    letI := linearModuleCategoryHasShift (k := k) D
    (IsLinearModule (C := C) k).ι.obj (M⟦a⟧) ≅
      D.F (-a) ⋙ M.obj := by
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  exact ((IsLinearModule (C := C) k).ι.commShiftIso a).app M

end LinearModule

namespace CoherentDeckShift

universe uK uM

variable {G : Type w} [Group G] [MulAction G C]
variable (k : Type uK) [CommRing k]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Degree `g` on the module category is Gabriel's inverse module translate:
its value at `X` is the original module's value at `g • X`. -/
noncomputable def linearModuleShiftEvaluationIso
    (M : LinearModuleCategory (C := C) k) (g : G) (X : C) :
    letI := linearModuleCategoryHasShift (k := k) D.core
    ((IsLinearModule (C := C) k).ι.obj
      (M⟦Additive.ofMul g⟧)).obj X ≅ M.obj.obj (g • X) := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  refine ((linearModuleShiftUnderlyingIso (k := k) D.core M
    (Additive.ofMul g)).app X).trans ?_
  simpa using M.obj.mapIso (D.objIso g⁻¹ X)

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
