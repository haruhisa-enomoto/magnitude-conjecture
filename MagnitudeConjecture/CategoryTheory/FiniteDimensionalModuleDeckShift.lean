import MagnitudeConjecture.CategoryTheory.LinearModuleDeckShift
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Deck translations on finite-dimensional modules

For a locally bounded category, a finite-dimensional module is pointwise
finite-dimensional and has finite object support.  This file defines that
literal full subcategory of linear modules and proves that coherent deck
translations preserve it.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]
variable (k : Type uK) [Field k]
variable [Preadditive C] [CategoryTheory.Linear k C]

/-- The object support of a module-valued functor. -/
def moduleSupport (M : C ⥤ ModuleCat.{uM} k) : Set C :=
  {X | Nontrivial (M.obj X)}

/-- A linear module is finite-dimensional when it is pointwise
finite-dimensional and has finite object support. -/
def IsFiniteDimensionalModule :
    ObjectProperty (LinearModuleCategory (C := C) k) :=
  fun M =>
    (∀ X : C, FiniteDimensional k (M.obj.obj X)) ∧
      (moduleSupport k M.obj).Finite

/-- The full category of finite-dimensional linear modules over `C`. -/
abbrev FiniteDimensionalModuleCategory :=
  (IsFiniteDimensionalModule (C := C) k).FullSubcategory

instance (M : FiniteDimensionalModuleCategory (C := C) k) (X : C) :
    FiniteDimensional k (M.obj.obj.obj X) :=
  M.property.1 X

/-- A finite-dimensional module has finite object support. -/
theorem finite_moduleSupport
    (M : FiniteDimensionalModuleCategory (C := C) k) :
    (moduleSupport k M.obj.obj).Finite :=
  M.property.2

instance : (IsFiniteDimensionalModule (C := C) k).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    let e' := (IsLinearModule (C := C) k).ι.mapIso e
    constructor
    · intro X
      letI : FiniteDimensional k
          (((IsLinearModule (C := C) k).ι.obj M).obj X) := hM.1 X
      exact (e'.app X).toLinearEquiv.finiteDimensional
    · have hsupport : moduleSupport k N.obj = moduleSupport k M.obj := by
        ext X
        exact (e'.app X).toLinearEquiv.toEquiv.nontrivial_congr.symm
      rw [hsupport]
      exact hM.2

namespace CoherentDeckShift

variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The support of a translated linear module is the preimage of its support
under the corresponding strict left deck transformation. -/
theorem moduleSupport_shift_eq_preimage
    (M : LinearModuleCategory (C := C) k) (g : G) :
    letI := linearModuleCategoryHasShift (k := k) D.core
    moduleSupport k
        ((IsLinearModule (C := C) k).ι.obj
          (M⟦Additive.ofMul g⟧)) =
      (g • ·) ⁻¹' moduleSupport k M.obj := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  ext X
  exact
    (D.linearModuleShiftEvaluationIso k M g X).toLinearEquiv.toEquiv.nontrivial_congr

instance isFiniteDimensionalModule_stableUnderShift :
    letI := linearModuleCategoryHasShift (k := k) D.core
    (IsFiniteDimensionalModule (C := C) k).IsStableUnderShift
      (Additive G) := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  refine ⟨fun a => ⟨?_⟩⟩
  rintro M hM
  let g := a.toMul
  constructor
  · intro X
    letI : FiniteDimensional k (M.obj.obj (g • X)) := hM.1 (g • X)
    exact
      (D.linearModuleShiftEvaluationIso k M g X).symm.toLinearEquiv.finiteDimensional
  · change (moduleSupport k
      ((IsLinearModule (C := C) k).ι.obj (M⟦a⟧))).Finite
    rw [show a = Additive.ofMul g by rfl,
      D.moduleSupport_shift_eq_preimage k M g]
    exact hM.2.preimage (MulAction.injective g).injOn

/-- Coherent deck translation restricts to finite-dimensional modules. -/
@[implicit_reducible]
noncomputable def finiteDimensionalModuleCategoryHasShift :
    HasShift (FiniteDimensionalModuleCategory (C := C) k) (Additive G) := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  infer_instance

/-- The finite-dimensional restriction forgets to the previously constructed
linear-module translation. -/
noncomputable def finiteDimensionalModuleShiftUnderlyingIso
    (M : FiniteDimensionalModuleCategory (C := C) k) (a : Additive G) :
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (IsFiniteDimensionalModule (C := C) k).ι.obj (M⟦a⟧) ≅
      M.obj⟦a⟧ := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  exact ((IsFiniteDimensionalModule (C := C) k).ι.commShiftIso a).app M

/-- The support formula for deck translation, stated directly for the
finite-dimensional full subcategory. -/
theorem finiteDimensionalModuleSupport_shift_eq_preimage
    (M : FiniteDimensionalModuleCategory (C := C) k) (g : G) :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    moduleSupport k
        ((IsFiniteDimensionalModule (C := C) k).ι.obj
          (M⟦Additive.ofMul g⟧)).obj =
      (g • ·) ⁻¹' moduleSupport k M.obj.obj := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  let e := (IsLinearModule (C := C) k).ι.mapIso
    (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) M
      (Additive.ofMul g))
  calc
    moduleSupport k
        ((IsFiniteDimensionalModule (C := C) k).ι.obj
          (M⟦Additive.ofMul g⟧)).obj =
        moduleSupport k
          ((IsLinearModule (C := C) k).ι.obj (M.obj⟦Additive.ofMul g⟧)) := by
            ext X
            exact (e.app X).toLinearEquiv.toEquiv.nontrivial_congr
    _ = (g • ·) ⁻¹' moduleSupport k M.obj.obj :=
      D.moduleSupport_shift_eq_preimage k M.obj g

/-- Evaluation of a translated finite-dimensional module obeys Gabriel's
inverse-translation formula. -/
noncomputable def finiteDimensionalModuleShiftEvaluationIso
    (M : FiniteDimensionalModuleCategory (C := C) k) (g : G) (X : C) :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ((IsLinearModule (C := C) k).ι.obj
      ((IsFiniteDimensionalModule (C := C) k).ι.obj
        (M⟦Additive.ofMul g⟧))).obj X ≅ M.obj.obj.obj (g • X) := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  exact (((IsLinearModule (C := C) k).ι.mapIso
    (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) M
      (Additive.ofMul g))).app X).trans
        (D.linearModuleShiftEvaluationIso k M.obj g X)

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
