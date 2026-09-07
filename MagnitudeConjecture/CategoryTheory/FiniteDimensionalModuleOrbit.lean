import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import MagnitudeConjecture.CategoryTheory.ShiftOrbitDecomposition
import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive

/-!
# The shift-orbit category of finite-dimensional modules

This file instantiates the concrete shift-orbit construction on the literal
category of finite-dimensional modules over the cover.  It supplies the
additive and linear shift instances needed by the construction, the canonical
faithful orbit functor, and its tautological Gabriel-shaped Hom decomposition.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v uE vE w uK uM

variable {C : Type u} [Category.{v} C]
variable {E : Type uE} [Category.{vE} E]

section Precomposition

variable (k : Type uK) [Semiring k]
variable [Preadditive E] [CategoryTheory.Linear k E]

instance (F : C ⥤ C) :
    (functorPrecomposition (E := E) F).Linear k where
  map_smul α r := by rfl

end Precomposition

/-- A faithful linear functor commuting with shifts transfers linearity of
the target shifts back to the source shifts. -/
theorem linearShiftOfCommShiftFaithful
    {D : Type uE} [Category.{vE} D]
    (k : Type uK) [Semiring k]
    [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
    {A : Type w} [AddMonoid A] [HasShift C A] [HasShift D A]
    (F : C ⥤ D) [F.Faithful] [F.Linear k] [F.CommShift A]
    [∀ a : A, (shiftFunctor D a).Linear k]
    (a : A) : (shiftFunctor C a).Linear k := by
  letI : (shiftFunctor C a ⋙ F).Linear k :=
    Functor.linear_of_iso k (F.commShiftIso a).symm
  constructor
  intro X Y f r
  apply F.map_injective
  rw [F.map_smul]
  change (shiftFunctor C a ⋙ F).map (r • f) =
    r • (shiftFunctor C a ⋙ F).map f
  exact (shiftFunctor C a ⋙ F).map_smul r f

variable {G : Type w} [Group G] [MulAction G C]
variable (k : Type uK) [Field k]
variable [Preadditive C] [CategoryTheory.Linear k C]

/-- The concrete shift-orbit category of finite-dimensional modules. -/
@[reducible, nolint unusedArguments]
def FiniteDimensionalModuleOrbitCategory (G : Type w) :=
  ShiftOrbitCategory
    (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (Additive G)

namespace CoherentDeckShift

variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k]
  [Preadditive C] [CategoryTheory.Linear k C] in
theorem moduleFunctorCategoryLinearShift :
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D.core
    ∀ a : Additive G,
      (shiftFunctor (C ⥤ ModuleCat.{uM} k) a).Linear k := by
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D.core
  intro a
  change (functorPrecomposition (E := ModuleCat.{uM} k)
    (D.core.F (-a))).Linear k
  infer_instance

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k]
  [Preadditive C] [CategoryTheory.Linear k C] in
theorem moduleFunctorCategoryAdditiveShift :
    letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D.core
    ∀ a : Additive G,
      (shiftFunctor (C ⥤ ModuleCat.{uM} k) a).Additive := by
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D.core
  intro a
  change (functorPrecomposition (E := ModuleCat.{uM} k)
    (D.core.F (-a))).Additive
  infer_instance

/-- Every coherent shift functor on finite-dimensional modules is additive. -/
theorem finiteDimensionalModuleCategoryAdditiveShift :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ a : Additive G,
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) a).Additive := by
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D.core
  letI := D.moduleFunctorCategoryAdditiveShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro a
  let J :
      FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        (C ⥤ ModuleCat.{uM} k) :=
    (IsFiniteDimensionalModule (C := C) k).ι ⋙
      (IsLinearModule (C := C) k).ι
  letI : (shiftFunctor
      (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) a ⋙ J).Additive :=
    Functor.additive_of_iso (J.commShiftIso a).symm
  exact Functor.additive_of_comp_faithful _ J

/-- Every coherent shift functor on finite-dimensional modules is linear. -/
theorem finiteDimensionalModuleCategoryLinearShift :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ a : Additive G,
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) a).Linear k := by
  letI := functorCategoryHasShift (E := ModuleCat.{uM} k) D.core
  letI := D.moduleFunctorCategoryLinearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro a
  let J :
      FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        (C ⥤ ModuleCat.{uM} k) :=
    (IsFiniteDimensionalModule (C := C) k).ι ⋙
      (IsLinearModule (C := C) k).ι
  exact linearShiftOfCommShiftFaithful k J a

/-- The canonical degree-zero functor from finite-dimensional modules to
their shift-orbit category. -/
noncomputable def finiteDimensionalModuleOrbitFunctor :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      FiniteDimensionalModuleOrbitCategory.{u, v, w, uK, uM}
        (C := C) k G := by
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  exact ShiftOrbitCategory.identityComponentFunctor
    (C := FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (A := Additive G)

/-- The canonical finite-dimensional module orbit functor is faithful before
any translate-orthogonality assumption. -/
theorem finiteDimensionalModuleOrbitFunctor_faithful :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    (D.finiteDimensionalModuleOrbitFunctor (k := k)).Faithful := by
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  exact ShiftOrbitCategory.identityComponentFunctor_faithful

/-- The canonical module orbit functor has the tautological direct-sum Hom
decomposition indexed by all deck translates. -/
noncomputable def finiteDimensionalModuleOrbitHomDecomposition :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    letI := D.finiteDimensionalModuleCategoryLinearShift (k := k)
    FunctorOrbitHomDecomposition (k := k)
      (D.finiteDimensionalModuleOrbitFunctor (k := k))
      (multiplicativeShiftHom
        (C := FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
        (A := Additive G)) := by
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI := D.finiteDimensionalModuleCategoryLinearShift (k := k)
  exact identityComponentFunctorOrbitHomDecomposition
    (k := k)
    (C := FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (A := Additive G)

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
