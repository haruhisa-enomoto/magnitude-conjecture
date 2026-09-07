import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Hom-finiteness of finite-support module categories

A natural transformation out of a finite-support pointwise
finite-dimensional linear module is determined by its components on that
finite support.  Evaluation therefore embeds every Hom space between finite
modules into a finite product of finite-dimensional linear-map spaces.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v uK uM

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (k : Type uK) [Field k] [CategoryTheory.Linear k C]

/-- Evaluate a morphism on the finite support of its source. -/
def finiteDimensionalModuleHomEvaluation
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    (M ⟶ N) →ₗ[k]
      ((X : moduleSupport k M.obj.obj) →
        M.obj.obj.obj X.1 →ₗ[k] N.obj.obj.obj X.1) where
  toFun f X := (f.hom.hom.app X.1).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation on source support detects a natural transformation. -/
theorem finiteDimensionalModuleHomEvaluation_injective
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    Function.Injective (finiteDimensionalModuleHomEvaluation k M N) := by
  intro f g hfg
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Z
  by_cases hZ : Nontrivial (M.obj.obj.obj Z)
  · apply ModuleCat.hom_ext
    exact congrFun hfg ⟨Z, hZ⟩
  · haveI : Subsingleton (M.obj.obj.obj Z) :=
      not_nontrivial_iff_subsingleton.mp hZ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [show x = 0 from Subsingleton.elim _ _]
    simp

/-- Hom spaces between finite-support pointwise finite-dimensional modules
are finite-dimensional. -/
noncomputable instance finiteDimensionalModuleHom_finiteDimensional
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    FiniteDimensional k (M ⟶ N) := by
  letI : Fintype (moduleSupport k M.obj.obj) := M.property.2.fintype
  letI (X : moduleSupport k M.obj.obj) :
      FiniteDimensional k
        (M.obj.obj.obj X.1 →ₗ[k] N.obj.obj.obj X.1) :=
    inferInstance
  exact FiniteDimensional.of_injective
    (finiteDimensionalModuleHomEvaluation k M N)
    (finiteDimensionalModuleHomEvaluation_injective k M N)

end MagnitudeConjecture.CoveringHom
