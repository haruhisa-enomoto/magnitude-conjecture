import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Pointwise-thin finite-dimensional modules

For modules on a basic finite or locally bounded linear category,
multiplicity-freeness is expressed by having coefficient-field dimension at
most one at every object.  This is the form supplied by the universal-cover
equality calculation.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w uM

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- A linear module is pointwise thin when every value has dimension at most
one over the coefficient field. -/
def IsPointwiseThin (M : C ⥤ ModuleCat.{uM} k) : Prop :=
  ∀ X : C, Module.finrank k (M.obj X) ≤ 1

/-- For a pointwise finite module, pointwise thinness is equivalently the
statement that every nonzero value has dimension one. -/
theorem isPointwiseThin_iff_finrank_eq_one_of_not_isZero
    (M : C ⥤ ModuleCat.{uM} k)
    (hM : ∀ X : C, FiniteDimensional k (M.obj X)) :
    IsPointwiseThin M ↔
      ∀ X : C, ¬ IsZero (M.obj X) →
        Module.finrank k (M.obj X) = 1 := by
  constructor
  · intro hthin X hX
    letI : FiniteDimensional k (M.obj X) := hM X
    have hpos : 0 < Module.finrank k (M.obj X) := by
      rw [Module.finrank_pos_iff]
      have hnsub : ¬ Subsingleton (M.obj X) :=
        (not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hX
      exact not_subsingleton_iff_nontrivial.mp hnsub
    exact le_antisymm (hthin X) hpos
  · intro hthin X
    by_cases hX : IsZero (M.obj X)
    · haveI : Subsingleton (M.obj X) :=
        ModuleCat.isZero_iff_subsingleton.mp hX
      rw [Module.finrank_zero_of_subsingleton]
      exact Nat.zero_le _
    · rw [hthin X hX]

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v w uM

variable {k : Type w} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable (S : Set C)

/-- Pointwise thinness descends from an extension-by-zero module to the
original module on the surviving category. -/
theorem isPointwiseThin_of_extensionByZero
    (M : LinearModuleCategory
      (C := DeletionCategory (k := k) C S) k)
    (hM : IsPointwiseThin
      ((linearModuleExtensionByZero (k := k) C S).obj M).obj) :
    IsPointwiseThin M.obj := by
  intro X
  let e := moduleExtensionByZeroObjIsoAt (k := k) C S M.obj X
  have hrank := LinearEquiv.finrank_eq e.toLinearEquiv
  exact hrank ▸ hM X.obj.as

end MagnitudeConjecture.ObjectDeletion
