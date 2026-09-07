import MagnitudeConjecture.CategoryTheory.OrbitHomOrthogonality
import MagnitudeConjecture.CategoryTheory.ShiftOrbitHom

/-!
# The tautological Hom decomposition of the shift-orbit category

The abstract Gabriel Hom interface is indexed by a multiplicative group,
whereas Mathlib's shift action is indexed by an additive group.  This file
reindexes the shift-orbit Hom direct sum along `Multiplicative.ofAdd` and
packages the result as the exact `FunctorOrbitHomDecomposition` used by the
local full-faithfulness theorems.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [CommSemiring k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- Shifted Hom indexed multiplicatively, solely to match the covering-Hom
interface's group convention. -/
abbrev multiplicativeShiftHom (X Y : C) (a : Multiplicative A) :=
  ShiftHom X Y a.toAdd

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
/-- Degree-zero shifted Hom is linearly equivalent to ordinary Hom. -/
noncomputable def shiftHomZeroLinearEquiv (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] ShiftHom X Y (0 : A) where
  toEquiv := CategoryTheory.ShiftedHom.homEquiv 0 rfl
  map_add' f g := by
    simp [CategoryTheory.ShiftedHom.homEquiv,
      CategoryTheory.ShiftedHom.mk₀_add]
  map_smul' r f := by
    exact shiftHomZero_smul (A := A) r f

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
/-- Proof-irrelevant packaging of the degree-zero shifted-Hom coordinate,
useful when specializing the equivalence at very large functor objects. -/
theorem shiftHomZeroLinearEquiv_nonempty (X Y : C) :
    Nonempty ((X ⟶ Y) ≃ₗ[k] ShiftHom X Y (0 : A)) :=
  ⟨shiftHomZeroLinearEquiv (A := A) X Y⟩

/-- Reindex the additive shift degrees by their multiplicative wrapper. -/
noncomputable def multiplicativeShiftHomDirectSumEquiv (X Y : C) :
    ShiftOrbitHom A X Y ≃ₗ[k]
      DirectSum (Multiplicative A) (multiplicativeShiftHom (A := A) X Y) :=
  DirectSum.lequivCongrLeft k Multiplicative.ofAdd

/-- The target Hom of the canonical orbit functor is tautologically the
direct sum of all multiplicatively indexed shifted Hom spaces. -/
noncomputable def identityComponentOrbitHomDecomposition (X Y : C) :
    OrbitHomDecomposition (k := k)
      (H := multiplicativeShiftHom (A := A) X Y)
      ((ShiftOrbitCategory.identityComponentFunctor (C := C) (A := A)).obj X ⟶
        (ShiftOrbitCategory.identityComponentFunctor (C := C) (A := A)).obj Y) where
  homEquiv := multiplicativeShiftHomDirectSumEquiv (A := A) X Y
  lift := shiftOrbitLof (k := k) X Y 0
  homEquiv_lift f := by
    classical
    exact DirectSum.lequivCongrLeft_lof k
      (e := Multiplicative.ofAdd) (i := (0 : A))
      (k := (1 : Multiplicative A)) rfl f f rfl

/-- The concrete shift-orbit functor satisfies the exact functor-level
Gabriel Hom decomposition interface. -/
noncomputable def identityComponentFunctorOrbitHomDecomposition :
    FunctorOrbitHomDecomposition (k := k)
      (ShiftOrbitCategory.identityComponentFunctor (C := C) (A := A))
      (multiplicativeShiftHom (C := C) (A := A)) where
  sourceEquiv X Y := shiftHomZeroLinearEquiv (A := A) X Y
  homDecomposition X Y := identityComponentOrbitHomDecomposition (A := A) X Y
  map_compat X Y f := by
    rfl

/-- Every nonzero additive shift Hom vanishes. -/
def ShiftHomOrthogonal : Prop :=
  ∀ (X Y : C) (a : A), a ≠ 0 → Subsingleton (ShiftHom X Y a)

omit [Preadditive C] [∀ a : A, (shiftFunctor C a).Additive] in
/-- Additive shift orthogonality is exactly the multiplicatively indexed
orthogonality consumed by the generic covering-Hom interface. -/
theorem multiplicativeShiftHom_translateHomOrthogonal
    (h : ShiftHomOrthogonal (C := C) (A := A)) :
    TranslateHomOrthogonal (multiplicativeShiftHom (C := C) (A := A)) := by
  intro X Y a ha
  apply h X Y a.toAdd
  intro hzero
  apply ha
  exact Multiplicative.toAdd.injective (by simpa using hzero)

/-- Shift orthogonality makes the concrete degree-zero orbit functor full. -/
theorem identityComponentFunctor_fullOfShiftHomOrthogonal
    (k : Type uK) [CommSemiring k] [CategoryTheory.Linear k C]
    [∀ a : A, (shiftFunctor C a).Linear k]
    (h : ShiftHomOrthogonal (C := C) (A := A)) :
    (ShiftOrbitCategory.identityComponentFunctor (C := C) (A := A)).Full :=
  (identityComponentFunctorOrbitHomDecomposition
    (k := k) (C := C) (A := A)).fullOfOrthogonal
    (multiplicativeShiftHom_translateHomOrthogonal h)

end MagnitudeConjecture.CoveringHom
