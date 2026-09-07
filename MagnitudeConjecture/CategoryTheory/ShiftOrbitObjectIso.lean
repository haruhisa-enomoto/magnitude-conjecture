import MagnitudeConjecture.CategoryTheory.ShiftOrbitHom

/-!
# Shifted objects are isomorphic in the shift-orbit category

The orbit category identifies every object with each of its shifts.  This
file constructs the identification explicitly from Mathlib's shift
equivalence and verifies both inverse laws against finite-support
convolution.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]

/-- The homogeneous orbit morphism from an object to its degree-`a` shift.
Its orbit degree is `-a`. -/
def shiftOrbitToShift (X : C) (a : A) :
    ShiftOrbitHom A X ((shiftFunctor C a).obj X) :=
  shiftOrbitOf X ((shiftFunctor C a).obj X) (-a)
    (shiftShiftNeg X a).inv

/-- The homogeneous orbit morphism from a degree-`a` shift back to the
unshifted object.  Its orbit degree is `a`. -/
def shiftOrbitFromShift (X : C) (a : A) :
    ShiftOrbitHom A ((shiftFunctor C a).obj X) X :=
  shiftOrbitOf ((shiftFunctor C a).obj X) X a (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftOrbitToShift_comp_shiftOrbitFromShift (X : C) (a : A) :
    shiftOrbitCompHom (shiftOrbitToShift X a) (shiftOrbitFromShift X a) =
      shiftOrbitId X := by
  classical
  rw [shiftOrbitToShift, shiftOrbitFromShift, shiftOrbitId,
    shiftOrbitCompHom_of_of]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_neg_cancel a)
  refine (shiftHomComp_heq_shiftHomComp' (add_neg_cancel a)
    (shiftShiftNeg X a).inv (𝟙 _)).trans (heq_of_eq ?_)
  simp [shiftHomComp', shiftHomId, shiftShiftNeg,
    shiftFunctorCompIsoId]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem shiftOrbitFromShift_comp_shiftOrbitToShift (X : C) (a : A) :
    shiftOrbitCompHom (shiftOrbitFromShift X a) (shiftOrbitToShift X a) =
      shiftOrbitId ((shiftFunctor C a).obj X) := by
  classical
  rw [shiftOrbitFromShift, shiftOrbitToShift, shiftOrbitId,
    shiftOrbitCompHom_of_of]
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (neg_add_cancel a)
  refine (shiftHomComp_heq_shiftHomComp' (neg_add_cancel a)
    (𝟙 _) (shiftShiftNeg X a).inv).trans (heq_of_eq ?_)
  apply (cancel_mono ((shiftFunctorZero C A).hom.app _)).1
  simpa [shiftHomComp', shiftHomId, shiftShiftNeg, shiftNegShift,
    shiftFunctorCompIsoId, Category.assoc] using
      shift_equiv_triangle a X

/-- Every object is canonically isomorphic in the orbit category to each of
its shifts. -/
noncomputable def ShiftOrbitCategory.objectShiftIso (X : C) (a : A) :
    (show ShiftOrbitCategory C A from X) ≅
      (show ShiftOrbitCategory C A from (shiftFunctor C a).obj X) where
  hom := shiftOrbitToShift X a
  inv := shiftOrbitFromShift X a
  hom_inv_id := shiftOrbitToShift_comp_shiftOrbitFromShift X a
  inv_hom_id := shiftOrbitFromShift_comp_shiftOrbitToShift X a

end MagnitudeConjecture.CoveringHom
