import MagnitudeConjecture.CategoryTheory.FiniteOrbitRadicalComponents

/-!
# Isomorphism components in a shift-orbit category

A finite-support shift-orbit isomorphism has an invertible homogeneous
component when the source orbit endomorphism ring and the relevant ordinary
endomorphism rings are local.  The proof uses the componentwise radical
criterion: if every component were radical, their finite sum would be
radical, contradicting invertibility of the orbit morphism.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalRadical
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]

include k in
/-- If every homogeneous component of a shift-orbit morphism is radical,
then the whole finite-support orbit morphism is radical. -/
theorem shiftOrbitHom_isRadicalMorphism_of_components
    {X Y : C} [IsLocalRing (End X)]
    [IsLocalRing (End (show ShiftOrbitCategory C A from X))]
    (q : ShiftOrbitHom A X Y)
    (hq : ∀ a : A, IsRadicalMorphism (q a)) :
    IsRadicalMorphism
      (show (show ShiftOrbitCategory C A from X) ⟶
        (show ShiftOrbitCategory C A from Y) from q) := by
  classical
  rw [show q = ∑ a ∈ q.support, shiftOrbitOf X Y a (q a) by
    exact DFinsupp.sum_single.symm]
  apply isRadicalMorphism_finset_sum
  intro a _
  exact (shiftOrbitOf_isRadicalMorphism_iff k a (q a)).mpr (hq a)

include k in
/-- An isomorphism in a shift-orbit category has an isomorphism among its
homogeneous components when the relevant endomorphism rings are local. -/
theorem exists_isIso_shiftOrbitHom_component
    {X Y : C} [IsLocalRing (End X)]
    [IsLocalRing (End (show ShiftOrbitCategory C A from X))]
    (hlocalY : ∀ a : A, IsLocalRing (End ((shiftFunctor C a).obj Y)))
    (q : ShiftOrbitHom A X Y)
    [IsIso
      (show (show ShiftOrbitCategory C A from X) ⟶
        (show ShiftOrbitCategory C A from Y) from q)] :
    ∃ a : A, IsIso (q a) := by
  by_contra h
  push Not at h
  have hradComponent : ∀ a : A, IsRadicalMorphism (q a) := by
    intro a
    rw [isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (not_isZero_of_end_isLocalRing X) (q a)]
    intro hsplit
    letI : IsSplitMono (q a) := hsplit
    letI : IsLocalRing (End ((shiftFunctor C a).obj Y)) := hlocalY a
    exact h a (isIso_of_isSplitMono_to_localEnd
      (q a) (not_isZero_of_end_isLocalRing X))
  have hrad := shiftOrbitHom_isRadicalMorphism_of_components
    (k := k) q hradComponent
  have hnotSplit :=
    (isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (not_isZero_of_end_isLocalRing
        (show ShiftOrbitCategory C A from X)) q).mp hrad
  exact hnotSplit inferInstance

end MagnitudeConjecture.CoveringHom
