import MagnitudeConjecture.CategoryTheory.LinearIdealQuotientLift
import MagnitudeConjecture.CategoryTheory.ObjectDeletionQuotient
import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
import Mathlib.CategoryTheory.Shift.Induced

/-!
# Shifts on object-deletion quotients

If a coherent shift preserves the set of deleted objects, every shift functor
preserves the deletion ideal.  It therefore descends to the raw Hom-ideal
quotient.  The induced shift on that quotient preserves the full subcategory
of surviving objects and hence restricts to the manuscript's category
`C/(S)`.

The construction is stated for an arbitrary additive group of shifts.  The
covering application takes the shifts indexed by `Additive Γ`, where the set
already deleted at an intermediate stage is a union of `Γ`-orbits.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.ObjectDeletion

universe u v w z

variable {k : Type z} [Ring k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable (A : Type w) [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- A deleted object set is shift-invariant when membership is unchanged by
every shift functor.  For a group of shifts, either implication would suffice;
the biconditional is the useful interface for both deleted and surviving
objects. -/
def ShiftInvariant (S : Set C) : Prop :=
  ∀ (a : A) (X : C), (shiftFunctor C a).obj X ∈ S ↔ X ∈ S

variable {C A}

/-- Shift first and then apply the raw deletion quotient. -/
abbrev shiftedRawFunctor (S : Set C) (a : A) :
    C ⥤ RawCategory (k := k) C S :=
  shiftFunctor C a ⋙ rawFunctor (k := k) C S

/-- Shift-invariance of the deleted objects makes every shifted raw quotient
functor kill the deletion ideal. -/
theorem shiftedRawFunctor_isKilledBy (S : Set C)
    (hS : ShiftInvariant (C := C) A S) (a : A) :
    (ideal (k := k) C S).IsKilledBy
      (shiftedRawFunctor (k := k) S a) := by
  intro X Y f hf
  have hk : f ∈
      (HomIdeal.functorKernel (k := k)
        (shiftedRawFunctor (k := k) S a)).hom X Y := by
    apply HomIdeal.linearSpan_le
      (endomorphismRelations C S)
      (HomIdeal.functorKernel (k := k)
        (shiftedRawFunctor (k := k) S a))
      ?_ hf
    intro U V r hr
    rcases hr with ⟨rfl, hU⟩
    change (rawFunctor (k := k) C S).map
      ((shiftFunctor C a).map r) = 0
    exact ((ideal (k := k) C S).map_eq_zero_iff
      ((shiftFunctor C a).map r)).2
        (endomorphism_mem_ideal (k := k) C S
          ((hS a U).2 hU) ((shiftFunctor C a).map r))
  exact (HomIdeal.mem_functorKernel_iff
    (k := k) (shiftedRawFunctor (k := k) S a) f).1 hk

/-- The shift functor descended to the raw Hom-ideal quotient. -/
def rawShiftFunctor (S : Set C)
    (hS : ShiftInvariant (C := C) A S) (a : A) :
    RawCategory (k := k) C S ⥤ RawCategory (k := k) C S :=
  (ideal (k := k) C S).quotientLift
    (shiftedRawFunctor (k := k) S a)
    (shiftedRawFunctor_isKilledBy (k := k) S hS a)

noncomputable instance rawShiftFunctor_additive (S : Set C)
    (hS : ShiftInvariant (C := C) A S) (a : A) :
    (rawShiftFunctor (k := k) S hS a).Additive :=
  HomIdeal.quotientLift_additive
    (ideal (k := k) C S)
    (shiftedRawFunctor (k := k) S a)
    (shiftedRawFunctor_isKilledBy (k := k) S hS a)

noncomputable instance rawShiftFunctor_linear (S : Set C)
    (hS : ShiftInvariant (C := C) A S) (a : A) :
    (rawShiftFunctor (k := k) S hS a).Linear k :=
  HomIdeal.quotientLift_linear
    (ideal (k := k) C S)
    (shiftedRawFunctor (k := k) S a)
    (shiftedRawFunctor_isKilledBy (k := k) S hS a)

/-- The raw quotient functor intertwines the ambient and descended shifts.
This is definitionally the quotient-lift triangle. -/
def rawFunctorShiftIso (S : Set C)
    (hS : ShiftInvariant (C := C) A S) (a : A) :
    rawFunctor (k := k) C S ⋙ rawShiftFunctor (k := k) S hS a ≅
      shiftFunctor C a ⋙ rawFunctor (k := k) C S :=
  Iso.refl _

/-- The coherent shift induced on the raw Hom-ideal quotient. -/
@[implicit_reducible]
def rawHasShift (S : Set C)
    (hS : ShiftInvariant (C := C) A S) :
    HasShift (RawCategory (k := k) C S) A :=
  HasShift.induced (rawFunctor (k := k) C S) A
    (rawShiftFunctor (k := k) S hS)
    (rawFunctorShiftIso (k := k) S hS)

/-- The raw quotient functor commutes coherently with the induced shifts. -/
@[implicit_reducible]
def rawFunctorCommShift (S : Set C)
    (hS : ShiftInvariant (C := C) A S) :
    letI := rawHasShift (k := k) S hS
    (rawFunctor (k := k) C S).CommShift A :=
  Functor.CommShift.ofInduced (rawFunctor (k := k) C S) A
    (rawShiftFunctor (k := k) S hS)
    (rawFunctorShiftIso (k := k) S hS)

/-- Surviving raw quotient objects are stable under the induced shift. -/
theorem isSurvivingRaw_stableUnderShift (S : Set C)
    (hS : ShiftInvariant (C := C) A S) :
    letI := rawHasShift (k := k) S hS
    (IsSurvivingRaw (k := k) C S).IsStableUnderShift A := by
  letI := rawHasShift (k := k) S hS
  refine { isStableUnderShiftBy := fun a ↦ ?_ }
  refine { le_shift := ?_ }
  intro X hX
  change ((rawShiftFunctor (k := k) S hS a).obj X).as ∉ S
  change (shiftFunctor C a).obj X.as ∉ S
  exact fun h ↦ hX ((hS a X.as).1 h)

/-- The coherent shift on the manuscript's deletion category `C/(S)`. -/
@[implicit_reducible]
def deletionHasShift (S : Set C)
    (hS : ShiftInvariant (C := C) A S) :
    HasShift (DeletionCategory (k := k) C S) A := by
  letI := rawHasShift (k := k) S hS
  letI := isSurvivingRaw_stableUnderShift (k := k) S hS
  exact ObjectProperty.hasShift (P := IsSurvivingRaw (k := k) C S)

/-- The inclusion of surviving quotient objects into the raw quotient
commutes with the induced shifts. -/
@[implicit_reducible]
def deletionInclusionCommShift (S : Set C)
    (hS : ShiftInvariant (C := C) A S) :
    letI := rawHasShift (k := k) S hS
    letI := deletionHasShift (k := k) S hS
    ((IsSurvivingRaw (k := k) C S).ι).CommShift A := by
  letI := rawHasShift (k := k) S hS
  letI := isSurvivingRaw_stableUnderShift (k := k) S hS
  simpa only [deletionHasShift] using
    (inferInstance : ((IsSurvivingRaw (k := k) C S).ι).CommShift A)

/-- Every shift functor on the deletion category remains additive. -/
theorem deletionShift_additive (S : Set C)
    (hS : ShiftInvariant (C := C) A S) (a : A) :
    letI := rawHasShift (k := k) S hS
    letI := deletionHasShift (k := k) S hS
    (shiftFunctor (DeletionCategory (k := k) C S) a).Additive := by
  letI := rawHasShift (k := k) S hS
  letI := isSurvivingRaw_stableUnderShift (k := k) S hS
  letI := deletionHasShift (k := k) S hS
  letI : (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    rawShiftFunctor_additive (k := k) S hS a
  infer_instance

/-- Every shift functor on the deletion category remains linear. -/
theorem deletionShift_linear (S : Set C)
    (hS : ShiftInvariant (C := C) A S) (a : A) :
    letI := rawHasShift (k := k) S hS
    letI := deletionHasShift (k := k) S hS
    (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k := by
  letI := rawHasShift (k := k) S hS
  letI := isSurvivingRaw_stableUnderShift (k := k) S hS
  letI := deletionHasShift (k := k) S hS
  letI : (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    rawShiftFunctor_linear (k := k) S hS a
  let P := IsSurvivingRaw (k := k) C S
  let F := shiftFunctor (P.FullSubcategory) a
  have hcomp : (F ⋙ P.ι).Linear k :=
    Functor.linear_of_iso k (P.ι.commShiftIso a).symm
  refine { map_smul := fun {X Y} f r ↦ ?_ }
  apply P.ι.map_injective
  change P.ι.map (F.map (r • f)) = P.ι.map (r • F.map f)
  rw [P.ι.map_smul]
  exact hcomp.map_smul f r

end MagnitudeConjecture.ObjectDeletion
