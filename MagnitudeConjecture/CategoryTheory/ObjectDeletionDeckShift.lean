import MagnitudeConjecture.CategoryTheory.DeckShiftAction
import MagnitudeConjecture.CategoryTheory.CoherentDeckShiftRestriction
import MagnitudeConjecture.CategoryTheory.ObjectDeletionShift
import Mathlib.CategoryTheory.Skeletal

/-!
# Deck shifts on invariant object-deletion quotients

An intermediate covering stage deletes a union of orbits for the subgroup
`Γ`.  This file supplies exactly the symmetry retained by such a stage.  An
action-invariant, isomorphism-closed deleted set is invariant under the
coherent deck shifts, so the shifts descend through `C/(S)`.  The literal deck
action on surviving objects and the descended shifts again form a
`CoherentDeckShift`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

universe u v w z

variable {k : Type z} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type w} [Group G] [MulAction G C]

/-- Membership in a set of objects is unchanged by the literal left group
action. -/
def ActionInvariant (S : Set C) : Prop :=
  ∀ (g : G) (X : C), g • X ∈ S ↔ X ∈ S

omit [Preadditive C] in
/-- In a skeletal category every object property is closed under
isomorphisms. -/
theorem isClosedUnderIsomorphisms_of_skeletal
    (hC : Skeletal C) (S : Set C) :
    ObjectProperty.IsClosedUnderIsomorphisms S where
  of_iso {X Y} e hX := by
    rw [← hC ⟨e⟩]
    exact hX

namespace CoherentDeckShift

open MagnitudeConjecture.CoveringHom

variable (D : CoveringHom.CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

omit [Preadditive C] [∀ a : Additive G, (D.core.F a).Additive] in
/-- Literal deck invariance, together with closure under isomorphism, implies
invariance under the chosen coherent deck functors. -/
theorem shiftInvariant_of_actionInvariant (S : Set C)
    [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    ShiftInvariant (C := C) (Additive G) S := by
  letI := D.hasShift
  intro a X
  change (D.core.F a).obj X ∈ S ↔ X ∈ S
  exact (ObjectProperty.prop_iff_of_iso S (D.objIso a.toMul X)).trans
    (hS a.toMul⁻¹ X)

end CoherentDeckShift

/-- The literal deck action on the surviving objects of `C/(S)`. -/
@[implicit_reducible]
def deletionMulAction (S : Set C)
    (hS : ActionInvariant (G := G) S) :
    MulAction G (DeletionCategory (k := k) C S) where
  smul g X :=
    ⟨⟨g • X.obj.as⟩, fun hgX ↦ X.property ((hS g X.obj.as).1 hgX)⟩
  one_smul X := by
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact one_smul G X.obj.as
  mul_smul g h X := by
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact mul_smul g h X.obj.as

@[simp]
theorem deletion_smul_obj_as (S : Set C)
    (hS : ActionInvariant (G := G) S)
    (g : G) (X : DeletionCategory (k := k) C S) :
    letI := deletionMulAction (k := k) S hS
    (g • X).obj.as = g • X.obj.as :=
  rfl

/-- Freeness of the literal object action survives deletion. -/
theorem deletionIsCancelSMul [IsCancelSMul G C]
    (S : Set C) (hS : ActionInvariant (G := G) S) :
    letI := deletionMulAction (k := k) S hS
    IsCancelSMul G (DeletionCategory (k := k) C S) := by
  letI := deletionMulAction (k := k) S hS
  exact
    { left_cancel' := fun g X Y h ↦ by
        apply ObjectProperty.FullSubcategory.ext
        apply CategoryTheory.Quotient.ext
        have e := congrArg (fun Z ↦ Z.obj.as) h
        change g • X.obj.as = g • Y.obj.as at e
        exact IsCancelSMul.left_cancel g X.obj.as Y.obj.as
          e
      right_cancel' := fun g h X e ↦ by
        have e' := congrArg (fun Z ↦ Z.obj.as) e
        change g • X.obj.as = h • X.obj.as at e'
        exact IsCancelSMul.right_cancel g h X.obj.as e' }

namespace CoherentDeckShift

open MagnitudeConjecture.CoveringHom

variable (D : CoveringHom.CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

private noncomputable def shiftMkCoreOfHasShift
    {B : Type u} [Category.{v} B]
    {A : Type w} [AddMonoid A] [HasShift B A] :
    ShiftMkCore B A where
  F := shiftFunctor B
  zero := shiftFunctorZero B A
  add := shiftFunctorAdd B
  assoc_hom_app := by
    intro a b c X
    simpa [shiftFunctorAdd'] using
      shiftFunctorAdd_assoc_hom_app a b c X
  zero_add_hom_app := shiftFunctorAdd_zero_add_hom_app
  add_zero_hom_app := shiftFunctorAdd_add_zero_hom_app

/-- A coherent deck shift descends to an invariant object-deletion quotient.
The resulting object comparison is the composite of the full-subcategory
shift comparison with the quotient of the original deck comparison. -/
def deletionCoherentDeckShift (S : Set C)
    [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    CoveringHom.CoherentDeckShift
      (DeletionCategory (k := k) C S) G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI := deletionHasShift (k := k) S hShift
  letI := rawFunctorCommShift (k := k) S hShift
  letI := deletionInclusionCommShift (k := k) S hShift
  letI := deletionMulAction (k := k) S hS
  let P := IsSurvivingRaw (k := k) C S
  exact
    { core := shiftMkCoreOfHasShift
      objIso := fun g X ↦
        ObjectProperty.isoMk P
          ((P.ι.commShiftIso (Additive.ofMul g)).app X ≪≫
            (rawFunctor (k := k) C S).mapIso (D.objIso g X.obj.as)) }

/-- The shift instance exported by the coherent deletion package is the
inherited deletion shift from which its core was built. -/
theorem deletionCoherentDeckShift_hasShift_eq
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    (deletionCoherentDeckShift (k := k) D S hS).hasShift =
      deletionHasShift (k := k) S hShift := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI := deletionHasShift (k := k) S hShift
  letI := deletionMulAction (k := k) S hS
  unfold deletionCoherentDeckShift
    MagnitudeConjecture.CoveringHom.CoherentDeckShift.hasShift
  unfold deletionHasShift ObjectProperty.hasShift
  rfl

/-- The functor field of the coherent deletion shift is the inherited
deletion shift functor.  This equation exposes the otherwise private
constructor used by `deletionCoherentDeckShift`. -/
theorem deletionCoherentDeckShift_core_F_eq_shiftFunctor
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    (deletionCoherentDeckShift (k := k) D S hS).core.F a =
      shiftFunctor (DeletionCategory (k := k) C S) a := by
  rfl

/-- Descending an invariant deck shift through object deletion commutes with
restriction to a subgroup at the level of the complete coherent shift core. -/
theorem deletionCoherentDeckShift_restrict_core_eq
    (N : Subgroup G) (S : Set C)
    [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hSG : ActionInvariant (G := G) S)
    (hSN : ActionInvariant (G := N) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := deletionMulAction (k := k) S hSG
    let DG := deletionCoherentDeckShift (k := k) D S hSG
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := deletionMulAction (k := k) S hSN
    let DN := deletionCoherentDeckShift (k := k) (D.restrict N) S hSN
    (DG.restrict N).core = DN.core := by
  dsimp
  unfold deletionCoherentDeckShift
  unfold deletionHasShift ObjectProperty.hasShift
  rfl

instance deletionCoherentDeckShift_core_additive
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    ((deletionCoherentDeckShift (k := k) D S hS).core.F a).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI := deletionHasShift (k := k) S hShift
  letI := deletionMulAction (k := k) S hS
  dsimp only [deletionCoherentDeckShift]
  change (shiftFunctor (DeletionCategory (k := k) C S) a).Additive
  exact deletionShift_additive (k := k) S hShift a

instance deletionCoherentDeckShift_core_linear
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    ((deletionCoherentDeckShift (k := k) D S hS).core.F a).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI := deletionHasShift (k := k) S hShift
  letI := deletionMulAction (k := k) S hS
  dsimp only [deletionCoherentDeckShift]
  change (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k
  exact deletionShift_linear (k := k) S hShift a

end CoherentDeckShift

end MagnitudeConjecture.ObjectDeletion
