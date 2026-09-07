import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckShift
import MagnitudeConjecture.CategoryTheory.LinearIdealQuotientLift
import MagnitudeConjecture.CategoryTheory.OrbitPushdownDescent
import MagnitudeConjecture.CategoryTheory.ShiftOrbitFactorization

/-!
# Object deletion commutes with a shift-orbit quotient

For a shift-invariant set of objects `S`, this file compares the two literal
categories occurring in the covering argument:

* first delete `S` and then form the shift-orbit category; and
* first form the shift-orbit category and then delete `S`.

The comparison is constructed first on the raw object-deletion quotient.
There every deleted object is a zero object, so the componentwise orbit map
kills the orbit-category deletion ideal.  The substantive kernel statement
is the converse: if every quotient component is zero, each ambient component
belongs to the original deletion ideal and its homogeneous orbit inclusion
belongs to the orbit-category deletion ideal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v w z

section ShiftOrbitZero

variable {E : Type u} [Category.{v} E] [Preadditive E]
variable {A : Type w} [AddMonoid A] [HasShift E A]
variable [∀ a : A, (shiftFunctor E a).Additive]

/-- A zero object of the base category remains zero in its shift-orbit
category. -/
theorem isZero_shiftOrbitCategory {X : E} (hX : IsZero X) :
    IsZero (show ShiftOrbitCategory E A from X) := by
  rw [IsZero.iff_id_eq_zero]
  change shiftOrbitId X = 0
  unfold shiftOrbitId
  have hhom : shiftHomId (A := A) X = 0 := hX.eq_of_src _ _
  rw [hhom]
  exact map_zero (shiftOrbitOf X X (0 : A))

end ShiftOrbitZero

section HomogeneousIdeal

variable {k : Type z} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- A homogeneous orbit morphism whose ambient component belongs to the
object-deletion ideal belongs to the corresponding ideal in the orbit
category. -/
theorem shiftOrbitOf_mem_orbitIdeal_of_mem_ideal
    (S : Set C) {X Y : C} (a : A) (f : ShiftHom X Y a)
    (hf : f ∈ (ideal (k := k) C S).hom X ((shiftFunctor C a).obj Y)) :
    shiftOrbitOf X Y a f ∈
      (ideal (k := k) (ShiftOrbitCategory C A) S).hom X Y := by
  change f ∈ HomIdeal.generatedHomSubmodule k
    (endomorphismRelations C S) X ((shiftFunctor C a).obj Y) at hf
  change shiftOrbitOf X Y a f ∈ HomIdeal.generatedHomSubmodule k
    (endomorphismRelations (ShiftOrbitCategory C A) S) X Y
  induction hf using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨U, V, r, hr, p, q, rfl⟩
      rcases hr with ⟨rfl, hU⟩
      have hfactor := comp_mem_ideal (k := k)
        (ShiftOrbitCategory C A) S hU
        (shiftOrbitOf X U 0
          (shiftHomZero (A := A) (p ≫ r)))
        (shiftOrbitOf U Y a q)
      change shiftOrbitCompHom
        (shiftOrbitOf X U 0 (shiftHomZero (A := A) (p ≫ r)))
        (shiftOrbitOf U Y a q) ∈ HomIdeal.generatedHomSubmodule k
          (endomorphismRelations (ShiftOrbitCategory C A) S) X Y at hfactor
      rw [shiftOrbitComp_zero_left_of] at hfactor
      simpa only [Category.assoc] using hfactor
  | zero =>
      simp
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact
        (HomIdeal.generatedHomSubmodule k
          (endomorphismRelations (ShiftOrbitCategory C A) S) X Y).add_mem ihp ihq
  | smul c q hq ihq =>
      change shiftOrbitLof (k := k) X Y a (c • q) ∈
        HomIdeal.generatedHomSubmodule k
          (endomorphismRelations (ShiftOrbitCategory C A) S) X Y
      rw [map_smul]
      exact
        (HomIdeal.generatedHomSubmodule k
          (endomorphismRelations (ShiftOrbitCategory C A) S) X Y).smul_mem c ihq

/-- An orbit morphism belongs to the orbit-category deletion ideal whenever
all of its homogeneous ambient components belong to the base deletion ideal. -/
theorem mem_orbitIdeal_of_components_mem_ideal
    (S : Set C) {X Y : C} (f : ShiftOrbitHom A X Y)
    (hf : ∀ a : A,
      f a ∈ (ideal (k := k) C S).hom X ((shiftFunctor C a).obj Y)) :
    f ∈ (ideal (k := k) (ShiftOrbitCategory C A) S).hom X Y := by
  classical
  rw [← DirectSum.sum_support_of f]
  apply Submodule.sum_mem
  intro a ha
  exact shiftOrbitOf_mem_orbitIdeal_of_mem_ideal (k := k) S a (f a) (hf a)

end HomogeneousIdeal

section RawComparison

variable {k : Type z} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]
variable (S : Set C) (hS : ShiftInvariant (C := C) A S)

/-- The componentwise raw deletion quotient on shift-orbit categories. -/
noncomputable abbrev orbitRawFunctor
    [HasShift (RawCategory (k := k) C S) A]
    [∀ a : A, (shiftFunctor (RawCategory (k := k) C S) a).Additive]
    [∀ a : A, (shiftFunctor (RawCategory (k := k) C S) a).Linear k]
    [(rawFunctor (k := k) C S).CommShift A] :
    ShiftOrbitCategory C A ⥤
      ShiftOrbitCategory (RawCategory (k := k) C S) A :=
  shiftOrbitMapFunctor (k := k) (A := A) (rawFunctor (k := k) C S)

set_option backward.isDefEq.respectTransparency false in
/-- The componentwise raw orbit map at degree `a` is the ordinary raw
quotient map followed by the shift-commutation isomorphism. -/
theorem orbitRawMapLinear_component {X Y : C}
    (f : ShiftOrbitHom A X Y) (a : A) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ b : A,
        (shiftFunctor (RawCategory (k := k) C S) b).Additive :=
      fun b ↦ rawShiftFunctor_additive (k := k) S hS b
    letI : ∀ b : A,
        (shiftFunctor (RawCategory (k := k) C S) b).Linear k :=
      fun b ↦ rawShiftFunctor_linear (k := k) S hS b
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    (shiftOrbitDescendMapLinear (k := k)
      (rawFunctor (k := k) C S) f) a =
      shiftOrbitDescendHomogeneousMap (rawFunctor (k := k) C S) a (f a) := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ b : A,
      (shiftFunctor (RawCategory (k := k) C S) b).Additive :=
    fun b ↦ rawShiftFunctor_additive (k := k) S hS b
  letI : ∀ b : A,
      (shiftFunctor (RawCategory (k := k) C S) b).Linear k :=
    fun b ↦ rawShiftFunctor_linear (k := k) S hS b
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  classical
  induction f using DirectSum.induction_on with
  | zero =>
      simp [shiftOrbitDescendHomogeneousMap]
  | of b g =>
      rw [← shiftOrbitOf_eq_directSumOf, shiftOrbitDescendMapLinear_of]
      by_cases hba : b = a
      · subst b
        simp [shiftOrbitOf_eq_directSumOf, shiftOrbitDescendHomogeneousMap]
      · simp [shiftOrbitOf_eq_directSumOf, DirectSum.of_apply, hba,
          shiftOrbitDescendHomogeneousMap]
  | add f g hf hg =>
      rw [map_add]
      change _ = shiftOrbitDescendHomogeneousMap
        (rawFunctor (k := k) C S) a (f a + g a)
      rw [DFinsupp.add_apply, hf, hg]
      simp [shiftOrbitDescendHomogeneousMap, Functor.map_add,
        Preadditive.add_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Every homogeneous morphism after the raw quotient has a homogeneous
ambient lift. -/
theorem exists_orbitRawHomogeneous_preimage {X Y : C} (a : A) :
    letI := rawHasShift (k := k) S hS
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    ∀ q : ShiftHom
        ((rawFunctor (k := k) C S).obj X)
        ((rawFunctor (k := k) C S).obj Y) a,
    ∃ f : ShiftHom X Y a,
      shiftOrbitDescendHomogeneousMap
        (rawFunctor (k := k) C S) a f = q := by
  letI := rawHasShift (k := k) S hS
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  intro q
  obtain ⟨f, hf⟩ := (rawFunctor (k := k) C S).map_surjective
    (q ≫ ((rawFunctor (k := k) C S).commShiftIso a).inv.app Y)
  refine ⟨f, ?_⟩
  unfold shiftOrbitDescendHomogeneousMap
  rw [hf, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id q

set_option backward.isDefEq.respectTransparency false in
/-- The componentwise raw orbit quotient is full. -/
theorem orbitRawFunctorFull :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    (shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S)).Full := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  constructor
  intro X Y q
  classical
  change ShiftOrbitHom A
    ((rawFunctor (k := k) C S).obj (show C from X))
    ((rawFunctor (k := k) C S).obj (show C from Y)) at q
  let preimage : ∀ a : A, ShiftHom (show C from X) (show C from Y) a :=
    fun a ↦ Classical.choose
      (exists_orbitRawHomogeneous_preimage (k := k) S hS a (q a))
  let f : ShiftOrbitHom A (show C from X) (show C from Y) :=
    ∑ a ∈ q.support, shiftOrbitOf _ _ a (preimage a)
  refine ⟨f, ?_⟩
  change shiftOrbitDescendMapLinear (k := k)
    (rawFunctor (k := k) C S) f = q
  calc
    shiftOrbitDescendMapLinear (k := k)
        (rawFunctor (k := k) C S) f =
        ∑ a ∈ q.support,
          shiftOrbitDescendMapLinear (k := k)
            (rawFunctor (k := k) C S)
            (shiftOrbitOf _ _ a (preimage a)) := by
              simp only [f, map_sum]
    _ = ∑ a ∈ q.support, shiftOrbitOf _ _ a (q a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [shiftOrbitDescendMapLinear_of]
      exact congrArg (shiftOrbitOf _ _ a)
        (Classical.choose_spec
          (exists_orbitRawHomogeneous_preimage (k := k) S hS a (q a)))
    _ = q := DirectSum.sum_support_of q

set_option backward.isDefEq.respectTransparency false in
/-- The raw orbit quotient kills the ideal generated by the deleted objects
inside the ambient shift-orbit category. -/
theorem orbitRawFunctor_isKilledBy :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    (ideal (k := k) (ShiftOrbitCategory C A) S).IsKilledBy
      (shiftOrbitMapFunctor (k := k) (A := A)
        (rawFunctor (k := k) C S)) := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  intro X Y f hf
  change f ∈ HomIdeal.generatedHomSubmodule k
    (endomorphismRelations (ShiftOrbitCategory C A) S) X Y at hf
  induction hf using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨U, V, r, hr, p, q, rfl⟩
      rcases hr with ⟨rfl, hU⟩
      rw [Functor.map_comp, Functor.map_comp]
      have hzeroRaw := rawFunctor_obj_isZero (k := k) C S hU
      have hzeroOrbit := isZero_shiftOrbitCategory (A := A) hzeroRaw
      have hrzero : (shiftOrbitMapFunctor (k := k) (A := A)
          (rawFunctor (k := k) C S)).map r = 0 :=
        hzeroOrbit.eq_of_src _ _
      rw [hrzero]
      simp
  | zero =>
      exact (shiftOrbitMapFunctor (k := k) (A := A)
        (rawFunctor (k := k) C S)).map_zero X Y
  | add p q hp hq ihp ihq =>
      rw [(shiftOrbitMapFunctor (k := k) (A := A)
        (rawFunctor (k := k) C S)).map_add, ihp, ihq, add_zero]
  | smul c q hq ihq =>
      rw [(shiftOrbitMapFunctor (k := k) (A := A)
        (rawFunctor (k := k) C S)).map_smul, ihq, smul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the componentwise raw orbit quotient is contained in the
orbit-category object-deletion ideal. -/
theorem orbitRawFunctor_kernel_le {X Y : C} (f : ShiftOrbitHom A X Y) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    (shiftOrbitMapFunctor (k := k) (A := A)
        (rawFunctor (k := k) C S)).map f = 0 →
      f ∈ (ideal (k := k) (ShiftOrbitCategory C A) S).hom X Y := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  intro hzero
  apply mem_orbitIdeal_of_components_mem_ideal (k := k) S f
  intro a
  apply ((ideal (k := k) C S).map_eq_zero_iff (f a)).1
  have hcomponent := congrArg
    (fun q : ShiftOrbitHom A
        ((rawFunctor (k := k) C S).obj X)
        ((rawFunctor (k := k) C S).obj Y) ↦ q a) hzero
  change (shiftOrbitDescendMapLinear (k := k)
    (rawFunctor (k := k) C S) f) a = 0 at hcomponent
  rw [orbitRawMapLinear_component (k := k) S hS f a] at hcomponent
  unfold shiftOrbitDescendHomogeneousMap at hcomponent
  apply (cancel_mono
    (((rawFunctor (k := k) C S).commShiftIso a).hom.app Y)).1
  simpa using hcomponent

/-- The raw object-deletion quotient of the ambient orbit category. -/
abbrev RawOrbitDeletionCategory :=
  RawCategory (k := k) (ShiftOrbitCategory C A) S

/-- The faithful comparison from the raw orbit-category deletion quotient to
the orbit category of the raw deletion quotient. -/
noncomputable def rawOrbitDeletionComparisonFunctor
    (hS : ShiftInvariant (C := C) A S) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    RawOrbitDeletionCategory (k := k) (A := A) S ⥤
      ShiftOrbitCategory (RawCategory (k := k) C S) A := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  exact (ideal (k := k) (ShiftOrbitCategory C A) S).quotientLift
    (shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S))
    (orbitRawFunctor_isKilledBy (k := k) S hS)

noncomputable instance rawOrbitDeletionComparisonFunctor_additive :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    (rawOrbitDeletionComparisonFunctor (k := k) S hS).Additive := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  exact HomIdeal.quotientLift_additive
    (ideal (k := k) (ShiftOrbitCategory C A) S)
    (shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S))
    (orbitRawFunctor_isKilledBy (k := k) S hS)

noncomputable instance rawOrbitDeletionComparisonFunctor_linear :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    (rawOrbitDeletionComparisonFunctor (k := k) S hS).Linear k := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  exact HomIdeal.quotientLift_linear
    (ideal (k := k) (ShiftOrbitCategory C A) S)
    (shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S))
    (orbitRawFunctor_isKilledBy (k := k) S hS)

set_option backward.isDefEq.respectTransparency false in
/-- The raw orbit/deletion comparison is full. -/
theorem rawOrbitDeletionComparisonFunctor_full :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    (rawOrbitDeletionComparisonFunctor (k := k) S hS).Full := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  letI : (shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S)).Full :=
    orbitRawFunctorFull (k := k) S hS
  exact HomIdeal.quotientLift_full
    (ideal (k := k) (ShiftOrbitCategory C A) S)
    (shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S))
    (orbitRawFunctor_isKilledBy (k := k) S hS)

set_option backward.isDefEq.respectTransparency false in
/-- The raw orbit/deletion comparison is faithful. -/
theorem rawOrbitDeletionComparisonFunctor_faithful :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    (rawOrbitDeletionComparisonFunctor (k := k) S hS).Faithful := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  exact HomIdeal.quotientLift_faithful
    (ideal (k := k) (ShiftOrbitCategory C A) S)
    (shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S))
    (orbitRawFunctor_isKilledBy (k := k) S hS)
    (fun {X Y} {f} hzero ↦
      orbitRawFunctor_kernel_le (k := k) S hS f hzero)

/-- Surviving raw deletion objects, regarded as objects of the shift-orbit
category of the raw deletion quotient. -/
def OrbitIsSurvivingRaw :
    ShiftOrbitCategory (RawCategory (k := k) C S) A → Prop :=
  fun X ↦ (show RawCategory (k := k) C S from X).as ∉ S

/-- The full subcategory of the raw deletion orbit category on surviving
ambient representatives. -/
abbrev SurvivingRawOrbitCategory
    [HasShift (RawCategory (k := k) C S) A]
    [∀ a : A, (shiftFunctor (RawCategory (k := k) C S) a).Additive] :=
  ObjectProperty.FullSubcategory
    (OrbitIsSurvivingRaw (k := k) (C := C) (A := A) S :
      ObjectProperty
        (ShiftOrbitCategory (RawCategory (k := k) C S) A))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the raw comparison to the surviving objects on both
sides. -/
noncomputable def orbitDeletionToSurvivingRawOrbitFunctor :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    DeletionCategory (k := k) (ShiftOrbitCategory C A) S ⥤
      SurvivingRawOrbitCategory (k := k) (A := A) S := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  let P := IsSurvivingRaw (k := k) (ShiftOrbitCategory C A) S
  let Q : ObjectProperty
      (ShiftOrbitCategory (RawCategory (k := k) C S) A) :=
    OrbitIsSurvivingRaw (k := k) (C := C) (A := A) S
  exact ObjectProperty.lift Q
    (P.ι ⋙ rawOrbitDeletionComparisonFunctor (k := k) S hS)
    (fun X ↦ X.property)

noncomputable instance orbitDeletionToSurvivingRawOrbitFunctor_additive :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    (orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS).Additive := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  dsimp only [orbitDeletionToSurvivingRawOrbitFunctor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance orbitDeletionToSurvivingRawOrbitFunctor_linear :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    let F := orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS
    F.Linear k := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  change (orbitDeletionToSurvivingRawOrbitFunctor
    (k := k) S hS).Linear k
  letI : (rawOrbitDeletionComparisonFunctor
      (k := k) S hS).Linear k :=
    rawOrbitDeletionComparisonFunctor_linear (k := k) S hS
  constructor
  intro X Y f r
  apply ObjectProperty.hom_ext
  exact (rawOrbitDeletionComparisonFunctor
    (k := k) S hS).map_smul r f.hom

set_option backward.isDefEq.respectTransparency false in
/-- The surviving restriction of the raw comparison is full. -/
theorem orbitDeletionToSurvivingRawOrbitFunctor_full :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    (orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS).Full := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawOrbitDeletionComparisonFunctor (k := k) S hS).Full :=
    rawOrbitDeletionComparisonFunctor_full (k := k) S hS
  let P := IsSurvivingRaw (k := k) (ShiftOrbitCategory C A) S
  let F := P.ι ⋙ rawOrbitDeletionComparisonFunctor (k := k) S hS
  haveI : F.Full := inferInstance
  constructor
  intro X Y f
  obtain ⟨g, hg⟩ := F.map_surjective f.hom
  refine ⟨g, ?_⟩
  apply ObjectProperty.hom_ext
  exact hg

set_option backward.isDefEq.respectTransparency false in
/-- The surviving restriction of the raw comparison is faithful. -/
theorem orbitDeletionToSurvivingRawOrbitFunctor_faithful :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    (orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS).Faithful := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawOrbitDeletionComparisonFunctor (k := k) S hS).Faithful :=
    rawOrbitDeletionComparisonFunctor_faithful (k := k) S hS
  let P := IsSurvivingRaw (k := k) (ShiftOrbitCategory C A) S
  let F := P.ι ⋙ rawOrbitDeletionComparisonFunctor (k := k) S hS
  haveI : F.Faithful := inferInstance
  constructor
  intro X Y f g hfg
  apply F.map_injective
  exact congrArg (fun q ↦ q.hom) hfg

set_option backward.isDefEq.respectTransparency false in
/-- Every surviving raw deletion object is represented by a surviving object
of the ambient orbit-category deletion quotient. -/
theorem orbitDeletionToSurvivingRawOrbitFunctor_essSurj :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    (orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS).EssSurj := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  constructor
  intro Y
  let X : DeletionCategory (k := k) (ShiftOrbitCategory C A) S :=
    ⟨(rawFunctor (k := k) (ShiftOrbitCategory C A) S).obj Y.obj.as,
      Y.property⟩
  refine ⟨X, ?_⟩
  have heq :
      ((orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS).obj X).obj =
        Y.obj := by
    apply CategoryTheory.Quotient.ext
    rfl
  exact ⟨ObjectProperty.isoMk _ (eqToIso heq)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Deleting `S` from the ambient shift-orbit category is equivalent to the
surviving full subcategory of the shift-orbit category of the raw deletion
quotient. -/
noncomputable def orbitDeletionToSurvivingRawOrbitEquivalence :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    DeletionCategory (k := k) (ShiftOrbitCategory C A) S ≌
      SurvivingRawOrbitCategory (k := k) (A := A) S := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  let F := orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS
  letI : F.Full := orbitDeletionToSurvivingRawOrbitFunctor_full (k := k) S hS
  letI : F.Faithful :=
    orbitDeletionToSurvivingRawOrbitFunctor_faithful (k := k) S hS
  letI : F.EssSurj :=
    orbitDeletionToSurvivingRawOrbitFunctor_essSurj (k := k) S hS
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

set_option backward.isDefEq.respectTransparency false in
noncomputable instance
    orbitDeletionToSurvivingRawOrbitEquivalence_functor_additive :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    let E := orbitDeletionToSurvivingRawOrbitEquivalence (k := k) S hS
    E.functor.Additive := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  change (orbitDeletionToSurvivingRawOrbitFunctor
    (k := k) S hS).Additive
  exact orbitDeletionToSurvivingRawOrbitFunctor_additive (k := k) S hS

set_option backward.isDefEq.respectTransparency false in
noncomputable instance
    orbitDeletionToSurvivingRawOrbitEquivalence_functor_linear :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    let E := orbitDeletionToSurvivingRawOrbitEquivalence (k := k) S hS
    E.functor.Linear k := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  change (orbitDeletionToSurvivingRawOrbitFunctor
    (k := k) S hS).Linear k
  exact orbitDeletionToSurvivingRawOrbitFunctor_linear (k := k) S hS

set_option backward.isDefEq.respectTransparency false in
/-- The orbit category of the surviving deletion category includes into the
raw deletion orbit category and lands in its surviving full subcategory. -/
noncomputable def deletionShiftOrbitInclusionFunctor :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    ShiftOrbitCategory (DeletionCategory (k := k) C S) A ⥤
      SurvivingRawOrbitCategory (k := k) (A := A) S := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let P := IsSurvivingRaw (k := k) C S
  let Q : ObjectProperty
      (ShiftOrbitCategory (RawCategory (k := k) C S) A) :=
    OrbitIsSurvivingRaw (k := k) (C := C) (A := A) S
  letI : P.ι.CommShift A := deletionInclusionCommShift (k := k) S hS
  exact ObjectProperty.lift Q
    (shiftOrbitMapFunctor (k := k) (A := A) P.ι)
    (fun X ↦ X.property)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance deletionShiftOrbitInclusionFunctor_additive :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    let F := deletionShiftOrbitInclusionFunctor (k := k) S hS
    F.Additive := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  change (deletionShiftOrbitInclusionFunctor (k := k) S hS).Additive
  dsimp only [deletionShiftOrbitInclusionFunctor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance deletionShiftOrbitInclusionFunctor_linear :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hS a
    let F := deletionShiftOrbitInclusionFunctor (k := k) S hS
    F.Linear k := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  change (deletionShiftOrbitInclusionFunctor (k := k) S hS).Linear k
  let P := IsSurvivingRaw (k := k) C S
  letI : P.ι.CommShift A := deletionInclusionCommShift (k := k) S hS
  let F := shiftOrbitMapFunctor (k := k) (A := A) P.ι
  haveI : F.Linear k := inferInstance
  constructor
  intro X Y f r
  apply ObjectProperty.hom_ext
  exact F.map_smul r f

set_option backward.isDefEq.respectTransparency false in
/-- The surviving inclusion from the orbit of the deletion category is
full. -/
theorem deletionShiftOrbitInclusionFunctor_full :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    (deletionShiftOrbitInclusionFunctor (k := k) S hS).Full := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let P := IsSurvivingRaw (k := k) C S
  letI : P.ι.CommShift A := deletionInclusionCommShift (k := k) S hS
  let F := shiftOrbitMapFunctor (k := k) (A := A) P.ι
  haveI : F.Full := inferInstance
  constructor
  intro X Y f
  obtain ⟨g, hg⟩ := F.map_surjective f.hom
  refine ⟨g, ?_⟩
  apply ObjectProperty.hom_ext
  exact hg

set_option backward.isDefEq.respectTransparency false in
/-- The surviving inclusion from the orbit of the deletion category is
faithful. -/
theorem deletionShiftOrbitInclusionFunctor_faithful :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    (deletionShiftOrbitInclusionFunctor (k := k) S hS).Faithful := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let P := IsSurvivingRaw (k := k) C S
  letI : P.ι.CommShift A := deletionInclusionCommShift (k := k) S hS
  let F := shiftOrbitMapFunctor (k := k) (A := A) P.ι
  haveI : F.Faithful := inferInstance
  constructor
  intro X Y f g hfg
  apply F.map_injective
  exact congrArg (fun q ↦ q.hom) hfg

set_option backward.isDefEq.respectTransparency false in
/-- Every surviving raw orbit object comes from an object of the deletion
category. -/
theorem deletionShiftOrbitInclusionFunctor_essSurj :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    (deletionShiftOrbitInclusionFunctor (k := k) S hS).EssSurj := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  constructor
  intro Y
  let X : DeletionCategory (k := k) C S := ⟨Y.obj, Y.property⟩
  refine ⟨(show ShiftOrbitCategory (DeletionCategory (k := k) C S) A from X), ?_⟩
  have heq :
      ((deletionShiftOrbitInclusionFunctor (k := k) S hS).obj X).obj =
        Y.obj := rfl
  exact ⟨ObjectProperty.isoMk _ (eqToIso heq)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The orbit category of `C/(S)` is equivalent to the surviving part of the
raw deletion orbit category. -/
noncomputable def deletionShiftOrbitInclusionEquivalence :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    ShiftOrbitCategory (DeletionCategory (k := k) C S) A ≌
      SurvivingRawOrbitCategory (k := k) (A := A) S := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let F := deletionShiftOrbitInclusionFunctor (k := k) S hS
  letI : F.Full := deletionShiftOrbitInclusionFunctor_full (k := k) S hS
  letI : F.Faithful :=
    deletionShiftOrbitInclusionFunctor_faithful (k := k) S hS
  letI : F.EssSurj :=
    deletionShiftOrbitInclusionFunctor_essSurj (k := k) S hS
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

set_option backward.isDefEq.respectTransparency false in
noncomputable instance deletionShiftOrbitInclusionEquivalence_functor_additive :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    let E := deletionShiftOrbitInclusionEquivalence (k := k) S hS
    E.functor.Additive := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  change (deletionShiftOrbitInclusionFunctor (k := k) S hS).Additive
  exact deletionShiftOrbitInclusionFunctor_additive (k := k) S hS

set_option backward.isDefEq.respectTransparency false in
noncomputable instance deletionShiftOrbitInclusionEquivalence_functor_linear :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hS a
    let E := deletionShiftOrbitInclusionEquivalence (k := k) S hS
    E.functor.Linear k := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  change (deletionShiftOrbitInclusionFunctor (k := k) S hS).Linear k
  exact deletionShiftOrbitInclusionFunctor_linear (k := k) S hS

set_option backward.isDefEq.respectTransparency false in
/-- Object deletion commutes with passage to the shift-orbit category:
`(C/(S))/A ≃ (C/A)/(S)`. -/
noncomputable def deletionOrbitEquivalence :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    ShiftOrbitCategory (DeletionCategory (k := k) C S) A ≌
      DeletionCategory (k := k) (ShiftOrbitCategory C A) S := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  exact (deletionShiftOrbitInclusionEquivalence (k := k) S hS).trans
    (orbitDeletionToSurvivingRawOrbitEquivalence (k := k) S hS).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable instance deletionOrbitEquivalence_functor_additive :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    let E := deletionOrbitEquivalence (k := k) S hS
    E.functor.Additive := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let eIncl := deletionShiftOrbitInclusionEquivalence (k := k) S hS
  let eRaw := orbitDeletionToSurvivingRawOrbitEquivalence (k := k) S hS
  letI : eIncl.functor.Additive :=
    deletionShiftOrbitInclusionEquivalence_functor_additive (k := k) S hS
  letI : eRaw.functor.Additive :=
    orbitDeletionToSurvivingRawOrbitEquivalence_functor_additive (k := k) S hS
  letI : eRaw.inverse.Additive := inferInstance
  change (eIncl.functor ⋙ eRaw.inverse).Additive
  infer_instance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance deletionOrbitEquivalence_functor_linear :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hS a
    let E := deletionOrbitEquivalence (k := k) S hS
    E.functor.Linear k := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let eIncl := deletionShiftOrbitInclusionEquivalence (k := k) S hS
  let eRaw := orbitDeletionToSurvivingRawOrbitEquivalence (k := k) S hS
  letI : eIncl.functor.Linear k :=
    deletionShiftOrbitInclusionEquivalence_functor_linear (k := k) S hS
  letI : eRaw.functor.Linear k :=
    orbitDeletionToSurvivingRawOrbitEquivalence_functor_linear (k := k) S hS
  letI : eRaw.inverse.Linear k := inferInstance
  change (eIncl.functor ⋙ eRaw.inverse).Linear k
  infer_instance

end RawComparison

end MagnitudeConjecture.ObjectDeletion
