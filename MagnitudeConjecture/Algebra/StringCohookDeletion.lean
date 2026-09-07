import MagnitudeConjecture.Algebra.StringLeftHookCohook

/-!
# Deleting maximal cohooks from string endpoints

In Butler--Ringel's peak cases, the endpoint operation is not a new hook:
the given word is already a maximal cohook extension of a shorter word, and
the cohook is deleted.  This file packages that relation in the direction
used by right-module Auslander--Reiten sequences.  Its canonical map goes
from the shortened word into the original word and is therefore the existing
negative-boundary inclusion.

The left-hand construction is defined on reversed words but exposes maps and
positions in the original orientation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- Deleting a maximal cohook at the right endpoint of `C` produces `D`.
Equivalently, `C` is a maximal right cohook extension of `D`. -/
structure CohookDeletion (C D : Word R) where
  cohook : CohookExtension D C

namespace CohookDeletion

/-- The number of letters removed by a right cohook deletion. -/
def steps {C D : Word R} (deletion : CohookDeletion C D) : ℕ :=
  deletion.cohook.steps

/-- A right cohook deletion removes a nonempty terminal segment. -/
theorem steps_pos {C D : Word R} (deletion : CohookDeletion C D) :
    0 < deletion.steps := by
  simp only [steps, CohookExtension.steps]
  omega

/-- Reattaching the deleted cohook recovers the original word length. -/
@[simp]
theorem source_length {C D : Word R} (deletion : CohookDeletion C D) :
    C.length = D.length + deletion.steps := by
  exact deletion.cohook.result_length

/-- A word from which a right cohook can be deleted starts on a peak at that
endpoint. -/
theorem source_startsOnPeak {C D : Word R}
    (deletion : CohookDeletion C D) : C.StartsOnPeak :=
  deletion.cohook.maximal

/-- The shortened word is not already in a deep at the deletion endpoint. -/
theorem result_not_startsInDeep {C D : Word R}
    (deletion : CohookDeletion C D) : ¬ D.StartsInDeep :=
  deletion.cohook.not_startsInDeep

/-- Embed an occurrence of the shortened word into the original word. -/
def position {C D : Word R} (deletion : CohookDeletion C D) {x : Q}
    (i : D.PositionAt x) : C.PositionAt x :=
  deletion.cohook.toNegativeBoundaryExtension.toRightExtension.position i

@[simp]
theorem position_index {C D : Word R} (deletion : CohookDeletion C D)
    {x : Q} (i : D.PositionAt x) :
    (deletion.position i).index = i.index := by
  exact deletion.cohook.toNegativeBoundaryExtension.toRightExtension.position_index i

/-- The canonical right-module map associated to deleting a right cohook. -/
def moduleMap {C D : Word R} (deletion : CohookDeletion C D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶ C.rightModule hmono :=
  deletion.cohook.moduleMap hmono

instance moduleMap_mono {C D : Word R} (deletion : CohookDeletion C D)
    (hmono : IsMonomial R) : Mono (deletion.moduleMap hmono) := by
  dsimp only [moduleMap]
  infer_instance

/-- The right-cohook deletion map sends every basis vector to the inherited
position of the original word. -/
@[simp]
theorem moduleMap_app_single {C D : Word R}
    (deletion : CohookDeletion C D) (hmono : IsMonomial R) {x : Q}
    (i : D.PositionAt x) (c : k) :
    (deletion.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single i c) =
      Finsupp.single (deletion.position i) c := by
  change
    deletion.cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion x
        (Finsupp.single i c) = _
  rw [RightExtension.spaceInclusion_single]
  rfl

end CohookDeletion

/-- Deleting a maximal cohook at the left endpoint of `C` produces `D`.
After reversing both words this is an ordinary right cohook deletion. -/
structure LeftCohookDeletion (C D : Word R) where
  cohook : CohookExtension D.reverse C.reverse

/-- Reversal turns a right cohook deletion into a left cohook deletion of the
reversed word. -/
def CohookDeletion.toReverseLeftCohookDeletion {C D : Word R}
    (deletion : CohookDeletion C D) :
    LeftCohookDeletion C.reverse D.reverse where
  cohook := Eq.mp
    (congrArg₂ (fun X Y : Word R ↦ CohookExtension X Y)
      (reverse_reverse R D).symm (reverse_reverse R C).symm)
    deletion.cohook

namespace LeftCohookDeletion

/-- The underlying right cohook deletion after reversing both words. -/
def toReverseDeletion {C D : Word R}
    (deletion : LeftCohookDeletion C D) :
    CohookDeletion C.reverse D.reverse :=
  ⟨deletion.cohook⟩

/-- Regard a left cohook deletion as the corresponding negative left
boundary extension of the shortened word. -/
def toLeftNegativeBoundaryExtension {C D : Word R}
    (deletion : LeftCohookDeletion C D) :
    LeftNegativeBoundaryExtension D where
  reverseResult := C.reverse
  extension := deletion.cohook.toNegativeBoundaryExtension

/-- The left-boundary extension associated to a deletion recovers the source
word literally up to the canonical double-reversal equality. -/
@[simp]
theorem toLeftNegativeBoundaryExtension_result {C D : Word R}
    (deletion : LeftCohookDeletion C D) :
    deletion.toLeftNegativeBoundaryExtension.result = C := by
  exact reverse_reverse R C

/-- The number of letters removed by a left cohook deletion. -/
def steps {C D : Word R} (deletion : LeftCohookDeletion C D) : ℕ :=
  deletion.cohook.steps

/-- A left cohook deletion removes a nonempty initial segment. -/
theorem steps_pos {C D : Word R} (deletion : LeftCohookDeletion C D) :
    0 < deletion.steps := by
  simp only [steps, CohookExtension.steps]
  omega

/-- Reattaching the deleted left cohook recovers the original word length. -/
@[simp]
theorem source_length {C D : Word R} (deletion : LeftCohookDeletion C D) :
    C.length = D.length + deletion.steps := by
  have h := deletion.cohook.result_length
  simpa only [reverse_length, steps] using h

/-- A word from which a left cohook can be deleted ends on a peak. -/
theorem source_endsOnPeak {C D : Word R}
    (deletion : LeftCohookDeletion C D) : C.EndsOnPeak :=
  deletion.cohook.maximal

/-- The shortened word does not already end in a deep. -/
theorem result_not_endsInDeep {C D : Word R}
    (deletion : LeftCohookDeletion C D) : ¬ D.EndsInDeep :=
  deletion.cohook.not_startsInDeep

/-- Embed an occurrence of the shortened word into the original word. -/
def position {C D : Word R} (deletion : LeftCohookDeletion C D) {x : Q}
    (i : D.PositionAt x) : C.PositionAt x :=
  unreversePosition C
    (deletion.cohook.toNegativeBoundaryExtension.toRightExtension.position
      (reversePosition D i))

/-- The inherited positions are shifted by the number of letters deleted on
the left. -/
@[simp]
theorem position_index {C D : Word R} (deletion : LeftCohookDeletion C D)
    {x : Q} (i : D.PositionAt x) :
    (deletion.position i).index = deletion.steps + i.index := by
  rw [position, unreversePosition_index,
    RightExtension.position_index, reversePosition_index,
    deletion.source_length]
  have hi := i.index_le
  omega

/-- The canonical right-module map associated to deleting a left cohook. -/
def moduleMap {C D : Word R} (deletion : LeftCohookDeletion C D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶ C.rightModule hmono :=
  (reverseRightModuleIso D hmono).hom ≫
    deletion.cohook.moduleMap hmono ≫
    (reverseRightModuleIso C hmono).inv

instance moduleMap_mono {C D : Word R}
    (deletion : LeftCohookDeletion C D)
    (hmono : IsMonomial R) : Mono (deletion.moduleMap hmono) := by
  dsimp only [moduleMap]
  infer_instance

/-- The left-cohook deletion map sends every basis vector to the inherited
position of the original word. -/
@[simp]
theorem moduleMap_app_single {C D : Word R}
    (deletion : LeftCohookDeletion C D) (hmono : IsMonomial R) {x : Q}
    (i : D.PositionAt x) (c : k) :
    (deletion.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single i c) =
      Finsupp.single (deletion.position i) c := by
  change (reverseSpaceEquiv C x).symm
      (deletion.cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion x
        (reverseSpaceEquiv D x (Finsupp.single i c))) = _
  rw [reverseSpaceEquiv_single, RightExtension.spaceInclusion_single,
    reverseSpaceEquiv_symm_single]
  rfl

end LeftCohookDeletion

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
