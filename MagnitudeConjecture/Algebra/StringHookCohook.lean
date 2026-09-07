import MagnitudeConjecture.Algebra.StringBoundaryExtension
import MagnitudeConjecture.Algebra.StringReverse
import Mathlib.Data.Nat.Find

/-!
# Maximal hooks and cohooks at string endpoints

This file records Butler--Ringel's endpoint terminology in the current word
convention.  At the right endpoint, a hook begins with a positive letter and
continues along a negative arm until a deep is reached.  A cohook begins with
a negative letter and continues along a positive arm until a peak is reached.

Because the formalization uses right modules, the canonical hook map is the
resulting quotient projection and the canonical cohook map is the resulting
submodule inclusion.  Reversal makes the same definitions available at the
left endpoint.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A word starts on a peak at its right endpoint when no positive displayed
arrow can be appended while retaining the string condition. -/
def StartsOnPeak (C : Word R) : Prop :=
  ∀ {z : Q} (a : C.target ⟶ z),
    ¬ IsString R (C.path.comp (positiveArrow a).toPath)

/-- A word starts in a deep at its right endpoint when no negative displayed
arrow can be appended while retaining the string condition. -/
def StartsInDeep (C : Word R) : Prop :=
  ∀ {z : Q} (a : z ⟶ C.target),
    ¬ IsString R (C.path.comp (negativeArrow a).toPath)

/-- Left-end peak terminology, defined by reversal. -/
def EndsOnPeak (C : Word R) : Prop := C.reverse.StartsOnPeak

/-- Left-end deep terminology, defined by reversal. -/
def EndsInDeep (C : Word R) : Prop := C.reverse.StartsInDeep

@[simp]
theorem reverse_startsOnPeak (C : Word R) :
    C.reverse.StartsOnPeak ↔ C.EndsOnPeak := Iff.rfl

@[simp]
theorem reverse_startsInDeep (C : Word R) :
    C.reverse.StartsInDeep ↔ C.EndsInDeep := Iff.rfl

@[simp]
theorem reverse_endsOnPeak (C : Word R) :
    C.reverse.EndsOnPeak ↔ C.StartsOnPeak := by
  rw [EndsOnPeak, reverse_reverse]

@[simp]
theorem reverse_endsInDeep (C : Word R) :
    C.reverse.EndsInDeep ↔ C.StartsInDeep := by
  rw [EndsInDeep, reverse_reverse]

/-- Admissibility ensures that every word has a maximal negative extension
arm.  No finiteness or uniqueness of the displayed arrows is needed. -/
theorem exists_negativeExtension_startsInDeep
    (hR : IsAdmissible R) (C : Word R) :
    ∃ D : Word R, ∃ _arm : NegativeExtension C D, D.StartsInDeep := by
  classical
  obtain ⟨N, _, hlong⟩ := hR.long_paths_mem
  let P : ℕ → Prop := fun n ↦
    ∃ D : Word R, ∃ arm : NegativeExtension C D, arm.steps = n
  have hPzero : P 0 := ⟨C, NegativeExtension.base, rfl⟩
  have hPmax : P (Nat.findGreatest P N) :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le N) hPzero
  rcases hPmax with ⟨D, arm, harmSteps⟩
  refine ⟨D, arm, ?_⟩
  intro z a hvalid
  let next : NegativeExtension C
      (append R D (negativeArrow a) hvalid) :=
    NegativeExtension.step arm a hvalid
  have hnextLt : next.steps < N :=
    next.steps_lt_of_long_paths_mem hlong
  have hPnext : P next.steps :=
    ⟨append R D (negativeArrow a) hvalid, next, rfl⟩
  have hnextLeMax : next.steps ≤ Nat.findGreatest P N :=
    Nat.le_findGreatest (P := P) (Nat.le_of_lt hnextLt) hPnext
  have hnextSteps : next.steps = arm.steps + 1 := rfl
  omega

/-- Admissibility ensures that every word has a maximal positive extension
arm. -/
theorem exists_positiveExtension_startsOnPeak
    (hR : IsAdmissible R) (C : Word R) :
    ∃ D : Word R, ∃ _arm : PositiveExtension C D, D.StartsOnPeak := by
  classical
  obtain ⟨N, _, hlong⟩ := hR.long_paths_mem
  let P : ℕ → Prop := fun n ↦
    ∃ D : Word R, ∃ arm : PositiveExtension C D, arm.steps = n
  have hPzero : P 0 := ⟨C, PositiveExtension.base, rfl⟩
  have hPmax : P (Nat.findGreatest P N) :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le N) hPzero
  rcases hPmax with ⟨D, arm, harmSteps⟩
  refine ⟨D, arm, ?_⟩
  intro z a hvalid
  let next : PositiveExtension C
      (append R D (positiveArrow a) hvalid) :=
    PositiveExtension.step arm a hvalid
  have hnextLt : next.steps < N :=
    next.steps_lt_of_long_paths_mem hlong
  have hPnext : P next.steps :=
    ⟨append R D (positiveArrow a) hvalid, next, rfl⟩
  have hnextLeMax : next.steps ≤ Nat.findGreatest P N :=
    Nat.le_findGreatest (P := P) (Nat.le_of_lt hnextLt) hPnext
  have hnextSteps : next.steps = arm.steps + 1 := rfl
  omega

/-- A maximal right hook: append one positive letter and then a negative arm
whose endpoint starts in a deep. -/
structure HookExtension (C D : Word R) where
  vertex : Q
  arrow : C.target ⟶ vertex
  valid : IsString R (C.path.comp (positiveArrow arrow).toPath)
  tail : NegativeExtension
    (append R C (positiveArrow arrow) valid) D
  maximal : D.StartsInDeep

namespace HookExtension

/-- Every valid initial positive letter extends to a maximal hook. -/
theorem exists_of_append_positive
    (hR : IsAdmissible R) (C : Word R) {z : Q}
    (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath)) :
    ∃ (D : Word R) (hook : HookExtension C D),
      (⟨hook.vertex, hook.arrow⟩ : Quiver.Star C.target) = ⟨z, a⟩ := by
  rcases exists_negativeExtension_startsInDeep hR
      (append R C (positiveArrow a) h) with ⟨D, tail, hdeep⟩
  exact ⟨D, {
    vertex := z
    arrow := a
    valid := h
    tail := tail
    maximal := hdeep }, rfl⟩

/-- A hook is in particular an arbitrary extension with positive boundary. -/
def toPositiveBoundaryExtension {C D : Word R}
    (hook : HookExtension C D) : PositiveBoundaryExtension C D where
  vertex := hook.vertex
  arrow := hook.arrow
  valid := hook.valid
  tail := hook.tail.toRightExtension

/-- The number of letters appended by the hook. -/
def steps {C D : Word R} (hook : HookExtension C D) : ℕ :=
  hook.tail.steps + 1

@[simp]
theorem result_length {C D : Word R} (hook : HookExtension C D) :
    D.length = C.length + hook.steps := by
  rw [hook.tail.result_length, append_length]
  simp only [steps]
  omega

/-- The canonical right-module hook projection. -/
def moduleMap {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶ C.rightModule hmono :=
  hook.toPositiveBoundaryExtension.rightModuleProjection hmono

instance moduleMap_epi {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) : Epi (hook.moduleMap hmono) := by
  dsimp only [moduleMap]
  infer_instance

/-- The presence of a hook witnesses that the original word does not start
on a peak. -/
theorem not_startsOnPeak {C D : Word R} (hook : HookExtension C D) :
    ¬ C.StartsOnPeak := by
  intro hpeak
  exact hpeak hook.arrow hook.valid

end HookExtension

/-- A maximal right cohook: append one negative letter and then a positive
arm whose endpoint starts on a peak. -/
structure CohookExtension (C D : Word R) where
  vertex : Q
  arrow : vertex ⟶ C.target
  valid : IsString R (C.path.comp (negativeArrow arrow).toPath)
  tail : PositiveExtension
    (append R C (negativeArrow arrow) valid) D
  maximal : D.StartsOnPeak

namespace CohookExtension

/-- Every valid initial negative letter extends to a maximal cohook. -/
theorem exists_of_append_negative
    (hR : IsAdmissible R) (C : Word R) {z : Q}
    (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath)) :
    ∃ (D : Word R) (cohook : CohookExtension C D),
      (⟨cohook.vertex, cohook.arrow⟩ : Quiver.Costar C.target) = ⟨z, a⟩ := by
  rcases exists_positiveExtension_startsOnPeak hR
      (append R C (negativeArrow a) h) with ⟨D, tail, hpeak⟩
  exact ⟨D, {
    vertex := z
    arrow := a
    valid := h
    tail := tail
    maximal := hpeak }, rfl⟩

/-- A cohook is in particular an arbitrary extension with negative boundary. -/
def toNegativeBoundaryExtension {C D : Word R}
    (cohook : CohookExtension C D) : NegativeBoundaryExtension C D where
  vertex := cohook.vertex
  arrow := cohook.arrow
  valid := cohook.valid
  tail := cohook.tail.toRightExtension

/-- The number of letters appended by the cohook. -/
def steps {C D : Word R} (cohook : CohookExtension C D) : ℕ :=
  cohook.tail.steps + 1

@[simp]
theorem result_length {C D : Word R} (cohook : CohookExtension C D) :
    D.length = C.length + cohook.steps := by
  rw [cohook.tail.result_length, append_length]
  simp only [steps]
  omega

/-- The canonical right-module cohook inclusion. -/
def moduleMap {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) :
    C.rightModule hmono ⟶ D.rightModule hmono :=
  cohook.toNegativeBoundaryExtension.rightModuleInclusion hmono

instance moduleMap_mono {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) : Mono (cohook.moduleMap hmono) := by
  dsimp only [moduleMap]
  infer_instance

/-- The right-cohook inclusion carries an inherited basis vector to the
corresponding prefix position in the extended word. -/
@[simp]
theorem moduleMap_app_single_position {C D : Word R}
    (cohook : CohookExtension C D) (hmono : IsMonomial R) {x : Q}
    (i : C.PositionAt x) (c : k) :
    (cohook.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single i c) =
      Finsupp.single
        (cohook.toNegativeBoundaryExtension.toRightExtension.position i) c := by
  change cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion x
      (Finsupp.single i c) = _
  exact cohook.toNegativeBoundaryExtension.toRightExtension.spaceInclusion_single
    i c

/-- The presence of a cohook witnesses that the original word does not start
in a deep. -/
theorem not_startsInDeep {C D : Word R} (cohook : CohookExtension C D) :
    ¬ C.StartsInDeep := by
  intro hdeep
  exact hdeep cohook.arrow cohook.valid

end CohookExtension

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
