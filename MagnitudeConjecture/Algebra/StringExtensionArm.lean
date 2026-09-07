import MagnitudeConjecture.Algebra.StringModuleExtension

/-!
# Iterated endpoint extensions of string modules

An extension arm records a finite sequence of same-sign letters appended at
the right endpoint of a string.  Negative arms compose the canonical
one-letter inclusions; positive arms compose the canonical one-letter
projections in the reverse direction.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A finite sequence of negative letters appended to `C`. -/
inductive NegativeExtension (C : Word R) : Word R → Type u
  | base : NegativeExtension C C
  | step {D : Word R} (arm : NegativeExtension C D) {z : Q}
      (a : z ⟶ D.target)
      (h : IsString R (D.path.comp (negativeArrow a).toPath)) :
      NegativeExtension C (append R D (negativeArrow a) h)

namespace NegativeExtension

/-- A negative arm does not change the source vertex. -/
theorem source_eq {C D : Word R} (arm : NegativeExtension C D) :
    D.source = C.source := by
  induction arm with
  | base => rfl
  | step arm a h ih => exact ih

/-- The ordinary displayed-quiver path traversed by a negative arm, from its
new endpoint back to the original endpoint. -/
def ordinaryPath {C D : Word R} : NegativeExtension C D →
    Quiver.Path D.target C.target
  | .base => Quiver.Path.nil
  | .step arm a _ => a.toPath.comp arm.ordinaryPath

/-- Number of letters in a negative extension arm. -/
def steps {C D : Word R} : NegativeExtension C D → ℕ
  | .base => 0
  | .step arm _ _ => arm.steps + 1

@[simp]
theorem ordinaryPath_length {C D : Word R}
    (arm : NegativeExtension C D) :
    arm.ordinaryPath.length = arm.steps := by
  induction arm with
  | base => rfl
  | step arm a h ih => simp [ordinaryPath, steps, ih, Nat.add_comm]

/-- Reversing the final word exposes the negative arm as a positive ordinary
prefix. -/
theorem exists_reverse_suffix {C D : Word R}
    (arm : NegativeExtension C D) :
    ∃ r : SignedPath C.target D.source,
      D.path.reverse = (positivePath arm.ordinaryPath).comp r := by
  induction arm with
  | base => exact ⟨C.path.reverse, by simp [ordinaryPath]⟩
  | @step D arm z a h ih =>
      rcases ih with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      change (D.path.comp (negativeArrow a).toPath).reverse =
        (positivePath (a.toPath.comp arm.ordinaryPath)).comp r
      calc
        (D.path.comp (negativeArrow a).toPath).reverse =
            (negativeArrow a).toPath.reverse.comp D.path.reverse :=
          @Quiver.Path.reverse_comp (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q) _ _ _ _
            D.path (negativeArrow a).toPath
        _ = (positiveArrow a).toPath.comp D.path.reverse := by
          rw [Quiver.Path.reverse_toPath, reverse_negativeArrow]
        _ = (positiveArrow a).toPath.comp
            ((positivePath arm.ordinaryPath).comp r) := by rw [hr]
        _ = (positivePath (a.toPath.comp arm.ordinaryPath)).comp r := by
          rw [positivePath_comp, positivePath_toPath (Q := Q)]
          simp only [Quiver.Path.comp_assoc]

/-- The ordinary path of a negative arm occurs positively in the reversed
final word. -/
theorem positivePath_ordinaryPath_contiguous_reverse {C D : Word R}
    (arm : NegativeExtension C D) :
    IsContiguousSubpath (positivePath arm.ordinaryPath) D.path.reverse := by
  rcases arm.exists_reverse_suffix with ⟨r, hr⟩
  refine ⟨Quiver.Path.nil, r, ?_⟩
  simpa using hr

/-- The ordinary path underlying a negative arm survives the relation
quotient. -/
theorem pathMap_ordinaryPath_ne_zero {C D : Word R}
    (arm : NegativeExtension C D) :
    pathMap R arm.ordinaryPath ≠ 0 :=
  D.isString.2.2 arm.ordinaryPath
    arm.positivePath_ordinaryPath_contiguous_reverse

/-- Any uniform admissibility bound for killed ordinary paths strictly bounds
the number of steps in a negative arm. -/
theorem steps_lt_of_long_paths_mem {C D : Word R}
    (arm : NegativeExtension C D) {N : ℕ}
    (hlong : ∀ {x y : Q} (p : Quiver.Path x y), N ≤ p.length →
      LinearPathCategory.pathHom p ∈
        HomIdeal.generatedHomSubmodule k R
          (LinearPathCategory.obj k Q y)
          (LinearPathCategory.obj k Q x)) :
    arm.steps < N := by
  apply Nat.lt_of_not_ge
  intro hN
  apply arm.pathMap_ordinaryPath_ne_zero
  apply (pathMap_eq_zero_iff_mem_relationIdeal R arm.ordinaryPath).2
  apply hlong arm.ordinaryPath
  simpa only [ordinaryPath_length] using hN

/-- The endpoint word is longer by exactly the number of arm steps. -/
@[simp]
theorem result_length {C D : Word R} (arm : NegativeExtension C D) :
    D.length = C.length + arm.steps := by
  induction arm with
  | base => rfl
  | step arm a h ih => simp [steps, ih, Nat.add_assoc]

/-- Concatenate two negative extension arms. -/
def trans {C D E : Word R}
    (first : NegativeExtension C D)
    (second : NegativeExtension D E) : NegativeExtension C E :=
  match second with
  | .base => first
  | .step arm a h => .step (first.trans arm) a h

@[simp]
theorem steps_trans {C D E : Word R}
    (first : NegativeExtension C D)
    (second : NegativeExtension D E) :
    (first.trans second).steps = first.steps + second.steps := by
  induction second with
  | base => simp [trans, steps]
  | step arm a h ih => simp [trans, steps, ih, Nat.add_assoc]

/-- Every initial number of steps of a negative arm is represented by a
prefix arm, followed by a residual negative arm. -/
theorem exists_prefix_of_steps_le {C D : Word R}
    (arm : NegativeExtension C D) {n : ℕ} (hn : n ≤ arm.steps) :
    ∃ (E : Word R) (initial : NegativeExtension C E),
      initial.steps = n ∧
        ∃ suffix : NegativeExtension E D,
          initial.trans suffix = arm := by
  induction arm generalizing n with
  | base =>
      have hnzero : n = 0 := by simpa [steps] using hn
      subst n
      exact ⟨C, .base, rfl, .base, rfl⟩
  | @step D arm z a h ih =>
      by_cases hprefix : n ≤ arm.steps
      · rcases ih hprefix with ⟨E, initial, hsteps, suffix, hsuffix⟩
        refine ⟨E, initial, hsteps, .step suffix a h, ?_⟩
        simp only [trans]
        rw [hsuffix]
      · have hnall : n = arm.steps + 1 := by
          simp only [steps] at hn
          omega
        subst n
        exact ⟨append R D (negativeArrow a) h, .step arm a h,
          rfl, .base, rfl⟩

/-- The composite right-module inclusion along a negative extension arm. -/
def moduleMap {C D : Word R} (arm : NegativeExtension C D)
    (hmono : IsMonomial R) : C.rightModule hmono ⟶ D.rightModule hmono :=
  match arm with
  | .base => 𝟙 _
  | .step arm a h =>
      arm.moduleMap hmono ≫
        appendRightModuleInclusionNegative _ a h hmono

instance moduleMap_mono {C D : Word R} (arm : NegativeExtension C D)
    (hmono : IsMonomial R) : Mono (arm.moduleMap hmono) := by
  induction arm with
  | base =>
      change Mono (𝟙 (C.rightModule hmono))
      infer_instance
  | step arm a h ih =>
      dsimp only [moduleMap]
      letI : Mono (arm.moduleMap hmono) := ih
      infer_instance

@[simp]
theorem moduleMap_trans {C D E : Word R}
    (first : NegativeExtension C D)
    (second : NegativeExtension D E) (hmono : IsMonomial R) :
    (first.trans second).moduleMap hmono =
      first.moduleMap hmono ≫ second.moduleMap hmono := by
  induction second with
  | base => simp [trans, moduleMap]
  | step arm a h ih => simp [trans, moduleMap, ih, Category.assoc]

end NegativeExtension

/-- A finite sequence of positive letters appended to `C`. -/
inductive PositiveExtension (C : Word R) : Word R → Type u
  | base : PositiveExtension C C
  | step {D : Word R} (arm : PositiveExtension C D) {z : Q}
      (a : D.target ⟶ z)
      (h : IsString R (D.path.comp (positiveArrow a).toPath)) :
      PositiveExtension C (append R D (positiveArrow a) h)

namespace PositiveExtension

/-- A positive arm does not change the source vertex. -/
theorem source_eq {C D : Word R} (arm : PositiveExtension C D) :
    D.source = C.source := by
  induction arm with
  | base => rfl
  | step arm a h ih => exact ih

/-- The ordinary displayed-quiver path traversed by a positive arm, from the
original endpoint to its new endpoint. -/
def ordinaryPath {C D : Word R} : PositiveExtension C D →
    Quiver.Path C.target D.target
  | .base => Quiver.Path.nil
  | .step arm a _ => arm.ordinaryPath.comp a.toPath

/-- Number of letters in a positive extension arm. -/
def steps {C D : Word R} : PositiveExtension C D → ℕ
  | .base => 0
  | .step arm _ _ => arm.steps + 1

@[simp]
theorem ordinaryPath_length {C D : Word R}
    (arm : PositiveExtension C D) :
    arm.ordinaryPath.length = arm.steps := by
  induction arm with
  | base => rfl
  | step arm a h ih => simp [ordinaryPath, steps, ih, Nat.add_comm]

/-- The positive ordinary path of an arm is a suffix of the final word. -/
theorem exists_path_prefix {C D : Word R}
    (arm : PositiveExtension C D) :
    ∃ l : SignedPath D.source C.target,
      D.path = l.comp (positivePath arm.ordinaryPath) := by
  induction arm with
  | base => exact ⟨C.path, by simp [ordinaryPath]⟩
  | @step D arm z a h ih =>
      rcases ih with ⟨l, hl⟩
      refine ⟨l, ?_⟩
      change D.path.comp (positiveArrow a).toPath =
        l.comp (positivePath (arm.ordinaryPath.comp a.toPath))
      calc
        D.path.comp (positiveArrow a).toPath =
            (l.comp (positivePath arm.ordinaryPath)).comp
              (positiveArrow a).toPath := by rw [hl]
        _ = l.comp ((positivePath arm.ordinaryPath).comp
              (positiveArrow a).toPath) :=
          Quiver.Path.comp_assoc _ _ _
        _ = l.comp (positivePath (arm.ordinaryPath.comp a.toPath)) := by
          rw [positivePath_comp, positivePath_toPath (Q := Q)]

/-- The ordinary path of a positive arm occurs positively in the final word. -/
theorem positivePath_ordinaryPath_contiguous {C D : Word R}
    (arm : PositiveExtension C D) :
    IsContiguousSubpath (positivePath arm.ordinaryPath) D.path := by
  rcases arm.exists_path_prefix with ⟨l, hl⟩
  refine ⟨l, Quiver.Path.nil, ?_⟩
  simpa using hl

/-- The ordinary path underlying a positive arm survives the relation
quotient. -/
theorem pathMap_ordinaryPath_ne_zero {C D : Word R}
    (arm : PositiveExtension C D) :
    pathMap R arm.ordinaryPath ≠ 0 :=
  D.isString.2.1 arm.ordinaryPath
    arm.positivePath_ordinaryPath_contiguous

/-- Any uniform admissibility bound for killed ordinary paths strictly bounds
the number of steps in a positive arm. -/
theorem steps_lt_of_long_paths_mem {C D : Word R}
    (arm : PositiveExtension C D) {N : ℕ}
    (hlong : ∀ {x y : Q} (p : Quiver.Path x y), N ≤ p.length →
      LinearPathCategory.pathHom p ∈
        HomIdeal.generatedHomSubmodule k R
          (LinearPathCategory.obj k Q y)
          (LinearPathCategory.obj k Q x)) :
    arm.steps < N := by
  apply Nat.lt_of_not_ge
  intro hN
  apply arm.pathMap_ordinaryPath_ne_zero
  apply (pathMap_eq_zero_iff_mem_relationIdeal R arm.ordinaryPath).2
  apply hlong arm.ordinaryPath
  simpa only [ordinaryPath_length] using hN

/-- The endpoint word is longer by exactly the number of arm steps. -/
@[simp]
theorem result_length {C D : Word R} (arm : PositiveExtension C D) :
    D.length = C.length + arm.steps := by
  induction arm with
  | base => rfl
  | step arm a h ih => simp [steps, ih, Nat.add_assoc]

/-- Concatenate two positive extension arms. -/
def trans {C D E : Word R}
    (first : PositiveExtension C D)
    (second : PositiveExtension D E) : PositiveExtension C E :=
  match second with
  | .base => first
  | .step arm a h => .step (first.trans arm) a h

@[simp]
theorem steps_trans {C D E : Word R}
    (first : PositiveExtension C D)
    (second : PositiveExtension D E) :
    (first.trans second).steps = first.steps + second.steps := by
  induction second with
  | base => simp [trans, steps]
  | step arm a h ih => simp [trans, steps, ih, Nat.add_assoc]

/-- Every initial number of steps of a positive arm is represented by a
prefix arm, followed by a residual positive arm. -/
theorem exists_prefix_of_steps_le {C D : Word R}
    (arm : PositiveExtension C D) {n : ℕ} (hn : n ≤ arm.steps) :
    ∃ (E : Word R) (initial : PositiveExtension C E),
      initial.steps = n ∧
        ∃ suffix : PositiveExtension E D,
          initial.trans suffix = arm := by
  induction arm generalizing n with
  | base =>
      have hnzero : n = 0 := by simpa [steps] using hn
      subst n
      exact ⟨C, .base, rfl, .base, rfl⟩
  | @step D arm z a h ih =>
      by_cases hprefix : n ≤ arm.steps
      · rcases ih hprefix with ⟨E, initial, hsteps, suffix, hsuffix⟩
        refine ⟨E, initial, hsteps, .step suffix a h, ?_⟩
        simp only [trans]
        rw [hsuffix]
      · have hnall : n = arm.steps + 1 := by
          simp only [steps] at hn
          omega
        subst n
        exact ⟨append R D (positiveArrow a) h, .step arm a h,
          rfl, .base, rfl⟩

/-- The composite right-module projection along a positive extension arm. -/
def moduleMap {C D : Word R} (arm : PositiveExtension C D)
    (hmono : IsMonomial R) : D.rightModule hmono ⟶ C.rightModule hmono :=
  match arm with
  | .base => 𝟙 _
  | .step arm a h =>
      appendRightModuleProjectionPositive _ a h hmono ≫
        arm.moduleMap hmono

instance moduleMap_epi {C D : Word R} (arm : PositiveExtension C D)
    (hmono : IsMonomial R) : Epi (arm.moduleMap hmono) := by
  induction arm with
  | base =>
      change Epi (𝟙 (C.rightModule hmono))
      infer_instance
  | step arm a h ih =>
      dsimp only [moduleMap]
      letI : Epi (arm.moduleMap hmono) := ih
      infer_instance

@[simp]
theorem moduleMap_trans {C D E : Word R}
    (first : PositiveExtension C D)
    (second : PositiveExtension D E) (hmono : IsMonomial R) :
    (first.trans second).moduleMap hmono =
      second.moduleMap hmono ≫ first.moduleMap hmono := by
  induction second with
  | base => simp [trans, moduleMap]
  | step arm a h ih => simp [trans, moduleMap, ih, Category.assoc]

end PositiveExtension

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
