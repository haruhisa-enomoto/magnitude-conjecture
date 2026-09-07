import MagnitudeConjecture.Algebra.StringRepresentation
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# One-letter extensions of string words

Appending one signed arrow adds exactly one endpoint occurrence to the word.
This file constructs the embedding of all old prefix positions into the
extended word and the induced linear inclusion and projection on vertex
spaces.  These are the coordinate maps underlying the canonical hook and
cohook morphisms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- Every old prefix position remains a prefix position after one letter is
appended. -/
def appendPosition (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (i : C.PositionAt x) :
    (append R C e h).PositionAt x := by
  refine ⟨i.1, ?_⟩
  rcases i.2 with ⟨q, hq⟩
  refine ⟨q.comp e.toPath, ?_⟩
  change C.path.comp e.toPath = i.1.comp (q.comp e.toPath)
  calc
    C.path.comp e.toPath = (i.1.comp q).comp e.toPath :=
      congrArg (fun p ↦ p.comp e.toPath) hq
    _ = i.1.comp (q.comp e.toPath) :=
      Quiver.Path.comp_assoc _ _ _

@[simp]
theorem appendPosition_val (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (i : C.PositionAt x) :
    (appendPosition C e h i).1 = i.1 := rfl

@[simp]
theorem appendPosition_index (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (i : C.PositionAt x) :
    (appendPosition C e h i).index = i.index := rfl

/-- Appending positions is injective. -/
theorem appendPosition_injective (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    Function.Injective (appendPosition C e h :
      C.PositionAt x → (append R C e h).PositionAt x) := by
  intro i j hij
  apply Subtype.ext
  exact congrArg (fun t ↦ t.1) hij

/-- Every arrow step between old positions remains an arrow step after
appending a letter. -/
theorem arrowStep_appendPosition (C : Word R) {z x y : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (a : x ⟶ y) (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    (append R C e h).ArrowStep a
      (appendPosition C e h i) (appendPosition C e h j) := by
  exact hij

/-- Path reachability between old positions is preserved by appending a
letter. -/
theorem pathReach_appendPosition (C : Word R) {z x y : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (p : Quiver.Path x y) (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.PathReach p i j) :
    (append R C e h).PathReach p
      (appendPosition C e h i) (appendPosition C e h j) := by
  induction p with
  | nil =>
      subst j
      rfl
  | cons p a ih =>
      rcases hij with ⟨m, him, hmj⟩
      exact ⟨appendPosition C e h m, ih m him,
        arrowStep_appendPosition C e h a m j hmj⟩

/-- The new final occurrence of the appended word. -/
def appendEndPosition (C : Word R) {z : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (append R C e h).PositionAt z :=
  ⟨(append R C e h).path, ⟨Quiver.Path.nil, by simp⟩⟩

@[simp]
theorem appendEndPosition_val (C : Word R) {z : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (appendEndPosition C e h).1 = (append R C e h).path := rfl

@[simp]
theorem appendEndPosition_index (C : Word R) {z : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (appendEndPosition C e h).index = C.length + 1 := by
  change (C.path.comp e.toPath).length = C.length + 1
  simp [Word.length]

/-- A position in the appended word whose index has not passed the old final
index comes from a unique old position. -/
theorem exists_eq_appendPosition_of_index_le (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (j : (append R C e h).PositionAt x)
    (hj : j.index ≤ C.length) :
    ∃ i : C.PositionAt x, appendPosition C e h i = j := by
  rcases j.2 with ⟨q, hq⟩
  change C.path.comp e.toPath = j.1.comp q at hq
  have hjLength : j.1.length ≤ C.path.length := by
    exact hj
  obtain ⟨v, p, r, hpr, hpLength⟩ :=
    C.path.exists_eq_comp_of_le_length hjLength
  have hcomp :
      p.comp (r.comp e.toPath) = j.1.comp q := by
    calc
      p.comp (r.comp e.toPath) = (p.comp r).comp e.toPath :=
        (Quiver.Path.comp_assoc _ _ _).symm
      _ = C.path.comp e.toPath :=
        congrArg (fun s ↦ s.comp e.toPath) hpr.symm
      _ = j.1.comp q := hq
  have hpjLength : p.length = j.1.length := hpLength
  have hvx := midpoint_eq_of_comp_eq_of_left_length_eq hcomp hpjLength
  have hvxQ : v = x := hvx
  subst v
  have hpj : p = j.1 := ((Quiver.Path.comp_inj' hpjLength).1 hcomp).1
  let i : C.PositionAt x := ⟨p, ⟨r, hpr⟩⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hpj

/-- The final endpoint is the only position created by appending one
letter. -/
theorem eq_appendEndPosition_of_not_exists_old (C : Word R) {z : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (j : (append R C e h).PositionAt z)
    (hj : ¬ ∃ i : C.PositionAt z, appendPosition C e h i = j) :
    j = appendEndPosition C e h := by
  have hjNotLe : ¬ j.index ≤ C.length := by
    intro hjLe
    exact hj (exists_eq_appendPosition_of_index_le C e h j hjLe)
  have hjFinal : j.index = C.length + 1 := by
    have hjUpper : j.index ≤ C.length + 1 := by
      simpa only [append_length] using j.index_le
    omega
  apply PositionAt.ext_index
  rw [hjFinal, appendEndPosition_index]

/-- The new endpoint is not the image of an old position. -/
theorem not_exists_appendPosition_eq_appendEndPosition
    (C : Word R) {z : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    ¬ ∃ i : C.PositionAt z,
      appendPosition C e h i = appendEndPosition C e h := by
  rintro ⟨i, hi⟩
  have hindex := congrArg PositionAt.index hi
  rw [appendPosition_index, appendEndPosition_index] at hindex
  exact (Nat.ne_of_lt (Nat.lt_succ_of_le i.index_le)) hindex

/-- Appending a negative letter creates no new arrow output from an old
position.  The new endpoint is a source for the underlying displayed arrow,
not a target of an old basis vector. -/
theorem exists_old_of_arrowStep_appendPosition_negative
    (C : Word R) {z x y : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (b : x ⟶ y) (i : C.PositionAt x)
    (l : (append R C (negativeArrow a) h).PositionAt y)
    (hil : (append R C (negativeArrow a) h).ArrowStep b
      (appendPosition C (negativeArrow a) h i) l) :
    ∃ j : C.PositionAt y,
      appendPosition C (negativeArrow a) h j = l := by
  rcases hil with hpositive | hnegative
  · by_cases hi : i.index < C.length
    · apply exists_eq_appendPosition_of_index_le C (negativeArrow a) h l
      have hindex : l.index = i.index + 1 := by
        change l.1.length = i.1.length + 1
        calc
          l.1.length =
              (appendPosition C (negativeArrow a) h i).1.length + 1 := by
            rw [hpositive, Quiver.Path.length_comp,
              Quiver.Path.length_toPath]
          _ = i.1.length + 1 := by
            rw [appendPosition_val]
            rfl
      omega
    · have hiFinal : i.index = C.length := by
        exact Nat.le_antisymm i.index_le (Nat.le_of_not_gt hi)
      have hx := i.eq_target_of_index_eq_length hiFinal
      have hxQ : x = C.target := hx
      subst x
      let iEnd : C.PositionAt C.target :=
        ⟨C.path, ⟨Quiver.Path.nil, by simp⟩⟩
      have hiEnd : i = iEnd := by
        apply PositionAt.ext_index
        exact hiFinal
      have hlIndex : l.index = i.index + 1 := by
        change l.1.length = i.1.length + 1
        calc
          l.1.length =
              (appendPosition C (negativeArrow a) h i).1.length + 1 := by
            rw [hpositive, Quiver.Path.length_comp,
              Quiver.Path.length_toPath]
          _ = i.1.length + 1 := by
            rw [appendPosition_val]
            rfl
      have hlFinal :
          l.index = (append R C (negativeArrow a) h).length := by
        calc
          l.index = i.index + 1 := hlIndex
          _ = C.length + 1 := congrArg (fun n ↦ n + 1) hiFinal
          _ = (append R C (negativeArrow a) h).length :=
            (append_length R C (negativeArrow a) h).symm
      have hy := l.eq_target_of_index_eq_length hlFinal
      have hyQ : y = z := hy
      subst y
      let lEnd :
          (append R C (negativeArrow a) h).PositionAt
            (append R C (negativeArrow a) h).target :=
        ⟨(append R C (negativeArrow a) h).path,
          ⟨Quiver.Path.nil, by simp⟩⟩
      have hlEnd : l = lEnd := by
        apply PositionAt.ext_index
        exact hlFinal
      rw [hiEnd, hlEnd] at hpositive
      have hpaths :
          C.path.comp (negativeArrow a).toPath =
            C.path.comp (positiveArrow b).toPath := hpositive
      have hsuffix := Quiver.Path.comp_injective_right C.path hpaths
      have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
      exact False.elim
        (positiveArrow_ne_negativeArrow b a (eq_of_heq harrows.symm))
  · apply exists_eq_appendPosition_of_index_le C (negativeArrow a) h l
    have hindex : i.index = l.index + 1 := by
      change i.1.length = l.1.length + 1
      calc
        i.1.length =
            (appendPosition C (negativeArrow a) h i).1.length := by
          rw [appendPosition_val]
          rfl
        _ = l.1.length + 1 := by
          rw [hnegative, Quiver.Path.length_comp,
            Quiver.Path.length_toPath]
    exact (Nat.le_trans (Nat.le_of_lt (by omega)) i.index_le)

/-- After appending a positive letter, the new endpoint has no outgoing
displayed-arrow step. -/
theorem not_exists_arrowStep_appendEndPosition_positive
    (C : Word R) {z y : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (b : z ⟶ y) :
    ¬ ∃ l : (append R C (positiveArrow a) h).PositionAt y,
      (append R C (positiveArrow a) h).ArrowStep b
        (appendEndPosition C (positiveArrow a) h) l := by
  rintro ⟨l, hl⟩
  rcases hl with hpositive | hnegative
  · have hlIndex : l.index = C.length + 2 := by
      change l.1.length = C.length + 2
      calc
        l.1.length =
            (appendEndPosition C (positiveArrow a) h).1.length + 1 := by
          rw [hpositive, Quiver.Path.length_comp,
            Quiver.Path.length_toPath]
        _ = (C.length + 1) + 1 := by
          rw [show (appendEndPosition C (positiveArrow a) h).1.length =
              (appendEndPosition C (positiveArrow a) h).index from rfl,
            appendEndPosition_index]
    have hlUpper : l.index ≤ C.length + 1 := by
      simpa only [append_length] using l.index_le
    omega
  · have hlIndex : l.index = C.length := by
      have hindex : C.length + 1 = l.index + 1 := by
        change C.length + 1 = l.1.length + 1
        calc
          C.length + 1 =
              (appendEndPosition C (positiveArrow a) h).1.length := by
            rw [show (appendEndPosition C (positiveArrow a) h).1.length =
                (appendEndPosition C (positiveArrow a) h).index from rfl,
              appendEndPosition_index]
          _ = l.1.length + 1 := by
            rw [hnegative, Quiver.Path.length_comp,
              Quiver.Path.length_toPath]
      omega
    rcases exists_eq_appendPosition_of_index_le
      C (positiveArrow a) h l (by omega) with ⟨j, rfl⟩
    have hjFinal : j.index = C.length := hlIndex
    have hy := j.eq_target_of_index_eq_length hjFinal
    have hyQ : y = C.target := hy
    subst y
    let jEnd : C.PositionAt C.target :=
      ⟨C.path, ⟨Quiver.Path.nil, by simp⟩⟩
    have hjEnd : j = jEnd := by
      apply PositionAt.ext_index
      exact hjFinal
    rw [hjEnd] at hnegative
    have hpaths :
        C.path.comp (positiveArrow a).toPath =
          C.path.comp (negativeArrow b).toPath := hnegative
    have hsuffix := Quiver.Path.comp_injective_right C.path hpaths
    have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
    exact positiveArrow_ne_negativeArrow a b (eq_of_heq harrows)

/-- The old-position inclusion on a vertex space. -/
def appendSpaceInclusion (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    C.Space x →ₗ[k] (append R C e h).Space x :=
  Finsupp.lmapDomain k k (appendPosition C e h)

@[simp]
theorem appendSpaceInclusion_single (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (i : C.PositionAt x) (c : k) :
    appendSpaceInclusion C e h (Finsupp.single i c) =
      Finsupp.single (appendPosition C e h i) c :=
  Finsupp.mapDomain_single

/-- The coordinate projection from an appended vertex space onto its old
positions.  The unique new endpoint basis vector is sent to zero. -/
def appendSpaceProjection (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    (append R C e h).Space x →ₗ[k] C.Space x :=
  Finsupp.linearCombination k fun j ↦ by
    classical
    exact if hex : ∃ i : C.PositionAt x, appendPosition C e h i = j then
        Finsupp.single (Classical.choose hex) 1
      else
        0

/-- Projection kills a basis position which is not inherited from the old
word. -/
theorem appendSpaceProjection_single_of_not_exists_old
    (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (j : (append R C e h).PositionAt x) (c : k)
    (hj : ¬ ∃ i : C.PositionAt x, appendPosition C e h i = j) :
    appendSpaceProjection C e h (Finsupp.single j c) = 0 := by
  rw [appendSpaceProjection, Finsupp.linearCombination_single, dif_neg hj,
    smul_zero]

/-- In particular, projection kills the newly appended endpoint. -/
@[simp]
theorem appendSpaceProjection_single_appendEndPosition
    (C : Word R) {z : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) (c : k) :
    appendSpaceProjection C e h
        (Finsupp.single (appendEndPosition C e h) c) = 0 := by
  apply appendSpaceProjection_single_of_not_exists_old
  exact not_exists_appendPosition_eq_appendEndPosition C e h

/-- Projection after inclusion is the identity on every old basis vector. -/
@[simp]
theorem appendSpaceProjection_single_appendPosition
    (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (i : C.PositionAt x) (c : k) :
    appendSpaceProjection C e h
        (Finsupp.single (appendPosition C e h i) c) =
      Finsupp.single i c := by
  classical
  rw [appendSpaceProjection, Finsupp.linearCombination_single]
  let hex : ∃ j : C.PositionAt x,
      appendPosition C e h j = appendPosition C e h i := ⟨i, rfl⟩
  rw [dif_pos hex]
  have hchosen : Classical.choose hex = i := by
    apply appendPosition_injective C e h
    exact Classical.choose_spec hex
  rw [hchosen]
  exact Finsupp.smul_single_one i c

/-- Projection is a left inverse to the old-position inclusion. -/
theorem appendSpaceProjection_inclusion (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath))
    (v : C.Space x) :
    appendSpaceProjection C e h (appendSpaceInclusion C e h v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      rw [appendSpaceInclusion_single,
        appendSpaceProjection_single_appendPosition]

/-- The old-position inclusion is injective. -/
theorem appendSpaceInclusion_injective (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    Function.Injective (appendSpaceInclusion C e h :
      C.Space x → (append R C e h).Space x) :=
  Function.LeftInverse.injective
    (fun v ↦ appendSpaceProjection_inclusion C e h v)

/-- The old-coordinate projection is surjective. -/
theorem appendSpaceProjection_surjective (C : Word R) {z x : Q}
    (e : SignedArrow C.target z)
    (h : IsString R (C.path.comp e.toPath)) :
    Function.Surjective (appendSpaceProjection C e h :
      (append R C e h).Space x → C.Space x) :=
  Function.LeftInverse.surjective
    (fun v ↦ appendSpaceProjection_inclusion C e h v)

/-- For a positive appended letter, projection commutes with displayed-arrow
action on every inherited basis vector.  A possible new target is precisely
the appended endpoint and is therefore killed by projection. -/
theorem appendSpaceProjection_arrowLinearMap_positive_appendPosition
    (C : Word R) {z x y : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (b : x ⟶ y) (i : C.PositionAt x) :
    appendSpaceProjection C (positiveArrow a) h
        ((append R C (positiveArrow a) h).arrowLinearMap b
          (Finsupp.single
            (appendPosition C (positiveArrow a) h i) 1)) =
      C.arrowLinearMap b
        (appendSpaceProjection C (positiveArrow a) h
          (Finsupp.single
            (appendPosition C (positiveArrow a) h i) 1)) := by
  classical
  rw [appendSpaceProjection_single_appendPosition]
  by_cases hex : ∃ j : C.PositionAt y, C.ArrowStep b i j
  · let j := Classical.choose hex
    have hij : C.ArrowStep b i j := Classical.choose_spec hex
    rw [(append R C (positiveArrow a) h).arrowLinearMap_single_one_of_step
        b (appendPosition C (positiveArrow a) h i)
        (appendPosition C (positiveArrow a) h j)
        (arrowStep_appendPosition C (positiveArrow a) h b i j hij),
      appendSpaceProjection_single_appendPosition,
      C.arrowLinearMap_single_one_of_step b i j hij]
  · rw [C.arrowLinearMap_single, one_smul,
      C.arrowOnBasis_eq_zero_of_not_exists b i hex]
    rw [(append R C (positiveArrow a) h).arrowLinearMap_single, one_smul]
    by_cases hext :
        ∃ l : (append R C (positiveArrow a) h).PositionAt y,
          (append R C (positiveArrow a) h).ArrowStep b
            (appendPosition C (positiveArrow a) h i) l
    · let l := Classical.choose hext
      have hil := Classical.choose_spec hext
      rw [(append R C (positiveArrow a) h).arrowOnBasis_eq_single_of_step
        b (appendPosition C (positiveArrow a) h i) l hil]
      apply appendSpaceProjection_single_of_not_exists_old
      rintro ⟨j, hj⟩
      change (append R C (positiveArrow a) h).ArrowStep b
        (appendPosition C (positiveArrow a) h i) l at hil
      rw [← hj] at hil
      apply hex
      refine ⟨j, ?_⟩
      exact hil
    · rw [(append R C (positiveArrow a) h).arrowOnBasis_eq_zero_of_not_exists
        b (appendPosition C (positiveArrow a) h i) hext, map_zero]

/-- For a positive appended letter, projection commutes with displayed-arrow
action on every basis vector. -/
theorem appendSpaceProjection_arrowLinearMap_positive_single
    (C : Word R) {z x y : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (b : x ⟶ y)
    (j : (append R C (positiveArrow a) h).PositionAt x) :
    appendSpaceProjection C (positiveArrow a) h
        ((append R C (positiveArrow a) h).arrowLinearMap b
          (Finsupp.single j 1)) =
      C.arrowLinearMap b
        (appendSpaceProjection C (positiveArrow a) h
          (Finsupp.single j 1)) := by
  classical
  by_cases hjOld : ∃ i : C.PositionAt x,
      appendPosition C (positiveArrow a) h i = j
  · rcases hjOld with ⟨i, rfl⟩
    exact appendSpaceProjection_arrowLinearMap_positive_appendPosition
      C a h b i
  · have hjNotLe : ¬ j.index ≤ C.length := by
      intro hjLe
      exact hjOld
        (exists_eq_appendPosition_of_index_le
          C (positiveArrow a) h j hjLe)
    have hjFinal :
        j.index = (append R C (positiveArrow a) h).length := by
      have hjUpper : j.index ≤ C.length + 1 := by
        simpa only [append_length] using j.index_le
      rw [append_length]
      omega
    have hx := j.eq_target_of_index_eq_length hjFinal
    have hxQ : x = z := hx
    clear hx
    subst x
    have hjEnd : j = appendEndPosition C (positiveArrow a) h :=
      eq_appendEndPosition_of_not_exists_old
        C (positiveArrow a) h j hjOld
    rw [hjEnd, (append R C (positiveArrow a) h).arrowLinearMap_single,
      one_smul,
      (append R C (positiveArrow a) h).arrowOnBasis_eq_zero_of_not_exists
        b (appendEndPosition C (positiveArrow a) h)
        (not_exists_arrowStep_appendEndPosition_positive C a h b),
      map_zero, appendSpaceProjection_single_appendEndPosition, map_zero]

/-- Appending a positive letter makes the old coordinate projection a
morphism of quiver representations. -/
theorem appendSpaceProjection_arrowLinearMap_positive
    (C : Word R) {z x y : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath))
    (b : x ⟶ y)
    (v : (append R C (positiveArrow a) h).Space x) :
    appendSpaceProjection C (positiveArrow a) h
        ((append R C (positiveArrow a) h).arrowLinearMap b v) =
      C.arrowLinearMap b
        (appendSpaceProjection C (positiveArrow a) h v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single j c =>
      rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul,
        appendSpaceProjection_arrowLinearMap_positive_single]

/-- For a negative appended letter, the old-position inclusion commutes with
every displayed-arrow action on a basis vector. -/
theorem appendSpaceInclusion_arrowLinearMap_negative_single
    (C : Word R) {z x y : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (b : x ⟶ y) (i : C.PositionAt x) :
    appendSpaceInclusion C (negativeArrow a) h
        (C.arrowLinearMap b (Finsupp.single i 1)) =
      (append R C (negativeArrow a) h).arrowLinearMap b
        (appendSpaceInclusion C (negativeArrow a) h
          (Finsupp.single i 1)) := by
  classical
  by_cases hex : ∃ j : C.PositionAt y, C.ArrowStep b i j
  · let j := Classical.choose hex
    have hij : C.ArrowStep b i j := Classical.choose_spec hex
    rw [C.arrowLinearMap_single_one_of_step b i j hij,
      appendSpaceInclusion_single, appendSpaceInclusion_single]
    symm
    apply (append R C (negativeArrow a) h).arrowLinearMap_single_one_of_step
    exact arrowStep_appendPosition C (negativeArrow a) h b i j hij
  · rw [arrowLinearMap_single, one_smul,
      C.arrowOnBasis_eq_zero_of_not_exists b i hex, map_zero,
      appendSpaceInclusion_single, arrowLinearMap_single, one_smul]
    symm
    apply (append R C (negativeArrow a) h).arrowOnBasis_eq_zero_of_not_exists
    rintro ⟨l, hil⟩
    rcases exists_old_of_arrowStep_appendPosition_negative
      C a h b i l hil with ⟨j, rfl⟩
    apply hex
    refine ⟨j, ?_⟩
    exact hil

/-- Appending a negative letter makes the old coordinate spaces a
subrepresentation. -/
theorem appendSpaceInclusion_arrowLinearMap_negative
    (C : Word R) {z x y : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath))
    (b : x ⟶ y) (v : C.Space x) :
    appendSpaceInclusion C (negativeArrow a) h (C.arrowLinearMap b v) =
      (append R C (negativeArrow a) h).arrowLinearMap b
        (appendSpaceInclusion C (negativeArrow a) h v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul,
        appendSpaceInclusion_arrowLinearMap_negative_single]

/-- The canonical inclusion associated to a negative one-letter extension,
packaged as a morphism of quiver representations. -/
def appendQuiverRepresentationInclusionNegative
    (C : Word R) {z : Q} (a : z ⟶ C.target)
    (h : IsString R (C.path.comp (negativeArrow a).toPath)) :
    C.quiverRepresentation ⟶
      (append R C (negativeArrow a) h).quiverRepresentation :=
  Paths.liftNatTrans
    (fun x ↦ ModuleCat.ofHom
      (appendSpaceInclusion C (negativeArrow a) h (x := x)))
    (fun {x y} b ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change appendSpaceInclusion C (negativeArrow a) h
          (C.arrowLinearMap b v) =
        (append R C (negativeArrow a) h).arrowLinearMap b
          (appendSpaceInclusion C (negativeArrow a) h v)
      exact appendSpaceInclusion_arrowLinearMap_negative C a h b v)

/-- The canonical projection associated to a positive one-letter extension,
packaged as a morphism of quiver representations. -/
def appendQuiverRepresentationProjectionPositive
    (C : Word R) {z : Q} (a : C.target ⟶ z)
    (h : IsString R (C.path.comp (positiveArrow a).toPath)) :
    (append R C (positiveArrow a) h).quiverRepresentation ⟶
      C.quiverRepresentation :=
  Paths.liftNatTrans
    (fun x ↦ ModuleCat.ofHom
      (appendSpaceProjection C (positiveArrow a) h (x := x)))
    (fun {x y} b ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change appendSpaceProjection C (positiveArrow a) h
          ((append R C (positiveArrow a) h).arrowLinearMap b v) =
        C.arrowLinearMap b
          (appendSpaceProjection C (positiveArrow a) h v)
      exact appendSpaceProjection_arrowLinearMap_positive C a h b v)

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
