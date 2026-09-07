import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckShift
import MagnitudeConjecture.CategoryTheory.ObjectDeletionComparison
import MagnitudeConjecture.CategoryTheory.CoherentDeckShiftRestriction
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Successive subgroup-orbit deletion stages

For representatives `g₀, ..., gₘ₋₁`, the covering proof deletes the subgroup
orbits `Γ gᵢ x` one at a time.  This file defines the accumulated object set
before and after each deletion, proves its `Γ`-invariance, and identifies a
successor stage with adjoining exactly the next orbit.
-/

set_option autoImplicit false

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

universe u v w z

variable {C : Type u}
variable {G : Type w} [Group G] [MulAction G C]

/-- The literal `N`-orbit of an ambient object. -/
def subgroupOrbit (N : Subgroup G) (X : C) : Set C :=
  {Y | ∃ n : N, (n : G) • X = Y}

@[simp]
theorem mem_subgroupOrbit_iff (N : Subgroup G) (X Y : C) :
    Y ∈ subgroupOrbit N X ↔ ∃ n : N, (n : G) • X = Y :=
  Iff.rfl

/-- A subgroup orbit is invariant under the subgroup action. -/
theorem subgroupOrbit_actionInvariant (N : Subgroup G) (X : C) :
    ActionInvariant (G := N) (subgroupOrbit N X) := by
  intro n Y
  change (n : G) • Y ∈ subgroupOrbit N X ↔ Y ∈ subgroupOrbit N X
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨n⁻¹ * g, ?_⟩
    calc
      (((n⁻¹ * g : N) : G) • X) = ((n⁻¹ : N) : G) • ((g : G) • X) := by
        simp only [Subgroup.coe_mul, mul_smul]
      _ = ((n⁻¹ : N) : G) • ((n : G) • Y) := by rw [hg]
      _ = Y := by simp
  · rintro ⟨g, rfl⟩
    refine ⟨n * g, ?_⟩
    simp only [Subgroup.coe_mul, mul_smul]

/-- The objects deleted after the first `j` representatives.  There are `m`
deletions and hence `m + 1` stages, including the empty initial stage. -/
def stageDeletedSet {m : ℕ} (N : Subgroup G) (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) : Set C :=
  {Y | ∃ i : Fin m, i.val < j.val ∧
    Y ∈ subgroupOrbit N (representative i • x)}

@[simp]
theorem stageDeletedSet_zero {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) :
    stageDeletedSet N representative x 0 = ∅ := by
  ext Y
  simp [stageDeletedSet]

/-- Every accumulated stage is invariant under `N`. -/
theorem stageDeletedSet_actionInvariant {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    ActionInvariant (G := N) (stageDeletedSet N representative x j) := by
  intro n Y
  constructor
  · rintro ⟨i, hi, hY⟩
    exact ⟨i, hi, (subgroupOrbit_actionInvariant N
      (representative i • x) n Y).1 hY⟩
  · rintro ⟨i, hi, hY⟩
    exact ⟨i, hi, (subgroupOrbit_actionInvariant N
      (representative i • x) n Y).2 hY⟩

/-- Passing from stage `i` to stage `i + 1` adjoins exactly the orbit
`N · (gᵢ · x)`. -/
theorem stageDeletedSet_succ {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (i : Fin m) :
    stageDeletedSet N representative x i.succ =
      stageDeletedSet N representative x i.castSucc ∪
        subgroupOrbit N (representative i • x) := by
  ext Y
  constructor
  · rintro ⟨r, hr, hY⟩
    by_cases hri : r.val < i.val
    · exact Or.inl ⟨r, hri, hY⟩
    · right
      have hEq : r = i := by
        apply Fin.ext
        change r.val < i.val + 1 at hr
        omega
      simpa [hEq] using hY
  · rintro (hY | hY)
    · rcases hY with ⟨r, hr, hY⟩
      refine ⟨r, ?_, hY⟩
      change r.val < i.val at hr
      change r.val < i.val + 1
      omega
    · exact ⟨i, by simp, hY⟩

/-- The terminal stage is the union of all displayed subgroup orbits. -/
theorem mem_stageDeletedSet_last_iff {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x Y : C) :
    Y ∈ stageDeletedSet N representative x (Fin.last m) ↔
      ∃ i : Fin m, Y ∈ subgroupOrbit N (representative i • x) := by
  constructor
  · rintro ⟨i, _, hY⟩
    exact ⟨i, hY⟩
  · rintro ⟨i, hY⟩
    exact ⟨i, by simp, hY⟩

section Categories

variable {k : Type z} [Ring k]
variable [Category.{v} C] [Preadditive C] [Linear k C]

/-- The manuscript's intermediate category after the first `j` subgroup
orbits have been deleted. -/
abbrev StageCategory {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :=
  DeletionCategory (k := k) C (stageDeletedSet N representative x j)

/-- The objects of the next subgroup orbit, viewed inside the current stage. -/
abbrev StageAdditionalDeleted {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (i : Fin m) :=
  AdditionalDeleted (k := k) C
    (stageDeletedSet N representative x i.castSucc)
    (subgroupOrbit N (representative i • x))

/-- Deleting the next subgroup orbit from the current stage is canonically
equivalent to the next accumulated stage. -/
noncomputable def stageSuccEquivalence {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (i : Fin m) :
    IteratedDeletionCategory (k := k) C
        (stageDeletedSet N representative x i.castSucc)
        (subgroupOrbit N (representative i • x)) ≌
      StageCategory (k := k) N representative x i.succ := by
  exact (iteratedDeletionEquivalence (k := k) C
      (stageDeletedSet N representative x i.castSucc)
      (subgroupOrbit N (representative i • x))).trans
    (deletionEquivalenceOfEq (k := k) C
      (stageDeletedSet_succ N representative x i).symm)

noncomputable instance stageSuccEquivalence_functor_additive {m : ℕ}
    (N : Subgroup G) (representative : Fin m → G) (x : C) (i : Fin m) :
    (stageSuccEquivalence (k := k) N representative x i).functor.Additive := by
  let e₁ := iteratedDeletionEquivalence (k := k) C
    (stageDeletedSet N representative x i.castSucc)
    (subgroupOrbit N (representative i • x))
  let e₂ := deletionEquivalenceOfEq (k := k) C
    (stageDeletedSet_succ N representative x i).symm
  letI : e₁.functor.Additive := inferInstance
  letI : e₂.functor.Additive := inferInstance
  change (e₁.functor ⋙ e₂.functor).Additive
  infer_instance

noncomputable instance stageSuccEquivalence_functor_linear {m : ℕ}
    (N : Subgroup G) (representative : Fin m → G) (x : C) (i : Fin m) :
    (stageSuccEquivalence (k := k) N representative x i).functor.Linear k := by
  let e₁ := iteratedDeletionEquivalence (k := k) C
    (stageDeletedSet N representative x i.castSucc)
    (subgroupOrbit N (representative i • x))
  let e₂ := deletionEquivalenceOfEq (k := k) C
    (stageDeletedSet_succ N representative x i).symm
  letI : e₁.functor.Linear k := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  change (e₁.functor ⋙ e₂.functor).Linear k
  infer_instance

/-- The canonical successor-stage equivalence is literally bijective on
objects. -/
theorem stageSuccEquivalence_functor_obj_bijective {m : ℕ}
    (N : Subgroup G) (representative : Fin m → G) (x : C) (i : Fin m) :
    Function.Bijective
      (stageSuccEquivalence (k := k) N representative x i).functor.obj := by
  let hIter := iteratedDeletionEquivalence_functor_obj_bijective
    (k := k) C
    (stageDeletedSet N representative x i.castSucc)
    (subgroupOrbit N (representative i • x))
  let hEq := deletionEquivalenceOfEq_functor_obj_bijective
    (k := k) C (stageDeletedSet_succ N representative x i).symm
  exact hEq.comp hIter

end Categories

section DeckShift

open MagnitudeConjecture.CoveringHom

variable {k : Type z} [CommRing k]
variable [Category.{v} C] [Preadditive C] [Linear k C]

/-- The literal `N`-action on an intermediate deletion stage. -/
@[implicit_reducible]
def stageMulAction {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    MulAction N (StageCategory (k := k) N representative x j) :=
  deletionMulAction (k := k) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)

/-- Freeness of the literal subgroup action survives at every intermediate
deletion stage. -/
theorem stageIsCancelSMul {m : ℕ} (N : Subgroup G)
    [IsCancelSMul N C] (representative : Fin m → G) (x : C)
    (j : Fin (m + 1)) :
    letI := stageMulAction (k := k) N representative x j
    IsCancelSMul N (StageCategory (k := k) N representative x j) := by
  letI := stageMulAction (k := k) N representative x j
  exact deletionIsCancelSMul (k := k)
    (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)

/-- Every intermediate stage retains the coherent deck shift of the subgroup
whose orbits are being deleted.  No action by the full ambient group is
asserted at an intermediate stage. -/
noncomputable def stageCoherentDeckShift
    (D : CoveringHom.CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    letI := stageMulAction (k := k) N representative x j
    CoveringHom.CoherentDeckShift
      (StageCategory (k := k) N representative x j) N := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  exact CoherentDeckShift.deletionCoherentDeckShift (k := k)
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)

noncomputable instance stageCoherentDeckShift_core_additive
    (D : CoveringHom.CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1))
    (a : Additive N) :
    letI := stageMulAction (k := k) N representative x j
    ((stageCoherentDeckShift (k := k) D hC N representative x j).core.F a).Additive := by
  letI := stageMulAction (k := k) N representative x j
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  change ((CoherentDeckShift.deletionCoherentDeckShift (k := k)
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)).core.F a).Additive
  infer_instance

noncomputable instance stageCoherentDeckShift_core_linear
    (D : CoveringHom.CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1))
    (a : Additive N) :
    letI := stageMulAction (k := k) N representative x j
    ((stageCoherentDeckShift (k := k) D hC N representative x j).core.F a).Linear k := by
  letI := stageMulAction (k := k) N representative x j
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  change ((CoherentDeckShift.deletionCoherentDeckShift (k := k)
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)).core.F a).Linear k
  infer_instance

end DeckShift

end MagnitudeConjecture.ObjectDeletion
