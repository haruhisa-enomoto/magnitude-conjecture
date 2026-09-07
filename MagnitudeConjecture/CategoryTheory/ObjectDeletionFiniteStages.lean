import MagnitudeConjecture.CategoryTheory.ObjectDeletionStage
import MagnitudeConjecture.CategoryTheory.ShiftOrbitResidualTranslate
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

/-!
# Finite quotient representatives and deletion-stage endpoints

For a finite quotient `G / N`, this file chooses one representative of every
coset, with the identity representative first.  The associated finite
deletion chain starts at the ambient category and ends after deleting the
entire `G`-orbit of the chosen object.  These are the literal endpoints of the
manuscript's covering telescope.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

universe u v w z

variable {C : Type u}
variable {G : Type w} [Group G] [MulAction G C]

/-- An ordering of all cosets of a finite quotient, with the identity coset
in the first position. -/
structure FiniteQuotientRepresentatives (N : Subgroup G) [N.Normal] where
  m : ℕ
  positive : 0 < m
  quotientEquiv : Fin m ≃ G ⧸ N
  first_eq_one : quotientEquiv ⟨0, positive⟩ = 1

namespace FiniteQuotientRepresentatives

variable {N : Subgroup G} [N.Normal]

/-- The first index of an ordered quotient representative family. -/
def firstIndex (R : FiniteQuotientRepresentatives N) : Fin R.m :=
  ⟨0, R.positive⟩

instance (R : FiniteQuotientRepresentatives N) : NeZero R.m :=
  ⟨Nat.ne_of_gt R.positive⟩

/-- Every nonempty finite quotient admits an enumeration beginning at the
identity coset. -/
def canonical [Fintype (G ⧸ N)] : FiniteQuotientRepresentatives N := by
  let Q := G ⧸ N
  have hpositive : 0 < Fintype.card Q := Fintype.card_pos
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  let first : Fin (Fintype.card Q) := ⟨0, hpositive⟩
  let identityIndex : Fin (Fintype.card Q) := e.symm 1
  let ordered := (Equiv.swap first identityIndex).trans e
  refine
    { m := Fintype.card Q
      positive := hpositive
      quotientEquiv := ordered
      first_eq_one := ?_ }
  simp [ordered, first, identityIndex]

/-- The number of chosen representatives is the quotient-group order. -/
theorem m_eq_card [Fintype (G ⧸ N)]
    (R : FiniteQuotientRepresentatives N) :
    R.m = Fintype.card (G ⧸ N) := by
  simpa using Fintype.card_congr R.quotientEquiv

/-- A literal ambient representative of the coset at index `i`.  The
identity coset is represented by the literal group identity. -/
def representative (R : FiniteQuotientRepresentatives N) (i : Fin R.m) : G :=
  by
    classical
    exact if R.quotientEquiv i = 1 then 1
      else MagnitudeConjecture.CoveringHom.CoherentDeckShift.normalQuotientRepresentative
        N (R.quotientEquiv i)

@[simp]
theorem representative_quotient (R : FiniteQuotientRepresentatives N)
    (i : Fin R.m) :
    ((R.representative i : G) : G ⧸ N) = R.quotientEquiv i := by
  by_cases h : R.quotientEquiv i = 1
  · simp [representative, h]
  · simp [representative, h,
      MagnitudeConjecture.CoveringHom.CoherentDeckShift.normalQuotientRepresentative_mk]

@[simp]
theorem representative_first (R : FiniteQuotientRepresentatives N) :
    R.representative R.firstIndex = 1 := by
  unfold representative
  split
  · rfl
  · rename_i h
    exact False.elim (h R.first_eq_one)

@[simp]
theorem representative_zero (R : FiniteQuotientRepresentatives N) :
    R.representative 0 = 1 := by
  change R.representative R.firstIndex = 1
  exact R.representative_first

/-- Every ambient group element is a subgroup element times one chosen
quotient representative. -/
theorem exists_subgroup_mul_representative_eq
    (R : FiniteQuotientRepresentatives N) (g : G) :
    ∃ (i : Fin R.m) (n : N), (n : G) * R.representative i = g := by
  let i := R.quotientEquiv.symm (g : G ⧸ N)
  have hquotient : ((R.representative i : G) : G ⧸ N) = (g : G ⧸ N) := by
    rw [R.representative_quotient, R.quotientEquiv.apply_symm_apply]
  have hmem : R.representative i / g ∈ N :=
    QuotientGroup.eq_iff_div_mem.mp hquotient
  let n : N := ⟨g * (R.representative i)⁻¹, by
    simpa [div_eq_mul_inv] using N.inv_mem hmem⟩
  refine ⟨i, n, ?_⟩
  simp [n]

/-- The representative of the next quotient coset has not occurred in any
earlier subgroup orbit.  This is where freeness of the ambient object action
and injectivity of the chosen quotient enumeration enter the successor
deletion step. -/
theorem representative_smul_not_mem_stageDeletedSet
    [IsCancelSMul G C]
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m) :
    R.representative i • x ∉
      stageDeletedSet N R.representative x i.castSucc := by
  rintro ⟨r, hr, n, hn⟩
  have hgroup : (n : G) * R.representative r = R.representative i :=
    IsCancelSMul.right_cancel ((n : G) * R.representative r)
      (R.representative i) x (by simpa only [mul_smul] using hn)
  have hquotient : R.quotientEquiv r = R.quotientEquiv i := by
    have hnone : ((n : G) : G ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).2 n.property
    calc
      R.quotientEquiv r = ((R.representative r : G) : G ⧸ N) :=
        (R.representative_quotient r).symm
      _ = ((n : G) : G ⧸ N) * (R.representative r : G) := by
        rw [hnone, one_mul]
      _ = (((n : G) * R.representative r : G) : G ⧸ N) := by
        rw [QuotientGroup.mk_mul]
      _ = ((R.representative i : G) : G ⧸ N) := congrArg _ hgroup
      _ = R.quotientEquiv i := R.representative_quotient i
  have hri : r = i := R.quotientEquiv.injective hquotient
  subst r
  exact (Nat.lt_irrefl i.val) hr

/-- The first accumulated stage deletes precisely the subgroup orbit of the
chosen object. -/
theorem stageDeletedSet_first
    (R : FiniteQuotientRepresentatives N) (x : C) :
    stageDeletedSet N R.representative x (0 : Fin R.m).succ =
      subgroupOrbit N x := by
  rw [stageDeletedSet_succ]
  simp

/-- After all quotient representatives have been used, the accumulated
subgroup orbits are exactly the full ambient orbit. -/
theorem stageDeletedSet_last_eq_orbit
    (R : FiniteQuotientRepresentatives N) (x : C) :
    stageDeletedSet N R.representative x (Fin.last R.m) =
      MulAction.orbit G x := by
  ext Y
  rw [mem_stageDeletedSet_last_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, n, rfl⟩
    exact ⟨(n : G) * R.representative i, by simp [mul_smul]⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨i, n, hn⟩ := R.exists_subgroup_mul_representative_eq g
    refine ⟨i, n, ?_⟩
    simp only [smul_smul, hn]

end FiniteQuotientRepresentatives

section Categories

variable {k : Type z} [Ring k]
variable [Category.{v} C] [Preadditive C] [Linear k C]

/-- The stage-zero deletion category is canonically equivalent to the
ambient category. -/
noncomputable def stageZeroEquivalence {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) :
    C ≌ StageCategory (k := k) N representative x 0 :=
  (emptyDeletionEquivalence (k := k) C).trans
    (deletionEquivalenceOfEq (k := k) C
      (stageDeletedSet_zero N representative x).symm)

variable {N : Subgroup G} [N.Normal]

/-- The terminal stage is canonically equivalent to deletion of the full
ambient orbit. -/
noncomputable def stageLastEquivalence
    (R : FiniteQuotientRepresentatives N) (x : C) :
    StageCategory (k := k) N R.representative x (Fin.last R.m) ≌
      DeletionCategory (k := k) C (MulAction.orbit G x) :=
  deletionEquivalenceOfEq (k := k) C (R.stageDeletedSet_last_eq_orbit x)

end Categories

section FiniteIndex

/-- The canonical ordered quotient representatives associated with a
finite-index normal subgroup. -/
def finiteIndexQuotientRepresentatives (N : FiniteIndexNormalSubgroup G) :
    FiniteQuotientRepresentatives (N : Subgroup G) := by
  letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  exact FiniteQuotientRepresentatives.canonical

end FiniteIndex

end MagnitudeConjecture.ObjectDeletion
