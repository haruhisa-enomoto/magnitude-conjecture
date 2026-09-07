import MagnitudeConjecture.Algebra.StringBoundQuiver
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Local vertex endomorphism rings of string quotients

At a displayed vertex of an admissible monomial bound-quiver quotient,
the surviving loops form a basis.  Splitting off the trivial loop writes
every endomorphism as a scalar identity plus a positive-length tail.  Path
length is additive under multiplication, while admissibility kills every
sufficiently long path, so the positive tail is nilpotent.  Consequently
the vertex endomorphism ring is local.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- Regard a vertex endomorphism in the quotient category as an element of
its endomorphism ring. -/
def quotientVertexEndLinearEquiv
    (P : StringPresentation k A Q) (y : Q) :
    (obj P.toPresentation.relations y ⟶
      obj P.toPresentation.relations y) ≃ₗ[k]
      End (obj P.toPresentation.relations y) where
  toFun := End.of
  invFun := End.asHom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The surviving-loop basis, regarded as a basis of the vertex
endomorphism ring. -/
def quotientVertexEndBasis
    (P : StringPresentation k A Q) (y : Q) :
    Module.Basis
      (SurvivingPath P.toPresentation.relations y y) k
      (End (obj P.toPresentation.relations y)) :=
  (survivingPathBasis P.toPresentation.relations P.monomial y y).map
    (P.quotientVertexEndLinearEquiv y)

@[simp]
theorem quotientVertexEndBasis_apply
    (P : StringPresentation k A Q) (y : Q)
    (p : SurvivingPath P.toPresentation.relations y y) :
    P.quotientVertexEndBasis y p =
      End.of (pathMap P.toPresentation.relations p.1) := by
  rw [quotientVertexEndBasis, Module.Basis.map_apply,
    survivingPathBasis_apply]
  rfl

/-- The surviving trivial loop at a displayed vertex. -/
def nilSurvivingLoop
    (P : StringPresentation k A Q) (y : Q) :
    SurvivingPath P.toPresentation.relations y y :=
  ⟨Quiver.Path.nil,
    pathMap_ne_zero_of_length_lt_two P.toPresentation.admissible
      Quiver.Path.nil (by simp)⟩

@[simp]
theorem quotientVertexEndBasis_nilSurvivingLoop
    (P : StringPresentation k A Q) (y : Q) :
    P.quotientVertexEndBasis y (P.nilSurvivingLoop y) = 1 := by
  rw [P.quotientVertexEndBasis_apply]
  change End.of
      ((LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map
          (LinearPathCategory.pathHom Quiver.Path.nil)) = 1
  rw [LinearPathCategory.pathHom_nil,
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_id]
  rfl

/-- The subspace spanned by surviving loops of length at least `n`. -/
def quotientVertexEndLengthTail
    (P : StringPresentation k A Q) (y : Q) (n : ℕ) :
    Submodule k (End (obj P.toPresentation.relations y)) :=
  Submodule.span k
    (P.quotientVertexEndBasis y ''
      {p | n ≤ p.1.length})

/-- A surviving-loop basis vector lies in every tail below its length. -/
theorem quotientVertexEndBasis_mem_lengthTail
    (P : StringPresentation k A Q) (y : Q) (n : ℕ)
    (p : SurvivingPath P.toPresentation.relations y y)
    (hp : n ≤ p.1.length) :
    P.quotientVertexEndBasis y p ∈
      P.quotientVertexEndLengthTail y n := by
  apply Submodule.subset_span
  exact ⟨p, hp, rfl⟩

/-- The length-zero tail is the whole vertex endomorphism ring. -/
theorem quotientVertexEndLengthTail_zero_eq_top
    (P : StringPresentation k A Q) (y : Q) :
    P.quotientVertexEndLengthTail y 0 = ⊤ := by
  apply top_unique
  rw [← (P.quotientVertexEndBasis y).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨p, rfl⟩
  exact ⟨p, Nat.zero_le _, rfl⟩

/-- If no surviving loop reaches length `n`, then the `n`th tail is zero. -/
theorem quotientVertexEndLengthTail_eq_bot_of_forall_lt
    (P : StringPresentation k A Q) (y : Q) (n : ℕ)
    (hn : ∀ p : SurvivingPath P.toPresentation.relations y y,
      p.1.length < n) :
    P.quotientVertexEndLengthTail y n = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.span_le.2
  rintro _ ⟨p, hp, rfl⟩
  exact False.elim (Nat.not_le_of_lt (hn p) hp)

/-- Admissibility makes one sufficiently deep surviving-loop tail zero. -/
theorem exists_quotientVertexEndLengthTail_eq_bot
    (P : StringPresentation k A Q) (y : Q) :
    ∃ n : ℕ, P.quotientVertexEndLengthTail y n = ⊥ := by
  obtain ⟨n, _, hlong⟩ := P.toPresentation.admissible.long_paths_mem
  refine ⟨n, P.quotientVertexEndLengthTail_eq_bot_of_forall_lt y n ?_⟩
  intro p
  apply Nat.lt_of_not_ge
  intro hp
  exact p.2 ((pathMap_eq_zero_iff_mem_relationIdeal
    P.toPresentation.relations p.1).2 (hlong p.1 hp))

set_option maxHeartbeats 800000 in
/-- Multiplication adds lower bounds on the lengths of surviving loops. -/
theorem mul_mem_quotientVertexEndLengthTail
    (P : StringPresentation k A Q) (y : Q) {i j : ℕ}
    {f g : End (obj P.toPresentation.relations y)}
    (hf : f ∈ P.quotientVertexEndLengthTail y i)
    (hg : g ∈ P.quotientVertexEndLengthTail y j) :
    f * g ∈ P.quotientVertexEndLengthTail y (i + j) := by
  let T := P.quotientVertexEndLengthTail y (i + j)
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨q, hq, rfl⟩ := hg
          rw [P.quotientVertexEndBasis_apply,
            P.quotientVertexEndBasis_apply]
          change End.of
              (pathMap P.toPresentation.relations q.1 ≫
                pathMap P.toPresentation.relations p.1) ∈ T
          rw [pathMap_comp]
          by_cases hzero :
              pathMap P.toPresentation.relations (p.1.comp q.1) = 0
          · rw [hzero]
            exact Submodule.zero_mem _
          · let r : SurvivingPath P.toPresentation.relations y y :=
              ⟨p.1.comp q.1, hzero⟩
            rw [← P.quotientVertexEndBasis_apply y r]
            apply P.quotientVertexEndBasis_mem_lengthTail
            change i + j ≤ (p.1.comp q.1).length
            simpa [Quiver.Path.length_comp] using Nat.add_le_add hp hq
      | zero => simpa only [mul_zero] using T.zero_mem
      | add g h _ _ hgm hhm =>
          simpa [mul_add] using T.add_mem hgm hhm
      | smul c g _ hgm =>
          simpa [Algebra.smul_mul_assoc] using T.smul_mem c hgm
  | zero => simpa only [zero_mul] using T.zero_mem
  | add f h _ _ hfm hhm =>
      simpa [add_mul] using T.add_mem hfm hhm
  | smul c f _ hfm =>
      simpa [Algebra.smul_mul_assoc] using T.smul_mem c hfm

/-- Every vertex endomorphism is a scalar identity plus a positive-length
tail. -/
theorem exists_eq_smul_one_add_mem_quotientVertexEndLengthTail_one
    (P : StringPresentation k A Q) (y : Q)
    (f : End (obj P.toPresentation.relations y)) :
    ∃ (c : k) (r : End (obj P.toPresentation.relations y)),
      r ∈ P.quotientVertexEndLengthTail y 1 ∧ f = c • 1 + r := by
  classical
  let b := P.quotientVertexEndBasis y
  let p₀ := P.nilSurvivingLoop y
  let c := b.repr f p₀
  let r := f - c • 1
  refine ⟨c, r, ?_, by simp [r]⟩
  rw [quotientVertexEndLengthTail, b.mem_span_image]
  intro p hp
  change 1 ≤ p.1.length
  apply Nat.one_le_iff_ne_zero.2
  intro hlength
  have hpPath : p.1 = Quiver.Path.nil :=
    Quiver.Path.eq_nil_of_length_zero p.1 hlength
  have hpp₀ : p = p₀ := by
    apply Subtype.ext
    exact hpPath
  subst p
  have hbone : b p₀ = 1 := by
    exact P.quotientVertexEndBasis_nilSurvivingLoop y
  have hrzero : b.repr r p₀ = 0 := by
    rw [show r = f - c • b p₀ by rw [hbone]]
    simp [c]
  exact (Finsupp.mem_support_iff.mp hp) hrzero

/-- Positive-length vertex endomorphisms are nilpotent. -/
theorem isNilpotent_of_mem_quotientVertexEndLengthTail_one
    (P : StringPresentation k A Q) (y : Q)
    (r : End (obj P.toPresentation.relations y))
    (hr : r ∈ P.quotientVertexEndLengthTail y 1) :
    IsNilpotent r := by
  have hpow : ∀ n : ℕ,
      r ^ n ∈ P.quotientVertexEndLengthTail y n := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, P.quotientVertexEndLengthTail_zero_eq_top]
        exact Submodule.mem_top
    | succ n ih =>
        rw [pow_succ]
        simpa only [Nat.add_comm] using
          P.mul_mem_quotientVertexEndLengthTail y ih hr
  obtain ⟨n, hn⟩ := P.exists_quotientVertexEndLengthTail_eq_bot y
  refine ⟨n, ?_⟩
  have h := hpow n
  rw [hn] at h
  exact h

/-- The endomorphism ring of a displayed quotient vertex is nontrivial,
witnessed by the surviving trivial path. -/
theorem quotientVertexEnd_nontrivial
    (P : StringPresentation k A Q) (y : Q) :
    Nontrivial (End (obj P.toPresentation.relations y)) := by
  refine ⟨1, 0, ?_⟩
  intro h
  have hzeroEnd : End.of (pathMap P.toPresentation.relations
      (Quiver.Path.nil : Quiver.Path y y)) = 0 := by
    calc
      End.of (pathMap P.toPresentation.relations
          (Quiver.Path.nil : Quiver.Path y y)) =
          P.quotientVertexEndBasis y (P.nilSurvivingLoop y) :=
        (P.quotientVertexEndBasis_apply y
          (P.nilSurvivingLoop y)).symm
      _ = 1 := P.quotientVertexEndBasis_nilSurvivingLoop y
      _ = 0 := h
  have hzero : pathMap P.toPresentation.relations
      (Quiver.Path.nil : Quiver.Path y y) = 0 :=
    congrArg End.asHom hzeroEnd
  exact (P.nilSurvivingLoop y).2 hzero

/-- Every displayed vertex of an admissible monomial bound-quiver quotient
has a local endomorphism ring. -/
theorem quotientVertexEnd_isLocalRing
    (P : StringPresentation k A Q) (y : Q) :
    IsLocalRing (End (obj P.toPresentation.relations y)) := by
  letI : Nontrivial (End (obj P.toPresentation.relations y)) :=
    P.quotientVertexEnd_nontrivial y
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  obtain ⟨c, r, hr, hfr⟩ :=
    P.exists_eq_smul_one_add_mem_quotientVertexEndLengthTail_one y f
  have hrnil := P.isNilpotent_of_mem_quotientVertexEndLengthTail_one y r hr
  by_cases hc : c = 0
  · right
    subst c
    simpa [hfr] using hrnil.isUnit_one_sub
  · left
    have hu : IsUnit (c • (1 : End (obj P.toPresentation.relations y))) := by
      rw [Algebra.smul_def]
      exact (isUnit_iff_ne_zero.mpr hc).map
        (algebraMap k (End (obj P.toPresentation.relations y)))
    have hcomm : Commute r (c • (1 : End (obj P.toPresentation.relations y))) := by
      rw [Algebra.smul_def]
      exact (Algebra.commutes c r).symm
    rw [hfr]
    simpa only [add_comm] using
      hrnil.isUnit_add_right_of_commute hu hcomm

/-- Every object of the quotient category is represented by a displayed
vertex, so all of its endomorphism rings are local. -/
theorem quotientEnd_isLocalRing
    (P : StringPresentation k A Q)
    (X : Category P.toPresentation.relations) :
    IsLocalRing (End X) := by
  rcases X with ⟨y⟩
  exact P.quotientVertexEnd_isLocalRing y

end StringPresentation

end MagnitudeConjecture.BoundQuiver
