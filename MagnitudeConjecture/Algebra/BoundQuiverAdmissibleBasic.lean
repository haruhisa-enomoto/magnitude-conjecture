import MagnitudeConjecture.Algebra.BoundQuiverPresentation
import Mathlib.CategoryTheory.Skeletal
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Basicness of admissible bound-quiver algebras

The positive path-length filtration survives an arbitrary admissible
relation quotient; no monomial hypothesis is needed.  Its positive part is
nilpotent, every vertex endomorphism is a scalar plus a positive term, and
maps between distinct displayed vertices are positive.  Consequently the
displayed vertex endomorphism rings are local and the quotient category is
skeletal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- The objects of any relation quotient are exactly its displayed quiver
vertices. -/
def relationQuotientObjectEquiv (R : RelationFamily k Q) : Category R ≃ Q where
  toFun X := LinearPathCategory.vertex
    ((CategoryTheory.Quotient.equiv
      (LinearPathCategory.HomogeneousQuotient.relationIdeal R).rel) X)
  invFun z := obj R z
  left_inv X := by cases X; rfl
  right_inv z := rfl

namespace IsAdmissible

variable {R : RelationFamily k Q} (hR : IsAdmissible R)

/-- The image of the free path-length tail in a quotient Hom space. -/
def quotientHomLengthTail
    (_hR : IsAdmissible R)
    (X Y : LinearPathCategory.Category k Q) (n : ℕ) :
    Submodule k
      (LinearPathCategory.HomogeneousQuotient.obj R X ⟶
        LinearPathCategory.HomogeneousQuotient.obj R Y) :=
  (LinearPathCategory.lengthTail X Y n).map
    (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X Y)

/-- The zeroth quotient path tail is the full Hom space. -/
theorem quotientHomLengthTail_zero_eq_top
    (X Y : LinearPathCategory.Category k Q) :
    hR.quotientHomLengthTail X Y 0 = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨g, rfl⟩ :=
    LinearPathCategory.HomogeneousQuotient.quotientHom_surjective R X Y f
  refine ⟨g, ?_, rfl⟩
  change g ∈ LinearPathCategory.lengthTail X Y 0
  rw [LinearPathCategory.mem_lengthTail_iff]
  intro p _
  exact Nat.zero_le p.length

/-- Raising the cutoff shrinks the quotient path-length tail. -/
theorem quotientHomLengthTail_antitone
    (X Y : LinearPathCategory.Category k Q) {m n : ℕ} (hmn : m ≤ n) :
    hR.quotientHomLengthTail X Y n ≤
      hR.quotientHomLengthTail X Y m :=
  Submodule.map_mono (LinearPathCategory.lengthTail_antitone X Y hmn)

/-- Composition adds lower bounds in the quotient path filtration. -/
theorem comp_mem_quotientHomLengthTail
    {X Y Z : LinearPathCategory.Category k Q} {i j : ℕ}
    {f : LinearPathCategory.HomogeneousQuotient.obj R X ⟶
      LinearPathCategory.HomogeneousQuotient.obj R Y}
    {g : LinearPathCategory.HomogeneousQuotient.obj R Y ⟶
      LinearPathCategory.HomogeneousQuotient.obj R Z}
    (hf : f ∈ hR.quotientHomLengthTail X Y i)
    (hg : g ∈ hR.quotientHomLengthTail Y Z j) :
    f ≫ g ∈ hR.quotientHomLengthTail X Z (i + j) := by
  rcases hf with ⟨f, hf, rfl⟩
  rcases hg with ⟨g, hg, rfl⟩
  refine ⟨f ≫ g,
    LinearPathCategory.comp_mem_lengthTail hf hg, ?_⟩
  exact (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map_comp f g

/-- The admissibility cutoff makes a sufficiently deep quotient tail zero. -/
theorem exists_quotientHomLengthTail_eq_bot
    (X Y : LinearPathCategory.Category k Q) :
    ∃ n : ℕ, hR.quotientHomLengthTail X Y n = ⊥ := by
  obtain ⟨n, -, hlong⟩ :=
    BoundQuiver.IsAdmissible.long_paths_mem hR
  refine ⟨n, le_bot_iff.mp ?_⟩
  rintro f ⟨g, hg, rfl⟩
  change
    LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X Y g = 0
  rw [← LinearMap.mem_ker,
    LinearPathCategory.HomogeneousQuotient.ker_quotientHomLinearMap]
  rw [LinearPathCategory.lengthTail_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨p, hp, rfl⟩
      exact hlong p hp
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

/-- Every map between distinct displayed vertices belongs to the positive
quotient path tail. -/
theorem quotientHomLengthTail_one_eq_top_of_vertex_ne
    {X Y : LinearPathCategory.Category k Q}
    (hXY : LinearPathCategory.vertex Y ≠ LinearPathCategory.vertex X) :
    hR.quotientHomLengthTail X Y 1 = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨g, rfl⟩ :=
    LinearPathCategory.HomogeneousQuotient.quotientHom_surjective R X Y f
  refine ⟨g, ?_, rfl⟩
  change g ∈ LinearPathCategory.lengthTail X Y 1
  rw [LinearPathCategory.mem_lengthTail_iff]
  intro p hp
  apply Nat.one_le_iff_ne_zero.2
  intro hzero
  exact hXY (Quiver.Path.eq_of_length_zero p hzero)

/-- Every quotient vertex endomorphism is a scalar identity plus an element
of the positive path tail. -/
theorem exists_eq_smul_one_add_mem_quotientHomLengthTail_one
    (X : LinearPathCategory.Category k Q)
    (f : End (LinearPathCategory.HomogeneousQuotient.obj R X)) :
    ∃ (c : k)
      (r : End (LinearPathCategory.HomogeneousQuotient.obj R X)),
      End.asHom r ∈ hR.quotientHomLengthTail X X 1 ∧
        f = c • 1 + r := by
  obtain ⟨g, hg⟩ :=
    LinearPathCategory.HomogeneousQuotient.quotientHom_surjective R X X f
  let c := LinearPathCategory.nilPathCoefficient X g
  let r₀ := g - c • 𝟙 X
  have hr₀ : r₀ ∈ LinearPathCategory.lengthTail X X 1 := by
    rw [LinearPathCategory.mem_lengthTail_iff]
    intro p hp
    apply Nat.one_le_iff_ne_zero.2
    intro hzero
    have hpNil : p = Quiver.Path.nil :=
      Quiver.Path.eq_nil_of_length_zero p hzero
    subst p
    apply Finsupp.mem_support_iff.mp hp
    change LinearPathCategory.nilPathCoefficient X r₀ = 0
    simp [r₀, c]
  let r : End (LinearPathCategory.HomogeneousQuotient.obj R X) :=
    End.of
      (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X X r₀)
  refine ⟨c, r, ⟨r₀, hr₀, rfl⟩, ?_⟩
  apply End.ext
  change
    End.asHom f = End.asHom
      (c • (1 : End
        (LinearPathCategory.HomogeneousQuotient.obj R X)) + r)
  calc
    End.asHom f =
        LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
          R X X g := hg.symm
    _ = LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
          R X X (c • 𝟙 X + r₀) := by
      rw [show g = c • 𝟙 X + r₀ by simp [r₀]]
    _ = c •
          LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
            R X X (𝟙 X) +
          LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
            R X X r₀ := by simp
    _ = c • 𝟙 (LinearPathCategory.HomogeneousQuotient.obj R X) +
          LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
            R X X r₀ := by
      have hid :
          LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
              R X X (𝟙 X) =
            𝟙 (LinearPathCategory.HomogeneousQuotient.obj R X) :=
        (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map_id X
      rw [hid]
    _ = End.asHom
        (c • (1 : End
          (LinearPathCategory.HomogeneousQuotient.obj R X)) + r) := rfl

/-- Positive-tail vertex endomorphisms are nilpotent. -/
theorem isNilpotent_of_mem_quotientHomLengthTail_one
    (X : LinearPathCategory.Category k Q)
    (r : End (LinearPathCategory.HomogeneousQuotient.obj R X))
    (hr : End.asHom r ∈ hR.quotientHomLengthTail X X 1) :
    IsNilpotent r := by
  have hpow : ∀ n : ℕ,
      End.asHom (r ^ n) ∈ hR.quotientHomLengthTail X X n := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, hR.quotientHomLengthTail_zero_eq_top]
        exact Submodule.mem_top
    | succ n ih =>
        rw [pow_succ]
        simp only [End.mul_def]
        change End.asHom r ≫ End.asHom (r ^ n) ∈
          hR.quotientHomLengthTail X X (n + 1)
        simpa only [Nat.add_comm] using
          hR.comp_mem_quotientHomLengthTail hr ih
  obtain ⟨n, hn⟩ := hR.exists_quotientHomLengthTail_eq_bot X X
  refine ⟨n, ?_⟩
  have h := hpow n
  rw [hn] at h
  exact h

include hR

/-- The quotient identity at a displayed vertex is nonzero. -/
theorem quotientVertexEnd_nontrivial
    (X : LinearPathCategory.Category k Q) :
    Nontrivial (End (LinearPathCategory.HomogeneousQuotient.obj R X)) := by
  refine ⟨1, 0, ?_⟩
  intro h
  have hid : (𝟙 (LinearPathCategory.HomogeneousQuotient.obj R X)) = 0 := h
  have hzero : LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
      R X X (𝟙 X) = 0 := by
    rw [show
      LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X X
          (𝟙 X) =
        𝟙 (LinearPathCategory.HomogeneousQuotient.obj R X) from
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map_id X]
    exact hid
  have hmem : (𝟙 X) ∈ HomIdeal.generatedHomSubmodule k R X X := by
    rw [← LinearPathCategory.HomogeneousQuotient.ker_quotientHomLinearMap,
      LinearMap.mem_ker]
    exact hzero
  have htail :=
    BoundQuiver.IsAdmissible.relationIdeal_le_lengthTail_two hR X X hmem
  have hone : LinearPathCategory.nilPathCoefficient X (𝟙 X) = 0 := by
    rw [LinearPathCategory.nilPathCoefficient,
      LinearMap.comp_apply, Finsupp.lapply_apply,
      ← Finsupp.notMem_support_iff]
    intro hnil
    have hlength :=
      (LinearPathCategory.mem_lengthTail_iff X X 2 (𝟙 X)).1 htail hnil
    simpa using hlength
  simpa using hone

/-- Every displayed vertex has a local endomorphism ring. -/
theorem quotientVertexEnd_isLocalRing
    (X : LinearPathCategory.Category k Q) :
    IsLocalRing (End (LinearPathCategory.HomogeneousQuotient.obj R X)) := by
  letI : Nontrivial
      (End (LinearPathCategory.HomogeneousQuotient.obj R X)) :=
    hR.quotientVertexEnd_nontrivial X
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  obtain ⟨c, r, hr, hfr⟩ :=
    hR.exists_eq_smul_one_add_mem_quotientHomLengthTail_one X f
  have hrnil := hR.isNilpotent_of_mem_quotientHomLengthTail_one X r hr
  by_cases hc : c = 0
  · right
    subst c
    simpa [hfr] using hrnil.isUnit_one_sub
  · left
    have hu : IsUnit
        (c • (1 : End
          (LinearPathCategory.HomogeneousQuotient.obj R X))) := by
      rw [Algebra.smul_def]
      exact (isUnit_iff_ne_zero.mpr hc).map
        (algebraMap k
          (End (LinearPathCategory.HomogeneousQuotient.obj R X)))
    have hcomm : Commute r
        (c • (1 : End
          (LinearPathCategory.HomogeneousQuotient.obj R X))) := by
      rw [Algebra.smul_def]
      exact (Algebra.commutes c r).symm
    rw [hfr]
    simpa only [add_comm] using
      hrnil.isUnit_add_right_of_commute hu hcomm

/-- Every quotient object is represented by a displayed vertex, so every
endomorphism ring is local. -/
theorem quotientEnd_isLocalRing (Y : Category R) : IsLocalRing (End Y) := by
  rcases Y with ⟨X⟩
  exact hR.quotientVertexEnd_isLocalRing X

/-- Isomorphic displayed quotient vertices are equal. -/
theorem eq_of_quotientVertex_iso {x y : Q}
    (e : obj R x ≅ obj R y) : x = y := by
  by_contra hxy
  let X := LinearPathCategory.obj k Q x
  let Y := LinearPathCategory.obj k Q y
  have hhom : e.hom ∈ hR.quotientHomLengthTail X Y 1 := by
    rw [hR.quotientHomLengthTail_one_eq_top_of_vertex_ne]
    · exact Submodule.mem_top
    · exact Ne.symm hxy
  have hinv : e.inv ∈ hR.quotientHomLengthTail Y X 1 := by
    rw [hR.quotientHomLengthTail_one_eq_top_of_vertex_ne]
    · exact Submodule.mem_top
    · exact hxy
  have hcomp := hR.comp_mem_quotientHomLengthTail hhom hinv
  have hpositive : e.hom ≫ e.inv ∈ hR.quotientHomLengthTail X X 1 :=
    hR.quotientHomLengthTail_antitone X X (by omega) hcomp
  rw [e.hom_inv_id] at hpositive
  have hnil := hR.isNilpotent_of_mem_quotientHomLengthTail_one X 1 hpositive
  letI : Nontrivial (End (obj R x)) :=
    hR.quotientVertexEnd_nontrivial X
  exact not_isNilpotent_one hnil

/-- The quotient category of an admissible relation family is skeletal. -/
theorem quotientCategory_skeletal : Skeletal (Category R) := by
  intro X Y hXY
  obtain ⟨e⟩ := hXY
  let x := relationQuotientObjectEquiv R X
  let y := relationQuotientObjectEquiv R Y
  let eX : obj R x ≅ X :=
    eqToIso ((relationQuotientObjectEquiv R).symm_apply_apply X)
  let eY : obj R y ≅ Y :=
    eqToIso ((relationQuotientObjectEquiv R).symm_apply_apply Y)
  have hxy : x = y := hR.eq_of_quotientVertex_iso
    (eX.trans (e.trans eY.symm))
  exact (relationQuotientObjectEquiv R).injective hxy

end IsAdmissible

end MagnitudeConjecture.BoundQuiver
