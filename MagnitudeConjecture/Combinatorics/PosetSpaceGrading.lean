import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import MagnitudeConjecture.Combinatorics.PosetSpaceRealization

/-!
# Graded poset spaces

This file isolates the linear-algebra step in the frozen manuscript's grading
argument.  An internal grading of the total space of a poset representation is
compatible when every distinguished subspace is closed under the homogeneous
projections.  For a Schur poset space those projections are scalar
endomorphisms, so exactly one homogeneous component can be nonzero.

The generic one-dimensional lemma is also recorded separately.  It is the
tool used for the one-dimensional spaces `Hom(P, P_t)` in the projective
boundary realization.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

namespace GradedLinear

universe u v w

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {ι : Type w} [DecidableEq ι]

/-- A one-dimensional internally graded vector space has exactly one
nonzero component, and that component is the whole space. -/
theorem existsUnique_component_eq_top_of_finrank_eq_one
    (A : ι → Submodule k V) (hA : DirectSum.IsInternal A)
    (hfin : Module.finrank k V = 1) :
    ∃! i, A i = ⊤ := by
  classical
  letI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (hfin.symm ▸ Nat.zero_lt_one)
  letI : IsSimpleOrder (Submodule k V) :=
    is_simple_module_of_finrank_eq_one hfin
  have hnontrivial : (⊥ : Submodule k V) ≠ ⊤ := bot_ne_top
  have hexists : ∃ i, A i ≠ ⊥ := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hsup : (⨆ i, A i) = ⊥ := iSup_eq_bot.2 h
    rw [hA.submodule_iSup_eq_top] at hsup
    exact hnontrivial hsup.symm
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, (eq_bot_or_eq_top (A i)).resolve_left hi, ?_⟩
  intro j hj
  by_contra hji
  have hdisj : Disjoint (A i) (A j) :=
    hA.submodule_iSupIndep.pairwiseDisjoint (Ne.symm hji)
  rw [(eq_bot_or_eq_top (A i)).resolve_left hi, hj] at hdisj
  exact hnontrivial (disjoint_self.1 hdisj).symm

/-- Every nonzero vector in a one-dimensional internally graded vector space
lies in a unique homogeneous component. -/
theorem existsUnique_mem_of_finrank_eq_one
    (A : ι → Submodule k V) (hA : DirectSum.IsInternal A)
    (hfin : Module.finrank k V = 1) {v : V} (hv : v ≠ 0) :
    ∃! i, v ∈ A i := by
  obtain ⟨j, hjtop, hjunique⟩ :=
    existsUnique_component_eq_top_of_finrank_eq_one A hA hfin
  refine ⟨j, ?_, ?_⟩
  · change v ∈ A j
    rw [hjtop]
    exact Submodule.mem_top
  · intro i hi
    have hne : A i ≠ ⊥ := by
      intro hbot
      have : v ∈ (⊥ : Submodule k V) := hbot ▸ hi
      exact hv (by simpa using this)
    letI : IsSimpleOrder (Submodule k V) :=
      is_simple_module_of_finrank_eq_one hfin
    exact hjunique i ((eq_bot_or_eq_top (A i)).resolve_left hne)

section Shift

variable {W : Type w} [AddCommGroup W] [Module k W]

/-- A linear map shifts an `ℕ`-grading by `d` when it sends the degree-`i`
component into degree `i + d`. -/
def ShiftsDegree (A : ℕ → Submodule k V) (B : ℕ → Submodule k W)
    (f : V →ₗ[k] W) (d : ℕ) : Prop :=
  ∀ i ⦃v : V⦄, v ∈ A i → f v ∈ B (i + d)

/-- The range of a degree-shifting linear map is homogeneous in the target
grading. -/
theorem ShiftsDegree.range_isHomogeneous
    (A : ℕ → Submodule k V) (B : ℕ → Submodule k W)
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B)
    (f : V →ₗ[k] W) {d : ℕ} (hf : ShiftsDegree A B f d) :
    letI : DirectSum.Decomposition B := hB.chooseDecomposition
    DirectSum.SetLike.IsHomogeneous B (LinearMap.range f) := by
  letI : DirectSum.Decomposition A := hA.chooseDecomposition
  letI : DirectSum.Decomposition B := hB.chooseDecomposition
  intro j y hy
  obtain ⟨x, rfl⟩ := hy
  refine DirectSum.Decomposition.inductionOn A ?_ ?_ ?_ x
  · simp
  · rintro i ⟨x, hx⟩
    by_cases hij : i + d = j
    · subst j
      rw [DirectSum.decompose_of_mem_same B (hf i hx)]
      exact ⟨x, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne B (hf i hx) hij]
      exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add, DirectSum.decompose_add]
    exact Submodule.add_mem _ hx hy

end Shift

end GradedLinear

namespace PosetSpace

open CategoryTheory

universe u

variable {k T : Type u} [Field k] [PartialOrder T]

/-- An internal grading of a poset space whose degree projections preserve
all distinguished subspaces. -/
structure InternalGrading (X : Obj k T) where
  component : ℕ → Submodule k X
  isInternal : DirectSum.IsInternal component
  subspace_isHomogeneous :
    letI : DirectSum.Decomposition component := isInternal.chooseDecomposition
    ∀ t, DirectSum.SetLike.IsHomogeneous component (X.subspace t)

namespace InternalGrading

variable {X Y : Obj k T}

/-- Projection onto one homogeneous component, regarded as a poset-space
endomorphism. -/
noncomputable def projection (G : InternalGrading X) (i : ℕ) : X ⟶ X := by
  letI : DirectSum.Decomposition G.component := G.isInternal.chooseDecomposition
  exact
    { linear :=
        { toFun := fun x ↦ (DirectSum.decompose G.component x i : X)
          map_add' := fun x y ↦ by simp
          map_smul' := fun a x ↦ by
            rw [DirectSum.decompose_smul]
            rfl }
      map_subspace := fun t x hx ↦ G.subspace_isHomogeneous t i hx }

@[simp]
theorem projection_apply (G : InternalGrading X) (i : ℕ) (x : X) :
    (G.projection i).linear x =
      letI : DirectSum.Decomposition G.component := G.isInternal.chooseDecomposition
      (DirectSum.decompose G.component x i : X) :=
  rfl

theorem exists_component_ne_bot (G : InternalGrading X)
    (hne : ∃ x : X, x ≠ 0) :
    ∃ i, G.component i ≠ ⊥ := by
  by_contra h
  push Not at h
  have hsup : (⨆ i, G.component i) = ⊥ := iSup_eq_bot.2 h
  rw [G.isInternal.submodule_iSup_eq_top] at hsup
  obtain ⟨x, hx⟩ := hne
  exact hx (show x = 0 by
    have : x ∈ (⊥ : Submodule k X) := hsup ▸ Submodule.mem_top
    simpa using this)

theorem component_eq_top_of_ne_bot_of_isSchur
    (G : InternalGrading X) (hX : IsSchur k T X)
    (i : ℕ) (hi : G.component i ≠ ⊥) :
    G.component i = ⊤ := by
  letI : DirectSum.Decomposition G.component := G.isInternal.chooseDecomposition
  obtain ⟨v, hvA, hv⟩ := (G.component i).ne_bot_iff.mp hi
  obtain ⟨a, ha⟩ := hX.2 (G.projection i)
  have hproj_v : (G.projection i).linear v = v :=
    DirectSum.decompose_of_mem_same G.component hvA
  have hav : a • v = v := by
    calc
      a • v = (a • (LinearMap.id : X →ₗ[k] X)) v := by simp
      _ = (G.projection i).linear v := LinearMap.congr_fun ha.symm v
      _ = v := hproj_v
  have ha_one : a = 1 := by
    have hazero : (a - 1) • v = 0 := by
      rw [sub_smul, hav, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hazero).resolve_right hv)
  rw [eq_top_iff]
  intro x _
  have hproj_x : (G.projection i).linear x = x := by
    rw [ha, ha_one]
    simp
  rw [← hproj_x]
  exact (DirectSum.decompose G.component x i).property

/-- A Schur poset space carrying a compatible internal grading is
concentrated in one unique degree. -/
theorem existsUnique_component_eq_top
    (G : InternalGrading X) (hX : IsSchur k T X) :
    ∃! i, G.component i = ⊤ := by
  obtain ⟨i, hi⟩ := G.exists_component_ne_bot hX.1
  have hitop := G.component_eq_top_of_ne_bot_of_isSchur hX i hi
  refine ⟨i, hitop, ?_⟩
  intro j hjtop
  by_contra hji
  have hdisj : Disjoint (G.component i) (G.component j) :=
    G.isInternal.submodule_iSupIndep.pairwiseDisjoint (Ne.symm hji)
  rw [hitop, hjtop] at hdisj
  have hbot_top : (⊥ : Submodule k X) = ⊤ := (disjoint_self.1 hdisj).symm
  obtain ⟨x, hx⟩ := hX.1
  exact hx (show x = 0 by
    have : x ∈ (⊥ : Submodule k X) := hbot_top ▸ Submodule.mem_top
    simpa using this)

/-- The unique degree containing a compatibly graded Schur poset space. -/
noncomputable def level (G : InternalGrading X) (hX : IsSchur k T X) : ℕ :=
  (G.existsUnique_component_eq_top hX).choose

@[simp]
theorem component_level_eq_top (G : InternalGrading X)
    (hX : IsSchur k T X) :
    G.component (G.level hX) = ⊤ :=
  (G.existsUnique_component_eq_top hX).choose_spec.1

theorem eq_level_of_component_eq_top (G : InternalGrading X)
    (hX : IsSchur k T X) {i : ℕ} (hi : G.component i = ⊤) :
    i = G.level hX :=
  (G.existsUnique_component_eq_top hX).choose_spec.2 i hi

theorem component_eq_bot_of_ne_level (G : InternalGrading X)
    (hX : IsSchur k T X) {i : ℕ} (hi : i ≠ G.level hX) :
    G.component i = ⊥ := by
  by_contra hbot
  exact hi (G.eq_level_of_component_eq_top hX
    (G.component_eq_top_of_ne_bot_of_isSchur hX i hbot))

/-- A morphism is homogeneous of degree `d` when it sends degree `i` into
degree `i + d`. -/
def HomogeneousOfDegree (GX : InternalGrading X) (GY : InternalGrading Y)
    (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∀ i ⦃x : X⦄, x ∈ GX.component i →
    f.linear x ∈ GY.component (i + d)

/-- A nonzero homogeneous morphism between compatibly graded Schur poset
spaces identifies the target level with source level plus its degree. -/
theorem level_add_degree_eq
    (GX : InternalGrading X) (GY : InternalGrading Y)
    (hX : IsSchur k T X) (hY : IsSchur k T Y)
    {f : X ⟶ Y} {d : ℕ} (hf : f ≠ 0)
    (hhom : HomogeneousOfDegree GX GY f d) :
    GX.level hX + d = GY.level hY := by
  have hflinear : f.linear ≠ 0 := by
    intro hzero
    apply hf
    apply Hom.ext
    simpa using hzero
  have hex : ∃ x : X, f.linear x ≠ 0 := by
    by_contra h
    push Not at h
    apply hflinear
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hex
  have hxcomponent : x ∈ GX.component (GX.level hX) := by
    rw [GX.component_level_eq_top hX]
    exact Submodule.mem_top
  have himage := hhom (GX.level hX) hxcomponent
  have hcomponent_ne_bot :
      GY.component (GX.level hX + d) ≠ ⊥ := by
    intro hbot
    have : f.linear x ∈ (⊥ : Submodule k Y) := hbot ▸ himage
    exact hx (by simpa using this)
  exact GY.eq_level_of_component_eq_top hY
    (GY.component_eq_top_of_ne_bot_of_isSchur hY _ hcomponent_ne_bot)

/-- A nonzero homogeneous morphism of positive degree strictly raises the
concentration level. -/
theorem level_lt_of_homogeneousOfDegree
    (GX : InternalGrading X) (GY : InternalGrading Y)
    (hX : IsSchur k T X) (hY : IsSchur k T Y)
    {f : X ⟶ Y} {d : ℕ} (hf : f ≠ 0) (hd : 0 < d)
    (hhom : HomogeneousOfDegree GX GY f d) :
    GX.level hX < GY.level hY := by
  rw [← GX.level_add_degree_eq GY hX hY hf hhom]
  omega

end InternalGrading

end PosetSpace

end MagnitudeConjecture
