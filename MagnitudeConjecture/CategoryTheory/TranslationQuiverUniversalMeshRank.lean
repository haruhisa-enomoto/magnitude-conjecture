import MagnitudeConjecture.CategoryTheory.FiniteMeshEndLocal
import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalGrading

/-!
# The integer rank on a universal mesh category

Every quiver arrow in the augmented-walk universal cover raises vertex degree
by one.  Hence a path-length component of the associated raw mesh category can
be nonzero only in the degree forced by its endpoints.  In particular the
endomorphism ring at a mesh vertex consists only of scalar identities, and a
nonzero nonisomorphism in the opposite mesh category strictly raises vertex
degree.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable (T : RightMeshData Q) (x₀ : Q)

/-- The degree difference between the endpoints of a universal-cover quiver
path is its length. -/
theorem vertexDegree_path {W Z : Vertex T x₀} (p : Quiver.Path W Z) :
    vertexDegree T x₀ Z = vertexDegree T x₀ W + p.length := by
  induction p with
  | nil => simp
  | cons p a ih =>
      rw [vertexDegree_arrow T x₀ a, ih]
      simp only [Quiver.Path.length_cons, Nat.cast_add, Nat.cast_one]
      omega

variable [∀ y : Q, Fintype (Quiver.Star y)]

noncomputable local instance universalMeshRankStarFintype
    (W : Vertex T x₀) : Fintype (Quiver.Star W) :=
  (cover T x₀).sourceStarFintype W

/-- A universal-mesh path-length component vanishes unless its length agrees
with the endpoint degree difference.  Recall that a morphism from `W` to `Z`
is represented by quiver paths from `Z` to `W`. -/
theorem meshLengthComponent_eq_bot_of_vertexDegree_ne
    (W Z : Vertex T x₀) (n : ℕ)
    (hdegree : vertexDegree T x₀ W ≠
      vertexDegree T x₀ Z + n) :
    MeshCategory.lengthComponent (k := k) (rightMeshData T x₀) W Z n = ⊥ := by
  rw [MeshCategory.lengthComponent,
    LinearPathCategory.HomogeneousQuotient.lengthComponent]
  have hfree :
      LinearPathCategory.lengthComponent
        (LinearPathCategory.obj k (Vertex T x₀) W)
        (LinearPathCategory.obj k (Vertex T x₀) Z) n = ⊥ := by
    rw [LinearPathCategory.lengthComponent_eq_span, Submodule.span_eq_bot]
    intro f hf
    rcases hf with ⟨p, hp, rfl⟩
    exfalso
    apply hdegree
    have hpath := vertexDegree_path T x₀ p
    change vertexDegree T x₀ W =
      vertexDegree T x₀ Z + p.length at hpath
    change p.length = n at hp
    rw [hp] at hpath
    exact hpath
  rw [hfree, Submodule.map_bot]

/-- Nontriviality of a universal-mesh Hom space forces a path length and the
corresponding endpoint degree equation. -/
theorem exists_meshLength_of_nontrivial_hom
    (W Z : Vertex T x₀)
    [Nontrivial
      (MeshCategory.obj (k := k) (rightMeshData T x₀) W ⟶
        MeshCategory.obj (k := k) (rightMeshData T x₀) Z)] :
    ∃ n : ℕ, vertexDegree T x₀ W = vertexDegree T x₀ Z + n ∧
      MeshCategory.lengthComponent (k := k) (rightMeshData T x₀) W Z n ≠ ⊥ := by
  have hcomponent : ∃ n : ℕ,
      MeshCategory.lengthComponent (k := k) (rightMeshData T x₀) W Z n ≠ ⊥ := by
    by_contra h
    push Not at h
    have hsup :
        (⨆ n, MeshCategory.lengthComponent
          (k := k) (rightMeshData T x₀) W Z n) = ⊥ :=
      iSup_eq_bot.2 h
    rw [(MeshCategory.lengthComponent_isInternal
      (k := k) (rightMeshData T x₀) W Z).submodule_iSup_eq_top] at hsup
    exact (bot_ne_top :
      (⊥ : Submodule k
        (MeshCategory.obj (k := k) (rightMeshData T x₀) W ⟶
          MeshCategory.obj (k := k) (rightMeshData T x₀) Z)) ≠ ⊤) hsup.symm
  obtain ⟨n, hn⟩ := hcomponent
  refine ⟨n, ?_, hn⟩
  by_contra hdegree
  exact hn (meshLengthComponent_eq_bot_of_vertexDegree_ne
    (k := k) T x₀ W Z n hdegree)

/-- Every endomorphism of a universal-mesh vertex is a scalar multiple of
the identity. -/
theorem meshEndomorphism_eq_smul_id
    (W : Vertex T x₀)
    (f : MeshCategory.obj (k := k) (rightMeshData T x₀) W ⟶
      MeshCategory.obj (k := k) (rightMeshData T x₀) W) :
    ∃ c : k, f = c • 𝟙 _ := by
  have hzeroTop :
      MeshCategory.lengthComponent (k := k) (rightMeshData T x₀) W W 0 = ⊤ := by
    apply top_unique
    rw [← (MeshCategory.lengthComponent_isInternal
      (k := k) (rightMeshData T x₀) W W).submodule_iSup_eq_top]
    refine iSup_le fun n ↦ ?_
    by_cases hn : n = 0
    · subst n
      exact le_rfl
    · rw [meshLengthComponent_eq_bot_of_vertexDegree_ne
          (k := k) T x₀ W W n]
      · exact bot_le
      · omega
  have hf : f ∈
      MeshCategory.lengthComponent (k := k) (rightMeshData T x₀) W W 0 := by
    rw [hzeroTop]
    exact Submodule.mem_top
  rw [MeshCategory.lengthComponent_zero_self] at hf
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
  exact ⟨c, hc.symm⟩

/-- A nonzero universal-mesh endomorphism is an isomorphism. -/
theorem meshEndomorphism_isIso_of_ne_zero
    (W : Vertex T x₀)
    (f : MeshCategory.obj (k := k) (rightMeshData T x₀) W ⟶
      MeshCategory.obj (k := k) (rightMeshData T x₀) W)
    (hf : f ≠ 0) : IsIso f := by
  obtain ⟨c, rfl⟩ := meshEndomorphism_eq_smul_id (k := k) T x₀ W f
  have hc : c ≠ 0 := by
    intro hc
    subst c
    simp at hf
  apply (isUnit_iff_isIso _).1
  change IsUnit (c • (1 : End
    (MeshCategory.obj (k := k) (rightMeshData T x₀) W)))
  rw [Algebra.smul_def]
  exact (isUnit_iff_ne_zero.mpr hc).map
    (algebraMap k (End
      (MeshCategory.obj (k := k) (rightMeshData T x₀) W)))

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
