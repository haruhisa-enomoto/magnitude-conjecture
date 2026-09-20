import MagnitudeConjecture.Graded.FiniteVectorGrading

/-! # Componentwise gradings on finite products of vector spaces -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace MagnitudeConjecture.Graded.VectorGrading

variable {k ι : Type*} [Field k] [Fintype ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
variable [∀ i, FiniteDimensional k (M i)] (G : ∀ i, VectorGrading k (M i))

/-- The union of the finite homogeneous supports of all coordinates. -/
def piSupport : Finset ℤ := Finset.univ.biUnion fun i ↦ (G i).degreeSupport

theorem sum_piSupport (i : ι) (x : M i) :
    ∑ d ∈ piSupport G, (G i).projection d x = x := by
  have hs : (G i).degreeSupport ⊆ piSupport G := by
    intro d hd
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hd⟩
  apply Eq.trans _ ((G i).sum_projection x)
  symm
  apply Finset.sum_subset hs
  intro d hd hout
  rw [(G i).projection_eq_zero_outside hout]
  rfl

/-- The degree-d component consists of tuples whose coordinates all have degree d. -/
def finitePi : VectorGrading k (∀ i, M i) where
  component d := Submodule.pi Set.univ (fun i ↦ (G i).component d)
  internal := by
    let C := fun d ↦ Submodule.pi Set.univ (fun i ↦ (G i).component d)
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro d
      let p : (∀ i, M i) →ₗ[k] (∀ i, M i) :=
        LinearMap.pi fun i ↦ ((G i).projection d).comp (LinearMap.proj i)
      have hk : (⨆ e, ⨆ (_ : e ≠ d), C e) ≤ p.ker := by
        apply iSup_le
        intro e
        apply iSup_le
        intro hed x hx
        apply funext
        intro i
        exact (G i).projection_of_mem_ne (hx i (Set.mem_univ i)) hed
      apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hz := hk hy
      apply funext
      intro i
      have hh := congrFun hz i
      change (G i).projection d (x i) = 0 at hh
      rw [(G i).projection_of_mem (hx i (Set.mem_univ i))] at hh
      exact hh
    · apply top_unique
      intro x hx
      have heq : x = ∑ d ∈ piSupport G, fun i ↦ (G i).projection d (x i) := by
        funext i
        simpa only [Finset.sum_apply] using (sum_piSupport G i (x i)).symm
      rw [heq]
      apply Submodule.sum_mem
      intro d hd
      apply (le_iSup C d)
      intro i hi
      exact (G i).projection_mem d (x i)

end MagnitudeConjecture.Graded.VectorGrading
