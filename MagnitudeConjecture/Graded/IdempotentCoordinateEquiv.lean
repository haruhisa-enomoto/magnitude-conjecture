import MagnitudeConjecture.Graded.IdempotentProjections

/-! # Finite homogeneous idempotent coordinates of an actual module -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.ModuleGrading
variable {k A M : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable {R : VectorGrading k A} (G : ModuleGrading (M := M) R)

variable {ι ν : Type*} [Fintype ι] [Fintype ν]
variable (e : ι → A) (he : ∀ i, e i * e i = e i)
variable (he0 : ∀ i, e i ∈ R.component 0)
variable (hsum : ∑ i, e i = 1) (horth : Pairwise fun i j ↦ e i * e j = 0)
variable (δ : ν → ℤ) (hδ : Function.Injective δ)
variable (hcover : ∀ d, G.component d ≠ ⊥ → ∃ q, δ q = d)

/-- An actual graded module is the product of its finitely many homogeneous idempotent parts. -/
def idempotentCoordinateEquiv : M ≃ₗ[k]
    (∀ p : ι × ν, idempotentComponent R G (e p.1) (δ p.2)) where
  toFun x p := ⟨G.idempotentProjection (e p.1) (δ p.2) x,
    G.idempotentProjection_mem (e p.1) (he p.1) (he0 p.1) (δ p.2) x⟩
  invFun x := ∑ p, (x p).val
  left_inv x := G.sum_idempotentProjection e hsum δ hδ hcover x
  right_inv x := by
    classical
    funext p
    apply Subtype.ext
    change G.idempotentProjection (e p.1) (δ p.2) (∑ q, (x q).val) = (x p).val
    rw [map_sum, Finset.sum_eq_single p]
    · exact G.idempotentProjection_of_mem _ _ _ (x p).property
    · intro q hq hqp
      by_cases hd : δ q.2 = δ p.2
      · have hi : p.1 ≠ q.1 := fun hi ↦ hqp (Prod.ext hi.symm (hδ hd))
        have hx : (x q).val ∈ idempotentComponent R G (e q.1) (δ p.2) :=
          hd ▸ (x q).property
        exact G.idempotentProjection_of_orthogonal (horth hi) _ _ hx
      · exact G.idempotentProjection_of_degree_ne _ hd _ (x q).property.1
    · simp
  map_add' x y := by
    funext p
    apply Subtype.ext
    exact (G.idempotentProjection (e p.1) (δ p.2)).map_add x y
  map_smul' c x := by
    funext p
    apply Subtype.ext
    exact (G.idempotentProjection (e p.1) (δ p.2)).map_smul c x

end MagnitudeConjecture.Graded.ModuleGrading
