import MagnitudeConjecture.CategoryTheory.GradedIntervalIdempotentAction
import MagnitudeConjecture.LinearAlgebra.SingleCoordinate

/-! # Recovering each representation coordinate from the reconstructed graded module -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable (F : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k)
variable [F.Additive] [F.Linear k]
variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ)

/-- The idempotent-fixed homogeneous component is exactly one coordinate subspace. -/
theorem reconstructedCoordinate_eq_single (p : ι × Fin (m + 1)) :
    letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
    letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
    idempotentComponent R (intervalReconstructedGrading R hmul e he0 he F hneg h1 hsum horth m)
      (e p.1) p.2.val =
    singleCoordinate (k := k)
      (fun q : ι × Fin (m + 1) ↦ F.obj (op (intervalProjectiveLabel R hmul e he0 m q))) p := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
  ext x
  constructor
  · intro hx q hqp
    by_cases hd : q.2 = p.2
    · have hi : q.1 ≠ p.1 := fun h ↦ hqp (Prod.ext h hd)
      have heq := congrFun hx.2 q
      change intervalActionMap R hmul e he0 he F m (e p.1) x q = x q at heq
      rw [intervalActionMap_idempotent R hmul e he0 he horth F, if_neg hi] at heq
      exact heq.symm
    · apply hx.1 q
      change (q.2.val : ℤ) ≠ p.2.val
      intro h
      apply hd
      apply Fin.ext
      exact_mod_cast h
  · intro hx
    constructor
    · intro q hq
      apply hx q
      intro h
      subst q
      exact hq rfl
    · funext q
      change intervalActionMap R hmul e he0 he F m (e p.1) x q = x q
      rw [intervalActionMap_idempotent R hmul e he0 he horth F]
      by_cases hi : q.1 = p.1
      · rw [if_pos hi]
      · rw [if_neg hi]
        exact (hx q (fun h ↦ hi (congrArg Prod.fst h))).symm

/-- Evaluation at (i,r) recovers the original vector space from the reconstructed coordinate. -/
def reconstructedCoordinateEquiv (p : ι × Fin (m + 1)) :
    letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
    letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
    idempotentComponent R (intervalReconstructedGrading R hmul e he0 he F hneg h1 hsum horth m)
      (e p.1) p.2.val ≃ₗ[k] F.obj (op (intervalProjectiveLabel R hmul e he0 m p)) := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
  exact (LinearEquiv.ofEq _ _ (reconstructedCoordinate_eq_single R hmul e he0 he F hneg h1 hsum horth m p)).trans
    (singleCoordinateEquiv (k := k) _ p)

end MagnitudeConjecture.Graded.FiniteGradedModule
