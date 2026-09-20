import MagnitudeConjecture.CategoryTheory.GradedPrincipalDegreeShift
import MagnitudeConjecture.CategoryTheory.GradedPrincipalSeparatedDeletion
import MagnitudeConjecture.CategoryTheory.OrthogonalMatrixBlocks
import MagnitudeConjecture.CategoryTheory.LinearMatrixFunctor

/-! # The product algebra of translated principal-projective blocks -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

/-- A single interval as a tuple in the whole principal degree category. -/
abbrev principalIntervalTuple (r : ℕ) : Mat_ (PrincipalDegreeCategory R hmul e he0) :=
  ⟨ι × Fin (r + 1), intervalProjectiveLabel R hmul e he0 r⟩

/-- The principal projective at one point of the j-th translated block. -/
def principalBlockFamily (r h j : ℕ) (p : ι × Fin (r + 1)) :
    PrincipalDegreeCategory R hmul e he0 :=
  (p.1, (p.2.val : ℤ) + (j : ℤ) * ((r : ℤ) + h + 1))

/-- Block labels have the required degree support. -/
theorem principalBlockFamily_inBlock (r h j : ℕ) (p : ι × Fin (r + 1)) :
    GradedInterval.InBlock r h j (principalBlockFamily R hmul e he0 r h j p).2 := by
  have ht := p.2.isLt
  dsimp [principalBlockFamily, GradedInterval.InBlock]
  constructor <;> omega

/-- The tuple of all retained translated blocks. -/
abbrev principalSeparatedBlockTuple (r h q : ℕ) : Mat_ (PrincipalDegreeCategory R hmul e he0) :=
  MagnitudeConjecture.CategoryTheory.blockMatrixTuple
    (fun j : Fin q ↦ principalBlockFamily R hmul e he0 r h j.val)

/-- Common degree translation identifies each block's endomorphism algebra
with the original interval tuple's algebra. -/
def principalBlockEndAlgEquiv (r h q : ℕ) (j : Fin q) :
    End (principalIntervalTuple R hmul e he0 r) ≃ₐ[k]
      End (MagnitudeConjecture.CategoryTheory.blockMatrixTupleAt
        (fun l : Fin q ↦ principalBlockFamily R hmul e he0 r h l.val) j) :=
  MagnitudeConjecture.CategoryTheory.matrixFunctorEndAlgEquiv
    (principalDegreeShift R hmul e he0 he ((j.val : ℤ) * ((r : ℤ) + h + 1)))
    (principalIntervalTuple R hmul e he0 r)

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥)

/-- The algebra of q separated blocks is the product of q copies of the
small interval tuple's algebra. -/
def principalSeparatedBlockEndAlgEquiv (r q : ℕ) :
    End (principalSeparatedBlockTuple R hmul e he0 r h q) ≃ₐ[k]
      (Fin q → End (principalIntervalTuple R hmul e he0 r)) := by
  let X := fun j : Fin q ↦ principalBlockFamily R hmul e he0 r h j.val
  have hz : ∀ j l : Fin q, j ≠ l → ∀ i t : ι × Fin (r + 1),
      ∀ f : X j i ⟶ X l t, f = 0 := by
    intro j l hjl i t f
    exact principalDegree_hom_eq_zero_of_separated R hmul e he0 he hneg h hupper r
      (fun heq ↦ hjl (Fin.ext heq))
      (principalBlockFamily_inBlock R hmul e he0 r h j.val i)
      (principalBlockFamily_inBlock R hmul e he0 r h l.val t) f
  exact (MagnitudeConjecture.CategoryTheory.orthogonalBlockEndAlgEquiv X hz).trans
    (AlgEquiv.piCongrRight (fun j ↦ (principalBlockEndAlgEquiv R hmul e he0 he r h q j).symm))

end MagnitudeConjecture.Graded.FiniteGradedModule
