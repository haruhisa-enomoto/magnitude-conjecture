import MagnitudeConjecture.CategoryTheory.GradedAdditiveEnvelope
import Mathlib.Algebra.Algebra.Pi

/-! # Endomorphism algebras of mutually orthogonal finite blocks -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace MagnitudeConjecture.CategoryTheory
universe u v
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {J I : Type} [Fintype J] [Fintype I]
variable (X : J → I → C)

/-- All objects in the block family, as one finite matrix object. -/
abbrev blockMatrixTuple : Mat_ C := ⟨J × I, fun p ↦ X p.1 p.2⟩

/-- The finite matrix object belonging to a single block. -/
abbrev blockMatrixTupleAt (j : J) : Mat_ C := ⟨I, X j⟩

/-- Extract the endomorphism matrix on one diagonal block. -/
def blockDiagonal (f : End (blockMatrixTuple X)) (j : J) : End (blockMatrixTupleAt X j) :=
  fun i l ↦ f (j, i) (j, l)

variable (hzero : ∀ j l : J, j ≠ l → ∀ i t : I, ∀ f : X j i ⟶ X l t, f = 0)

include hzero in
/-- Orthogonality makes restriction to a diagonal block preserve composition. -/
theorem blockDiagonal_comp (f g : End (blockMatrixTuple X)) (j : J) :
    blockDiagonal X (f ≫ g) j = blockDiagonal X f j ≫ blockDiagonal X g j := by
  classical
  apply Mat_.hom_ext
  intro i t
  change (∑ z : J × I, f (j, i) z ≫ g z (j, t)) =
    ∑ l : I, f (j, i) (j, l) ≫ g (j, l) (j, t)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_single j
  · intro l hl hlj
    apply Finset.sum_eq_zero
    intro s hs
    rw [hzero j l hlj.symm i s (f (j, i) (l, s)), zero_comp]
  · simp

/-- Restriction to the diagonal blocks is an algebra homomorphism. -/
def blockDiagonalAlgHom : End (blockMatrixTuple X) →ₐ[k] ∀ j, End (blockMatrixTupleAt X j) where
  toFun := blockDiagonal X
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by
    classical
    funext j
    apply Mat_.hom_ext
    intro i l
    change (𝟙 (blockMatrixTuple X) : End _ ) (j, i) (j, l) =
      (𝟙 (blockMatrixTupleAt X j) : End _) i l
    by_cases hi : i = l
    · subst l
      simp
    · rw [Mat_.id_apply_of_ne _ _ _ (by intro hh; exact hi (congrArg Prod.snd hh)), Mat_.id_apply_of_ne _ _ _ hi]
  map_mul' f g := by
    funext j
    exact blockDiagonal_comp X hzero g f j
  commutes' c := by
    change blockDiagonal X (c • 𝟙 (blockMatrixTuple X)) =
      fun j ↦ c • 𝟙 (blockMatrixTupleAt X j)
    funext j
    apply Mat_.hom_ext
    intro i l
    change c • (𝟙 (blockMatrixTuple X) : End _) (j, i) (j, l) =
      c • (𝟙 (blockMatrixTupleAt X j) : End _) i l
    congr 1
    classical
    by_cases hi : i = l
    · subst l
      simp
    · rw [Mat_.id_apply_of_ne _ _ _ (by intro hh; exact hi (congrArg Prod.snd hh)), Mat_.id_apply_of_ne _ _ _ hi]

include hzero in
/-- Every endomorphism is determined by its diagonal blocks. -/
theorem blockDiagonal_injective : Function.Injective (blockDiagonal X) := by
  intro f g hfg
  apply Mat_.hom_ext
  rintro ⟨j, i⟩ ⟨l, t⟩
  by_cases hj : j = l
  · subst l
    exact congrArg (fun F ↦ F j i t) hfg
  · rw [hzero j l hj i t (f (j, i) (l, t)), hzero j l hj i t (g (j, i) (l, t))]

/-- Any family of block endomorphisms extends to the full matrix object. -/
theorem blockDiagonal_surjective : Function.Surjective (blockDiagonal X) := by
  classical
  intro f
  let g : End (blockMatrixTuple X) := fun p q ↦
    if hpq : p.1 = q.1 then
      f p.1 p.2 q.2 ≫ eqToHom (congrArg (fun j ↦ X j q.2) hpq)
    else 0
  refine ⟨g, ?_⟩
  funext j
  apply Mat_.hom_ext
  intro i l
  simp only [blockDiagonal, g, dif_pos rfl]
  change f j i l ≫ 𝟙 _ = f j i l
  exact Category.comp_id _

/-- Mutually orthogonal blocks split the endomorphism algebra as a product. -/
def orthogonalBlockEndAlgEquiv :
    End (blockMatrixTuple X) ≃ₐ[k] ∀ j, End (blockMatrixTupleAt X j) :=
  AlgEquiv.ofBijective (blockDiagonalAlgHom X hzero)
    ⟨blockDiagonal_injective X hzero, blockDiagonal_surjective X⟩

end MagnitudeConjecture.CategoryTheory
