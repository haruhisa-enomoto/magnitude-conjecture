import MagnitudeConjecture.CategoryTheory.GradedPrincipalRetainedBlocks
import MagnitudeConjecture.CategoryTheory.OrthogonalModuleSupport

/-! # The block support of actual retained interval modules -/
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
variable (he0 : ∀ i, e i ∈ R.component 0)

/-- The unique block number of a literal retained object. -/
def principalRetainedBlock (r h q : ℕ)
    (X : PrincipalRetainedCategory R hmul e he0 r h q) : Fin q :=
  ((principalRetainedBlockEquiv R hmul e he0 r h q).symm X).1

/-- The degree of a retained object lies in the block specified by its coordinates. -/
theorem principalRetainedBlock_inBlock (r h q : ℕ)
    (X : PrincipalRetainedCategory R hmul e he0 r h q) :
    GradedInterval.InBlock r h (principalRetainedBlock R hmul e he0 r h q X).val
      (X.obj.unop.2.val : ℤ) := by
  let E := principalRetainedBlockEquiv R hmul e he0 r h q
  let p := E.symm X
  have hx : X = principalRetainedBlockObject R hmul e he0 r h q p := (E.apply_symm_apply X).symm
  have hd := congrArg (fun Y : PrincipalRetainedCategory R hmul e he0 r h q ↦ Y.obj.unop.2) hx
  change GradedInterval.InBlock r h p.1.val (X.obj.unop.2.val : ℤ)
  rw [hd]
  exact GradedInterval.blockPoint_inBlock r h q p.1 p.2.2

variable (he : ∀ i, e i * e i = e i)
variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥)

include he hneg hupper in
/-- The literal retained category has zero Hom spaces between different blocks. -/
theorem principalRetained_hom_eq_zero_of_block_ne (r q : ℕ)
    (X Y : PrincipalRetainedCategory R hmul e he0 r h q)
    (hXY : principalRetainedBlock R hmul e he0 r h q X ≠
      principalRetainedBlock R hmul e he0 r h q Y) (f : X ⟶ Y) : f = 0 := by
  apply ObjectProperty.hom_ext
  apply Quiver.Hom.unop_inj
  apply InducedCategory.hom_ext
  exact principalDegree_hom_eq_zero_of_separated R hmul e he0 he hneg h hupper r
    (fun hv ↦ hXY (Fin.ext hv).symm)
    (principalRetainedBlock_inBlock R hmul e he0 r h q Y)
    (principalRetainedBlock_inBlock R hmul e he0 r h q X) f.hom.unop.hom

include he hneg hupper in
/-- Every indecomposable module on the actual retained category belongs to
exactly one of its separated blocks. -/
theorem principalRetained_indecomposable_unique_block (r q : ℕ)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := PrincipalRetainedCategory R hmul e he0 r h q) k) (hM : Indecomposable M) :
    ∃! j : Fin q, ∀ X : PrincipalRetainedCategory R hmul e he0 r h q,
      principalRetainedBlock R hmul e he0 r h q X ≠ j →
        CategoryTheory.Limits.IsZero (M.obj.obj.obj X) :=
  CoveringHom.existsUnique_support_block (principalRetainedBlock R hmul e he0 r h q)
    (principalRetained_hom_eq_zero_of_block_ne R hmul e he0 he hneg h hupper r q) M hM

end MagnitudeConjecture.Graded.FiniteGradedModule
