import MagnitudeConjecture.CategoryTheory.GradedModuleHomCategory
import MagnitudeConjecture.Graded.EquivTransport

/-! # Bundling graded modules with the canonical field action -/
set_option autoImplicit false
noncomputable section
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {M : Type v} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

def bundledModule : ModuleCat A := ModuleCat.of A M

/-- The canonical field action on a bundled algebra module agrees linearly
with any given compatible field action. -/
def moduleCatScalarEquiv : (bundledModule (A := A) (M := M)) ≃ₗ[k] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change M at x
    change (algebraMap k A c) • (x : M) = c • (x : M)
    exact IsScalarTower.algebraMap_smul A c (x : M)

/-- Bundle the grading after identifying the two compatible field actions. -/
def ModuleGrading.toBundled {R : VectorGrading k A} (G : ModuleGrading (M := M) R)
    [FiniteDimensional k M] : FiniteGradedModule R where
  module := bundledModule (A := A) (M := M)
  finite := Module.Finite.equiv (moduleCatScalarEquiv (k := k) (A := A) (M := M)).symm
  grading :=
    { toVectorGrading := G.toVectorGrading.comap (moduleCatScalarEquiv (k := k) (A := A))
      smul_mem := fun ha hx ↦ G.smul_mem ha hx }

end MagnitudeConjecture.Graded
