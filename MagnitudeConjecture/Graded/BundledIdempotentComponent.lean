import MagnitudeConjecture.Graded.IdempotentProjective
import MagnitudeConjecture.Graded.ModuleBundling

/-! # Idempotent coordinates commute with bundling a graded module -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.ModuleGrading
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {M : Type v} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [FiniteDimensional k M] {R : VectorGrading k A} (G : ModuleGrading (M := M) R)

/-- The canonical bundled field action preserves each homogeneous idempotent coordinate. -/
def bundledIdempotentComponentEquiv (e : A) (d : ℤ) :
    idempotentComponent R G.toBundled.grading e d ≃ₗ[k] idempotentComponent R G e d where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := Subtype.ext
    ((moduleCatScalarEquiv (k := k) (A := A) (M := M)).map_smul c x.val)

end MagnitudeConjecture.Graded.ModuleGrading
