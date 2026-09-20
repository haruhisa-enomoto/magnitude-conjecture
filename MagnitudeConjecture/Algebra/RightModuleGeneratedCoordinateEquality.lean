import MagnitudeConjecture.Algebra.RightModuleGeneratedAtIdempotent
import MagnitudeConjecture.LinearAlgebra.ScalarCornerGeneratedCoordinate

/-! # No extra coordinate relations are generated at a scalar corner -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- For a scalar corner, the e-coordinate of the generated relation module
contains exactly the original vector-space relations. -/
theorem mem_generatedCoordinateRelations_iff
    {e : A} (he : IsIdempotentElem e)
    (hcorner : ∀ a : Aᵐᵒᵖ, ∃ c : k,
      MulOpposite.op e * a * MulOpposite.op e =
        algebraMap k Aᵐᵒᵖ c * MulOpposite.op e)
    (V : FinitelyGeneratedCategory A)
    (R : Submodule k (idempotentCoordinate (k := k) e V))
    (x : idempotentCoordinate (k := k) e V) :
    (x : V) ∈ generatedCoordinateRelations e V R ↔ x ∈ R := by
  let W := R.map (idempotentCoordinate (k := k) e V).subtype
  have hfix : ∀ y ∈ W, (MulOpposite.op e) • y = y := by
    rintro y ⟨r, hr, rfl⟩
    exact idempotentCoordinate_fixed he V r
  constructor
  · intro hx
    have hw : (x : V) ∈ W :=
      (ScalarCorner.mem_span_and_fixed_iff (MulOpposite.op e) W hfix hcorner x).1
        ⟨hx, idempotentCoordinate_fixed he V x⟩
    obtain ⟨r, hr, heq⟩ := hw
    have hrx : r = x := Subtype.ext heq
    rwa [hrx] at hr
  · intro hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩

end MagnitudeConjecture.RightModule
