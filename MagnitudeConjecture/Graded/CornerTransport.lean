import MagnitudeConjecture.Graded.ProjectiveCorners
import MagnitudeConjecture.Graded.EquivTransport

/-! # Homogeneous corners under algebra equivalence -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded
variable {k A B : Type*} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- Pulling a grading and two idempotents back along an algebra equivalence
preserves their homogeneous corner spaces. -/
def cornerComapEquiv (R : VectorGrading k B) (E : A ≃ₐ[k] B) (e f : B) (d : ℤ) :
    cornerComponent (R.comap E.toLinearEquiv) (E.symm e) (E.symm f) d ≃ₗ[k]
      cornerComponent R e f d where
  toFun a := ⟨E a.val, a.property.1, by
    simpa using congrArg E a.property.2.1, by
    simpa using congrArg E a.property.2.2⟩
  invFun b := ⟨E.symm b.val, by
    change E (E.symm b.val) ∈ R.component d
    simpa using b.property.1, by
    simpa using congrArg E.symm b.property.2.1, by
    simpa using congrArg E.symm b.property.2.2⟩
  left_inv a := Subtype.ext (E.symm_apply_apply a.val)
  right_inv b := Subtype.ext (E.apply_symm_apply b.val)
  map_add' a b := Subtype.ext (E.map_add a.val b.val)
  map_smul' c a := Subtype.ext (E.toLinearEquiv.map_smul c a.val)

end MagnitudeConjecture.Graded
