import MagnitudeConjecture.Graded.IdempotentProjective

/-! # The corner-space description of graded projective morphisms -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))

/-- The degree-d part of eAf, written by its two idempotent equations. -/
def cornerComponent (e f : A) (d : ℤ) : Submodule k A where
  carrier := {a | a ∈ R.component d ∧ e * a = a ∧ a * f = a}
  zero_mem' := ⟨(R.component d).zero_mem, mul_zero e, zero_mul f⟩
  add_mem' := fun hx hy ↦ ⟨(R.component d).add_mem hx.1 hy.1, by
    rw [mul_add, hx.2.1, hy.2.1], by rw [add_mul, hx.2.2, hy.2.2]⟩
  smul_mem' := fun c a ha ↦ ⟨(R.component d).smul_mem c ha.1, by
    rw [mul_smul_comm, ha.2.1], by rw [smul_mul_assoc, ha.2.2]⟩

variable [FiniteDimensional k A]

/-- The e-coordinate of Af is precisely the corner eAf, degree by degree. -/
def principalCoordinateEquiv (e f : A) (hf : f * f = f) (hf0 : f ∈ R.component 0) (d : ℤ) :
    idempotentComponent R (principalProjectiveGrading R hmul f hf0) e d ≃ₗ[k]
      cornerComponent R e f d where
  toFun x := ⟨x.val.val, x.property.1, congrArg Subtype.val x.property.2,
    principal_fixed hf x.val⟩
  invFun a := ⟨⟨a.val, ⟨a.val, a.property.2.2⟩⟩, a.property.1,
    Subtype.ext a.property.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Homogeneous module maps Ae → Af identify with the expected homogeneous corner. -/
def principalCornerHomEquiv (e f : A) (he : e * e = e) (hf : f * f = f)
    (he0 : e ∈ R.component 0) (hf0 : f ∈ R.component 0) (d : ℤ) :
    (principalProjectiveGrading R hmul e he0).homComponent
      (principalProjectiveGrading R hmul f hf0) d ≃ₗ[k] cornerComponent R e f d :=
  (principalHomEquiv R hmul (principalProjectiveGrading R hmul f hf0) e he he0 d).trans
    (principalCoordinateEquiv R hmul e f hf hf0 d)

/-- Maps from Ae are determined on every vector by their value at e. -/
theorem principal_apply {M : Type*} [AddCommGroup M] [Module A M]
    (e : A) (he : e * e = e) (f : principalProjective e →ₗ[A] M)
    (z : principalProjective e) : f z = z.val • f (principalGenerator e) := by
  rw [← f.map_smul]
  congr 1
  apply Subtype.ext
  exact (principal_fixed he z).symm

/-- Composition of projective maps is multiplication of their corner coordinates. -/
theorem principal_comp_evaluation (e f g : A) (hf : f * f = f)
    (a : principalProjective e →ₗ[A] principalProjective f)
    (b : principalProjective f →ₗ[A] principalProjective g) :
    (b (a (principalGenerator e))).val =
      (a (principalGenerator e)).val * (b (principalGenerator f)).val := by
  have h := principal_apply f hf b (a (principalGenerator e))
  exact congrArg Subtype.val h

end MagnitudeConjecture.Graded
