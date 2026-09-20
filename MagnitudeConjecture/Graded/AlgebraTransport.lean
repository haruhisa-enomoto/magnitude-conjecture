import MagnitudeConjecture.Graded.ModuleMapComponents
import MagnitudeConjecture.Graded.EquivTransport

/-! # Transporting graded modules along algebra equivalences -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded
variable {k A B M : Type*} [Field k] [Ring A] [Ring B]
variable [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]

/-- Restriction along an algebra equivalence retains the original scalar tower. -/
def restrictedScalarTower (e : A ≃ₐ[k] B) :
    letI : Module A M := Module.compHom M e.toRingHom
    IsScalarTower k A M := by
  letI : Module A M := Module.compHom M e.toRingHom
  constructor
  intro c a x
  change e.toLinearEquiv (c • a) • x = c • (e.toLinearEquiv a • x)
  rw [e.toLinearEquiv.map_smul]
  exact smul_assoc c (e a) x

/-- The same homogeneous module components, with action restricted along the algebra equivalence. -/
def ModuleGrading.restrictAlgebra {R : VectorGrading k B} (G : ModuleGrading (M := M) R)
    (e : A ≃ₐ[k] B) :
    letI : Module A M := Module.compHom M e.toRingHom
    ModuleGrading (M := M) (R.comap e.toLinearEquiv) := by
  letI : Module A M := Module.compHom M e.toRingHom
  exact
    { toVectorGrading := G.toVectorGrading
      smul_mem := fun ha hx ↦ G.smul_mem ha hx }

/-- Existing module maps remain linear after transport of the algebra action. -/
def restrictAlgebraMap {N : Type*} [AddCommGroup N] [Module B N]
    (e : A ≃ₐ[k] B) (f : M →ₗ[B] N) :
    letI : Module A M := Module.compHom M e.toRingHom
    letI : Module A N := Module.compHom N e.toRingHom
    M →ₗ[A] N := by
  letI : Module A M := Module.compHom M e.toRingHom
  letI : Module A N := Module.compHom N e.toRingHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun a x ↦ f.map_smul (e a) x }

end MagnitudeConjecture.Graded
