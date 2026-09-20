import MagnitudeConjecture.CategoryTheory.GradedIntervalReconstructionAction
import MagnitudeConjecture.Graded.CoordinateGrading
import MagnitudeConjecture.Graded.ModuleBundling
import MagnitudeConjecture.CategoryTheory.GradedSupportedCategory

/-! # The actual supported graded module reconstructed from interval coordinates -/
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
variable (horth : Pairwise fun i j ↦ e i * e j = 0)

/-- The reconstructed algebra module structure on the interval coordinate space. -/
def intervalReconstructedModule (m : ℕ) : Module A (intervalCoordinateSpace R hmul e he0 F m) :=
  Module.compHom _ (intervalActionAlgHom R hmul e he0 he F hneg h1 hsum horth m).toRingHom

/-- The reconstructed action agrees with the original field action. -/
def intervalReconstructedScalarTower (m : ℕ) :
    letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
    IsScalarTower k A (intervalCoordinateSpace R hmul e he0 F m) := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  constructor
  intro c a x
  change (intervalActionAlgHom R hmul e he0 he F hneg h1 hsum horth m (c • a)) x =
    c • (intervalActionAlgHom R hmul e he0 he F hneg h1 hsum horth m a) x
  rw [map_smul]
  rfl

/-- The degree labels grade the reconstructed algebra action. -/
def intervalReconstructedGrading (m : ℕ) :
    letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
    letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
    ModuleGrading (M := intervalCoordinateSpace R hmul e he0 F m) R := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
  refine
    { toVectorGrading := VectorGrading.coordinateGrading
        (fun p : ι × Fin (m + 1) ↦ F.obj (op (intervalProjectiveLabel R hmul e he0 m p)))
        (fun p ↦ (p.2.val : ℤ))
      smul_mem := ?_ }
  intro d n a x ha hx p hp
  change (p.2.val : ℤ) ≠ d + n at hp
  change (∑ q, (F.map (intervalActionCoefficient R hmul e he0 he m p q a).op).hom (x q)) = 0
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hqn : (q.2.val : ℤ) = n
  · have hdn : d ≠ (p.2.val : ℤ) - q.2.val := by omega
    have hc : intervalActionCoefficient R hmul e he0 he m p q a = 0 := by
      apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
      rw [map_zero]
      apply Subtype.ext
      rw [intervalActionCoefficient_coord]
      simp only [intervalCorner, R.projection_of_mem_ne ha hdn, mul_zero, zero_mul,
        ZeroMemClass.coe_zero]
    rw [hc]
    simp only [Limits.op_zero, F.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  · rw [hx q hqn, map_zero]

variable (hfinite : ∀ p, FiniteDimensional k (F.obj p))

/-- An actual finite-dimensional graded module reconstructed from the interval representation. -/
def intervalReconstructedObject (m : ℕ) : FiniteGradedModule.{u,u} R := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
  letI : ∀ p : ι × Fin (m + 1), FiniteDimensional k
      (F.obj (op (intervalProjectiveLabel R hmul e he0 m p))) := fun p ↦ hfinite _
  exact (intervalReconstructedGrading R hmul e he0 he F hneg h1 hsum horth m).toBundled

/-- No homogeneous component of the reconstructed module lies outside [0,m]. -/
theorem intervalReconstructed_supported (m : ℕ) : SupportedIn m
    (⟨intervalReconstructedObject R hmul e he0 he F hneg h1 hsum horth hfinite m, 0⟩ : ShiftedModule) := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  have hn := ((intervalReconstructedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).grading.toVectorGrading.mem_support_iff j).mp hj
  by_contra hout
  change ¬ (0 ≤ j + 0 ∧ j + 0 ≤ (m : ℤ)) at hout
  have ho : j < 0 ∨ (m : ℤ) < j := by omega
  apply hn
  apply bot_unique
  intro x hx
  change (x : intervalCoordinateSpace R hmul e he0 F m) = 0
  funext p
  apply hx p
  change (p.2.val : ℤ) ≠ j
  have hp := p.2.isLt
  omega

/-- The reconstructed object bundled in the supported graded category. -/
def intervalReconstructedSupportedObject (m : ℕ) : SupportedCategory (R := R) m :=
  ⟨⟨intervalReconstructedObject R hmul e he0 he F hneg h1 hsum horth hfinite m, 0⟩,
    intervalReconstructed_supported R hmul e he0 he F hneg h1 hsum horth hfinite m⟩

end MagnitudeConjecture.Graded.FiniteGradedModule
