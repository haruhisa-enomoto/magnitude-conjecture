import MagnitudeConjecture.CategoryTheory.GradedIntervalActionCoefficients

/-! # The algebra action reconstructed from an interval representation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type v} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable (F : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k)
variable [F.Additive] [F.Linear k]

/-- The underlying vector space assembled from all coordinates in [0,m]. -/
abbrev intervalCoordinateSpace (m : ℕ) :=
  ∀ p : ι × Fin (m + 1), F.obj (op (intervalProjectiveLabel R hmul e he0 m p))

/-- An algebra element acts through its matrix of homogeneous projective morphisms. -/
def intervalActionMap (m : ℕ) (a : A) :
    intervalCoordinateSpace R hmul e he0 F m →ₗ[k] intervalCoordinateSpace R hmul e he0 F m where
  toFun x p := ∑ q, (F.map (intervalActionCoefficient R hmul e he0 he m p q a).op).hom (x q)
  map_add' x y := by
    funext p
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext p
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- The reconstructed action is linear in the algebra element as well. -/
def intervalActionLinear (m : ℕ) :
    A →ₗ[k] Module.End k (intervalCoordinateSpace R hmul e he0 F m) where
  toFun := intervalActionMap R hmul e he0 he F m
  map_add' a b := by
    apply LinearMap.ext
    intro x
    funext p
    simp only [intervalActionMap, LinearMap.coe_mk, AddHom.coe_mk, map_add, op_add,
      F.map_add, ModuleCat.hom_add, LinearMap.add_apply, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    funext p
    simp only [intervalActionMap, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
      CoveringHom.opposite_op_smul, F.map_smul, ModuleCat.hom_smul,
      LinearMap.smul_apply, Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

/-- The interval action respects multiplication. -/
theorem intervalActionMap_mul (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (hsum : ∑ i, e i = 1) (m : ℕ) (a b : A) :
    intervalActionMap R hmul e he0 he F m (a * b) =
      (intervalActionMap R hmul e he0 he F m a).comp (intervalActionMap R hmul e he0 he F m b) := by
  apply LinearMap.ext
  intro x
  funext p
  change (∑ q, (F.map (intervalActionCoefficient R hmul e he0 he m p q (a * b)).op).hom (x q)) =
    ∑ z, (F.map (intervalActionCoefficient R hmul e he0 he m p z a).op).hom
      (∑ q, (F.map (intervalActionCoefficient R hmul e he0 he m z q b).op).hom (x q))
  simp only [intervalActionCoefficient_mul R hmul e he0 he hneg hsum, op_sum,
    Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, op_comp, F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, map_sum]
  exact Finset.sum_comm

/-- Orthogonal complete coordinates make the action of 1 the identity. -/
theorem intervalActionMap_one (h1 : (1 : A) ∈ R.component 0)
    (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ) :
    intervalActionMap R hmul e he0 he F m 1 = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  funext p
  change (∑ q, (F.map (intervalActionCoefficient R hmul e he0 he m p q 1).op).hom (x q)) = x p
  rw [Finset.sum_eq_single p]
  · rw [intervalActionCoefficient_one_self R hmul e he0 he h1 horth, op_id, F.map_id]
    rfl
  · intro q hq hqp
    rw [intervalActionCoefficient_one_ne R hmul e he0 he h1 horth m p q (Ne.symm hqp)]
    simp only [Limits.op_zero, F.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  · simp

/-- The reconstructed module action, packaged as an algebra homomorphism. -/
def intervalActionAlgHom (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
    (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ) :
    A →ₐ[k] Module.End k (intervalCoordinateSpace R hmul e he0 F m) :=
  AlgHom.ofLinearMap (intervalActionLinear R hmul e he0 he F m)
    (intervalActionMap_one R hmul e he0 he F h1 horth m)
    (intervalActionMap_mul R hmul e he0 he F hneg hsum m)

end MagnitudeConjecture.Graded.FiniteGradedModule
