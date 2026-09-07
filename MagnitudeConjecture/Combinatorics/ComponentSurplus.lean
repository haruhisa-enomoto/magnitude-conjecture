import MagnitudeConjecture.Combinatorics.EulerSurplus
import Mathlib.Data.Fintype.Sigma

/-!
# Additivity of Auslander--Reiten surplus across components

If a finite Auslander--Reiten multigraph is partitioned into pieces and no
arrow crosses the partition, then its surplus is the sum of the surpluses of
the induced pieces.  This is the numerical component-additivity used by the
frozen manuscript both in the induction and in the equality case.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.ARCount

universe u v

variable {ι : Type u} [Fintype ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]

/-- Restrict an arrow-multiplicity function to one fibre of a component map. -/
abbrev componentArrowMultiplicity
    (arrowMultiplicity : ι → ι → ℕ) (component : ι → κ) (c : κ) :
    {x : ι // component x = c} → {x : ι // component x = c} → ℕ :=
  fun x y ↦ arrowMultiplicity x.1 y.1

/-- Restrict the projective predicate to one fibre of a component map. -/
abbrev componentIsProjective
    (IsProjective : ι → Prop) (component : ι → κ) (c : κ) :
    {x : ι // component x = c} → Prop :=
  fun x ↦ IsProjective x.1

omit [Fintype κ] in
/-- When arrows do not cross components, the indegree computed in one fibre
is the ambient indegree. -/
theorem component_indegree_eq
    (arrowMultiplicity : ι → ι → ℕ)
    (component : ι → κ)
    (hcross : ∀ x y, component x ≠ component y → arrowMultiplicity x y = 0)
    (c : κ) (y : {x : ι // component x = c}) :
    indegree (componentArrowMultiplicity arrowMultiplicity component c) y =
      indegree arrowMultiplicity y.1 := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun x : ι ↦ component x = c)
    (fun x ↦ (arrowMultiplicity x y.1 : ℤ))
  have hzero :
      (∑ x : {x : ι // ¬ component x = c},
        (arrowMultiplicity x.1 y.1 : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hcross x.1 y.1]
    · rfl
    · intro hxy
      exact x.2 (hxy.trans y.2)
  change (∑ x : {x : ι // component x = c},
      (arrowMultiplicity x.1 y.1 : ℤ)) =
    ∑ x : ι, (arrowMultiplicity x y.1 : ℤ)
  calc
    (∑ x : {x : ι // component x = c},
        (arrowMultiplicity x.1 y.1 : ℤ)) =
        (∑ x : {x : ι // component x = c},
          (arrowMultiplicity x.1 y.1 : ℤ)) +
          ∑ x : {x : ι // ¬ component x = c},
            (arrowMultiplicity x.1 y.1 : ℤ) := by rw [hzero, add_zero]
    _ = ∑ x : ι, (arrowMultiplicity x y.1 : ℤ) := hsplit

omit [Fintype κ] in
/-- When arrows do not cross components, local density computed in one fibre
is the ambient local density. -/
theorem component_localDensity_eq
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (component : ι → κ)
    (hcross : ∀ x y, component x ≠ component y → arrowMultiplicity x y = 0)
    (c : κ) (y : {x : ι // component x = c}) :
    localDensity (componentArrowMultiplicity arrowMultiplicity component c)
        (componentIsProjective IsProjective component c) y =
      localDensity arrowMultiplicity IsProjective y.1 := by
  classical
  rw [localDensity, localDensity,
    component_indegree_eq arrowMultiplicity component hcross c y]

/-- Frozen manuscript, component additivity of surplus: a partition with no
crossing arrows decomposes the ambient surplus into the sum of the induced
component surpluses. -/
theorem surplus_eq_sum_componentSurplus
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (component : ι → κ)
    (hcross : ∀ x y, component x ≠ component y → arrowMultiplicity x y = 0) :
    surplus arrowMultiplicity IsProjective =
      ∑ c : κ,
        surplus (componentArrowMultiplicity arrowMultiplicity component c)
          (componentIsProjective IsProjective component c) := by
  classical
  rw [← sum_localDensity_eq_surplus arrowMultiplicity IsProjective]
  simp_rw [← sum_localDensity_eq_surplus]
  let e : (Σ c : κ, {x : ι // component x = c}) ≃ ι :=
    Equiv.sigmaFiberEquiv component
  calc
    (∑ x : ι, localDensity arrowMultiplicity IsProjective x) =
        ∑ z : Σ c : κ, {x : ι // component x = c},
          localDensity arrowMultiplicity IsProjective z.2.1 := by
      symm
      exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = ∑ c : κ, ∑ x : {x : ι // component x = c},
          localDensity arrowMultiplicity IsProjective x.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ c : κ, ∑ x : {x : ι // component x = c},
          localDensity
            (componentArrowMultiplicity arrowMultiplicity component c)
            (componentIsProjective IsProjective component c) x := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro x hx
      exact (component_localDensity_eq arrowMultiplicity IsProjective
        component hcross c x).symm

/-- Nonnegative surplus on every component implies nonnegative ambient
surplus. -/
theorem surplus_nonnegative_of_componentSurplus_nonnegative
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (component : ι → κ)
    (hcross : ∀ x y, component x ≠ component y → arrowMultiplicity x y = 0)
    (hcomponent : ∀ c : κ, 0 ≤
      surplus (componentArrowMultiplicity arrowMultiplicity component c)
        (componentIsProjective IsProjective component c)) :
    0 ≤ surplus arrowMultiplicity IsProjective := by
  rw [surplus_eq_sum_componentSurplus arrowMultiplicity IsProjective
    component hcross]
  exact Finset.sum_nonneg fun c _ ↦ hcomponent c

/-- If every component surplus is nonnegative and the ambient surplus
vanishes, then the surplus of any chosen component vanishes. -/
theorem componentSurplus_eq_zero_of_surplus_eq_zero
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (component : ι → κ)
    (hcross : ∀ x y, component x ≠ component y → arrowMultiplicity x y = 0)
    (hcomponent : ∀ c : κ, 0 ≤
      surplus (componentArrowMultiplicity arrowMultiplicity component c)
        (componentIsProjective IsProjective component c))
    (hzero : surplus arrowMultiplicity IsProjective = 0)
    (c : κ) :
    surplus (componentArrowMultiplicity arrowMultiplicity component c)
      (componentIsProjective IsProjective component c) = 0 := by
  classical
  let f : κ → ℤ := fun d ↦
    surplus (componentArrowMultiplicity arrowMultiplicity component d)
      (componentIsProjective IsProjective component d)
  have hsum : ∑ d : κ, f d = 0 := by
    rw [← surplus_eq_sum_componentSurplus arrowMultiplicity IsProjective
      component hcross]
    exact hzero
  have hle : f c ≤ ∑ d : κ, f d := by
    apply Finset.single_le_sum
    · intro d hd
      exact hcomponent d
    · exact Finset.mem_univ c
  exact le_antisymm (by simpa [hsum] using hle) (hcomponent c)

/-- Under componentwise nonnegativity, ambient equality is equivalent to
equality on every component. -/
theorem surplus_eq_zero_iff_componentSurplus_eq_zero
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (component : ι → κ)
    (hcross : ∀ x y, component x ≠ component y → arrowMultiplicity x y = 0)
    (hcomponent : ∀ c : κ, 0 ≤
      surplus (componentArrowMultiplicity arrowMultiplicity component c)
        (componentIsProjective IsProjective component c)) :
    surplus arrowMultiplicity IsProjective = 0 ↔
      ∀ c : κ,
        surplus (componentArrowMultiplicity arrowMultiplicity component c)
          (componentIsProjective IsProjective component c) = 0 := by
  constructor
  · intro hzero c
    exact componentSurplus_eq_zero_of_surplus_eq_zero arrowMultiplicity
      IsProjective component hcross hcomponent hzero c
  · intro hzero
    rw [surplus_eq_sum_componentSurplus arrowMultiplicity IsProjective
      component hcross]
    exact Finset.sum_eq_zero fun c _ ↦ hzero c

end MagnitudeConjecture.ARCount
