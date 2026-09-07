import MagnitudeConjecture.Combinatorics.OrbitQuotientAction
import MagnitudeConjecture.Combinatorics.SupportInteractionSeparation

/-!
# Finite control windows in orbit quotients

Once residual finiteness has separated distinct subgroup translates of a
finite control window, passage to the subgroup-orbit quotient is faithful on
that window: its points remain distinct and the quotient creates no new
instances of the chosen interaction relation.  This is the set-theoretic
locality statement used before transporting vertices, arrows, and meshes in
the covering argument.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.CoveringSeparation

universe u v w

variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X]

/-- Two subgroup-orbits interact when some representatives interact.  This
definition is representative-free and does not require the relation to be
invariant under translating its two variables independently. -/
def OrbitQuotientInteracts (N : Subgroup G) (R : X → X → Prop)
    (x y : MulAction.orbitRel.Quotient N X) : Prop :=
  ∃ x' ∈ x.orbit, ∃ y' ∈ y.orbit, R x' y'

/-- A window whose distinct subgroup translates are interaction-free has
exactly its original interaction relation after passing to subgroup-orbits.
-/
theorem orbitQuotientInteracts_mk_iff_of_pairwise_windowSeparated
    (N : Subgroup G) (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (W : Set X)
    (separated :
      ∀ ⦃n₁ n₂ : G⦄, n₁ ∈ N → n₂ ∈ N → n₁ ≠ n₂ →
        ∀ ⦃x y : X⦄, x ∈ W → y ∈ W → ¬ R (n₁ • x) (n₂ • y))
    {x y : X} (hx : x ∈ W) (hy : y ∈ W) :
    OrbitQuotientInteracts N R
        (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)
        (Quotient.mk'' y : MulAction.orbitRel.Quotient N X) ↔
      R x y := by
  constructor
  · rintro ⟨x', hx', y', hy', hxy⟩
    rw [MulAction.orbitRel.Quotient.orbit_mk,
      MulAction.mem_orbit_iff] at hx' hy'
    obtain ⟨n₁, rfl⟩ := hx'
    obtain ⟨n₂, rfl⟩ := hy'
    by_cases hn : (n₁ : G) = n₂
    · have hn' : n₁ = n₂ := Subtype.ext hn
      subst n₂
      exact (invariant n₁ x y).mp hxy
    · exact (separated n₁.property n₂.property hn hx hy hxy).elim
  · intro hxy
    refine ⟨x, ?_, y, ?_, hxy⟩
    · rw [MulAction.orbitRel.Quotient.orbit_mk]
      exact MulAction.mem_orbit_self x
    · rw [MulAction.orbitRel.Quotient.orbit_mk]
      exact MulAction.mem_orbit_self y

/-- If the separated relation contains equality, the orbit map is injective
on the control window. -/
theorem orbitQuotient_mk_injOn_of_pairwise_windowSeparated
    (N : Subgroup G) (R : X → X → Prop)
    (reflexive : ∀ x : X, R x x)
    (W : Set X)
    (separated :
      ∀ ⦃n₁ n₂ : G⦄, n₁ ∈ N → n₂ ∈ N → n₁ ≠ n₂ →
        ∀ ⦃x y : X⦄, x ∈ W → y ∈ W → ¬ R (n₁ • x) (n₂ • y)) :
    Set.InjOn
      (fun x : X ↦
        (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)) W := by
  intro x hx y hy hxy
  rw [Quotient.eq'', MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff] at hxy
  obtain ⟨n, hn⟩ := hxy
  by_cases hnOne : (n : G) = 1
  · change (n : G) • y = x at hn
    rw [hnOne, one_smul] at hn
    exact hn.symm
  · exfalso
    apply separated n.property N.one_mem hnOne hy hx
    have hnG : (n : G) • y = x := by
      simpa only [MulAction.subgroup_smul_def] using hn
    change R ((n : G) • y) ((1 : G) • x)
    rw [hnG, one_smul]
    exact reflexive x

/-- Residual separation simultaneously embeds a finite window in a finite
index subgroup quotient and preserves its interaction relation there. -/
theorem exists_finiteIndexNormalSubgroup_preserving_window
    [Group.ResiduallyFinite G]
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (reflexive : ∀ x : X, R x x)
    (W : Set X) (hW : W.Finite)
    (locallyFinite : ∀ x y : X, {g : G | R x (g • y)}.Finite) :
    ∃ N : FiniteIndexNormalSubgroup G,
      Set.InjOn
          (fun x : X ↦
            (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)) W ∧
        ∀ ⦃x y : X⦄, x ∈ W → y ∈ W →
          (OrbitQuotientInteracts (N : Subgroup G) R
              (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)
              (Quotient.mk'' y : MulAction.orbitRel.Quotient N X) ↔
            R x y) := by
  obtain ⟨N, hN⟩ :=
    exists_finiteIndexNormalSubgroup_pairwise_windowSeparated_of_localFinite
      R invariant W hW locallyFinite
  refine ⟨N,
    orbitQuotient_mk_injOn_of_pairwise_windowSeparated
      (N : Subgroup G) R reflexive W hN,
    ?_⟩
  intro x y hx hy
  exact orbitQuotientInteracts_mk_iff_of_pairwise_windowSeparated
    (N : Subgroup G) R invariant W hN hx hy

variable {O : Type w} [MulAction G O] [IsCancelSMul G O]

/-- Finite equivariant supports and support-detectable interactions supply the
finite quotient preserving a finite control window. -/
theorem exists_finiteIndexNormalSubgroup_preserving_window_of_finite_support
    [Group.ResiduallyFinite G]
    (support : X → Set O)
    (support_finite : ∀ x, (support x).Finite)
    (support_smul : ∀ (g : G) (x : X) (o : O),
      o ∈ support (g • x) ↔ g⁻¹ • o ∈ support x)
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (reflexive : ∀ x : X, R x x)
    (interaction_meets_support : ∀ {x y}, R x y →
      ∃ o, o ∈ support x ∧ o ∈ support y)
    (W : Set X) (hW : W.Finite) :
    ∃ N : FiniteIndexNormalSubgroup G,
      Set.InjOn
          (fun x : X ↦
            (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)) W ∧
        ∀ ⦃x y : X⦄, x ∈ W → y ∈ W →
          (OrbitQuotientInteracts (N : Subgroup G) R
              (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)
              (Quotient.mk'' y : MulAction.orbitRel.Quotient N X) ↔
            R x y) := by
  apply exists_finiteIndexNormalSubgroup_preserving_window R invariant
    reflexive W hW
  exact interactionTranslations_finite_of_finite_support support support_finite
    support_smul R interaction_meets_support

end MagnitudeConjecture.CoveringSeparation
