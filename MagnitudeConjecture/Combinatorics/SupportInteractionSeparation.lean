import MagnitudeConjecture.Combinatorics.ResidualFiniteSeparation

/-!
# Separating finite-support interactions

For objects with finite support over a freely acted-on base, an interaction
that forces the two supports to meet can occur for only finitely many
translations.  Combined with residual finiteness, this supplies the finite
window separation mechanism used for modules over the universal cover.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.CoveringSeparation

universe u v w

variable {G : Type u} [Group G]
variable {O : Type v} [MulAction G O] [IsCancelSMul G O]
variable {X : Type w} [MulAction G X]

/-- Under a free action, the set of group elements carrying one specified
base object to another is finite (indeed, subsingleton). -/
theorem smulTransporter_finite (source target : O) :
    {g : G | g • source = target}.Finite := by
  apply Set.Subsingleton.finite
  intro g hg h hh
  exact IsCancelSMul.right_cancel g h source (hg.trans hh.symm)

/-- Finite equivariant supports turn support-detectable interactions into
pointwise finite sets of translations. -/
theorem interactionTranslations_finite_of_finite_support
    (support : X → Set O)
    (support_finite : ∀ x, (support x).Finite)
    (support_smul : ∀ (g : G) (x : X) (o : O),
      o ∈ support (g • x) ↔ g⁻¹ • o ∈ support x)
    (R : X → X → Prop)
    (interaction_meets_support : ∀ {x y}, R x y →
      ∃ o, o ∈ support x ∧ o ∈ support y)
    (x y : X) :
    {g : G | R x (g • y)}.Finite := by
  classical
  let sourceSupport : Finset O := (support_finite x).toFinset
  let targetSupport : Finset O := (support_finite y).toFinset
  let bound : Finset G :=
    sourceSupport.biUnion fun target ↦
      targetSupport.biUnion fun source ↦
        (smulTransporter_finite (G := G) source target).toFinset
  apply bound.finite_toSet.subset
  intro g hg
  change R x (g • y) at hg
  obtain ⟨target, htargetX, htargetGY⟩ := interaction_meets_support hg
  let source : O := g⁻¹ • target
  have hsourceY : source ∈ support y :=
    (support_smul g y target).mp htargetGY
  have htranslate : g • source = target := by
    simp [source]
  change g ∈ bound
  apply Finset.mem_biUnion.mpr
  refine ⟨target, (support_finite x).mem_toFinset.mpr htargetX, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨source, (support_finite y).mem_toFinset.mpr hsourceY, ?_⟩
  exact (smulTransporter_finite (G := G) source target).mem_toFinset.mpr
    htranslate

/-- Residual finiteness separates a finite window whenever interaction is
detected by meeting finite equivariant supports over a freely acted-on base. -/
theorem exists_finiteIndexNormalSubgroup_pairwise_windowSeparated_of_finite_support
    [Group.ResiduallyFinite G]
    (support : X → Set O)
    (support_finite : ∀ x, (support x).Finite)
    (support_smul : ∀ (g : G) (x : X) (o : O),
      o ∈ support (g • x) ↔ g⁻¹ • o ∈ support x)
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (interaction_meets_support : ∀ {x y}, R x y →
      ∃ o, o ∈ support x ∧ o ∈ support y)
    (W : Set X) (hW : W.Finite) :
    ∃ N : FiniteIndexNormalSubgroup G,
      ∀ ⦃n₁ n₂ : G⦄, n₁ ∈ N → n₂ ∈ N → n₁ ≠ n₂ →
        ∀ ⦃x y : X⦄, x ∈ W → y ∈ W → ¬ R (n₁ • x) (n₂ • y) :=
  exists_finiteIndexNormalSubgroup_pairwise_windowSeparated_of_localFinite
    R invariant W hW
      (interactionTranslations_finite_of_finite_support support support_finite
        support_smul R interaction_meets_support)

end MagnitudeConjecture.CoveringSeparation
