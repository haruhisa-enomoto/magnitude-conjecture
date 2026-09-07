import Mathlib.GroupTheory.ResiduallyFinite

/-!
# Residual separation of a finite control window

The covering argument first isolates a finite family of group elements whose
translates of a control window intersect or have a relevant morphism.  A
finite-index normal subgroup avoiding that family makes distinct subgroup
translates disjoint and interaction-free.  This file formalizes that exact
group-theoretic step, independently of the later covering-category model.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.CoveringSeparation

universe u v

variable {G : Type u} [Group G]

/-- Residual finiteness separates every member of a finite set from the
identity using one finite-index normal subgroup. -/
theorem exists_finiteIndexNormalSubgroup_avoiding_finset
    [Group.ResiduallyFinite G]
    (bad : Finset G) (hne : ∀ g ∈ bad, g ≠ 1) :
    ∃ N : FiniteIndexNormalSubgroup G, ∀ g ∈ bad, g ∉ N := by
  classical
  induction bad using Finset.induction_on with
  | empty =>
      let N : FiniteIndexNormalSubgroup G :=
        { toSubgroup := ⊤ }
      exact ⟨N, by simp⟩
  | @insert g bad hg ih =>
      obtain ⟨Ng, hNg⟩ :=
        Group.exists_finiteIndexNormalSubgroup_notMem g
          (hne g (Finset.mem_insert_self g bad))
      obtain ⟨Nbad, hNbad⟩ := ih (fun x hx ↦
        hne x (Finset.mem_insert_of_mem hx))
      refine ⟨Ng ⊓ Nbad, ?_⟩
      intro x hx hmem
      rw [Finset.mem_insert] at hx
      change x ∈ Ng ∧ x ∈ Nbad at hmem
      rcases hx with rfl | hx
      · exact hNg hmem.1
      · exact hNbad x hx hmem.2

/-- Set-valued form of simultaneous residual separation. -/
theorem exists_finiteIndexNormalSubgroup_avoiding
    [Group.ResiduallyFinite G]
    {bad : Set G} (hfinite : bad.Finite) (hne : ∀ g ∈ bad, g ≠ 1) :
    ∃ N : FiniteIndexNormalSubgroup G, ∀ g ∈ bad, g ∉ N := by
  classical
  obtain ⟨N, hN⟩ :=
    exists_finiteIndexNormalSubgroup_avoiding_finset hfinite.toFinset
      (fun g hg ↦ hne g (hfinite.mem_toFinset.mp hg))
  exact ⟨N, fun g hg ↦ hN g (hfinite.mem_toFinset.mpr hg)⟩

variable {X : Type v} [MulAction G X]

/-- A control window interacts with its `g`-translate when the chosen
relation holds between some point of the window and some translated point. -/
def WindowInteracts (R : X → X → Prop) (W : Set X) (g : G) : Prop :=
  ∃ x ∈ W, ∃ y ∈ W, R x (g • y)

/-- The nonidentity translations whose windows interact. -/
def badTranslations (R : X → X → Prop) (W : Set X) : Set G :=
  {g | g ≠ 1 ∧ WindowInteracts R W g}

/-- Pointwise finiteness of interacting translates makes the bad-translation
set of every finite window finite. -/
theorem badTranslations_finite
    (R : X → X → Prop) (W : Set X) (hW : W.Finite)
    (locallyFinite : ∀ x y : X,
      {g : G | R x (g • y)}.Finite) :
    (badTranslations (G := G) R W).Finite := by
  classical
  let Wf : Finset X := hW.toFinset
  let badBound : Finset G :=
    Wf.biUnion fun x ↦
      Wf.biUnion fun y ↦ (locallyFinite x y).toFinset
  apply badBound.finite_toSet.subset
  intro g hg
  change g ≠ 1 ∧ WindowInteracts (G := G) R W g at hg
  obtain ⟨_, x, hx, y, hy, hxy⟩ := hg
  change g ∈ badBound
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hW.mem_toFinset.mpr hx, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨y, hW.mem_toFinset.mpr hy,
    (locallyFinite x y).mem_toFinset.mpr hxy⟩

/-- If only finitely many nonidentity translations interact with a control
window, residual finiteness supplies a finite-index normal subgroup whose
distinct translates are pairwise interaction-free.

For the covering application, `R x y` means that `x = y` or that there is a
nonzero Hom in either direction. -/
theorem exists_finiteIndexNormalSubgroup_pairwise_windowSeparated
    [Group.ResiduallyFinite G]
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (W : Set X) (hbad : (badTranslations (G := G) R W).Finite) :
    ∃ N : FiniteIndexNormalSubgroup G,
      ∀ ⦃n₁ n₂ : G⦄, n₁ ∈ N → n₂ ∈ N → n₁ ≠ n₂ →
        ∀ ⦃x y : X⦄, x ∈ W → y ∈ W → ¬ R (n₁ • x) (n₂ • y) := by
  obtain ⟨N, hN⟩ := exists_finiteIndexNormalSubgroup_avoiding hbad
    (fun g hg ↦ hg.1)
  refine ⟨N, ?_⟩
  intro n₁ n₂ hn₁ hn₂ hn x y hx hy hxy
  let g : G := n₁⁻¹ * n₂
  have hgN : g ∈ N := N.mul_mem (N.inv_mem hn₁) hn₂
  have hgne : g ≠ 1 := by
    intro hg
    apply hn
    exact inv_mul_eq_one.mp hg
  have hinteracts : WindowInteracts (G := G) R W g := by
    refine ⟨x, hx, y, hy, ?_⟩
    have htranslated :=
      (invariant n₁⁻¹ (n₁ • x) (n₂ • y)).mpr hxy
    simpa only [smul_smul, inv_mul_cancel, one_smul, g] using htranslated
  exact hN g ⟨hgne, hinteracts⟩ hgN

/-- Local finiteness of interacting translates is the direct hypothesis used
in the covering proof to obtain a pairwise separated finite quotient. -/
theorem exists_finiteIndexNormalSubgroup_pairwise_windowSeparated_of_localFinite
    [Group.ResiduallyFinite G]
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (W : Set X) (hW : W.Finite)
    (locallyFinite : ∀ x y : X,
      {g : G | R x (g • y)}.Finite) :
    ∃ N : FiniteIndexNormalSubgroup G,
      ∀ ⦃n₁ n₂ : G⦄, n₁ ∈ N → n₂ ∈ N → n₁ ≠ n₂ →
        ∀ ⦃x y : X⦄, x ∈ W → y ∈ W → ¬ R (n₁ • x) (n₂ • y) :=
  exists_finiteIndexNormalSubgroup_pairwise_windowSeparated R invariant W
    (badTranslations_finite R W hW locallyFinite)

end MagnitudeConjecture.CoveringSeparation
