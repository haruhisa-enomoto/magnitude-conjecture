import MagnitudeConjecture.Combinatorics.FiniteWindowOrbitQuotient
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Finite interaction neighborhoods

The covering argument enlarges a finite seed window three times by adjoining
all objects having a nonzero Hom in either direction with an object already
present.  This file isolates the relation-theoretic content of that
construction.  Locally finite interaction neighborhoods remain finite under
iteration, and an invariant interaction relation makes every iterated window
equivariant under the deck-group action.  The resulting three-step window can
therefore be passed directly to finite residual quotient separation.
-/

set_option autoImplicit false

open scoped Pointwise

namespace MagnitudeConjecture.CoveringSeparation

universe u v w

variable {X : Type v}

/-- Enlarge a set by taking every point interacting with one of its points. -/
def interactionNeighborhood (R : X → X → Prop) (W : Set X) : Set X :=
  {y | ∃ x ∈ W, R x y}

@[simp]
theorem mem_interactionNeighborhood_iff
    (R : X → X → Prop) (W : Set X) (y : X) :
    y ∈ interactionNeighborhood R W ↔ ∃ x ∈ W, R x y :=
  Iff.rfl

/-- A reflexive interaction relation makes each window lie in its first
enlargement. -/
theorem subset_interactionNeighborhood
    (R : X → X → Prop) (reflexive : ∀ x : X, R x x) (W : Set X) :
    W ⊆ interactionNeighborhood R W := by
  intro x hx
  exact ⟨x, hx, reflexive x⟩

/-- Interaction-neighborhood enlargement is monotone in the seed set. -/
theorem interactionNeighborhood_mono
    (R : X → X → Prop) :
    Monotone (interactionNeighborhood R) := by
  intro U W hUW y
  rintro ⟨x, hx, hxy⟩
  exact ⟨x, hUW hx, hxy⟩

/-- A finite set has finite interaction neighborhood when every point has only
finitely many interaction neighbors. -/
theorem interactionNeighborhood_finite
    (R : X → X → Prop)
    (locallyFinite : ∀ x : X, {y : X | R x y}.Finite)
    (W : Set X) (hW : W.Finite) :
    (interactionNeighborhood R W).Finite := by
  apply (hW.biUnion fun x _ ↦ locallyFinite x).subset
  intro y
  rintro ⟨x, hx, hxy⟩
  exact Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx hxy)

/-- Iteration of interaction-neighborhood enlargement.  In the manuscript,
`iterateInteractionNeighborhood R i U₀` is the control window `Uᵢ`. -/
def iterateInteractionNeighborhood (R : X → X → Prop) :
    ℕ → Set X → Set X
  | 0, W => W
  | n + 1, W =>
      interactionNeighborhood R (iterateInteractionNeighborhood R n W)

@[simp]
theorem iterateInteractionNeighborhood_zero
    (R : X → X → Prop) (W : Set X) :
    iterateInteractionNeighborhood R 0 W = W :=
  rfl

@[simp]
theorem iterateInteractionNeighborhood_succ
    (R : X → X → Prop) (n : ℕ) (W : Set X) :
    iterateInteractionNeighborhood R (n + 1) W =
      interactionNeighborhood R (iterateInteractionNeighborhood R n W) :=
  rfl

/-- Every finite seed has finite iterated neighborhoods. -/
theorem iterateInteractionNeighborhood_finite
    (R : X → X → Prop)
    (locallyFinite : ∀ x : X, {y : X | R x y}.Finite)
    (W : Set X) (hW : W.Finite) :
    ∀ n : ℕ, (iterateInteractionNeighborhood R n W).Finite
  | 0 => hW
  | n + 1 => interactionNeighborhood_finite R locallyFinite _
      (iterateInteractionNeighborhood_finite R locallyFinite W hW n)

/-- For a reflexive relation the control windows form an increasing sequence. -/
theorem iterateInteractionNeighborhood_subset_succ
    (R : X → X → Prop) (reflexive : ∀ x : X, R x x)
    (W : Set X) (n : ℕ) :
    iterateInteractionNeighborhood R n W ⊆
      iterateInteractionNeighborhood R (n + 1) W :=
  subset_interactionNeighborhood R reflexive _

variable {G : Type u} [Group G] [MulAction G X]

/-- Invariance of the interaction relation makes one neighborhood enlargement
commute with the group action. -/
theorem interactionNeighborhood_smul
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (g : G) (W : Set X) :
    interactionNeighborhood R (g • W) =
      g • interactionNeighborhood R W := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
    exact ⟨g⁻¹ • x, hx, (invariant g⁻¹ x y).mpr hxy⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨g • x, ?_, ?_⟩
    · exact Set.smul_mem_smul_set hx
    · have := (invariant g x (g⁻¹ • y)).mpr hxy
      simpa only [smul_smul, mul_inv_cancel, one_smul] using this

/-- Every iterated control window commutes with the group action. -/
theorem iterateInteractionNeighborhood_smul
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (g : G) (W : Set X) :
    ∀ n : ℕ,
      iterateInteractionNeighborhood R n (g • W) =
        g • iterateInteractionNeighborhood R n W
  | 0 => rfl
  | n + 1 => by
      change
        interactionNeighborhood R
            (iterateInteractionNeighborhood R n (g • W)) =
          g • interactionNeighborhood R
            (iterateInteractionNeighborhood R n W)
      rw [iterateInteractionNeighborhood_smul R invariant g W n,
        interactionNeighborhood_smul R invariant]

/-- The manuscript's control window after three successive Hom-neighborhood
enlargements. -/
def threeStepControlWindow (R : X → X → Prop) (W : Set X) : Set X :=
  iterateInteractionNeighborhood R 3 W

/-- The three-step control window of a finite seed is finite. -/
theorem threeStepControlWindow_finite
    (R : X → X → Prop)
    (locallyFinite : ∀ x : X, {y : X | R x y}.Finite)
    (W : Set X) (hW : W.Finite) :
    (threeStepControlWindow R W).Finite :=
  iterateInteractionNeighborhood_finite R locallyFinite W hW 3

/-- The three-step control-window construction is equivariant. -/
theorem threeStepControlWindow_smul
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (g : G) (W : Set X) :
    threeStepControlWindow R (g • W) =
      g • threeStepControlWindow R W :=
  iterateInteractionNeighborhood_smul R invariant g W 3

/-- Residual finiteness produces a finite quotient that embeds and preserves
all interactions in the manuscript's finite three-step control window. -/
theorem exists_finiteIndexNormalSubgroup_preserving_threeStepControlWindow
    [Group.ResiduallyFinite G]
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (reflexive : ∀ x : X, R x x)
    (neighborsFinite : ∀ x : X, {y : X | R x y}.Finite)
    (translationsFinite : ∀ x y : X, {g : G | R x (g • y)}.Finite)
    (W : Set X) (hW : W.Finite) :
    ∃ N : FiniteIndexNormalSubgroup G,
      Set.InjOn
          (fun x : X ↦
            (Quotient.mk'' x : MulAction.orbitRel.Quotient N X))
          (threeStepControlWindow R W) ∧
        ∀ ⦃x y : X⦄,
          x ∈ threeStepControlWindow R W →
          y ∈ threeStepControlWindow R W →
          (OrbitQuotientInteracts (N : Subgroup G) R
              (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)
              (Quotient.mk'' y : MulAction.orbitRel.Quotient N X) ↔
            R x y) :=
  exists_finiteIndexNormalSubgroup_preserving_window R invariant reflexive
    (threeStepControlWindow R W)
    (threeStepControlWindow_finite R neighborsFinite W hW)
    translationsFinite

variable {O : Type w} [MulAction G O] [IsCancelSMul G O]

/-- Finite equivariant supports discharge the translate-finiteness hypothesis
for separation of the three-step window. -/
theorem
    exists_finiteIndexNormalSubgroup_preserving_threeStepControlWindow_of_finite_support
    [Group.ResiduallyFinite G]
    (support : X → Set O)
    (support_finite : ∀ x, (support x).Finite)
    (support_smul : ∀ (g : G) (x : X) (o : O),
      o ∈ support (g • x) ↔ g⁻¹ • o ∈ support x)
    (R : X → X → Prop)
    (invariant : ∀ (g : G) (x y : X), R (g • x) (g • y) ↔ R x y)
    (reflexive : ∀ x : X, R x x)
    (neighborsFinite : ∀ x : X, {y : X | R x y}.Finite)
    (interaction_meets_support : ∀ {x y}, R x y →
      ∃ o, o ∈ support x ∧ o ∈ support y)
    (W : Set X) (hW : W.Finite) :
    ∃ N : FiniteIndexNormalSubgroup G,
      Set.InjOn
          (fun x : X ↦
            (Quotient.mk'' x : MulAction.orbitRel.Quotient N X))
          (threeStepControlWindow R W) ∧
        ∀ ⦃x y : X⦄,
          x ∈ threeStepControlWindow R W →
          y ∈ threeStepControlWindow R W →
          (OrbitQuotientInteracts (N : Subgroup G) R
              (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)
              (Quotient.mk'' y : MulAction.orbitRel.Quotient N X) ↔
            R x y) := by
  apply exists_finiteIndexNormalSubgroup_preserving_threeStepControlWindow
    R invariant reflexive neighborsFinite _ W hW
  exact interactionTranslations_finite_of_finite_support support support_finite
    support_smul R interaction_meets_support

end MagnitudeConjecture.CoveringSeparation
