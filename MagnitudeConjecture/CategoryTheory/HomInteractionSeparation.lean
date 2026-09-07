import MagnitudeConjecture.CategoryTheory.OrbitHomOrthogonality
import MagnitudeConjecture.Combinatorics.ResidualFiniteSeparation
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Hom interaction and translate orthogonality

The covering control relation joins equal objects and pairs carrying a
nonzero Hom in either direction.  Separation of distinct subgroup translates
for this relation makes every nonidentity translated Hom space vanish.  This
file connects the set-theoretic residual-separation theorem to the exact
`TranslateHomOrthogonal` input used by the orbit Hom formula.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringSeparation

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The symmetric Hom-neighborhood relation used in the manuscript's control
windows.  Equality is included so that the relation is reflexive even before
nonzeroness of the objects under consideration has been established. -/
def homInteraction (X Y : C) : Prop :=
  X = Y ∨ Nontrivial (X ⟶ Y) ∨ Nontrivial (Y ⟶ X)

@[simp]
theorem homInteraction_self (X : C) : homInteraction X X :=
  Or.inl rfl

theorem homInteraction_symm {X Y : C} :
    homInteraction X Y → homInteraction Y X := by
  rintro (hXY | hXY | hYX)
  · exact Or.inl hXY.symm
  · exact Or.inr (Or.inr hXY)
  · exact Or.inr (Or.inl hYX)

/-- Failure of Hom interaction forces the forward Hom space to vanish. -/
theorem hom_subsingleton_of_not_homInteraction
    {X Y : C} (h : ¬ homInteraction X Y) : Subsingleton (X ⟶ Y) :=
  not_nontrivial_iff_subsingleton.mp fun hnontrivial ↦
    h (Or.inr (Or.inl hnontrivial))

variable {k : Type w} [Semiring k]
variable [Preadditive C] [CategoryTheory.Linear k C]

variable {G : Type w} [Group G] [MulAction G C]

/-- The full subcategory on a set-valued control window. -/
abbrev WindowCategory (W : Set C) :=
  (show ObjectProperty C from fun X ↦ X ∈ W).FullSubcategory

/-- The translated ambient Hom family attached to two objects of a full
control-window subcategory and a subgroup of deck transformations. -/
abbrev windowTranslateHom (N : Subgroup G) (W : Set C)
    (X Y : WindowCategory W) (n : N) : Type v :=
  X.1 ⟶ (n : G) • Y.1

instance windowTranslateHomAddCommGroup (N : Subgroup G) (W : Set C)
    (X Y : WindowCategory W) (n : N) :
    AddCommGroup (windowTranslateHom N W X Y n) :=
  inferInstance

instance windowTranslateHomModule (N : Subgroup G) (W : Set C)
    (X Y : WindowCategory W) (n : N) :
    Module k (windowTranslateHom N W X Y n) :=
  inferInstance

/-- The identity translated Hom summand is linearly equivalent to the Hom
space of the full window subcategory. -/
noncomputable def windowIdentityHomLinearEquiv
    (N : Subgroup G) (W : Set C) (X Y : WindowCategory W) :
    (X ⟶ Y) ≃ₗ[k] windowTranslateHom N W X Y 1 := by
  exact
    (InducedCategory.homLinearEquiv (R := k)).trans
      (CategoryTheory.Linear.homCongr k (Iso.refl X.1)
        (eqToIso (by simp : ((1 : N) : G) • Y.1 = Y.1)).symm)

omit [Preadditive C] in
/-- Pairwise separation of subgroup translates for `homInteraction` gives
the exact nonidentity translate-Hom orthogonality used by the functor-level
Gabriel formula. -/
theorem windowTranslateHom_orthogonal_of_pairwise_windowSeparated
    (N : Subgroup G) (W : Set C)
    (separated :
      ∀ {n₁ n₂ : G}, n₁ ∈ N → n₂ ∈ N → n₁ ≠ n₂ →
        ∀ {X Y : C}, X ∈ W → Y ∈ W →
          ¬ homInteraction (n₁ • X) (n₂ • Y)) :
    CoveringHom.TranslateHomOrthogonal (windowTranslateHom N W) := by
  intro X Y n hn
  apply not_nontrivial_iff_subsingleton.mp
  intro hnontrivial
  have hne : (1 : G) ≠ (n : G) := by
    intro hone
    apply hn
    exact Subtype.ext hone.symm
  apply separated (n₁ := 1) (n₂ := (n : G))
    N.one_mem n.property hne X.property Y.property
  simpa only [one_smul] using
    (show homInteraction X.1 ((n : G) • Y.1) from
      Or.inr (Or.inl hnontrivial))

end MagnitudeConjecture.CoveringSeparation
