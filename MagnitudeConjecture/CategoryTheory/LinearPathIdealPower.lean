import MagnitudeConjecture.CategoryTheory.LinearPathLift
import QuotientSubmoduleEquidistribution.CategoryTheory.HomIdealPowers

/-!
# Path evaluation and powers of a Hom ideal

Evaluating a path whose displayed arrows lie in a two-sided Hom ideal gives a
morphism in the power indexed by the path length.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.LinearPathCategory

open QuotientSubmoduleEquidistribution.CategoricalIdeal

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {C : Type z} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]

/-- Evaluating a path whose arrows lie in a Hom ideal gives a morphism in
the ideal power indexed by the path length. -/
theorem pathMap_mem_ideal_pow
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (I : HomIdeal C)
    (hF₁ : ∀ {i j : Q} (a : i ⟶ j), F₁ a ∈ I.hom (F₀ j) (F₀ i))
    {x y : Q} (p : Quiver.Path x y) :
    pathMap F₀ F₁ p ∈ (I.pow p.length).hom (F₀ y) (F₀ x) := by
  induction p with
  | nil =>
      change True
      trivial
  | cons p a ih =>
      rw [pathMap_cons, Quiver.Path.length_cons,
        HomIdeal.pow_succ_eq_mul_pow]
      exact HomIdeal.comp_mem_mul (hF₁ a) ih

end MagnitudeConjecture.LinearPathCategory
