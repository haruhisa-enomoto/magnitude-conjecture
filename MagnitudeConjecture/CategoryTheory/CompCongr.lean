import Mathlib.CategoryTheory.Category.Basic

/-!
# Small congruence lemmas for categorical composition
-/

set_option autoImplicit false

namespace MagnitudeConjecture

open CategoryTheory

universe v u

/-- Precomposition preserves equality of morphisms.  Naming this generic
operation prevents downstream elaboration from expanding a large concrete
morphism family inside `congrArg`. -/
theorem precomp_congr
    {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) {g h : Y ⟶ Z} (e : g = h) :
    f ≫ g = f ≫ h :=
  congrArg (fun t ↦ f ≫ t) e

/-- An equality of a two-step composite remains true after one further
precomposition, with reassociation performed generically. -/
theorem assoc_comp_congr
    {C : Type u} [Category.{v} C] {W X Y Z : C}
    (f : W ⟶ X) {g : X ⟶ Y} {h : Y ⟶ Z} {l : X ⟶ Z}
    (e : g ≫ h = l) :
    (f ≫ g) ≫ h = f ≫ l :=
  (Category.assoc _ _ _).trans (precomp_congr f e)

end MagnitudeConjecture
