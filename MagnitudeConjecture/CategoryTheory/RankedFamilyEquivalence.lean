import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Transporting strict descent of a family through an additive equivalence -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CategoryTheory
universe u v u' v' w
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable (E : C ≌ D) [E.functor.Additive]
variable {ι : Type w} (F : ι → D) (rank : ι → ℤ)

/-- Strict descent of nonzero nonisomorphisms is invariant under an additive equivalence. -/
theorem ranked_family_of_equivalence
    (hF : ∀ i j, ∀ f : F i ⟶ F j, f ≠ 0 → ¬ IsIso f → rank j < rank i)
    (i j : ι) (f : E.inverse.obj (F i) ⟶ E.inverse.obj (F j))
    (hf : f ≠ 0) (hi : ¬ IsIso f) : rank j < rank i := by
  let ei := E.counitIso.app (F i)
  let ej := E.counitIso.app (F j)
  let g : F i ⟶ F j := ei.inv ≫ E.functor.map f ≫ ej.hom
  have hmap : E.functor.map f = ei.hom ≫ g ≫ ej.inv := by simp [g]
  apply hF i j g
  · intro hg
    apply hf
    apply E.functor.map_injective
    rw [E.functor.map_zero, hmap, hg]
    simp
  · intro hg
    letI : IsIso g := hg
    haveI : IsIso (E.functor.map f) := by rw [hmap]; infer_instance
    exact hi (isIso_of_reflects_iso f E.functor)

end MagnitudeConjecture.CategoryTheory
