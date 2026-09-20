import MagnitudeConjecture.CategoryTheory.HomogeneousRelationQuotient

/-! # Homogeneous path maps are spanned by degree-one factorizations -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient
universe u v w
variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q]
variable (R : ∀ X Y : Category k Q, Set (X ⟶ Y))

/-- Composites of a degree-one map and a degree-n map through a vertex. -/
def firstDegreeComposites (x y : Q) (n : ℕ) :
    Set (obj R (LinearPathCategory.obj k Q x) ⟶ obj R (LinearPathCategory.obj k Q y)) :=
  {f | ∃ z : Q, ∃ a : obj R (LinearPathCategory.obj k Q x) ⟶ obj R (LinearPathCategory.obj k Q z),
    ∃ b : obj R (LinearPathCategory.obj k Q z) ⟶ obj R (LinearPathCategory.obj k Q y),
    a ∈ lengthComponent R _ _ 1 ∧ b ∈ lengthComponent R _ _ n ∧ a ≫ b = f}

/-- Splitting the final quiver edge gives the first categorical factor,
because the representable convention reverses paths. -/
theorem lengthComponent_le_firstDegreeComposites (x y : Q) (n : ℕ) :
    lengthComponent R (LinearPathCategory.obj k Q x) (LinearPathCategory.obj k Q y) (n + 1) ≤
      Submodule.span k (firstDegreeComposites R x y n) := by
  rw [lengthComponent, Submodule.map_le_iff_le_comap, LinearPathCategory.lengthComponent_eq_span]
  apply Submodule.span_le.mpr
  rintro f ⟨p, hp, rfl⟩
  change (quotientFunctor R).map (pathHom p) ∈ Submodule.span k (firstDegreeComposites R x y n)
  cases p with
  | nil => simp at hp
  | @cons z x p a =>
    have hp' : p.length = n := Nat.succ.inj hp
    apply Submodule.subset_span
    refine ⟨z,
      (quotientFunctor R).map (pathHom a.toPath),
      (quotientFunctor R).map (pathHom p), ?_, ?_, ?_⟩
    · exact ⟨pathHom a.toPath, (pathHom_mem_lengthComponent_iff _ _).2 rfl, rfl⟩
    · exact ⟨pathHom p, (pathHom_mem_lengthComponent_iff _ _).2 hp', rfl⟩
    · rw [← Functor.map_comp, pathHom_comp]
      rfl

end MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient
