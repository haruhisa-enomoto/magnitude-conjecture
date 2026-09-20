import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-! # Lifting a linear functor through a fully faithful realization -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CategoryTheory
universe u₁ u₂ u₃ v
variable {k : Type v} [Field k]
variable {C : Type u₁} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D] [Linear k D]
variable {E : Type u₃} [Category.{v} E] [Preadditive E] [Linear k E]
variable (F : D ⥤ E) [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
variable (G : C ⥤ E) [G.Additive] [G.Linear k]
variable (obj : C → D) (e : ∀ X, F.obj (obj X) ≅ G.obj X)

/-- Lift the maps of a functor to specified objects in a fully faithful realization. -/
def fullyFaithfulObjectLift : C ⥤ D where
  obj := obj
  map {X Y} f := F.preimage ((e X).hom ≫ G.map f ≫ (e Y).inv)
  map_id X := by
    apply F.map_injective
    simp
  map_comp f g := by
    apply F.map_injective
    simp

instance fullyFaithfulObjectLift_additive : (fullyFaithfulObjectLift F G obj e).Additive where
  map_add {X Y} f g := by
    apply F.map_injective
    simp [fullyFaithfulObjectLift, F.map_add, Preadditive.comp_add, Preadditive.add_comp]

instance fullyFaithfulObjectLift_linear : (fullyFaithfulObjectLift F G obj e).Linear k where
  map_smul f c := by
    apply F.map_injective
    simp [fullyFaithfulObjectLift, F.map_smul]

instance fullyFaithfulObjectLift_faithful [G.Faithful] :
    (fullyFaithfulObjectLift F G obj e).Faithful where
  map_injective {X Y} f g hfg := by
    apply G.map_injective
    have h := congrArg F.map hfg
    simpa [fullyFaithfulObjectLift] using h

instance fullyFaithfulObjectLift_full [G.Full] :
    (fullyFaithfulObjectLift F G obj e).Full where
  map_surjective {X Y} f := by
    refine ⟨G.preimage ((e X).inv ≫ F.map f ≫ (e Y).hom), ?_⟩
    apply F.map_injective
    simp [fullyFaithfulObjectLift]

end MagnitudeConjecture.CategoryTheory
