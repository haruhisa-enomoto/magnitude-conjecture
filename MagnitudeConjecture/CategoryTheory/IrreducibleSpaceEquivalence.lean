import MagnitudeConjecture.CategoryTheory.HomIdealProductEquivalence
import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Intrinsic irreducible spaces under linear equivalences -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture
universe u v w z
variable {C : Type u} {D : Type v}
variable [Category.{w} C] [Category.{w} D] [Preadditive C] [Preadditive D]

/-- Equivalences preserve and reflect the intrinsic radical ideal. -/
theorem radical_comap_equivalence (E : C ≌ D) [E.functor.Additive] :
    (homIdeal : HomIdeal D).comap E.functor = (homIdeal : HomIdeal C) := by
  apply HomIdeal.ext_hom
  intro X Y
  ext f
  exact (isRadicalMorphism_iff_map_of_fullyFaithful E.functor E.fullyFaithfulFunctor f).symm

/-- Radical-square membership is invariant under equivalence. -/
theorem radicalSquare_map_equivalence_iff (E : C ≌ D) [E.functor.Additive]
    {X Y : C} (f : X ⟶ Y) :
    E.functor.map f ∈ ((homIdeal : HomIdeal D) ⋆ᵢ homIdeal).hom _ _ ↔
      f ∈ ((homIdeal : HomIdeal C) ⋆ᵢ homIdeal).hom X Y := by
  change f ∈ ((homIdeal ⋆ᵢ homIdeal).comap E.functor).hom X Y ↔ _
  rw [← homIdealProduct_comap_equivalence, radical_comap_equivalence]

namespace CategoricalIrreducible
variable (k : Type z) [Field k] [Linear k C] [Linear k D]
variable (E : C ≌ D) [E.functor.Additive] [E.functor.Linear k]

/-- Restrict the Hom map of a linear equivalence to radical numerators. -/
def radicalEquivalence (X Y : C) :
    radical k X Y ≃ₗ[k] radical k (E.functor.obj X) (E.functor.obj Y) where
  toFun f := ⟨E.functor.map f.val,
    (isRadicalMorphism_iff_map_of_fullyFaithful E.functor E.fullyFaithfulFunctor f.val).mp
      f.property⟩
  invFun f := ⟨E.functor.preimage f.val, by
    apply (isRadicalMorphism_iff_map_of_fullyFaithful
      E.functor E.fullyFaithfulFunctor _).mpr
    rw [E.functor.map_preimage]
    exact f.property⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := by ext; simp
  map_smul' r f := by ext; simp

/-- The radical numerator equivalence carries the radical-square denominator
onto the corresponding denominator. -/
theorem denominator_map_equivalence (X Y : C) :
    (denominator k X Y).map (radicalEquivalence k E X Y).toLinearMap =
      denominator k (E.functor.obj X) (E.functor.obj Y) := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (radicalSquare_map_equivalence_iff E g.val).mpr hg
  · intro hf
    refine ⟨(radicalEquivalence k E X Y).symm f, ?_,
      (radicalEquivalence k E X Y).apply_symm_apply f⟩
    apply (radicalSquare_map_equivalence_iff E _).mp
    change E.functor.map (E.functor.preimage f.val) ∈ _
    rw [E.functor.map_preimage]
    exact hf

/-- A linear category equivalence induces a linear equivalence on intrinsic
irreducible quotients. -/
def spaceEquivalence (X Y : C) :
    Space k X Y ≃ₗ[k] Space k (E.functor.obj X) (E.functor.obj Y) :=
  Submodule.Quotient.equiv _ _ (radicalEquivalence k E X Y)
    (denominator_map_equivalence k E X Y)

end CategoricalIrreducible
end MagnitudeConjecture
