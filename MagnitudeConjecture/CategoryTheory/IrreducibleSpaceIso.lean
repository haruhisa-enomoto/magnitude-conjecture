import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceEquivalence

/-! # Intrinsic irreducible quotients under changes of representatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Membership in any Hom ideal is invariant under conjugating its endpoints
by isomorphisms. -/
theorem homIdeal_mem_iso_iff (I : HomIdeal C) {X X' Y Y' : C}
    (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    i.inv ≫ f ≫ j.hom ∈ I.hom X' Y' ↔ f ∈ I.hom X Y := by
  constructor
  · intro hf
    have h := I.postcomp j.inv (I.precomp i.hom hf)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using h
  · intro hf
    exact I.precomp i.inv (I.postcomp j.hom hf)

namespace CategoricalIrreducible
variable (k : Type w) [Field k] [Linear k C]
variable {X X' Y Y' : C} (i : X ≅ X') (j : Y ≅ Y')

/-- Changing representatives induces a linear equivalence on radical numerators. -/
def radicalIsoEquiv : radical k X Y ≃ₗ[k] radical k X' Y' where
  toFun f := ⟨i.inv ≫ f.val ≫ j.hom, (homIdeal_mem_iso_iff homIdeal i j f.val).mpr f.property⟩
  invFun f := ⟨i.hom ≫ f.val ≫ j.inv,
    (homIdeal_mem_iso_iff homIdeal i.symm j.symm f.val).mpr f.property⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := by ext; simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' r f := by ext; simp

/-- The change of representatives identifies the radical-square denominators. -/
theorem denominator_map_iso :
    (denominator k X Y).map (radicalIsoEquiv k i j).toLinearMap = denominator k X' Y' := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (homIdeal_mem_iso_iff (homIdeal ⋆ᵢ homIdeal) i j g.val).mpr hg
  · intro hf
    refine ⟨(radicalIsoEquiv k i j).symm f, ?_, (radicalIsoEquiv k i j).apply_symm_apply f⟩
    exact (homIdeal_mem_iso_iff (homIdeal ⋆ᵢ homIdeal) i.symm j.symm f.val).mpr hf

/-- Intrinsic irreducible quotient spaces do not depend on the chosen representatives. -/
def spaceIsoEquiv : Space k X Y ≃ₗ[k] Space k X' Y' :=
  Submodule.Quotient.equiv _ _ (radicalIsoEquiv k i j) (denominator_map_iso k i j)

/-- The inverse realization identifies quotient spaces with the original
objects, using the counit to remove the change of representatives. -/
def spaceInverseEquivalence {D : Type*} [Category.{v} D] [Preadditive D] [Linear k D]
    (E : C ≌ D) [E.functor.Additive] [E.functor.Linear k] (X Y : D) :
    Space k (E.inverse.obj X) (E.inverse.obj Y) ≃ₗ[k] Space k X Y :=
  (spaceEquivalence k E (E.inverse.obj X) (E.inverse.obj Y)).trans
    (spaceIsoEquiv k (E.counitIso.app X) (E.counitIso.app Y))

end CategoricalIrreducible
end MagnitudeConjecture
