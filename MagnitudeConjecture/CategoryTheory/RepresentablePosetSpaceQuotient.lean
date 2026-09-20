import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpace
import MagnitudeConjecture.Combinatorics.PosetSpaceBoundaryCover

/-! # Realization by a quotient of a represented boundary cover -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.PosetSpace.RepresentableData
universe u v
variable {k T : Type u} {C : Type v} [Field k] [PartialOrder T]
variable [Category.{u} C] [Preadditive C] [Linear k C]

/-- A represented boundary cover becomes a realization after taking a
quotient with the prescribed total space, provided projective maps lift. -/
def isoOfQuotientCover (D : RepresentableData k T C)
    {X M : C} {Y : Obj k T} (c : D.obj X ⟶ Y)
    (hc : BoundarySurjective c) (q : X ⟶ M)
    (E : (D.source ⟶ M) ≃ₗ[k] Y)
    (hE : ∀ f : D.source ⟶ X, E (f ≫ q) = c.linear f)
    (hlift : ∀ t (f : D.projective t ⟶ M), ∃ g : D.projective t ⟶ X, g ≫ q = f) :
    D.obj M ≅ Y where
  hom :=
    { linear := E.toLinearMap
      map_subspace := by
        intro t x hx
        obtain ⟨f, rfl⟩ := hx
        obtain ⟨g, rfl⟩ := hlift t f
        change E (D.unit t ≫ (g ≫ q)) ∈ Y.subspace t
        rw [← Category.assoc, hE]
        exact c.map_subspace t _ ⟨g, rfl⟩ }
  inv :=
    { linear := E.symm.toLinearMap
      map_subspace := by
        intro t y hy
        rw [← hc.2 t] at hy
        obtain ⟨x, hx, hxy⟩ := hy
        obtain ⟨g, rfl⟩ := hx
        refine ⟨g ≫ q, ?_⟩
        apply E.injective
        change E (D.unit t ≫ (g ≫ q)) = E (E.symm y)
        rw [← Category.assoc, hE, E.apply_symm_apply]
        exact hxy }
  hom_inv_id := by
    apply Hom.ext
    ext x
    exact E.symm_apply_apply x
  inv_hom_id := by
    apply Hom.ext
    ext y
    exact E.apply_symm_apply y

end MagnitudeConjecture.PosetSpace.RepresentableData
