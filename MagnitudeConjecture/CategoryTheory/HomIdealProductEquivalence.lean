import MagnitudeConjecture.CategoryTheory.HomIdealComap
import Mathlib.CategoryTheory.Equivalence

/-! # Products of Hom ideals under equivalences -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal
namespace MagnitudeConjecture
universe u v w
variable {C : Type u} {D : Type v}
variable [Category.{w} C] [Category.{w} D] [Preadditive C] [Preadditive D]

/-- An equivalence identifies the product of pulled-back ideals with the
pullback of their product. Intermediates downstairs lift using the counit. -/
theorem homIdealProduct_comap_equivalence (E : C ≌ D) [E.functor.Additive]
    (I J : HomIdeal D) :
    I.comap E.functor ⋆ᵢ J.comap E.functor = (I ⋆ᵢ J).comap E.functor := by
  apply HomIdeal.ext_hom
  intro X Y
  apply le_antisymm
  · intro f hf
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
        obtain ⟨Z, a, b, ha, hb, rfl⟩ := hf
        change E.functor.map (a ≫ b) ∈ (I ⋆ᵢ J).hom _ _
        rw [E.functor.map_comp]
        exact HomIdeal.comp_mem_mul ha hb
    | zero => exact (((I ⋆ᵢ J).comap E.functor).hom X Y).zero_mem
    | add f g _ _ hf hg => exact (((I ⋆ᵢ J).comap E.functor).hom X Y).add_mem hf hg
    | neg f _ hf => exact (((I ⋆ᵢ J).comap E.functor).hom X Y).neg_mem hf
  · intro f hf
    let K := I.comap E.functor ⋆ᵢ J.comap E.functor
    have hle : (I ⋆ᵢ J).hom (E.functor.obj X) (E.functor.obj Y) ≤
        (K.hom X Y).map E.functor.mapAddHom := by
      apply (AddSubgroup.closure_le _).2
      rintro g ⟨Z, a, b, ha, hb, rfl⟩
      let a' := E.functor.preimage (a ≫ (E.counitIso.app Z).inv)
      let b' := E.functor.preimage ((E.counitIso.app Z).hom ≫ b)
      have ha' : a' ∈ (I.comap E.functor).hom X (E.inverse.obj Z) := by
        change E.functor.map a' ∈ I.hom _ _
        dsimp [a']
        rw [E.functor.map_preimage]
        exact I.postcomp _ ha
      have hb' : b' ∈ (J.comap E.functor).hom (E.inverse.obj Z) Y := by
        change E.functor.map b' ∈ J.hom _ _
        dsimp [b']
        rw [E.functor.map_preimage]
        exact J.precomp _ hb
      refine ⟨a' ≫ b', HomIdeal.comp_mem_mul ha' hb', ?_⟩
      change E.functor.map (a' ≫ b') = a ≫ b
      simp [a', b']
    obtain ⟨g, hg, hgf⟩ := hle hf
    have : g = f := E.functor.map_injective hgf
    subst g
    exact hg

end MagnitudeConjecture
