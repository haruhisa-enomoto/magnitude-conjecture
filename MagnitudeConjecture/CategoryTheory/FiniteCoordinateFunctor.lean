import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition

/-!
# Functors controlled by finite additive coordinates

If every source object is a finite biproduct of a fixed family of coordinate
objects, fullness or faithfulness on pairs of coordinates extends to the
whole functor.  These lemmas isolate the finite matrix argument used in the
standard-mesh restriction comparison.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]
variable {D : Type u'} [Category.{v'} D]
variable {P : Type} (H : P → C)

/-- A functor is faithful if its map is injective between every pair of
coordinate objects and every source object is a finite biproduct of
coordinates. -/
theorem functor_faithful_of_finite_coordinates
    (F : C ⥤ D)
    (hcoord : ∀ X : C, ∃ (n : ℕ) (p : Fin n → P),
      Nonempty ((⨁ fun i ↦ H (p i)) ≅ X))
    (hfaithful : ∀ p q : P, Function.Injective
      (fun f : H p ⟶ H q ↦ F.map f)) : F.Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨n, p, ⟨eX⟩⟩ := hcoord X
    obtain ⟨m, q, ⟨eY⟩⟩ := hcoord Y
    let A : Fin n → C := fun i ↦ H (p i)
    let B : Fin m → C := fun j ↦ H (q j)
    apply (cancel_epi eX.hom).1
    apply (cancel_mono eY.inv).1
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    apply hfaithful (p i) (q j)
    simp only [Functor.map_comp, Category.assoc]
    rw [h]

variable [Preadditive D]

set_option backward.isDefEq.respectTransparency false

/-- An additive functor is full if its map is surjective between every pair
of coordinate objects and every source object is a finite biproduct of
coordinates. -/
theorem functor_full_of_finite_coordinates
    (F : C ⥤ D) [F.Additive]
    (hcoord : ∀ X : C, ∃ (n : ℕ) (p : Fin n → P),
      Nonempty ((⨁ fun i ↦ H (p i)) ≅ X))
    (hfull : ∀ p q : P, Function.Surjective
      (fun f : H p ⟶ H q ↦ F.map f)) : F.Full where
  map_surjective {X Y} f := by
    obtain ⟨n, p, ⟨eX⟩⟩ := hcoord X
    obtain ⟨m, q, ⟨eY⟩⟩ := hcoord Y
    let A : Fin n → C := fun i ↦ H (p i)
    let B : Fin m → C := fun j ↦ H (q j)
    let FA : Fin n → D := F.obj ∘ A
    let FB : Fin m → D := F.obj ∘ B
    let fmat : (⨁ FA) ⟶ (⨁ FB) :=
      (F.mapBiproduct A).inv ≫ F.map eX.hom ≫ f ≫
        F.map eY.inv ≫ (F.mapBiproduct B).hom
    choose g hg using fun i j ↦ hfull (p i) (q j)
      (biproduct.ι FA i ≫ fmat ≫ biproduct.π FB j)
    let gmat : (⨁ A) ⟶ (⨁ B) := biproduct.matrix g
    let result : X ⟶ Y := eX.inv ≫ gmat ≫ eY.hom
    refine ⟨result, ?_⟩
    apply (cancel_epi ((F.mapBiproduct A).inv ≫ F.map eX.hom)).1
    apply (cancel_mono (F.map eY.inv ≫ (F.mapBiproduct B).hom)).1
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [result, Functor.map_comp, Category.assoc]
    rw [← F.map_comp_assoc, eX.hom_inv_id, F.map_id,
      Category.id_comp]
    rw [← F.map_comp_assoc eY.hom eY.inv, eY.hom_inv_id,
      F.map_id, Category.id_comp]
    have hι : biproduct.ι (F.obj ∘ A) i ≫
        (F.mapBiproduct A).inv = F.map (biproduct.ι A i) := by
      rw [Functor.mapBiproduct_inv, biproduct.ι_desc]
    have hπ : (F.mapBiproduct B).hom ≫
        biproduct.π (F.obj ∘ B) j = F.map (biproduct.π B j) := by
      rw [Functor.mapBiproduct_hom]
      change (biproduct.lift fun j ↦ F.map (biproduct.π B j)) ≫
        biproduct.π (fun j ↦ F.obj (B j)) j = _
      rw [biproduct.lift_π]
    have hmap :
        biproduct.ι (F.obj ∘ A) i ≫
              (F.mapBiproduct A).inv ≫ F.map gmat ≫
                (F.mapBiproduct B).hom ≫ biproduct.π (F.obj ∘ B) j =
            F.map (g i j) := by
      rw [show
        biproduct.ι (F.obj ∘ A) i ≫
              (F.mapBiproduct A).inv ≫ F.map gmat ≫
                (F.mapBiproduct B).hom ≫ biproduct.π (F.obj ∘ B) j =
            F.map (biproduct.ι A i ≫ gmat ≫ biproduct.π B j) by
        simp only [← Category.assoc, hι, hπ, F.map_comp]]
      simpa only [gmat, biproduct.components] using
        congrArg F.map (biproduct.matrix_components g i j)
    have hg' : F.map (g i j) =
        biproduct.ι (F.obj ∘ A) i ≫
          (F.mapBiproduct A).inv ≫ F.map eX.hom ≫ f ≫
            F.map eY.inv ≫ (F.mapBiproduct B).hom ≫
              biproduct.π (F.obj ∘ B) j := by
      simpa only [fmat, FA, FB, Category.assoc] using hg i j
    exact hmap.trans hg'

end MagnitudeConjecture.CategoryTheory
