import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite

/-!
# Essential-image closure from almost-split morphisms

If the image of a morphism is right almost split, every irreducible
predecessor of its endpoint is a retract of the image of its source.  A finite
indecomposable decomposition of that source and localness of the predecessor's
endomorphism ring then identify the predecessor with the image of one
indecomposable summand.  The dual statement uses a left almost-split image.

These are the categorical component-closure steps in Gabriel's Theorem 3.6(b).
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasFiniteBiproducts D] [HasBinaryBiproducts D]
  [IsIdempotentComplete D]

/-- A split subobject of a finite biproduct of indecomposables is isomorphic
to one of its summands when the source is indecomposable with local
endomorphism ring. -/
theorem exists_iso_finBiproduct_summand_of_isSplitMono
    {J : Type} [Fintype J]
    (X : J → D) (hX : ∀ j, Indecomposable (X j))
    {Y : D} (hY : Indecomposable Y) [IsLocalRing (End Y)]
    (f : Y ⟶ ⨁ X) [IsSplitMono f] :
    ∃ j : J, Nonempty (Y ≅ X j) := by
  classical
  let c : J → End Y := fun j ↦
    ((f ≫ biproduct.π X j) ≫
      (biproduct.ι X j ≫ retraction f) : End Y)
  have hsum : ∑ j, c j = 𝟙 Y := by
    change
      ∑ j,
          ((f ≫ biproduct.π X j) ≫
            (biproduct.ι X j ≫ retraction f) : End Y) =
        𝟙 Y
    calc
      ∑ j,
          ((f ≫ biproduct.π X j) ≫
            (biproduct.ι X j ≫ retraction f) : End Y) =
          f ≫ (∑ j, biproduct.π X j ≫ biproduct.ι X j) ≫
            retraction f := by
              simp only [Category.assoc, Preadditive.comp_sum,
                Preadditive.sum_comp]
      _ = f ≫ retraction f := by
        have htotal :
            (∑ j, biproduct.π X j ≫ biproduct.ι X j) = 𝟙 (⨁ X) :=
          biproduct.total
        rw [htotal]
        simp
      _ = 𝟙 Y := IsSplitMono.id f
  have hunit : IsUnit (∑ j, c j) := by
    rw [hsum]
    exact isUnit_one
  obtain ⟨j, _, hj⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := c) hunit
  let a : Y ⟶ X j := f ≫ biproduct.π X j
  let b : X j ⟶ Y := biproduct.ι X j ≫ retraction f
  have hab : IsIso (a ≫ b) := by
    apply (isUnit_iff_isIso (a ≫ b)).1
    simpa only [c, a, b] using hj
  letI : IsIso (a ≫ b) := hab
  letI : IsSplitMono a := by
    apply IsSplitMono.mk'
    exact
      { retraction := b ≫ inv (a ≫ b)
        id := by rw [← Category.assoc, IsIso.hom_inv_id] }
  haveI : IsIso a :=
    isIso_of_isSplitMono_to_indecomposable (hX j) a hY.1
  exact ⟨j, ⟨asIso a⟩⟩

/-- If `F.map m` is right almost split, every irreducible predecessor of its
endpoint belongs to the essential image of `F`, provided the source of `m`
has a finite indecomposable decomposition and `F` preserves those
indecomposables. -/
theorem exists_essentialImage_of_irreducible_to_of_map_rightAlmostSplit
    (F : C ⥤ D) [F.Additive]
    (decomposition : ∀ Z : C,
      Nonempty (FiniteIndecomposableDecomposition Z))
    (map_indec : ∀ (Z : C), Indecomposable Z → Indecomposable (F.obj Z))
    {M N : C} (m : N ⟶ M)
    (hm : IsRightAlmostSplit (F.map m))
    {Y : D} (hY : Indecomposable Y) (hlocalY : IsLocalRing (End Y))
    (f : Y ⟶ F.obj M) (hf : IsIrreducibleMorphism f) :
    ∃ Z : C, Indecomposable Z ∧ Nonempty (F.obj Z ≅ Y) := by
  letI : IsLocalRing (End Y) := hlocalY
  obtain ⟨h, hh⟩ := hm.factors f hf.not_isSplitEpi
  have hsplit : IsSplitMono h :=
    (hf.factorization h (F.map m) hh).resolve_right hm.not_isSplitEpi
  letI : IsSplitMono h := hsplit
  obtain ⟨d⟩ := decomposition N
  let e : F.obj N ≅ ⨁ fun j ↦ F.obj (d.summand j) :=
    F.mapIso d.isoBiproduct ≪≫ F.mapBiproduct d.summand
  let a : Y ⟶ ⨁ fun j ↦ F.obj (d.summand j) := h ≫ e.hom
  letI : IsSplitMono a := by
    dsimp only [a]
    infer_instance
  obtain ⟨j, ⟨ej⟩⟩ :=
    exists_iso_finBiproduct_summand_of_isSplitMono
      (fun j ↦ F.obj (d.summand j))
      (fun j ↦ map_indec (d.summand j) (d.indecomposable j))
      hY a
  exact ⟨d.summand j, d.indecomposable j, ⟨ej.symm⟩⟩

/-- Dual component closure: if `F.map m` is left almost split, every
irreducible successor of its source belongs to the essential image of `F`.-/
theorem exists_essentialImage_of_irreducible_from_of_map_leftAlmostSplit
    (F : C ⥤ D) [F.Additive]
    (decomposition : ∀ Z : C,
      Nonempty (FiniteIndecomposableDecomposition Z))
    (map_indec : ∀ (Z : C), Indecomposable Z → Indecomposable (F.obj Z))
    {M N : C} (m : M ⟶ N)
    (hm : IsLeftAlmostSplit (F.map m))
    {Y : D} (hY : Indecomposable Y) (hlocalY : IsLocalRing (End Y))
    (f : F.obj M ⟶ Y) (hf : IsIrreducibleMorphism f) :
    ∃ Z : C, Indecomposable Z ∧ Nonempty (F.obj Z ≅ Y) := by
  letI : IsLocalRing (End Y) := hlocalY
  obtain ⟨h, hh⟩ := hm.factors f hf.not_isSplitMono
  have hsplit : IsSplitEpi h :=
    (hf.factorization (F.map m) h hh).resolve_left hm.not_isSplitMono
  letI : IsSplitEpi h := hsplit
  obtain ⟨d⟩ := decomposition N
  let e : F.obj N ≅ ⨁ fun j ↦ F.obj (d.summand j) :=
    F.mapIso d.isoBiproduct ≪≫ F.mapBiproduct d.summand
  let a : Y ⟶ ⨁ fun j ↦ F.obj (d.summand j) := section_ h ≫ e.hom
  letI : IsSplitMono a := by
    dsimp only [a]
    infer_instance
  obtain ⟨j, ⟨ej⟩⟩ :=
    exists_iso_finBiproduct_summand_of_isSplitMono
      (fun j ↦ F.obj (d.summand j))
      (fun j ↦ map_indec (d.summand j) (d.indecomposable j))
      hY a
  exact ⟨d.summand j, d.indecomposable j, ⟨ej.symm⟩⟩

end MagnitudeConjecture.CategoryTheory
