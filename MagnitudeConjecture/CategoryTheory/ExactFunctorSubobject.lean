import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Subobjects under exact functors

An exact functor between abelian categories sends a monomorphism representing
a subobject to a monomorphism.  This file packages the resulting map on
subobjects and its preservation of binary intersections and sums.
-/

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The direct image of a subobject under a mono-preserving functor. -/
def Functor.mapSubobject (F : Functor C D) [F.PreservesMonomorphisms]
    {X : C} (P : Subobject X) : Subobject (F.obj X) :=
  Subobject.mk (F.map P.arrow)

namespace Functor

variable (F : Functor C D) [F.PreservesMonomorphisms]

/-- The object underlying the direct image of a subobject is the image under
the functor of the original underlying object. -/
def mapSubobjectUnderlyingIso {X : C} (P : Subobject X) :
    (mapSubobject F P : D) ≅ F.obj (P : C) :=
  Subobject.underlyingIso (F.map P.arrow)

@[reassoc (attr := simp)]
theorem mapSubobjectUnderlyingIso_hom_arrow {X : C} (P : Subobject X) :
    (mapSubobjectUnderlyingIso F P).hom ≫ F.map P.arrow =
      (mapSubobject F P).arrow := by
  simp [mapSubobjectUnderlyingIso, mapSubobject]

/-- Direct image of subobjects is monotone. -/
theorem mapSubobject_mono {X : C} {P Q : Subobject X} (h : P ≤ Q) :
    mapSubobject F P ≤ mapSubobject F Q := by
  apply Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE P Q h))
  simp [← F.map_comp]

/-- Direct image is independent of the representative chosen for a
subobject. -/
theorem mapSubobject_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    mapSubobject F (Subobject.mk f) = Subobject.mk (F.map f) := by
  let e : (mapSubobject F (Subobject.mk f) : D) ≅
      (Subobject.mk (F.map f) : D) :=
    mapSubobjectUnderlyingIso F (Subobject.mk f) ≪≫
      F.mapIso (Subobject.underlyingIso f) ≪≫
        (Subobject.underlyingIso (F.map f)).symm
  apply Subobject.eq_of_comm e
  dsimp only [e]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Subobject.underlyingIso_arrow, Functor.mapIso_hom, ← F.map_comp,
    Subobject.underlyingIso_hom_comp_eq_mk,
    mapSubobjectUnderlyingIso_hom_arrow]

variable [Abelian C] [Abelian D]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Exact functors carry the image subobject of a morphism to the image
subobject of the mapped morphism. -/
theorem mapSubobject_imageSubobject {X Y : C} (f : X ⟶ Y) :
    mapSubobject F (imageSubobject f) = imageSubobject (F.map f) := by
  let e : (mapSubobject F (imageSubobject f) : D) ≅
      (imageSubobject (F.map f) : D) :=
    mapSubobjectUnderlyingIso F (imageSubobject f) ≪≫
      F.mapIso (imageSubobjectIso f) ≪≫
        (PreservesImage.iso F f).symm ≪≫
          (imageSubobjectIso (F.map f)).symm
  apply Subobject.eq_of_comm e
  dsimp only [e]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [imageSubobject_arrow', PreservesImage.inv_comp_image_ι_map,
    Functor.mapIso_hom, ← F.map_comp, imageSubobject_arrow,
    mapSubobjectUnderlyingIso_hom_arrow]

/-- The join of two subobjects is the image of the morphism induced from
their biproduct. -/
theorem sup_eq_imageSubobject_biprod_desc {X : C} (P Q : Subobject X) :
    P ⊔ Q = imageSubobject (biprod.desc P.arrow Q.arrow) := by
  apply le_antisymm
  · apply sup_le
    · apply Subobject.le_of_comm
        (biprod.inl ≫ factorThruImageSubobject
          (biprod.desc P.arrow Q.arrow))
      simp
    · apply Subobject.le_of_comm
        (biprod.inr ≫ factorThruImageSubobject
          (biprod.desc P.arrow Q.arrow))
      simp
  · apply imageSubobject_le
      (biprod.desc P.arrow Q.arrow)
      (biprod.desc
        (Subobject.ofLE P (P ⊔ Q) le_sup_left)
        (Subobject.ofLE Q (P ⊔ Q) le_sup_right))
    ext <;> simp

/-- Exact functors preserve binary joins of subobjects. -/
theorem mapSubobject_sup {X : C} (P Q : Subobject X) :
    mapSubobject F (P ⊔ Q) = mapSubobject F P ⊔ mapSubobject F Q := by
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  rw [sup_eq_imageSubobject_biprod_desc,
    mapSubobject_imageSubobject F,
    sup_eq_imageSubobject_biprod_desc]
  let eP := mapSubobjectUnderlyingIso F P
  let eQ := mapSubobjectUnderlyingIso F Q
  let e : F.obj ((P : C) ⊞ (Q : C)) ≅
      (mapSubobject F P : D) ⊞ (mapSubobject F Q : D) :=
    F.mapBiprod (P : C) (Q : C) ≪≫ biprod.mapIso eP.symm eQ.symm
  rw [← imageSubobject_iso_comp e.hom
    (biprod.desc (mapSubobject F P).arrow (mapSubobject F Q).arrow)]
  congr 1
  have hmap :
      (biprod.mapIso eP.symm eQ.symm).hom ≫
          biprod.desc (mapSubobject F P).arrow (mapSubobject F Q).arrow =
        biprod.desc (F.map P.arrow) (F.map Q.arrow) := by
    apply biprod.hom_ext'
    · simp [eP, mapSubobjectUnderlyingIso, mapSubobject,
        Subobject.underlyingIso_arrow]
    · simp [eQ, mapSubobjectUnderlyingIso, mapSubobject,
        Subobject.underlyingIso_arrow]
  simp only [e, Iso.trans_hom, Category.assoc]
  rw [hmap]
  exact (biprod.mapBiprod_hom_desc F
    (P : C) (Q : C) P.arrow Q.arrow).symm

omit [PreservesFiniteColimits F] in
/-- Exact functors preserve binary intersections of subobjects. -/
theorem mapSubobject_inf {X : C} (P Q : Subobject X) :
    mapSubobject F (P ⊓ Q) = mapSubobject F P ⊓ mapSubobject F Q := by
  apply le_antisymm
  · apply le_inf
    · exact mapSubobject_mono F (inf_le_left : P ⊓ Q ≤ P)
    · exact mapSubobject_mono F (inf_le_right : P ⊓ Q ≤ Q)
  · let S := mapSubobject F P ⊓ mapSubobject F Q
    let a : (S : D) ⟶ F.obj (P : C) :=
      Subobject.ofLE S (mapSubobject F P) inf_le_left ≫
        (mapSubobjectUnderlyingIso F P).hom
    let b : (S : D) ⟶ F.obj (Q : C) :=
      Subobject.ofLE S (mapSubobject F Q) inf_le_right ≫
        (mapSubobjectUnderlyingIso F Q).hom
    have hab : a ≫ F.map P.arrow = b ≫ F.map Q.arrow := by
      simp [a, b]
    have hpb : IsPullback
        (F.map (Subobject.ofLE (P ⊓ Q) P inf_le_left))
        (F.map (Subobject.ofLE (P ⊓ Q) Q inf_le_right))
        (F.map P.arrow) (F.map Q.arrow) :=
      (Subobject.inf_isPullback P Q).map F
    let l : (S : D) ⟶ F.obj ((P ⊓ Q : Subobject X) : C) :=
      hpb.lift a b hab
    apply Subobject.le_of_comm
      (l ≫ (mapSubobjectUnderlyingIso F (P ⊓ Q)).inv)
    dsimp only [mapSubobjectUnderlyingIso, mapSubobject]
    rw [Category.assoc, Subobject.underlyingIso_arrow]
    rw [← Subobject.inf_comp_left P Q, F.map_comp,
      ← Category.assoc, hpb.lift_fst]
    simp [a, S]

omit [PreservesFiniteColimits F] in
/-- Exact functors preserve the bottom subobject. -/
theorem mapSubobject_bot {X : C} :
    mapSubobject F (⊥ : Subobject X) = ⊥ := by
  change Subobject.mk (F.map (⊥ : Subobject X).arrow) = ⊥
  rw [Subobject.mk_eq_bot_iff_zero]
  simp

end Functor

end MagnitudeConjecture.CategoryTheory
