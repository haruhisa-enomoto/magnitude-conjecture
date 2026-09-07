import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Subobject orders under categorical equivalence

A fully faithful functor embeds the subobject order of an object into the
subobject order of its image.  For an equivalence this embedding is
surjective, hence an order isomorphism.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CategoryTheory

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A fully faithful mono-preserving functor embeds the subobject order of an
object into the subobject order of its image. -/
def subobjectOrderEmbedding
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (X : C) : Subobject X ↪o Subobject (F.obj X) where
  toFun P := Subobject.mk (F.map P.arrow)
  inj' := by
    intro P Q hPQ
    apply le_antisymm
    · have hmap : Subobject.mk (F.map P.arrow) ≤
          Subobject.mk (F.map Q.arrow) := by
        simpa using le_of_eq hPQ
      let g := Subobject.ofMkLEMk (F.map P.arrow) (F.map Q.arrow) hmap
      apply Subobject.le_of_comm (F.preimage g)
      apply F.map_injective
      simp [g]
    · have hmap : Subobject.mk (F.map Q.arrow) ≤
          Subobject.mk (F.map P.arrow) := by
        simpa using le_of_eq hPQ.symm
      let g := Subobject.ofMkLEMk (F.map Q.arrow) (F.map P.arrow) hmap
      apply Subobject.le_of_comm (F.preimage g)
      apply F.map_injective
      simp [g]
  map_rel_iff' := by
    intro P Q
    constructor
    · intro hPQ
      let g := Subobject.ofMkLEMk (F.map P.arrow) (F.map Q.arrow) hPQ
      apply Subobject.le_of_comm (F.preimage g)
      apply F.map_injective
      simp [g]
    · intro hPQ
      let g := Subobject.ofLE P Q hPQ
      apply Subobject.mk_le_mk_of_comm (F.map g)
      simp [g, ← F.map_comp]

/-- If an object property is closed under subobjects, passing from its full
subcategory to the ambient category does not change the subobject order. -/
def fullSubcategorySubobjectOrderIso
    [Abelian C] (P : ObjectProperty C) [P.ContainsZero]
    [P.IsClosedUnderSubobjects]
    (X : P.FullSubcategory) :
    Subobject X ≃o Subobject X.obj := by
  letI : P.IsClosedUnderKernels := inferInstance
  letI : P.ι.PreservesMonomorphisms :=
    P.preservesMonomorphisms_ι_of_isNormalEpiCategory
  let f := subobjectOrderEmbedding P.ι X
  have hsurj : Function.Surjective f := by
    intro Q
    let Y : P.FullSubcategory :=
      ⟨(Q : C), P.prop_of_mono Q.arrow X.property⟩
    let p : Y ⟶ X := ⟨Q.arrow⟩
    letI : Mono p := P.ι.mono_of_mono_map
      (show Mono (P.ι.map p) from by
        change Mono Q.arrow
        infer_instance)
    let S : Subobject X := Subobject.mk p
    let iQ : P.ι.obj (S : P.FullSubcategory) ≅ (Q : C) :=
      P.ι.mapIso (Subobject.underlyingIso p)
    refine ⟨S, ?_⟩
    dsimp [f, S, subobjectOrderEmbedding]
    apply Subobject.mk_eq_of_comm (P.ι.map (Subobject.mk p).arrow) iQ
    change P.ι.map (Subobject.underlyingIso p).hom ≫ P.ι.map p =
      P.ι.map (Subobject.mk p).arrow
    rw [← P.ι.map_comp]
    simp
  exact
    { toFun := f
      invFun := fun Q ↦ Classical.choose (hsurj Q)
      left_inv := fun Q ↦ f.injective (Classical.choose_spec (hsurj (f Q)))
      right_inv := fun Q ↦ Classical.choose_spec (hsurj Q)
      map_rel_iff' := f.le_iff_le }

/-- An equivalence induces an order isomorphism on the subobjects of every
object. -/
def Equivalence.subobjectOrderIso (E : C ≌ D) (X : C) :
    Subobject X ≃o Subobject (E.functor.obj X) := by
  let f := subobjectOrderEmbedding E.functor X
  have hsurj : Function.Surjective f := by
    intro Q
    let jQ := E.functor.objObjPreimageIso (Q : D)
    let p : E.functor.objPreimage (Q : D) ⟶ X :=
      E.functor.preimage (jQ.hom ≫ Q.arrow)
    letI : Mono p := by
      apply E.functor.mono_of_mono_map
      rw [show E.functor.map p = jQ.hom ≫ Q.arrow by simp [p]]
      infer_instance
    let P : Subobject X := Subobject.mk p
    let iQ : E.functor.obj (P : C) ≅ (Q : D) :=
      (E.functor.mapIso (Subobject.underlyingIso p)).trans jQ
    refine ⟨P, ?_⟩
    dsimp [f, P, subobjectOrderEmbedding]
    apply Subobject.mk_eq_of_comm
      (E.functor.map (Subobject.mk p).arrow) iQ
    change (E.functor.map (Subobject.underlyingIso p).hom ≫ jQ.hom) ≫
      Q.arrow = E.functor.map (Subobject.mk p).arrow
    rw [Category.assoc, show jQ.hom ≫ Q.arrow = E.functor.map p by simp [p],
      ← E.functor.map_comp]
    simp
  exact
    { toFun := f
      invFun := fun Q ↦ Classical.choose (hsurj Q)
      left_inv := fun P ↦ f.injective (Classical.choose_spec (hsurj (f P)))
      right_inv := fun Q ↦ Classical.choose_spec (hsurj Q)
      map_rel_iff' := f.le_iff_le }

end MagnitudeConjecture.CategoryTheory
