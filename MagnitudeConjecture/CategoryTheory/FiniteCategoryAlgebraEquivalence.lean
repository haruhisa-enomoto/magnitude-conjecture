import MagnitudeConjecture.Algebra.IndecomposableLocalEnd
import MagnitudeConjecture.CategoryTheory.BiserialObject
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator

/-!
# Finite category algebras under object-bijective linear equivalence

A linear equivalence of finite categories need not preserve the chosen
category algebra: an equivalent category may contain duplicate isomorphic
objects, and the biproduct of all representables then changes.  This file
records the exact replacement.  When the forward functor is literally
bijective on objects, precomposition identifies corresponding
representables, the two finite projective generators, and hence their
endomorphism algebras.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory.Functor

universe uC uD vC vD uK

variable {k : Type uK} [Field k]
variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]

/-- A fully faithful linear functor identifies Hom spaces linearly. -/
noncomputable def mapLinearEquivOfFullyFaithful
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (X Y : C) : (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) := by
  let H := _root_.CategoryTheory.Functor.FullyFaithful.ofFullyFaithful F
  exact
    { toEquiv := H.homEquiv
      map_add' := fun x y ↦ by
        change F.map (x + y) = F.map x + F.map y
        exact F.map_add
      map_smul' := fun c x ↦ by
        change F.map (c • x) = c • F.map x
        exact F.map_smul c x }

/-- A fully faithful linear functor identifies endomorphism algebras. -/
noncomputable def endAlgEquivOfFullyFaithful
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (X : C) : End X ≃ₐ[k] End (F.obj X) := by
  exact
  { toFun := F.map
    invFun := F.preimage
    left_inv := F.preimage_map
    right_inv := F.map_preimage
    map_add' := fun _ _ ↦ F.map_add
    map_mul' := fun f g ↦ F.map_comp g f
    commutes' := by
      intro c
      change F.map (c • 𝟙 X) = c • 𝟙 (F.obj X)
      rw [F.map_smul, F.map_id] }

end MagnitudeConjecture.CategoryTheory.Functor

namespace MagnitudeConjecture.CategoryTheory.Iso

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Conjugation along an isomorphism is an equivalence of endomorphism
algebras. -/
noncomputable def endAlgEquiv {X Y : C} (e : X ≅ Y) :
    End X ≃ₐ[k] End Y :=
  { e.conj with
    map_add' := by
      intro f g
      apply End.ext
      change e.inv ≫ (End.asHom f + End.asHom g) ≫ e.hom =
        e.inv ≫ End.asHom f ≫ e.hom +
          e.inv ≫ End.asHom g ≫ e.hom
      simp only [Preadditive.comp_add, Preadditive.add_comp]
    commutes' := by
      intro c
      change e.inv ≫ (c • 𝟙 X) ≫ e.hom = c • 𝟙 Y
      simp only [Linear.comp_smul, Linear.smul_comp]
      simp }

end MagnitudeConjecture.CategoryTheory.Iso

namespace MagnitudeConjecture.CoveringHom

universe uC uD v

variable {k : Type v} [Field k]
variable {C : Type uC} {D : Type uD} [Category.{v} C] [Category.{v} D]
variable [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]
variable [Fintype C] [Fintype D]

omit [Fintype D] in
/-- Finite-dimensional representables pull back along a fully faithful
linear functor whose source has finitely many objects. -/
theorem linearCoyonedaFiniteOfFullyFaithful
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (hD : ∀ Y : D, IsFiniteDimensionalModule (C := D) k
      (linearCoyonedaLinearModule (k := k) Y)) :
    ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X) := by
  intro X
  constructor
  · intro Y
    letI : FiniteDimensional k (F.obj X ⟶ F.obj Y) :=
      (hD (F.obj X)).1 (F.obj Y)
    exact
      (MagnitudeConjecture.CategoryTheory.Functor.mapLinearEquivOfFullyFaithful
        (k := k) F X Y).symm.finiteDimensional
  · exact Set.toFinite _

section

variable
    (hC : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hD : ∀ Y : D, IsFiniteDimensionalModule (C := D) k
      (linearCoyonedaLinearModule (k := k) Y))
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (hobj : Function.Bijective e.functor.obj)

private noncomputable def objectEquiv : C ≃ D :=
  Equiv.ofBijective e.functor.obj hobj

private noncomputable def moduleCongrEquivalence :
    FiniteDimensionalModuleCategory.{uD, v, v, v} (C := D) k ≌
      FiniteDimensionalModuleCategory.{uC, v, v, v} (C := C) k :=
  finiteDimensionalModuleCongrEquivalence (k := k) e
    (objectEquiv e hobj) (fun _ ↦ rfl)

/-- Precomposition sends the representable at `e X` to the representable at
`X`. -/
private noncomputable def representableCongrIso (X : C) :
    (moduleCongrEquivalence (k := k) e hobj).functor.obj
        ((finiteDimensionalLinearCoyonedaFunctor (k := k) hD).obj
          (Opposite.op (e.functor.obj X))) ≅
      (finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
        (Opposite.op X) := by
  let F := e.symm.inverse
  letI : F.Additive := by
    change e.functor.Additive
    infer_instance
  letI : F.Linear k := by
    change e.functor.Linear k
    infer_instance
  letI : F.Full := by
    dsimp only [F]
    infer_instance
  letI : F.Faithful := by
    dsimp only [F]
    infer_instance
  let H := _root_.CategoryTheory.Functor.FullyFaithful.ofFullyFaithful F
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun Y ↦
    (MagnitudeConjecture.CategoryTheory.Functor.mapLinearEquivOfFullyFaithful
      (k := k) F X Y).symm.toModuleIso) ?_
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  dsimp only [moduleCongrEquivalence,
    finiteDimensionalModuleCongrEquivalence,
    linearModuleCongrEquivalence] at q ⊢
  change
    (MagnitudeConjecture.CategoryTheory.Functor.mapLinearEquivOfFullyFaithful
        (k := k) F X Z).symm (q ≫ F.map f) =
      (MagnitudeConjecture.CategoryTheory.Functor.mapLinearEquivOfFullyFaithful
        (k := k) F X Y).symm q ≫ f
  change H.preimage (q ≫ F.map f) = H.preimage q ≫ f
  rw [H.preimage_comp, H.preimage_map]

omit [Fintype C] [Fintype D] in
include hobj in
/-- A linear equivalence that is bijective on objects preserves intrinsic
biseriality of the corresponding covariant representables. -/
theorem finiteDimensionalLinearCoyoneda_isBiserialObject_iff_of_equivalence
    (X : C) :
    IsBiserialObject
        ((finiteDimensionalLinearCoyonedaFunctor (k := k) hD).obj
          (Opposite.op (e.functor.obj X))) ↔
      IsBiserialObject
        ((finiteDimensionalLinearCoyonedaFunctor (k := k) hC).obj
          (Opposite.op X)) := by
  let E := moduleCongrEquivalence (k := k) e hobj
  let i := representableCongrIso hC hD e hobj X
  constructor
  · intro hDrep
    exact (hDrep.map_equivalence E).congr i
  · intro hCrep
    apply IsBiserialObject.of_map_equivalence E
    exact hCrep.congr i.symm

/-- The object-bijective base equivalence identifies the two chosen finite
projective generators. -/
noncomputable def finiteCategoryProjectiveGeneratorCongrIso :
    (moduleCongrEquivalence (k := k) e hobj).functor.obj
        (finiteCategoryProjectiveGenerator hD) ≅
      finiteCategoryProjectiveGenerator hC := by
  let T := (moduleCongrEquivalence (k := k) e hobj).functor
  letI : T.IsEquivalence := inferInstance
  letI : T.Additive :=
    finiteDimensionalModuleCongrEquivalence_functor_additive
      (k := k) e (objectEquiv e hobj) (fun _ ↦ rfl)
  letI : T.Linear k :=
    finiteDimensionalModuleCongrEquivalence_functor_linear
      (k := k) e (objectEquiv e hobj) (fun _ ↦ rfl)
  let RD := fun Y : D ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hD).obj
      (Opposite.op Y)
  let ε : C ≃ D := objectEquiv e hobj
  letI : PreservesBiproduct RD T :=
    preservesBiproduct_of_preservesProduct T
  exact T.mapBiproduct RD ≪≫
    (biproduct.whiskerEquiv ε
      (fun X ↦ representableCongrIso hC hD e hobj X)).symm

/-- The fully faithful part of the finite category algebra equivalence,
before conjugating the transported projective generator back to the chosen
one. -/
noncomputable def finiteCategoryAlgebraMapEquiv :
    finiteCategoryProjectiveGenerator.algebra hD ≃ₐ[k]
      End ((moduleCongrEquivalence (k := k) e hobj).functor.obj
        (finiteCategoryProjectiveGenerator hD)) := by
  let T := (moduleCongrEquivalence (k := k) e hobj).functor
  letI : T.IsEquivalence := inferInstance
  letI : T.Additive :=
    finiteDimensionalModuleCongrEquivalence_functor_additive
      (k := k) e (objectEquiv e hobj) (fun _ ↦ rfl)
  letI : T.Linear k :=
    finiteDimensionalModuleCongrEquivalence_functor_linear
      (k := k) e (objectEquiv e hobj) (fun _ ↦ rfl)
  exact MagnitudeConjecture.CategoryTheory.Functor.endAlgEquivOfFullyFaithful
    (k := k) T (finiteCategoryProjectiveGenerator hD)

/-- Conjugation by the transported-generator isomorphism is the second part
of the finite category algebra equivalence. -/
noncomputable def finiteCategoryAlgebraConjEquiv :
    End ((moduleCongrEquivalence (k := k) e hobj).functor.obj
        (finiteCategoryProjectiveGenerator hD)) ≃ₐ[k]
      finiteCategoryProjectiveGenerator.algebra hC :=
  MagnitudeConjecture.CategoryTheory.Iso.endAlgEquiv
    (k := k) (finiteCategoryProjectiveGeneratorCongrIso hC hD e hobj)

/-- An object-bijective linear equivalence identifies the finite category
algebras, not merely their Morita classes. -/
noncomputable def finiteCategoryAlgebraEquiv :
    finiteCategoryProjectiveGenerator.algebra hC ≃ₐ[k]
      finiteCategoryProjectiveGenerator.algebra hD := by
  exact ((finiteCategoryAlgebraMapEquiv
      (k := k) (hD := hD) (e := e) (hobj := hobj)).trans
    (finiteCategoryAlgebraConjEquiv hC hD e hobj)).symm

end

end MagnitudeConjecture.CoveringHom
