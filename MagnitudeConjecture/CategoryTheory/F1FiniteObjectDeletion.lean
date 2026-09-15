import MagnitudeConjecture.CategoryTheory.BiserialObjectExtensionByZero
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPointwiseThinBiserial
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStructure

/-!
# Finite object-support quotients for the frozen deletion route

The frozen proof uses a finite set of surviving objects rather than a finite
convex window.  This file supplies the finite quotient and the representable
restriction comparison used by the equality/biserial layer.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Deleting the complement of a finite object set leaves a finite quotient
category, without any convexity assumption on the retained set. -/
theorem finite_deletion_of_finite_survivors
    (U : Set C) (hU : U.Finite) :
    Finite (DeletionCategory (k := k) C Uᶜ) := by
  let f : DeletionCategory (k := k) C Uᶜ → U := fun X ↦
    ⟨X.obj.as, by
      have hX := X.property
      change X.obj.as ∉ Uᶜ at hX
      simpa only [Set.mem_compl_iff, not_not] using hX⟩
  letI : Finite U := hU
  exact Finite.of_injective f (by
    intro X Y hXY
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact congrArg Subtype.val hXY)

/-- The restriction of a representable which is supported in `U` is the
representable of the object-deletion quotient.  The proof uses the quotient
Yoneda map and the support vanishing certificate; no convexity is required. -/
noncomputable def deletionRepresentableRestrictionIso
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (U : Set C) (X : DeletionCategory (k := k) C Uᶜ)
    (hsupport : moduleSupport k
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X.obj.as)).obj.obj ⊆ U) :
    let hR := deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP Uᶜ
    let M := (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op X.obj.as)
    let hvanish : ModuleVanishesOnDeleted (k := k) C Uᶜ M.obj.obj := by
      intro Z hZ
      rw [ModuleCat.isZero_iff_subsingleton]
      exact not_nontrivial_iff_subsingleton.mp fun hnontrivial ↦
        hZ (hsupport hnontrivial)
    let R := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C Uᶜ M hvanish
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hR).obj
        (Opposite.op X) ≅ R := by
  dsimp
  let D := DeletionCategory (k := k) C Uᶜ
  let M := (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X.obj.as)
  let hvanish : ModuleVanishesOnDeleted (k := k) C Uᶜ M.obj.obj := by
    intro Z hZ
    rw [ModuleCat.isZero_iff_subsingleton]
    exact not_nontrivial_iff_subsingleton.mp fun hnontrivial ↦
      hZ (hsupport hnontrivial)
  let R := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C Uᶜ M hvanish
  let α : linearCoyonedaLinearModule (k := k) X ⟶ R.obj :=
    linearCoyonedaHom R.obj X (𝟙 X.obj.as)
  have hα (Y : D) (f : X.obj.as ⟶ Y.obj.as) :
      (α.hom.app Y).hom (survivingMap (k := k) C Uᶜ
        X.property (by change Y.obj.as ∉ Uᶜ; exact Y.property) f) = f := by
    change (moduleRestrictionToDeletion (k := k) C Uᶜ M.obj.obj hvanish).map
      (survivingMap (k := k) C Uᶜ X.property
        (by change Y.obj.as ∉ Uᶜ; exact Y.property) f)
        (𝟙 X.obj.as) = f
    rw [moduleRestrictionToDeletion_map_survivingMap
      (k := k) C Uᶜ M.obj.obj hvanish X.property
      (by change Y.obj.as ∉ Uᶜ; exact Y.property) f]
    change M.obj.obj.map f (𝟙 X.obj.as) = f
    change (𝟙 X.obj.as) ≫ f = f
    simp
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun Y ↦ ?_) ?_
  · have hinj : Function.Injective (α.hom.app Y).hom := by
      intro q₁ q₂ hq
      let f₁ : X.obj.as ⟶ Y.obj.as := Quot.out q₁.hom
      let f₂ : X.obj.as ⟶ Y.obj.as := Quot.out q₂.hom
      have hf₁ : (Quot.mk _ f₁ : X.obj ⟶ Y.obj) = q₁.hom :=
        Quot.out_eq q₁.hom
      have hf₂ : (Quot.mk _ f₂ : X.obj ⟶ Y.obj) = q₂.hom :=
        Quot.out_eq q₂.hom
      have hq₁ : q₁ = survivingMap (k := k) C Uᶜ
          X.property (by change Y.obj.as ∉ Uᶜ; exact Y.property) f₁ := by
        apply ObjectProperty.hom_ext
        change q₁.hom = Quot.mk _ f₁
        exact hf₁.symm
      have hq₂ : q₂ = survivingMap (k := k) C Uᶜ
          X.property (by change Y.obj.as ∉ Uᶜ; exact Y.property) f₂ := by
        apply ObjectProperty.hom_ext
        change q₂.hom = Quot.mk _ f₂
        exact hf₂.symm
      have hf : f₁ = f₂ := by
        have hq' :
            (α.hom.app Y).hom (survivingMap (k := k) C Uᶜ X.property
              (by change Y.obj.as ∉ Uᶜ; exact Y.property) f₁) =
              (α.hom.app Y).hom (survivingMap (k := k) C Uᶜ X.property
                (by change Y.obj.as ∉ Uᶜ; exact Y.property) f₂) := by
          simpa [hq₁, hq₂] using hq
        have hf' := hq'
        rw [hα Y f₁, hα Y f₂] at hf'
        change f₁ = f₂ at hf'
        exact hf'
      exact hq₁.trans ((congrArg (fun f ↦ survivingMap (k := k) C Uᶜ
        X.property (by change Y.obj.as ∉ Uᶜ; exact Y.property) f) hf).trans hq₂.symm)
    have hsurj : Function.Surjective (α.hom.app Y).hom := by
      intro m
      change X.obj.as ⟶ Y.obj.as at m
      refine ⟨survivingMap (k := k) C Uᶜ X.property
        (by change Y.obj.as ∉ Uᶜ; exact Y.property) m, ?_⟩
      exact hα Y m
    let e : (X ⟶ Y) ≃ₗ[k] R.obj.obj.obj Y :=
      LinearEquiv.ofBijective (α.hom.app Y).hom ⟨hinj, hsurj⟩
    exact e.toModuleIso
  · intro Y Z f
    exact α.hom.naturality f

end MagnitudeConjecture.ObjectDeletion
