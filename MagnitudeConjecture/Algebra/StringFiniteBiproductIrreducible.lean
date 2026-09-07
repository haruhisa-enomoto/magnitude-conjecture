import MagnitudeConjecture.Algebra.StringIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.IrreducibleBinaryBiproduct
import MagnitudeConjecture.CategoryTheory.IrreducibleRepeatedBiproduct

/-!
# Irreducible binary-biproduct maps between finite string modules

This file specializes the generic binary-biproduct irreducibility criterion
to literal finite string modules.  Morphisms between two nonisomorphic string
modules are categorical-radical, so two irreducible boundary maps with a
common endpoint assemble to an irreducible map whenever their other endpoints
are nonisomorphic.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q} [Fintype Q]

/-- Every morphism between two nonisomorphic finite string modules is
categorically radical. -/
theorem finiteRightModule_isRadicalMorphism_of_not_iso
    {C D : Word R} (hmono : IsMonomial R)
    (hCD : ¬ Nonempty
      (C.finiteRightModule hmono ≅ D.finiteRightModule hmono))
    (f : C.finiteRightModule hmono ⟶ D.finiteRightModule hmono) :
    IsRadicalMorphism f := by
  letI : IsLocalRing (End (C.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (C.finiteRightModule hmono)
      (C.finiteRightModule_indecomposable hmono)
  exact MagnitudeConjecture.CategoryTheory.isRadicalMorphism_of_indecomposable_of_not_iso
    (C.finiteRightModule_indecomposable hmono)
    (D.finiteRightModule_indecomposable hmono) hCD f

/-- Two irreducible maps from one finite string module to nonisomorphic
finite string modules assemble to an irreducible map into their binary
biproduct. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_lift_of_not_iso
    {X Y₁ Y₂ : Word R} (hmono : IsMonomial R)
    (f₁ : X.finiteRightModule hmono ⟶ Y₁.finiteRightModule hmono)
    (f₂ : X.finiteRightModule hmono ⟶ Y₂.finiteRightModule hmono)
    (hf₁ : IsIrreducibleMorphism f₁)
    (hf₂ : IsIrreducibleMorphism f₂)
    (hY : ¬ Nonempty
      (Y₁.finiteRightModule hmono ≅ Y₂.finiteRightModule hmono)) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  letI : IsLocalRing (End (X.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (X.finiteRightModule hmono)
      (X.finiteRightModule_indecomposable hmono)
  apply MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_lift
    f₁ f₂ hf₁ hf₂
  · exact fun q ↦ finiteRightModule_isRadicalMorphism_of_not_iso hmono hY q
  · apply finiteRightModule_isRadicalMorphism_of_not_iso hmono
    intro h
    exact hY ⟨h.some.symm⟩

/-- Two irreducible maps from nonisomorphic finite string modules to one
finite string module assemble to an irreducible map out of their binary
biproduct. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_desc_of_not_iso
    {Y₁ Y₂ Z : Word R} (hmono : IsMonomial R)
    (g₁ : Y₁.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (g₂ : Y₂.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (hg₁ : IsIrreducibleMorphism g₁)
    (hg₂ : IsIrreducibleMorphism g₂)
    (hY : ¬ Nonempty
      (Y₁.finiteRightModule hmono ≅ Y₂.finiteRightModule hmono)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  letI : IsLocalRing (End (Z.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Z.finiteRightModule hmono)
      (Z.finiteRightModule_indecomposable hmono)
  apply MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_desc
    g₁ g₂ hg₁ hg₂
  · exact fun q ↦ finiteRightModule_isRadicalMorphism_of_not_iso hmono hY q
  · apply finiteRightModule_isRadicalMorphism_of_not_iso hmono
    intro h
    exact hY ⟨h.some.symm⟩

/-- Two maps from one finite string module to the same finite string module
assemble to an irreducible binary lift when all scalar row operations on the
second map remain irreducible. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_lift_repeated
    [IsAlgClosed k] {X Y : Word R} (hmono : IsMonomial R)
    (f₁ f₂ : X.finiteRightModule hmono ⟶ Y.finiteRightModule hmono)
    (hf₁ : IsIrreducibleMorphism f₁)
    (hcombination : ∀ c : k,
      IsIrreducibleMorphism (f₂ - c • f₁)) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  letI : IsLocalRing (End (X.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (X.finiteRightModule hmono)
      (X.finiteRightModule_indecomposable hmono)
  letI : IsLocalRing (End (Y.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Y.finiteRightModule hmono)
      (Y.finiteRightModule_indecomposable hmono)
  exact
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_lift_repeated
      f₁ f₂ hf₁ hcombination fun q ↦
        MagnitudeConjecture.CategoryTheory.exists_scalar_sub_isRadicalMorphism_of_algClosed
          (Y.finiteRightModule_indecomposable hmono).1 q

/-- The symmetric repeated-target criterion, with scalar row operations
based at the second component. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_lift_repeated_symm
    [IsAlgClosed k] {X Y : Word R} (hmono : IsMonomial R)
    (f₁ f₂ : X.finiteRightModule hmono ⟶ Y.finiteRightModule hmono)
    (hf₂ : IsIrreducibleMorphism f₂)
    (hcombination : ∀ c : k,
      IsIrreducibleMorphism (f₁ - c • f₂)) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  letI : IsLocalRing (End (X.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (X.finiteRightModule hmono)
      (X.finiteRightModule_indecomposable hmono)
  letI : IsLocalRing (End (Y.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Y.finiteRightModule hmono)
      (Y.finiteRightModule_indecomposable hmono)
  exact
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_lift_repeated_symm
      f₁ f₂ hf₂ hcombination fun q ↦
        MagnitudeConjecture.CategoryTheory.exists_scalar_sub_isRadicalMorphism_of_algClosed
          (Y.finiteRightModule_indecomposable hmono).1 q

/-- Two maps from the same finite string module to one finite string module
assemble to an irreducible binary desc when all scalar column operations on
the second map remain irreducible. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_desc_repeated
    [IsAlgClosed k] {Y Z : Word R} (hmono : IsMonomial R)
    (g₁ g₂ : Y.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (hg₁ : IsIrreducibleMorphism g₁)
    (hcombination : ∀ c : k,
      IsIrreducibleMorphism (g₂ - c • g₁)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  letI : IsLocalRing (End (Z.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Z.finiteRightModule hmono)
      (Z.finiteRightModule_indecomposable hmono)
  letI : IsLocalRing (End (Y.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Y.finiteRightModule hmono)
      (Y.finiteRightModule_indecomposable hmono)
  exact
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_desc_repeated
      g₁ g₂ hg₁ hcombination fun q ↦
        MagnitudeConjecture.CategoryTheory.exists_scalar_sub_isRadicalMorphism_of_algClosed
          (Y.finiteRightModule_indecomposable hmono).1 q

/-- The symmetric repeated-source criterion, with scalar column operations
based at the second component. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_desc_repeated_symm
    [IsAlgClosed k] {Y Z : Word R} (hmono : IsMonomial R)
    (g₁ g₂ : Y.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (hg₂ : IsIrreducibleMorphism g₂)
    (hcombination : ∀ c : k,
      IsIrreducibleMorphism (g₁ - c • g₂)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  letI : IsLocalRing (End (Z.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Z.finiteRightModule hmono)
      (Z.finiteRightModule_indecomposable hmono)
  letI : IsLocalRing (End (Y.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Y.finiteRightModule hmono)
      (Y.finiteRightModule_indecomposable hmono)
  exact
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_desc_repeated_symm
      g₁ g₂ hg₂ hcombination fun q ↦
        MagnitudeConjecture.CategoryTheory.exists_scalar_sub_isRadicalMorphism_of_algClosed
          (Y.finiteRightModule_indecomposable hmono).1 q

/-- The repeated-target criterion for two isomorphic, rather than literally
equal, finite string-module summands. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_lift_isomorphic
    [IsAlgClosed k] {X Y₁ Y₂ : Word R} (hmono : IsMonomial R)
    (e : Y₂.finiteRightModule hmono ≅ Y₁.finiteRightModule hmono)
    (f₁ : X.finiteRightModule hmono ⟶ Y₁.finiteRightModule hmono)
    (f₂ : X.finiteRightModule hmono ⟶ Y₂.finiteRightModule hmono)
    (hf₁ : IsIrreducibleMorphism f₁)
    (hcombination : ∀ c : k,
      IsIrreducibleMorphism (f₂ ≫ e.hom - c • f₁)) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  letI : IsLocalRing (End (X.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (X.finiteRightModule hmono)
      (X.finiteRightModule_indecomposable hmono)
  letI : IsLocalRing (End (Y₁.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Y₁.finiteRightModule hmono)
      (Y₁.finiteRightModule_indecomposable hmono)
  exact
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_lift_isomorphic
      e f₁ f₂ hf₁ hcombination fun q ↦
        MagnitudeConjecture.CategoryTheory.exists_scalar_sub_isRadicalMorphism_of_algClosed
          (Y₁.finiteRightModule_indecomposable hmono).1 q

/-- The repeated-source criterion for two isomorphic, rather than literally
equal, finite string-module summands. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_desc_isomorphic
    [IsAlgClosed k] {Y₁ Y₂ Z : Word R} (hmono : IsMonomial R)
    (e : Y₂.finiteRightModule hmono ≅ Y₁.finiteRightModule hmono)
    (g₁ : Y₁.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (g₂ : Y₂.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (hg₁ : IsIrreducibleMorphism g₁)
    (hcombination : ∀ c : k,
      IsIrreducibleMorphism (e.inv ≫ g₂ - c • g₁)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  letI : IsLocalRing (End (Z.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Z.finiteRightModule hmono)
      (Z.finiteRightModule_indecomposable hmono)
  letI : IsLocalRing (End (Y₁.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (Y₁.finiteRightModule hmono)
      (Y₁.finiteRightModule_indecomposable hmono)
  exact
    MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_biprod_desc_isomorphic
      e g₁ g₂ hg₁ hcombination fun q ↦
        MagnitudeConjecture.CategoryTheory.exists_scalar_sub_isRadicalMorphism_of_algClosed
          (Y₁.finiteRightModule_indecomposable hmono).1 q

/-- The symmetric isomorphic-source criterion, based at the second
component and transported through the opposite equality direction. -/
theorem isIrreducibleMorphism_finiteRightModule_biprod_desc_isomorphic_symm
    [IsAlgClosed k] {Y₁ Y₂ Z : Word R} (hmono : IsMonomial R)
    (e : Y₁.finiteRightModule hmono ≅ Y₂.finiteRightModule hmono)
    (g₁ : Y₁.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (g₂ : Y₂.finiteRightModule hmono ⟶ Z.finiteRightModule hmono)
    (hg₂ : IsIrreducibleMorphism g₂)
    (hcombination : ∀ c : k,
      IsIrreducibleMorphism (e.inv ≫ g₁ - c • g₂)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  have hswapped :=
    isIrreducibleMorphism_finiteRightModule_biprod_desc_isomorphic
      hmono e g₂ g₁ hg₂ hcombination
  have hbraided := hswapped.precomp_iso
    (biprod.braiding (Y₁.finiteRightModule hmono)
      (Y₂.finiteRightModule hmono))
  convert hbraided using 1
  apply biprod.hom_ext' <;> simp [biprod.braiding]

end MagnitudeConjecture.BoundQuiver.StringWord.Word
