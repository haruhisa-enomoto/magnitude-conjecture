import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleInheritance

/-!
# Finite decompositions and objectwise vanishing

These elementary lemmas are shared by the incoming-Hom locality proof and by
the older control-window development.  They require neither a control window
nor a finite quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasFiniteBiproducts D] [HasBinaryBiproducts D]

namespace FiniteIndecomposableDecomposition

/-- Inclusion of one displayed indecomposable summand. -/
def inclusion {X : D} (d : FiniteIndecomposableDecomposition X)
    (i : Fin d.n) : d.summand i ⟶ X :=
  biproduct.ι d.summand i ≫ d.isoBiproduct.inv

/-- Projection onto one displayed indecomposable summand. -/
def projection {X : D} (d : FiniteIndecomposableDecomposition X)
    (i : Fin d.n) : X ⟶ d.summand i :=
  d.isoBiproduct.hom ≫ biproduct.π d.summand i

@[simp]
theorem inclusion_projection {X : D}
    (d : FiniteIndecomposableDecomposition X) (i : Fin d.n) :
    d.inclusion i ≫ d.projection i = 𝟙 (d.summand i) := by
  simp [inclusion, projection, Category.assoc]

/-- Every displayed component of a right-minimal map is nonzero. -/
theorem inclusion_comp_ne_zero_of_isRightMinimal
    {X Y : D} (d : FiniteIndecomposableDecomposition X)
    (i : Fin d.n) (f : X ⟶ Y) (hf : IsRightMinimal f) :
    d.inclusion i ≫ f ≠ 0 := by
  intro hzero
  let e : X ⟶ X := 𝟙 X - d.projection i ≫ d.inclusion i
  have hefix : e ≫ f = f := by
    dsimp only [e]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      hzero, comp_zero, sub_zero]
  letI : IsIso e := hf e hefix
  have hie : d.inclusion i ≫ e = 0 := by
    dsimp only [e]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      d.inclusion_projection, Category.id_comp, sub_self]
  have hi0 : d.inclusion i = 0 := by
    apply (cancel_mono e).1
    simpa only [zero_comp] using hie
  have hzeroSummand : IsZero (d.summand i) := by
    rw [IsZero.iff_id_eq_zero, ← d.inclusion_projection i, hi0, zero_comp]
  exact (d.indecomposable i).1 hzeroSummand

/-- Every displayed component of a left-minimal map is nonzero. -/
theorem comp_projection_ne_zero_of_isLeftMinimal
    {X Y : D} (d : FiniteIndecomposableDecomposition Y)
    (i : Fin d.n) (f : X ⟶ Y) (hf : IsLeftMinimal f) :
    f ≫ d.projection i ≠ 0 := by
  intro hzero
  let e : Y ⟶ Y := 𝟙 Y - d.projection i ≫ d.inclusion i
  have hefix : f ≫ e = f := by
    dsimp only [e]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      hzero, zero_comp, sub_zero]
  letI : IsIso e := hf e hefix
  have hep : e ≫ d.projection i = 0 := by
    dsimp only [e]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      d.inclusion_projection, Category.comp_id, sub_self]
  have hp0 : d.projection i = 0 := by
    apply (cancel_epi e).1
    simpa only [comp_zero] using hep
  have hzeroSummand : IsZero (d.summand i) := by
    rw [IsZero.iff_id_eq_zero, ← d.inclusion_projection i, hp0, comp_zero]
  exact (d.indecomposable i).1 hzeroSummand

end FiniteIndecomposableDecomposition
end MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- A finite-dimensional module vanishes on the complement of any set which
contains its object support. -/
theorem moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (U : Set C)
    (hU : moduleSupport k M.obj.obj ⊆ U) :
    ModuleVanishesOnDeleted (k := k) C Uᶜ M.obj.obj := by
  intro X hX
  rw [ModuleCat.isZero_iff_subsingleton]
  exact not_nontrivial_iff_subsingleton.mp (fun hnontrivial ↦ hX (hU hnontrivial))

/-- Vanishing on a deleted set is invariant under isomorphism of finite
ambient modules. -/
theorem moduleVanishesOnDeleted_of_iso
    (D : Set C)
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (e : M ≅ N) (hM : ModuleVanishesOnDeleted (k := k) C D M.obj.obj) :
    ModuleVanishesOnDeleted (k := k) C D N.obj.obj := by
  intro X hX
  let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C) k).ι
  let K := (IsLinearModule.{u, v, v, v} (C := C) k).ι
  let eX : (K.obj (J.obj M)).obj X ≅ (K.obj (J.obj N)).obj X :=
    (K.mapIso (J.mapIso e)).app X
  exact (eX.isZero_iff).1 (hM X hX)

/-- If every displayed indecomposable summand of a finite decomposition
vanishes on a deleted object set, then so does the decomposed module. -/
theorem moduleVanishesOnDeleted_of_decomposition_summands
    (S : Set C)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (hvanish : ∀ i, ModuleVanishesOnDeleted
      (k := k) C S (d.summand i).obj.obj) :
    ModuleVanishesOnDeleted (k := k) C S Y.obj.obj := by
  intro X hXS
  let E := finiteDimensionalModuleEvaluation (k := k) C X
  have hzeroSummand (i : Fin d.n) : IsZero (E.obj (d.summand i)) :=
    hvanish i X hXS
  have hzeroSum : IsZero (⨁ fun i : Fin d.n ↦ E.obj (d.summand i)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro i
    exact (hzeroSummand i).eq_of_tgt _ _
  letI : E.Additive := by
    dsimp only [E, finiteDimensionalModuleEvaluation]
    infer_instance
  have hzeroBiproduct : IsZero (E.obj (⨁ d.summand)) :=
    hzeroSum.of_iso (E.mapBiproduct d.summand)
  exact hzeroBiproduct.of_iso (E.mapIso d.isoBiproduct)

end MagnitudeConjecture.ObjectDeletion
