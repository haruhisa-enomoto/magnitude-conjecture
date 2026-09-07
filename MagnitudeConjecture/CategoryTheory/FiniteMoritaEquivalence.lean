import MagnitudeConjecture.CategoryTheory.SubobjectEquivalence
import MagnitudeConjecture.CategoryTheory.ContragredientLinear
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Morita.Basic

/-!
# Morita equivalences on finitely generated modules

A linear equivalence between the categories of all modules over two
finite-dimensional algebras preserves finite-length objects.  Over an
Artinian ring these are exactly the finitely generated modules, so a Mathlib
`MoritaEquivalence` restricts to the finitely generated module categories.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture

universe u

namespace MoritaEquivalence

variable {k A B : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]

/-- A categorical equivalence carries a finite-length module over one
finite-dimensional algebra to a finite-length module over the other. -/
theorem moduleFinite_functor_obj
    (e : _root_.MoritaEquivalence k A B)
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite B (e.eqv.functor.obj M) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  letI : IsArtinianRing B := IsArtinianRing.of_finite k B
  have hLengthA : IsFiniteLength A M := by
    apply ((IsArtinianRing.tfae A M).out 0 3).mp
    exact (inferInstance : Module.Finite A M)
  have hDimA : FiniteDimensionalOrder (Submodule A M) :=
    Module.finiteDimensionalOrder_submodule_iff.mpr hLengthA
  let submoduleEquiv : Submodule A M ≃o
      Submodule B (e.eqv.functor.obj M) :=
    (ModuleCat.subobjectModule M).symm.trans <|
      (MagnitudeConjecture.CategoryTheory.Equivalence.subobjectOrderIso
        e.eqv M).trans <|
          ModuleCat.subobjectModule (e.eqv.functor.obj M)
  have hDimB : FiniteDimensionalOrder
      (Submodule B (e.eqv.functor.obj M)) := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top,
      ← Order.krullDim_eq_of_orderIso submoduleEquiv,
      ← Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
    exact hDimA
  have hLengthB : IsFiniteLength B (e.eqv.functor.obj M) :=
    Module.finiteDimensionalOrder_submodule_iff.mp hDimB
  exact ((IsArtinianRing.tfae B (e.eqv.functor.obj M)).out 3 0).mp
    hLengthB

/-- A Morita equivalence between finite-dimensional algebras restricts to
an equivalence of their finitely generated left-module categories. -/
def fgModuleEquivalence (e : _root_.MoritaEquivalence k A B) :
    FGModuleCat.{u} A ≌ FGModuleCat.{u} B := by
  let E := e.eqv
  letI : (ModuleCat.isFG.{u} B).IsClosedUnderIsomorphisms := by
    constructor
    intro X Y i hX
    letI : Module.Finite B X := hX
    exact Module.Finite.equiv i.toLinearEquiv
  apply E.congrFullSubcategory
  funext M
  apply propext
  constructor
  · intro hM
    letI : Module.Finite B (E.functor.obj M) := hM
    have hInv : Module.Finite A (E.inverse.obj (E.functor.obj M)) :=
      moduleFinite_functor_obj (_root_.MoritaEquivalence.symm k e)
        (E.functor.obj M)
    exact (Module.Finite.equiv_iff
      (E.unitIso.app M).toLinearEquiv).2 hInv
  · intro hM
    letI : Module.Finite A M := hM
    exact moduleFinite_functor_obj e M

noncomputable instance fgModuleEquivalence_functor_additive
    (e : _root_.MoritaEquivalence k A B) :
    (fgModuleEquivalence e).functor.Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change e.eqv.functor.map (f.1 + g.1) =
      e.eqv.functor.map f.1 + e.eqv.functor.map g.1
    exact e.eqv.functor.map_add

noncomputable instance fgModuleEquivalence_inverse_additive
    (e : _root_.MoritaEquivalence k A B) :
    (fgModuleEquivalence e).inverse.Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change e.eqv.inverse.map (f.1 + g.1) =
      e.eqv.inverse.map f.1 + e.eqv.inverse.map g.1
    exact e.eqv.inverse.map_add

noncomputable instance fgModuleEquivalence_functor_linear
    (e : _root_.MoritaEquivalence k A B) :
    (fgModuleEquivalence e).functor.Linear k where
  map_smul := by
    intro X Y f r
    apply ObjectProperty.hom_ext
    change e.eqv.functor.map (r • f.1) =
      r • e.eqv.functor.map f.1
    exact e.eqv.functor.map_smul r f.1

noncomputable instance fgModuleEquivalence_inverse_linear
    (e : _root_.MoritaEquivalence k A B) :
    (fgModuleEquivalence e).inverse.Linear k where
  map_smul := by
    intro X Y f r
    apply ObjectProperty.hom_ext
    change e.eqv.inverse.map (r • f.1) =
      r • e.eqv.inverse.map f.1
    exact e.eqv.inverse.map_smul r f.1

/-- A Morita equivalence of finite-dimensional algebras also induces a
linear equivalence between their finitely generated right-module
categories.  Contragredient duality changes right modules to the opposites
of the corresponding left-module categories, where the supplied Morita
equivalence applies. -/
def fgRightModuleEquivalence (e : _root_.MoritaEquivalence k A B) :
    FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} Bᵐᵒᵖ :=
  (QuotientSubmoduleEquidistribution.Contragredient.dualityEquivalence
      k A).symm.trans <|
    (fgModuleEquivalence e).op.trans <|
      QuotientSubmoduleEquidistribution.Contragredient.dualityEquivalence
        k B

noncomputable instance fgRightModuleEquivalence_functor_additive
    (e : _root_.MoritaEquivalence k A B) :
    (fgRightModuleEquivalence e).functor.Additive := by
  change
    ((QuotientSubmoduleEquidistribution.Contragredient.dualityEquivalence
        k A).inverse ⋙
      ((fgModuleEquivalence e).functor.op ⋙
        (QuotientSubmoduleEquidistribution.Contragredient.dualityEquivalence
          k B).functor)).Additive
  infer_instance

noncomputable instance fgRightModuleEquivalence_functor_linear
    (e : _root_.MoritaEquivalence k A B) :
    (fgRightModuleEquivalence e).functor.Linear k := by
  change
    ((QuotientSubmoduleEquidistribution.Contragredient.dualityEquivalence
        k A).inverse ⋙
      ((fgModuleEquivalence e).functor.op ⋙
        (QuotientSubmoduleEquidistribution.Contragredient.dualityEquivalence
          k B).functor)).Linear k
  infer_instance

noncomputable instance fgRightModuleEquivalence_inverse_additive
    (e : _root_.MoritaEquivalence k A B) :
    (fgRightModuleEquivalence e).inverse.Additive := inferInstance

noncomputable instance fgRightModuleEquivalence_inverse_linear
    (e : _root_.MoritaEquivalence k A B) :
    (fgRightModuleEquivalence e).inverse.Linear k := inferInstance

end MoritaEquivalence

end MagnitudeConjecture
