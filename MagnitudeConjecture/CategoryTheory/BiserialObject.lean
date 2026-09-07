import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import MagnitudeConjecture.Algebra.BiserialModule
import MagnitudeConjecture.CategoryTheory.SubobjectEquivalence

/-!
# Biserial objects

This file packages the simple-top form of biseriality intrinsically in the
subobject lattice of an abelian category.  The formulation is designed to be
transported through categorical equivalences, without retaining coordinates
from a category algebra.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D]

/-- An object is biserial when its unique maximal subobject is the join of two
chains whose intersection is zero or simple. -/
def IsBiserialObject (X : C) : Prop :=
  ∃ R U V : Subobject X,
    IsCoatom R ∧
      (∀ Q : Subobject X, IsCoatom Q → Q = R) ∧
      U ⊔ V = R ∧
      Std.Total ((· ≤ ·) : Set.Iic U → Set.Iic U → Prop) ∧
      Std.Total ((· ≤ ·) : Set.Iic V → Set.Iic V → Prop) ∧
      (U ⊓ V = ⊥ ∨ IsAtom (U ⊓ V))

namespace IsBiserialObject

variable {X : C}

theorem total_of_orderIso
    {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β)
    (h : Std.Total ((· ≤ ·) : α → α → Prop)) :
    Std.Total ((· ≤ ·) : β → β → Prop) := by
  constructor
  intro P Q
  rcases h.total (e.symm P) (e.symm Q) with hPQ | hQP
  · exact Or.inl ((e.symm.le_iff_le).mp hPQ)
  · exact Or.inr ((e.symm.le_iff_le).mp hQP)

/-- Intrinsic biseriality is invariant under an order isomorphism of
subobject lattices. -/
theorem congrOrderIso
    [Abelian D] {Y : D}
    (hX : IsBiserialObject X)
    (e : Subobject X ≃o Subobject Y) :
    IsBiserialObject Y := by
  rcases hX with ⟨R, U, V, hR, hR_unique, hsup, hU, hV, hinter⟩
  refine ⟨e R, e U, e V, (e.isCoatom_iff R).mpr hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    have hQ' : IsCoatom (e.symm Q) :=
      (e.symm.isCoatom_iff Q).mpr hQ
    have heq : e.symm Q = R := hR_unique (e.symm Q) hQ'
    simpa using congrArg e heq
  · simpa only [map_sup] using congrArg e hsup
  · exact total_of_orderIso (e.Iic U) hU
  · exact total_of_orderIso (e.Iic V) hV
  · rcases hinter with hbot | hatom
    · left
      simpa only [map_inf, map_bot] using congrArg e hbot
    · right
      simpa only [map_inf] using (e.isAtom_iff (U ⊓ V)).mpr hatom

/-- Intrinsic biseriality is invariant under isomorphism. -/
theorem congr (hX : IsBiserialObject X) {Y : C} (e : X ≅ Y) :
    IsBiserialObject Y :=
  congrOrderIso hX (Subobject.mapIsoToOrderIso e)

/-- An equivalence sends biserial objects to biserial objects. -/
theorem map_equivalence
    (hX : IsBiserialObject X) (E : C ≌ D) [Abelian D] :
    IsBiserialObject (E.functor.obj X) :=
  congrOrderIso hX
    (MagnitudeConjecture.CategoryTheory.Equivalence.subobjectOrderIso E X)

/-- Biseriality of the image under an equivalence reflects to the source. -/
theorem of_map_equivalence
    (E : C ≌ D) [Abelian D]
    (hEX : IsBiserialObject (E.functor.obj X)) :
    IsBiserialObject X :=
  congrOrderIso hEX
    (MagnitudeConjecture.CategoryTheory.Equivalence.subobjectOrderIso E X).symm

/-- Intrinsic biseriality in an ambient abelian category restricts to a full
abelian subcategory closed under subobjects. -/
theorem of_fullSubcategory_ambient
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
    [Abelian P.FullSubcategory]
    {Z : P.FullSubcategory} (hZ : IsBiserialObject Z.obj) :
    IsBiserialObject Z :=
  congrOrderIso hZ
    (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso P Z).symm

/-- Intrinsic biseriality in a full abelian subcategory closed under
subobjects also holds in the ambient category. -/
theorem to_fullSubcategory_ambient
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
    [Abelian P.FullSubcategory]
    {Z : P.FullSubcategory} (hZ : IsBiserialObject Z) :
    IsBiserialObject Z.obj :=
  congrOrderIso hZ
    (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso P Z)

end IsBiserialObject

namespace IsBiserialModule

universe uR uM

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- A biserial module with simple top is intrinsically biserial as an object
of the module category. -/
theorem toIsBiserialObject
    (hbis : IsBiserialModule R M)
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    IsBiserialObject (ModuleCat.of R M) := by
  rcases hbis with ⟨U, V, hsup, hU, hV, hinter⟩
  let e := ModuleCat.subobjectModule (ModuleCat.of R M)
  have hJ : IsCoatom (Module.jacobson R M) :=
    isSimpleModule_iff_isCoatom.mp htop
  refine ⟨e.symm (Module.jacobson R M), e.symm U, e.symm V,
    (e.symm.isCoatom_iff (Module.jacobson R M)).mpr hJ, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    apply e.injective
    simp only [OrderIso.apply_symm_apply]
    have hQ' : IsCoatom (e Q) := (e.isCoatom_iff Q).mpr hQ
    apply (hJ.le_iff_eq hQ'.ne_top).mp
    rw [Module.jacobson]
    exact sInf_le hQ'
  · rw [← e.symm.map_sup, hsup]
  · exact IsBiserialObject.total_of_orderIso
      ((U.mapIic).trans (e.symm.Iic U)) hU
  · exact IsBiserialObject.total_of_orderIso
      ((V.mapIic).trans (e.symm.Iic V)) hV
  · rcases hinter with hzero | hsimple
    · left
      letI : Subsingleton (↥(U ⊓ V : Submodule R M)) := hzero
      have hbot : U ⊓ V = ⊥ := Submodule.eq_bot_of_subsingleton
      rw [← e.symm.map_inf, hbot, e.symm.map_bot]
    · right
      have hatom : IsAtom (U ⊓ V) :=
        isSimpleModule_iff_isAtom.mp hsimple
      rw [← e.symm.map_inf]
      exact (e.symm.isAtom_iff (U ⊓ V)).mpr hatom

/-- A biserial finitely generated module with simple top is intrinsically
biserial in the finitely generated module category. -/
theorem toFGModuleCatIsBiserialObject
    [IsNoetherianRing R]
    (N : FGModuleCat R)
    (hbis : IsBiserialModule R N)
    (htop : IsSimpleModule R (N ⧸ Module.jacobson R N)) :
    IsBiserialObject N := by
  letI : (ModuleCat.isFG R).IsClosedUnderSubobjects := {
    prop_of_mono := by
      intro X Y f _ hY
      letI : Module.Finite R Y := hY
      exact Module.Finite.of_injective f.hom
        ((ModuleCat.mono_iff_injective f).mp inferInstance) }
  letI : (ModuleCat.isFG R).ContainsZero := {
    exists_zero := ⟨ModuleCat.of R PUnit,
      ModuleCat.isZero_of_subsingleton _, by
      change Module.Finite R PUnit
      infer_instance⟩ }
  apply IsBiserialObject.of_fullSubcategory_ambient (ModuleCat.isFG R)
  change IsBiserialObject (ModuleCat.of R N)
  exact toIsBiserialObject hbis htop

end IsBiserialModule

namespace IsBiserialObject

universe uR uM

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- Intrinsic biseriality of a module-category object recovers the usual
module-theoretic biserial decomposition. -/
theorem toIsBiserialModule
    (hbis : IsBiserialObject (ModuleCat.of R M)) :
    IsBiserialModule R M := by
  rcases hbis with ⟨J, U, V, hJ, hJunique, hsup, hU, hV, hinter⟩
  let e := ModuleCat.subobjectModule (ModuleCat.of R M)
  have hJmod : IsCoatom (e J) :=
    (e.isCoatom_iff J).mpr hJ
  have hJuniqueMod : ∀ Q : Submodule R M, IsCoatom Q → Q = e J := by
    intro Q hQ
    have hQobj : IsCoatom (e.symm Q) :=
      (e.symm.isCoatom_iff Q).mpr hQ
    have hQeq : e.symm Q = J := hJunique (e.symm Q) hQobj
    simpa using congrArg e hQeq
  have hjac : Module.jacobson R M = e J := by
    rw [Module.jacobson]
    apply le_antisymm
    · exact sInf_le hJmod
    · apply le_sInf
      intro Q hQ
      rw [hJuniqueMod Q hQ]
  have hUmod : IsUniserialModule R (e U) :=
    total_of_orderIso
      ((e.Iic U).trans (e U).mapIic.symm) hU
  have hVmod : IsUniserialModule R (e V) :=
    total_of_orderIso
      ((e.Iic V).trans (e V).mapIic.symm) hV
  refine ⟨e U, e V, ?_, hUmod, hVmod, ?_⟩
  · rw [← e.map_sup, hsup, hjac]
  · rcases hinter with hbot | hatom
    · left
      apply Submodule.subsingleton_iff_eq_bot.mpr
      rw [← e.map_inf, hbot, e.map_bot]
    · right
      apply isSimpleModule_iff_isAtom.mpr
      rw [← e.map_inf]
      exact (e.isAtom_iff (U ⊓ V)).mpr hatom

/-- Intrinsic biseriality in the finitely generated module category recovers
the usual biserial decomposition of the underlying module. -/
theorem toIsBiserialModule_of_fg
    [IsNoetherianRing R] (N : FGModuleCat R)
    (hN : IsBiserialObject N) : IsBiserialModule R N := by
  letI : (ModuleCat.isFG R).IsClosedUnderSubobjects := {
    prop_of_mono := by
      intro X Y f _ hY
      letI : Module.Finite R Y := hY
      exact Module.Finite.of_injective f.hom
        ((ModuleCat.mono_iff_injective f).mp inferInstance) }
  letI : (ModuleCat.isFG R).ContainsZero := {
    exists_zero := ⟨ModuleCat.of R PUnit,
      ModuleCat.isZero_of_subsingleton _, by
      change Module.Finite R PUnit
      infer_instance⟩ }
  apply toIsBiserialModule
  exact IsBiserialObject.to_fullSubcategory_ambient
    (ModuleCat.isFG R) hN

end IsBiserialObject

end MagnitudeConjecture
