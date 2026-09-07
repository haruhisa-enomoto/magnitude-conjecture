import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import MagnitudeConjecture.Algebra.UniserialModule
import MagnitudeConjecture.CategoryTheory.SubobjectEquivalence

/-!
# Uniserial objects

The covering part of the magnitude proof uses modules over finite and locally
bounded linear categories.  This file packages uniseriality intrinsically as
totality of the categorical subobject order, independently of any chosen
category algebra.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- An object is uniserial when any two of its subobjects are comparable. -/
def IsUniserialObject (X : C) : Prop :=
  Std.Total ((· ≤ ·) : Subobject X → Subobject X → Prop)

namespace IsUniserialObject

variable {X Y : C}

/-- Totality of an order is invariant under an order isomorphism. -/
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

/-- Uniseriality is invariant under an order isomorphism of subobject
lattices. -/
theorem congrOrderIso {Y : D}
    (hX : IsUniserialObject X)
    (e : Subobject X ≃o Subobject Y) :
    IsUniserialObject Y :=
  total_of_orderIso e hX

/-- The underlying object of a subobject is uniserial exactly when the
subobjects below it form a chain. -/
theorem subobject_iff_total_Iic (R : Subobject X) :
    IsUniserialObject (R : C) ↔
      Std.Total ((· ≤ ·) : Set.Iic R → Set.Iic R → Prop) := by
  let E := Subobject.subobjectOrderIso R
  constructor
  · intro h
    constructor
    intro P Q
    rcases h.total (E.symm P) (E.symm Q) with hPQ | hQP
    · exact Or.inl ((E.symm.le_iff_le).mp hPQ)
    · exact Or.inr ((E.symm.le_iff_le).mp hQP)
  · intro h
    constructor
    intro P Q
    rcases h.total (E P) (E Q) with hPQ | hQP
    · exact Or.inl ((E.le_iff_le).mp hPQ)
    · exact Or.inr ((E.le_iff_le).mp hQP)

/-- Uniseriality is invariant under isomorphism. -/
theorem congr (hX : IsUniserialObject X) (e : X ≅ Y) :
    IsUniserialObject Y :=
  congrOrderIso hX (Subobject.mapIsoToOrderIso e)

/-- An equivalence sends uniserial objects to uniserial objects. -/
theorem map_equivalence
    (hX : IsUniserialObject X) (E : C ≌ D) :
    IsUniserialObject (E.functor.obj X) :=
  congrOrderIso hX
    (MagnitudeConjecture.CategoryTheory.Equivalence.subobjectOrderIso E X)

/-- Uniseriality of the image under an equivalence reflects to the source. -/
theorem of_map_equivalence
    (E : C ≌ D)
    (hEX : IsUniserialObject (E.functor.obj X)) :
    IsUniserialObject X :=
  congrOrderIso hEX
    (MagnitudeConjecture.CategoryTheory.Equivalence.subobjectOrderIso E X).symm

/-- Passing to the opposite category preserves uniseriality.  The
subobject-order correspondence reverses order, which does not affect
totality. -/
theorem op [Abelian C] (hX : IsUniserialObject X) :
    IsUniserialObject (Opposite.op X) := by
  let E := CategoryTheory.Abelian.subobjectIsoSubobjectOp X
  unfold IsUniserialObject at hX ⊢
  constructor
  intro P Q
  rcases hX.total (E.symm P) (E.symm Q) with hPQ | hQP
  · exact Or.inr ((E.symm.le_iff_le).mp hPQ)
  · exact Or.inl ((E.symm.le_iff_le).mp hQP)

/-- The object underlying a subobject of a uniserial object is uniserial. -/
theorem subobject (hX : IsUniserialObject X) (R : Subobject X) :
    IsUniserialObject (R : C) := by
  let E := Subobject.subobjectOrderIso R
  unfold IsUniserialObject at hX ⊢
  constructor
  intro P Q
  let P' : Set.Iic R := E P
  let Q' : Set.Iic R := E Q
  rcases hX.total P'.1 Q'.1 with hPQ | hQP
  · left
    have hP'Q' : P' ≤ Q' := Subtype.mk_le_mk.mpr hPQ
    exact E.le_iff_le.mp hP'Q'
  · right
    have hQ'P' : Q' ≤ P' := Subtype.mk_le_mk.mpr hQP
    exact E.le_iff_le.mp hQ'P'

/-- A subobject is radical when it contains every proper subobject of its
ambient object. -/
def IsRadicalSubobject (R : Subobject X) : Prop :=
  ∀ P : Subobject X, P ≠ ⊤ → P ≤ R

/-- An object whose radical subobject is uniserial is itself uniserial. -/
theorem of_radicalSubobject
    (R : Subobject X) (hR : IsRadicalSubobject R)
    (hRU : IsUniserialObject (R : C)) :
    IsUniserialObject X := by
  let E := Subobject.subobjectOrderIso R
  unfold IsUniserialObject
  constructor
  intro P Q
  by_cases hPtop : P = ⊤
  · right
    simpa [hPtop]
  by_cases hQtop : Q = ⊤
  · left
    simpa [hQtop]
  let P' : Set.Iic R := ⟨P, hR P hPtop⟩
  let Q' : Set.Iic R := ⟨Q, hR Q hQtop⟩
  rcases hRU.total (E.symm P') (E.symm Q') with hPQ | hQP
  · left
    have hP'Q' : P' ≤ Q' := by
      simpa only [P', Q', E, OrderIso.apply_symm_apply] using E.monotone hPQ
    exact Subtype.mk_le_mk.mp hP'Q'
  · right
    have hQ'P' : Q' ≤ P' := by
      simpa only [P', Q', E, OrderIso.apply_symm_apply] using E.monotone hQP
    exact Subtype.mk_le_mk.mp hQ'P'

/-- Every zero object is uniserial. -/
theorem of_isZero (hX : IsZero X) : IsUniserialObject X := by
  unfold IsUniserialObject
  letI : Subsingleton (Subobject X) := Subobject.subsingleton_of_isZero hX
  constructor
  intro P Q
  left
  exact Subsingleton.elim P Q ▸ le_rfl

end IsUniserialObject

namespace IsUniserialModule

universe uR uM

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The module-theoretic and categorical definitions of uniseriality agree. -/
theorem iff_moduleCat :
    IsUniserialModule R M ↔
      IsUniserialObject (ModuleCat.of R M) := by
  let E := ModuleCat.subobjectModule (ModuleCat.of R M)
  constructor
  · intro hM
    unfold IsUniserialModule at hM
    unfold IsUniserialObject
    constructor
    intro P Q
    rcases hM.total (E P) (E Q) with hPQ | hQP
    · exact Or.inl ((E.le_iff_le).mp hPQ)
    · exact Or.inr ((E.le_iff_le).mp hQP)
  · intro hM
    unfold IsUniserialObject at hM
    unfold IsUniserialModule
    constructor
    intro P Q
    rcases hM.total (E.symm P) (E.symm Q) with hPQ | hQP
    · left
      simpa only [E, OrderIso.apply_symm_apply] using E.monotone hPQ
    · right
      simpa only [E, OrderIso.apply_symm_apply] using E.monotone hQP

/-- A finitely generated uniserial module is intrinsically uniserial in the
finitely generated module category. -/
theorem toFGModuleCatIsUniserialObject
    [IsNoetherianRing R]
    (N : FGModuleCat R) (hN : IsUniserialModule R N) :
    IsUniserialObject N := by
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
  have hAmbient : IsUniserialObject (ModuleCat.of R N) :=
    iff_moduleCat.mp hN
  exact IsUniserialObject.congrOrderIso hAmbient
    (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
      (ModuleCat.isFG R) N).symm

end IsUniserialModule

end MagnitudeConjecture
