import MagnitudeConjecture.Algebra.RightModuleAlgebraEquiv
import MagnitudeConjecture.CategoryTheory.BiserialObject

/-!
# Biserial principal ideals under algebra equivalence

An algebra equivalence induces an equivalence of finitely generated
right-module categories and identifies corresponding principal right ideals.
Intrinsic biseriality therefore transports in both directions.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A B : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]
  [IsNoetherianRing Bᵐᵒᵖ]

/-- Corresponding principal right ideals under an algebra equivalence are
intrinsically biserial simultaneously. -/
theorem rightIdealFGObj_isBiserialObject_mapAlgEquiv_iff
    (f : A ≃ₐ[k] B) (e : A) :
    IsBiserialObject (rightIdealFGObj (f e)) ↔
      IsBiserialObject (rightIdealFGObj e) := by
  let E := fgModuleEquivalenceOfAlgEquiv f
  let i := rightIdealFGObjMapAlgEquivIso f e
  constructor
  · intro h
    apply IsBiserialObject.of_map_equivalence E
    exact h.congr i.symm
  · intro h
    exact (h.map_equivalence E).congr i

end MagnitudeConjecture.RightModule
