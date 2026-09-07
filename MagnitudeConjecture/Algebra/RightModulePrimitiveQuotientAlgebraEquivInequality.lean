import MagnitudeConjecture.Algebra.RightModuleAlgebraEquiv
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientFiniteSkeleton

/-!
# Primitive-quotient inequalities under algebra equivalence
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.RightModule

universe u

variable {k A B : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]
  [IsNoetherianRing Bᵐᵒᵖ]

/-- Transport a primitive-quotient AR-surplus inequality across an algebra
equivalence. -/
theorem FiniteIndecomposableSkeleton.primitiveQuotient_ambientARSurplus_le_mapAlgEquiv
    (S : FiniteIndecomposableSkeleton k B) (f : A ≃ₐ[k] B)
    (e : A) (P : PrimitiveIdempotentData e)
    [IsNoetherianRing (primitiveQuotientAlgebra e)ᵐᵒᵖ]
    [IsNoetherianRing (primitiveQuotientAlgebra (f e))ᵐᵒᵖ]
    (h : ((S.mapAlgEquiv f.symm).primitiveQuotientFiniteIndecomposableSkeleton P
        ).ambientARSurplus ≤ (S.mapAlgEquiv f.symm).ambientARSurplus) :
    (S.primitiveQuotientFiniteIndecomposableSkeleton (P.mapAlgEquiv f)
      ).ambientARSurplus ≤ S.ambientARSurplus := by
  let Salg := S.mapAlgEquiv f.symm
  let Q := Salg.primitiveQuotientFiniteIndecomposableSkeleton P
  let Qmap := Q.mapAlgEquiv (primitiveQuotientAlgEquiv f e)
  let Pf := P.mapAlgEquiv f
  let Qstandard := S.primitiveQuotientFiniteIndecomposableSkeleton Pf
  have hleft : Qstandard.ambientARSurplus = Q.ambientARSurplus :=
    (Qstandard.ambientARSurplus_eq Qmap).trans
      (Q.ambientARSurplus_mapAlgEquiv (primitiveQuotientAlgEquiv f e))
  have hright : Salg.ambientARSurplus = S.ambientARSurplus :=
    S.ambientARSurplus_mapAlgEquiv f.symm
  change Qstandard.ambientARSurplus ≤ S.ambientARSurplus
  rw [hleft, ← hright]
  exact h

/-- Transport equality between ambient and primitive-quotient AR surplus
back across an algebra equivalence. -/
theorem FiniteIndecomposableSkeleton.ambientARSurplus_eq_primitiveQuotient_mapAlgEquiv
    (S : FiniteIndecomposableSkeleton k B) (f : A ≃ₐ[k] B)
    (e : A) (P : PrimitiveIdempotentData e)
    [IsNoetherianRing (primitiveQuotientAlgebra e)ᵐᵒᵖ]
    [IsNoetherianRing (primitiveQuotientAlgebra (f e))ᵐᵒᵖ]
    (h : S.ambientARSurplus =
      (S.primitiveQuotientFiniteIndecomposableSkeleton (P.mapAlgEquiv f)
        ).ambientARSurplus) :
    (S.mapAlgEquiv f.symm).ambientARSurplus =
      ((S.mapAlgEquiv f.symm).primitiveQuotientFiniteIndecomposableSkeleton P
        ).ambientARSurplus := by
  let Salg := S.mapAlgEquiv f.symm
  let Q := Salg.primitiveQuotientFiniteIndecomposableSkeleton P
  let Qmap := Q.mapAlgEquiv (primitiveQuotientAlgEquiv f e)
  let Pf := P.mapAlgEquiv f
  let Qstandard := S.primitiveQuotientFiniteIndecomposableSkeleton Pf
  have hleft : Qstandard.ambientARSurplus = Q.ambientARSurplus :=
    (Qstandard.ambientARSurplus_eq Qmap).trans
      (Q.ambientARSurplus_mapAlgEquiv (primitiveQuotientAlgEquiv f e))
  have hright : Salg.ambientARSurplus = S.ambientARSurplus :=
    S.ambientARSurplus_mapAlgEquiv f.symm
  exact hright.trans (h.trans hleft)

end MagnitudeConjecture.RightModule
