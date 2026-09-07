import MagnitudeConjecture.Algebra.RightModuleAlgebraEquiv
import MagnitudeConjecture.Algebra.StringButlerRingelCount

/-!
# Vanishing of the module-category surplus for string algebras

The literal Butler--Ringel count is stated for the quotient-category algebra
carried by a string presentation.  This file transports that count across the
algebra equivalence bundled in an arbitrary string model and states the result
for any complete duplicate-free right-module skeleton of the presented
algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

/-- Every right-mesh middle term of a representation-finite string algebra
has total arity at most two, including the projective endpoints. -/
theorem rightMiddleArity_le_two_of_admitsStringPresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (hString : BoundQuiver.AdmitsStringPresentation k A)
    (i : Fin S.n) :
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2 := by
  obtain ⟨M⟩ := hString
  letI : Fintype M.Vertex := M.vertexFintype
  letI : Quiver.{u} M.Vertex := M.quiver
  letI (x y : M.Vertex) : Fintype (x ⟶ y) := M.arrowFintype x y
  let P := M.presentation
  let B := P.quotientCategoryAlgebra
  letI : FiniteDimensional k B := by
    let hP := BoundQuiver.finiteRepresentablesOfAdmissible
      P.toPresentation.admissible
    exact
      CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
        hP
  letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let e : A ≃ₐ[k] B := P.toPresentation.algebraEquiv
  let T := S.mapAlgEquiv e
  let E := RightModule.fgModuleEquivalenceOfAlgEquiv e
  letI : E.functor.Additive := inferInstance
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory B) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  have harity := FiniteTauMatrix.rightMiddleArity_eq_of_equivalence
    S.finiteTauCategoryData.toFiniteRightTauCategoryData
    T.finiteTauCategoryData.toFiniteRightTauCategoryData E
    (Equiv.refl (Fin S.n)) (S.mapAlgEquivObjIso e) i
  have hT : FiniteTauMatrix.rightMiddleArity
      T.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2 := by
    by_cases hi : T.finiteTauCategoryData.IsProjective i
    · exact P.rightMiddleArity_le_two_of_projective T i hi
    · exact P.rightMiddleArity_le_two_of_not_projective
        P.toSpecialBiserialPresentation.arrowPolarization T i hi
  exact harity.trans_le hT

/-- Every representation-finite algebra admitting a string presentation has
`beta ≤ 2`: its nonprojective right-mesh middle terms have total arity at
most two, and `beta` only counts their nonprojective summands. -/
theorem beta_le_two_of_admitsStringPresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (hString : BoundQuiver.AdmitsStringPresentation k A) :
    FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
  exact FiniteTauMatrix.beta_le_of_rightMiddleArity_le _ 2
    (fun i _ ↦ S.rightMiddleArity_le_two_of_admitsStringPresentation
      hString i)

/-- Every representation-finite algebra admitting a string presentation has
zero Auslander--Reiten surplus on any chosen indecomposable skeleton. -/
theorem ambientARSurplus_eq_zero_of_admitsStringPresentation
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (hString : BoundQuiver.AdmitsStringPresentation k A) :
    S.ambientARSurplus = 0 := by
  obtain ⟨M⟩ := hString
  letI : Fintype M.Vertex := M.vertexFintype
  letI : Quiver.{u} M.Vertex := M.quiver
  letI (x y : M.Vertex) : Fintype (x ⟶ y) := M.arrowFintype x y
  let P := M.presentation
  let B := P.quotientCategoryAlgebra
  letI : FiniteDimensional k B := by
    let hP := BoundQuiver.finiteRepresentablesOfAdmissible
      P.toPresentation.admissible
    exact
      CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
        hP
  letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k _
  let e : A ≃ₐ[k] B := P.toPresentation.algebraEquiv
  let T := S.mapAlgEquiv e
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory B) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  have hzero := P.quotientCategoryAlgebra_surplus_eq_zero
    P.toSpecialBiserialPresentation.arrowPolarization T
  have hprojective :
      T.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective =
        fun i ↦ Projective (T.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj
      T.finiteTauCategoryData.toFiniteRightTauCategoryData i
  have hzero' : T.ambientARSurplus = 0 := by
    change @ARCount.surplus (Fin T.n) inferInstance
      (FiniteTauMatrix.arrowMultiplicity
        T.finiteTauCategoryData.toFiniteRightTauCategoryData)
      (fun i ↦ Projective (T.fgObj i)) (Classical.decPred _) = 0
    exact (congrArg (fun projective : Fin T.n → Prop ↦
      @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          T.finiteTauCategoryData.toFiniteRightTauCategoryData)
        projective (Classical.decPred projective)) hprojective).symm.trans hzero
  rw [S.ambientARSurplus_mapAlgEquiv e] at hzero'
  exact hzero'

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
