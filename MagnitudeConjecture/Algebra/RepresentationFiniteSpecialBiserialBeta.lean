import MagnitudeConjecture.Algebra.SpecialBiserialSocleReduction
import MagnitudeConjecture.Algebra.RightModuleBetaBiserial
import MagnitudeConjecture.Algebra.RightModuleMoritaBasicUniqueness

/-!
# The beta characterization of representation-finite special-biserial algebras

The forward implication transports to a literal special-biserial Morita
representative, applies the proved projective-injective socle reduction, and
uses the string-algebra middle-term bound.  The converse is developed below
through the representation-finite Auslander--Reiten structure theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

/-- A representation-finite special-biserial algebra has at most two
nonprojective occurrences in every almost-split middle term. -/
theorem specialBiserial_beta_le_two
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (hSpecial : BoundQuiver.IsSpecialBiserial k A) :
    FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
  rcases hSpecial with ⟨M⟩
  rcases M.presentation with ⟨N⟩
  letI : Fintype N.Vertex := N.vertexFintype
  letI : Quiver.{u} N.Vertex := N.quiver
  letI (x y : N.Vertex) : Fintype (x ⟶ y) := N.arrowFintype x y
  let R := N.presentation
  let hR := BoundQuiver.finiteRepresentablesOfAdmissible
    R.toPresentation.admissible
  let D := CoveringHom.finiteCategoryProjectiveGenerator.algebra hR
  letI : FiniteDimensional k D :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hR
  letI : IsNoetherianRing Dᵐᵒᵖ := IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing M.Carrierᵐᵒᵖ := IsNoetherianRing.of_finite k _
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory M.Carrier) :=
    fgModuleCat_enoughProjectives M.Carrierᵐᵒᵖ
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory D) :=
    fgModuleCat_enoughProjectives Dᵐᵒᵖ
  let E := MoritaEquivalence.fgRightModuleEquivalence M.morita
  let T := RightModule.FiniteIndecomposableSkeleton.mapEquivalence S E
  let f : M.Carrier ≃ₐ[k] D := R.toPresentation.algebraEquiv
  let U := T.mapAlgEquiv f
  let P : U.PrimitiveProjectivePresentation :=
    R.quotientCategoryPrimitiveProjectivePresentation U
  have hSpecialD : BoundQuiver.IsSpecialBiserial k D :=
    BoundQuiver.isSpecialBiserial_of_presentation ⟨N.mapAlgEquiv f.symm⟩
  have hString :=
    specialBiserial_socleFamilyQuotient_admitsStringPresentation
      U P hSpecialD
  have hBetaU : FiniteTauMatrix.beta
      U.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 :=
    P.beta_le_two_of_socleFamilyQuotient_admitsStringPresentation hString
  have hBetaT : FiniteTauMatrix.beta
      T.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
    let Ealg := RightModule.fgModuleEquivalenceOfAlgEquiv f
    exact (FiniteTauMatrix.beta_le_iff_of_equivalence
      T.finiteTauCategoryData.toFiniteRightTauCategoryData
      U.finiteTauCategoryData.toFiniteRightTauCategoryData
      Ealg (Equiv.refl (Fin T.n)) (T.mapAlgEquivObjIso f)).2 hBetaU
  exact (FiniteTauMatrix.beta_le_iff_of_equivalence
    S.finiteTauCategoryData.toFiniteRightTauCategoryData
    T.finiteTauCategoryData.toFiniteRightTauCategoryData
    E (Equiv.refl (Fin S.n)) (S.mapEquivalenceObjIso E)).2 hBetaT

/-- For a finite-dimensional representation-finite algebra over an
algebraically closed field, special-biseriality is equivalent to the bound
`β ≤ 2` on nonprojective occurrences in almost-split middle terms. -/
theorem representationFinite_isSpecialBiserial_iff_beta_le_two
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    BoundQuiver.IsSpecialBiserial k A ↔
      FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
  constructor
  · exact specialBiserial_beta_le_two S
  · exact S.isSpecialBiserial_of_beta_le_two

/-- The beta characterization specialized to an algebra carrying a complete
duplicate-free primitive-projective presentation. -/
theorem representationFinite_isSpecialBiserial_iff_beta_le_two_of_presentation
    [IsNoetherianRing A] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (_P : S.PrimitiveProjectivePresentation) :
    BoundQuiver.IsSpecialBiserial k A ↔
      FiniteTauMatrix.beta
        S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 :=
  representationFinite_isSpecialBiserial_iff_beta_le_two S

end MagnitudeConjecture
