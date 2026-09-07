import MagnitudeConjecture.Algebra.RightModuleFactorAuslander
import MagnitudeConjecture.Algebra.RightModulePrimitivePosetRealization
import MagnitudeConjecture.CategoryTheory.RepresentablePresentation

/-!
# The tau-projective boundary generator

The manuscript realizes the primitive factor through the biproduct `U` of
all indecomposable tau-projective boundary objects.  This file constructs that
literal object, exhibits it as a coordinate retract of the full surviving
additive generator, and proves directly that its representable functor is
faithful in the primitive situation.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The biproduct of all surviving indecomposable tau-projectives.  This is
the manuscript's object `U`. -/
def factorProjectiveGenerator (K : Set (Fin S.n)) : S.FactorCategory K := by
  classical
  exact ⨁ fun p : S.FactorProjectiveLabel K ↦ S.factorObject K p.1

/-- The boundary generator is the coordinate retract of the full surviving
additive generator selected by the tau-projective predicate. -/
def factorProjectiveGeneratorRetract (K : Set (Fin S.n)) :
    Retract (S.factorProjectiveGenerator K) (S.factorAdditiveGenerator K) where
  i := biproduct.fromSubtype
    (fun x : S.SurvivingLabel K ↦ S.factorObject K x)
    (fun x ↦ (S.factorFiniteTauCategoryData K).IsProjective x)
  r := biproduct.toSubtype
    (fun x : S.SurvivingLabel K ↦ S.factorObject K x)
    (fun x ↦ (S.factorFiniteTauCategoryData K).IsProjective x)
  retract := biproduct.fromSubtype_toSubtype _ _

/-- In particular, the tau-projective boundary generator belongs to the
additive closure of the full surviving generator. -/
def factorProjectiveGenerator_finiteAddPresentation
    (K : Set (Fin S.n)) :
    MagnitudeConjecture.CategoryTheory.FiniteAddPresentation
      (S.factorAdditiveGenerator K) (S.factorProjectiveGenerator K) :=
  { n := 1
    retract :=
      (S.factorProjectiveGeneratorRetract K).trans
        (Retract.ofIso
          (biproductUniqueIso
            (fun _ : Fin 1 ↦ S.factorAdditiveGenerator K)).symm) }

/-- Restricted Yoneda on the actual tau-projective boundary generator. -/
def factorProjectiveRestrictedYoneda (K : Set (Fin S.n)) :
    S.FactorCategory K ⥤
      ModuleCat.{u} (End (S.factorProjectiveGenerator K))ᵐᵒᵖ :=
  preadditiveCoyonedaObj (S.factorProjectiveGenerator K)

/-- In a primitive factor, restricted Yoneda on all tau-projectives is
faithful.  The distinguished source is one of the summands of `U`, and its
representable functor was already proved faithful by the trace quotient. -/
theorem factorProjectiveRestrictedYoneda_faithful
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) :
    (S.factorProjectiveRestrictedYoneda K).Faithful where
  map_injective {X Y} f g hfg := by
    apply D.toPrimitiveTraceInput.toPrimitiveFactorInput.representableFaithful
      f g
    intro h
    change S.factorObject K D.source ⟶ X at h
    change h ≫ f = h ≫ g
    let U := S.factorProjectiveGenerator K
    let P : S.FactorCategory K := S.factorObject K D.source
    let π : U ⟶ P :=
      biproduct.π
        (fun p : S.FactorProjectiveLabel K ↦ S.factorObject K p.1)
        D.sourceProjectiveLabel
    have happ := congrArg
      (fun q ↦ q.hom (π ≫ h)) hfg
    change (π ≫ h) ≫ f = (π ≫ h) ≫ g at happ
    let ι : P ⟶ U :=
      biproduct.ι
        (fun p : S.FactorProjectiveLabel K ↦ S.factorObject K p.1)
        D.sourceProjectiveLabel
    have hiπ : ι ≫ π = 𝟙 P := by
      dsimp only [ι, π]
      exact biproduct.ι_π_self _ _
    have hroot := congrArg (fun q ↦ ι ≫ q) happ
    simpa only [← Category.assoc, hiπ, Category.id_comp] using hroot

/-- Once finite presentations by the tau-projective boundary generator are
constructed, the restricted Yoneda functor is full.  This is the exact
routine lifting part of Iyama's minimal-realization argument. -/
theorem factorProjectiveRestrictedYoneda_full_of_presentations
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (hpresent : ∀ X : S.FactorCategory K,
      Nonempty
        (MagnitudeConjecture.CategoryTheory.FiniteAddGeneratorPresentation
          (S.factorProjectiveGenerator K) X)) :
    (S.factorProjectiveRestrictedYoneda K).Full :=
  MagnitudeConjecture.CategoryTheory.preadditiveCoyonedaObj_full_of_finiteAddGeneratorPresentations
      (S.factorProjectiveGenerator K)
      (S.factorProjectiveRestrictedYoneda_faithful D)
      hpresent

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
