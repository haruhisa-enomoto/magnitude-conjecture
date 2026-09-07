import MagnitudeConjecture.Algebra.RightModuleBoundaryPresentations
import MagnitudeConjecture.Algebra.RightModuleIncidenceCategory
import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpaceFullness

/-!
# Fullness of the primitive incidence realization

The boundary generator used by the minimal-realization argument is reindexed
as the root projective followed by the projectives of the finite poset.  A
map of represented poset spaces then lifts to a module map on its restricted
Yoneda representables, and boundary-generator fullness lifts that module map
to the required categorical morphism.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

/-- The root-plus-poset boundary family is componentwise the original family
of all factor tau-projectives, after reindexing by `projectiveEquiv`. -/
noncomputable def boundaryFamilyIso
    (R : S.PrimitiveProjectivePosetData D T) (q : Option T) :
    R.representableData.boundaryFamily q ≅
      S.factorObject K (R.projectiveEquiv.symm q).1 := by
  cases q with
  | none =>
      have hp : R.projectiveEquiv.symm none = D.sourceProjectiveLabel := by
        apply R.projectiveEquiv.injective
        rw [Equiv.apply_symm_apply, R.source_eq_none]
      rw [hp]
      exact Iso.refl _
  | some t => exact Iso.refl _

/-- The root-plus-poset boundary biproduct is isomorphic to the literal
biproduct of all factor tau-projectives. -/
noncomputable def boundaryGeneratorIso
    (R : S.PrimitiveProjectivePosetData D T) :
    R.representableData.boundaryGenerator ≅
      S.factorProjectiveGenerator K := by
  let F : S.FactorProjectiveLabel K → S.FactorCategory K :=
    fun p ↦ S.factorObject K p.1
  exact biproduct.mapIso (fun q ↦ R.boundaryFamilyIso q) ≪≫
    PosetSpace.RepresentableData.biproductReindex
      R.projectiveEquiv.symm F

/-- The root-plus-poset boundary generator remains faithful. -/
theorem boundaryRestrictedYoneda_faithful
    (R : S.PrimitiveProjectivePosetData D T) :
    (preadditiveCoyonedaObj
      R.representableData.boundaryGenerator).Faithful where
  map_injective {X Y} f g hfg := by
    apply (S.factorProjectiveRestrictedYoneda_faithful D).map_injective
    apply ModuleCat.hom_ext
    ext h
    let e := R.boundaryGeneratorIso
    have happ := congrArg (fun q ↦ q.hom (e.hom ≫ h)) hfg
    have hcancel := congrArg (fun q ↦ e.inv ≫ q) happ
    change h ≫ f = h ≫ g
    change e.inv ≫ ((e.hom ≫ h) ≫ f) =
      e.inv ≫ ((e.hom ≫ h) ≫ g) at hcancel
    simpa only [← Category.assoc, e.inv_hom_id_assoc] using hcancel

/-- Every factor object has a two-term presentation by the reindexed
root-plus-poset boundary generator. -/
theorem boundaryGenerator_presentations
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (X : S.FactorCategory K) :
    Nonempty (FiniteAddGeneratorPresentation
      R.representableData.boundaryGenerator X) := by
  obtain ⟨P⟩ := S.factorProjectiveGenerator_presentations D H X
  exact ⟨P.replaceGenerator R.boundaryGeneratorIso.symm⟩

/-- Restricted Yoneda is full after the boundary generator is reindexed as
the root followed by the projective poset. -/
theorem boundaryRestrictedYoneda_full
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    (preadditiveCoyonedaObj
      R.representableData.boundaryGenerator).Full :=
  preadditiveCoyonedaObj_full_of_finiteAddGeneratorPresentations
    R.representableData.boundaryGenerator
    R.boundaryRestrictedYoneda_faithful
    (R.boundaryGenerator_presentations H)

/-- The concrete primitive representable functor to finite poset spaces is
full. -/
theorem representable_full
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    R.representableData.functor.Full where
  map_surjective f :=
    R.representableData.map_surjective_of_boundaryCoyoneda_full
      (fun t Z ↦ R.precomposition_injective t Z)
      R.boundaryUnit_spans
      (R.boundaryRestrictedYoneda_full H) f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData
