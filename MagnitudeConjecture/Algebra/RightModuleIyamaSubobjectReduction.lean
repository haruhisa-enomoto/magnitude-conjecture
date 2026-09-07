import MagnitudeConjecture.Algebra.RightModuleIyamaBoundaryDefect
import MagnitudeConjecture.Combinatorics.PosetSpaceFullSupport
import MagnitudeConjecture.CategoryTheory.LinearBiproduct

/-!
# Reduction of Iyama realization to subobject closure

Finite biproducts of the distinguished sink represent all full-support poset
spaces.  Since every poset space embeds into its full-support envelope,
essential surjectivity of the primitive incidence functor follows from the
single hereditary-torsionfree statement that its essential image is closed
under subobjects.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

namespace PrimitiveProjectivePosetData

/-- The finite biproduct of copies of the distinguished sink. -/
def sinkBiproduct
    (D : S.PrimitiveMultiplicityInput K) (n : ℕ) :
    S.FactorCategory K :=
  ⨁ fun _ : Fin n ↦ S.factorObject K D.sink

/-- Precomposition from every non-root boundary projective onto a finite
biproduct of sinks is surjective. -/
theorem precomposition_surjective_to_sinkBiproduct
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1) (n : ℕ) (t : T) :
    Function.Surjective
      (R.representableData.precomposition t (sinkBiproduct D n)) := by
  let F : Fin n → S.FactorCategory K :=
    fun _ ↦ S.factorObject K D.sink
  change Function.Surjective
    (R.representableData.precomposition t (⨁ F))
  intro h
  choose g hg using fun j : Fin n ↦
    R.precomposition_surjective_to_sink hsink t
      (h ≫ biproduct.π F j)
  refine ⟨biproduct.lift g, ?_⟩
  dsimp only [PosetSpace.RepresentableData.precomposition]
  apply biproduct.hom_ext
  intro j
  change (R.representableData.unit t ≫ biproduct.lift g) ≫
    biproduct.π F j = h ≫ biproduct.π F j
  dsimp only [PosetSpace.RepresentableData.precomposition] at hg
  have hgj := hg j
  change R.representableData.unit t ≫ g j =
    h ≫ biproduct.π F j at hgj
  calc
    (R.representableData.unit t ≫ biproduct.lift g) ≫
        biproduct.π F j =
      R.representableData.unit t ≫
        (biproduct.lift g ≫ biproduct.π F j) := Category.assoc _ _ _
    _ = R.representableData.unit t ≫ g j := by
      rw [biproduct.lift_π]
    _ = h ≫ biproduct.π F j := hgj

/-- Coordinates on the represented sink biproduct, followed by a basis of
the requested finite-dimensional ambient space. -/
noncomputable def representedSinkBiproductCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1)
    (Y : PosetSpace.Obj k T) :
    (R.representableData.obj
      (sinkBiproduct D (Module.finrank k Y))).carrier ≃ₗ[k] Y := by
  change
    (R.representableData.source ⟶
        sinkBiproduct D (Module.finrank k Y)) ≃ₗ[k] Y
  exact
    (MagnitudeConjecture.CategoryTheory.homBiproductLinearEquiv
      k R.representableData.source
        (fun _ : Fin (Module.finrank k Y) ↦
          S.factorObject K D.sink)).trans
      ((LinearEquiv.piCongrRight fun _ : Fin (Module.finrank k Y) ↦
        R.sinkCoordinateEquiv hsink).trans
          (Module.finBasis k Y).equivFun.symm)

/-- A finite biproduct of the distinguished sink represents the full-support
envelope of any finite poset space. -/
noncomputable def sinkBiproductObjIsoFullSupport
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1)
    (Y : PosetSpace.Obj k T) :
    R.representableData.obj
        (sinkBiproduct D (Module.finrank k Y)) ≅
      PosetSpace.fullSupport Y where
  hom :=
    { linear := R.representedSinkBiproductCoordinateEquiv hsink Y
      map_subspace := by simp [PosetSpace.fullSupport] }
  inv :=
    { linear := (R.representedSinkBiproductCoordinateEquiv hsink Y).symm
      map_subspace := by
        intro t y hy
        obtain ⟨g, hg⟩ :=
          R.precomposition_surjective_to_sinkBiproduct hsink
            (Module.finrank k Y) t
            ((R.representedSinkBiproductCoordinateEquiv hsink Y).symm y)
        exact ⟨g, hg⟩ }
  hom_inv_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact
      (R.representedSinkBiproductCoordinateEquiv hsink Y).symm_apply_apply x
  inv_hom_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact
      (R.representedSinkBiproductCoordinateEquiv hsink Y).apply_symm_apply x

/-- All full-support poset spaces lie in the essential image of the primitive
representable functor. -/
theorem fullSupport_mem_essentialImage
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1)
    (Y : PosetSpace.Obj k T) :
    ∃ X : S.FactorCategory K,
      Nonempty (R.representableData.obj X ≅ PosetSpace.fullSupport Y) :=
  ⟨sinkBiproduct D (Module.finrank k Y),
    ⟨R.sinkBiproductObjIsoFullSupport hsink Y⟩⟩

/-- Iyama essential surjectivity is reduced to its hereditary-torsionfree
content: closure of the restricted-Yoneda image under subobjects. -/
theorem representable_essSurj_of_closedUnderSubobjects
    (R : S.PrimitiveProjectivePosetData D T)
    (hsink : D.multiplicity D.sink.1 = 1)
    (hclosed :
      R.representableData.EssentialImageClosedUnderSubobjects) :
    ∀ Y : PosetSpace.Obj k T,
      ∃ X : S.FactorCategory K,
        Nonempty (R.representableData.obj X ≅ Y) :=
  R.representableData.essSurj_of_fullSupport_of_closedUnderSubobjects
    (R.fullSupport_mem_essentialImage hsink) hclosed

end PrimitiveProjectivePosetData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
