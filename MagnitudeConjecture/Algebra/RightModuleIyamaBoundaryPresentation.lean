import MagnitudeConjecture.Algebra.RightModuleIyamaBoundaryCover
import MagnitudeConjecture.Algebra.RightModuleIncidenceFullness
import MagnitudeConjecture.Combinatorics.PosetSpaceBoundaryPresentation

/-!
# Lifting the two-term boundary presentation

Covering the kernel of the represented boundary cover gives a second
represented boundary object.  Fullness of restricted Yoneda lifts the
relation map between these two objects back to the primitive factor category.
On the poset-space side the original cover is a weak cokernel of that lifted
relation.

This file deliberately stops before the remaining Iyama theorem: constructing
inside the finite strict tau-category a realization whose restricted Yoneda
object is that weak cokernel.
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

/-- The categorical boundary object representing the relation space in the
canonical two-term presentation of `Y`. -/
abbrev categoricalBoundaryRelationObject
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T) : S.FactorCategory K :=
  R.boundaryCoverObject (PosetSpace.boundaryKernel Y)

/-- The relation map transported between the two represented boundary-cover
objects. -/
noncomputable def representedBoundaryRelationMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) :
    R.representableData.obj (R.categoricalBoundaryRelationObject Y) ⟶
      R.representableData.obj (R.boundaryCoverObject Y) :=
  (R.boundaryCoverObjectIso H (PosetSpace.boundaryKernel Y)).hom ≫
    PosetSpace.boundaryRelationMap Y ≫
      (R.boundaryCoverObjectIso H Y).inv

/-- The represented relation is annihilated by the represented boundary
cover. -/
theorem representedBoundaryRelationMap_comp
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) :
    R.representedBoundaryRelationMap H Y ≫
      R.representedBoundaryCoverMap H Y = 0 := by
  simp only [representedBoundaryRelationMap, representedBoundaryCoverMap,
    Category.assoc]
  rw [Iso.inv_hom_id_assoc, PosetSpace.boundaryRelationMap_comp,
    comp_zero]

/-- On the poset-space side, the represented boundary cover is a weak
cokernel of the represented relation map. -/
theorem representedBoundaryCoverMap_weakCokernel
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) {Z : PosetSpace.Obj k T}
    (q : R.representableData.obj (R.boundaryCoverObject Y) ⟶ Z)
    (hq : R.representedBoundaryRelationMap H Y ≫ q = 0) :
    ∃ s : Y ⟶ Z, R.representedBoundaryCoverMap H Y ≫ s = q := by
  let e₁ := R.boundaryCoverObjectIso H (PosetSpace.boundaryKernel Y)
  let e₀ := R.boundaryCoverObjectIso H Y
  have hrelation : PosetSpace.boundaryRelationMap Y ≫ e₀.inv ≫ q = 0 := by
    apply (cancel_epi e₁.hom).1
    simpa only [e₁, e₀, representedBoundaryRelationMap,
      Category.assoc, comp_zero] using hq
  obtain ⟨s, hs⟩ := PosetSpace.boundaryCoverMap_weakCokernel
    Y (e₀.inv ≫ q) hrelation
  refine ⟨s, ?_⟩
  simp only [representedBoundaryCoverMap, Category.assoc]
  rw [hs, Iso.hom_inv_id_assoc]

/-- Fullness lifts the relation map of the boundary presentation to the
primitive factor category. -/
noncomputable def liftedBoundaryRelationMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) :
    R.categoricalBoundaryRelationObject Y ⟶ R.boundaryCoverObject Y :=
  Classical.choose
    ((R.representable_full H).map_surjective
      (R.representedBoundaryRelationMap H Y))

/-- Restricted Yoneda sends the lifted categorical relation to the explicit
relation map between the represented boundary covers. -/
theorem map_liftedBoundaryRelationMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) :
    R.representableData.map (R.liftedBoundaryRelationMap H Y) =
      R.representedBoundaryRelationMap H Y :=
  Classical.choose_spec
    ((R.representable_full H).map_surjective
      (R.representedBoundaryRelationMap H Y))

/-- The represented boundary cover is therefore a weak cokernel of the image
of the lifted categorical relation. -/
theorem representedBoundaryCoverMap_weakCokernel_lifted
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) {Z : PosetSpace.Obj k T}
    (q : R.representableData.obj (R.boundaryCoverObject Y) ⟶ Z)
    (hq : R.representableData.map (R.liftedBoundaryRelationMap H Y) ≫ q = 0) :
    ∃ s : Y ⟶ Z, R.representedBoundaryCoverMap H Y ≫ s = q := by
  rw [R.map_liftedBoundaryRelationMap H Y] at hq
  exact R.representedBoundaryCoverMap_weakCokernel H Y q hq

end PrimitiveProjectivePosetData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
