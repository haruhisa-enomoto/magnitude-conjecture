import MagnitudeConjecture.Algebra.RightModuleIyamaSubobjectReduction
import MagnitudeConjecture.Combinatorics.PosetSpaceBoundaryCover
import MagnitudeConjecture.CategoryTheory.LinearBiproduct

/-!
# Representing the strict boundary-generator cover

The explicit strict cover of a finite poset space is represented by a finite
biproduct of the distinguished source and the non-root tau-projectives.  This
supplies the degree-zero object in a boundary-projective presentation for
Iyama's minimal realization.  Applying the same construction to its kernel
will supply the relation object; the remaining step is to lift that relation
map and construct its categorical weak cokernel/minimal realization.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

namespace PrimitiveProjectivePosetData

/-- Coordinates used for the root and point summands of the strict cover. -/
abbrev boundaryCoverIndex (Y : PosetSpace.Obj k T) :=
  (Fin (Module.finrank k Y)) ⊕
    (Σ t : T, Fin (Module.finrank k (Y.subspace t)))

/-- The categorical family whose root summands are copies of `P` and whose
point summands over `t` are copies of `P_t`. -/
def boundaryCoverFamily
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T) :
    boundaryCoverIndex Y → S.FactorCategory K
  | Sum.inl _ => R.representableData.source
  | Sum.inr p => R.projective p.1

/-- The object representing the explicit boundary-generator cover. -/
abbrev boundaryCoverObject
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T) : S.FactorCategory K :=
  ⨁ R.boundaryCoverFamily Y

/-- Projection from the categorical cover to one root copy. -/
def boundaryCoverRootProjection
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T) (i : Fin (Module.finrank k Y)) :
    R.boundaryCoverObject Y ⟶ R.representableData.source :=
  biproduct.π (R.boundaryCoverFamily Y) (Sum.inl i)

/-- Projection from the categorical cover to one point copy. -/
def boundaryCoverPointProjection
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T) (t : T)
    (i : Fin (Module.finrank k (Y.subspace t))) :
    R.boundaryCoverObject Y ⟶ R.projective t :=
  biproduct.π (R.boundaryCoverFamily Y) (Sum.inr ⟨t, i⟩)

/-- Boundary Hom coordinates converted into the carrier coordinates of the
explicit root-plus-point cover. -/
noncomputable def boundaryCoverCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T) :
    (∀ j : boundaryCoverIndex Y,
      R.representableData.source ⟶ R.boundaryCoverFamily Y j) ≃ₗ[k]
      PosetSpace.boundaryCoverCarrier Y where
  toFun f :=
    ((Module.finBasis k Y).equivFun.symm
        (fun i ↦ R.sourceCoordinateEquiv (f (Sum.inl i))),
      fun t ↦ (Module.finBasis k (Y.subspace t)).equivFun.symm
        (fun i ↦ R.unitCoordinateEquiv t
          (f (Sum.inr ⟨t, i⟩))))
  invFun x
    | Sum.inl i =>
        R.sourceCoordinateEquiv.symm
          ((Module.finBasis k Y).equivFun x.1 i)
    | Sum.inr p =>
        (R.unitCoordinateEquiv p.1).symm
          ((Module.finBasis k (Y.subspace p.1)).equivFun (x.2 p.1) p.2)
  left_inv f := by
    funext j
    cases j with
    | inl i =>
        change R.sourceCoordinateEquiv.symm
            ((Module.finBasis k Y).equivFun
              ((Module.finBasis k Y).equivFun.symm
                (fun i ↦ R.sourceCoordinateEquiv (f (Sum.inl i)))) i) = _
        rw [LinearEquiv.apply_symm_apply]
        exact R.sourceCoordinateEquiv.symm_apply_apply _
    | inr p =>
        rcases p with ⟨t, i⟩
        change (R.unitCoordinateEquiv t).symm
            ((Module.finBasis k (Y.subspace t)).equivFun
              ((Module.finBasis k (Y.subspace t)).equivFun.symm
                (fun i ↦ R.unitCoordinateEquiv t
                  (f (Sum.inr ⟨t, i⟩)))) i) = _
        rw [LinearEquiv.apply_symm_apply]
        exact (R.unitCoordinateEquiv t).symm_apply_apply _
  right_inv x := by
    apply Prod.ext
    · exact (Module.finBasis k Y).equivFun.injective (by
        funext i
        simp only [LinearEquiv.apply_symm_apply])
    · funext t
      exact (Module.finBasis k (Y.subspace t)).equivFun.injective (by
        funext i
        simp only [LinearEquiv.apply_symm_apply])
  map_add' f g := by
    apply Prod.ext
    · change (Module.finBasis k Y).equivFun.symm
          (fun i ↦ R.sourceCoordinateEquiv
            (f (Sum.inl i) + g (Sum.inl i))) =
        (Module.finBasis k Y).equivFun.symm
            (fun i ↦ R.sourceCoordinateEquiv (f (Sum.inl i))) +
          (Module.finBasis k Y).equivFun.symm
            (fun i ↦ R.sourceCoordinateEquiv (g (Sum.inl i)))
      rw [← LinearEquiv.map_add]
      congr 1
      funext i
      exact R.sourceCoordinateEquiv.map_add _ _
    · funext t
      change (Module.finBasis k (Y.subspace t)).equivFun.symm
          (fun i ↦ R.unitCoordinateEquiv t
            (f (Sum.inr ⟨t, i⟩) + g (Sum.inr ⟨t, i⟩))) =
        (Module.finBasis k (Y.subspace t)).equivFun.symm
            (fun i ↦ R.unitCoordinateEquiv t
              (f (Sum.inr ⟨t, i⟩))) +
          (Module.finBasis k (Y.subspace t)).equivFun.symm
            (fun i ↦ R.unitCoordinateEquiv t
              (g (Sum.inr ⟨t, i⟩)))
      rw [← LinearEquiv.map_add]
      congr 1
      funext i
      exact (R.unitCoordinateEquiv t).map_add _ _
  map_smul' c f := by
    apply Prod.ext
    · change (Module.finBasis k Y).equivFun.symm
          (fun i ↦ R.sourceCoordinateEquiv (c • f (Sum.inl i))) =
        c • (Module.finBasis k Y).equivFun.symm
          (fun i ↦ R.sourceCoordinateEquiv (f (Sum.inl i)))
      rw [← LinearEquiv.map_smul]
      congr 1
      funext i
      exact R.sourceCoordinateEquiv.map_smul c _
    · funext t
      change (Module.finBasis k (Y.subspace t)).equivFun.symm
          (fun i ↦ R.unitCoordinateEquiv t
            (c • f (Sum.inr ⟨t, i⟩))) =
        c • (Module.finBasis k (Y.subspace t)).equivFun.symm
          (fun i ↦ R.unitCoordinateEquiv t
            (f (Sum.inr ⟨t, i⟩)))
      rw [← LinearEquiv.map_smul]
      congr 1
      funext i
      exact (R.unitCoordinateEquiv t).map_smul c _

/-- The represented carrier of the categorical cover has the explicit
root-plus-point coordinates. -/
noncomputable def representedBoundaryCoverLinearEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T) :
    (R.representableData.obj (R.boundaryCoverObject Y)).carrier ≃ₗ[k]
      PosetSpace.boundaryCoverCarrier Y := by
  change (R.representableData.source ⟶
      R.boundaryCoverObject Y) ≃ₗ[k]
    PosetSpace.boundaryCoverCarrier Y
  exact
    (homBiproductLinearEquiv k R.representableData.source
      (R.boundaryCoverFamily Y)).trans
        (R.boundaryCoverCoordinateEquiv Y)

@[simp]
theorem representedBoundaryCoverLinearEquiv_apply_root
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T)
    (f : (R.representableData.obj (R.boundaryCoverObject Y)).carrier)
    (i : Fin (Module.finrank k Y)) :
    (Module.finBasis k Y).equivFun
        ((R.representedBoundaryCoverLinearEquiv Y f).1) i =
      R.sourceCoordinateEquiv
        (f ≫ R.boundaryCoverRootProjection Y i) := by
  change (Module.finBasis k Y).equivFun
      ((Module.finBasis k Y).equivFun.symm
        (fun i ↦ R.sourceCoordinateEquiv
          (f ≫ R.boundaryCoverRootProjection Y i))) i = _
  rw [LinearEquiv.apply_symm_apply]

@[simp]
theorem representedBoundaryCoverLinearEquiv_apply_point
    (R : S.PrimitiveProjectivePosetData D T)
    (Y : PosetSpace.Obj k T)
    (f : (R.representableData.obj (R.boundaryCoverObject Y)).carrier)
    (t : T) (i : Fin (Module.finrank k (Y.subspace t))) :
    (Module.finBasis k (Y.subspace t)).equivFun
        ((R.representedBoundaryCoverLinearEquiv Y f).2 t) i =
      R.unitCoordinateEquiv t
        (f ≫ R.boundaryCoverPointProjection Y t i) := by
  change (Module.finBasis k (Y.subspace t)).equivFun
      ((Module.finBasis k (Y.subspace t)).equivFun.symm
        (fun i ↦ R.unitCoordinateEquiv t
          (f ≫ R.boundaryCoverPointProjection Y t i))) i = _
  rw [LinearEquiv.apply_symm_apply]

/-- Restricted Yoneda sends the categorical boundary-cover object to the
explicit strict boundary cover. -/
noncomputable def boundaryCoverObjectIso
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) :
    R.representableData.obj (R.boundaryCoverObject Y) ≅
      PosetSpace.boundaryCover Y where
  hom :=
    { linear := (R.representedBoundaryCoverLinearEquiv Y).toLinearMap
      map_subspace := by
        classical
        intro r x hx
        change x ∈ LinearMap.range
          (R.representableData.precomposition r
            (R.boundaryCoverObject Y)) at hx
        change R.representedBoundaryCoverLinearEquiv Y x ∈
          PosetSpace.boundaryCoverSubspace Y r
        obtain ⟨h, rfl⟩ := hx
        change R.representableData.projective r ⟶
          R.boundaryCoverObject Y at h
        constructor
        · apply (Module.finBasis k Y).equivFun.injective
          funext i
          rw [R.representedBoundaryCoverLinearEquiv_apply_root]
          dsimp only [PosetSpace.RepresentableData.precomposition]
          change R.sourceCoordinateEquiv
              ((R.unit r ≫ h) ≫
                R.boundaryCoverRootProjection Y i) = _
          have hzero := R.eq_zero_of_projectiveHom_to_source H r
            (h ≫ R.boundaryCoverRootProjection Y i)
          have htotal : (R.unit r ≫ h) ≫
              R.boundaryCoverRootProjection Y i = 0 := by
            calc
              _ = R.unit r ≫
                  (h ≫ R.boundaryCoverRootProjection Y i) :=
                Category.assoc _ _ _
              _ = R.unit r ≫ 0 :=
                congrArg (fun q ↦ R.unit r ≫ q) hzero
              _ = 0 := comp_zero
          calc
            R.sourceCoordinateEquiv
                ((R.unit r ≫ h) ≫
                  R.boundaryCoverRootProjection Y i) =
                R.sourceCoordinateEquiv 0 :=
              congrArg R.sourceCoordinateEquiv htotal
            _ = (Module.finBasis k Y).equivFun 0 i := by simp
        · intro t htr
          apply (Module.finBasis k (Y.subspace t)).equivFun.injective
          funext i
          rw [R.representedBoundaryCoverLinearEquiv_apply_point]
          dsimp only [PosetSpace.RepresentableData.precomposition]
          change R.unitCoordinateEquiv t
              ((R.unit r ≫ h) ≫
                R.boundaryCoverPointProjection Y t i) = _
          have hzero := R.eq_zero_of_projectiveHom_of_not_le htr
            (h ≫ R.boundaryCoverPointProjection Y t i)
          have htotal : (R.unit r ≫ h) ≫
              R.boundaryCoverPointProjection Y t i = 0 := by
            calc
              _ = R.unit r ≫
                  (h ≫ R.boundaryCoverPointProjection Y t i) :=
                Category.assoc _ _ _
              _ = R.unit r ≫ 0 :=
                congrArg (fun q ↦ R.unit r ≫ q) hzero
              _ = 0 := comp_zero
          calc
            R.unitCoordinateEquiv t
                ((R.unit r ≫ h) ≫
                  R.boundaryCoverPointProjection Y t i) =
                R.unitCoordinateEquiv t 0 :=
              congrArg (R.unitCoordinateEquiv t) htotal
            _ = (Module.finBasis k (Y.subspace t)).equivFun 0 i := by simp }
  inv :=
    { linear := (R.representedBoundaryCoverLinearEquiv Y).symm.toLinearMap
      map_subspace := by
        classical
        intro r x hx
        change x ∈ PosetSpace.boundaryCoverSubspace Y r at hx
        change (R.representedBoundaryCoverLinearEquiv Y).symm x ∈
          LinearMap.range (R.representableData.precomposition r
            (R.boundaryCoverObject Y))
        let component : ∀ j : boundaryCoverIndex Y,
            R.representableData.projective r ⟶ R.boundaryCoverFamily Y j
          | Sum.inl _ => 0
          | Sum.inr p => if hpr : p.1 ≤ r then
              ((Module.finBasis k (Y.subspace p.1)).equivFun
                  (x.2 p.1) p.2) • R.incidenceMap hpr
            else 0
        let h : R.representableData.projective r ⟶
            R.boundaryCoverObject Y :=
          biproduct.lift component
        refine ⟨h, ?_⟩
        apply (R.representedBoundaryCoverLinearEquiv Y).injective
        rw [LinearEquiv.apply_symm_apply]
        apply Prod.ext
        · apply (Module.finBasis k Y).equivFun.injective
          funext i
          rw [R.representedBoundaryCoverLinearEquiv_apply_root]
          dsimp only [PosetSpace.RepresentableData.precomposition]
          change R.sourceCoordinateEquiv
              ((R.unit r ≫ h) ≫
                R.boundaryCoverRootProjection Y i) = _
          have hcomponent : h ≫ R.boundaryCoverRootProjection Y i = 0 := by
            change biproduct.lift component ≫
              biproduct.π (R.boundaryCoverFamily Y) (Sum.inl i) = 0
            rw [biproduct.lift_π]
          have htotal : (R.unit r ≫ h) ≫
              R.boundaryCoverRootProjection Y i = 0 := by
            calc
              _ = R.unit r ≫
                  (h ≫ R.boundaryCoverRootProjection Y i) :=
                Category.assoc _ _ _
              _ = R.unit r ≫ 0 :=
                congrArg (fun q ↦ R.unit r ≫ q) hcomponent
              _ = 0 := comp_zero
          calc
            R.sourceCoordinateEquiv
                ((R.unit r ≫ h) ≫
                  R.boundaryCoverRootProjection Y i) =
                R.sourceCoordinateEquiv 0 :=
              congrArg R.sourceCoordinateEquiv htotal
            _ = (Module.finBasis k Y).equivFun x.1 i := by
              rw [R.sourceCoordinateEquiv.map_zero, hx.1]
              exact congrFun
                (Module.finBasis k Y).equivFun.map_zero.symm i
        · funext t
          apply (Module.finBasis k (Y.subspace t)).equivFun.injective
          funext i
          rw [R.representedBoundaryCoverLinearEquiv_apply_point]
          dsimp only [PosetSpace.RepresentableData.precomposition]
          change R.unitCoordinateEquiv t
              ((R.unit r ≫ h) ≫
                R.boundaryCoverPointProjection Y t i) = _
          have hcomponent : h ≫ R.boundaryCoverPointProjection Y t i =
              component (Sum.inr ⟨t, i⟩) := by
            change biproduct.lift component ≫
              biproduct.π (R.boundaryCoverFamily Y)
                (Sum.inr ⟨t, i⟩) = _
            rw [biproduct.lift_π]
          have htotal : (R.unit r ≫ h) ≫
              R.boundaryCoverPointProjection Y t i =
                R.unit r ≫ component (Sum.inr ⟨t, i⟩) := by
            calc
              _ = R.unit r ≫
                  (h ≫ R.boundaryCoverPointProjection Y t i) :=
                Category.assoc _ _ _
              _ = _ := congrArg (fun q ↦ R.unit r ≫ q) hcomponent
          calc
            R.unitCoordinateEquiv t
                ((R.unit r ≫ h) ≫
                  R.boundaryCoverPointProjection Y t i) =
                R.unitCoordinateEquiv t
                  (R.unit r ≫ component (Sum.inr ⟨t, i⟩)) :=
              congrArg (R.unitCoordinateEquiv t) htotal
            _ = (Module.finBasis k (Y.subspace t)).equivFun (x.2 t) i := by
              by_cases htr : t ≤ r
              · let c := (Module.finBasis k (Y.subspace t)).equivFun
                    (x.2 t) i
                have hc : component (Sum.inr ⟨t, i⟩) =
                    c • R.incidenceMap htr := by
                  dsimp only [component]
                  rw [dif_pos htr]
                have hcomp : R.unit r ≫ component (Sum.inr ⟨t, i⟩) =
                    c • R.unit t := by
                  calc
                    _ = R.unit r ≫ (c • R.incidenceMap htr) :=
                      congrArg (fun q ↦ R.unit r ≫ q) hc
                    _ = c • (R.unit r ≫ R.incidenceMap htr) :=
                      Linear.comp_smul _ _ _ _ _ _
                    _ = _ := congrArg (c • ·)
                      (R.unit_comp_incidenceMap htr)
                calc
                  R.unitCoordinateEquiv t
                      (R.unit r ≫ component (Sum.inr ⟨t, i⟩)) =
                      R.unitCoordinateEquiv t (c • R.unit t) :=
                    congrArg (R.unitCoordinateEquiv t) hcomp
                  _ = c := by
                    rw [← R.unitCoordinateEquiv_symm_apply t,
                      LinearEquiv.apply_symm_apply]
              · have hc : component (Sum.inr ⟨t, i⟩) = 0 := by
                  dsimp only [component]
                  rw [dif_neg htr]
                have hcomp : R.unit r ≫ component (Sum.inr ⟨t, i⟩) =
                    0 := by
                  calc
                    _ = R.unit r ≫ 0 :=
                      congrArg (fun q ↦ R.unit r ≫ q) hc
                    _ = 0 := comp_zero
                calc
                  R.unitCoordinateEquiv t
                      (R.unit r ≫ component (Sum.inr ⟨t, i⟩)) =
                      R.unitCoordinateEquiv t 0 :=
                    congrArg (R.unitCoordinateEquiv t) hcomp
                  _ = (Module.finBasis k (Y.subspace t)).equivFun
                      (x.2 t) i := by
                    rw [(R.unitCoordinateEquiv t).map_zero, hx.2 t htr]
                    exact congrFun (Module.finBasis k
                      (Y.subspace t)).equivFun.map_zero.symm i }
  hom_inv_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact (R.representedBoundaryCoverLinearEquiv Y).symm_apply_apply x
  inv_hom_id := by
    apply PosetSpace.Hom.ext
    apply LinearMap.ext
    intro x
    exact (R.representedBoundaryCoverLinearEquiv Y).apply_symm_apply x

/-- The explicit represented cover map. -/
noncomputable def representedBoundaryCoverMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) :
    R.representableData.obj (R.boundaryCoverObject Y) ⟶ Y :=
  (R.boundaryCoverObjectIso H Y).hom ≫ PosetSpace.boundaryCoverMap Y

/-- Every finite poset space admits a represented boundary-surjective cover
assembled only from the distinguished source and non-root tau-projectives. -/
theorem representedBoundaryCoverMap_boundarySurjective
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (Y : PosetSpace.Obj k T) :
    PosetSpace.BoundarySurjective (R.representedBoundaryCoverMap H Y) :=
  (PosetSpace.boundarySurjective_iso_hom
      (R.boundaryCoverObjectIso H Y)).comp
    (PosetSpace.boundaryCoverMap_boundarySurjective Y)

end PrimitiveProjectivePosetData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
