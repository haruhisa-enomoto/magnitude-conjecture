import MagnitudeConjecture.Algebra.StringArrowRightIdealObjectCoordinate

/-!
# The global range of a represented string-arrow map

The represented arrow range is identified with the product of its vertexwise
left-composition ranges.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The global represented arrow range is the product of its vertexwise
left-composition ranges. -/
def representedArrowRangeCoordinateLinearEquiv
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    LinearMap.range (P.representedArrowKLinearMap a) ≃ₗ[k]
      (∀ X : Category P.toPresentation.relations,
        LinearMap.range (P.leftArrowCompositionLinearMapObj a X)) := by
  let ex := P.representedVertexCoordinateLinearEquiv x
  let ey := P.representedVertexCoordinateLinearEquiv y
  let t := P.representedArrowKLinearMap a
  let L := fun X : Category P.toPresentation.relations ↦
    P.leftArrowCompositionLinearMapObj a X
  let toFun : LinearMap.range t →
      (∀ X : Category P.toPresentation.relations, LinearMap.range (L X)) :=
    fun g X ↦ ⟨ey g.1 X, by
      rcases g.2 with ⟨f, hf⟩
      refine ⟨ex f X, ?_⟩
      rw [← hf]
      exact P.representedVertexCoordinateLinearEquiv_arrow a f X⟩
  let preimage (g : ∀ X : Category P.toPresentation.relations,
      LinearMap.range (L X)) (X : Category P.toPresentation.relations) :=
    Classical.choose (g X).2
  have preimage_spec (g : ∀ X : Category P.toPresentation.relations,
      LinearMap.range (L X)) (X : Category P.toPresentation.relations) :
      L X (preimage g X) = (g X).1 :=
    Classical.choose_spec (g X).2
  let invFun : (∀ X : Category P.toPresentation.relations,
      LinearMap.range (L X)) → LinearMap.range t :=
    fun g ↦ ⟨ey.symm (fun X ↦ (g X).1), by
      refine ⟨ex.symm (preimage g), ?_⟩
      apply ey.injective
      funext X
      rw [ey.apply_symm_apply]
      change ey (t (ex.symm (preimage g))) X = (g X).1
      rw [P.representedVertexCoordinateLinearEquiv_arrow,
        ex.apply_symm_apply]
      exact preimage_spec g X⟩
  refine
    { toEquiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := ?_
          right_inv := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro g
    apply Subtype.ext
    apply ey.injective
    change ey (ey.symm (fun z ↦ ey g.1 z)) = ey g.1
    rw [ey.apply_symm_apply]
  · intro g
    funext X
    apply Subtype.ext
    change ey (ey.symm (fun W ↦ (g W).1)) X = (g X).1
    rw [ey.apply_symm_apply]
  · intro g h
    funext X
    apply Subtype.ext
    exact congrFun (ey.map_add g.1 h.1) X
  · intro r g
    funext X
    apply Subtype.ext
    exact congrFun (ey.map_smul r g.1) X

end StringPresentation

end MagnitudeConjecture.BoundQuiver
