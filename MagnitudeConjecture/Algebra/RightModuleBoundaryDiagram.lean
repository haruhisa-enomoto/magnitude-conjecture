import MagnitudeConjecture.Algebra.RightModuleIncidenceCategory
import MagnitudeConjecture.Combinatorics.PosetSpaceBoundarySocle

/-!
# Restricted Yoneda as a boundary diagram

The manuscript treats modules over the category of tau-projective boundary
objects as contravariant diagrams on the augmented incidence poset.  This
file makes that identification literal for the restricted Yoneda objects of
the primitive factor.

At a boundary point `q`, the diagram has value `Hom(P_q,X)`.  Along
`q ≤ r`, its structure map is precomposition with the normalized incidence
morphism `P_q ⟶ P_r`.  The resulting diagram is naturally isomorphic to the
boundary diagram of the concrete represented poset space.  In particular,
its maps into the root are injective and it has no nonzero subdiagram
supported away from the root.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.PosetSpace
open Opposite

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

/-- The boundary-category form of restricted Yoneda at a factor object. -/
def incidenceRestrictedYonedaDiagram
    (R : S.PrimitiveProjectivePosetData D T) (X : S.FactorCategory K) :
    (BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj q := ModuleCat.of k
    (R.representableData.boundaryFamily q.unop.toOption ⟶ X)
  map {q r} f := ModuleCat.ofHom
    { toFun := fun h ↦
        R.boundaryIncidenceMap
            ((boundaryLE_toOption_iff_le r.unop q.unop).2
              (le_of_op_hom f)) ≫ h
      map_add' := fun h g ↦ by simp
      map_smul' := fun c h ↦ by simp }
  map_id q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change R.boundaryIncidenceMap
        ((boundaryLE_toOption_iff_le q.unop q.unop).2
          (le_of_op_hom (𝟙 q))) ≫ h = h
    rw [show ((boundaryLE_toOption_iff_le q.unop q.unop).2
      (le_of_op_hom (𝟙 q))) = boundaryLE_refl q.unop.toOption from
        Subsingleton.elim _ _]
    simp
  map_comp {q r s} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    let hrs : boundaryLE s.unop.toOption r.unop.toOption :=
      (boundaryLE_toOption_iff_le s.unop r.unop).2 (le_of_op_hom g)
    let hrq : boundaryLE r.unop.toOption q.unop.toOption :=
      (boundaryLE_toOption_iff_le r.unop q.unop).2 (le_of_op_hom f)
    change R.boundaryIncidenceMap
        ((boundaryLE_toOption_iff_le s.unop q.unop).2
          (le_of_op_hom (f ≫ g))) ≫ h =
      R.boundaryIncidenceMap hrs ≫
        (R.boundaryIncidenceMap hrq ≫ h)
    rw [← Category.assoc, R.boundaryIncidenceMap_comp hrs hrq]

/-- Postcomposition gives the morphism of restricted-Yoneda boundary
diagrams induced by a factor morphism. -/
def incidenceRestrictedYonedaDiagramMap
    (R : S.PrimitiveProjectivePosetData D T)
    {X Y : S.FactorCategory K} (f : X ⟶ Y) :
    R.incidenceRestrictedYonedaDiagram X ⟶
      R.incidenceRestrictedYonedaDiagram Y where
  app q := ModuleCat.ofHom
    { toFun := fun h ↦ h ≫ f
      map_add' := fun h g ↦ by simp
      map_smul' := fun c h ↦ by simp }
  naturality q r g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    let b := R.boundaryIncidenceMap
      ((boundaryLE_toOption_iff_le r.unop q.unop).2
        (le_of_op_hom g))
    change (b ≫ h) ≫ f = b ≫ (h ≫ f)
    exact Category.assoc _ _ _

/-- Restricted Yoneda on the boundary category is functorial in the factor
object. -/
def incidenceRestrictedYonedaDiagramFunctor
    (R : S.PrimitiveProjectivePosetData D T) :
    S.FactorCategory K ⥤
      ((BoundaryIndex T)ᵒᵖ ⥤ ModuleCat.{u} k) where
  obj := R.incidenceRestrictedYonedaDiagram
  map := R.incidenceRestrictedYonedaDiagramMap
  map_id X := by
    ext q h
    change h ≫ 𝟙 X = h
    simp
  map_comp f g := by
    ext q h
    change h ≫ (f ≫ g) = (h ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm

/-- Precomposition with `P ⟶ P_t` identifies `Hom(P_t,X)` with its range
inside `Hom(P,X)`. -/
def representedBoundaryLinearEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    (X : S.FactorCategory K) (t : T) :
    (R.projective t ⟶ X) ≃ₗ[k]
      LinearMap.range (R.representableData.precomposition t X) :=
  LinearEquiv.ofBijective
    (R.representableData.precomposition t X).rangeRestrict
    ⟨(LinearMap.injective_rangeRestrict_iff _).2
        (R.precomposition_injective t X),
      (R.representableData.precomposition t X).surjective_rangeRestrict⟩

/-- Componentwise identification of boundary restricted Yoneda with the
boundary diagram of the represented poset space. -/
def incidenceRestrictedYonedaDiagramComponentIso
    (R : S.PrimitiveProjectivePosetData D T)
    (X : S.FactorCategory K) (q : (BoundaryIndex T)ᵒᵖ) :
    (R.incidenceRestrictedYonedaDiagram X).obj q ≅
      (boundaryDiagram k T (R.representableData.obj X)).obj q := by
  cases q using Opposite.rec with
  | _ q =>
      cases q with
      | root => exact Iso.refl _
      | nonroot t =>
          exact (R.representedBoundaryLinearEquiv X t).toModuleIso

/-- The boundary-category restricted Yoneda diagram is the same diagram as
the one obtained from the concrete represented poset space. -/
def incidenceRestrictedYonedaDiagramIso
    (R : S.PrimitiveProjectivePosetData D T)
    (X : S.FactorCategory K) :
    R.incidenceRestrictedYonedaDiagram X ≅
      boundaryDiagram k T (R.representableData.obj X) :=
  NatIso.ofComponents (R.incidenceRestrictedYonedaDiagramComponentIso X) (by
    intro q r f
    cases q using Opposite.rec with
    | _ q =>
        cases r using Opposite.rec with
        | _ r =>
            have hrq : r ≤ q := le_of_op_hom f
            cases q with
            | root =>
                cases r with
                | root =>
                    rw [show f = 𝟙 _ from Subsingleton.elim _ _]
                    simp
                | nonroot t => exact False.elim hrq
            | nonroot s =>
                cases r with
                | root =>
                    rw [show f = boundaryRootArrow T s from
                      Subsingleton.elim _ _]
                    apply ModuleCat.hom_ext
                    apply LinearMap.ext
                    intro h
                    rfl
                | nonroot t =>
                    have hst : s ≤ t := hrq
                    rw [show f = boundaryNonrootArrow T hst from
                      Subsingleton.elim _ _]
                    apply ModuleCat.hom_ext
                    apply LinearMap.ext
                    intro h
                    apply Subtype.ext
                    change R.unit t ≫ (R.incidenceMap hst ≫ h) =
                      R.unit s ≫ h
                    rw [← Category.assoc, R.unit_comp_incidenceMap hst])

/-- The preceding objectwise isomorphisms are natural in the represented
factor object. -/
def incidenceRestrictedYonedaDiagramNatIso
    (R : S.PrimitiveProjectivePosetData D T) :
    R.incidenceRestrictedYonedaDiagramFunctor ≅
      R.representableData.functor ⋙ boundaryDiagramFunctor k T :=
  NatIso.ofComponents R.incidenceRestrictedYonedaDiagramIso (by
    intro X Y f
    ext q h
    cases q using Opposite.rec with
    | _ q =>
        cases q with
        | root => rfl
        | nonroot t =>
            apply Subtype.ext
            change R.unit t ≫ (h ≫ f) = (R.unit t ≫ h) ≫ f
            exact (Category.assoc _ _ _).symm)

/-- Every restricted-Yoneda boundary diagram has finite values and
injective maps into the root. -/
theorem incidenceRestrictedYonedaDiagram_isFiniteInjective
    (R : S.PrimitiveProjectivePosetData D T)
    (X : S.FactorCategory K) :
    IsFiniteInjectiveBoundaryDiagram k T
      (R.incidenceRestrictedYonedaDiagram X) := by
  constructor
  · intro q
    change Module.Finite k
      (R.representableData.boundaryFamily q.toOption ⟶ X)
    infer_instance
  · intro t
    change Function.Injective (R.representableData.precomposition t X)
    exact R.precomposition_injective t X

/-- Equivalently, a restricted-Yoneda boundary diagram has no nonzero
subdiagram supported away from the root. -/
theorem incidenceRestrictedYonedaDiagram_no_supportedAwaySubdiagram
    (R : S.PrimitiveProjectivePosetData D T)
    (X : S.FactorCategory K)
    (N : BoundarySubdiagram k T (R.incidenceRestrictedYonedaDiagram X))
    (hN : N.SupportedAwayFromRoot) : N.IsZero := by
  exact
    (BoundarySubdiagram.injective_rootMaps_iff_no_supportedAwaySubdiagram
      (k := k) (T := T) (R.incidenceRestrictedYonedaDiagram X)).mp
      (R.incidenceRestrictedYonedaDiagram_isFiniteInjective X).2 N hN

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData
