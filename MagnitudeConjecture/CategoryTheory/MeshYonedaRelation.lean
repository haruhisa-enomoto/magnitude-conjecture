import MagnitudeConjecture.CategoryTheory.MeshSimplePresentation
import MagnitudeConjecture.CategoryTheory.LinearYonedaRelation

/-! # Yoneda reflection for a finite mesh presentation -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u v w

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q]
  [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable (T : RightMeshData Q)

/-- Reflect the translation relation before specializing the mesh data to an
algebra's standard form. -/
theorem yoneda_reflected_relation
    (hP : T.FiniteContravariantRepresentables (k := k))
    (z : {z : Q // z ∉ T.projective}) (x : Q)
    (h : T.incomingCoefficientFiniteModule (k := k) hP z.1 ⟶
      T.contravariantRepresentableFiniteModule (k := k) hP x)
    (hh : T.translationMapFinite (k := k) hP z ≫ h = 0) :
    let Y := linearYoneda k (T.VertexCategory (k := k))
    (∑ a : IncomingArrow z.1,
      InducedCategory.homMk
        (T.incomingArrowHom (k := k)
          (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1)) ≫
      Y.preimage ((T.incomingSummandInclusionFinite (k := k) hP z.1 a ≫ h).hom.hom))
      = 0 := by
  classical
  let Y := linearYoneda k (T.VertexCategory (k := k))
  exact linearYoneda_reflect_sum_relation
    (fun a : IncomingArrow z.1 ↦ (show T.VertexCategory (k := k) from a.1))
    (fun a ↦ InducedCategory.homMk
      (T.incomingArrowHom (k := k)
        (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1)))
    (fun a ↦ Y.preimage
      ((T.incomingSummandInclusionFinite (k := k) hP z.1 a ≫ h).hom.hom))
    (T.incomingCoefficientFunctor (k := k) z.1)
    (fun a ↦ T.incomingSummandInclusion (k := k) z.1 a)
    h.hom.hom (T.translationMap (k := k) z)
    (T.translationMap_eq_sum_paired_incoming (k := k) z)
    (fun a ↦ Y.map_preimage _)
    (congrArg (fun q ↦ q.hom.hom) hh)

end MagnitudeConjecture.MeshCategory.RightMeshData
