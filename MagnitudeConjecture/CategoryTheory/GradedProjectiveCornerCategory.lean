import MagnitudeConjecture.CategoryTheory.GradedProjectiveRepresentation
import MagnitudeConjecture.Graded.ProjectiveCorners

/-! # Homogeneous corner coordinates on the degree-labelled projective category -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type v} (e : ι → A) (he0 : ∀ i, e i ∈ R.component 0)
variable (he : ∀ i, e i * e i = e i)
include he

/-- Morphisms between shifted projectives are the manuscript's homogeneous corner spaces. -/
def principalDegreeHomEquiv (p q : PrincipalDegreeCategory R hmul e he0) :
    (p ⟶ q) ≃ₗ[k] cornerComponent R (e p.1) (e q.1) (p.2 - q.2) where
  toFun f := principalCornerHomEquiv R hmul (e p.1) (e q.1)
    (he p.1) (he q.1) (he0 p.1) (he0 q.1) (p.2 - q.2) f.hom
  invFun a := InducedCategory.homMk ((principalCornerHomEquiv R hmul (e p.1) (e q.1)
    (he p.1) (he q.1) (he0 p.1) (he0 q.1) (p.2 - q.2)).symm a)
  left_inv f := by
    apply InducedCategory.hom_ext
    exact (principalCornerHomEquiv R hmul (e p.1) (e q.1)
      (he p.1) (he q.1) (he0 p.1) (he0 q.1) (p.2 - q.2)).symm_apply_apply f.hom
  right_inv a := (principalCornerHomEquiv R hmul (e p.1) (e q.1)
    (he p.1) (he q.1) (he0 p.1) (he0 q.1) (p.2 - q.2)).apply_symm_apply a
  map_add' _ _ := rfl
  map_smul' c f := by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_smul A c
      ((principalCornerHomEquiv R hmul (e p.1) (e q.1)
        (he p.1) (he q.1) (he0 p.1) (he0 q.1) (p.2 - q.2)) f.hom).val

/-- The identity has the selected idempotent as its corner coordinate. -/
theorem principalDegreeHomEquiv_id (p : PrincipalDegreeCategory R hmul e he0) :
    (principalDegreeHomEquiv R hmul e he0 he p p (𝟙 p)).val = e p.1 := rfl

/-- Composition is multiplication in A, with the contravariant left-module convention. -/
theorem principalDegreeHomEquiv_comp {p q r : PrincipalDegreeCategory R hmul e he0}
    (f : p ⟶ q) (g : q ⟶ r) :
    (principalDegreeHomEquiv R hmul e he0 he p r (f ≫ g)).val =
      (principalDegreeHomEquiv R hmul e he0 he p q f).val *
        (principalDegreeHomEquiv R hmul e he0 he q r g).val :=
  principal_comp_evaluation (e p.1) (e q.1) (e r.1) (he q.1) f.hom.val g.hom.val

/-- Precomposition in the representation is the action of its corner coordinate. -/
theorem principalEvaluation_action {p q : PrincipalDegreeCategory R hmul e he0}
    (f : p ⟶ q) (X : ShiftedModule.{u,u} (R := R))
    (x : (principalDegreeInclusion R hmul e he0).obj q ⟶ X) :
    (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2 X (f.hom ≫ x)).val =
      (principalDegreeHomEquiv R hmul e he0 he p q f).val •
        (principalShiftHomEquiv R hmul (e q.1) (he q.1) (he0 q.1) q.2 X x).val :=
  principal_apply (e q.1) (he q.1) x.val
    ((f.hom.val : (principalObject R hmul (e p.1) (he0 p.1)).module →ₗ[A]
      (principalObject R hmul (e q.1) (he0 q.1)).module).toFun (principalGenerator (e p.1)))

end MagnitudeConjecture.Graded.FiniteGradedModule
