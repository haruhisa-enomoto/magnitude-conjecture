import MagnitudeConjecture.CategoryTheory.GradedSupportedModuleCoordinates

/-! # Compatibility of actual module coordinates with the reconstructed action -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

variable (hsum : ∑ i, e i = 1) (horth : Pairwise fun i j ↦ e i * e j = 0)
variable (m : ℕ) (X : SupportedCategory (R := R) m)

/-- Evaluation turns the reconstructed matrix action into the same action on coordinate vectors. -/
theorem intervalActionMap_evaluation (a : A)
    (y : intervalCoordinateSpace R hmul e he0
      (CoveringHom.restrictedLinearYoneda (k := k) (principalDegreeInclusion R hmul e he0) X.obj) m)
    (p : ι × Fin (m + 1)) :
    (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj
      (intervalActionMap R hmul e he0 he
        (CoveringHom.restrictedLinearYoneda (k := k) (principalDegreeInclusion R hmul e he0) X.obj)
        m a y p)).val =
      ∑ q : ι × Fin (m + 1), intervalCorner R e m p q a •
        (principalShiftHomEquiv R hmul (e q.1) (he q.1) (he0 q.1) q.2.val X.obj (y q)).val := by
  change (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj
    (∑ q, _)).val = _
  rw [map_sum, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have h := principalEvaluation_action R hmul e he0 he
    (intervalActionCoefficient R hmul e he0 he m p q a) X.obj (y q)
  rw [intervalActionCoefficient_coord] at h
  exact h

/-- The vector-space coordinate equivalence intertwines the actual algebra action with reconstruction. -/
theorem supportedModuleCoordinateEquiv_smul (a : A) (x : X.obj.obj.module) :
    supportedModuleCoordinateEquiv R hmul e he0 he hsum horth m X (a • x) =
      intervalActionMap R hmul e he0 he
        (CoveringHom.restrictedLinearYoneda (k := k) (principalDegreeInclusion R hmul e he0) X.obj)
        m a (supportedModuleCoordinateEquiv R hmul e he0 he hsum horth m X x) := by
  funext p
  apply (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj).injective
  apply Subtype.ext
  rw [supportedModuleCoordinateEquiv_evaluation, intervalActionMap_evaluation]
  simp only [supportedModuleCoordinateEquiv_evaluation]
  have h := X.obj.obj.grading.idempotentProjection_smul e he he0 hsum
    (fun r : Fin (m + 1) ↦ (r.val : ℤ) - X.obj.degree)
    (by
      intro r s h
      change (r.val : ℤ) - X.obj.degree = (s.val : ℤ) - X.obj.degree at h
      apply Fin.ext
      omega)
    (supportedModule_degree_cover R m X) p a x
  simpa only [intervalCorner, sub_sub_sub_cancel_right] using h

end MagnitudeConjecture.Graded.FiniteGradedModule
