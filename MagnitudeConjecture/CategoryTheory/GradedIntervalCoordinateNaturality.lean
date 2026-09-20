import MagnitudeConjecture.CategoryTheory.GradedIntervalEvaluationCoordinate

/-! # Naturality of the evaluation–reconstruction coordinate comparison -/
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

/-- A homogeneous projective map is recovered from its own corner coefficient. -/
theorem intervalActionCoefficient_of_morphism (m : ℕ) (p q : ι × Fin (m + 1))
    (f : intervalProjectiveLabel R hmul e he0 m p ⟶ intervalProjectiveLabel R hmul e he0 m q) :
    intervalActionCoefficient R hmul e he0 he m p q
      (principalDegreeHomEquiv R hmul e he0 he _ _ f).val = f := by
  apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
  apply Subtype.ext
  rw [intervalActionCoefficient_coord]
  have hf := (principalDegreeHomEquiv R hmul e he0 he _ _ f).property
  dsimp only [intervalProjectiveLabel] at hf
  change e p.1 * R.projection ((p.2.val : ℤ) - q.2.val) _ * e q.1 = _
  dsimp only [intervalProjectiveLabel]
  rw [R.projection_of_mem hf.1, hf.2.1, hf.2.2]

variable (F : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k)
variable [F.Additive] [F.Linear k]

/-- On a single coordinate, the reconstructed action is the original representation map. -/
theorem intervalActionMap_singleCoordinate (m : ℕ) (p q : ι × Fin (m + 1))
    (f : intervalProjectiveLabel R hmul e he0 m p ⟶ intervalProjectiveLabel R hmul e he0 m q)
    (x : intervalCoordinateSpace R hmul e he0 F m)
    (hx : x ∈ singleCoordinate (k := k)
      (fun z : ι × Fin (m + 1) ↦ F.obj (op (intervalProjectiveLabel R hmul e he0 m z))) q) :
    intervalActionMap R hmul e he0 he F m
      (principalDegreeHomEquiv R hmul e he0 he _ _ f).val x p = (F.map f.op).hom (x q) := by
  classical
  change (∑ z, (F.map (intervalActionCoefficient R hmul e he0 he m p z
    (principalDegreeHomEquiv R hmul e he0 he _ _ f).val).op).hom (x z)) = _
  rw [Finset.sum_eq_single q]
  · rw [intervalActionCoefficient_of_morphism]
  · intro z hz hzq
    rw [hx z hzq, map_zero]
  · simp

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0)
variable (hfinite : ∀ p, FiniteDimensional k (F.obj p)) (m : ℕ)

/-- Evaluation after reconstruction intertwines every morphism between interval projectives. -/
theorem intervalEvaluationCoordinate_naturality (p q : ι × Fin (m + 1))
    (f : intervalProjectiveLabel R hmul e he0 m p ⟶ intervalProjectiveLabel R hmul e he0 m q)
    (g : (principalDegreeInclusion R hmul e he0).obj (intervalProjectiveLabel R hmul e he0 m q) ⟶
      (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).obj) :
    intervalEvaluationCoordinateEquiv R hmul e he0 he F hneg h1 hsum horth hfinite m p (f.hom ≫ g) =
      (F.map f.op).hom
        (intervalEvaluationCoordinateEquiv R hmul e he0 he F hneg h1 hsum horth hfinite m q g) := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
  let X := intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m
  let x : intervalCoordinateSpace R hmul e he0 F m :=
    (g.val : (principalObject R hmul (e q.1) (he0 q.1)).module →ₗ[A]
      (intervalReconstructedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).module).toFun
        (principalGenerator (e q.1))
  have hx : x ∈ singleCoordinate (k := k)
      (fun z : ι × Fin (m + 1) ↦ F.obj (op (intervalProjectiveLabel R hmul e he0 m z))) q := by
    apply (reconstructedCoordinate_eq_single R hmul e he0 he F hneg h1 hsum horth m q).le
    have h := (principalShiftHomEquiv R hmul (e q.1) (he q.1) (he0 q.1) q.2.val X.obj g).property
    change x ∈ idempotentComponent R
      (intervalReconstructedGrading R hmul e he0 he F hneg h1 hsum horth m)
        (e q.1) ((q.2.val : ℤ) - 0) at h
    simpa only [sub_zero] using h
  rw [intervalEvaluationCoordinateEquiv_apply, intervalEvaluationCoordinateEquiv_apply]
  have h := principalEvaluation_action R hmul e he0 he f X.obj g
  have hp := congrArg (fun y : X.obj.obj.module ↦
    (show intervalCoordinateSpace R hmul e he0 F m from y) p) h
  exact hp.trans (intervalActionMap_singleCoordinate R hmul e he0 he F m p q f x hx)

end MagnitudeConjecture.Graded.FiniteGradedModule
