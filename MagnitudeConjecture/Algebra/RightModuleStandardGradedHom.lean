import MagnitudeConjecture.Algebra.RightModuleStandardGradedFunctor
import MagnitudeConjecture.CategoryTheory.GradedFunctorHomEquiv

/-! # Homogeneous mesh maps are exactly the graded module maps -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

instance standardFormMeshEmbeddingLinear : (Mat_.embedding S.StandardFormMeshCategory).Linear k where
  map_smul := by intros; rfl

/-- The vertex realization by graded modules, with all underlying maps retained. -/
def standardFormGradedVertexFunctor : S.StandardFormMeshCategory ⥤
    Graded.FiniteGradedModule (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite) :=
  Mat_.embedding _ ⋙ S.standardFormGradedFunctor

instance : S.standardFormGradedVertexFunctor.Full := by
  unfold standardFormGradedVertexFunctor
  infer_instance
instance : S.standardFormGradedVertexFunctor.Faithful := by
  unfold standardFormGradedVertexFunctor
  infer_instance
instance : S.standardFormGradedVertexFunctor.Additive := by
  unfold standardFormGradedVertexFunctor
  infer_instance
instance : S.standardFormGradedVertexFunctor.Linear k := by
  unfold standardFormGradedVertexFunctor
  infer_instance

/-- The vertex realization preserves each degree. -/
theorem standardFormGradedVertexFunctor_homogeneous {X Y : S.StandardFormMeshCategory}
    {d : ℤ} {f : X ⟶ Y} (hf : f ∈ S.standardFormIntegerHomGrading.component X Y d) :
    S.standardFormGradedVertexFunctor.map f ∈
      Graded.FiniteGradedModule.homGrading.component
        (S.standardFormGradedVertexFunctor.obj X) (S.standardFormGradedVertexFunctor.obj Y) d := by
  apply S.standardFormGradedMap_homogeneous S.standardFormMeshHomFinite
  intro i hi j hj
  exact hf

/-- The manuscript's graded Hom identification, with degree equal to source
shift minus target shift. -/
def standardFormGradedHomEquiv (X Y : S.StandardFormMeshCategory) (s t : ℤ) :
    S.standardFormIntegerHomGrading.component X Y (s - t) ≃ₗ[k]
      ((⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
        ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩) :=
  S.standardFormIntegerHomGrading.componentEquiv Graded.FiniteGradedModule.homGrading
    S.standardFormGradedVertexFunctor (fun hf ↦ S.standardFormGradedVertexFunctor_homogeneous hf)
    X Y (s - t)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
