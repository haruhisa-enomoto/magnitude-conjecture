import MagnitudeConjecture.Algebra.RightModuleStandardSupportedCategory
import MagnitudeConjecture.Algebra.RightModuleStandardGradedDirected

/-! # Directedness inside the supported graded category -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance supportedDirectedQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance supportedDirectedArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- Nonzero noninvertible maps in the supported family strictly lower shift. -/
theorem standardFormSupported_noniso_descent {m : ℕ} (a b : S.standardFormSupportedLabel m)
    (f : S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b)
    (hf : f ≠ 0) (hi : ¬ IsIso f) : b.2.val < a.2.val := by
  let F := (Graded.FiniteGradedModule.intervalSupport
    (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite) m).ι
  apply S.standardFormGraded_noniso_descent
    (MeshCategory.obj (k := k) S.standardFormRightMeshData a.1)
    (MeshCategory.obj (k := k) S.standardFormRightMeshData b.1) a.2.val b.2.val f.hom
  · intro hz
    apply hf
    apply ObjectProperty.hom_ext
    exact hz
  · intro hiso
    let : IsIso (F.map f) := hiso
    exact hi (isIso_of_reflects_iso f F)

/-- Edges between supported indecomposable representatives. -/
def standardFormSupportedEdge (m : ℕ) (a b : S.standardFormSupportedLabel m) : Prop :=
  ∃ f : S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b,
    f ≠ 0 ∧ ¬ IsIso f

/-- No cycle of nonzero nonisomorphisms occurs in the complete supported family. -/
theorem standardFormSupported_acyclic (m : ℕ) (a : S.standardFormSupportedLabel m) :
    ¬ Relation.TransGen (S.standardFormSupportedEdge m) a a := by
  have descent {b c} (h : Relation.TransGen (S.standardFormSupportedEdge m) b c) :
      c.2.val < b.2.val := by
    induction h with
    | single h =>
      obtain ⟨f, hf, hi⟩ := h
      exact S.standardFormSupported_noniso_descent _ _ f hf hi
    | tail h he ih =>
      obtain ⟨f, hf, hi⟩ := he
      exact lt_trans (S.standardFormSupported_noniso_descent _ _ f hf hi) ih
  intro h
  exact (lt_irrefl a.2.val) (descent h)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
