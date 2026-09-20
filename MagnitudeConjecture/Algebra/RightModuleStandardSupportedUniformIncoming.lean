import MagnitudeConjecture.Algebra.RightModuleStandardSupportedIncomingCount

/-! # Uniform incoming bounds independent of the interval length -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped BigOperators
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance uniformIncomingQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance uniformIncomingArrowFintype (x y : Fin S.n) :
    Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- One pair of constants bounds the number of incoming indecomposable
sources and every Hom dimension for every finite interval. -/
theorem standardFormSupported_uniform_incoming_bounds :
    ∃ h D : ℕ, 1 ≤ h ∧ ∀ m : ℕ,
      (∀ b : S.standardFormSupportedLabel m,
        Nat.card (S.standardFormSupportedIncomingLabel b) ≤ S.n * (h + 1)) ∧
      (∀ a b : S.standardFormSupportedLabel m,
        Module.finrank k (S.standardFormSupportedFamily m a ⟶
          S.standardFormSupportedFamily m b) ≤ D) := by
  classical
  let d (i j : Fin S.n) := Module.finrank k
    (MeshCategory.obj (k := k) S.standardFormRightMeshData i ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData j)
  obtain ⟨h, hh, hb⟩ := S.standardFormGraded_uniform_bound
  refine ⟨h, ∑ i, ∑ j, d i j, hh, fun m ↦ ⟨?_, ?_⟩⟩
  · intro b
    exact S.standardFormSupportedIncomingLabel_card_le h hb b
  · intro a b
    apply (S.standardFormSupported_hom_finrank_le a b).trans
    change d a.1 b.1 ≤ ∑ i, ∑ j, d i j
    exact (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (d a.1 j))
      (Finset.mem_univ b.1)).trans
      (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (∑ j, d i j))
        (Finset.mem_univ a.1))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
