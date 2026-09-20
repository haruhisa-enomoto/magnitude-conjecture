import MagnitudeConjecture.CategoryTheory.LinearBiproduct
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Finite decomposition codes under a Hom-dimension bound -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace MagnitudeConjecture.FiniteKernel
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
variable {ι : Type} [Fintype ι]

/-- A bounded ordered list of labels from a finite family. -/
abbrev DecompositionCode (ι : Type) (D : ℕ) :=
  (n : Fin (D + 1)) × (Fin n.val → ι)

/-- The biproduct specified by a decomposition code. -/
def codeObject (F : ι → C) {D : ℕ} (c : DecompositionCode ι D) : C :=
  ⨁ fun j ↦ F (c.2 j)

/-- If G sees every family member, its Hom dimension bounds the number of
summands and hence gives a finite code for every bounded object. -/
theorem exists_bounded_decomposition (F : ι → C) (G : C)
    [∀ X : C, FiniteDimensional k (G ⟶ X)]
    (hG : ∀ i, 1 ≤ Module.finrank k (G ⟶ F i))
    (hdec : ∀ X : C, ∃ n : ℕ, ∃ label : Fin n → ι,
      Nonempty (X ≅ ⨁ fun j ↦ F (label j)))
    (X : C) (D : ℕ) (hX : Module.finrank k (G ⟶ X) ≤ D) :
    ∃ c : DecompositionCode ι D, Nonempty (X ≅ codeObject F c) := by
  classical
  obtain ⟨n, label, ⟨e⟩⟩ := hdec X
  have hn : n ≤ Module.finrank k (G ⟶ X) := by
    calc
      n = ∑ _j : Fin n, (1 : ℕ) := by simp
      _ ≤ ∑ j : Fin n, Module.finrank k (G ⟶ F (label j)) :=
        Finset.sum_le_sum (fun j _ ↦ hG (label j))
      _ = Module.finrank k (G ⟶ X) :=
        (MagnitudeConjecture.CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
          k G X (fun j ↦ F (label j)) e).symm
  exact ⟨⟨⟨n, Nat.lt_succ_of_le (hn.trans hX)⟩, label⟩, ⟨e⟩⟩

/-- A monomorphism bounds the Hom dimension of its source by that of its target. -/
theorem finrank_hom_le_of_mono (G : C) {X Z : C} (f : X ⟶ Z) [Mono f]
    [FiniteDimensional k (G ⟶ Z)] :
    Module.finrank k (G ⟶ X) ≤ Module.finrank k (G ⟶ Z) :=
  LinearMap.finrank_le_finrank_of_injective (f := Linear.rightComp k G f)
    (fun a b h ↦ (cancel_mono f).mp h)

end MagnitudeConjecture.FiniteKernel
