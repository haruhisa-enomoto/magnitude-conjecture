import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition

/-! # Expanding a factorization through its nonzero incoming summands -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasBinaryBiproducts C] [HasFiniteBiproducts C]
variable {X M Y : C} (d : FiniteIndecomposableDecomposition M)

/-- The component from a summand to the target. -/
def incomingComponent (b : M ⟶ Y) (j : Fin d.n) : d.summand j ⟶ Y :=
  biproduct.ι d.summand j ≫ d.isoBiproduct.inv ≫ b

/-- The summands that actually contribute to a map to the target. -/
abbrev IncomingIndex (b : M ⟶ Y) := {j : Fin d.n // d.incomingComponent b j ≠ 0}

/-- The source component in the same displayed decomposition. -/
def outgoingComponent (a : X ⟶ M) (j : Fin d.n) : X ⟶ d.summand j :=
  a ≫ d.isoBiproduct.hom ≫ biproduct.π d.summand j

/-- A composite is the sum of its components through the summands whose
maps to the target are nonzero. -/
theorem comp_eq_sum_incoming (a : X ⟶ M) (b : M ⟶ Y) :
    letI : Fintype (d.IncomingIndex b) := Fintype.ofFinite _
    a ≫ b = ∑ j : d.IncomingIndex b,
      d.outgoingComponent a j.val ≫ d.incomingComponent b j.val := by
  classical
  letI : Fintype (d.IncomingIndex b) := Fintype.ofFinite _
  have htotal : (∑ j : Fin d.n, d.outgoingComponent a j ≫ d.incomingComponent b j) = a ≫ b := by
    simp only [outgoingComponent, incomingComponent, Category.assoc]
    rw [← Preadditive.comp_sum, ← Preadditive.comp_sum]
    have h : (∑ j : Fin d.n, biproduct.π d.summand j ≫
        biproduct.ι d.summand j ≫ d.isoBiproduct.inv ≫ b) = d.isoBiproduct.inv ≫ b := by
      simp only [← Category.assoc]
      rw [← Preadditive.sum_comp, ← Preadditive.sum_comp, biproduct.total]
      simp
    rw [h]
    simp
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun j : Fin d.n ↦ d.incomingComponent b j ≠ 0)
    (fun j ↦ d.outgoingComponent a j ≫ d.incomingComponent b j)
  have hzero : (∑ j : {j : Fin d.n // ¬ d.incomingComponent b j ≠ 0},
      d.outgoingComponent a j.val ≫ d.incomingComponent b j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [not_ne_iff.mp j.property, comp_zero]
  rw [hzero, add_zero, htotal] at hsplit
  convert hsplit.symm using 2
  ext j
  simp

/-- Any property shared by all indecomposables mapping nontrivially to Y
holds for each intermediate object in the reduced sum. -/
theorem incoming_summand_property (P : C → Prop)
    (hP : ∀ Z : C, Indecomposable Z → ∀ f : Z ⟶ Y, f ≠ 0 → P Z)
    (b : M ⟶ Y) (j : d.IncomingIndex b) : P (d.summand j.val) :=
  hP _ (d.indecomposable j.val) (d.incomingComponent b j.val) j.property

/-- A displayed decomposition supplies a reduced factorization whose
intermediates all have the incoming-object property. -/
theorem exists_factorization_decomposition (P : C → Prop)
    (hP : ∀ Z : C, Indecomposable Z → ∀ f : Z ⟶ Y, f ≠ 0 → P Z)
    (hd : Nonempty (FiniteIndecomposableDecomposition M))
    (a : X ⟶ M) (b : M ⟶ Y) :
    ∃ d : FiniteIndecomposableDecomposition M,
      (∀ q : d.IncomingIndex b, P (d.summand q.val)) ∧
      (letI : Fintype (d.IncomingIndex b) := Fintype.ofFinite _;
        a ≫ b = ∑ q : d.IncomingIndex b,
          d.outgoingComponent a q.val ≫ d.incomingComponent b q.val) := by
  obtain ⟨d⟩ := hd
  exact ⟨d, d.incoming_summand_property P hP b, d.comp_eq_sum_incoming a b⟩

end MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
