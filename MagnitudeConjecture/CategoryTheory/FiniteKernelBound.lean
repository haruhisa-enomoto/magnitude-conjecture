import MagnitudeConjecture.CategoryTheory.KernelIsoScalarMaps
import MagnitudeConjecture.CategoryTheory.FiniteBoundedDecomposition
import MagnitudeConjecture.LinearAlgebra.FiniteProportionalClasses

/-! # The finite-kernel dimension bound with explicit extension input -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.FiniteKernel
universe u v w
variable {k : Type u} [Field k] [Infinite k]
variable {C : Type v} [Category.{w} C] [Abelian C] [Linear k C]
variable [HasFiniteBiproducts C]
variable {ι : Type} [Fintype ι]

/-- A finite additive classification bounds the possible kernel classes.
If kernel maps extend to a scalar-endomorphism source and the target is
injective with scalar endomorphisms, the Hom dimension is at most one. -/
theorem finrank_hom_le_one_of_finite_decompositions
    (F : ι → C) (G : C) [∀ X : C, FiniteDimensional k (G ⟶ X)]
    (hG : ∀ i, 1 ≤ Module.finrank k (G ⟶ F i))
    (hdec : ∀ X : C, ∃ n : ℕ, ∃ label : Fin n → ι,
      Nonempty (X ≅ ⨁ fun j ↦ F (label j)))
    (Z I : C) [Injective I]
    (hZ : ∀ a : Z ⟶ Z, ∃ c : k, a = c • 𝟙 Z)
    (hI : ∀ a : I ⟶ I, ∃ c : k, a = c • 𝟙 I)
    (hext : ∀ f : Z ⟶ I, f ≠ 0 → ∀ h : kernel f ⟶ Z,
      ∃ a : Z ⟶ Z, kernel.ι f ≫ a = h) :
    Module.finrank k (Z ⟶ I) ≤ 1 := by
  classical
  let D := Module.finrank k (G ⟶ Z)
  have hrep (f : {f : Z ⟶ I // f ≠ 0}) :
      ∃ c : DecompositionCode ι D, Nonempty (kernel f.val ≅ codeObject F c) :=
    exists_bounded_decomposition F G hG hdec (kernel f.val) D
      (finrank_hom_le_of_mono G (kernel.ι f.val))
  apply finrank_le_one_of_finite_proportional_classes (fun f ↦ (hrep f).choose)
  intro f g h
  obtain ⟨ef⟩ := (hrep f).choose_spec
  obtain ⟨eg⟩ := (hrep g).choose_spec
  let e : kernel f.val ≅ kernel g.val :=
    ef.trans ((eqToIso (congrArg (codeObject F) h)).trans eg.symm)
  exact exists_scalar_of_kernel_iso hZ hI f.val g.val e (hext f.val f.property)

/-- The sum of the finite family detects every nonzero summand, so a Hom-finite
category with a finite additive classification satisfies the finite-kernel bound. -/
theorem finrank_hom_le_one_of_finite_additive_family
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (F : ι → C) (hF : ∀ i, ¬ IsZero (F i))
    (hdec : ∀ X : C, ∃ n : ℕ, ∃ label : Fin n → ι,
      Nonempty (X ≅ ⨁ fun j ↦ F (label j)))
    (Z I : C) [Injective I]
    (hZ : ∀ a : Z ⟶ Z, ∃ c : k, a = c • 𝟙 Z)
    (hI : ∀ a : I ⟶ I, ∃ c : k, a = c • 𝟙 I)
    (hext : ∀ f : Z ⟶ I, f ≠ 0 → ∀ h : kernel f ⟶ Z,
      ∃ a : Z ⟶ Z, kernel.ι f ≫ a = h) :
    Module.finrank k (Z ⟶ I) ≤ 1 := by
  classical
  let G : C := ⨁ F
  have hG (i : ι) : 1 ≤ Module.finrank k (G ⟶ F i) := by
    apply Nat.succ_le_of_lt
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨biproduct.π F i, ?_⟩
    intro hz
    apply hF i
    apply (IsZero.iff_id_eq_zero _).mpr
    calc
      𝟙 (F i) = biproduct.ι F i ≫ biproduct.π F i := by simp
      _ = 0 := by rw [hz, comp_zero]
  exact finrank_hom_le_one_of_finite_decompositions F G hG hdec Z I hZ hI hext

end MagnitudeConjecture.FiniteKernel
