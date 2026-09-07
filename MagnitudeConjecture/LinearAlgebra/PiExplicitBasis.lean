import Mathlib.LinearAlgebra.StdBasis

/-!
# An explicit basis for finite dependent products

This is the usual product basis, packaged so its basis vectors are
definitionally a named single-coordinate function.  Keeping the construction
generic prevents downstream elaboration from specializing the internals of
`Pi.basis` to large dependent module families.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture

universe u
universe u₁ u₂ u₃ u₄

/-- Rebuild a basis with an extensionally equal family as its explicit
coefficient function. -/
def explicitBasisOfFamily
    {ι R M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) (v : ι → M)
    (h : ∀ i, b i = v i) : Module.Basis ι R M := by
  have hfamily : (fun i ↦ b i) = v := funext h
  have hli := b.linearIndependent
  change LinearIndependent R (fun i ↦ b i) at hli
  rw [hfamily] at hli
  apply Module.Basis.mk hli
  have hspan := b.span_eq
  change Submodule.span R (Set.range fun i ↦ b i) = ⊤ at hspan
  rw [hfamily] at hspan
  exact hspan.ge

@[simp]
theorem explicitBasisOfFamily_apply
    {ι R M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) (v : ι → M)
    (h : ∀ i, b i = v i) (i : ι) :
    explicitBasisOfFamily b v h i = v i := by
  simp [explicitBasisOfFamily, Module.Basis.mk_apply]

/-- Insert a value into one coordinate of a dependent product, using one
canonical classical decidable equality hidden behind a named definition. -/
def piSingle
    {η : Type u} {M : η → Type u} [∀ a, Zero (M a)]
    (a : η) (x : M a) : ∀ b, M b := by
  classical
  exact Pi.single a x

/-- Equality in the selected coordinate gives equality of the corresponding
single-coordinate vectors. -/
theorem piSingle_congr
    {η : Type u} {M : η → Type u} [∀ a, Zero (M a)]
    {a : η} {x y : M a} (h : x = y) :
    piSingle a x = piSingle a y :=
  congrArg (piSingle a) h

/-- Reindex a dependent product along an equivalence.  Keeping this wrapper
generic prevents concrete large module families from expanding the internals
of `LinearEquiv.piCongrLeft` during downstream elaboration. -/
def piReindexLinearEquiv
    {R : Type u₁} {η : Type u₂} {ι : Type u₃} {M : η → Type u₄}
    [Semiring R] [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
    (e : ι ≃ η) :
    (∀ i, M (e i)) ≃ₗ[R] (∀ a, M a) :=
  LinearEquiv.piCongrLeft R M e

/-- A basis vector inserted into one coordinate of a dependent product. -/
def piBasisVector
    {R η : Type u} {ι : η → Type u} {M : η → Type u}
    [Semiring R] [Fintype η]
    [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
    (s : ∀ a, Module.Basis (ι a) R (M a))
    (t : Σ a, ι a) : ∀ a, M a :=
  piSingle t.1 (s t.1 t.2)

@[simp]
theorem piBasisVector_mk
    {R η : Type u} {ι : η → Type u} {M : η → Type u}
    [Semiring R] [Fintype η]
    [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
    (s : ∀ a, Module.Basis (ι a) R (M a)) (a : η) (i : ι a) :
    piBasisVector s ⟨a, i⟩ = piSingle a (s a i) :=
  rfl

/-- The named single-coordinate basis vectors span the dependent product. -/
theorem span_range_piBasisVector_eq_top
    {R η : Type u} {ι : η → Type u} {M : η → Type u}
    [Semiring R] [Fintype η]
    [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
    (s : ∀ a, Module.Basis (ι a) R (M a)) :
    Submodule.span R (Set.range (piBasisVector s)) = ⊤ := by
  classical
  have hfamily :
      piBasisVector s =
        (Pi.basis s : (Σ a, ι a) → (∀ a, M a)) := by
    funext t
    unfold piBasisVector piSingle
    exact (Pi.basis_apply s t).symm
  rw [hfamily]
  exact (Pi.basis s).span_eq

/-- The explicit single-coordinate basis of a finite dependent product. -/
def piExplicitBasis
    {R η : Type u} {ι : η → Type u} {M : η → Type u}
    [Semiring R] [Fintype η]
    [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
    (s : ∀ a, Module.Basis (ι a) R (M a)) :
    Module.Basis (Σ a, ι a) R (∀ a, M a) := by
  have hli : LinearIndependent R (piBasisVector s) := by
    classical
    unfold piBasisVector
    exact Pi.linearIndependent_single
      (fun a i ↦ s a i) (fun a ↦ (s a).linearIndependent)
  apply Module.Basis.mk hli
  exact (span_range_piBasisVector_eq_top s).ge

@[simp]
theorem piExplicitBasis_apply
    {R η : Type u} {ι : η → Type u} {M : η → Type u}
    [Semiring R] [Fintype η]
    [∀ a, AddCommMonoid (M a)] [∀ a, Module R (M a)]
    (s : ∀ a, Module.Basis (ι a) R (M a)) (t : Σ a, ι a) :
    piExplicitBasis s t = piBasisVector s t := by
  simp [piExplicitBasis, Module.Basis.mk_apply]

end MagnitudeConjecture
