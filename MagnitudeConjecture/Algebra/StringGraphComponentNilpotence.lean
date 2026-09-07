import MagnitudeConjecture.Algebra.StringGraphComponentProductDiagonal
import Mathlib.Data.List.Chain

/-!
# Nilpotence of proper string graph components

Proper component maps define directed partial-bijection steps on the finite
set of positions above each displayed vertex.  The proper ideal has no
directed position cycle: a cycle would produce an element of the ideal with
diagonal coefficient one.  Conversely, every nonzero coefficient of a power
of an element of the ideal produces a position chain of the same length.
Pigeonhole therefore gives a uniform nilpotence bound.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

noncomputable local instance nilpotencePositionAtFintype
    (C : Word R) (x : Q) : Fintype (C.PositionAt x) :=
  Fintype.ofFinite _

/-- A directed position step supported by one proper self-component. -/
def ProperMorphismCoefficientStepAt
    (C : Word R) {x : Q} (i j : C.PositionAt x) : Prop :=
  ∃ component : C.ProperBoundaryFreeMorphismCoefficientComponent,
    Relation.EqvGen (C.MorphismCoefficientStep C)
      component.1.1.representative
      (⟨x, i, j⟩ : C.MorphismCoefficientPosition C)

/-- A single proper-component step is realized by an element of the proper
ideal with coefficient one and with no other nonzero coefficient in that
input row. -/
theorem exists_properMorphismCoefficientComponentSubspace_rowWitness_of_step
    (C : Word R) (hmono : IsMonomial R)
    {x : Q} {i j : C.PositionAt x}
    (hij : C.ProperMorphismCoefficientStepAt i j) :
    ∃ f : C.rightModule hmono ⟶ C.rightModule hmono,
      f ∈ C.properMorphismCoefficientComponentSubspace hmono ∧
      C.morphismCoefficientAt C hmono hmono f ⟨x, i, j⟩ = 1 ∧
      ∀ t : C.PositionAt x,
        C.morphismCoefficientAt C hmono hmono f ⟨x, i, t⟩ ≠ 0 →
          t = j := by
  classical
  obtain ⟨component, hcomponent⟩ := hij
  let f := C.properBoundaryFreeMorphismCoefficientComponentMap hmono component
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [properMorphismCoefficientComponentSubspace]
    apply Submodule.subset_span
    exact ⟨component, rfl⟩
  · change C.morphismCoefficientAt C hmono hmono
        (C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono
          component.1) ⟨x, i, j⟩ = 1
    rw [C.morphismCoefficientAt_boundaryFreeComponentMap,
      C.coefficientComponentIndicator_eq_one]
    exact hcomponent
  · intro t ht
    change C.morphismCoefficientAt C hmono hmono
        (C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono
          component.1) ⟨x, i, t⟩ ≠ 0 at ht
    rw [C.morphismCoefficientAt_boundaryFreeComponentMap] at ht
    have htComponent :
        Relation.EqvGen (C.MorphismCoefficientStep C)
          component.1.1.representative
          (⟨x, i, t⟩ : C.MorphismCoefficientPosition C) := by
      by_contra hnot
      rw [C.coefficientComponentIndicator_eq_zero C
        component.1.1.representative ⟨x, i, t⟩ hnot] at ht
      exact ht rfl
    have hpositions :
        (⟨x, i, j⟩ : C.MorphismCoefficientPosition C) =
          (⟨x, i, t⟩ : C.MorphismCoefficientPosition C) :=
      C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq C
        (Relation.EqvGen.trans _ component.1.1.representative _
          (Relation.EqvGen.symm _ _ hcomponent) htComponent) rfl
    cases hpositions
    rfl

/-- Row witnesses compose: the product still has coefficient one at the
chosen endpoint and a unique nonzero entry in the chosen input row. -/
theorem exists_properMorphismCoefficientComponentSubspace_rowWitness_of_transGen
    (C : Word R) (hmono : IsMonomial R)
    {x : Q} {i j : C.PositionAt x}
    (hij : Relation.TransGen C.ProperMorphismCoefficientStepAt i j) :
    ∃ f : C.rightModule hmono ⟶ C.rightModule hmono,
      f ∈ C.properMorphismCoefficientComponentSubspace hmono ∧
      C.morphismCoefficientAt C hmono hmono f ⟨x, i, j⟩ = 1 ∧
      ∀ t : C.PositionAt x,
        C.morphismCoefficientAt C hmono hmono f ⟨x, i, t⟩ ≠ 0 →
          t = j := by
  classical
  induction hij using Relation.TransGen.trans_induction_on with
  | single hij =>
      exact C.exists_properMorphismCoefficientComponentSubspace_rowWitness_of_step
        hmono hij
  | @trans a b c hab hbc ihab ihbc =>
      obtain ⟨f, hf, hfab, hfUnique⟩ := ihab
      obtain ⟨g, hg, hgbc, hgUnique⟩ := ihbc
      refine ⟨f ≫ g,
        C.properMorphismCoefficientComponentSubspace_comp_mem_of_mem_left
          hmono hf, ?_, ?_⟩
      · rw [C.morphismCoefficientAt_comp C C hmono hmono hmono]
        rw [Finset.sum_eq_single b]
        · rw [hfab, hgbc, one_mul]
        · intro t ht htb
          by_cases hft :
              C.morphismCoefficientAt C hmono hmono f ⟨x, a, t⟩ = 0
          · rw [hft, zero_mul]
          · exact (htb (hfUnique t hft)).elim
        · simp
      · intro t ht
        rw [C.morphismCoefficientAt_comp C C hmono hmono hmono] at ht
        obtain ⟨s, hsMem, hs⟩ :=
          Finset.exists_ne_zero_of_sum_ne_zero ht
        obtain ⟨hfs, hgs⟩ := mul_ne_zero_iff.mp hs
        have hsb : s = b := hfUnique s hfs
        subst s
        exact hgUnique t hgs

/-- The directed relation generated by proper graph components has no
cycle above any displayed vertex. -/
theorem properMorphismCoefficientStepAt_transGen_irrefl
    (C : Word R) (hmono : IsMonomial R)
    {x : Q} (i : C.PositionAt x) :
    ¬ Relation.TransGen C.ProperMorphismCoefficientStepAt i i := by
  intro hii
  obtain ⟨f, hf, hcoeff, hrow⟩ :=
    C.exists_properMorphismCoefficientComponentSubspace_rowWitness_of_transGen
      hmono hii
  have hdiag : C.diagonalMorphismCoefficientLinearMap hmono f = 0 := by
    rw [C.properMorphismCoefficientComponentSubspace_eq_ker] at hf
    exact hf
  have hiZero :
      C.morphismCoefficientAt C hmono hmono f
          (C.diagonalMorphismCoefficientPosition i) = 0 := by
    calc
      _ = C.morphismCoefficientAt C hmono hmono f
          (C.diagonalMorphismCoefficientPosition C.sourcePosition) :=
        C.morphismCoefficientAt_eq_of_eqvGen C hmono hmono f
          (C.diagonalMorphismCoefficientPosition_eqvGen_source i)
      _ = C.morphismCoefficientAt C hmono hmono f
          C.diagonalMorphismCoefficientComponent.representative :=
        (C.morphismCoefficientAt_diagonalComponent_representative_eq_source
          hmono f).symm
      _ = 0 := hdiag
  exact one_ne_zero (hcoeff.symm.trans hiZero)

/-- A nonzero coefficient of an element of the proper span is supported by
at least one proper component. -/
theorem properMorphismCoefficientStepAt_of_mem_of_coefficient_ne_zero
    (C : Word R) (hmono : IsMonomial R)
    {f : C.rightModule hmono ⟶ C.rightModule hmono}
    (hf : f ∈ C.properMorphismCoefficientComponentSubspace hmono)
    {x : Q} {i j : C.PositionAt x}
    (hne : C.morphismCoefficientAt C hmono hmono f ⟨x, i, j⟩ ≠ 0) :
    C.ProperMorphismCoefficientStepAt i j := by
  classical
  rw [properMorphismCoefficientComponentSubspace] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨component, rfl⟩ := hf
      refine ⟨component, ?_⟩
      change C.morphismCoefficientAt C hmono hmono
          (C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono
            component.1) ⟨x, i, j⟩ ≠ 0 at hne
      rw [C.morphismCoefficientAt_boundaryFreeComponentMap] at hne
      by_contra hnot
      rw [C.coefficientComponentIndicator_eq_zero C
        component.1.1.representative ⟨x, i, j⟩ hnot] at hne
      exact hne rfl
  | zero =>
      simp at hne
  | add f g hf hg ihf ihg =>
      rw [C.morphismCoefficientAt_add] at hne
      by_cases hfne :
          C.morphismCoefficientAt C hmono hmono f ⟨x, i, j⟩ ≠ 0
      · exact ihf hfne
      · have hgne :
            C.morphismCoefficientAt C hmono hmono g ⟨x, i, j⟩ ≠ 0 := by
          intro hgzero
          rw [not_ne_iff.mp hfne, hgzero, add_zero] at hne
          exact hne rfl
        exact ihg hgne
  | smul c f hf ih =>
      rw [C.morphismCoefficientAt_smul] at hne
      exact ih (mul_ne_zero_iff.mp hne).2

/-- A nonzero coefficient of the `n`th power of an element of the proper
span produces a directed position chain of exactly `n` steps. -/
theorem exists_properMorphismCoefficientStepAt_chain_of_pow_coefficient_ne_zero
    (C : Word R) (hmono : IsMonomial R)
    {f : End (C.rightModule hmono)}
    (hf : f ∈ C.properMorphismCoefficientComponentSubspace hmono)
    (n : ℕ) {x : Q} (i j : C.PositionAt x)
    (hne : C.morphismCoefficientAt C hmono hmono (f ^ n) ⟨x, i, j⟩ ≠ 0) :
    ∃ positions : List (C.PositionAt x),
      positions.length = n ∧
      (i :: positions).IsChain C.ProperMorphismCoefficientStepAt := by
  classical
  induction n generalizing i j with
  | zero =>
      exact ⟨[], rfl, List.isChain_singleton i⟩
  | succ n ih =>
      rw [pow_succ, CategoryTheory.End.mul_def,
        C.morphismCoefficientAt_comp C C hmono hmono hmono] at hne
      obtain ⟨t, htMem, ht⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨hft, hpow⟩ := mul_ne_zero_iff.mp ht
      have hit : C.ProperMorphismCoefficientStepAt i t :=
        C.properMorphismCoefficientStepAt_of_mem_of_coefficient_ne_zero
          hmono hf hft
      obtain ⟨positions, hlength, hchain⟩ := ih t j hpow
      refine ⟨t :: positions, by simp [hlength], ?_⟩
      exact hchain.cons_cons hit

/-- The uniform nilpotence bound for the proper-component ideal: the number
of word positions annihilates every element. -/
theorem pow_length_add_one_eq_zero_of_mem_properMorphismCoefficientComponentSubspace
    (C : Word R) (hmono : IsMonomial R)
    (f : End (C.rightModule hmono))
    (hf : f ∈ C.properMorphismCoefficientComponentSubspace hmono) :
    f ^ (C.length + 1) = 0 := by
  classical
  apply CategoryTheory.End.ext
  apply C.rightModuleHom_ext_morphismCoefficientAt C hmono hmono
  rintro ⟨x, i, j⟩
  change C.morphismCoefficientAt C hmono hmono
      (CategoryTheory.End.asHom (f ^ (C.length + 1))) ⟨x, i, j⟩ = 0
  by_contra hne
  obtain ⟨positions, hlength, hchain⟩ :=
    C.exists_properMorphismCoefficientStepAt_chain_of_pow_coefficient_ne_zero
      hmono hf (C.length + 1) i j hne
  have hTransChain :
      (i :: positions).IsChain
        (Relation.TransGen C.ProperMorphismCoefficientStepAt) :=
    hchain.imp fun _ _ h ↦ Relation.TransGen.single h
  letI : Std.Irrefl
      (Relation.TransGen (@ProperMorphismCoefficientStepAt k Q _ _ R C x)) :=
    ⟨C.properMorphismCoefficientStepAt_transGen_irrefl hmono⟩
  have hnodup : (i :: positions).Nodup := hTransChain.pairwise.nodup
  have hlengthLeCard :
      (i :: positions).length ≤ Fintype.card (C.PositionAt x) :=
    hnodup.length_le_card
  have hcardLe : Fintype.card (C.PositionAt x) ≤ C.length + 1 := by
    simpa using Fintype.card_le_of_injective
      (PositionAt.indexEmbedding C x)
      (PositionAt.indexEmbedding C x).injective
  simp only [List.length_cons, hlength] at hlengthLeCard
  omega

/-- Every element of the proper-component ideal is nilpotent, with the
uniform exponent `C.length + 1`. -/
theorem isNilpotent_of_mem_properMorphismCoefficientComponentSubspace
    (C : Word R) (hmono : IsMonomial R)
    (f : End (C.rightModule hmono))
    (hf : f ∈ C.properMorphismCoefficientComponentSubspace hmono) :
    IsNilpotent f :=
  ⟨C.length + 1,
    C.pow_length_add_one_eq_zero_of_mem_properMorphismCoefficientComponentSubspace
      hmono f hf⟩

end MagnitudeConjecture.BoundQuiver.StringWord.Word
