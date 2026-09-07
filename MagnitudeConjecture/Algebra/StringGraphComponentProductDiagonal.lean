import MagnitudeConjecture.Algebra.StringGraphComponentConvexity
import MagnitudeConjecture.Algebra.StringGraphComponentRadicalCandidate
import MagnitudeConjecture.Algebra.StringEndomorphismDiagonal

/-!
# Diagonal coefficients of products of string graph-component maps

This file reduces a possible nonzero diagonal coefficient of a component-map
product to a full-support oriented self-interval.  The midpoint argument
excluding a proper full-support interval is developed below.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

noncomputable local instance productDiagonalPositionAtFintype
    (C : Word R) (x : Q) : Fintype (C.PositionAt x) :=
  Fintype.ofFinite _

/-- A nonzero diagonal coefficient of a product of two component maps has an
intermediate position supported by both components. -/
theorem exists_intermediate_of_boundaryFreeComponentMap_comp_diagonal_ne_zero
    (C : Word R) (hmono : IsMonomial R)
    (first second : C.BoundaryFreeMorphismCoefficientComponent C)
    {x : Q} (i : C.PositionAt x)
    (hne : C.morphismCoefficientAt C hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono first ≫
        C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (C.diagonalMorphismCoefficientPosition i) ≠ 0) :
    ∃ j : C.PositionAt x,
      Relation.EqvGen (C.MorphismCoefficientStep C)
        first.1.representative ⟨x, i, j⟩ ∧
      Relation.EqvGen (C.MorphismCoefficientStep C)
        second.1.representative ⟨x, j, i⟩ := by
  classical
  rw [C.morphismCoefficientAt_boundaryFreeComponentMap_comp] at hne
  change (∑ j : C.PositionAt x,
      C.coefficientComponentIndicator C first.1.representative ⟨x, i, j⟩ *
        C.coefficientComponentIndicator C second.1.representative
          ⟨x, j, i⟩) ≠ 0 at hne
  by_contra h
  apply hne
  apply Finset.sum_eq_zero
  intro j hj
  have hnot :
      ¬ (Relation.EqvGen (C.MorphismCoefficientStep C)
          first.1.representative ⟨x, i, j⟩ ∧
        Relation.EqvGen (C.MorphismCoefficientStep C)
          second.1.representative ⟨x, j, i⟩) := by
    intro hboth
    exact h ⟨j, hboth⟩
  rcases not_and_or.mp hnot with hfirst | hsecond
  · rw [C.coefficientComponentIndicator_eq_zero C
      first.1.representative ⟨x, i, j⟩ hfirst, zero_mul]
  · rw [C.coefficientComponentIndicator_eq_zero C
      second.1.representative ⟨x, j, i⟩ hsecond, mul_zero]

/-- If one diagonal coefficient of a component-map product is nonzero, the
first component has a supported coefficient above every word position. -/
theorem firstComponent_full_inputSupport_of_comp_diagonal_ne_zero
    (C : Word R) (hmono : IsMonomial R)
    (first second : C.BoundaryFreeMorphismCoefficientComponent C)
    {x : Q} (i : C.PositionAt x)
    (hne : C.morphismCoefficientAt C hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono first ≫
        C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (C.diagonalMorphismCoefficientPosition i) ≠ 0) :
    ∀ {y : Q} (l : C.PositionAt y),
      ∃ j : C.PositionAt y,
        Relation.EqvGen (C.MorphismCoefficientStep C)
          first.1.representative ⟨y, l, j⟩ := by
  intro y l
  let product :=
    C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono first ≫
      C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second
  have hcoeff :
      C.morphismCoefficientAt C hmono hmono product
          (C.diagonalMorphismCoefficientPosition l) =
        C.morphismCoefficientAt C hmono hmono product
          (C.diagonalMorphismCoefficientPosition i) := by
    rw [show C.morphismCoefficientAt C hmono hmono product
          (C.diagonalMorphismCoefficientPosition l) =
        C.endomorphismCoefficient hmono product l by rfl,
      show C.morphismCoefficientAt C hmono hmono product
          (C.diagonalMorphismCoefficientPosition i) =
        C.endomorphismCoefficient hmono product i by rfl,
      C.endomorphismCoefficient_eq_source hmono product l,
      C.endomorphismCoefficient_eq_source hmono product i]
  have hlne : C.morphismCoefficientAt C hmono hmono product
      (C.diagonalMorphismCoefficientPosition l) ≠ 0 := by
    rw [hcoeff]
    exact hne
  obtain ⟨j, hfirst, hsecond⟩ :=
    C.exists_intermediate_of_boundaryFreeComponentMap_comp_diagonal_ne_zero
      hmono first second l hlne
  exact ⟨j, hfirst⟩

/-- Full input support at the two word endpoints forces a full increasing or
full decreasing interval correspondence. -/
theorem firstComponent_endpointIndices_of_comp_diagonal_ne_zero
    (C : Word R) (hmono : IsMonomial R)
    (first second : C.BoundaryFreeMorphismCoefficientComponent C)
    {x : Q} (i : C.PositionAt x)
    (hne : C.morphismCoefficientAt C hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono first ≫
        C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (C.diagonalMorphismCoefficientPosition i) ≠ 0) :
    ∃ j₀ : C.PositionAt C.source, ∃ jₙ : C.PositionAt C.target,
      Relation.EqvGen (C.MorphismCoefficientStep C)
          first.1.representative ⟨C.source, C.sourcePosition, j₀⟩ ∧
      Relation.EqvGen (C.MorphismCoefficientStep C)
          first.1.representative ⟨C.target, C.targetPosition, jₙ⟩ ∧
      ((j₀.index = 0 ∧ jₙ.index = C.length) ∨
        (j₀.index = C.length ∧ jₙ.index = 0)) := by
  obtain ⟨j₀, hj₀⟩ :=
    C.firstComponent_full_inputSupport_of_comp_diagonal_ne_zero
      hmono first second i hne C.sourcePosition
  obtain ⟨jₙ, hjₙ⟩ :=
    C.firstComponent_full_inputSupport_of_comp_diagonal_ne_zero
      hmono first second i hne C.targetPosition
  refine ⟨j₀, jₙ, hj₀, hjₙ, ?_⟩
  let p₀ : C.MorphismCoefficientPosition C :=
    ⟨C.source, C.sourcePosition, j₀⟩
  let pₙ : C.MorphismCoefficientPosition C :=
    ⟨C.target, C.targetPosition, jₙ⟩
  have hcomponent :
      Relation.EqvGen (C.MorphismCoefficientStep C) p₀ pₙ :=
    Relation.EqvGen.trans _ first.1.representative _
      (Relation.EqvGen.symm _ _ hj₀) hjₙ
  have hslope :=
    C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      C hcomponent (by
        change C.sourcePosition.index ≤ C.targetPosition.index
        simp)
  change jₙ.index = j₀.index + (C.length - 0) ∨
    j₀.index = jₙ.index + (C.length - 0) at hslope
  have hj₀le := j₀.index_le
  have hjₙle := jₙ.index_le
  rcases hslope with hslope | hslope
  · left
    constructor <;> omega
  · right
    constructor <;> omega

/-- A proper self-component cannot be a full reversal of the word-position
interval.  At an even midpoint it would meet the diagonal; at an odd
midpoint it would match one word edge with the same edge traversed in the
opposite direction. -/
theorem not_full_reversing_boundaryFreeComponent
    (C : Word R)
    (component : C.BoundaryFreeMorphismCoefficientComponent C)
    (hproper : component.1 ≠ C.diagonalMorphismCoefficientComponent)
    (j₀ : C.PositionAt C.source) (jₙ : C.PositionAt C.target)
    (hj₀ : Relation.EqvGen (C.MorphismCoefficientStep C)
      component.1.representative ⟨C.source, C.sourcePosition, j₀⟩)
    (hjₙ : Relation.EqvGen (C.MorphismCoefficientStep C)
      component.1.representative ⟨C.target, C.targetPosition, jₙ⟩)
    (hj₀Index : j₀.index = C.length) :
    False := by
  let p₀ : C.MorphismCoefficientPosition C :=
    ⟨C.source, C.sourcePosition, j₀⟩
  let pₙ : C.MorphismCoefficientPosition C :=
    ⟨C.target, C.targetPosition, jₙ⟩
  let support₀ : C.MorphismCoefficientComponentSupport C p₀ :=
    ⟨p₀, Relation.EqvGen.refl _⟩
  let supportₙ : C.MorphismCoefficientComponentSupport C p₀ :=
    ⟨pₙ, Relation.EqvGen.trans _ component.1.representative _
      (Relation.EqvGen.symm _ _ hj₀) hjₙ⟩
  rcases Nat.even_or_odd' C.length with ⟨m, hlength | hlength⟩
  · obtain ⟨r, hrIndex⟩ :=
      C.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
        C p₀ support₀ supportₙ m (by
          change 0 ≤ m
          omega)
        (by
          change m ≤ C.length
          omega)
    rcases r with ⟨⟨z, l, l'⟩, hr⟩
    change l.index = m at hrIndex
    have hp₀r :
        Relation.EqvGen (C.MorphismCoefficientStep C) p₀
          (⟨z, l, l'⟩ : C.MorphismCoefficientPosition C) :=
      hr
    have hcomponentR :
        Relation.EqvGen (C.MorphismCoefficientStep C)
          component.1.representative ⟨z, l, l'⟩ :=
      Relation.EqvGen.trans _ p₀ _ hj₀ hr
    have hslope :=
      C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
        C hp₀r (by
          change 0 ≤ l.index
          omega)
    have hrOutputLe := l'.index_le
    have hrOutput : l'.index = m := by
      change
        l'.index =
            j₀.index + (l.index - C.sourcePosition.index) ∨
          j₀.index =
            l'.index + (l.index - C.sourcePosition.index)
        at hslope
      simp only [sourcePosition_index, Nat.sub_zero] at hslope
      rcases hslope with hslope | hslope <;> omega
    have hll' : l = l' := PositionAt.ext_index (by
      exact hrIndex.trans hrOutput.symm)
    subst l'
    exact C.not_representative_eqvGen_diagonal_of_ne
      component.1 hproper l (by
        simpa [diagonalMorphismCoefficientPosition] using hcomponentR)
  · obtain ⟨r, hrIndex⟩ :=
      C.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
        C p₀ support₀ supportₙ m (by
          change 0 ≤ m
          omega)
        (by
          change m ≤ C.length
          omega)
    obtain ⟨s, hsIndex⟩ :=
      C.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
        C p₀ support₀ supportₙ (m + 1) (by
          change 0 ≤ m + 1
          omega)
        (by
          change m + 1 ≤ C.length
          omega)
    rcases r with ⟨⟨z, l, l'⟩, hr⟩
    rcases s with ⟨⟨w, t, t'⟩, hs⟩
    change l.index = m at hrIndex
    change t.index = m + 1 at hsIndex
    have hp₀r :
        Relation.EqvGen (C.MorphismCoefficientStep C) p₀
          (⟨z, l, l'⟩ : C.MorphismCoefficientPosition C) :=
      hr
    have hp₀s :
        Relation.EqvGen (C.MorphismCoefficientStep C) p₀
          (⟨w, t, t'⟩ : C.MorphismCoefficientPosition C) :=
      hs
    have hrSlope :=
      C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
        C hp₀r (by
          change 0 ≤ l.index
          omega)
    have hsSlope :=
      C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
        C hp₀s (by
          change 0 ≤ t.index
          omega)
    have hrOutputLe := l'.index_le
    have hsOutputLe := t'.index_le
    have hrOutput : l'.index = m + 1 := by
      change
        l'.index =
            j₀.index + (l.index - C.sourcePosition.index) ∨
          j₀.index =
            l'.index + (l.index - C.sourcePosition.index)
        at hrSlope
      simp only [sourcePosition_index, Nat.sub_zero] at hrSlope
      rcases hrSlope with hrSlope | hrSlope <;> omega
    have hsOutput : t'.index = m := by
      change
        t'.index =
            j₀.index + (t.index - C.sourcePosition.index) ∨
          j₀.index =
            t'.index + (t.index - C.sourcePosition.index)
        at hsSlope
      simp only [sourcePosition_index, Nat.sub_zero] at hsSlope
      rcases hsSlope with hsSlope | hsSlope <;> omega
    have hrsEqv :
        Relation.EqvGen (C.MorphismCoefficientStep C)
          (⟨z, l, l'⟩ : C.MorphismCoefficientPosition C)
          (⟨w, t, t'⟩ : C.MorphismCoefficientPosition C) :=
      Relation.EqvGen.trans _ p₀ _
        (Relation.EqvGen.symm _ _ hr) hs
    have hrsForward :=
      C.reflTransGen_morphismCoefficientForwardStep_of_eqvGen_of_inputIndex_le
        C hrsEqv (by
          change l.index ≤ t.index
          omega)
    have hrsStep :=
      C.morphismCoefficientForwardStep_of_reflTransGen_of_inputIndex_add_one
        C hrsForward (by
          change t.index = l.index + 1
          omega)
    have hrsInputPosition :
        (⟨z, l⟩ : C.Position) = (⟨w, t'⟩ : C.Position) :=
      Position.ext_index (hrIndex.trans hsOutput.symm)
    have hrsOutputPosition :
        (⟨z, l'⟩ : C.Position) = (⟨w, t⟩ : C.Position) :=
      Position.ext_index (hrOutput.trans hsIndex.symm)
    have hzw : z = w := congrArg Sigma.fst hrsInputPosition
    subst w
    have hlt' : l = t' := PositionAt.ext_index (by
      exact hrIndex.trans hsOutput.symm)
    have hl't : l' = t := PositionAt.ext_index (by
      exact hrOutput.trans hsIndex.symm)
    subst t'
    subst t
    rcases hrsStep.1 with hrs | hrs
    · cases hrs with
      | ofArrow a i j i' j' hij hij' =>
        exact C.not_arrowSteps_reverse_of_index_add_one
          hij hij' (by exact hrsStep.2)
    · cases hrs with
      | ofArrow a i j i' j' hij hij' =>
        exact C.not_arrowSteps_reverse_of_index_add_one
          hij' hij (by exact hrsStep.2)

/-- The product of two proper self-component basis maps has zero diagonal
coordinate. -/
theorem morphismCoefficientAt_properComponentMap_comp_diagonal_eq_zero
    (C : Word R) (hmono : IsMonomial R)
    (first second : C.ProperBoundaryFreeMorphismCoefficientComponent)
    {x : Q} (i : C.PositionAt x) :
    C.morphismCoefficientAt C hmono hmono
      (C.properBoundaryFreeMorphismCoefficientComponentMap hmono first ≫
        C.properBoundaryFreeMorphismCoefficientComponentMap hmono second)
      (C.diagonalMorphismCoefficientPosition i) = 0 := by
  by_contra hne
  obtain ⟨j₀, jₙ, hj₀, hjₙ, hendpoints⟩ :=
    C.firstComponent_endpointIndices_of_comp_diagonal_ne_zero
      hmono first.1 second.1 i hne
  rcases hendpoints with hincreasing | hreversing
  · have hj₀Eq : j₀ = C.sourcePosition :=
      PositionAt.ext_index (hincreasing.1.trans C.sourcePosition_index.symm)
    subst j₀
    exact first.2 (by
      apply (C.representative_eqv_iff C first.1.1
        C.diagonalMorphismCoefficientComponent).mp
      exact Relation.EqvGen.trans _ (C.diagonalMorphismCoefficientPosition
          C.sourcePosition) _
        hj₀
        (Relation.EqvGen.symm _ _
          C.diagonalMorphismCoefficientComponent_representative_eqvGen_source))
  · exact C.not_full_reversing_boundaryFreeComponent first.1 first.2
      j₀ jₙ hj₀ hjₙ hreversing.1

/-- The diagonal coordinate vanishes on the composite of any two elements
of the proper-component span. -/
theorem diagonalMorphismCoefficientLinearMap_comp_eq_zero_of_mem_proper
    (C : Word R) (hmono : IsMonomial R)
    {f g : C.rightModule hmono ⟶ C.rightModule hmono}
    (hf : f ∈ C.properMorphismCoefficientComponentSubspace hmono)
    (hg : g ∈ C.properMorphismCoefficientComponentSubspace hmono) :
    C.diagonalMorphismCoefficientLinearMap hmono (f ≫ g) = 0 := by
  rw [properMorphismCoefficientComponentSubspace] at hf hg
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem f g hf hg =>
      rcases hf with ⟨first, rfl⟩
      rcases hg with ⟨second, rfl⟩
      rw [C.diagonalMorphismCoefficientLinearMap_apply,
        C.morphismCoefficientAt_diagonalComponent_representative_eq_source]
      exact C.morphismCoefficientAt_properComponentMap_comp_diagonal_eq_zero
        hmono first second C.sourcePosition
  | zero_left g hg =>
      simp
  | zero_right f hf =>
      simp
  | add_left f g h hf hg hh hfh hgh =>
      simpa using congrArg₂ (· + ·) hfh hgh
  | add_right f g h hf hg hh hfg hfh =>
      simpa using congrArg₂ (· + ·) hfg hfh
  | smul_left c f g hf hg hfg =>
      simpa using congrArg (c * ·) hfg
  | smul_right c f g hf hg hfg =>
      simpa [mul_comm] using congrArg (c * ·) hfg

/-- The diagonal graph coordinate is multiplicative on the full string
endomorphism ring. -/
theorem diagonalMorphismCoefficientLinearMap_comp
    (C : Word R) (hmono : IsMonomial R)
    (f g : C.rightModule hmono ⟶ C.rightModule hmono) :
    C.diagonalMorphismCoefficientLinearMap hmono (f ≫ g) =
      C.diagonalMorphismCoefficientLinearMap hmono f *
        C.diagonalMorphismCoefficientLinearMap hmono g := by
  let cf := C.diagonalMorphismCoefficientLinearMap hmono f
  let cg := C.diagonalMorphismCoefficientLinearMap hmono g
  obtain ⟨r, hr, hfr⟩ :=
    C.exists_eq_smul_id_add_mem_properComponentSubspace hmono f
  obtain ⟨s, hs, hgs⟩ :=
    C.exists_eq_smul_id_add_mem_properComponentSubspace hmono g
  have hrdiag : C.diagonalMorphismCoefficientLinearMap hmono r = 0 := by
    rw [C.properMorphismCoefficientComponentSubspace_eq_ker] at hr
    exact hr
  have hsdiag : C.diagonalMorphismCoefficientLinearMap hmono s = 0 := by
    rw [C.properMorphismCoefficientComponentSubspace_eq_ker] at hs
    exact hs
  have hrsdiag :
      C.diagonalMorphismCoefficientLinearMap hmono (r ≫ s) = 0 :=
    C.diagonalMorphismCoefficientLinearMap_comp_eq_zero_of_mem_proper
      hmono hr hs
  rw [hfr, hgs]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul,
    Category.comp_id, Category.id_comp, map_add, map_smul,
    C.diagonalMorphismCoefficientLinearMap_id, hrdiag, hsdiag, hrsdiag,
    mul_zero, add_zero, smul_eq_mul, mul_one]
  simp [mul_comm]

/-- The proper-component subspace is closed under composition. -/
theorem properMorphismCoefficientComponentSubspace_comp_mem
    (C : Word R) (hmono : IsMonomial R)
    {f g : C.rightModule hmono ⟶ C.rightModule hmono}
    (hf : f ∈ C.properMorphismCoefficientComponentSubspace hmono)
    (hg : g ∈ C.properMorphismCoefficientComponentSubspace hmono) :
    f ≫ g ∈ C.properMorphismCoefficientComponentSubspace hmono := by
  rw [C.properMorphismCoefficientComponentSubspace_eq_ker]
  exact C.diagonalMorphismCoefficientLinearMap_comp_eq_zero_of_mem_proper
    hmono hf hg

/-- The proper-component subspace is stable under postcomposition by an
arbitrary endomorphism. -/
theorem properMorphismCoefficientComponentSubspace_comp_mem_of_mem_left
    (C : Word R) (hmono : IsMonomial R)
    {r f : C.rightModule hmono ⟶ C.rightModule hmono}
    (hr : r ∈ C.properMorphismCoefficientComponentSubspace hmono) :
    r ≫ f ∈ C.properMorphismCoefficientComponentSubspace hmono := by
  rw [C.properMorphismCoefficientComponentSubspace_eq_ker]
  have hrdiag :
      C.diagonalMorphismCoefficientLinearMap hmono r = 0 := by
    rw [C.properMorphismCoefficientComponentSubspace_eq_ker] at hr
    exact hr
  change C.diagonalMorphismCoefficientLinearMap hmono (r ≫ f) = 0
  rw [C.diagonalMorphismCoefficientLinearMap_comp, hrdiag, zero_mul]

/-- The proper-component subspace is stable under precomposition by an
arbitrary endomorphism. -/
theorem properMorphismCoefficientComponentSubspace_comp_mem_of_mem_right
    (C : Word R) (hmono : IsMonomial R)
    {f r : C.rightModule hmono ⟶ C.rightModule hmono}
    (hr : r ∈ C.properMorphismCoefficientComponentSubspace hmono) :
    f ≫ r ∈ C.properMorphismCoefficientComponentSubspace hmono := by
  rw [C.properMorphismCoefficientComponentSubspace_eq_ker]
  have hrdiag :
      C.diagonalMorphismCoefficientLinearMap hmono r = 0 := by
    rw [C.properMorphismCoefficientComponentSubspace_eq_ker] at hr
    exact hr
  change C.diagonalMorphismCoefficientLinearMap hmono (f ≫ r) = 0
  rw [C.diagonalMorphismCoefficientLinearMap_comp, hrdiag, mul_zero]

end MagnitudeConjecture.BoundQuiver.StringWord.Word
