import MagnitudeConjecture.Algebra.StringHookCohookGraphComponent
import MagnitudeConjecture.Algebra.StringGraphComponentComposition
import MagnitudeConjecture.Algebra.StringGraphComponentInterval

/-!
# Extracting graph components from string-map factorizations

A nonzero coefficient of a composite selects an intermediate position where
both factor coefficients are nonzero.  The two coefficient components through
that position have product coefficient exactly one: partial-bijection
uniqueness leaves no second intermediate position and hence no
characteristic-dependent cancellation.  Full input or output support of a
selected output component then transfers to the corresponding factor
component.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

noncomputable local instance factorizationPositionAtFintype
    (C : Word R) (x : Q) : Fintype (C.PositionAt x) :=
  Fintype.ofFinite _

/-- A nonzero coefficient of an arbitrary composite has an intermediate
position at which both factor coefficients are nonzero. -/
theorem exists_intermediate_of_comp_coefficient_ne_zero
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (g : D.rightModule hD ⟶ E.rightModule hE)
    (p : C.MorphismCoefficientPosition E)
    (hne : C.morphismCoefficientAt E hC hE (f ≫ g) p ≠ 0) :
    ∃ j : D.PositionAt p.1,
      C.morphismCoefficientAt D hC hD f ⟨p.1, p.2.1, j⟩ ≠ 0 ∧
      D.morphismCoefficientAt E hD hE g ⟨p.1, j, p.2.2⟩ ≠ 0 := by
  classical
  rw [C.morphismCoefficientAt_comp D E hC hD hE] at hne
  by_contra h
  apply hne
  apply Finset.sum_eq_zero
  intro j _
  have hj : ¬ (C.morphismCoefficientAt D hC hD f
        ⟨p.1, p.2.1, j⟩ ≠ 0 ∧
      D.morphismCoefficientAt E hD hE g
        ⟨p.1, j, p.2.2⟩ ≠ 0) := by
    intro hj
    exact h ⟨j, hj⟩
  rcases not_and_or.mp hj with hfirst | hsecond
  · rw [not_ne_iff.mp hfirst, zero_mul]
  · rw [not_ne_iff.mp hsecond, mul_zero]

/-- Component basis maps whose supports meet at one intermediate position
have composite coefficient one at the induced outside pair. -/
theorem morphismCoefficientAt_componentMaps_comp_eq_one_of_intermediate
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    {x : Q} (i : C.PositionAt x) (j : D.PositionAt x)
    (l : E.PositionAt x)
    (hfirst : Relation.EqvGen (C.MorphismCoefficientStep D)
      first.1.representative ⟨x, i, j⟩)
    (hsecond : Relation.EqvGen (D.MorphismCoefficientStep E)
      second.1.representative ⟨x, j, l⟩) :
    C.morphismCoefficientAt E hC hE
        (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
          D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
        ⟨x, i, l⟩ = 1 := by
  classical
  rw [C.morphismCoefficientAt_boundaryFreeComponentMap_comp]
  rw [Finset.sum_eq_single j]
  · rw [C.coefficientComponentIndicator_eq_one D _ _ hfirst,
      D.coefficientComponentIndicator_eq_one E _ _ hsecond,
      one_mul]
  · intro t _ ht
    rw [C.coefficientComponentIndicator_eq_zero D]
    · simp
    · intro htSupport
      have hpositions :
          (⟨x, i, j⟩ : C.MorphismCoefficientPosition D) = ⟨x, i, t⟩ :=
        C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq D
          (Relation.EqvGen.trans _ first.1.representative _
            hfirst.symm htSupport) rfl
      have htj : t = j := by
        cases hpositions
        rfl
      exact ht htj
  · simp

/-- A nonzero coefficient of a product of two graph-component basis maps has
an intermediate position supported by both components. -/
theorem exists_intermediate_of_componentMaps_comp_coefficient_ne_zero
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (p : C.MorphismCoefficientPosition E)
    (hne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      p ≠ 0) :
    ∃ j : D.PositionAt p.1,
      Relation.EqvGen (C.MorphismCoefficientStep D)
        first.1.representative ⟨p.1, p.2.1, j⟩ ∧
      Relation.EqvGen (D.MorphismCoefficientStep E)
        second.1.representative ⟨p.1, j, p.2.2⟩ := by
  classical
  rw [C.morphismCoefficientAt_boundaryFreeComponentMap_comp] at hne
  by_contra h
  apply hne
  apply Finset.sum_eq_zero
  intro j _
  have hj : ¬ (Relation.EqvGen (C.MorphismCoefficientStep D)
        first.1.representative ⟨p.1, p.2.1, j⟩ ∧
      Relation.EqvGen (D.MorphismCoefficientStep E)
        second.1.representative ⟨p.1, j, p.2.2⟩) := by
    intro hj
    exact h ⟨j, hj⟩
  rcases not_and_or.mp hj with hfirst | hsecond
  · rw [C.coefficientComponentIndicator_eq_zero D _ _ hfirst, zero_mul]
  · rw [D.coefficientComponentIndicator_eq_zero E _ _ hsecond, mul_zero]

/-- From a nonzero coefficient of an arbitrary composite, select one
component from each factor whose basis-map product has coefficient exactly
one at the same outside position. -/
theorem exists_component_pair_of_comp_coefficient_ne_zero
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (g : D.rightModule hD ⟶ E.rightModule hE)
    (p : C.MorphismCoefficientPosition E)
    (hne : C.morphismCoefficientAt E hC hE (f ≫ g) p ≠ 0) :
    ∃ (first : C.BoundaryFreeMorphismCoefficientComponent D)
      (second : D.BoundaryFreeMorphismCoefficientComponent E),
      C.morphismCoefficientAt D hC hD f first.1.representative ≠ 0 ∧
      D.morphismCoefficientAt E hD hE g second.1.representative ≠ 0 ∧
      C.morphismCoefficientAt E hC hE
        (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
          D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
        p = 1 := by
  rcases p with ⟨x, i, l⟩
  obtain ⟨j, hfirstCoefficient, hsecondCoefficient⟩ :=
    C.exists_intermediate_of_comp_coefficient_ne_zero D E hC hD hE
      f g ⟨x, i, l⟩ hne
  let firstRoot : C.MorphismCoefficientPosition D := ⟨x, i, j⟩
  let secondRoot : D.MorphismCoefficientPosition E := ⟨x, j, l⟩
  let hfirstFree := C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    D hC hD f firstRoot hfirstCoefficient
  let hsecondFree := D.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    E hD hE g secondRoot hsecondCoefficient
  let first := C.boundaryFreeMorphismCoefficientComponentOf
    D firstRoot hfirstFree
  let second := D.boundaryFreeMorphismCoefficientComponentOf
    E secondRoot hsecondFree
  have hfirstSupport : Relation.EqvGen (C.MorphismCoefficientStep D)
      first.1.representative ⟨x, i, j⟩ := by
    exact C.boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
      D firstRoot hfirstFree
  have hsecondSupport : Relation.EqvGen (D.MorphismCoefficientStep E)
      second.1.representative ⟨x, j, l⟩ := by
    exact D.boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
      E secondRoot hsecondFree
  have hfirstRepresentative : C.morphismCoefficientAt D hC hD f
      first.1.representative ≠ 0 :=
    (C.morphismCoefficientAt_ne_zero_iff_of_eqvGen D hC hD f
      hfirstSupport).mpr hfirstCoefficient
  have hsecondRepresentative : D.morphismCoefficientAt E hD hE g
      second.1.representative ≠ 0 :=
    (D.morphismCoefficientAt_ne_zero_iff_of_eqvGen E hD hE g
      hsecondSupport).mpr hsecondCoefficient
  exact ⟨first, second, hfirstRepresentative, hsecondRepresentative,
    C.morphismCoefficientAt_componentMaps_comp_eq_one_of_intermediate
      D E hC hD hE first second i j l hfirstSupport hsecondSupport⟩

/-- Full source support of an output component transfers to the first factor
component whenever their product is nonzero on the output component. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.first_of_comp
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (output : C.BoundaryFreeMorphismCoefficientComponent E)
    (houtput : output.HasFullInputSupport)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (hne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      output.1.representative ≠ 0) :
    first.HasFullInputSupport := by
  intro x i
  obtain ⟨l, hl⟩ := houtput i
  have hpne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      ⟨x, i, l⟩ ≠ 0 := by
    have heq := C.morphismCoefficientAt_eq_of_eqvGen E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second) hl
    rw [heq] at hne
    exact hne
  obtain ⟨j, hfirst, _⟩ :=
    C.exists_intermediate_of_componentMaps_comp_coefficient_ne_zero
      D E hC hD hE first second ⟨x, i, l⟩ hpne
  exact ⟨j, hfirst⟩

/-- Full target support of an output component transfers to the second factor
component whenever their product is nonzero on the output component. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.second_of_comp
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (output : C.BoundaryFreeMorphismCoefficientComponent E)
    (houtput : output.HasFullOutputSupport)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (hne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      output.1.representative ≠ 0) :
    second.HasFullOutputSupport := by
  intro x l
  obtain ⟨i, hi⟩ := houtput l
  have hpne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      ⟨x, i, l⟩ ≠ 0 := by
    have heq := C.morphismCoefficientAt_eq_of_eqvGen E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second) hi
    rw [heq] at hne
    exact hne
  obtain ⟨j, _, hsecond⟩ :=
    C.exists_intermediate_of_componentMaps_comp_coefficient_ne_zero
      D E hC hD hE first second ⟨x, i, l⟩ hpne
  exact ⟨j, hsecond⟩

/-- A factorization of one graph-basis map selects a pair of factor
components with coefficient one on the output component.  Any full support
of the output transfers to the corresponding selected factor. -/
theorem exists_component_pair_of_factorization_eq_componentMap
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (output : C.BoundaryFreeMorphismCoefficientComponent E)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (g : D.rightModule hD ⟶ E.rightModule hE)
    (hfactor : f ≫ g =
      C.boundaryFreeMorphismCoefficientComponentMap E hC hE output) :
    ∃ (first : C.BoundaryFreeMorphismCoefficientComponent D)
      (second : D.BoundaryFreeMorphismCoefficientComponent E),
      C.morphismCoefficientAt D hC hD f first.1.representative ≠ 0 ∧
      D.morphismCoefficientAt E hD hE g second.1.representative ≠ 0 ∧
      C.morphismCoefficientAt E hC hE
        (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
          D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
        output.1.representative = 1 ∧
      (output.HasFullInputSupport → first.HasFullInputSupport) ∧
      (output.HasFullOutputSupport → second.HasFullOutputSupport) := by
  have hcoefficient : C.morphismCoefficientAt E hC hE (f ≫ g)
      output.1.representative = 1 := by
    rw [hfactor, C.morphismCoefficientAt_boundaryFreeComponentMap,
      C.coefficientComponentIndicator_eq_one E _ _
        (Relation.EqvGen.refl _)]
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient, hproduct⟩ :=
    C.exists_component_pair_of_comp_coefficient_ne_zero D E hC hD hE
      f g output.1.representative (hcoefficient.trans_ne one_ne_zero)
  refine ⟨first, second, hfirstCoefficient, hsecondCoefficient,
    hproduct, ?_, ?_⟩
  · intro hfull
    exact hfull.first_of_comp C D E hC hD hE output first second
      (hproduct.trans_ne one_ne_zero)
  · intro hfull
    exact hfull.second_of_comp C D E hC hD hE output first second
      (hproduct.trans_ne one_ne_zero)

/-- A factorization of a right hook projection through a literal string
module selects a second factor component with full target support. -/
theorem HookExtension.exists_component_pair_of_moduleMap_factorization
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (f : D.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    ∃ (first : D.BoundaryFreeMorphismCoefficientComponent M)
      (second : M.BoundaryFreeMorphismCoefficientComponent C),
      D.morphismCoefficientAt M hmono hmono f first.1.representative ≠ 0 ∧
      M.morphismCoefficientAt C hmono hmono g second.1.representative ≠ 0 ∧
      D.morphismCoefficientAt C hmono hmono
        (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
          M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
        (hook.moduleMapComponent hmono).1.representative = 1 ∧
      second.HasFullOutputSupport := by
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient,
      hproduct, _, hsecond⟩ :=
    D.exists_component_pair_of_factorization_eq_componentMap M C
      hmono hmono hmono (hook.moduleMapComponent hmono) f g
      (hfactor.trans (hook.moduleMap_eq_componentMap hmono))
  exact ⟨first, second, hfirstCoefficient, hsecondCoefficient, hproduct,
    hsecond (hook.moduleMapComponent_hasFullOutputSupport hmono)⟩

/-- A factorization of a right cohook inclusion through a literal string
module selects a first factor component with full source support. -/
theorem CohookExtension.exists_component_pair_of_moduleMap_factorization
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    ∃ (first : C.BoundaryFreeMorphismCoefficientComponent M)
      (second : M.BoundaryFreeMorphismCoefficientComponent D),
      C.morphismCoefficientAt M hmono hmono f first.1.representative ≠ 0 ∧
      M.morphismCoefficientAt D hmono hmono g second.1.representative ≠ 0 ∧
      C.morphismCoefficientAt D hmono hmono
        (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
          M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
        (cohook.moduleMapComponent hmono).1.representative = 1 ∧
      first.HasFullInputSupport := by
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient,
      hproduct, hfirst, _⟩ :=
    C.exists_component_pair_of_factorization_eq_componentMap M D
      hmono hmono hmono (cohook.moduleMapComponent hmono) f g
      (hfactor.trans (cohook.moduleMap_eq_componentMap hmono))
  exact ⟨first, second, hfirstCoefficient, hsecondCoefficient, hproduct,
    hfirst (cohook.moduleMapComponent_hasFullInputSupport hmono)⟩

/-- A factorization of a left hook projection through a literal string
module selects a second factor component with full target support. -/
theorem LeftHookExtension.exists_component_pair_of_moduleMap_factorization
    {C M : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    (f : hook.result.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    ∃ (first : hook.result.BoundaryFreeMorphismCoefficientComponent M)
      (second : M.BoundaryFreeMorphismCoefficientComponent C),
      hook.result.morphismCoefficientAt M hmono hmono f
          first.1.representative ≠ 0 ∧
      M.morphismCoefficientAt C hmono hmono g second.1.representative ≠ 0 ∧
      hook.result.morphismCoefficientAt C hmono hmono
        (hook.result.boundaryFreeMorphismCoefficientComponentMap M
            hmono hmono first ≫
          M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
        (hook.moduleMapComponent hmono).1.representative = 1 ∧
      second.HasFullOutputSupport := by
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient,
      hproduct, _, hsecond⟩ :=
    hook.result.exists_component_pair_of_factorization_eq_componentMap M C
      hmono hmono hmono (hook.moduleMapComponent hmono) f g
      (hfactor.trans (hook.moduleMap_eq_componentMap hmono))
  exact ⟨first, second, hfirstCoefficient, hsecondCoefficient, hproduct,
    hsecond (hook.moduleMapComponent_hasFullOutputSupport hmono)⟩

/-- A factorization of a left cohook inclusion through a literal string
module selects a first factor component with full source support. -/
theorem LeftCohookExtension.exists_component_pair_of_moduleMap_factorization
    {C M : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ cohook.result.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    ∃ (first : C.BoundaryFreeMorphismCoefficientComponent M)
      (second : M.BoundaryFreeMorphismCoefficientComponent cohook.result),
      C.morphismCoefficientAt M hmono hmono f first.1.representative ≠ 0 ∧
      M.morphismCoefficientAt cohook.result hmono hmono g
          second.1.representative ≠ 0 ∧
      C.morphismCoefficientAt cohook.result hmono hmono
        (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
          M.boundaryFreeMorphismCoefficientComponentMap cohook.result
            hmono hmono second)
        (cohook.moduleMapComponent hmono).1.representative = 1 ∧
      first.HasFullInputSupport := by
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient,
      hproduct, hfirst, _⟩ :=
    C.exists_component_pair_of_factorization_eq_componentMap M cohook.result
      hmono hmono hmono (cohook.moduleMapComponent hmono) f g
      (hfactor.trans (cohook.moduleMap_eq_componentMap hmono))
  exact ⟨first, second, hfirstCoefficient, hsecondCoefficient, hproduct,
    hfirst (cohook.moduleMapComponent_hasFullInputSupport hmono)⟩

end MagnitudeConjecture.BoundQuiver.StringWord.Word
