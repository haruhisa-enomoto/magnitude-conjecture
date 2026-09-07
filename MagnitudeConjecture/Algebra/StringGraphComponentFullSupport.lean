import MagnitudeConjecture.Algebra.StringGraphComponentFactorization
import MagnitudeConjecture.Algebra.StringGraphComponentConvexity
import MagnitudeConjecture.Algebra.StringIndecomposable
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Full-support string graph components

The constant-slope interval normal form gives exact endpoint displacement for
a component which covers a whole source or target word.  In particular, full
source support forces the source word no longer than the target word, full
target support gives the opposite inequality, and two-sided full support
forces equal word lengths.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- A component covering its complete source word embeds the source position
line as one increasing or decreasing interval in the target word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.exists_endpointPositions
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport) :
    ∃ j₀ : D.PositionAt C.source, ∃ jₙ : D.PositionAt C.target,
      Relation.EqvGen (C.MorphismCoefficientStep D)
          component.1.representative ⟨C.source, C.sourcePosition, j₀⟩ ∧
      Relation.EqvGen (C.MorphismCoefficientStep D)
          component.1.representative ⟨C.target, C.targetPosition, jₙ⟩ ∧
      (jₙ.index = j₀.index + C.length ∨
        j₀.index = jₙ.index + C.length) := by
  obtain ⟨j₀, hj₀⟩ := hfull C.sourcePosition
  obtain ⟨jₙ, hjₙ⟩ := hfull C.targetPosition
  refine ⟨j₀, jₙ, hj₀, hjₙ, ?_⟩
  let p₀ : C.MorphismCoefficientPosition D :=
    ⟨C.source, C.sourcePosition, j₀⟩
  let pₙ : C.MorphismCoefficientPosition D :=
    ⟨C.target, C.targetPosition, jₙ⟩
  have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D) p₀ pₙ :=
    Relation.EqvGen.trans _ component.1.representative _ hj₀.symm hjₙ
  have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
    D hcomponent (by
      change C.sourcePosition.index ≤ C.targetPosition.index
      simp)
  change jₙ.index = j₀.index + (C.length - 0) ∨
    j₀.index = jₙ.index + (C.length - 0) at hslope
  simpa using hslope

/-- Full source support forces the source word no longer than the target
word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.source_length_le_target_length
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport) :
    C.length ≤ D.length := by
  obtain ⟨j₀, jₙ, _, _, hslope⟩ := hfull.exists_endpointPositions component
  have hj₀ := j₀.index_le
  have hjₙ := jₙ.index_le
  omega

/-- A component covering its complete target word embeds the target position
line as one increasing or decreasing interval in the source word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.exists_endpointPositions
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport) :
    ∃ i₀ : C.PositionAt D.source, ∃ iₙ : C.PositionAt D.target,
      Relation.EqvGen (C.MorphismCoefficientStep D)
          component.1.representative ⟨D.source, i₀, D.sourcePosition⟩ ∧
      Relation.EqvGen (C.MorphismCoefficientStep D)
          component.1.representative ⟨D.target, iₙ, D.targetPosition⟩ ∧
      (iₙ.index = i₀.index + D.length ∨
        i₀.index = iₙ.index + D.length) := by
  obtain ⟨i₀, hi₀⟩ := hfull D.sourcePosition
  obtain ⟨iₙ, hiₙ⟩ := hfull D.targetPosition
  refine ⟨i₀, iₙ, hi₀, hiₙ, ?_⟩
  let p₀ : C.MorphismCoefficientPosition D :=
    ⟨D.source, i₀, D.sourcePosition⟩
  let pₙ : C.MorphismCoefficientPosition D :=
    ⟨D.target, iₙ, D.targetPosition⟩
  have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D) p₀ pₙ :=
    Relation.EqvGen.trans _ component.1.representative _ hi₀.symm hiₙ
  rcases le_total i₀.index iₙ.index with hle | hle
  · have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hle
    change D.length = 0 + (iₙ.index - i₀.index) ∨
      0 = D.length + (iₙ.index - i₀.index) at hslope
    left
    omega
  · have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent.symm hle
    change 0 = D.length + (i₀.index - iₙ.index) ∨
      D.length = 0 + (i₀.index - iₙ.index) at hslope
    right
    omega

/-- Full target support forces the target word no longer than the source
word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.target_length_le_source_length
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport) :
    D.length ≤ C.length := by
  obtain ⟨i₀, iₙ, _, _, hslope⟩ := hfull.exists_endpointPositions component
  have hi₀ := i₀.index_le
  have hiₙ := iₙ.index_le
  omega

/-- A component with full support on both words connects words of equal
length. -/
theorem BoundaryFreeMorphismCoefficientComponent.length_eq_of_fullSupport
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport) :
    C.length = D.length :=
  Nat.le_antisymm
    (hinput.source_length_le_target_length component)
    (houtput.target_length_le_source_length component)

/-- At equal word length, full target support already covers the complete
source word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.hasFullInputSupport_of_length_eq
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hlength : C.length = D.length) :
    component.HasFullInputSupport := by
  intro x i
  obtain ⟨i₀, iₙ, hi₀, hiₙ, hslope⟩ :=
    hfull.exists_endpointPositions component
  let p₀ : C.MorphismCoefficientPosition D :=
    ⟨D.source, i₀, D.sourcePosition⟩
  let pₙ : C.MorphismCoefficientPosition D :=
    ⟨D.target, iₙ, D.targetPosition⟩
  let s₀ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨p₀, hi₀⟩
  let sₙ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨pₙ, hiₙ⟩
  have hi₀le := i₀.index_le
  have hiₙle := iₙ.index_le
  have hiLe := i.index_le
  rcases hslope with hslope | hslope
  · have hi₀zero : i₀.index = 0 := by omega
    have hiₙlength : iₙ.index = C.length := by omega
    obtain ⟨r, hrIndex⟩ :=
      C.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
        D component.1.representative s₀ sₙ i.index (by
          change i₀.index ≤ i.index
          omega) (by
          change i.index ≤ iₙ.index
          omega)
    rcases r with ⟨⟨y, i', j⟩, hr⟩
    have hposition : (⟨y, i'⟩ : C.Position) = ⟨x, i⟩ :=
      Position.ext_index hrIndex
    cases hposition
    exact ⟨j, hr⟩
  · have hiₙzero : iₙ.index = 0 := by omega
    have hi₀length : i₀.index = C.length := by omega
    obtain ⟨r, hrIndex⟩ :=
      C.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
        D component.1.representative sₙ s₀ i.index (by
          change iₙ.index ≤ i.index
          omega) (by
          change i.index ≤ i₀.index
          omega)
    rcases r with ⟨⟨y, i', j⟩, hr⟩
    have hposition : (⟨y, i'⟩ : C.Position) = ⟨x, i⟩ :=
      Position.ext_index hrIndex
    cases hposition
    exact ⟨j, hr⟩

/-- At equal word length, full source support already covers the complete
target word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.hasFullOutputSupport_of_length_eq
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hlength : C.length = D.length) :
    component.HasFullOutputSupport := by
  intro x j
  obtain ⟨j₀, jₙ, hj₀, hjₙ, hslope⟩ :=
    hfull.exists_endpointPositions component
  let p₀ : C.MorphismCoefficientPosition D :=
    ⟨C.source, C.sourcePosition, j₀⟩
  let pₙ : C.MorphismCoefficientPosition D :=
    ⟨C.target, C.targetPosition, jₙ⟩
  let s₀ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨p₀, hj₀⟩
  let sₙ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨pₙ, hjₙ⟩
  have hj₀le := j₀.index_le
  have hjₙle := jₙ.index_le
  have hjLe := j.index_le
  rcases hslope with hslope | hslope
  · have hj₀zero : j₀.index = 0 := by omega
    have hjₙlength : jₙ.index = D.length := by omega
    obtain ⟨r, hrIndex⟩ :=
      C.exists_morphismCoefficientComponentSupport_outputIndex_eq_of_between
        D component.1.representative s₀ sₙ j.index (by
          change j₀.index ≤ j.index
          omega) (by
          change j.index ≤ jₙ.index
          omega)
    rcases r with ⟨⟨y, i, j'⟩, hr⟩
    have hposition : (⟨y, j'⟩ : D.Position) = ⟨x, j⟩ :=
      Position.ext_index hrIndex
    cases hposition
    exact ⟨i, hr⟩
  · have hjₙzero : jₙ.index = 0 := by omega
    have hj₀length : j₀.index = D.length := by omega
    obtain ⟨r, hrIndex⟩ :=
      C.exists_morphismCoefficientComponentSupport_outputIndex_eq_of_between
        D component.1.representative sₙ s₀ j.index (by
          change jₙ.index ≤ j.index
          omega) (by
          change j.index ≤ j₀.index
          omega)
    rcases r with ⟨⟨y, i, j'⟩, hr⟩
    have hposition : (⟨y, j'⟩ : D.Position) = ⟨x, j⟩ :=
      Position.ext_index hrIndex
    cases hposition
    exact ⟨i, hr⟩

/-- The unique source position supported below a given target position of a
full-output-support component. -/
def BoundaryFreeMorphismCoefficientComponent.inputPosition
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (houtput : component.HasFullOutputSupport)
    {x : Q} (j : D.PositionAt x) : C.PositionAt x :=
  Classical.choose (houtput j)

/-- The selected input position belongs to the component. -/
theorem BoundaryFreeMorphismCoefficientComponent.inputPosition_support
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (houtput : component.HasFullOutputSupport)
    {x : Q} (j : D.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, component.inputPosition houtput j, j⟩ :=
  Classical.choose_spec (houtput j)

/-- The selected input is the only input supported below the given target
position. -/
theorem BoundaryFreeMorphismCoefficientComponent.inputPosition_eq_of_support
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (houtput : component.HasFullOutputSupport)
    {x : Q} (j : D.PositionAt x) (i : C.PositionAt x)
    (hi : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, i, j⟩) :
    component.inputPosition houtput j = i := by
  apply PositionAt.ext_index
  have hselected := component.inputPosition_support houtput j
  have hpositions := C.eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq
    D (Relation.EqvGen.trans _ component.1.representative _
      hselected.symm hi) rfl
  exact congrArg MorphismCoefficientPosition.inputIndex hpositions

/-- A component's selected input-position map is injective. -/
theorem BoundaryFreeMorphismCoefficientComponent.inputPosition_injective
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (houtput : component.HasFullOutputSupport) {x : Q} :
    Function.Injective
      (component.inputPosition houtput : D.PositionAt x → C.PositionAt x) := by
  intro i j hij
  have hi := component.inputPosition_support houtput i
  have hj := component.inputPosition_support houtput j
  have hpq : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨x, component.inputPosition houtput i, i⟩ :
        C.MorphismCoefficientPosition D)
      ⟨x, component.inputPosition houtput j, j⟩ :=
    Relation.EqvGen.trans _ component.1.representative _ hi.symm hj
  have hpositions := C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq
    D hpq (congrArg PositionAt.index hij)
  exact PositionAt.ext_index
    (congrArg MorphismCoefficientPosition.outputIndex hpositions)

/-- The unique target position supported above a given source position of a
full-input-support component. -/
def BoundaryFreeMorphismCoefficientComponent.outputPosition
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    {x : Q} (i : C.PositionAt x) : D.PositionAt x :=
  Classical.choose (hinput i)

/-- The selected output position belongs to the component. -/
theorem BoundaryFreeMorphismCoefficientComponent.outputPosition_support
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, i, component.outputPosition hinput i⟩ :=
  Classical.choose_spec (hinput i)

/-- The selected output is the only output supported above the given source
position. -/
theorem BoundaryFreeMorphismCoefficientComponent.outputPosition_eq_of_support
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    {x : Q} (i : C.PositionAt x) (j : D.PositionAt x)
    (hj : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, i, j⟩) :
    component.outputPosition hinput i = j := by
  apply PositionAt.ext_index
  have hselected := component.outputPosition_support hinput i
  have hpositions := C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq
    D (Relation.EqvGen.trans _ component.1.representative _
      hselected.symm hj) rfl
  exact congrArg MorphismCoefficientPosition.outputIndex hpositions

/-- A component's selected output-position map is injective. -/
theorem BoundaryFreeMorphismCoefficientComponent.outputPosition_injective
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport) {x : Q} :
    Function.Injective
      (component.outputPosition hinput : C.PositionAt x → D.PositionAt x) := by
  intro i j hij
  have hi := component.outputPosition_support hinput i
  have hj := component.outputPosition_support hinput j
  have hpq : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨x, i, component.outputPosition hinput i⟩ :
        C.MorphismCoefficientPosition D)
      ⟨x, j, component.outputPosition hinput j⟩ :=
    Relation.EqvGen.trans _ component.1.representative _ hi.symm hj
  have hpositions := C.eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq
    D hpq (congrArg PositionAt.index hij)
  exact PositionAt.ext_index
    (congrArg MorphismCoefficientPosition.inputIndex hpositions)

/-- Full output support makes the selected output-position map surjective. -/
theorem BoundaryFreeMorphismCoefficientComponent.outputPosition_surjective
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport) {x : Q} :
    Function.Surjective
      (component.outputPosition hinput : C.PositionAt x → D.PositionAt x) := by
  intro j
  obtain ⟨i, hi⟩ := houtput j
  refine ⟨i, ?_⟩
  have hselected := component.outputPosition_support hinput i
  have hpq : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨x, i, component.outputPosition hinput i⟩ :
        C.MorphismCoefficientPosition D) ⟨x, i, j⟩ :=
    Relation.EqvGen.trans _ component.1.representative _ hselected.symm hi
  have hpositions := C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq
    D hpq rfl
  cases hpositions
  rfl

/-- Two-sided full support gives a position equivalence on every displayed
vertex. -/
def BoundaryFreeMorphismCoefficientComponent.outputPositionEquiv
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport) (x : Q) :
    C.PositionAt x ≃ D.PositionAt x :=
  Equiv.ofBijective (component.outputPosition hinput)
    ⟨component.outputPosition_injective hinput,
      component.outputPosition_surjective hinput houtput⟩

@[simp]
theorem BoundaryFreeMorphismCoefficientComponent.outputPositionEquiv_apply
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport)
    {x : Q} (i : C.PositionAt x) :
    component.outputPositionEquiv hinput houtput x i =
      component.outputPosition hinput i :=
  rfl

/-- On a source basis position, a full-input component indicator is the
single target basis vector selected above it. -/
theorem BoundaryFreeMorphismCoefficientComponent.coefficientComponentOnBasis_eq_single
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    {x : Q} (i : C.PositionAt x) :
    C.coefficientComponentOnBasis D component.1.representative i =
      Finsupp.single (component.outputPosition hinput i) 1 := by
  classical
  apply Finsupp.ext
  intro j
  rw [C.coefficientComponentOnBasis_apply, Finsupp.single_apply]
  by_cases hj : component.outputPosition hinput i = j
  · rw [if_pos hj]
    exact C.coefficientComponentIndicator_eq_one D _ _
      (hj ▸ component.outputPosition_support hinput i)
  · rw [if_neg hj]
    apply C.coefficientComponentIndicator_eq_zero D
    intro hjSupport
    have hselected := component.outputPosition_support hinput i
    have hpq : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨x, i, component.outputPosition hinput i⟩ :
          C.MorphismCoefficientPosition D) ⟨x, i, j⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hselected.symm hjSupport
    have hpositions := C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq
      D hpq rfl
    apply hj
    cases hpositions
    rfl

/-- With two-sided full support, the component indicator linear map is the
coordinate permutation induced by the position equivalence. -/
theorem BoundaryFreeMorphismCoefficientComponent.coefficientComponentLinearMap_eq_domLCongr
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport) (x : Q) :
    C.coefficientComponentLinearMap D component.1.representative x =
      (Finsupp.domLCongr (component.outputPositionEquiv hinput houtput x) :
        C.Space x ≃ₗ[k] D.Space x).toLinearMap := by
  apply Finsupp.lhom_ext
  intro i c
  rw [C.coefficientComponentLinearMap_single,
    component.coefficientComponentOnBasis_eq_single hinput]
  change c • Finsupp.single (component.outputPosition hinput i) 1 =
    (Finsupp.domLCongr (component.outputPositionEquiv hinput houtput x) :
      C.Space x ≃ₗ[k] D.Space x) (Finsupp.single i c)
  rw [Finsupp.domLCongr_single,
    component.outputPositionEquiv_apply hinput houtput]
  simp

/-- A graph-component basis map with full support on both words is an
isomorphism of right modules. -/
theorem BoundaryFreeMorphismCoefficientComponent.isIso_componentMap_of_fullSupport
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hC : IsMonomial R) (hD : IsMonomial R)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport) :
    IsIso (C.boundaryFreeMorphismCoefficientComponentMap
      D hC hD component) := by
  let map := C.boundaryFreeMorphismCoefficientComponentMap D hC hD component
  letI appIso (X : (Category R)ᵒᵖ) : IsIso (map.app X) := by
    apply (ConcreteCategory.isIso_iff_bijective (map.app X)).mpr
    change Function.Bijective
      (C.coefficientComponentLinearMap D component.1.representative X.unop.as)
    rw [component.coefficientComponentLinearMap_eq_domLCongr
      hinput houtput X.unop.as]
    exact (Finsupp.domLCongr
      (component.outputPositionEquiv hinput houtput X.unop.as) :
        C.Space X.unop.as ≃ₗ[k] D.Space X.unop.as).bijective
  exact NatIso.isIso_of_isIso_app map

/-- The inverse of a two-sided full-support component map is the inverse
coordinate permutation at every displayed vertex. -/
theorem BoundaryFreeMorphismCoefficientComponent.inv_componentMap_app_eq_domLCongr_symm
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hC : IsMonomial R) (hD : IsMonomial R)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport) (x : Q) :
    let map := C.boundaryFreeMorphismCoefficientComponentMap
      D hC hD component
    letI : IsIso map := component.isIso_componentMap_of_fullSupport
      hC hD hinput houtput
    (inv map).app (Opposite.op (obj R x)) =
      ModuleCat.ofHom
        (Finsupp.domLCongr
          (component.outputPositionEquiv hinput houtput x)).symm.toLinearMap := by
  dsimp only
  let map := C.boundaryFreeMorphismCoefficientComponentMap
    D hC hD component
  letI : IsIso map := component.isIso_componentMap_of_fullSupport
    hC hD hinput houtput
  apply (cancel_epi (map.app (Opposite.op (obj R x)))).1
  change map.app (Opposite.op (obj R x)) ≫
      (inv map).app (Opposite.op (obj R x)) = _
  have hidentity := congrArg
    (fun t => t.app (Opposite.op (obj R x))) (IsIso.hom_inv_id map)
  change map.app (Opposite.op (obj R x)) ≫
      (inv map).app (Opposite.op (obj R x)) =
        𝟙 _ at hidentity
  rw [hidentity]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change
    v = (Finsupp.domLCongr
      (component.outputPositionEquiv hinput houtput x) :
        C.Space x ≃ₗ[k] D.Space x).symm
        (C.coefficientComponentLinearMap
          D component.1.representative x v)
  rw [component.coefficientComponentLinearMap_eq_domLCongr
    hinput houtput x]
  exact (Finsupp.domLCongr
    (component.outputPositionEquiv hinput houtput x) :
      C.Space x ≃ₗ[k] D.Space x).symm_apply_apply v |>.symm

/-- Postcomposing with the inverse full-support component map turns its
selected coefficient into the corresponding diagonal coefficient. -/
theorem BoundaryFreeMorphismCoefficientComponent.morphismCoefficientAt_comp_inv_componentMap_diagonal
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hC : IsMonomial R) (hD : IsMonomial R)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {x : Q} (i : C.PositionAt x) :
    let map := C.boundaryFreeMorphismCoefficientComponentMap
      D hC hD component
    letI : IsIso map := component.isIso_componentMap_of_fullSupport
      hC hD hinput houtput
    C.morphismCoefficientAt C hC hC (f ≫ inv map)
        (C.diagonalMorphismCoefficientPosition i) =
      C.morphismCoefficientAt D hC hD f
        ⟨x, i, component.outputPosition hinput i⟩ := by
  dsimp only
  let map := C.boundaryFreeMorphismCoefficientComponentMap
    D hC hD component
  letI : IsIso map := component.isIso_componentMap_of_fullSupport
    hC hD hinput houtput
  change
    (show C.Space x from
      ((inv map).app (Opposite.op (obj R x))).hom
        ((f.app (Opposite.op (obj R x))).hom (Finsupp.single i 1))) i = _
  rw [component.inv_componentMap_app_eq_domLCongr_symm
    hC hD hinput houtput x]
  change
    (Finsupp.domLCongr
      (component.outputPositionEquiv hinput houtput x) :
        C.Space x ≃ₗ[k] D.Space x).symm
          ((f.app (Opposite.op (obj R x))).hom
            (Finsupp.single i 1)) i = _
  simp
  rfl

/-- Any string-module morphism with a nonzero coefficient on a two-sided
full-support component is an isomorphism. -/
theorem BoundaryFreeMorphismCoefficientComponent.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hC : IsMonomial R) (hD : IsMonomial R)
    (hinput : component.HasFullInputSupport)
    (houtput : component.HasFullOutputSupport)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (hcoefficient : C.morphismCoefficientAt D hC hD f
      component.1.representative ≠ 0) :
    IsIso f := by
  let map := C.boundaryFreeMorphismCoefficientComponentMap
    D hC hD component
  letI : IsIso map := component.isIso_componentMap_of_fullSupport
    hC hD hinput houtput
  have hselected : C.morphismCoefficientAt D hC hD f
      ⟨C.source, C.sourcePosition,
        component.outputPosition hinput C.sourcePosition⟩ ≠ 0 :=
    (C.morphismCoefficientAt_ne_zero_iff_of_eqvGen D hC hD f
      (component.outputPosition_support hinput C.sourcePosition)).mp
        hcoefficient
  have hdiagonalPoint : C.morphismCoefficientAt C hC hC
      (f ≫ inv map)
      (C.diagonalMorphismCoefficientPosition C.sourcePosition) ≠ 0 := by
    rw [component.morphismCoefficientAt_comp_inv_componentMap_diagonal
      hC hD hinput houtput f C.sourcePosition]
    exact hselected
  have hdiagonal : C.diagonalMorphismCoefficientLinearMap hC
      (f ≫ inv map) ≠ 0 := by
    rw [C.diagonalMorphismCoefficientLinearMap_apply,
      C.morphismCoefficientAt_diagonalComponent_representative_eq_source]
    exact hdiagonalPoint
  letI : IsIso (f ≫ inv map) :=
    C.isIso_of_diagonalMorphismCoefficientLinearMap_ne_zero
      hC (f ≫ inv map) hdiagonal
  rw [show f = (f ≫ inv map) ≫ map by simp]
  infer_instance

end MagnitudeConjecture.BoundQuiver.StringWord.Word
