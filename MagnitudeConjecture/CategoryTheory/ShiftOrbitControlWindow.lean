import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso
import MagnitudeConjecture.CategoryTheory.ShiftOrbitWindow
import MagnitudeConjecture.Combinatorics.FiniteInteractionNeighborhood

/-!
# Local closure from Hom-interaction windows

A nonzero morphism in the shift-orbit category has a nonzero homogeneous
component.  After translating its external endpoint, that component is an
ordinary nonzero Hom adjacent to the chosen endpoint.  Hence one
Hom-interaction enlargement of a seed contains a representative of every
orbit object needed to test left or right almost-splitness.  The explicit
object-shift isomorphism supplies the essential-image witness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]

omit [∀ a : A, (shiftFunctor C a).Additive] in
/-- A nonzero finite-support orbit morphism has a nonzero homogeneous
component. -/
theorem exists_shiftOrbitHom_component_ne_zero
    {X Y : C} {f : ShiftOrbitHom A X Y} (hf : f ≠ 0) :
    ∃ a : A, f a ≠ 0 := by
  by_contra h
  apply hf
  ext a
  by_contra ha
  exact h ⟨a, ha⟩

/-- One Hom-interaction enlargement contains representatives of all orbit
objects carrying a nonzero map out of a seed object. -/
theorem windowIdentityComponentFunctor_locallyLeftObjectClosed
    (U W : Set C)
    (hUW : CoveringSeparation.interactionNeighborhood
      CoveringSeparation.homInteraction U ⊆ W)
    (X : CoveringSeparation.WindowCategory W) (hX : X.1 ∈ U) :
    IsLocallyLeftObjectClosedAt
      (windowIdentityComponentFunctor (A := A) W) X := by
  intro M g hg _
  change ShiftOrbitHom A X.1 M at g
  obtain ⟨a, ha⟩ := exists_shiftOrbitHom_component_ne_zero hg
  let V : C := (shiftFunctor C a).obj M
  have hnontrivial : Nontrivial (X.1 ⟶ V) :=
    ⟨⟨g a, 0, ha⟩⟩
  have hV : V ∈ W := hUW ⟨X.1, hX, Or.inr (Or.inl hnontrivial)⟩
  refine ⟨⟨V, hV⟩, ⟨?_⟩⟩
  exact (ShiftOrbitCategory.objectShiftIso (C := C) M a).symm

/-- One Hom-interaction enlargement contains representatives of all orbit
objects carrying a nonzero map into a seed object. -/
theorem windowIdentityComponentFunctor_locallyRightObjectClosed
    (U W : Set C)
    (hUW : CoveringSeparation.interactionNeighborhood
      CoveringSeparation.homInteraction U ⊆ W)
    (Y : CoveringSeparation.WindowCategory W) (hY : Y.1 ∈ U) :
    IsLocallyRightObjectClosedAt
      (windowIdentityComponentFunctor (A := A) W) Y := by
  intro M g hg _
  change ShiftOrbitHom (C := C) A (show C from M) Y.1 at g
  obtain ⟨a, ha⟩ := exists_shiftOrbitHom_component_ne_zero hg
  let V : C := (shiftFunctor C (-a)).obj M
  let f : V ⟶ Y.1 :=
    (shiftFunctor C (-a)).map (g a) ≫ (shiftShiftNeg Y.1 a).hom
  have hf : f ≠ 0 := by
    intro hfzero
    apply ha
    apply (shiftFunctor C (-a)).map_injective
    apply (cancel_mono (shiftShiftNeg Y.1 a).hom).1
    simpa [f] using hfzero
  have hnontrivial : Nontrivial (V ⟶ Y.1) :=
    ⟨⟨f, 0, hf⟩⟩
  have hV : V ∈ W := hUW ⟨Y.1, hY, Or.inr (Or.inr hnontrivial)⟩
  refine ⟨⟨V, hV⟩, ⟨?_⟩⟩
  exact (ShiftOrbitCategory.objectShiftIso (C := C) M (-a)).symm

/-- One Hom-interaction enlargement contains every intermediate orbit object
needed to test a nonzero morphism between seed objects for irreducibility. -/
theorem windowIdentityComponentFunctor_locallyFactorizationClosed
    (U W : Set C)
    (hUW : CoveringSeparation.interactionNeighborhood
      CoveringSeparation.homInteraction U ⊆ W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (hX : X.1 ∈ U) (hf : f ≠ 0) :
    IsLocallyFactorizationClosedAt
      (windowIdentityComponentFunctor (A := A) W) f := by
  letI : (windowIdentityComponentFunctor (A := A) W).Faithful :=
    windowIdentityComponentFunctor_faithful W
  intro M g h hgh hg _
  have hgzero : g ≠ 0 := by
    intro hzero
    apply hf
    apply (windowIdentityComponentFunctor (A := A) W).map_injective
    have hmapzero :
        (windowIdentityComponentFunctor (A := A) W).map
            (0 : X ⟶ Y) = 0 := by
      change shiftOrbitOf X.1 Y.1 0
        (shiftHomZero (A := A) (0 : X.1 ⟶ Y.1)) = 0
      simp [shiftHomZero]
    rw [hmapzero]
    simpa [hzero] using hgh.symm
  exact
    windowIdentityComponentFunctor_locallyLeftObjectClosed
      U W hUW X hX M g hgzero hg

/-- The manuscript's third Hom-neighborhood contains every orbit object
needed for left almost-split tests based at its second neighborhood. -/
theorem threeStepWindow_locallyLeftObjectClosed
    (U : Set C)
    (X : CoveringSeparation.WindowCategory
      (CoveringSeparation.threeStepControlWindow
        CoveringSeparation.homInteraction U))
    (hX : X.1 ∈ CoveringSeparation.iterateInteractionNeighborhood
      CoveringSeparation.homInteraction 2 U) :
    IsLocallyLeftObjectClosedAt
      (windowIdentityComponentFunctor (A := A)
        (CoveringSeparation.threeStepControlWindow
          CoveringSeparation.homInteraction U)) X := by
  apply windowIdentityComponentFunctor_locallyLeftObjectClosed
    (CoveringSeparation.iterateInteractionNeighborhood
      CoveringSeparation.homInteraction 2 U)
  · intro Z hZ
    exact hZ
  · exact hX

/-- The manuscript's third Hom-neighborhood contains every orbit object
needed for right almost-split tests based at its second neighborhood. -/
theorem threeStepWindow_locallyRightObjectClosed
    (U : Set C)
    (Y : CoveringSeparation.WindowCategory
      (CoveringSeparation.threeStepControlWindow
        CoveringSeparation.homInteraction U))
    (hY : Y.1 ∈ CoveringSeparation.iterateInteractionNeighborhood
      CoveringSeparation.homInteraction 2 U) :
    IsLocallyRightObjectClosedAt
      (windowIdentityComponentFunctor (A := A)
        (CoveringSeparation.threeStepControlWindow
          CoveringSeparation.homInteraction U)) Y := by
  apply windowIdentityComponentFunctor_locallyRightObjectClosed
    (CoveringSeparation.iterateInteractionNeighborhood
      CoveringSeparation.homInteraction 2 U)
  · intro Z hZ
    exact hZ
  · exact hY

/-- The manuscript's third Hom-neighborhood contains all intermediate orbit
objects needed to test a nonzero morphism based at its second neighborhood
for irreducibility. -/
theorem threeStepWindow_locallyFactorizationClosed
    (U : Set C)
    {X Y : CoveringSeparation.WindowCategory
      (CoveringSeparation.threeStepControlWindow
        CoveringSeparation.homInteraction U)}
    {f : X ⟶ Y}
    (hX : X.1 ∈ CoveringSeparation.iterateInteractionNeighborhood
      CoveringSeparation.homInteraction 2 U)
    (hf : f ≠ 0) :
    IsLocallyFactorizationClosedAt
      (windowIdentityComponentFunctor (A := A)
        (CoveringSeparation.threeStepControlWindow
          CoveringSeparation.homInteraction U)) f := by
  apply windowIdentityComponentFunctor_locallyFactorizationClosed
    (CoveringSeparation.iterateInteractionNeighborhood
      CoveringSeparation.homInteraction 2 U)
  · intro Z hZ
    exact hZ
  · exact hX
  · exact hf

section Linear

universe uK

/-- Shift-Hom orthogonality and one Hom-neighborhood identify
irreducibility before and after the concrete window orbit functor. -/
theorem isIrreducibleMorphism_windowMap_iff_of_shiftHomOrthogonal
    (k : Type uK) [CommSemiring k] [CategoryTheory.Linear k C]
    [∀ a : A, (shiftFunctor C a).Linear k]
    (U W : Set C)
    (hUW : CoveringSeparation.interactionNeighborhood
      CoveringSeparation.homInteraction U ⊆ W)
    (horthogonal : WindowShiftHomOrthogonal (A := A) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (hX : X.1 ∈ U) (hf : f ≠ 0) :
    IsIrreducibleMorphism
        ((windowIdentityComponentFunctor (A := A) W).map f) ↔
      IsIrreducibleMorphism f :=
  (windowIdentityComponentFunctorOrbitHomDecomposition
      (k := k) (A := A) W).isIrreducibleMorphism_map_iff_of_orthogonal
    (windowMultiplicativeShiftHom_translateHomOrthogonal horthogonal)
    (windowIdentityComponentFunctor_locallyFactorizationClosed
      U W hUW hX hf)

/-- Shift-Hom orthogonality and one Hom-neighborhood preserve a right
almost-split morphism whose endpoint belongs to the seed. -/
theorem rightAlmostSplit_windowMap_of_shiftHomOrthogonal
    (k : Type uK) [CommSemiring k] [CategoryTheory.Linear k C]
    [∀ a : A, (shiftFunctor C a).Linear k]
    (U W : Set C)
    (hUW : CoveringSeparation.interactionNeighborhood
      CoveringSeparation.homInteraction U ⊆ W)
    (horthogonal : WindowShiftHomOrthogonal (A := A) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit f) (hY : Y.1 ∈ U) :
    IsRightAlmostSplit
      ((windowIdentityComponentFunctor (A := A) W).map f) :=
  (windowIdentityComponentFunctorOrbitHomDecomposition
      (k := k) (A := A) W).rightAlmostSplit_map_of_orthogonal
    (windowMultiplicativeShiftHom_translateHomOrthogonal horthogonal)
    hf
    (windowIdentityComponentFunctor_locallyRightObjectClosed U W hUW Y hY)

/-- Shift-Hom orthogonality and one Hom-neighborhood preserve a left
almost-split morphism whose source belongs to the seed. -/
theorem leftAlmostSplit_windowMap_of_shiftHomOrthogonal
    (k : Type uK) [CommSemiring k] [CategoryTheory.Linear k C]
    [∀ a : A, (shiftFunctor C a).Linear k]
    (U W : Set C)
    (hUW : CoveringSeparation.interactionNeighborhood
      CoveringSeparation.homInteraction U ⊆ W)
    (horthogonal : WindowShiftHomOrthogonal (A := A) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f) (hX : X.1 ∈ U) :
    IsLeftAlmostSplit
      ((windowIdentityComponentFunctor (A := A) W).map f) :=
  (windowIdentityComponentFunctorOrbitHomDecomposition
      (k := k) (A := A) W).leftAlmostSplit_map_of_orthogonal
    (windowMultiplicativeShiftHom_translateHomOrthogonal horthogonal)
    hf
    (windowIdentityComponentFunctor_locallyLeftObjectClosed U W hUW X hX)

end Linear

end MagnitudeConjecture.CoveringHom
