import MagnitudeConjecture.CategoryTheory.ObjectDeletionAlmostSplit
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleControlWindow

/-!
# Finite control of object-deletion source and sink terms

The manuscript places the middle terms created by intrinsic source and sink
maps at an object-deletion stage in the second ambient Hom neighborhood.  The
key point is minimality: every indecomposable summand of a minimal right
almost-split source has a nonzero component to the endpoint, and dually every
summand of a minimal left almost-split target receives a nonzero component
from the endpoint.  Extension by zero preserves those nonzero maps.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasFiniteBiproducts D] [HasBinaryBiproducts D]

namespace FiniteIndecomposableDecomposition

/-- Inclusion of one displayed indecomposable summand. -/
def inclusion {X : D} (d : FiniteIndecomposableDecomposition X)
    (i : Fin d.n) : d.summand i ⟶ X :=
  biproduct.ι d.summand i ≫ d.isoBiproduct.inv

/-- Projection onto one displayed indecomposable summand. -/
def projection {X : D} (d : FiniteIndecomposableDecomposition X)
    (i : Fin d.n) : X ⟶ d.summand i :=
  d.isoBiproduct.hom ≫ biproduct.π d.summand i

@[simp]
theorem inclusion_projection {X : D}
    (d : FiniteIndecomposableDecomposition X) (i : Fin d.n) :
    d.inclusion i ≫ d.projection i = 𝟙 (d.summand i) := by
  simp [inclusion, projection, Category.assoc]

/-- Every displayed component of a right-minimal map is nonzero. -/
theorem inclusion_comp_ne_zero_of_isRightMinimal
    {X Y : D} (d : FiniteIndecomposableDecomposition X)
    (i : Fin d.n) (f : X ⟶ Y) (hf : IsRightMinimal f) :
    d.inclusion i ≫ f ≠ 0 := by
  intro hzero
  let e : X ⟶ X := 𝟙 X - d.projection i ≫ d.inclusion i
  have hefix : e ≫ f = f := by
    dsimp only [e]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      hzero, comp_zero, sub_zero]
  letI : IsIso e := hf e hefix
  have hie : d.inclusion i ≫ e = 0 := by
    dsimp only [e]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      d.inclusion_projection, Category.id_comp, sub_self]
  have hi0 : d.inclusion i = 0 := by
    apply (cancel_mono e).1
    simpa only [zero_comp] using hie
  have hzeroSummand : IsZero (d.summand i) := by
    rw [IsZero.iff_id_eq_zero, ← d.inclusion_projection i, hi0, zero_comp]
  exact (d.indecomposable i).1 hzeroSummand

/-- Every displayed component of a left-minimal map is nonzero. -/
theorem comp_projection_ne_zero_of_isLeftMinimal
    {X Y : D} (d : FiniteIndecomposableDecomposition Y)
    (i : Fin d.n) (f : X ⟶ Y) (hf : IsLeftMinimal f) :
    f ≫ d.projection i ≠ 0 := by
  intro hzero
  let e : Y ⟶ Y := 𝟙 Y - d.projection i ≫ d.inclusion i
  have hefix : f ≫ e = f := by
    dsimp only [e]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      hzero, zero_comp, sub_zero]
  letI : IsIso e := hf e hefix
  have hep : e ≫ d.projection i = 0 := by
    dsimp only [e]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      d.inclusion_projection, Category.comp_id, sub_self]
  have hp0 : d.projection i = 0 := by
    apply (cancel_epi e).1
    simpa only [comp_zero] using hep
  have hzeroSummand : IsZero (d.summand i) := by
    rw [IsZero.iff_id_eq_zero, ← d.inclusion_projection i, hp0, comp_zero]
  exact (d.indecomposable i).1 hzeroSummand

end FiniteIndecomposableDecomposition

end MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Every displayed middle summand of a right-minimal map ending in the
`n`th Hom neighborhood belongs to the next neighborhood. -/
theorem rightMinimal_middleSummand_mem_nextHomNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C))
    {n : ℕ} {X Y : ControlFiniteModule k C}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X)
    (f : X ⟶ Y) (hf : IsRightMinimal f)
    (hY : Y ∈ (S.iterateHomNeighborhood hlocal n).isoClosure)
    (t : Fin d.n) :
    d.summand t ∈
      (S.iterateHomNeighborhood hlocal (n + 1)).isoClosure :=
  S.mem_iterateHomNeighborhood_succ_of_ne_zero_from
    hlocal hY (d.indecomposable t) (d.inclusion t ≫ f)
      (d.inclusion_comp_ne_zero_of_isRightMinimal t f hf)

/-- Every displayed middle summand of a left-minimal map starting in the
`n`th Hom neighborhood belongs to the next neighborhood. -/
theorem leftMinimal_middleSummand_mem_nextHomNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C))
    {n : ℕ} {X Y : ControlFiniteModule k C}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (f : X ⟶ Y) (hf : IsLeftMinimal f)
    (hX : X ∈ (S.iterateHomNeighborhood hlocal n).isoClosure)
    (t : Fin d.n) :
    d.summand t ∈
      (S.iterateHomNeighborhood hlocal (n + 1)).isoClosure :=
  S.mem_iterateHomNeighborhood_succ_of_ne_zero_to
    hlocal hX (d.indecomposable t) (f ≫ d.projection t)
      (d.comp_projection_ne_zero_of_isLeftMinimal t f hf)

/-- The manuscript's `U₁` sink clause: middle summands of a right-minimal
sink map ending at a seed module lie in the first Hom neighborhood. -/
theorem rightMinimal_middleSummand_mem_firstFiberHomNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    {X Y : ControlFiniteModule k C}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X)
    (f : X ⟶ Y) (hf : IsRightMinimal f)
    (hY : Y ∈ (finiteFiberControlSeed hlocal y).isoClosure)
    (t : Fin d.n) :
    d.summand t ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 1).isoClosure :=
  by
    simpa only [FiniteIndecomposableModuleFamily.iterateHomNeighborhood] using
      rightMinimal_middleSummand_mem_nextHomNeighborhood
        hlocal (finiteFiberControlSeed hlocal y) (n := 0) d f hf hY t

/-- The manuscript's `U₁` source clause: middle summands of a left-minimal
source map starting at a seed module lie in the first Hom neighborhood. -/
theorem leftMinimal_middleSummand_mem_firstFiberHomNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    {X Y : ControlFiniteModule k C}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (f : X ⟶ Y) (hf : IsLeftMinimal f)
    (hX : X ∈ (finiteFiberControlSeed hlocal y).isoClosure)
    (t : Fin d.n) :
    d.summand t ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 1).isoClosure :=
  by
    simpa only [FiniteIndecomposableModuleFamily.iterateHomNeighborhood] using
      leftMinimal_middleSummand_mem_nextHomNeighborhood
        hlocal (finiteFiberControlSeed hlocal y) (n := 0) d f hf hX t

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable (S : Set C)

/-- If an indecomposable endpoint lies outside the two-step Hom neighborhood
of `y`, the source of any right-minimal map to that endpoint vanishes at
`y`. -/
theorem rightMinimal_source_vanishesAt_of_endpoint_not_mem_twoStep
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    {Y Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (g : Y ⟶ Z) (hgmin : IsRightMinimal g) (hZ : Indecomposable Z)
    (houtside : Z ∉
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 2).isoClosure) :
    ModuleVanishesOnDeleted (k := k) C ({y} : Set C) Y.obj.obj := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  let E := finiteDimensionalModuleEvaluation (k := k) C y
  have hzeroSummand (t : Fin dY.n) : IsZero (E.obj (dY.summand t)) := by
    by_contra hzero
    have hnontrivial : Nontrivial ((dY.summand t).obj.obj.obj y) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    have hseed : dY.summand t ∈ (finiteFiberControlSeed hlocal y).isoClosure :=
      mem_finiteFiberControlSeed_isoClosure
        hlocal y (dY.indecomposable t) hnontrivial
    have hcomponent : dY.inclusion t ≫ g ≠ 0 :=
      dY.inclusion_comp_ne_zero_of_isRightMinimal t g hgmin
    have hone : Z ∈
        ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
          hlocal 1).isoClosure := by
      simpa only [FiniteIndecomposableModuleFamily.iterateHomNeighborhood] using
        (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_ne_zero_to
          hlocal (n := 0) hseed hZ (dY.inclusion t ≫ g) hcomponent
    have htwo : Z ∈
        ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
          hlocal 2).isoClosure :=
      (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_homInteraction
        hlocal hone hZ (Or.inl rfl)
    exact houtside htwo
  have hzeroSum : IsZero (⨁ fun t : Fin dY.n ↦ E.obj (dY.summand t)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro t
    exact (hzeroSummand t).eq_of_tgt _ _
  letI : E.Additive := by
    dsimp only [E, finiteDimensionalModuleEvaluation]
    infer_instance
  have hzeroBiproduct : IsZero (E.obj (⨁ dY.summand)) :=
    hzeroSum.of_iso (E.mapBiproduct dY.summand)
  exact hzeroBiproduct.of_iso (E.mapIso dY.isoBiproduct)

/-- Outside the two-step control neighborhood of a deleted object, the
intrinsic deletion sink retains right almost-splitness, right minimality,
source arity, and the projectivity flag of its ambient endpoint. -/
theorem finiteDeletion_sink_localData_unchanged_of_endpoint_not_mem_twoStep
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C ({y} : Set C)) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero
        (k := k) C ({y} : Set C)).obj Z)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g)
    (hZ : Indecomposable
      ((finiteDimensionalModuleExtensionByZero
        (k := k) C ({y} : Set C)).obj Z))
    (houtside :
      (finiteDimensionalModuleExtensionByZero
          (k := k) C ({y} : Set C)).obj Z ∉
        ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
          hlocal 2).isoClosure)
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (dR : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (finiteVanishingModuleRestriction (k := k) C ({y} : Set C)
        ((finiteMaximalVanishingSubmoduleFunctor
          (k := k) C ({y} : Set C)).obj Y))) :
    IsRightAlmostSplit
        (finiteDeletionRightAdjointSinkCandidate
          (k := k) C ({y} : Set C) g) ∧
      IsRightMinimal
        (finiteDeletionRightAdjointSinkCandidate
          (k := k) C ({y} : Set C) g) ∧
      dR.n = dY.n ∧
      (Projective Z ↔
        Projective ((finiteDimensionalModuleExtensionByZero
          (k := k) C ({y} : Set C)).obj Z)) := by
  have hY : ModuleVanishesOnDeleted
      (k := k) C ({y} : Set C) Y.obj.obj :=
    rightMinimal_source_vanishesAt_of_endpoint_not_mem_twoStep
      (k := k) C hlocal y dY g hgmin hZ houtside
  exact ⟨
    finiteDeletionRightAdjointSinkCandidate_isRightAlmostSplit
      (k := k) C ({y} : Set C) g hg,
    finiteDeletionRightAdjointSinkCandidate_isRightMinimal_of_source_vanishes
      (k := k) C ({y} : Set C) g hgmin hY,
    finiteMaximalVanishingSubmoduleRestriction_arity_eq_of_vanishesOnDeleted
      (k := k) C ({y} : Set C) Y hY dY dR,
    finiteDeletion_projective_iff_of_minimal_sink_source_vanishes
      (k := k) C ({y} : Set C) hP g hg hgmin hY⟩

/-- If the ambient middle term to which the right adjoint is applied lies in
the first Hom neighborhood, then every indecomposable middle summand of the
resulting right-minimal deletion-stage sink lies in the second ambient Hom
neighborhood. -/
theorem exists_finiteDeletion_rightMinimal_sink_controlled
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z)
    (hg : IsRightAlmostSplit g)
    (hY : Y ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 1).isoClosure) :
    ∃ (Y' : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k)
      (g' : Y' ⟶ Z)
      (i : Y' ⟶
        finiteVanishingModuleRestriction (k := k) C S
          ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y))
      (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y'),
      IsRightAlmostSplit g' ∧ IsRightMinimal g' ∧ IsSplitMono i ∧
        i ≫ finiteDeletionRightAdjointSinkCandidate (k := k) C S g = g' ∧
        ∀ t,
          (finiteDimensionalModuleExtensionByZero (k := k) C S).obj
              (d.summand t) ∈
            ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
              hlocal 2).isoClosure := by
  obtain ⟨Y', g', i, hg', hg'min, hi, hcomp⟩ :=
    exists_finiteDeletion_rightMinimal_sink_retract_of_ambient
      (k := k) C S g hg
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition Y'
  refine ⟨Y', g', i, d, hg', hg'min, hi, hcomp, ?_⟩
  intro t
  letI : IsSplitMono i := hi
  letI : IsSplitMono (d.inclusion t) := IsSplitMono.mk'
    { retraction := d.projection t
      id := d.inclusion_projection t }
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let R := (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S R
  let I := (finiteModuleVanishesOnDeleted (k := k) C S).ι
  haveI : IsSplitMono (d.inclusion t ≫ i) := inferInstance
  haveI : IsSplitMono (F.map (d.inclusion t ≫ i)) := inferInstance
  haveI : IsIso e.hom.hom := by
    change IsIso (I.map e.hom)
    infer_instance
  let component : F.obj (d.summand t) ⟶ Y :=
    F.map (d.inclusion t ≫ i) ≫ e.hom.hom ≫
      finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y
  haveI : Mono component := by
    dsimp only [component]
    apply mono_comp'
    · infer_instance
    · apply mono_comp'
      · exact IsIso.mono_of_iso e.hom.hom
      · exact finiteMaximalVanishingSubmoduleInclusion_mono
          (k := k) C S Y
  have hind : Indecomposable (F.obj (d.summand t)) :=
    finiteDimensionalModuleExtensionByZero_indec
      (k := k) C S (d.summand t) (d.indecomposable t)
  have hcomponent : component ≠ 0 := by
    intro hzero
    exact hind.1 (IsZero.of_mono_eq_zero component hzero)
  exact (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_ne_zero_from
      hlocal hY hind component hcomponent

/-- Dually, if the ambient middle term to which the left adjoint is applied
lies in the first Hom neighborhood, every indecomposable middle summand of
the resulting left-minimal deletion-stage source lies in the second ambient
Hom neighborhood. -/
theorem exists_finiteDeletion_leftMinimal_source_controlled
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z ⟶ Y)
    (hf : IsLeftAlmostSplit f)
    (hY : Y ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 1).isoClosure) :
    ∃ (Y' : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k)
      (f' : Z ⟶ Y')
      (i : Y' ⟶
        finiteVanishingModuleRestriction (k := k) C S
          ((finiteMaximalVanishingQuotientFunctor (k := k) C S).obj Y))
      (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y'),
      IsLeftAlmostSplit f' ∧ IsLeftMinimal f' ∧ IsSplitMono i ∧
        f' ≫ i = finiteDeletionLeftAdjointSourceCandidate (k := k) C S f ∧
        ∀ t,
          (finiteDimensionalModuleExtensionByZero (k := k) C S).obj
              (d.summand t) ∈
            ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
              hlocal 2).isoClosure := by
  obtain ⟨Y', f', i, hf', hf'min, hi, hcomp⟩ :=
    exists_finiteDeletion_leftMinimal_source_retract_of_ambient
      (k := k) C S f hf
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition Y'
  refine ⟨Y', f', i, d, hf', hf'min, hi, hcomp, ?_⟩
  intro t
  letI : IsSplitMono i := hi
  letI : IsSplitEpi (d.projection t) := IsSplitEpi.mk'
    { section_ := d.inclusion t
      id := d.inclusion_projection t }
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let L := (finiteMaximalVanishingQuotientFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S L
  let I := (finiteModuleVanishesOnDeleted (k := k) C S).ι
  haveI : IsSplitEpi (retraction i ≫ d.projection t) := inferInstance
  haveI : IsSplitEpi (F.map (retraction i ≫ d.projection t)) := inferInstance
  haveI : IsIso e.inv.hom := by
    change IsIso (I.map e.inv)
    infer_instance
  let component : Y ⟶ F.obj (d.summand t) :=
    finiteMaximalVanishingQuotientProjection (k := k) C S Y ≫
      e.inv.hom ≫ F.map (retraction i ≫ d.projection t)
  haveI : Epi component := by
    dsimp only [component]
    apply epi_comp'
    · infer_instance
    · apply epi_comp'
      · exact IsIso.epi_of_iso e.inv.hom
      · exact IsSplitEpi.epi (F.map
          (retraction i ≫ d.projection t))
  have hind : Indecomposable (F.obj (d.summand t)) :=
    finiteDimensionalModuleExtensionByZero_indec
      (k := k) C S (d.summand t) (d.indecomposable t)
  have hcomponent : component ≠ 0 := by
    intro hzero
    exact hind.1 (IsZero.of_epi_eq_zero component hzero)
  exact (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_ne_zero_to
      hlocal hY hind component hcomponent

/-- A nonzero factorization through an indecomposable deletion-stage module
is still a nonzero factorization after extension by zero.  If its source term
lies in the ambient `U₂` window, the witness therefore lies in the ambient
`U₃` window, independently of which earlier objects were deleted. -/
theorem finiteDeletion_bifactor_extension_mem_threeStepControlFamily
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    {X Y Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (hX : (finiteDimensionalModuleExtensionByZero (k := k) C S).obj X ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 2).isoClosure)
    (hZ : Indecomposable Z) (a : X ⟶ Z) (ha : a ≠ 0)
    (b : Z ⟶ Y) (hb : b ≠ 0) :
    (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z ∈
      (finiteThreeStepControlFamily hlocal y).isoClosure := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  have hFa : F.map a ≠ 0 := by
    intro hzero
    exact ha ((F.map_eq_zero_iff).mp hzero)
  have hFb : F.map b ≠ 0 := by
    intro hzero
    exact hb ((F.map_eq_zero_iff).mp hzero)
  have hFZ : Indecomposable (F.obj Z) :=
    finiteDimensionalModuleExtensionByZero_indec (k := k) C S Z hZ
  exact (finiteFiberControlSeed hlocal y).bifactor_mem_threeStepControlFamily
    hlocal hX hFZ (F.map a) hFa (F.map b) hFb

end MagnitudeConjecture.ObjectDeletion
