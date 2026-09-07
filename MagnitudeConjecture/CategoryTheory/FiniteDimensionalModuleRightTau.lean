import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteAlmostSplit
import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import QuotientSubmoduleEquidistribution.CategoryTheory.FiniteTauCategory

/-!
# Right tau-data on a finite-dimensional module skeleton

Minimal right almost-split maps and their kernels give the chosen right mesh
at each indecomposable label.  Finite componentwise biproducts extend these
meshes to every object and assemble the generic finite right-tau interface.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open QuotientSubmoduleEquidistribution.Iyama

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

namespace FiniteDimensionalModuleIndecomposableSkeleton

variable (S : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))

/-- The kernel--source--endpoint complex of the chosen minimal right
almost-split morphism at a skeleton label. -/
def labelRightMesh (y : Fin S.n) :
    ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :=
  let A := S.minimalRightAlmostSplitAt y
  ShortComplex.mk (kernel.ι A.map) A.map (kernel.condition A.map)

/-- Every label mesh is a right tau-sequence.  At a nonprojective endpoint
the terminal map is epic and its kernel inclusion is left almost split; at a
projective endpoint the terminal map is monic and its kernel is zero. -/
theorem labelRightTau
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]
    (y : Fin S.n) : RightTauSequence (S.labelRightMesh y) := by
  let A := S.minimalRightAlmostSplitAt y
  change RightTauSequence
    (ShortComplex.mk (kernel.ι A.map) A.map (kernel.condition A.map))
  letI : IsLocalRing (End (S.obj y)) := S.obj_end_local y
  have hgRad : IsRadicalMorphism A.map :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
      (S.indecomposable y).1 A.map).2 A.rightAlmostSplit.not_isSplitEpi
  have hfRad : IsRadicalMorphism (kernel.ι A.map) :=
    MagnitudeConjecture.CategoryTheory.isRadicalMorphism_kernel_ι_of_isRightMinimal
      A.map A.rightMinimal
  refine
    { f_radical := hfRad
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakKernel := ?_ }
  · intro W a ha
    by_cases hy : Projective (S.obj y)
    · letI : Projective (S.obj y) := hy
      letI : Mono A.map :=
        MagnitudeConjecture.CategoryTheory.rightAlmostSplit_mono_of_projective_target
          A.map A.rightAlmostSplit A.rightMinimal
      have hzero : IsZero (kernel A.map) := isZero_kernel_of_mono A.map
      refine ⟨0, ?_⟩
      have haZero : a = 0 := hzero.eq_of_src a 0
      rw [haZero]
      simp
    · letI : Epi A.map :=
        MagnitudeConjecture.CategoryTheory.IsRightAlmostSplit.epi_of_not_projective
          A.map A.rightAlmostSplit hy
      have hleft : IsLeftAlmostSplit (kernel.ι A.map) :=
        A.rightAlmostSplit.kernel_ι_isLeftAlmostSplit A.map A.rightMinimal
      have hsource : ¬ IsZero (kernel A.map) := by
        intro hzero
        apply hleft.not_isSplitMono
        exact IsSplitMono.mk'
          { retraction := 0
            id := hzero.eq_of_src _ _ }
      exact hleft.factors a
        (MagnitudeConjecture.CategoryTheory.not_isSplitMono_of_isRadicalMorphism
          hsource ha)
  · intro W a ha
    exact A.rightAlmostSplit.factors a
      ((MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
        (S.indecomposable y).1 a).1 ha)
  · constructor
    · rw [ShortComplex.isWeakKernel_iff]
      intro W q hq
      exact ⟨kernel.lift A.map q hq, kernel.lift_ι A.map q hq⟩
    · intro e he
      have heq : e = 𝟙 _ := by
        apply (cancel_mono (kernel.ι A.map)).1
        simpa only [Category.id_comp] using he
      rw [heq]
      infer_instance

/-- The right endpoint of a label mesh is definitionally its skeleton
object. -/
theorem labelRightMesh_X₃ (y : Fin S.n) :
    (S.labelRightMesh y).X₃ = S.obj y := rfl

/-- A chosen decomposition of an arbitrary finite-dimensional module into
the fixed skeleton labels. -/
structure ChosenLabelDecomposition
    (X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) where
  n : ℕ
  label : Fin n → Fin S.n
  iso : X ≅ ⨁ fun i ↦ S.obj (label i)

/-- Choose one label decomposition for every finite-dimensional module. -/
noncomputable def chosenLabelDecomposition
    (X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    S.ChosenLabelDecomposition X :=
  let h := S.obj_decomposition X
  { n := Classical.choose h
    label := Classical.choose (Classical.choose_spec h)
    iso := Classical.choice
      (Classical.choose_spec (Classical.choose_spec h)) }

/-- Extend the labelwise right meshes to every module by finite
componentwise biproduct. -/
def moduleRightMesh
    (X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :=
  let d := S.chosenLabelDecomposition X
  shortComplexBiproduct (fun i : Fin d.n ↦ S.labelRightMesh (d.label i))

/-- The modulewise right mesh has the supplied module as its endpoint. -/
def moduleRightTermIso
    (X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    (S.moduleRightMesh X).X₃ ≅ X :=
  let d := S.chosenLabelDecomposition X
  (biproduct.mapIso fun i : Fin d.n ↦
      eqToIso (S.labelRightMesh_X₃ (d.label i))).trans d.iso.symm

/-- Every modulewise right mesh is a right tau-sequence. -/
theorem moduleRightTau
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]
    (X : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    RightTauSequence (S.moduleRightMesh X) := by
  let d := S.chosenLabelDecomposition X
  exact rightTauSequence_shortComplexBiproduct S.nilpotentRadicalData
    (fun i : Fin d.n ↦ S.labelRightMesh (d.label i))
    (fun i ↦ S.labelRightTau (d.label i))

/-- A finite indecomposable skeleton and enough projectives construct the
complete finite right-tau-category interface. -/
def toFiniteRightTauCategoryData
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)] :
    FiniteRightTauCategoryData
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
      (Fin S.n) where
  obj := S.obj
  obj_indec := S.indecomposable
  obj_end_local := S.obj_end_local
  obj_decomposition := S.obj_decomposition
  obj_complete := S.complete
  obj_skeletal := S.skeletal
  radical := S.nilpotentRadicalData
  rightMesh := S.moduleRightMesh
  rightTermIso := S.moduleRightTermIso
  rightTau := S.moduleRightTau

end FiniteDimensionalModuleIndecomposableSkeleton

end MagnitudeConjecture.CoveringHom
