import MagnitudeConjecture.Algebra.RightModuleStandardFormAuslander

/-!
# Projective-injective coordinates over the standard mesh

Every indecomposable projective-injective finite contravariant module over
the standard mesh is the dual corepresentable based at a projective mesh
vertex.  Finite Krull--Schmidt decomposition then gives literal finite
coordinates for every projective-injective object.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormProjectiveInjectiveQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormProjectiveInjectiveArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- An indecomposable projective-injective standard-mesh module is the dual
corepresentable based at a projective mesh vertex. -/
theorem indecomposable_projectiveInjective_iso_standardFormProjectiveDual
    (N : S.StandardFormFiniteContravariantModuleCategory)
    [Projective N] [Injective N] (hN : Indecomposable N) :
    ∃ p : S.StandardFormProjectiveVertex, Nonempty
      (finiteDimensionalDualLinearYoneda
        (k := k) (S.standardFormOppositeVertex (k := k) p.1)
        (S.standardFormFiniteContravariantDualCorepresentables
          (S.standardFormOppositeVertex (k := k) p.1)) ≅ N) := by
  obtain ⟨X, ⟨e⟩⟩ :=
    indecomposable_injective_iso_finiteDimensionalDualLinearYoneda
      S.standardFormFiniteContravariantDualCorepresentables
      S.standardFormOppositeVertexCategoryEndLocal N hN
  rcases X with ⟨x⟩
  let I := finiteDimensionalDualLinearYoneda
    (k := k) (S.standardFormOppositeVertex (k := k) x)
    (S.standardFormFiniteContravariantDualCorepresentables
      (S.standardFormOppositeVertex (k := k) x))
  letI : Projective I := Projective.of_iso e.symm inferInstance
  have hIind : Indecomposable I :=
    finiteDimensionalDualLinearYoneda_indecomposable
      S.standardFormFiniteContravariantDualCorepresentables
      S.standardFormOppositeVertexCategoryEndLocal
      (S.standardFormOppositeVertex (k := k) x)
  obtain ⟨Y, ⟨d⟩⟩ :=
    indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      S.standardFormFiniteContravariantRepresentables
      S.standardFormOppositeVertexCategoryEndLocal I hIind
  rcases Y with ⟨y⟩
  let rIso := S.standardFormRightMeshData.contravariantRepresentableFiniteIso
    (k := k) S.standardFormFiniteContravariantRepresentables y
  let f := S.standardFormContravariantDualSocleInclusion (k := k) x ≫
    d.inv ≫ rIso.hom
  have hf : f ≠ 0 := by
    intro hf
    apply S.standardFormContravariantDualSocleInclusion_ne_zero x
    apply (cancel_mono (d.inv ≫ rIso.hom)).1
    simpa [f] using hf
  have hx : x ∈ S.standardFormProjectiveSet :=
    S.standardForm_mem_projective_of_nonzero_map_simple_to_contravariantRepresentable
      ((S.standardFormContravariantDualSocleIsoSimple x).inv ≫ f) (by
        intro hzero
        apply hf
        apply (cancel_epi (S.standardFormContravariantDualSocleIsoSimple x).inv).1
        simpa using hzero)
  exact ⟨⟨x, (S.mem_standardFormProjectiveSet_iff x).1 hx⟩, ⟨e⟩⟩

/-- Literal finite coordinates on a projective-injective standard-mesh
module by dual corepresentables based at projective vertices. -/
structure StandardFormProjectiveInjectiveCoordinates
    (M : S.StandardFormFiniteContravariantModuleCategory) where
  n : ℕ
  p : Fin n → S.StandardFormProjectiveVertex
  isoSource :
    (⨁ fun i ↦ finiteDimensionalDualLinearYoneda
      (k := k) (S.standardFormOppositeVertex (k := k) (p i).1)
      (S.standardFormFiniteContravariantDualCorepresentables
        (S.standardFormOppositeVertex (k := k) (p i).1))) ≅ M

/-- Every projective-injective finite standard-mesh module has finite
projective-vertex dual-corepresentable coordinates. -/
theorem standardFormProjectiveInjectiveCoordinates_nonempty
    (M : S.StandardFormFiniteContravariantModuleCategory)
    [Projective M] [Injective M] :
    Nonempty (S.StandardFormProjectiveInjectiveCoordinates M) := by
  classical
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition M
  have hprojective (j : Fin d.n) : Projective (d.summand j) := by
    let i : d.summand j ⟶ M :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv
    let r : M ⟶ d.summand j :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand j
    apply projective_of_retract (P := M) (Q := d.summand j)
      (inferInstance : Projective M) i r
    simp [i, r, Category.assoc]
  have hinjective (j : Fin d.n) : Injective (d.summand j) := by
    let i : d.summand j ⟶ M :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv
    let r : M ⟶ d.summand j :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand j
    exact Retract.injective
      { i := i
        r := r
        retract := by simp [i, r, Category.assoc] }
  have hdense (j : Fin d.n) :
      ∃ p : S.StandardFormProjectiveVertex, Nonempty
        (finiteDimensionalDualLinearYoneda
          (k := k) (S.standardFormOppositeVertex (k := k) p.1)
          (S.standardFormFiniteContravariantDualCorepresentables
            (S.standardFormOppositeVertex (k := k) p.1)) ≅ d.summand j) := by
    letI : Projective (d.summand j) := hprojective j
    letI : Injective (d.summand j) := hinjective j
    exact S.indecomposable_projectiveInjective_iso_standardFormProjectiveDual
      (d.summand j) (d.indecomposable j)
  choose p e using hdense
  exact ⟨{
    n := d.n
    p := p
    isoSource :=
      biproduct.mapIso (fun j ↦ Classical.choice (e j)) ≪≫
        d.isoBiproduct.symm }⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
