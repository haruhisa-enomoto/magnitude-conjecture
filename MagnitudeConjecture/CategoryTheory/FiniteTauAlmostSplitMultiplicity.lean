import MagnitudeConjecture.CategoryTheory.AlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteTauMatrix
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaLadderRadical

/-!
# Incoming multiplicity in a finite tau-category

The terminal map of a chosen right tau-sequence is a minimal right
almost-split map after identifying its endpoint with the chosen
indecomposable representative.  Hence the number of occurrences in the
chosen right-mesh middle term is the size of every finite indecomposable
decomposition of every minimal right almost-split source at that endpoint.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.FiniteTauMatrix

open QuotientSubmoduleEquidistribution.Iyama

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteRightTauCategoryData C Ind)

/-- The chosen right-mesh middle term as a displayed finite
indecomposable decomposition. -/
def rightMiddleFiniteIndecomposableDecomposition (Y : Ind) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (T.rightMesh (T.obj Y)).X₂ where
  n := rightMiddleArity T Y
  summand := fun i ↦ T.obj (rightMiddleLabel T Y i)
  indecomposable := fun i ↦ T.obj_indec (rightMiddleLabel T Y i)
  isoBiproduct := Classical.choice (rightMiddleIso T Y)

/-- After the chosen endpoint identification, the terminal map of a right
tau-sequence is right almost split. -/
theorem rightMesh_terminal_isRightAlmostSplit (Y : Ind) :
    IsRightAlmostSplit
      ((T.rightMesh (T.obj Y)).g ≫ (T.rightTermIso (T.obj Y)).hom) := by
  let S := T.rightMesh (T.obj Y)
  let e : S.X₃ ≅ T.obj Y := T.rightTermIso (T.obj Y)
  constructor
  · have hrad : IsRadicalMorphism (S.g ≫ e.hom) :=
      isRadicalMorphism_postcomp e.hom (T.rightTau (T.obj Y)).g_radical
    exact
      (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj (S.g ≫ e.hom)).1
        hrad
  · intro X g hg
    have hgrad : IsRadicalMorphism g :=
      (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj g).2 hg
    have hgrad' : IsRadicalMorphism (g ≫ e.inv) :=
      isRadicalMorphism_postcomp e.inv hgrad
    obtain ⟨c, hc⟩ :=
      (T.rightTau (T.obj Y)).factors_into_right (g ≫ e.inv) hgrad'
    refine ⟨c, ?_⟩
    calc
      c ≫ (S.g ≫ e.hom) = (c ≫ S.g) ≫ e.hom :=
        (Category.assoc _ _ _).symm
      _ = (g ≫ e.inv) ≫ e.hom := by rw [hc]
      _ = g := by simp

/-- The chosen right-mesh terminal map is right minimal after the endpoint
identification. -/
theorem rightMesh_terminal_isRightMinimal (Y : Ind) :
    IsRightMinimal
      ((T.rightMesh (T.obj Y)).g ≫ (T.rightTermIso (T.obj Y)).hom) :=
  IsRightMinimal.postcomp_iso (T.rightTermIso (T.obj Y))
    (T.rightTau (T.obj Y)).isRightMinimal_g

/-- The total incoming-arrow multiplicity at `Y`, represented by
`rightMiddleArity`, is the number of indecomposable occurrences in every
minimal right almost-split source ending at `T.obj Y`. -/
theorem rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
    (Y : Ind) {E : C} {f : E ⟶ T.obj Y}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition E)
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f) :
    rightMiddleArity T Y = d.n := by
  let dMesh := rightMiddleFiniteIndecomposableDecomposition T Y
  have hlocal (i : Fin dMesh.n) :
      IsLocalRing (End (dMesh.summand i)) :=
    T.obj_end_local (rightMiddleLabel T Y i)
  exact dMesh.n_eq_of_minimalRightAlmostSplit d hlocal
    (rightMesh_terminal_isRightAlmostSplit T Y)
    (rightMesh_terminal_isRightMinimal T Y) hf hfmin

end MagnitudeConjecture.FiniteTauMatrix
