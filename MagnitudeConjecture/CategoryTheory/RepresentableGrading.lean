import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpace
import MagnitudeConjecture.Combinatorics.PosetSpaceGrading

/-!
# Gradings carried by a representable poset-space realization

The frozen manuscript grades the factor category by path length and then
grades each represented total space `Hom(P, X)` by the same homogeneous Hom
components.  The chosen maps `P ⟶ P_t` are homogeneous.  Composition
therefore makes every distinguished subspace

`image (Hom(P_t, X) ⟶ Hom(P, X))`

homogeneous, so the represented poset space acquires the compatible internal
grading used in the concentration argument.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.PosetSpace

universe u v

variable (k T : Type u) (C : Type v) [Field k] [PartialOrder T]
variable [Category.{u} C] [Preadditive C] [Linear k C]

namespace RepresentableData

variable {k T C}

/-- An internal grading on every Hom space, compatible with composition and
with the chosen maps defining a representable poset-space realization. -/
structure HomGrading (D : RepresentableData k T C) where
  component : ∀ X Y : C, ℕ → Submodule k (X ⟶ Y)
  isInternal : ∀ X Y, DirectSum.IsInternal (component X Y)
  comp_mem : ∀ {X Y Z : C} {i j : ℕ} {f : X ⟶ Y} {g : Y ⟶ Z},
    f ∈ component X Y i → g ∈ component Y Z j →
      f ≫ g ∈ component X Z (i + j)
  unitDegree : T → ℕ
  unit_mem : ∀ t, D.unit t ∈ component D.source (D.projective t) (unitDegree t)

namespace HomGrading

variable {D : RepresentableData k T C}

/-- Precomposition by a chosen homogeneous map `P ⟶ P_t` shifts degree by
the degree of that map. -/
theorem precomposition_shiftsDegree (G : D.HomGrading) (t : T) (X : C) :
    GradedLinear.ShiftsDegree
      (G.component (D.projective t) X)
      (G.component D.source X)
      (D.precomposition t X) (G.unitDegree t) := by
  intro i f hf
  change D.unit t ≫ f ∈ G.component D.source X (i + G.unitDegree t)
  simpa [Nat.add_comm] using G.comp_mem (G.unit_mem t) hf

/-- Every distinguished subspace in the represented poset space is
homogeneous for the grading inherited from `Hom(P, X)`. -/
theorem subspace_isHomogeneous (G : D.HomGrading) (X : C) (t : T) :
    letI : DirectSum.Decomposition (G.component D.source X) :=
      (G.isInternal D.source X).chooseDecomposition
    DirectSum.SetLike.IsHomogeneous
      (G.component D.source X) ((D.obj X).subspace t) := by
  change
    letI : DirectSum.Decomposition (G.component D.source X) :=
      (G.isInternal D.source X).chooseDecomposition
    DirectSum.SetLike.IsHomogeneous
      (G.component D.source X) (LinearMap.range (D.precomposition t X))
  exact GradedLinear.ShiftsDegree.range_isHomogeneous
    (G.component (D.projective t) X) (G.component D.source X)
    (G.isInternal (D.projective t) X) (G.isInternal D.source X)
    (D.precomposition t X) (G.precomposition_shiftsDegree t X)

/-- The grading on `Hom(P, X)` is a compatible internal grading of the
represented poset space `F(X)`. -/
def objInternalGrading (G : D.HomGrading) (X : C) :
    InternalGrading (D.obj X) where
  component := G.component D.source X
  isInternal := G.isInternal D.source X
  subspace_isHomogeneous := G.subspace_isHomogeneous X

/-- A homogeneous categorical morphism induces a homogeneous morphism of the
represented poset spaces, of the same degree. -/
theorem map_homogeneousOfDegree (G : D.HomGrading)
    {X Y : C} {f : X ⟶ Y} {d : ℕ}
    (hf : f ∈ G.component X Y d) :
    InternalGrading.HomogeneousOfDegree
      (G.objInternalGrading X) (G.objInternalGrading Y) (D.map f) d := by
  intro i x hx
  exact G.comp_mem hx hf

/-- A nonzero homogeneous morphism between objects whose represented poset
spaces are Schur raises their concentration levels by exactly its degree. -/
theorem objLevel_add_degree_eq (G : D.HomGrading)
    {X Y : C} (hX : IsSchur k T (D.obj X)) (hY : IsSchur k T (D.obj Y))
    {f : X ⟶ Y} {d : ℕ} (hf : D.map f ≠ 0)
    (hfd : f ∈ G.component X Y d) :
    (G.objInternalGrading X).level hX + d =
      (G.objInternalGrading Y).level hY :=
  InternalGrading.level_add_degree_eq _ _ hX hY hf
    (G.map_homogeneousOfDegree hfd)

end HomGrading

end RepresentableData

end MagnitudeConjecture.PosetSpace
